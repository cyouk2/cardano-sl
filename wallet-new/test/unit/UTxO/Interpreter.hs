-- | Interpreter from the DSL to Cardano types
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams #-}
module UTxO.Interpreter (
    -- * Translate the DSL to Cardano types
    Interpret(..)
  , intTopId
  , IntException(..)
  , IntM
  , runIntM
    -- * Convenience re-exports
  , SlotId(..)
  ) where

import Universum
import Data.Default (def)
import Prelude (Show(..))
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict    as Map

import Pos.Block.Logic
import Pos.Client.Txp
import Pos.Core
import Pos.Crypto
import Pos.Ssc (defaultSscPayload)
import Pos.Txp.Toil
import Pos.Util.Chrono

import UTxO.Bootstrap
import UTxO.Context
import UTxO.Crypto
import UTxO.Translate
import qualified UTxO.DSL as DSL

{-------------------------------------------------------------------------------
  Translate the DSL UTxO definitions to Cardano types

  NOTE: Delegation in Cardano is described in the document
  "Delegation and Stake Locking in Cardano SL"
  <cardano-sl-articles/delegation/pdf/article.pdf>.
-------------------------------------------------------------------------------}

-- | Interpretation error
data IntException =
    IntExNonOrdinaryAddress
  | IntExClassifyInputs Text
  | IntExMkDlg          Text
  | IntExCreateBlock    Text
  | IntExMkSlot         Text
  | IntExTx             TxError -- ^ Occurs during fee calculation
  deriving (Show)

instance Exception IntException

-- | Interpretation context
--
-- In order to interpret an input, we need the context (the ledger) in order
-- to resolve transaction hashes. See also 'int'.
type IntCtxt h = DSL.Ledger h Addr

-- | Interpretation monad
type IntM a = Translate IntException a

-- | Run the interpreter monad
runIntM :: IntM a -> a
runIntM = runTranslate

-- | Interpretation of the UTxO DSL
class Interpret h a where
  type Interpreted a :: *

  int :: IntCtxt h -> a -> IntM (Interpreted a)

-- | Run interpreter in the empty context
--
-- Specific to Identity otherwise we get unresolved type variables.
intTopId :: Interpret Identity a => a -> IntM (Interpreted a)
intTopId = int (DSL.ledgerEmpty :: DSL.Ledger Identity Addr)

instance Interpret h Addr where
  type Interpreted Addr = (SomeKeyPair, Address)

  int :: IntCtxt h -> Addr -> IntM (SomeKeyPair, Address)
  int _l = asks . resolveAddr

instance InterpretHash h => Interpret h (DSL.Input h Addr) where
  type Interpreted (DSL.Input h Addr) = TxOwnedInput SomeKeyPair

  int :: IntCtxt h -> DSL.Input h Addr -> IntM (TxOwnedInput SomeKeyPair)
  int l inp@(DSL.Input t _ix) | isBootstrapTransaction (DSL.findHash' l t) = do
      (ownerKey, ownerAddr) <- int l $ DSL.outAddr (DSL.inpSpentOutput' l inp)
      -- See explanation at 'bootstrapTransaction'
      return (
            ownerKey
          , TxInUtxo {
                txInHash  = unsafeHash ownerAddr
              , txInIndex = 0
              }
          )
  int l inp@DSL.Input{..} = do
      -- We figure out who must sign the input by looking at the output
      (ownerKey, _) <- int     l $ DSL.outAddr (DSL.inpSpentOutput' l inp)
      inpTrans'     <- intHash l $ inpTrans
      return (
            ownerKey
          , TxInUtxo {
                txInHash  = inpTrans'
              , txInIndex = inpIndex
              }
          )

instance Interpret h (DSL.Output Addr) where
  type Interpreted (DSL.Output Addr) = TxOutAux

  int :: IntCtxt h -> DSL.Output Addr -> IntM TxOutAux
  int l DSL.Output{..} = do
      (_, outAddr') <- int l outAddr
      return TxOutAux {
          toaOut = TxOut {
              txOutAddress = outAddr'
            , txOutValue   = mkCoin outVal
            }
        }

-- | Interpretation of transactions
instance InterpretHash h => Interpret h (DSL.Transaction h Addr) where
  type Interpreted (DSL.Transaction h Addr) = TxAux

  int :: IntCtxt h -> DSL.Transaction h Addr -> IntM TxAux
  int l t = do
      trIns'  <- mapM (int l) $ DSL.trIns' t
      trOuts' <- mapM (int l) $ DSL.trOuts t
      case classifyInputs trIns' of
        Left err ->
          throwError (IntExClassifyInputs err)
        Right (InputsRegular trIns'') -> withConfig $ return $
          makeMPubKeyTx
            (FakeSigner . regKpSec)
            (NE.fromList trIns'')
            (NE.fromList trOuts')
        Right (InputsRedeem (kp, inp)) -> withConfig $ return $
          makeRedemptionTx
            (redKpSec kp)
            (NE.fromList [inp])
            (NE.fromList trOuts')

-- | Interpretation of a list of transactions, oldest first
--
-- Each transaction becomes part of the context for the next.
instance InterpretHash h => Interpret h (DSL.Block h Addr) where
  type Interpreted (DSL.Block h Addr) = OldestFirst [] TxAux

  int :: IntCtxt h -> DSL.Block h Addr -> IntM (OldestFirst [] TxAux)
  int = \l ts -> (OldestFirst . snd) <$> go l (toList ts)
    where
      go :: IntCtxt h -> [DSL.Transaction h Addr] -> IntM (IntCtxt h, [TxAux])
      go l []     = return (l, [])
      go l (t:ts) = do
          t' <- int l t
          second (t':) <$> go (DSL.ledgerAdd t l) ts

-- | Interpretation of a list of list of transactions (basically a chain)
--
-- Each list becomes part of the context for the next.
instance InterpretHash h => Interpret h (DSL.Blocks h Addr) where
  type Interpreted (DSL.Blocks h Addr) = OldestFirst [] (OldestFirst [] TxAux)

  int :: IntCtxt h
      -> DSL.Blocks h Addr -> IntM (OldestFirst [] (OldestFirst [] TxAux))
  int = \l tss -> (OldestFirst . snd) <$> go l (toList tss)
    where
      go :: IntCtxt h
         -> [DSL.Block h Addr]
         -> IntM (IntCtxt h, [OldestFirst [] TxAux])
      go l []       = return (l, [])
      go l (ts:tss) = do
          ts' <- int l ts
          second (ts':) <$> go (DSL.ledgerAdds (toNewestFirst ts) l) tss

-- TODO: Here and elsewhere we assume we stay within a single epoch
instance InterpretHash h => Interpret h (DSL.Chain h Addr) where
  type Interpreted (DSL.Chain h Addr) = OldestFirst [] Block

  int :: IntCtxt h -> DSL.Chain h Addr -> IntM (OldestFirst [] Block)
  int = \l DSL.Chain{..} -> do
      tss <- int l chainBlocks
      OldestFirst <$> mkBlocks Nothing 0 (toList (map toList tss))
    where
      mkBlocks :: Maybe MainBlock -> Word16 -> [[TxAux]] -> IntM [Block]
      mkBlocks _    _    []       = return []
      mkBlocks prev slot (ts:tss) = do
          lsi <- mapTranslateErrors IntExMkSlot $
                   withConfig $ mkLocalSlotIndex slot
          let slotId = SlotId (EpochIndex 0) lsi
          block <- mkBlock prev slotId ts
          (Right block :) <$> mkBlocks (Just block) (slot + 1) tss

      mkBlock :: Maybe MainBlock -> SlotId -> [TxAux] -> IntM MainBlock
      mkBlock mPrev slotId ts = do
        -- empty delegation payload
        dlgPayload <- mapTranslateErrors IntExMkDlg $
                        withConfig $ mkDlgPayload []

        -- empty update payload
        let updPayload = def

        -- previous block header
        -- if none specified, use genesis block
        prev <-
          case mPrev of
            Just prev -> (Right . view gbHeader) <$> return prev
            Nothing   -> (Left  . view gbHeader) <$> asks (ccBlock0 . tcCardano)

        -- figure out who needs to sign the block
        BlockSignInfo{..} <- asks $ blockSignInfoForSlot slotId

        mapTranslateErrors IntExCreateBlock $
          withConfig $ createMainBlockPure
            blockSizeLimit
            prev
            (Just (bsiPSK, bsiLeader))
            slotId
            bsiKey
            (RawPayload
                (toList ts)
                (defaultSscPayload (siSlot slotId)) -- TODO
                dlgPayload
                updPayload
              )

      -- TODO: Get this value from somewhere rather than hardcoding it
      blockSizeLimit = 2 * 1024 * 1024 -- 2 MB

instance InterpretHash h => Interpret h (DSL.Utxo h Addr) where
  type Interpreted (DSL.Utxo h Addr) = Utxo

  int :: IntCtxt h -> DSL.Utxo h Addr -> IntM Utxo
  int l = fmap Map.fromList . mapM aux . DSL.utxoToList
    where
      aux :: (DSL.Input h Addr, DSL.Output Addr) -> IntM (TxIn, TxOutAux)
      aux (inp, out) = do
          (_key, inp') <- int l inp
          out'         <- int l out
          return (inp', out')

{-------------------------------------------------------------------------------
  Hashing
-------------------------------------------------------------------------------}

-- | Interpret a hash as TxId
--
-- NOTE: See <http://cardano-dev.askbot.com/question/11/why-transactions-dont-include-witnesses/>
-- for why 'TxId' is @Hash Tx@ rather than @Hash TxAux@.
class DSL.Hash h Addr => InterpretHash h where
  intHash :: IntCtxt h -> h (DSL.Transaction h Addr) -> IntM TxId

instance InterpretHash Identity where
  intHash l (Identity t) = (hash . taTx) <$> int l t
