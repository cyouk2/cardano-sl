{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Idealized specification of UTxO-style accounting
module UTxO.DSL (
    -- * Parameters
    Value
  , Index
    -- * Addresses
  , Address(..)
    -- * Transaction
  , Transaction(..)
  , trIns'
  , trIsAcceptable
  , trBalance
  , trSpentOutputs
  , trGeneratedOutputs
  , trUtxo
    -- * Outputs
  , Output(..)
    -- * Inputs
  , Input(..)
  , inpTransaction
  , inpSpentOutput
  , inpSpentOutput'
  , inpVal
  , inpVal'
    -- * Ledger
  , Ledger(..)
  , ledgerEmpty
  , ledgerAdd
  , ledgerAdds
  , ledgerTails
  , ledgerBalance
  , ledgerUnspentOutputs
  , ledgerUtxo
  , ledgerIsValid
    -- * Hash
  , Hash(..)
  , findHash'
    -- * Additional
    -- ** UTxO
  , Utxo(..)
  , utxoEmpty
  , utxoFromMap
  , utxoFromList
  , utxoToList
  , utxoDomain
  , utxoRemove
  , utxoUnion
    -- ** Chain
  , Block
  , Blocks
  , Chain(..)
  , chainToLedger
  ) where

import Universum
import Data.List (tail)
import Data.Map.Strict (Map)
import Data.Set (Set)
import Formatting (bprint, build, (%))
import Pos.Util.Chrono
import Serokell.Util (listJson, mapJson)
import qualified Data.Map.Strict as Map
import qualified Data.Set        as Set
import qualified Data.Text.Buildable

{-------------------------------------------------------------------------------
  Parameters
-------------------------------------------------------------------------------}

type Value = Word64
type Index = Word32

{-------------------------------------------------------------------------------
  Addresses
-------------------------------------------------------------------------------}

-- | Address
--
-- We identity some special addresses to deal with fresh coin generation and
-- fees. This is only used in balance computations.
data Address a =
    AddrGenesis
  | AddrTreasury
  | AddrRegular a
  deriving (Eq, Ord)

{-------------------------------------------------------------------------------
  Transactions

  We define UTxO-style transactions only; for our purposes account-style
  transactions are not needed.
-------------------------------------------------------------------------------}

data Transaction h a = Transaction {
      trFresh :: Value
    , trIns   :: Set (Input h a)
    , trOuts  :: [Output a]
    , trFee   :: Value
    }

deriving instance (Hash h a, Eq  a) => Eq  (Transaction h a)
deriving instance (Hash h a, Ord a) => Ord (Transaction h a)

-- | The inputs as a list
--
-- Useful in various calculations
trIns' :: Transaction h a -> [Input h a]
trIns' = Set.toList . trIns

-- | Whether this transaction is acceptable for the given ledger
--
-- NOTE: The notion of 'valid' is not relevant for UTxO transactions,
-- so we omit it.
trIsAcceptable :: Hash h a => Transaction h a -> Ledger h a -> Bool
trIsAcceptable t l = and [
      allInputsHaveOutputs
    , valueIsPreserved
    , inputsHaveNotBeenSpent
    ]
  where
    allInputsHaveOutputs :: Bool
    allInputsHaveOutputs = all (isJust . inpSpentOutput l) (trIns t)

    valueIsPreserved :: Bool
    valueIsPreserved =
           sum (map (inpVal' l) (trIns' t)) + trFresh t
        == sum (map outVal      (trOuts t)) + trFee   t

    inputsHaveNotBeenSpent :: Bool
    inputsHaveNotBeenSpent = all (`Set.member` ledgerUnspentOutputs l) (trIns t)

-- | The effect this transaction has on the balance of an address
trBalance :: forall h a. (Hash h a, Eq a)
          => Address a -> Transaction h a -> Ledger h a -> Value
trBalance a t l = received - spent
  where
    received, spent :: Value
    received = total outputsReceived + case a of
                                         AddrTreasury -> trFee t
                                         _otherwise   -> 0
    spent    = total outputsSpent    + case a of
                                         AddrGenesis  -> trFresh t
                                         _otherwise   -> 0

    outputsReceived, outputsSpent :: [Output a]
    outputsReceived = our $                          trOuts t
    outputsSpent    = our $ map (inpSpentOutput' l) (trIns' t)

    our :: [Output a] -> [Output a]
    our = filter (\o -> AddrRegular (outAddr o) == a)

    total :: [Output a] -> Value
    total = sum . map outVal

-- | The outputs spent by this transaction
--
-- Defined only for consistency.
trSpentOutputs :: Transaction h a -> Set (Input h a)
trSpentOutputs = trIns

-- | The outputs generated by this transaction
trGeneratedOutputs :: Hash h a => Transaction h a -> Set (Input h a)
trGeneratedOutputs = utxoDomain . trUtxo

-- | The UTxO generated by this transaction
trUtxo :: Hash h a => Transaction h a -> Utxo h a
trUtxo t = utxoFromList $
             zipWith (\i o -> (Input (hash t) i, o)) [0..] (trOuts t)

{-------------------------------------------------------------------------------
  Outputs
-------------------------------------------------------------------------------}

-- | Transaction output
--
-- NOTE: In the spec, this allows for @Address a@ rather than @a@. This is not
-- needed in Cardano, where that additional flexibility is not supported. We
-- therefore use this more restricted version.
data Output a = Output {
      outAddr :: a
    , outVal  :: Value
    }
  deriving (Eq, Ord)

{-------------------------------------------------------------------------------
  Inputs
-------------------------------------------------------------------------------}

data Input h a = Input {
      inpTrans :: h (Transaction h a)
    , inpIndex :: Index
    }

deriving instance Hash h a => Eq  (Input h a)
deriving instance Hash h a => Ord (Input h a)

inpTransaction :: Hash h a => Ledger h a -> Input h a -> Maybe (Transaction h a)
inpTransaction l i = findHash l (inpTrans i)

inpSpentOutput :: Hash h a => Ledger h a -> Input h a -> Maybe (Output a)
inpSpentOutput l i = do
    t <- inpTransaction l i
    trOuts t `at` fromIntegral (inpIndex i)

inpVal :: Hash h a => Ledger h a -> Input h a -> Maybe Value
inpVal l i = outVal <$> inpSpentOutput l i

{-------------------------------------------------------------------------------
  Variations on the functions on inputs, when we are sure that the
  transaction is known and the input index is correct
-------------------------------------------------------------------------------}

inpSpentOutput' :: Hash h a => Ledger h a -> Input h a -> Output a
inpSpentOutput' l = fromMaybe (error "inpSpentOutput': Nothing")
                  . inpSpentOutput l

inpVal' :: Hash h a => Ledger h a -> Input h a -> Value
inpVal' l = fromMaybe (error "inpVal': Nothing")
          . inpVal l

{-------------------------------------------------------------------------------
  Ledger
-------------------------------------------------------------------------------}

-- | Ledger (list of transactions)
--
-- The ledger is stored in newest-first order. To enforce this, the constructor
-- is marked as unsafe.
newtype Ledger h a = Ledger {
    ledgerTransactions :: NewestFirst [] (Transaction h a)
  }

ledgerEmpty :: Ledger h a
ledgerEmpty = Ledger (NewestFirst [])

ledgerToNewestFirst :: Ledger h a -> [Transaction h a]
ledgerToNewestFirst (Ledger l) = toList l

-- | Append single transaction to the ledger
ledgerAdd :: Transaction h a -> Ledger h a -> Ledger h a
ledgerAdd = ledgerAdds . NewestFirst . (:[])

-- | Append a bunch of transactions to the ledger
ledgerAdds :: NewestFirst [] (Transaction h a) -> Ledger h a -> Ledger h a
ledgerAdds (NewestFirst ts) (Ledger (NewestFirst l)) =
    Ledger (NewestFirst (ts ++ l))

-- | Each transaction in the ledger, along with its context (the transactions
-- it's allowed to refer to)
ledgerTails :: Ledger h a -> [(Transaction h a, Ledger h a)]
ledgerTails (Ledger (NewestFirst l)) =
    zipWith (\t ts -> (t, Ledger (NewestFirst ts))) l (tail (tails l))

ledgerBalance :: forall h a. (Hash h a, Eq a)
              => Address a -> Ledger h a -> Value
ledgerBalance a l = sum $ map (uncurry (trBalance a)) (ledgerTails l)

-- | Unspent outputs in the ledger
--
-- Should satisfy that
--
-- > ledgerUnspentOutputs l = Map.keysSet (ledgerUtxo l)
ledgerUnspentOutputs :: forall h a. Hash h a => Ledger h a -> Set (Input h a)
ledgerUnspentOutputs l = go (ledgerToNewestFirst l)
  where
    go :: [Transaction h a] -> Set (Input h a)
    go []     = Set.empty
    go (t:ts) = (go ts Set.\\ trSpentOutputs t) `Set.union` trGeneratedOutputs t

-- | UTxO of a ledger
--
-- TODO: We should have a property relating this to 'ledgerBalance'.
ledgerUtxo :: forall h a. Hash h a => Ledger h a -> Utxo h a
ledgerUtxo l = go (ledgerToNewestFirst l)
  where
    go :: [Transaction h a] -> Utxo h a
    go []     = utxoEmpty
    go (t:ts) = go ts `utxoRemove` trSpentOutputs t `utxoUnion` trUtxo t

-- | Ledger validity
ledgerIsValid :: forall h a. Hash h a => Ledger h a -> Bool
ledgerIsValid l = all (uncurry trIsAcceptable) (ledgerTails l)

{-------------------------------------------------------------------------------
  We parameterize over the hashing function
-------------------------------------------------------------------------------}

-- | Generalization of a hashing function
--
-- Ideally we'd strip the @a@ parameter here, but that would mean we'd need
-- quantified contexts to model the superclass constraint, which sadly we
-- don't have in ghc yet.
class ( Ord       (h (Transaction h a))
      , Buildable (h (Transaction h a))
      ) => Hash h a where
  -- | Hash a transaction
  hash :: Transaction h a -> h (Transaction h a)

-- | Locate a transaction in the ledger, giving its hash
--
-- NOTE: Even when we instantiate @h@ to 'Identity', we still want to search
-- the ledger, because an input that refers to a transaction that isn't
-- actually in the ledger would be invalid.
findHash :: Hash h a
         => Ledger h a -> h (Transaction h a) -> Maybe (Transaction h a)
findHash l h = find (\t -> hash t == h) (ledgerToNewestFirst l)

-- | Variation on 'findHash', assumes hash refers to existing transaction
findHash' :: Hash h a => Ledger h a -> h (Transaction h a) -> Transaction h a
findHash' l = fromMaybe (error "findHash': Nothing")
            . findHash l

{-------------------------------------------------------------------------------
  Instantiating the hash to the identity
-------------------------------------------------------------------------------}

instance (Ord a, Buildable a) => Hash Identity a where
  hash = Identity

instance (Ord a, Buildable a) => Buildable (Identity (Transaction Identity a)) where
  build (Identity t) = bprint build t

{-------------------------------------------------------------------------------
  Additional: UTxO
-------------------------------------------------------------------------------}

-- | Unspent transaciton outputs
data Utxo h a = Utxo { utxoToMap :: Map (Input h a) (Output a) }

utxoEmpty :: Utxo h a
utxoEmpty = Utxo Map.empty

utxoFromMap :: Map (Input h a) (Output a) -> Utxo h a
utxoFromMap = Utxo

utxoFromList :: Hash h a => [(Input h a, Output a)] -> Utxo h a
utxoFromList = utxoFromMap . Map.fromList

utxoToList :: Utxo h a -> [(Input h a, Output a)]
utxoToList = Map.toList . utxoToMap

utxoDomain :: Utxo h a -> Set (Input h a)
utxoDomain = Map.keysSet . utxoToMap

utxoRemove :: Hash h a => Utxo h a -> Set (Input h a) -> Utxo h a
utxoRemove (Utxo utxo) inps = Utxo (utxo `withoutKeys` inps)

utxoUnion :: Hash h a => Utxo h a -> Utxo h a -> Utxo h a
utxoUnion (Utxo utxo) (Utxo utxo') = Utxo (utxo `Map.union` utxo')

{-------------------------------------------------------------------------------
  Additional: chain
-------------------------------------------------------------------------------}

type Block  h a = OldestFirst [] (Transaction h a)
type Blocks h a = OldestFirst [] (Block h a)

-- | A chain
--
-- A chain is just a series of blocks, here modelled simply as the transactions
-- they contain, since the rest of the block information can then be inferred.
data Chain h a = Chain { chainBlocks :: Blocks h a }

chainToLedger :: Transaction h a -> Chain h a -> Ledger h a
chainToLedger boot = Ledger
                   . NewestFirst
                   . reverse
                   . (boot :)
                   . concat . map toList . toList
                   . chainBlocks

{-------------------------------------------------------------------------------
  Pretty-printing
-------------------------------------------------------------------------------}

instance Buildable a => Buildable (Address a) where
  build AddrGenesis     = "AddrGenesis"
  build AddrTreasury    = "AddrTreasury"
  build (AddrRegular a) = bprint ("AddrRegular " % build) a

instance Buildable a => Buildable (Output a) where
  build Output{..} = bprint
      ( "Output"
      % "{ addr: " % build
      % ", val:  " % build
      % "}"
      )
      outAddr
      outVal

instance (Buildable a, Hash h a) => Buildable (Input h a) where
  build Input{..} = bprint
      ( "Input"
      % "{ trans: " % build
      % ", index: " % build
      % "}"
      )
      inpTrans
      inpIndex

instance (Buildable a, Hash h a) => Buildable (Transaction h a) where
  build Transaction{..} = bprint
      ( "Transaction"
      % "{ fresh: " % build
      % ", ins:   " % listJson
      % ", outs:  " % listJson
      % ", fee:   " % build
      % "}"
      )
      trFresh
      trIns
      trOuts
      trFee

instance (Buildable a, Hash h a) => Buildable (Chain h a) where
  build Chain{..} = bprint
      ( "Chain"
      % "{ blocks: " % listJson
      % "}"
      )
      chainBlocks

instance ( Buildable a, Hash h a, Foldable f) => Buildable (NewestFirst f (Transaction h a)) where
  build ts = bprint ("NewestFirst " % listJson) (toList ts)

instance (Buildable a, Hash h a, Foldable f) => Buildable (OldestFirst f (Transaction h a)) where
  build ts = bprint ("OldestFirst " % listJson) (toList ts)

instance (Buildable a, Hash h a) => Buildable (Ledger h a) where
  build (Ledger l) = bprint build l

instance (Buildable a, Hash h a) => Buildable (Utxo h a) where
  build (Utxo utxo) = bprint ("Utxo " % mapJson) utxo

{-------------------------------------------------------------------------------
  Auxiliary
-------------------------------------------------------------------------------}

at :: [a] -> Int -> Maybe a
at []     _ = Nothing
at (x:_)  0 = Just x
at (_:xs) i = at xs (i - 1)

withoutKeys :: Ord k => Map k a -> Set k -> Map k a
m `withoutKeys` s = m `Map.difference` Map.fromSet (const ()) s
