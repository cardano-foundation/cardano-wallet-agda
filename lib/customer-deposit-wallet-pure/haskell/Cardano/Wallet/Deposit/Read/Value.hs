{-# LANGUAGE StandaloneDeriving, LambdaCase #-}
module Cardano.Wallet.Deposit.Read.Value where

import qualified Haskell.Data.ByteString as BS (ByteString)
import qualified Haskell.Data.Map as Map (Map, empty, filterWithKey, fromList, lookup, null, unionWith)
import Haskell.Data.Maybe (fromMaybe)
import Numeric.Natural (Natural)

type Coin = Natural

monusCoin :: Coin -> Coin -> Coin
monusCoin a b
  = case a < b of
        False -> a - b
        True -> 0

type AssetName = BS.ByteString

type ScriptHash = BS.ByteString

type PolicyID = ScriptHash

type Quantity = Integer

data AssetID = AdaID
             | Asset PolicyID AssetName

deriving instance Eq AssetID

deriving instance Ord AssetID

data Value = Value{ada :: Coin,
                   assets :: Map.Map (PolicyID, AssetName) Quantity}

deriving instance Eq Value

valueFromList :: Coin -> [(PolicyID, AssetName, Quantity)] -> Value
valueFromList coin xs
  = Value coin
      (Map.fromList
         (map
            (\case
                 (p, n, q) -> ((p, n), q))
            xs))

injectCoin :: Coin -> Value
injectCoin coin = Value coin Map.empty

getCoin :: Value -> Coin
getCoin v = ada v

largerOrEqual :: Value -> Value -> Bool
largerOrEqual a b
  = ada a >= ada b &&
      Map.null (Map.filterWithKey isSmallerThanB (assets a))
  where
    isSmallerThanB :: (PolicyID, AssetName) -> Quantity -> Bool
    isSmallerThanB key qa
      = qa < fromMaybe 0 (Map.lookup key (assets b))

instance Semigroup Value where
    a <> b
      = Value (ada a + ada b) (Map.unionWith (+) (assets a) (assets b))

instance Monoid Value where
    mempty = Value 0 Map.empty

monus :: Value -> Value -> Value
monus a b
  = Value (monusCoin (ada a) (ada b))
      (Map.unionWith minus (assets a) (assets b))
  where
    minus :: Quantity -> Quantity -> Quantity
    minus a b = a - b

