module Cardano.Wallet.Deposit.Pure.Timeline where

import qualified Haskell.Data.Map as Map (Map, insert, lookup, takeWhileAntitone, toAscList)

data Timeline time a = Timeline{events :: Map.Map time a,
                                tip :: time}

atTime :: Ord time => time -> Timeline time a -> Maybe a
atTime t = Map.lookup t . \ r -> events r

getTip :: Ord time => Timeline time a -> time
getTip = \ r -> tip r

rollForward ::
              Ord time => time -> a -> Timeline time a -> Timeline time a
rollForward time a xs
  = if time > tip xs then
      Timeline (Map.insert time a (events xs)) time else xs

rollBackward ::
               Ord time => time -> Timeline time a -> Timeline time a
rollBackward time xs
  = if time < tip xs then
      Timeline (Map.takeWhileAntitone (<= time) (events xs)) time else xs

filterRange ::
              Ord time => (time, time) -> Timeline time a -> Timeline time a
filterRange (low, high) xs
  = Timeline
      (Map.takeWhileAntitone (<= high)
         (Map.takeWhileAntitone (> low) (events xs)))
      (tip xs)

toAscList :: Ord time => Timeline time a -> [(time, a)]
toAscList = Map.toAscList . \ r -> events r

