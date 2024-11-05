{-# LANGUAGE ScopedTypeVariables #-}

module Cardano.Wallet.Deposit.Pure.RollbackWindow
    ( -- * Definition
      RollbackWindow
    , tip
    , finality
      -- $prop-RollbackWindow-invariant
    , member
      -- $prop-member-tip
      -- $prop-member-finality
    , singleton
      -- $prop-member-singleton

      -- * Operations

      -- ** Rolling
    , rollForward
    , MaybeRollback (..)
    , rollBackward
    , prune

      -- ** Other
    , intersection
      -- $prop-member-intersection
    )
where

import Prelude hiding (null, subtract)

-- |
-- (Internal function, exported for technical reasons.)
if' :: Bool -> a -> a -> a
if' True thn els = thn
if' False thn els = els

-- |
-- A 'RollbackWindow' is a time interval.
-- This time interval is used to keep track of data / transactions
-- that are not final and may still be rolled back.
--
-- * 'tip' is the higher end of the interval,
-- representing the latest state of the data.
-- * 'finality' is the lower end of the interval,
-- until which rollbacks are supported.
data RollbackWindow time = RollbackWindowC
    { finality :: time
    , tip :: time
    }

-- |
-- Test whether a given time is within a 'RollbackWindow'.
--
-- > member time w = (finality w <= time) && (time <= tip w)
member :: Ord time => time -> RollbackWindow time -> Bool
member time w = finality w <= time && time <= tip w

-- |
-- Interval containing a single point.
singleton :: Ord time => time -> RollbackWindow time
singleton time = RollbackWindowC time time

-- |
-- Move forward the tip of the 'RollbackWindow'.
-- Return 'Nothing' if the new tip would not actually be moving forward.
rollForward
    :: Ord time
    => time
    -> RollbackWindow time
    -> Maybe (RollbackWindow time)
rollForward newTip w =
    if'
        (tip w < newTip)
        (Just (RollbackWindowC (finality w) newTip))
        Nothing

-- |
-- Potential results of a 'rollBackwards'.
data MaybeRollback a
    = Past
    | Present a
    | Future

-- |
-- Roll back the tip of the 'RollbackWindow' to a point within the window.
-- Return different error conditions if the target is outside the window.
rollBackward
    :: Ord time
    => time
    -> RollbackWindow time
    -> MaybeRollback (RollbackWindow time)
rollBackward newTip w =
    if'
        (tip w <= newTip)
        Future
        ( if'
            (finality w <= newTip)
            (Present (RollbackWindowC (finality w) newTip))
            Past
        )

-- |
-- Move forward the finality of the 'RollbackWindow'.
-- Return 'Nothing' if the finality is not moving forward, or too far.
prune
    :: Ord time
    => time
    -> RollbackWindow time
    -> Maybe (RollbackWindow time)
prune newFinality w =
    if finality w <= newFinality && newFinality <= tip w
        then Just (RollbackWindowC newFinality (tip w))
        else Nothing

-- | Intersection of two 'RollbackWindow'.
intersection
    :: forall time
     . Ord time
    => RollbackWindow time
    -> RollbackWindow time
    -> Maybe (RollbackWindow time)
intersection w1 w2 =
    if' (fin3 <= tip3) (Just (RollbackWindowC fin3 tip3)) Nothing
  where
    fin3 :: time
    fin3 = max (finality w1) (finality w2)
    tip3 :: time
    tip3 = min (tip w1) (tip w2)

-- * Properties

-- $prop-RollbackWindow-invariant
-- #p:prop-RollbackWindow-invariant#
--
-- [prop-RollbackWindow-invariant]:
--
--     Invariant: 'finality' is always before or equal to the 'tip'.
--
--     @
--     @0 prop-RollbackWindow-invariant
--       : ∀ {time} {{_ : Ord time}}
--           (w : RollbackWindow time)
--       → (finality w <= tip w) ≡ True
--     @

-- $prop-member-finality
-- #p:prop-member-finality#
--
-- [prop-member-finality]:
--
--     The 'finality' is always a 'member' of a 'RollbackWindow'.
--
--     @
--     @0 prop-member-finality
--       : ∀ {time} {{_ : Ord time}} {{@0 _ : IsLawfulOrd time}}
--           (w : RollbackWindow time)
--       → member (finality w) w ≡ True
--     @

-- $prop-member-intersection
-- #p:prop-member-intersection#
--
-- [prop-member-intersection]:
--
--     A time @t@ is a 'member' of an intersection
--     if it is a member of both 'RollbackWindow's.
--
--     @
--     @0 prop-member-intersection
--       : ∀ {time} {{_ : Ord time}} {{@0 _ : IsLawfulOrd time}}
--           (w1 w2 w3 : RollbackWindow time)
--           (t : time)
--       → intersection w1 w2 ≡ Just w3
--       → member t w3 ≡ (member t w1 && member t w2)
--     @

-- $prop-member-singleton
-- #p:prop-member-singleton#
--
-- [prop-member-singleton]:
--
--     'singleton' contains exactly one point.
--
--     @
--     @0 prop-member-singleton
--       : ∀ {time} {{_ : Ord time}} {{@0 _ : IsLawfulOrd time}}
--           (t1 t2 : time)
--       → member t1 (singleton t2) ≡ (t1 == t2)
--     @

-- $prop-member-tip
-- #p:prop-member-tip#
--
-- [prop-member-tip]:
--
--     The 'tip' is always a 'member' of a 'RollbackWindow'.
--
--     @
--     @0 prop-member-tip
--       : ∀ {time} {{_ : Ord time}} {{@0 _ : IsLawfulOrd time}}
--           (w : RollbackWindow time)
--       → member (tip w) w ≡ True
--     @
