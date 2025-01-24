-- | A map from pairs of keys to values,
-- with efficient lookups for single keys.
module Data.Maps.PairMap where

open import Haskell.Prelude
open import Haskell.Reasoning

open import Haskell.Data.List using
    ( foldl'
    )
open import Data.Map using
    ( Map
    )
open import Haskell.Data.Maybe using
    ( fromMaybe
    )
open import Data.Set using
    ( ℙ
    )

import Data.Map as Map

{-# FOREIGN AGDA2HS
{-# LANGUAGE StrictData #-}
#-}

{-# FOREIGN AGDA2HS
-- Working around a limitation in agda2hs.
import Data.List (foldl')
import Data.Maybe (fromMaybe)
import Data.Map (Map)
import qualified Data.Map as Map
#-}

variable
  v : Set


{-----------------------------------------------------------------------------
    Helper properties
    general
------------------------------------------------------------------------------}
prop-bind-if-Maybe
  : ∀ (b : Bool) (t e : a → Maybe c) (m1 : Maybe a)
  → m1 >>= (λ x → if b then t x else e x)
      ≡ (if b then (m1 >>= t) else (m1 >>= e))
prop-bind-if-Maybe False = λ t e m1 → refl
prop-bind-if-Maybe True = λ t e m1 → refl

prop-bind-Nothing
  : ∀ {a b : Set} (m : Maybe a)
  → let nothing : Maybe b
        nothing = Nothing
    in m >>= (λ x → nothing) ≡ nothing
prop-bind-Nothing Nothing = refl
prop-bind-Nothing (Just x) = refl

--
prop-elem-keys
  : ∀ {a k : Set} {{_ : Ord k}}
  → ∀ (key : k) (xs : Map k a)
  → elem key (Map.keys xs) ≡ False
  → Map.lookup key xs ≡ Nothing
--
prop-elem-keys key xs
  rewrite Map.prop-elem-keys key xs
  with Map.lookup key xs in eq
... | Nothing = λ x → refl
... | Just x = λ ()

{-----------------------------------------------------------------------------
    Helper functions
------------------------------------------------------------------------------}

explicitEmpty : {{_ : Ord a}} → Map a v → Maybe (Map a v)
explicitEmpty m = if Map.null m then Nothing else Just m

implicitEmpty : {{_ : Ord a}} → Maybe (Map a v) → Map a v
implicitEmpty = fromMaybe Map.empty

withEmpty
  : {{_ : Ord a}}
  → (Map a v → Map a v)
  → Maybe (Map a v) → Maybe (Map a v)
withEmpty f = explicitEmpty ∘ f ∘ implicitEmpty

{-# COMPILE AGDA2HS explicitEmpty #-}
{-# COMPILE AGDA2HS implicitEmpty #-}
{-# COMPILE AGDA2HS withEmpty #-}

@0 prop-explicitEmpty-bind
  : ∀ {{_ : Ord a}} (x : a) (m : Map a b)
  → explicitEmpty m >>= Map.lookup x
    ≡ Map.lookup x m
prop-explicitEmpty-bind x m = case Map.null m of λ
  { True {{eq}} →
    begin
      (if Map.null m then Nothing else Just m) >>= Map.lookup x
    ≡⟨ cong (λ o → (if o then Nothing else Just m) >>= Map.lookup x) eq ⟩
      Nothing
    ≡⟨ sym (Map.prop-lookup-empty x) ⟩
      Map.lookup x Map.empty
    ≡⟨ cong (λ o → Map.lookup x o) (sym (Map.prop-null→empty m eq)) ⟩
      Map.lookup x m
    ∎
  ; False {{eq}} →
    begin
      (if Map.null m then Nothing else Just m) >>= Map.lookup x
    ≡⟨ cong (λ o → (if o then Nothing else Just m) >>= Map.lookup x) eq ⟩
      Just m >>= Map.lookup x
    ≡⟨⟩
      Map.lookup x m
    ∎
  }

@0 prop-implicitEmpty-bind
  : ∀ {{_ : Ord a}} (x : a) (m : Maybe (Map a b))
  → m >>= Map.lookup x
    ≡ Map.lookup x (implicitEmpty m)
prop-implicitEmpty-bind x Nothing = sym (Map.prop-lookup-empty x)
prop-implicitEmpty-bind x (Just m1) = refl

{-----------------------------------------------------------------------------
    Map a (Map b v)
    Helper functions and properties
------------------------------------------------------------------------------}

lookup2
  : {{_ : Ord a}} → {{_ : Ord b}}
  → a → b → Map a (Map b v) → Maybe v
lookup2 a b m = Map.lookup a m >>= Map.lookup b

insert2
  : {{_ : Ord a}} → {{_ : Ord b}}
  → a → b → v → Map a (Map b v) → Map a (Map b v)
insert2 ai bi v m =
  Map.insert ai (Map.insert bi v (implicitEmpty (Map.lookup ai m))) m

delete2
  : {{_ : Ord a}} → {{_ : Ord b}}
  → a → b → Map a (Map b v) → Map a (Map b v)
delete2 a b = Map.update (explicitEmpty ∘ Map.delete b) a

delete2s
  : {{_ : Ord a}} → {{_ : Ord b}}
  → List a → b → Map a (Map b v) → Map a (Map b v)
delete2s xs b m0 = foldr (λ a m → delete2 a b m) m0 xs
-- fixme: use foldl'

{-# COMPILE AGDA2HS lookup2 #-}
{-# COMPILE AGDA2HS insert2 #-}
{-# COMPILE AGDA2HS delete2 #-}
{-# COMPILE AGDA2HS delete2s #-}

prop-lookup2-eqA
  : ∀ {A B V : Set} {{_ : Ord A}} → {{_ : Ord B}}
  → ∀ (a1 a2 : A) (b : B) (m : Map A (Map B V))
  → (a1 == a2) ≡ True
  → lookup2 a1 b m ≡ lookup2 a2 b m
prop-lookup2-eqA a1 a2 b m eq =
  cong (_>>= Map.lookup b) (Map.prop-lookup-eq a1 a2 m eq)

prop-lookup2-eqB
  : ∀ {A B V : Set} {{_ : Ord A}} → {{_ : Ord B}}
  → ∀ (a : A) (b1 b2 : B) (m : Map A (Map B V))
  → (b1 == b2) ≡ True
  → lookup2 a b1 m ≡ lookup2 a b2 m
prop-lookup2-eqB a b1 b2 m eq =
  cong (Map.lookup a m >>=_) (ext (λ o → Map.prop-lookup-eq b1 b2 o eq))

--
@0 prop-lookup2-insert2
  : {A B V : Set} {{_ : Ord A}} → {{_ : Ord B}}
  → ∀ (a ai : A) (b bi : B) (v : V) (m : Map A (Map B V))
  → lookup2 a b (insert2 ai bi v m)
    ≡ (if a == ai && b == bi then Just v else lookup2 a b m)
--
prop-lookup2-insert2 a ai b bi v m = lem2
  where
    fun = Map.insert bi v ∘ implicitEmpty

    lem1
      : ((a == ai) ≡ True)
      → (if (b == bi) then Just v else lookup2 a b m)
        ≡ (if (b == bi) then Just v else lookup2 ai b m)
    lem1 = λ eq →
      begin
        (if (b == bi) then Just v else lookup2 a b m)
      ≡⟨ cong (λ o → if (b == bi) then Just v else o) (prop-lookup2-eqA a ai b m eq) ⟩
        (if (b == bi) then Just v else lookup2 ai b m)
      ∎

    lem2 =
      begin
        lookup2 a b (insert2 ai bi v m)
      ≡⟨⟩
        Map.lookup a (Map.insert ai (Map.insert bi v (implicitEmpty (Map.lookup ai m))) m)
          >>= Map.lookup b
      ≡⟨ cong (λ o → o >>= Map.lookup b) (Map.prop-lookup-insert a ai _ m) ⟩
        (if (a == ai)
          then Just (Map.insert bi v (implicitEmpty (Map.lookup ai m)))
          else Map.lookup a m
        ) >>= Map.lookup b
      ≡⟨ prop-if-apply (a == ai) _ (Map.lookup a m) (_>>= Map.lookup b) ⟩
        (if (a == ai)
          then Map.lookup b (Map.insert bi v (implicitEmpty (Map.lookup ai m)))
          else lookup2 a b m
        )
      ≡⟨ cong (λ o → if (a == ai) then o else _) (Map.prop-lookup-insert b bi v _) ⟩
        (if (a == ai)
          then (if (b == bi) then Just v else Map.lookup b (implicitEmpty (Map.lookup ai m)))
          else lookup2 a b m
        )
      ≡⟨ cong (λ o → if (a == ai) then (if (b == bi) then Just v else o) else _) (sym (prop-implicitEmpty-bind b (Map.lookup ai m))) ⟩
        (if (a == ai)
          then (if (b == bi) then Just v else Map.lookup ai m >>= Map.lookup b)
          else lookup2 a b m
        )
      ≡⟨⟩
        (if (a == ai)
          then (if (b == bi) then Just v else lookup2 ai b m)
          else lookup2 a b m
        )
      ≡⟨ sym (prop-if-eq-subst a ai (λ ax → if (b == bi) then Just v else lookup2 ax b m) (lookup2 a b m) lem1) ⟩
        (if (a == ai)
          then (if (b == bi) then Just v else lookup2 a b m)
          else lookup2 a b m
        )
      ≡⟨ prop-if-nested (a == ai) (b == bi) _ (lookup2 a b m) ⟩
        (if a == ai && b == bi then Just v else lookup2 a b m)
     ∎

--
@0 prop-lookup2-delete2
  : {A B V : Set} {{_ : Ord A}} → {{_ : Ord B}}
  → ∀ (a : A) (b : B) (ai : A) (bi : B) (m : Map A (Map B V))
  → lookup2 a b (delete2 ai bi m)
    ≡ (if a == ai && b == bi then Nothing else lookup2 a b m)
--
prop-lookup2-delete2 {A} {B} {V} a b ai bi m = lem2
  where
    fun : Map B V → Maybe (Map B V)
    fun x = explicitEmpty (Map.delete bi x)

    nothing : Maybe V
    nothing = Nothing

    lem1
      : ∀ (m : Map A (Map B V))
      → ((Map.lookup a m >>= fun) >>= Map.lookup b)
        ≡ (if b == bi then Nothing else (Map.lookup a m >>= Map.lookup b))
    lem1 m =
      begin
        ((Map.lookup a m >>= fun) >>= Map.lookup b)
      ≡⟨ sym (IsLawfulMonad.associativity iLawfulMonadMaybe (Map.lookup a m) fun (Map.lookup b)) ⟩
        (Map.lookup a m >>= (λ x → fun x >>= Map.lookup b))
      ≡⟨⟩
        (Map.lookup a m >>= (λ x → explicitEmpty (Map.delete bi x) >>= Map.lookup b))
      ≡⟨ cong (λ o → Map.lookup a m >>= o) (ext (λ x → prop-explicitEmpty-bind b (Map.delete bi x))) ⟩
        (Map.lookup a m >>= (λ x → Map.lookup b (Map.delete bi x)))
      ≡⟨ cong (λ o → Map.lookup a m >>= o) (ext (Map.prop-lookup-delete b bi)) ⟩
        (Map.lookup a m >>= (λ x → if b == bi then Nothing else Map.lookup b x))
      ≡⟨ prop-bind-if-Maybe (b == bi) (λ x → nothing) (Map.lookup b) (Map.lookup a m) ⟩
        (if b == bi then ((Map.lookup a m) >>= (λ x → nothing)) else (Map.lookup a m >>= Map.lookup b))
      ≡⟨ cong (λ o → if b == bi then o else (Map.lookup a m >>= Map.lookup b) ) (prop-bind-Nothing (Map.lookup a m)) ⟩
        (if b == bi then Nothing else (Map.lookup a m >>= Map.lookup b))
      ∎

    lem2 =
      begin
        lookup2 a b (delete2 ai bi m)
      ≡⟨⟩
        Map.lookup a (Map.update fun ai m) >>= Map.lookup b
      ≡⟨ cong (_>>= Map.lookup b) (Map.prop-lookup-update a ai m fun) ⟩
        (if (a == ai) then (Map.lookup ai m >>= fun) else Map.lookup a m)
          >>= Map.lookup b
      ≡⟨ cong (_>>= Map.lookup b) (sym (prop-if-eq-subst a ai (λ o → Map.lookup o m >>= fun) (Map.lookup a m) (λ eq → cong ((_>>= fun)) (Map.prop-lookup-eq a ai m eq)))) ⟩
        (if (a == ai) then (Map.lookup a m >>= fun) else Map.lookup a m)
          >>= Map.lookup b
      ≡⟨ prop-if-apply (a == ai) (Map.lookup a m >>= fun) (Map.lookup a m) (_>>= Map.lookup b) ⟩
        (if (a == ai)
          then ((Map.lookup a m >>= fun) >>= Map.lookup b)
          else (Map.lookup a m >>= Map.lookup b)
        )
      ≡⟨⟩
        (if (a == ai)
          then ((Map.lookup a m >>= fun) >>= Map.lookup b)
          else lookup2 a b m
        )
      ≡⟨ cong (λ o → if (a == ai) then o else lookup2 a b m) (lem1 m) ⟩
        (if (a == ai)
          then (if b == bi then Nothing else (Map.lookup a m >>= Map.lookup b))
          else lookup2 a b m
        )
      ≡⟨⟩
        (if (a == ai)
          then (if b == bi then Nothing else (lookup2 a b m))
          else lookup2 a b m
        )
      ≡⟨ prop-if-nested {Maybe V} (a == ai) (b == bi) Nothing (lookup2 a b m) ⟩
        (if a == ai && b == bi then Nothing else lookup2 a b m)
      ∎

--
@0 prop-lookup2-delete2s
  : {A B V : Set} {{_ : Ord A}} → {{_ : Ord B}}
  → ∀ (a : A) (b : B) (as : List A) (bi : B) (m : Map A (Map B V))
  → lookup2 a b (delete2s as bi m)
    ≡ (if elem a as && b == bi then Nothing else lookup2 a b m)
--
prop-lookup2-delete2s a b [] bi m = refl
prop-lookup2-delete2s a b (x ∷ xs) bi m =
    begin
      lookup2 a b (delete2s (x ∷ xs) bi m)
    ≡⟨⟩
      lookup2 a b (delete2 x bi (delete2s xs bi m))
    ≡⟨ prop-lookup2-delete2 a b x bi _ ⟩
      (if a == x && b == bi then Nothing else lookup2 a b (delete2s xs bi m))
    ≡⟨ cong (λ o → if a == x && _ then Nothing else o) (prop-lookup2-delete2s a b xs bi m) ⟩
      (if a == x && b == bi
        then Nothing
        else (if elem a xs && b == bi then Nothing else lookup2 a b m)
      )
    ≡⟨ lem-if-shuffle (a == x) (elem a xs) (b == bi) (lookup2 a b m) ⟩
      (if (a == x || elem a xs) && b == bi then Nothing else lookup2 a b m)
    ≡⟨⟩
      (if elem a (x ∷ xs) && b == bi then Nothing else lookup2 a b m)
    ∎
  where
    lem-if-shuffle
      : ∀ {X : Set} (c1 c2 c3 : Bool) (mv : Maybe X)
      → (if (c1 && c3) then Nothing else (if (c2 && c3) then Nothing else mv))
        ≡ (if (c1 || c2) && c3 then Nothing else mv)
    lem-if-shuffle True True True = λ mv → refl
    lem-if-shuffle True False True = λ mv → refl
    lem-if-shuffle False True True = λ mv → refl
    lem-if-shuffle False False True = λ mv → refl
    lem-if-shuffle True True False = λ mv → refl
    lem-if-shuffle True False False = λ mv → refl
    lem-if-shuffle False True False = λ mv → refl
    lem-if-shuffle False False False = λ mv → refl

--
@0 prop-lookup2-delete2all
  : {A B V : Set} {{_ : Ord A}} → {{_ : Ord B}}
  → ∀ (a : A) (b : B) (as : List A) (bi : B) (m : Map A (Map B V))
  → (elem a as ≡ False → lookup2 a bi m ≡ Nothing)
  → lookup2 a b (delete2s as bi m)
    ≡ (if b == bi then Nothing else lookup2 a b m)
--
prop-lookup2-delete2all a b as bi m conseq =
  case elem a as of λ
    { True {{eq}} →
      begin
        lookup2 a b (delete2s as bi m)
      ≡⟨ prop-lookup2-delete2s a b as bi m ⟩
        (if elem a as && b == bi then Nothing else lookup2 a b m)
      ≡⟨ cong (λ x → if x && _ then _ else _) eq ⟩
        (if b == bi then Nothing else lookup2 a b m)
      ∎
    ; False {{eq}} →
      begin
        lookup2 a b (delete2s as bi m)
      ≡⟨ prop-lookup2-delete2s a b as bi m ⟩
        (if elem a as && b == bi then Nothing else lookup2 a b m)
      ≡⟨ cong (λ x → if x && _ then _ else _) eq ⟩
        lookup2 a b m
      ≡⟨ sym (prop-if-redundant (b == bi) (lookup2 a b m)) ⟩
        (if b == bi then lookup2 a b m else lookup2 a b m)
      ≡⟨ prop-if-eq-subst b bi (λ bx → lookup2 a bx m) (lookup2 a b m) (prop-lookup2-eqB a b bi m) ⟩
       (if b == bi then lookup2 a bi m else lookup2 a b m)
      ≡⟨ cong (λ o → if b == bi then o else lookup2 a b m) (conseq eq) ⟩
        (if b == bi then Nothing else lookup2 a b m)
      ∎
    }

--
prop-lookup2-delete1all
  : {A B V : Set} {{_ : Ord A}} → {{_ : Ord B}}
  → ∀ (a : A) (b : B) (ai : A) (m : Map A (Map B V))
  → lookup2 a b (Map.delete ai m)
    ≡ (if a == ai then Nothing else lookup2 a b m)
--
prop-lookup2-delete1all a b ai m =
  begin
    lookup2 a b (Map.delete ai m)
  ≡⟨⟩
    Map.lookup a (Map.delete ai m) >>= Map.lookup b
  ≡⟨ cong (λ o → o >>= Map.lookup b) (Map.prop-lookup-delete a ai m)⟩
    (if a == ai then Nothing else Map.lookup a m) >>= Map.lookup b
  ≡⟨ prop-if-apply (a == ai) Nothing (Map.lookup a m) (_>>= Map.lookup b) ⟩
    (if a == ai then Nothing else (Map.lookup a m >>= Map.lookup b))
  ≡⟨⟩
    (if a == ai then Nothing else lookup2 a b m)
  ∎

{-----------------------------------------------------------------------------
    PairMap
------------------------------------------------------------------------------}
{-|

The type `PairMap a b v` is essentially the type `Map (a × b) v`,
but with two efficient lookup functions

> lookupA : a → PairMap a b v → Map b v
> lookupB : b → PairMap a b v → Map a v

The property `prop-lookupA-lookupB` states that these lookups
yield the same values.

In the terminology of relational database,
this type stores rows of the form `a × b × v`
and maintains an index on both the first column `a` and the second column `b`.

-}
record PairMap (a b v : Set) {{@0 orda : Ord a}} {{@0 ordb : Ord b}} : Set where
  field
    mab : Map a (Map b v)
    mba : Map b (Map a v)

    @0 invariant-equal
      : ∀ (x : a) (y : b)
      → lookup2 x y mab ≡ lookup2 y x mba

open PairMap public

module _ {a b v : Set} {{_ : Ord a}} {{_ : Ord b}} where
  empty : PairMap a b v
  empty = record
    { mab = Map.empty
    ; mba = Map.empty
    ; invariant-equal = λ x y →
      begin
        Map.lookup x Map.empty >>= Map.lookup y
      ≡⟨ cong (λ m → m >>= _) (Map.prop-lookup-empty x) ⟩
        Nothing >>= Map.lookup y
      ≡⟨⟩
        Nothing
      ≡⟨⟩
        Nothing >>= Map.lookup x
      ≡⟨ sym (cong (λ m → m >>= _) (Map.prop-lookup-empty y)) ⟩
        Map.lookup y Map.empty >>= Map.lookup x
      ∎
    }

  lookupA : a → PairMap a b v → Map b v
  lookupA a = implicitEmpty ∘ Map.lookup a ∘ mab

  lookupB : b → PairMap a b v → Map a v
  lookupB b = implicitEmpty ∘ Map.lookup b ∘ mba

  lookupAB : a → b → PairMap a b v → Maybe v
  lookupAB a b m = Map.lookup a (mab m) >>= Map.lookup b

  insert : a → b → v → PairMap a b v → PairMap a b v
  insert ai bi v m = record
    { mab = insert2 ai bi v (mab m)
    ; mba = insert2 bi ai v (mba m)
    ; invariant-equal = λ al bl →
        begin
          lookup2 al bl (insert2 ai bi v (mab m))
        ≡⟨ prop-lookup2-insert2 al ai bl bi v (mab m) ⟩
          (if al == ai && bl == bi then Just v else lookup2 al bl (mab m))
        ≡⟨ cong (λ x → if x then _ else _) (&&-sym (al == ai) (bl == bi)) ⟩
          (if bl == bi && al == ai then Just v else lookup2 al bl (mab m))
        ≡⟨ cong (λ x → if bl == bi && _ then _ else x) (invariant-equal m al bl) ⟩
          (if bl == bi && al == ai then Just v else lookup2 bl al (mba m))
        ≡⟨ sym (prop-lookup2-insert2 bl bi al ai v (mba m)) ⟩
          lookup2 bl al (insert2 bi ai v (mba m))
        ∎
    }

  deleteA : a → PairMap a b v → PairMap a b v
  deleteA ai m = record
      { mab = Map.delete ai (mab m)
      ; mba = delete2s bs ai (mba m)
      ; invariant-equal = λ al bl →
        begin
          lookup2 al bl (Map.delete ai (mab m))
        ≡⟨ prop-lookup2-delete1all al bl ai (mab m) ⟩
          (if al == ai then Nothing else lookup2 al bl (mab m))
        ≡⟨ cong (λ x → if al == ai then Nothing else x) (invariant-equal m al bl) ⟩
          (if al == ai then Nothing else lookup2 bl al (mba m))
        ≡⟨ sym (prop-lookup2-delete2all bl al bs ai (mba m) (lem1 bl)) ⟩
          lookup2 bl al (delete2s bs ai (mba m))
        ∎
      }
    where
      bs : List b
      bs = Map.keys (implicitEmpty (Map.lookup ai (mab m)))

      @0 lem1
        : ∀ (y : b)
        → elem y bs ≡ False → lookup2 y ai (mba m) ≡ Nothing
      lem1 y eq-elem =
        begin
          lookup2 y ai (mba m)
        ≡⟨ sym (invariant-equal m ai y) ⟩
          lookup2 ai y (mab m)
        ≡⟨⟩
          Map.lookup ai (mab m) >>= Map.lookup y
        ≡⟨ prop-implicitEmpty-bind y (Map.lookup ai (mab m)) ⟩
          Map.lookup y (implicitEmpty (Map.lookup ai (mab m)))
        ≡⟨ prop-elem-keys y (implicitEmpty (Map.lookup ai (mab m))) eq-elem ⟩
          Nothing
        ∎

  withoutKeysA : PairMap a b v → ℙ a → PairMap a b v
  withoutKeysA m0 xs = foldl' (λ m x → deleteA x m) m0 xs

  @0 prop-lookupA-lookupB
    : ∀ (x : a) (y : b) (m : PairMap a b v)
    → Map.lookup y (lookupA x m)
      ≡ Map.lookup x (lookupB y m)
  prop-lookupA-lookupB x y m =
    begin
      Map.lookup y (lookupA x m)
    ≡⟨ sym (prop-implicitEmpty-bind y (Map.lookup x (mab m))) ⟩
      lookup2 x y (mab m)
    ≡⟨ invariant-equal m x y ⟩
      lookup2 y x (mba m)
    ≡⟨ prop-implicitEmpty-bind x (Map.lookup y (mba m)) ⟩
      Map.lookup x (lookupB y m)
    ∎

{-# COMPILE AGDA2HS PairMap #-}
{-# COMPILE AGDA2HS empty #-}
{-# COMPILE AGDA2HS lookupA #-}
{-# COMPILE AGDA2HS lookupB #-}
{-# COMPILE AGDA2HS lookupAB #-}
{-# COMPILE AGDA2HS insert #-}
{-# COMPILE AGDA2HS deleteA #-}
{-# COMPILE AGDA2HS withoutKeysA #-}
