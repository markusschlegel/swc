module swc where

open import Level using (Level; suc; _⊔_)
import Data.List as L
open L using (List; []; _∷_)
import Data.Maybe as Maybe
open Maybe using (Maybe; just; nothing; _<∣>_)
import Data.String as S
open S using (String; _==_)
import Data.Bool as B
open B using (Bool; if_then_else_; _∧_)
open import Function.Base using (id; _∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong; refl; module ≡-Reasoning)
  public


private
  variable
    ℓ : Level
    ℓ₁ : Level
    ℓ₂ : Level
    k : Set ℓ₁
    v : Set ℓ₂

record Eq (a : Set ℓ) : Set ℓ where
  field
    equal? : a -> a -> Bool

open Eq {{...}}

record Monoid (a : Set ℓ) : Set ℓ where
  field
    mempty : a
    _<>_ : a -> a -> a

open Monoid {{...}}

module Dmap where

  data Dmap (k : Set ℓ₁) (v : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
    default : v -> Dmap k v
    assoc : k -> v -> Dmap k v -> Dmap k v


  denotation : {{Eq k}} -> Dmap k v -> (k -> v)
  denotation (default v) = λ _ -> v
  denotation (assoc k v dm) k' = if (equal? k k')
                                    then v
                                    else denotation dm k'

  -- Functor:

  map : {a b : Set ℓ₂} -> (a -> b) -> (Dmap k a -> Dmap k b)
  map f (default v) = (default (f v))
  map f (assoc k v dm) = (assoc k (f v) (map f dm))

  open ≡-Reasoning

  map-id : (dm : Dmap k v) -> (map id) dm ≡ (id dm)
  map-id (default v) = refl
  map-id (assoc k v dm') = begin
    (map id) (assoc k v dm')
      ≡⟨⟩
    assoc k v (map id dm')
      ≡⟨ cong (assoc k v) (map-id dm') ⟩
    assoc k v dm'
    ∎

  map-comp : {a b c : Set} (f : b -> c) (g : a -> b) (dm : Dmap k a) -> map (f ∘ g) dm ≡ (map f ∘ map g) dm
  map-comp f g (default v) = refl
  map-comp f g (assoc k v dm') = begin
    map (f ∘ g) (assoc k v dm')
      ≡⟨⟩
    (assoc k ((f ∘ g) v) (map (f ∘ g) dm'))
      ≡⟨ cong (assoc k ((f ∘ g) v)) (map-comp f g dm') ⟩
    (assoc k ((f ∘ g) v) ((map f ∘ map g) dm'))
      ≡⟨⟩
    (map f ∘ map g) (assoc k v dm')
    ∎

  -- Applicative:

  pure : v -> Dmap k v
  pure = default

  ap : {a b : Set ℓ₂} -> {{Eq k}} -> Dmap k (a -> b) -> Dmap k a -> Dmap k b
  ap (default f) dmx = map f dmx
  ap (assoc k f dmf) dmx = assoc k (f (denotation dmx k)) (ap dmf dmx)

  ap-id : {a : Set ℓ₂} -> {{eq : Eq k}} -> ∀ (dm : Dmap k a) -> ap (pure id) dm ≡ dm
  ap-id (default x) = refl
  ap-id (assoc k v dm') = begin
    ap (pure id) (assoc k v dm')
      ≡⟨⟩
    map id (assoc k v dm')
      ≡⟨⟩
    (assoc k (id v) (map id dm'))
      ≡⟨⟩
    (assoc k v (map id dm'))
      ≡⟨ cong (assoc k v) (map-id dm') ⟩
    (assoc k v dm')
    ∎

  -- TODO: ap-comp, ap-hom, ap-interchange

  liftA2 : {a b c : Set ℓ₂} -> {{Eq k}} -> (a -> b -> c) -> Dmap k a -> Dmap k b -> Dmap k c
  liftA2 f x y = (ap ((map f) x) y)

  -- Alternative:

  empty : {a : Set ℓ₂} -> Dmap k (Maybe a)
  empty = default Maybe.nothing

  or : {a : Set ℓ₂} → {{Eq k}} → Dmap k (Maybe a) → Dmap k (Maybe a) → Dmap k (Maybe a)
  or = liftA2 _<∣>_


-- For the current discussion you can skip the `Web` module.
-- It's just one more layer, which we can argue about later.

module Web where

  URL : Set
  URL = List String

  url= : URL -> URL -> Bool
  url= [] [] = B.true
  url= [] (x ∷ u2) = B.false
  url= (x ∷ u1) [] = B.false
  url= (x ∷ u1) (y ∷ u2) = (x == y) ∧ (url= u1 u2)

  instance
    URLEq : Eq URL
    URLEq = record { equal? = url= }

    URLMonoid : Monoid URL
    URLMonoid = record { mempty = []; _<>_ = L._++_}

  -- The Web language is almost just the free construction of
  -- applicative alternative functor.  There's one additional
  -- constructor `seg`
  data Web (a : Set ℓ₁) : Set (suc ℓ₁) where
    empty : Web a
    pure : a -> Web a
    map : {b : Set} -> (b -> a) -> Web b -> Web a
    ap : {b : Set} -> Web (b -> a) -> Web b -> Web a
    or : Web a -> Web a -> Web a
    -- match against a single URL segment
    seg : String -> Web a -> Web a


  dmap-shift : {a : Set} -> {{Monoid k}} -> (k -> k) -> Dmap.Dmap k (Maybe a) -> Dmap.Dmap k (Maybe a)
  dmap-shift f (Dmap.default x) = Dmap.assoc (f mempty) x (Dmap.default nothing)
  dmap-shift f (Dmap.assoc k v dm) = Dmap.assoc (f k) v (dmap-shift f dm)

  as-dmap : {a : Set} -> Web a -> Dmap.Dmap URL (Maybe a)
  as-dmap empty = Dmap.empty
  as-dmap (pure x) = Dmap.pure (just x)
  as-dmap (map f w) = Dmap.map (Maybe.map f) (as-dmap w)
  as-dmap (ap fw xw) = Dmap.ap (Dmap.map Maybe.ap (as-dmap fw)) (as-dmap xw)
  as-dmap (or w₁ w₂) = Dmap.or (as-dmap w₁) (as-dmap w₂)
  as-dmap (seg s w) = dmap-shift (λ k -> s ∷ k) (as-dmap w)

  denotation : {a : Set} -> Web a -> (URL -> Maybe a)
  denotation w = Dmap.denotation (as-dmap w)




-----------

-- A quick implementation of associative maps

module Map where

  data Map (k : Set ℓ₁) (v : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
    empty : Map k v
    assoc : k -> v -> Map k v -> Map k v

  denotation : {{Eq k}} -> Map k v -> (k -> Maybe v)
  denotation empty _ = nothing
  denotation (assoc k v m) k' = if equal? k k'
                                     then just v
                                     else denotation m k'


-- Compilation / Downsampling

dmap-as-map : {a : Set ℓ} -> {{Eq k}} -> {{Monoid k}} -> Dmap.Dmap k (Maybe a) -> Map.Map k a
-- This is the culprit: I'd really like `default v` to mean `λ _ ->
-- v`, but constant functions cannot be modelled by maps.
-- So here I choose to associate the content `x` with `index.html` effectively.
dmap-as-map (Dmap.default (just x)) = Map.assoc mempty x Map.empty
-- These are all fine:
dmap-as-map (Dmap.default nothing) = Map.empty
dmap-as-map (Dmap.assoc k (just x) dm) = Map.assoc k x (dmap-as-map dm)
dmap-as-map (Dmap.assoc k nothing dm) = dmap-as-map dm

-- This would be the ultimate correctness criterium: The triangle made
-- of Map's denotation, dmap-as-map, and Dmap's denotation commutes.
dmap-correct-1 : {k : Set ℓ₁} ->
                 {v : Set ℓ₂} ->
                 {{eq : Eq k}} ->
                 {{mon : Monoid k}} ->
                 (dm : Dmap.Dmap k (Maybe v)) ->
                 (kv : k) ->
                 Map.denotation (dmap-as-map dm) kv ≡ Dmap.denotation dm kv
dmap-correct-1 = {!!}

-- Compilation of the web DSL is now just a translation to dmap and then to map
compile : {a : Set} -> Web.Web a -> Map.Map Web.URL a
compile = dmap-as-map ∘ Web.as-dmap

-- -- This might be part of a weaker criterium: Whenever we compile to a
-- -- just, the triangle commutes.
-- compile-correct-alternative-2 : {a : Set} -> (w : Web.Web a) (url : Web.URL) (res : a) -> Map.denotation Web.url= (compile w) url ≡ just res -> Web.denotation w url ≡ just res
-- compile-correct-alternative-2 = {!!}
