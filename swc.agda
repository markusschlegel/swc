module swc where

open import Level using (Level; suc; _⊔_)
import Data.List as L
open L using (List; []; _∷_)
import Data.Maybe as Maybe
open Maybe using (Maybe; just; nothing; _<∣>_)
import Data.String as S
open S using (String; _==_)
import Data.Bool as B
open B using (if_then_else_; _∧_)
open import Function.Base using (id; _∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong; refl; module ≡-Reasoning)
  public


private
  variable
    ℓ₁ : Level
    ℓ₂ : Level
    k : Set ℓ₁
    v : Set ℓ₂

Eq : Set ℓ₁ -> Set ℓ₁
Eq a = a -> a -> B.Bool

module Dmap where

  data Dmap (k : Set ℓ₁) (v : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
    default : v -> Dmap k v
    assoc : k -> v -> Dmap k v -> Dmap k v

  denotation : Eq k -> Dmap k v -> (k -> v)
  denotation eq (default v) = λ _ -> v
  denotation eq (assoc k v dm) k' = if (eq k k')
                                    then v
                                    else denotation eq dm k'

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

  ap : {a b : Set ℓ₂} -> Eq k -> Dmap k (a -> b) -> Dmap k a -> Dmap k b
  ap eq (default f) dmx = map f dmx
  ap eq (assoc k f dmf) dmx = assoc k (f (denotation eq dmx k)) (ap eq dmf dmx)

  ap-id : {a : Set ℓ₂} -> (eq : Eq k) -> ∀ (dm : Dmap k a) -> ap eq (pure id) dm ≡ dm
  ap-id eq (default x) = refl
  ap-id eq (assoc k v dm') = begin
    ap eq (pure id) (assoc k v dm')
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

  liftA2 : {a b c : Set ℓ₂} -> Eq k -> (a -> b -> c) -> Dmap k a -> Dmap k b -> Dmap k c
  liftA2 eq f x y = (ap eq ((map f) x) y)

  -- Alternative:

  empty : {a : Set ℓ₂} -> Dmap k (Maybe.Maybe a)
  empty = default Maybe.nothing

  or : {a : Set ℓ₂} → Eq k → Dmap k (Maybe.Maybe a) → Dmap k (Maybe.Maybe a) → Dmap k (Maybe.Maybe a)
  or eq = liftA2 eq _<∣>_


module Web where

  open Dmap public hiding (denotation)

  URL : Set
  URL = List String

  url= : Eq URL
  url= [] [] = B.true
  url= [] (x ∷ u2) = B.false
  url= (x ∷ u1) [] = B.false
  url= (x ∷ u1) (y ∷ u2) = (x == y) ∧ (url= u1 u2)

  Web : Set -> Set
  Web a = Dmap URL (Maybe.Maybe a)

  denotation = Dmap.denotation




-----------

-- A quick implementation of associative maps

module Map where

  data Map (k : Set ℓ₁) (v : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
    empty : Map k v
    assoc : k -> v -> Map k v -> Map k v

  denotation : Eq k -> Map k v -> (k -> Maybe.Maybe v)
  denotation eq empty _ = nothing
  denotation eq (assoc k v m) k' = if eq k k'
                                     then just v
                                     else denotation eq m k'


-- Compilation / Downsampling

compile : {a : Set} -> Web.Web a -> Map.Map Web.URL a
compile (Web.default (just x)) = Map.assoc [] x Map.empty
compile (Web.default nothing) = Map.empty
compile (Web.assoc k (just x) w) = Map.assoc k x (compile w)
compile (Web.assoc k nothing w) = compile w

compile-correct-alternative-1 : {a : Set} -> (w : Web.Web a) (url : Web.URL) (res : a) -> Map.denotation Web.url= (compile w) url ≡ just res -> Web.denotation Web.url= w url ≡ just res
compile-correct-alternative-1 = {!!}

compile-correct-alternative-2 : {a : Set} -> ∀ (w : Web.Web a) (url : Web.URL) -> (Map.denotation Web.url= (compile w)) url ≡ Web.denotation Web.url= w url
compile-correct-alternative-2 = {!!}
