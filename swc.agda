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

open ≡-Reasoning

private
  variable
    ℓ₁ : Level
    ℓ₂ : Level
    k : Set ℓ₁
    v : Set ℓ₂

-- Equality

Eq : Set ℓ₁ -> Set ℓ₁
Eq a = a -> a -> B.Bool

-- URLs

URL : Set
URL = List String

url= : Eq URL
url= [] [] = B.true
url= [] (x ∷ u2) = B.false
url= (x ∷ u1) [] = B.false
url= (x ∷ u1) (y ∷ u2) = (x == y) ∧ (url= u1 u2)

-- Default maps

data Dmap (k : Set ℓ₁) (v : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  default : v -> Dmap k v
  assoc : k -> v -> Dmap k v -> Dmap k v

sem-dmap : Eq k -> Dmap k v -> (k -> v)
sem-dmap eq (default v) = λ _ -> v
sem-dmap eq (assoc k v dm) k' = if (eq k k')
                                  then v
                                  else sem-dmap eq dm k'

-- Functor:

fmap : {a b : Set ℓ₂} -> (a -> b) -> (Dmap k a -> Dmap k b)
fmap f (default v) = (default (f v))
fmap f (assoc k v dm) = (assoc k (f v) (fmap f dm))

dmap-id : (dm : Dmap k v) -> (fmap id) dm ≡ (id dm)
dmap-id (default v) = refl
dmap-id (assoc k v dm') = begin
  (fmap id) (assoc k v dm')
    ≡⟨⟩
  assoc k v (fmap id dm')
    ≡⟨ cong (assoc k v) (dmap-id dm') ⟩
  assoc k v dm'
  ∎

dmap-comp : {a b c : Set} (f : b -> c) (g : a -> b) (dm : Dmap k a) -> fmap (f ∘ g) dm ≡ (fmap f ∘ fmap g) dm
dmap-comp f g (default v) = refl
dmap-comp f g (assoc k v dm') = begin
  fmap (f ∘ g) (assoc k v dm')
    ≡⟨⟩
  (assoc k ((f ∘ g) v) (fmap (f ∘ g) dm'))
    ≡⟨ cong (assoc k ((f ∘ g) v)) (dmap-comp f g dm') ⟩
  (assoc k ((f ∘ g) v) ((fmap f ∘ fmap g) dm'))
    ≡⟨⟩
  (fmap f ∘ fmap g) (assoc k v dm')
  ∎

-- Applicative:

pure : v -> Dmap k v
pure = default

ap : {a b : Set ℓ₂} -> Eq k -> Dmap k (a -> b) -> Dmap k a -> Dmap k b
ap eq (default f) dmx = fmap f dmx
ap eq (assoc k f dmf) dmx = assoc k (f (sem-dmap eq dmx k)) (ap eq dmf dmx)

ap-identity : {a : Set ℓ₂} -> (eq : Eq k) -> ∀ (dm : Dmap k a) -> ap eq (pure id) dm ≡ dm
ap-identity eq (default x) = refl
ap-identity eq (assoc k v dm') = begin
  ap eq (pure id) (assoc k v dm')
    ≡⟨⟩
  fmap id (assoc k v dm')
    ≡⟨⟩
  (assoc k (id v) (fmap id dm'))
    ≡⟨⟩
  (assoc k v (fmap id dm'))
    ≡⟨ cong (assoc k v) (dmap-id dm') ⟩
  (assoc k v dm')
  ∎

-- TODO: ap-comp, ap-hom, ap-interchange

liftA2 : {a b c : Set ℓ₂} -> Eq k -> (a -> b -> c) -> Dmap k a -> Dmap k b -> Dmap k c
liftA2 eq f x y = (ap eq ((fmap f) x) y)

-- Alternative:

empty : {a : Set ℓ₂} -> Dmap k (Maybe.Maybe a)
empty = default Maybe.nothing

or : {a : Set ℓ₂} → Eq k → Dmap k (Maybe.Maybe a) → Dmap k (Maybe.Maybe a) → Dmap k (Maybe.Maybe a)
or eq = liftA2 eq _<∣>_

-- Web DSL is just Dmap String (Maybe.Maybe a)

Web : Set -> Set
Web a = Dmap URL (Maybe.Maybe a)

sem-web = sem-dmap

-----------

data Map (k : Set ℓ₁) (v : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  leer : Map k v
  assoc : k -> v -> Map k v -> Map k v

sem-map : Eq k -> Map k v -> (k -> Maybe.Maybe v)
sem-map eq leer _ = nothing
sem-map eq (assoc k v m) k' = if eq k k'
                                then just v
                                else sem-map eq m k'


-- Compilation / Downsampling

compile : {a : Set} -> Web a -> Map URL a
compile (default (just x)) = assoc [] x leer
compile (default nothing) = leer
compile (assoc k (just x) w) = assoc k x (compile w)
compile (assoc k nothing w) = compile w

compile-correct : {a : Set} -> (w : Web a) (url : URL) (res : a) -> sem-map url= (compile w) url ≡ just res -> sem-web url= w url ≡ just res
compile-correct (default (just d)) [] res x = begin
  sem-web url= (default (just d)) []
    ≡⟨⟩
  just d
    ≡⟨⟩
  (if url= [] [] then just d else nothing)
    ≡⟨ x ⟩
  just res
  ∎
compile-correct (default (just d)) (seg ∷ url) res x = {!!}
compile-correct (assoc x₁ x₂ w) url res x = {!!}

-- compile-correct : {a : Set} -> ∀ (w : Web a) (url : String) -> (sem-map (compile w)) url ≡ sem-web w url
-- compile-correct = {!!}
