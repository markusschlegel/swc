module website where

import Data.List as L
open L using (List; _++_; []; _∷_; [_])
import Data.Maybe as Maybe
open Maybe using (Maybe; just; nothing; _<∣>_)
open import Data.String using (String; _==_; _≟_)
import Data.Bool as B
open B using (Bool; if_then_else_; _∧_)
open import Function.Base using (id; _∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≗_; cong; sym; trans; refl)
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no)

private
  variable
    a b c d : Set

---

is-just : Maybe a -> Set
is-just (just _) = ⊤
is-just nothing = ⊥

module PathMap where

  -- A PathMap denotes a partial function from Path to a

  Path : Set
  Path = List String

  empty-path : Path
  empty-path = []

  path-eq : (x : Path) → (y : Path) → Dec (x ≡ y)
  path-eq = {!!}

  assocd : Path -> a -> (Path -> Maybe a) -> (Path -> Maybe a)
  assocd k v f k' with path-eq k k'
  ... | yes _ = just v
  ... | no _  = f k'

  data PathMap (a : Set) : (Path -> Maybe a) -> Set where
    emp : PathMap a (λ _ -> nothing)
    assoc : (k : Path)
            → (v : a)
            → {f : Path -> Maybe a}
            -> PathMap a f
            → PathMap a (assocd k v f)

  -- run extracts the denotation
  run : {f : Path -> Maybe a} -> PathMap a f -> ∃ λ (f' : Path -> Maybe a) -> f' ≗ f
  run = {!!}

  -- the domain where the partial function is defined
  dom : {f : Path -> Maybe a} -> PathMap a f -> (Path -> Set) -- List Path
  dom emp _ = ⊥
  dom (assoc k _ m) p = p ≡ k ⊎ dom m p

  -- every path in dom is associated with a just
  dom-is-domain-1 : {f : Path -> Maybe a} -> (m : PathMap a f) -> (p : Path) -> (dom m p) -> is-just (f p)
  dom-is-domain-1 (assoc k v m') p x with path-eq k p
  ... | yes _ = tt
  dom-is-domain-1 (assoc k v m') p (inj₁ p≡k) | no ¬k≡p = ⊥-elim (¬k≡p (sym p≡k))
  dom-is-domain-1 (assoc k v m') p (inj₂ y)   | no _      = dom-is-domain-1 m' p y

  -- every just is associated with dom
  dom-is-domain-2 : {f : Path -> Maybe a} -> (m : PathMap a f) -> (p : Path) -> is-just (f p) -> (dom m p)
  dom-is-domain-2 (assoc k v m') p x with path-eq k p
  ... | yes pr = inj₁ (sym pr)
  ... | no pr = inj₂ (dom-is-domain-2 m' p x)

  -- a sampling at exactly the given paths
  sample : (f : Path → a) → (ps : List Path) → {f' : Path -> Maybe a} -> (∃ λ (m : PathMap a f') -> (p : Path) -> dom m p -> f' p ≡ just (f p))
  sample = {!!}

---

module spec where

  open PathMap hiding (run)

  Website : Set → Set → Set
  Website a b = a → b
  
  const : b → Website a (Maybe b)
  const x = λ _ → just x
  
  map : (b → c) → Website a b → Website a c
  map f w = f ∘ w
  
  map2 : (b → c → d) → Website a b → Website a c → Website a d
  map2 f w₁ w₂ = λ x → f (w₁ x) (w₂ x)

  empty : Website a (Maybe b)
  empty = λ _ → nothing
  
  or : Website a (Maybe b) → Website a (Maybe b) → Website a (Maybe b)
  or ws₁ ws₂ = λ x → ws₁ x <∣> ws₂ x
  
  seg : String → Website Path (Maybe a) → Website Path (Maybe a)
  seg s w [] = nothing
  seg s w (s' ∷ url) = if s == s' then w url else nothing
  
---

module impl where

  open PathMap hiding (run)

  data WS : {spec.Website a b} → Set₁ where
    -- const x = λ _ → just x
    const : (x : b) → WS {a} {Maybe b} {spec.const x}
    -- map f w = f ∘ w
    map : {g : spec.Website a b} →
          (f : b → c) → WS {a} {b} {g} → WS {a} {c} {spec.map f g}
    -- map2 f w₁ w₂ = λ x → f (w₁ x) (w₂ x)
    map2 : {g : spec.Website a b} → {h : spec.Website a c}
           → (f : b → c → d)
           → WS {a} {b} {g}
           → WS {a} {c} {h}
           → WS {a} {d} {spec.map2 f g h}
    -- empty = λ _ → nothing
    empty : WS {a} {Maybe b} {spec.empty}
    -- or ws₁ ws₂ = λ x → ws₁ x <∣> ws₂ x
    or : {f g : spec.Website a (Maybe b)}
         → WS {a} {Maybe b} {f}
         → WS {a} {Maybe b} {g}
         → WS {a} {Maybe b} {spec.or f g}
    -- seg s w [] = nothing
    -- seg s w (s' ∷ url) = if s == s' then w url else nothing
    seg : {f : spec.Website Path (Maybe a)}
          → (s : String)
          → WS {Path} {Maybe a} {f}
          → WS {Path} {Maybe a} {spec.seg s f}

  run : {f : spec.Website a b} → WS {a} {b} {f} → (a → b)
  run (const x) _ = just x
  run (map f x) a = f (run x a)
  run (map2 f w₁ w₂) a = f (run w₁ a) (run w₂ a)
  run empty x = nothing
  run (or w₁ w₂) x = run w₁ x <∣> run w₂ x
  run (seg s w) [] = nothing
  run (seg s w) (s' ∷ url) = if s == s' then run w url else nothing

  -- run' : {a b : Set} → {f : spec.Website a b} → WS f → ∃ λ (f' : a → b) → f' ≗ f
  -- run' (const x) = run (const x) , λ s → refl
  -- run' (map f x) = run (map f x) , λ s → cong f {!!}
  -- run' (map2 f x x₁) = {!!}
  -- run' empty = {!!}
  -- run' (or x x₁) = {!!}
  -- run' (seg s x) = {!!}

  sugg : {f : spec.Website Path b}
         → WS {Path} {b} {f}
         → List Path
  sugg (const x) = [ empty-path ]
  sugg (map _ w) = sugg w
  sugg (map2 f w₁ w₂) = sugg w₁ ++ sugg w₂
  sugg empty = [ empty-path ]
  sugg (or w₁ w₂) = sugg w₁ ++ sugg w₂
  sugg (seg s w) = L.map (s ∷_) (sugg w)

  -- render : {f : spec.Website Path b}
  --          → WS {Path} {b} {f}
  --          → PathMap b
  -- render w = sample (run w) (sugg w)

  -- unwrap : PathMap (Maybe a) → PathMap a
  -- unwrap emp = emp
  -- unwrap (assoc k (just x) m) = assoc k x (unwrap m)
  -- unwrap (assoc k nothing m) = (unwrap m)

  -- render' : {f : spec.Website Path (Maybe b)}
  --           → WS {Path} {Maybe b} {f}
  --           → PathMap b
  -- render' w = unwrap (sample (run w) (sugg w))
