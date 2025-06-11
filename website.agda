module website where

import Data.List as L
open L using (List; _++_; []; _∷_; [_])
import Data.Maybe as Maybe
open Maybe using (Maybe; just; nothing; _<∣>_)
import Data.String as S
open S using (String; _==_)
import Data.Bool as B
open B using (Bool; if_then_else_)
open import Function.Base using (id; _∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong; sym; trans; refl)
open import Data.Product hiding (map)
open import Data.Unit using (⊤; tt)

private
  variable
    a b c d : Set

module spec where

  Website : Set → Set → Set
  Website a b = a → b
  
  const : b → Website a (Maybe b)
  const x = λ _ → just x
  
  map : (b → c) → Website a b → Website a c
  map f w = f ∘ w
  
  map2 : (b → c → d) → Website a b → Website a c → Website a d
  map2 f w₁ w₂ = λ x → f (w₁ x) (w₂ x)

  URL : Set
  URL = List String

  empty-url : URL
  empty-url = []

  -- url== : URL -> URL -> Bool
  -- url== [] [] = B.true
  -- url== [] (_ ∷ _) = B.false
  -- url== (_ ∷ _) [] = B.false
  -- url== (x ∷ xs) (y ∷ ys) = (x == y) ∧ (url== xs ys)
  
  empty : Website a (Maybe b)
  empty = λ _ → nothing
  
  or : Website a (Maybe b) → Website a (Maybe b) → Website a (Maybe b)
  or ws₁ ws₂ = λ x → ws₁ x <∣> ws₂ x
  
  seg : String → Website URL (Maybe a) → Website URL (Maybe a)
  seg s w [] = nothing
  seg s w (s' ∷ url) = if s == s' then w url else nothing
  
  
  -- A few example websites
  ex1 : Website URL (Maybe String)
  ex1 = const "Hello World"
  
  ex2 : Website URL (Maybe String)
  ex2 = const "Bye bye"
  
  ex3 : Website URL (Maybe String)
  ex3 = or (seg "foo" ex1)
           (seg "bar" ex2)
  
  data Markdown : Set where
    s : String -> Markdown
    # : Markdown -> Markdown
    ## : Markdown -> Markdown
    ** : String -> Markdown
    _<>_ : Markdown -> Markdown -> Markdown
  
  data HTML : Set where
    s : String -> HTML
    h1 : HTML -> HTML
    h2 : HTML -> HTML
    strong : String -> HTML
    _<>_ : HTML -> HTML -> HTML
    
  markdown->html : Markdown -> HTML
  markdown->html (s x) = s x
  markdown->html (# x) = h1 (markdown->html x)
  markdown->html (## x) = h2 (markdown->html x)
  markdown->html (** x) = strong x
  markdown->html (x <> y) = markdown->html x <> markdown->html y
  
  case : List (String × Website URL (Maybe a)) -> Website URL (Maybe a)
  case [] = empty
  case (( st , w ) ∷ cases) = or (seg st w) (case cases)
  
  ex4 : Website URL (Maybe Markdown)
  ex4 = case (( "hi" , const (# ((s "Hello ") <> (** "Lambda Days")))) ∷
              ( "bye" , const (s "Bye") ) ∷
              ( "about" , const (s "Nice website") ) ∷
              [])
  
  ex5 : Website URL (Maybe HTML)
  ex5 = map (Maybe.map markdown->html) ex4
  
  
  
  -- sampling
  
  module URLMap where
  
    data URLMap (a : Set) : Set where
      emp : URLMap a
      assoc : (k : URL) -> (v : a) -> URLMap a -> URLMap a
  
    keys : {a : Set} -> URLMap a -> List URL
    keys emp = []
    keys (assoc k _ mp) = k ∷ (keys mp)
  
    approximates : {a : Set} -> (URL -> a) -> URLMap a -> Set
    approximates f emp = ⊤
    approximates f (assoc k v mp) = v ≡ f k × approximates f mp
  
    -- app : {a : Set ℓ} -> {m : M a} -> SMap m -> String -> Maybe a
    -- app empty k = nothing
    -- app (assoc k' v m') k = if k' == k then just v else app m' k
  
  open URLMap
  
  sample : (f : URL -> a) -> (urls : List URL) -> URLMap a
  sample f [] = emp
  sample f (url ∷ urls) = assoc url (f url) (sample f urls)
  
  
  -- and we're done ... ?
  
  -- Where do the sampling points come from?
  -- The website itself can give us hints as to where interesting sampling points are
  -- In order to be able to do that, we have to reflect the website functions as data
  
  

module impl where

  data WS : {spec.Website a b} -> Set₁ where
    -- const x = λ _ -> just x
    const : (x : b) -> WS {a} {Maybe b} {spec.const x}
    -- map f w = f ∘ w
    map : {g : spec.Website a b} ->
          (f : b -> c) -> WS {a} {b} {g} -> WS {a} {c} {spec.map f g}
    -- map2 f w₁ w₂ = λ x -> f (w₁ x) (w₂ x)
    map2 : {g : spec.Website a b} -> {h : spec.Website a c}
           -> (f : b -> c -> d)
           -> WS {a} {b} {g}
           -> WS {a} {c} {h}
           -> WS {a} {d} {spec.map2 f g h}
    -- empty = λ _ -> nothing
    empty : WS {a} {Maybe b} {spec.empty}
    -- or ws₁ ws₂ = λ x -> ws₁ x <∣> ws₂ x
    or : {f g : spec.Website a (Maybe b)}
         -> WS {a} {Maybe b} {f}
         -> WS {a} {Maybe b} {g}
         -> WS {a} {Maybe b} {spec.or f g}
    -- seg s w [] = nothing
    -- seg s w (s' ∷ url) = if s == s' then w url else nothing
    seg : {f : spec.Website spec.URL (Maybe a)}
          -> (s : String)
          -> WS {spec.URL} {Maybe a} {f}
          -> WS {spec.URL} {Maybe a} {spec.seg s f}

  run : {f : spec.Website a b} -> WS {a} {b} {f} -> (a -> b)
  run (const x) _ = just x
  run (map f x) a = f (run x a)
  run (map2 f w₁ w₂) a = f (run w₁ a) (run w₂ a)
  run empty x = nothing
  run (or w₁ w₂) x = run w₁ x <∣> run w₂ x
  run (seg s w) [] = nothing
  run (seg s w) (s' ∷ url) = if s == s' then run w url else nothing

  -- run' : {a b : Set} -> {f : spec.Website a b} -> WS f -> ∃ λ (f' : a -> b) -> f' ≗ f
  -- run' (const x) = run (const x) , λ s -> refl
  -- run' (map f x) = run (map f x) , λ s → cong f {!!}
  -- run' (map2 f x x₁) = {!!}
  -- run' empty = {!!}
  -- run' (or x x₁) = {!!}
  -- run' (seg s x) = {!!}

  sugg : {f : spec.Website spec.URL b}
         -> WS {spec.URL} {b} {f}
         -> List spec.URL
  sugg (const x) = [ spec.empty-url ]
  sugg (map _ w) = sugg w
  sugg (map2 f w₁ w₂) = sugg w₁ ++ sugg w₂
  sugg empty = [ spec.empty-url ]
  sugg (or w₁ w₂) = sugg w₁ ++ sugg w₂
  sugg (seg s w) = L.map (s ∷_) (sugg w)

  open spec.URLMap

  render : {f : spec.Website spec.URL b}
           -> WS {spec.URL} {b} {f}
           -> URLMap b
  render w = spec.sample (run w) (sugg w)

  unwrap : URLMap (Maybe a) -> URLMap a
  unwrap emp = emp
  unwrap (assoc k (just x) m) = assoc k x (unwrap m)
  unwrap (assoc k nothing m) = (unwrap m)

  render' : {f : spec.Website spec.URL (Maybe b)}
            -> WS {spec.URL} {Maybe b} {f}
            -> URLMap b
  render' w = unwrap (spec.sample (run w) (sugg w))

ex1' : impl.WS {spec.URL}
ex1' = impl.const "Hello World"

ex2' : impl.WS {spec.URL}
ex2' = impl.const "Bye bye"

ex3' : impl.WS
ex3' = impl.or (impl.seg "foo" ex1')
               (impl.seg "bar" ex2')

open spec.URLMap

ex1'r : URLMap String
ex1'r = impl.render' ex1'

ex2'r : URLMap String
ex2'r = impl.render' ex2'

ex1't : ex1'r ≡ assoc [] "Hello World" emp
ex1't = refl

ex3'r : URLMap String
ex3'r = impl.render' ex3'

ex3't : ex3'r ≡ assoc [ "foo" ] "Hello World"
               (assoc [ "bar" ] "Bye bye"
                emp)
ex3't = refl

