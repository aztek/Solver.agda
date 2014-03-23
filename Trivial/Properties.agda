module Trivial.Properties where

open import Trivial
open import Formula using (Formula; Interpretation; eval; Solver)
open import Data.Nat
open import Data.Maybe
open import Data.Bool using (true; false)
open import Data.Vec  using (Vec; _∷_; [])
open import Data.List using (List; _∷_; []; _++_; map)
open import Relation.Nullary.Core
open import Relation.Binary.PropositionalEquality
open import Data.Product hiding (map) renaming (_×_ to _⋀_)
open import Data.Bool.Properties using (¬-not)
open import Data.List.Any using (here; there; module Membership-≡)
open Membership-≡ using (_∈_)
open import List.Properties
open import SAT

all-interpretations : ∀ n i → i ∈ interpretations n
all-interpretations 0 [] = here refl
all-interpretations (suc n) (true ∷ i) =
  ∈-++₁ (∈-map (_∷_ true) (all-interpretations n i))
all-interpretations (suc n) (false ∷ i) =
  ∈-++₂ {ys = map (_∷_ true) (interpretations n)}
        (∈-map (_∷_ false) (all-interpretations n i))


stable-search : ∀ n (f : Formula n) is i →
                (∃ λ j → find-model f is ≡ just j ⋀ Model f j) →
                (∃ λ j → find-model f (i ∷ is) ≡ just j ⋀ Model f j)
stable-search 0 _ _ [] ([] , _ , model)
  rewrite model = [] , refl , model
stable-search (suc _) f _ i (j , e , model)
  rewrite e with eval f i | inspect (eval f) i
...            | true     | [ r ] = i , refl , r
...            | false    | [ _ ] = j , refl , model

finds-model : ∀ n (i : Interpretation n) is f →
              i ∈ is → Model f i → ∃ λ j → find-model f is ≡ just j ⋀ Model f j
finds-model 0 [] [] _ () _
finds-model 0 [] ([] ∷ _) _ _ model
  rewrite model = [] , refl , model
finds-model (suc _) .i .(i ∷ is) f (here {i} {is} refl) model
  rewrite model = i , refl , model
finds-model (suc n) j .(i ∷ is) f (there {i} {is} p) model
  rewrite model = stable-search (suc n) f is i
                                (finds-model (suc n) j is f p model)


soundness : ∀ n f → SAT f → ∃ λ i → trivial n f ≡ just i ⋀ Model f i
soundness 0 _ ([] , model)
  rewrite model = [] , refl , model
soundness (suc n) f (true ∷ i , model) =
  finds-model (suc n) (true ∷ i) (interpretations (suc n)) f
              (∈-++₁ (∈-map (_∷_ true) (all-interpretations n i)))
              model
soundness (suc n) f (false ∷ i , model) =
  finds-model (suc n) (false ∷ i) (interpretations (suc n)) f
              (∈-++₂ {ys = map (_∷_ true) (interpretations n)}
                     (∈-map (_∷_ false) (all-interpretations n i)))
              model


¬sat-false : ∀ {n} {f : Formula n} → ¬ SAT f →
             ∀ i → eval f i ≡ false
¬sat-false ¬sat i = ¬-not λ z → ¬sat (i , z)

finds-no-model : ∀ {n} {f : Formula n} → ¬ SAT f →
                 ∀ is → find-model f is ≡ nothing
finds-no-model _ [] = refl
finds-no-model {f = f} ¬sat (i ∷ is)
  rewrite ¬sat-false {f = f} ¬sat i = finds-no-model ¬sat is

completeness : ∀ n f → ¬ SAT f → trivial n f ≡ nothing
completeness 0 f ¬sat
  rewrite ¬sat-false {f = f} ¬sat [] = refl
completeness (suc n) f ¬sat =
  let is = interpretations n
      ts = map (_∷_ true)  is
      fs = map (_∷_ false) is
   in finds-no-model ¬sat (ts ++ fs)

correctness : CorrectSolver trivial
correctness = soundness , completeness
