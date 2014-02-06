module Trivial where

open import Formula using (Formula; Interpretation; eval; Solver)
open import Data.Nat
open import Data.Maybe
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Vec  using (Vec; _∷_; [])
open import Data.List using (List; _∷_; []; _++_; map)

-- Get list of all possible interpretations of n variables (of length 2 ^ n)
interpretations : (n : ℕ) → List (Interpretation n)
interpretations 0 = [] ∷ []
interpretations (suc n) = map (_∷_ true)  (interpretations n) ++
                          map (_∷_ false) (interpretations n) 

-- Check if any of given interpretations satisfies given formula
find-model : {n : ℕ} → Formula n → List (Interpretation n) → Maybe (Interpretation n)
find-model f []       = nothing
find-model f (i ∷ is) = if (eval f i) then (just i) else (find-model f is)

-- Trivial SAT-solver - brute forces all possible interpretations
trivial : Solver
trivial n f = find-model f (interpretations n)

module Properties where
  open import Relation.Nullary.Core
  open import Relation.Binary.PropositionalEquality
  open import Data.Product hiding (map) renaming (_×_ to _∧_)
  open import Data.Bool.Properties
  open import Data.List.Any using (here; there; module Membership-≡)
  open Membership-≡
  open import ListProperties
  open import BoolProperties
  open import SAT

  all-interpretations : ∀ n i → i ∈ interpretations n
  all-interpretations 0 [] = here refl
  all-interpretations (suc n) (true ∷ i) =
    ∈-++₁ (∈-map (_∷_ true) (all-interpretations n i))
  all-interpretations (suc n) (false ∷ i) =
    ∈-++₂ {ys = map (_∷_ true) (interpretations n)}
          (∈-map (_∷_ false) (all-interpretations n i))


  stable-search : ∀ (n : ℕ) (f : Formula n) is i →
                  (∃ λ j → find-model f is ≡ just j ∧ Model f j) →
                  (∃ λ j → find-model f (i ∷ is) ≡ just j ∧ Model f j)
  stable-search 0 f _ [] ([] , _ , true-by e)
    rewrite e = [] , refl , true-by e
  stable-search (suc n) f is i (j , e , model)
    rewrite e = bool-split (eval f i)
                  (λ x → i , if-true x  , true-by x)
                  (λ x → j , if-false x , model)


  finds-model : ∀ (n : ℕ) (i : Interpretation n) is f →
                i ∈ is → Model f i → (∃ λ j → find-model f is ≡ just j ∧ Model f j)
  finds-model 0 [] .([] ∷ xs) _ (here {[]} {xs} px) (true-by e)
    rewrite e = [] , refl , true-by e
  finds-model zero [] .([] ∷ xs) f (there {[]} {xs} x) (true-by e)
    rewrite e = [] , refl , true-by e
  finds-model (suc n) .i .(i ∷ is) f (here {i} {is} refl) (true-by e)
    rewrite e = i , refl , true-by e
  finds-model (suc n) j .(i ∷ is) f (there {i} {is} p) (true-by e)
    rewrite e = stable-search (suc n) f is i
                              (finds-model (suc n) j is f p (true-by e))


  soundness : ∀ n f → SAT f → (∃ λ i → trivial n f ≡ just i ∧ Model f i)
  soundness 0 f (has-model ([] , true-by e))
    rewrite e = [] , refl , true-by e
  soundness (suc n) f (has-model (true ∷ i , model)) =
    finds-model (suc n) (true ∷ i) (interpretations (suc n)) f
                (∈-++₁ (∈-map (_∷_ true) (all-interpretations n i)))
                model
  soundness (suc n) f (has-model (false ∷ i , model)) =
    finds-model (suc n) (false ∷ i) (interpretations (suc n)) f
                (∈-++₂ {ys = map (_∷_ true) (interpretations n)}
                       (∈-map (_∷_ false) (all-interpretations n i)))
                model


  ¬sat-false : ∀ {n} {f : Formula n} → ¬ SAT f → ∀ i → eval f i ≡ false
  ¬sat-false ¬sat i = ¬-not λ z → ¬sat (has-model (i , true-by z))

  finds-no-model : ∀ {n} {f : Formula n} → ¬ SAT f → ∀ is → find-model f is ≡ nothing
  finds-no-model _ [] = refl
  finds-no-model ¬sat (i ∷ is) rewrite ¬sat-false ¬sat i = finds-no-model ¬sat is

  completeness : ∀ n f → ¬ SAT f → trivial n f ≡ nothing
  completeness 0 _ ¬sat
    rewrite ¬sat-false ¬sat [] = refl
  completeness (suc n) _ ¬sat =
    let is = interpretations n
     in finds-no-model ¬sat (map (_∷_ true) is ++ map (_∷_ false) is)

  correctness : CorrectSolver trivial
  correctness = soundness , completeness
