module Trivial where

open import Formula using (Formula; Interpretation; eval; Solver)
open import Data.Nat
open import Data.Maybe hiding (map)
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
find-model _ []       = nothing
find-model f (i ∷ is) = if (eval f i) then (just i) else (find-model f is)

-- Trivial SAT-solver - brute forces all possible interpretations
trivial : Solver
trivial n f = find-model f (interpretations n)
