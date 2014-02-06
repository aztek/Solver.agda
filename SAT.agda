module SAT where

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Core
open import Data.Maybe
open import Data.Nat
open import Data.Bool using (true)
open import Data.Product renaming (_×_ to _∧_)
open import Formula using (Formula; Interpretation; eval)

data Model {n : ℕ} (f : Formula n) : Interpretation n → Set where
  true-by : ∀ {i} → eval f i ≡ true → Model f i

data SAT {n : ℕ} (f : Formula n) : Set where
  has-model : ∃ (Model f) → SAT f

CorrectSolver : (solver : (n : ℕ) → Formula n → Maybe (Interpretation n)) → Set
CorrectSolver solver = (∀ n f →   SAT f → (∃ λ i → solver n f ≡ just i ∧ Model f i)) ∧
                       (∀ n f → ¬ SAT f → solver n f ≡ nothing)
