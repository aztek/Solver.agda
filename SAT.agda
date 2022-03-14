module SAT where

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Maybe
open import Data.Nat
open import Data.Bool using (true)
open import Data.Product renaming (_×_ to _∧_)
open import Formula using (Formula; Interpretation; eval)

Model : {n : ℕ} → Formula n → Interpretation n → Set
Model f i = eval f i ≡ true

SAT : {n : ℕ} → Formula n → Set
SAT f = ∃ (Model f)

CorrectSolver : (solver : (n : ℕ) → Formula n → Maybe (Interpretation n)) → Set
CorrectSolver solver = (∀ n f →   SAT f → (∃ λ i → solver n f ≡ just i ∧ Model f i)) ∧
                       (∀ n f → ¬ SAT f → solver n f ≡ nothing)

KeepsSAT : (transformation : (n : ℕ) → Formula n → Σ ℕ Formula) → Set
KeepsSAT transformation = ∀ n f → SAT f → SAT (proj₂ (transformation n f))

Keeps¬SAT : (transformation : (n : ℕ) → Formula n → Σ ℕ Formula) → Set
Keeps¬SAT transformation = ∀ n f → ¬ SAT f → ¬ SAT (proj₂ (transformation n f))

Equisatisfiable : (transformation : (n : ℕ) → Formula n → Σ ℕ Formula) → Set
Equisatisfiable transformation = KeepsSAT transformation ∧ Keeps¬SAT transformation
