module CNF where

open import Data.Nat hiding (_≤_; ≤-pred) renaming (_≤′_ to _≤_; ≤′-refl to ≤-refl; ≤′-step to ≤-step)
open import Data.Fin hiding (_≤_; inject≤)
open import Data.Product
open import Formula

data Literal {n : ℕ} : Formula n → Set where
  positive : ∀ {x} → Literal (var x)
  negative : ∀ {x} → Literal (¬ var x)
  constant : ∀ {b} → Literal (const b)

data Clause {n : ℕ} : Formula n → Set where
  trivial : ∀ {x} → Literal x → Clause x
  disjunction : ∀ {x q} → Literal x → Clause q → Clause (x ∨ q)

data CNF {n : ℕ} : Formula n → Set where
  trivial : ∀ {p} → Clause p → CNF p
  conjunction : ∀ {p q} → Clause p → CNF q → CNF (p ∧ q)

CorrectCNF : (transformation : (n : ℕ) → Formula n → Σ ℕ Formula) → Set
CorrectCNF transformation = ∀ n f → CNF (proj₂ (transformation n f))
