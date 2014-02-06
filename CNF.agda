-- Tseitin transformation

open import Data.Nat
open import Formula

module CNF where
  data Literal {n : ℕ} : Formula n → Set where
    positive : ∀ {x} → Literal (var x)
    negative : ∀ {x} → Literal (¬ var x)

  data Clause {n : ℕ} : Formula n → Set where
    trivial : ∀ {x} → Literal x → Clause x
    disjuction : ∀ {x q} → Literal x → Clause q → Clause (x ∨ q)

  data CNF {n : ℕ} : Formula n → Set where
    trivial : ∀ {p} → Clause p → CNF p
    conjunction : ∀ {p q} → Clause p → CNF q → CNF (p ∧ q)
