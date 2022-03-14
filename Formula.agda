module Formula where

open import Data.Bool renaming (not to ¬♭_; _∨_ to _∨♭_; _∧_ to _∧♭_)
open import Data.Vec using (Vec; _∷_; []; [_]; lookup)
open import Data.Nat
open import Data.Fin
open import Data.Maybe

infixl 4 _∨_
infixl 4 _∧_
infixl 4 _⇔_
infixl 6 ¬_

-- Boolean formula, that contains n variables
data Formula (n : ℕ) : Set where
  const : (b : Bool) → Formula n
  var   : (x : Fin n) → Formula n
  ¬_    : (f : Formula n) → Formula n
  _∨_   : (f g : Formula n) → Formula n
  _∧_   : (f g : Formula n) → Formula n
  _⇒_   : (f g : Formula n) → Formula n
  _⇔_   : (f g : Formula n) → Formula n

Interpretation = Vec Bool

eval : {n : ℕ} → Formula n → Interpretation n → Bool
eval (const b) _ = b
eval (var x)   i = lookup i x
eval (¬ f)     i = ¬♭ (eval f i)
eval (f ∨ g)   i = (eval f i) ∨♭ (eval g i)
eval (f ∧ g)   i = (eval f i) ∧♭ (eval g i)
eval (f ⇒ g)   i = ¬♭ (eval f i) ∨♭ (eval g i)
eval (f ⇔ g)   i = (a ∧♭ b) ∨♭ (¬♭ a ∧♭ ¬♭ b)
                     where a = eval f i
                           b = eval g i

private
  -- Example
  x : Formula 3
  x = var (# 0)

  y : Formula 3
  y = var (# 1)

  z : Formula 3
  z = var (# 2)

  f = (x ∨ y) ∧ (y ∨ ¬ z ∨ x) ∧ x

  -- x = 0, y = 1, z = 0
  i = false ∷ true ∷ false ∷ []

  open import Relation.Binary.PropositionalEquality

  f≡0 : eval f i ≡ false
  f≡0 = refl


data Equivalent {n : ℕ} (f : Formula n) (g : Formula n) : Set where
  by-eval : (∀ {i} → eval f i ≡ eval g i) → Equivalent f g


Solver = (n : ℕ) → Formula n → Maybe (Interpretation n)
