module Bool.Properties where

-- Additional properties of booleans

open import Relation.Binary.PropositionalEquality
open import Data.Bool

bool-split : ∀ {ℓ} {P : Set ℓ} b → (b ≡ true → P) → (b ≡ false → P) → P
bool-split true  1→P _ = 1→P refl
bool-split false _ 0→P = 0→P refl

if-true : ∀ {ℓ} {A : Set ℓ} {p : Bool} {a b : A} → p ≡ true → (if p then a else b) ≡ a
if-true refl = refl

if-false : ∀ {ℓ} {A : Set ℓ} {p : Bool} {a b : A} → p ≡ false → (if p then a else b) ≡ b
if-false refl = refl
