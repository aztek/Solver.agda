module ListProperties where

open import Data.List

open import Relation.Binary.PropositionalEquality
open import Data.List.Any using (here; there; module Membership-≡)
open Membership-≡

∈-map : ∀ {ℓ} {A B : Set ℓ} {x : A} {xs} (f : A → B) → x ∈ xs → f x ∈ map f xs
∈-map f (here px) = here (cong f px)
∈-map f (there p) = there (∈-map f p)

∈-++₁ : ∀ {ℓ} {A : Set ℓ} {z : A} {xs ys} → z ∈ xs → z ∈ (xs ++ ys)
∈-++₁ (here px) = here px
∈-++₁ (there p) = there (∈-++₁ p)

∈-++₂ : ∀ {ℓ} {A : Set ℓ} {z : A} {xs ys} → z ∈ xs → z ∈ (ys ++ xs)
∈-++₂ {ℓ} {A} {z} {x ∷ xs} {[]} (here px) = here px
∈-++₂ {ℓ} {A} {z} {x ∷ xs} {[]} (there p) = there p
∈-++₂ {ℓ} {A} {z} {x ∷ xs} {y ∷ ys} (here px) = there (∈-++₂ {xs = x ∷ xs} {ys = ys} (here px))
∈-++₂ {ℓ} {A} {z} {x ∷ xs} {y ∷ ys} (there p) = there (∈-++₂ {xs = x ∷ xs} {ys = ys} (there p))
