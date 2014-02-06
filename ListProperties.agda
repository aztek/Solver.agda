module ListProperties where

open import Data.List

data _∈_ {A : Set} : A → List A → Set where
  here  : ∀ {x}   {xs : List A} → x ∈ (x ∷ xs)
  there : ∀ {x y} {xs : List A} (x∈xs : x ∈ xs) → x ∈ (y ∷ xs)

∈-map : ∀ {A B} {x : A} {xs} (f : A → B) → x ∈ xs → f x ∈ map f xs
∈-map f here = here
∈-map f (there p) = there (∈-map f p)

∈-++₁ : ∀ {A} {z : A} xs ys → z ∈ xs → z ∈ (xs ++ ys)
∈-++₁ {A} {.z} (z ∷ xs) ys here = here
∈-++₁ {A} {z}  (_ ∷ xs) ys (there z∈xs) = there (∈-++₁ xs ys z∈xs)

∈-++₂ : ∀ {A} {z : A} xs ys → z ∈ xs → z ∈ (ys ++ xs)
∈-++₂ {A} {.z} (z ∷ xs) [] here = here
∈-++₂ {A} {z}  (_ ∷ xs) [] (there z∈xs) = there z∈xs
∈-++₂ {A} {.z} (z ∷ xs) (_ ∷ ys) here = there (∈-++₂ (z ∷ xs) ys here)
∈-++₂ {A} {z}  (x ∷ xs) (_ ∷ ys) (there z∈xs) = there (∈-++₂ (x ∷ xs) ys (there z∈xs))
