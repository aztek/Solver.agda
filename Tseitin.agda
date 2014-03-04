module Tseitin where

open import Data.Nat hiding (_≤_; ≤-pred) renaming (_≤′_ to _≤_; ≤′-refl to ≤-refl; ≤′-step to ≤-step)
open import Data.Fin hiding (_≤_; inject≤)
open import Data.Product
open import Data.List as List
open import Data.Bool using (Bool; true; false)
open import Function hiding (const)
open import Formula
open import CNF

to-cnf : {n : ℕ} → List (Formula n) → Formula n
to-cnf = foldr _∧_ (const true)

inject≤ : ∀ {m n} → Fin m → m ≤ n → Fin n
inject≤ m ≤-refl = m
inject≤ m (≤-step m≤n) = suc (inject≤ m m≤n)

elevate : {n m : ℕ} {n≤m : n ≤ m} → Formula n → Formula m
elevate (const b) = const b
elevate {n≤m = n≤m} (var x) = var (inject≤ x n≤m)
elevate {n≤m = n≤m} (¬ f)   = ¬ (elevate {n≤m = n≤m} f)
elevate {n≤m = n≤m} (f ∨ g) = (elevate {n≤m = n≤m} f) ∨ (elevate {n≤m = n≤m} g)
elevate {n≤m = n≤m} (f ∧ g) = (elevate {n≤m = n≤m} f) ∧ (elevate {n≤m = n≤m} g)
elevate {n≤m = n≤m} (f ⇒ g) = (elevate {n≤m = n≤m} f) ⇒ (elevate {n≤m = n≤m} g)
elevate {n≤m = n≤m} (f ⇔ g) = (elevate {n≤m = n≤m} f) ⇔ (elevate {n≤m = n≤m} g)

0≤n : ∀ {n} → 0 ≤ n
0≤n {0} = ≤-refl
0≤n {suc _} = ≤-step 0≤n

≤-pred : ∀ {n m} → suc n ≤ m → n ≤ m
≤-pred {n} .{suc n} ≤-refl = ≤-step ≤-refl
≤-pred {n} {suc m} (≤-step .{m} suc[n]≤m) = ≤-step (≤-pred suc[n]≤m)

≤-trans : ∀ {n m k} → n ≤ m → m ≤ k → n ≤ k
≤-trans {0}     {_}       {_}    _  _ = 0≤n
≤-trans {suc _} {0}       {_}    () _
≤-trans {_}     {suc _}   {0}     _ ()
≤-trans {suc .m} {suc m}  {suc k} ≤-refl m≤k = m≤k
≤-trans {suc n}  {suc .k} {suc k} n≤k ≤-refl = n≤k
≤-trans {suc n}  {suc m}  {suc k} (≤-step suc[n]≤m) (≤-step suc[m]≤k) =
  ≤-step (≤-trans suc[n]≤m (≤-pred suc[m]≤k))

clausify : {n : ℕ} → Formula n → Formula n → List (Formula n)
clausify x (const true)  = [  x  ]
clausify x (const false) = [ ¬ x ]
clausify x (y ∨ z) = (¬ y ∨ x) ∷ (¬ z ∨ x) ∷ [ ¬ x ∨ y ∨ z ]
clausify x (y ∧ z) = (¬ x ∨ y) ∷ (¬ x ∨ z) ∷ [ ¬ y ∨ ¬ z ∨ x ]
clausify x (y ⇒ z) = (y ∨ x) ∷ (¬ z ∨ x) ∷ [ ¬ x ∨ ¬ y ∨ z ]
clausify x (y ⇔ z) = (¬ x ∨ ¬ y ∨ z) ∷ (¬ x ∨ ¬ z ∨ y) ∷ (¬ y ∨ ¬ z ∨ x) ∷ [ y ∨ z ∨ x ]
clausify x (¬ y)   = (x ∨ y) ∷ [ ¬ x ∨ ¬ y ]
clausify x y       = (x ∨ ¬ y) ∷ [ (¬ x) ∨ y ]

mutual
  new-vars-binary : {n : ℕ} → Formula n → ({m : ℕ} → Formula m → Formula m → Formula m) →
                   Formula n → Σ ℕ (λ m → n ≤ m × Formula m × List (Formula m))
  new-vars-binary f _⊗_ g
    with new-vars f
  ...  | m , n≤m , x , fs
    with new-vars (elevate {n≤m = n≤m} g)
  ...  | k , m≤k , y , gs
    with ≤-step m≤k | ≤-step (≤-refl {k})
  ...  | m≤suc[k]   | k≤suc[k] =
    suc k , ≤-trans n≤m m≤suc[k] , z , clausify z (x′ ⊗ y′) ++ fs′ ++ gs′
      where x′ = elevate {n≤m = m≤suc[k]} x
            y′ = elevate {n≤m = k≤suc[k]} y
            fs′ = List.map (elevate {n≤m = m≤suc[k]}) fs
            gs′ = List.map (elevate {n≤m = k≤suc[k]}) gs
            z = var (fromℕ k)


  new-vars-unary : {n : ℕ} → ({m : ℕ} → Formula m → Formula m) →
                  Formula n → Σ ℕ (λ m → n ≤ m × Formula m × List (Formula m))
  new-vars-unary □_ f
    with new-vars f
  ...  | m , n≤m , x , fs
    with ≤-step n≤m | ≤-step (≤-refl {m})
  ...  | n≤suc[m]   | m≤suc[m] =
    suc m , n≤suc[m] , y , clausify y (□ x′) ++ fs′
      where x′ = elevate {n≤m = m≤suc[m]} x
            fs′ = List.map (elevate {n≤m = m≤suc[m]}) fs
            y = var (fromℕ m)


  new-vars : {n : ℕ} → Formula n → Σ ℕ (λ m → n ≤ m × Formula m × List (Formula m))
  new-vars (const b) = , (≤-refl , const b , [ const b ])
  new-vars (var x)   = , (≤-refl , var x   , [  var x  ])
  new-vars (¬ f)   = new-vars-unary  ¬_ f
  new-vars (f ∨ g) = new-vars-binary f _∨_ g
  new-vars (f ∧ g) = new-vars-binary f _∧_ g
  new-vars (f ⇒ g) = new-vars-binary f _⇒_ g
  new-vars (f ⇔ g) = new-vars-binary f _⇔_ g


tseitin : (n : ℕ) → Formula n → Σ ℕ Formula
tseitin n f
  with new-vars f
...  | m , _ , x , fs = m , to-cnf (x ∷ fs)
