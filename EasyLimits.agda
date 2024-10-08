module EasyLimits where

open import Cubical.Data.Nat renaming (elim to ℕElim)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Everything
open import Cubical.HITs.Truncation
open import Cubical.Homotopy.Connected

open import Limits
open import DiagramSigma

{- The most straightforward way to define a limit for a fixed diagram (A , a)
   as Σ (x : Π A_n) (a_n (x_n+1) = x_n) -}

One-Cones-Cones : (A : ℕ-Family) → ConeℕFam A ((n : ℕ) → A n)
One-Cones-Cones A n x = x n

Iso-One-Cones-Cone : (A : ℕ-Family) (X : Type ℓ-zero)
                   → Iso (X → (n : ℕ) → A n) (ConeℕFam A X)
Iso.fun (Iso-One-Cones-Cone A X) f n x = f x n
Iso.inv (Iso-One-Cones-Cone A X) c x n = c n x
Iso.rightInv (Iso-One-Cones-Cone A X) c = refl
Iso.leftInv (Iso-One-Cones-Cone A X) f = refl

Equiv-One-Cones-Cone : (A : ℕ-Family) (X : Type ℓ-zero)
                    → (X → (n : ℕ) → A n) ≃ (ConeℕFam A X)
Equiv-One-Cones-Cone A X = isoToEquiv (Iso-One-Cones-Cone A X)   

One-Cones-Det : (A : ℕ-Family)
             → Iso.inv (Iso-One-Cones-Cone A ((n : ℕ) → A n))
                        (One-Cones-Cones A)
              ≡ (λ x → x)
One-Cones-Det A = refl

Nat-One-Cones-Cone : (A : ℕ-Family) (X Y : Type ℓ-zero) (f : Y → X)
                     (c : X → (n : ℕ) → A n)
                  → ConeℕFam→Map→ConeℕFam A X Y
                       (Iso.fun (Iso-One-Cones-Cone A X) c) f
                   ≡ Iso.fun (Iso-One-Cones-Cone A Y) (c ∘ f)
Nat-One-Cones-Cone A X Y f c = refl

Prod-Equiv-One-Cones : (A : ℕ-Family) (X : Type ℓ-zero)
                    → isEquiv (ConeℕFam→Map→ConeℕFam A ((n : ℕ) → A n) X
                                                        (One-Cones-Cones A))
Prod-Equiv-One-Cones A X = snd (Equiv-One-Cones-Cone A X)

easyProduct : (A : ℕ-Family) → is-ℕ-Product-of A ((n : ℕ) → A n)
easyProduct A = (One-Cones-Cones A) , (Prod-Equiv-One-Cones A)

limitType : ℕ-Diagram → Type ℓ-zero
limitType A = Σ[ c ∈ ((n : ℕ) → fst A n) ]
              ((n : ℕ) → snd A n (c (1 + n)) ≡ c n)

One-dCones-Cones : (A : ℕ-Diagram) → ConeℕDiag A (limitType A)
fst (One-dCones-Cones A) n (c , d) = c n
snd (One-dCones-Cones A) n (c , d) = d n

Iso-One-dCones-Cone : (A : ℕ-Diagram) (X : Type ℓ-zero)
                   → Iso (X → limitType A) (ConeℕDiag A X)
fst (Iso.fun (Iso-One-dCones-Cone A X) f) n x = fst (f x) n
snd (Iso.fun (Iso-One-dCones-Cone A X) f) n x = snd (f x) n
fst (Iso.inv (Iso-One-dCones-Cone A X) c x) n = fst c n x
snd (Iso.inv (Iso-One-dCones-Cone A X) c x) n = snd c n x
Iso.rightInv (Iso-One-dCones-Cone A X) c = refl
Iso.leftInv (Iso-One-dCones-Cone A X) f = refl

Equiv-One-dCones-Cone : (A : ℕ-Diagram) (X : Type ℓ-zero)
                    → (X → limitType A) ≃ (ConeℕDiag A X)
Equiv-One-dCones-Cone A X = isoToEquiv (Iso-One-dCones-Cone A X)  

One-dCones-Det : (A : ℕ-Diagram)
             → Iso.inv (Iso-One-dCones-Cone A (limitType A))
                        (One-dCones-Cones A)
              ≡ (λ x → x)
One-dCones-Det A = refl

Nat-One-dCones-Cone : (A : ℕ-Diagram) (X Y : Type ℓ-zero) (f : Y → X)
                      (c : X → limitType A)
                   → ConeℕDiag→Map→ConeℕDiag A X Y
                        (Iso.fun (Iso-One-dCones-Cone A X) c) f
                    ≡ Iso.fun (Iso-One-dCones-Cone A Y) (c ∘ f)
Nat-One-dCones-Cone A X Y f c = refl

Lim-Equiv-One-Cone : (A : ℕ-Diagram) (X : Type ℓ-zero)
                    → isEquiv (ConeℕDiag→Map→ConeℕDiag A
                                  (limitType A) X
                                  (One-dCones-Cones A))
Lim-Equiv-One-Cone A X = snd (Equiv-One-dCones-Cone A X)

easyLimit : (A : ℕ-Diagram) → is-ℕ-Limit-of A (limitType A)
easyLimit A = (One-dCones-Cones A) , (Lim-Equiv-One-Cone A)
