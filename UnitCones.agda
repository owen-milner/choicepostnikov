
module UnitCones where

open import Cubical.Data.Nat renaming (elim to ℕElim)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Foundations.Everything
open import Cubical.HITs.Truncation
open import Cubical.Homotopy.Connected

open import Limits
open import DiagramSigma

{- One way to define limits and products -}

One-Cones-Iso : (A : ℕ-Family) → Iso (ConeℕFam A Unit) ((n : ℕ) → A n)
Iso.fun (One-Cones-Iso A) x n = x n tt
Iso.inv (One-Cones-Iso A) x n tt = x n
Iso.rightInv (One-Cones-Iso A) x = refl
Iso.leftInv (One-Cones-Iso A) x = refl

One-Cones-Equiv : (A : ℕ-Family) → (ConeℕFam A Unit) ≃ ((n : ℕ) → A n)
One-Cones-Equiv A = isoToEquiv (One-Cones-Iso A)

One-Cones-Cones : (A : ℕ-Family) → ConeℕFam A (ConeℕFam A Unit)
One-Cones-Cones A n x = x n tt

Iso-One-Cones-Cone : (A : ℕ-Family) (X : Type ℓ-zero)
                   → Iso (X → ConeℕFam A Unit) (ConeℕFam A X)
Iso.fun (Iso-One-Cones-Cone A X) f n x = f x n tt
Iso.inv (Iso-One-Cones-Cone A X) c x n tt = c n x
Iso.rightInv (Iso-One-Cones-Cone A X) c = refl
Iso.leftInv (Iso-One-Cones-Cone A X) f = refl

Equiv-One-Cones-Cone : (A : ℕ-Family) (X : Type ℓ-zero)
                    → (X → ConeℕFam A Unit) ≃ (ConeℕFam A X)
Equiv-One-Cones-Cone A X = isoToEquiv (Iso-One-Cones-Cone A X)   

One-Cones-Det : (A : ℕ-Family)
             → Iso.inv (Iso-One-Cones-Cone A (ConeℕFam A Unit))
                        (One-Cones-Cones A)
              ≡ (λ x → x)
One-Cones-Det A = refl

Nat-One-Cones-Cone : (A : ℕ-Family) (X Y : Type ℓ-zero) (f : Y → X)
                     (c : X → ConeℕFam A Unit)
                  → ConeℕFam→Map→ConeℕFam A X Y
                       (Iso.fun (Iso-One-Cones-Cone A X) c) f
                   ≡ Iso.fun (Iso-One-Cones-Cone A Y) (c ∘ f)
Nat-One-Cones-Cone A X Y f c = refl

Prod-Equiv-One-Cones : (A : ℕ-Family) (X : Type ℓ-zero)
                    → isEquiv (ConeℕFam→Map→ConeℕFam A (ConeℕFam A Unit) X
                                                        (One-Cones-Cones A))
Prod-Equiv-One-Cones A X = snd (Equiv-One-Cones-Cone A X)

One-Cones-Product : (A : ℕ-Family) → is-ℕ-Product-of A (ConeℕFam A Unit)
One-Cones-Product A = (One-Cones-Cones A) , (Prod-Equiv-One-Cones A)

One-dCones-Iso : (A : ℕ-Diagram)
              → Iso (ConeℕDiag A Unit)
                     (Σ[ x ∈ ((n : ℕ) → (fst A n)) ]
                       ((n : ℕ) → snd A n (x (1 + n)) ≡ x n))
Iso.fun (One-dCones-Iso A) (c , d) = (λ n → c n tt) , λ n → d n tt
Iso.inv (One-dCones-Iso A) (c , d) = (λ n _ → c n) , λ n _ → d n
Iso.rightInv (One-dCones-Iso A) (c , d) = refl
Iso.leftInv (One-dCones-Iso A) (c , d) = refl

One-dCones-Equiv : (A : ℕ-Diagram)
                → (ConeℕDiag A Unit)
                 ≃ (Σ[ x ∈ ((n : ℕ) → (fst A n)) ]
                   ((n : ℕ) → snd A n (x (1 + n)) ≡ x n))
One-dCones-Equiv A = isoToEquiv (One-dCones-Iso A)

One-dCones-Cones : (A : ℕ-Diagram) → ConeℕDiag A (ConeℕDiag A Unit)
fst (One-dCones-Cones A) n (c , d) = c n tt
snd (One-dCones-Cones A) n (c , d) = d n tt

Iso-One-dCones-Cone : (A : ℕ-Diagram) (X : Type ℓ-zero)
                   → Iso (X → ConeℕDiag A Unit) (ConeℕDiag A X)
fst (Iso.fun (Iso-One-dCones-Cone A X) f) n x = fst (f x) n tt
snd (Iso.fun (Iso-One-dCones-Cone A X) f) n x = snd (f x) n tt
fst (Iso.inv (Iso-One-dCones-Cone A X) c x) n tt = fst c n x
snd (Iso.inv (Iso-One-dCones-Cone A X) c x) n tt = snd c n x
Iso.rightInv (Iso-One-dCones-Cone A X) c = refl
Iso.leftInv (Iso-One-dCones-Cone A X) f = refl

Equiv-One-dCones-Cone : (A : ℕ-Diagram) (X : Type ℓ-zero)
                    → (X → ConeℕDiag A Unit) ≃ (ConeℕDiag A X)
Equiv-One-dCones-Cone A X = isoToEquiv (Iso-One-dCones-Cone A X)  

One-dCones-Det : (A : ℕ-Diagram)
             → Iso.inv (Iso-One-dCones-Cone A (ConeℕDiag A Unit))
                        (One-dCones-Cones A)
              ≡ (λ x → x)
One-dCones-Det A = refl

Nat-One-dCones-Cone : (A : ℕ-Diagram) (X Y : Type ℓ-zero) (f : Y → X)
                      (c : X → ConeℕDiag A Unit)
                   → ConeℕDiag→Map→ConeℕDiag A X Y
                        (Iso.fun (Iso-One-dCones-Cone A X) c) f
                    ≡ Iso.fun (Iso-One-dCones-Cone A Y) (c ∘ f)
Nat-One-dCones-Cone A X Y f c = refl

Lim-Equiv-One-Cone : (A : ℕ-Diagram) (X : Type ℓ-zero)
                    → isEquiv (ConeℕDiag→Map→ConeℕDiag A
                                  (ConeℕDiag A Unit) X
                                  (One-dCones-Cones A))
Lim-Equiv-One-Cone A X = snd (Equiv-One-dCones-Cone A X)

One-Cones-Limit : (A : ℕ-Diagram) → is-ℕ-Limit-of A (ConeℕDiag A Unit)
One-Cones-Limit A = (One-dCones-Cones A) , (Lim-Equiv-One-Cone A)

