module EasyLimMaps where

open import Cubical.Data.Nat renaming (elim to ℕElim)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Everything
open import Cubical.Functions.FunExtEquiv
open import Cubical.HITs.Truncation
open import Cubical.Homotopy.Connected

open import DiagramMaps
open import Limits
open import DiagramSigma
open import PostnikovTowers
open import EasyLimits

{- This file contains a proof that, for the choice of limits and products
   defined in the "EasyLimits" file, a products of maps being n+1 connected
   implies the limit of those maps is n connected -}

module _ (A B : ℕ-Family) (f : MapOfFamilies A B) where

{- Easy characterisation of map of products -}
  the-pathProd :
    MapOfFamilies→MapOfProds A B
      (((n : ℕ) → A n) , (easyProduct A))
      (((n : ℕ) → B n) , (easyProduct B)) f
    ≡ λ x n → f n (x n)
  the-pathProd = refl


module _ (A B : ℕ-Diagram) (f : MapOfDiagrams A B) where

{- Easy characterisation of map of limits -}
  the-pathLim :
    MapOfDiagrams→MapOfLimits' A B f
      (limitType A , (easyLimit A))
      (limitType B , (easyLimit B))
    ≡ λ x →
      (λ n → (fst f) n (fst x n))
      , λ n → snd f n (fst x (suc n)) ∙ cong (fst f n) (snd x n)
  the-pathLim = refl


{- helper lemmas telling us certain maps are equivalences, others are
   connected -}
dFunExt-iso-∙ : (X : Type ℓ-zero) (Y : X → Type ℓ-zero)
                (f g h : (x : X) → Y x) (p : (x : X) → f x ≡ g x)
                → isIso (λ (q : (x : X) → g x ≡ h x) (x : X)
                          → p x ∙ q x)
fst (dFunExt-iso-∙ X Y f g h p) =
  λ q x → (p x) ⁻¹ ∙ q x
fst (snd (dFunExt-iso-∙ X Y f g h p)) q =
  funExt (λ x → assoc (p x) (p x ⁻¹) (q x)
                 ∙ cong (_∙ q x) (rCancel (p x))
                 ∙ lUnit (q x) ⁻¹)
snd (snd (dFunExt-iso-∙ X Y f g h p)) q =
  funExt (λ x → assoc (p x ⁻¹) (p x) (q x)
                 ∙ cong (_∙ q x) (lCancel (p x))
                 ∙ lUnit (q x) ⁻¹)

dFunExt-conn-∙ : (n : ℕ) (X : Type ℓ-zero) (Y : X → Type ℓ-zero)
                 (f g h : (x : X) → Y x) (p : (x : X) → f x ≡ g x)
                 → isConnectedFun n (λ (q : (x : X) → g x ≡ h x) (x : X)
                                     → p x ∙ q x)
dFunExt-conn-∙ n X Y f g h p =
  isEquiv→isConnected _
  (isoToIsEquiv
  (isIso→Iso (λ q x → p x ∙ q x)
  (dFunExt-iso-∙ X Y f g h p))) n


connectedΣFun-aux2' : (A B : Type ℓ-zero) (C : A → Type ℓ-zero)
  (D : B → Type ℓ-zero) (f : A → B) (g : (a : A) → C a → D (f a))
  → (b : B) (d : D b)
  → Iso ((Σ (Σ A C)
       (λ a →
          Σ-syntax (f (fst a) ≡ b)
          (λ p → PathP (λ i → D (p i)) (g (fst a) (snd a)) d))))
        (Σ[ x ∈ (Σ[ y ∈ A ] f y ≡ b) ]
          (Σ[ y ∈ C (fst x) ] (PathP (λ i → D ((snd x) i)))
                                         (g (fst x) y) d))
Iso.fun (connectedΣFun-aux2' A B C D f g b d) ((a , c) , (p , q)) =
  (a , p) , (c , q)
Iso.inv (connectedΣFun-aux2' A B C D f g b d) ((a , p) , (c , q)) =
  (a , c) , (p , q)
Iso.rightInv (connectedΣFun-aux2' A B C D f g b d) qd =
  refl
Iso.leftInv (connectedΣFun-aux2' A B C D f g b d) qd = refl

connectedΣFun-aux1' : (A B : Type ℓ-zero) (C : A → Type ℓ-zero)
  (D : B → Type ℓ-zero) (f : A → B) (g : (a : A) → C a → D (f a))
  → (b : B) (d : D b)
  → Iso (fiber (λ x → f (fst x) , g (fst x) (snd x)) (b , d))
     (Σ[ x ∈ (Σ[ y ∈ A ] f y ≡ b) ]
       (Σ[ y ∈ C (fst x) ] (transport (λ i → D ((snd x) i)))
                                          (g (fst x) y) ≡ d))
connectedΣFun-aux1' A B C D f g b d =
  compIso (Σ-cong-iso-snd (λ x → invIso ΣPathIsoPathΣ))
          (compIso (connectedΣFun-aux2 A B C D f g b d)
                   (Σ-cong-iso-snd
                    (λ x → Σ-cong-iso-snd λ y
                         → PathPIsoPath (λ i → D ((snd x) i))
                                         (g (fst x) y) d)))

transportConn : (n : ℕ) (A B C : Type ℓ-zero) (f : A → B) (p : B ≡ C)
             → isConnectedFun n f
             → isConnectedFun n (λ x → transport (λ i → (p i)) (f x))
transportConn n A B C f p connf =
  isConnectedComp (transport (λ i → (p i))) f n
  (ConnectedEquiv B C (transport (λ i → (p i))) (isEquivTransport p) n)
  connf

connectedΣFun : (n : ℕ) (A B : Type ℓ-zero) (C : A → Type ℓ-zero)
  (D : B → Type ℓ-zero) (f : A → B) (g : (a : A) → C a → D (f a))
  → isConnectedFun n f → ((a : A) → isConnectedFun n (g a))
  → isConnectedFun n {B = Σ B D}
        (λ (x : Σ A C) → (f (fst x) , g (fst x) (snd x)))
connectedΣFun n A B C D f g connf conng (b , d) =
  transport (λ i → isContr (cong (∥_∥ n)
                                  (ua (isoToEquiv
                                      (connectedΣFun-aux1 A B C D f g b d)))
                                  (~ i)))
  (transport
  (λ i → isContr
          (ua (isoToEquiv
              (truncOfΣIso n {A = (Σ A (λ y → f y ≡ b))}
                             {B = λ z → Σ (C (fst z))
                                           (λ y → transport
                                                   (λ i₁ → D (snd z i₁))
                                                   (g (fst z) y) ≡ d)}))
              (~ i)))
  (transport
  (λ i → isContr
          (cong (∥_∥ n)
          (ua (Σ-contractSnd
          λ (x : Σ A (λ y → f y ≡ b))
          → transportConn n (C (fst x)) (D (f (fst x))) (D b)
                           (g (fst x)) (λ i → D (snd x i)) (conng (fst x)) d))
  (~ i)))
  (connf b)))

module _ (A B : ℕ-Diagram) (f : MapOfDiagrams A B) where
{- This is essentially the proof that countable choice in degree n+1 implies
   dependent choice in degree n -}
  connectivityLemma : (n : ℕ) →
    isConnectedFun (1 + n)
      (MapOfFamilies→MapOfProds (fst A) (fst B)
       (((n : ℕ) → fst A n) , (easyProduct (fst A)))
       (((n : ℕ) → fst B n) , (easyProduct (fst B))) (fst f))
    → isConnectedFun n
       (MapOfDiagrams→MapOfLimits' A B f
        (limitType A , (easyLimit A))
        (limitType B , (easyLimit B)))
  connectivityLemma n hC =
    connectedΣFun n ((n : ℕ) → fst A n) ((n : ℕ) → fst B n)
                    (λ x → (n : ℕ) → snd A n (x (1 + n)) ≡ x n)
                    (λ x → (n : ℕ) → snd B n (x (1 + n)) ≡ x n)
                    (λ x n → fst f n (x n))
                    (λ x p n → snd f n (x (suc n)) ∙ cong (fst f n) (p n))
                    (isConnectedFunSubtr n 1 (λ x n → fst f n (x n)) hC)
                    λ x → isConnectedComp
                           (λ (p : (n : ℕ)
                                → fst f n (snd A n (x (1 + n)))
                                 ≡ fst f n (x n)) → λ n → snd f n (x (1 + n))
                                                           ∙ (p n))
                    (λ p n → cong (fst f n) (p n)) n
                    (dFunExt-conn-∙ n ℕ (fst B)
                    (λ n → snd B n (fst f (1 + n) (x (1 + n))))
                    (λ n → fst f n (snd A n (x (1 + n))))
                    (λ n → fst f n (x n))
                     λ n → snd f n (x (1 + n)))
                     (isConnectedComp
                     funExt⁻
                     (cong (λ (x : (n : ℕ) → fst A n)
                              (n : ℕ) → fst f n (x n)) ∘ funExt)
                     n (isEquiv→isConnected funExt⁻
                          (snd (invEquiv funExtEquiv)) n)
                       (isConnectedComp
                        (cong (λ (x : (n : ℕ) → fst A n)
                                 (n : ℕ) → fst f n (x n)))
                        funExt
                        n
                        (isConnectedCong n (λ x n → fst f n (x n))
                         hC)
                        (isEquiv→isConnected funExt
                          (snd (funExtEquiv)) n)))
