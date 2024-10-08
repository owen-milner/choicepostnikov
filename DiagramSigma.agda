
module DiagramSigma where

open import Cubical.Data.Nat renaming (elim to ℕElim)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Everything hiding (transpEquiv)
open import Cubical.Functions.FunExtEquiv
open import Cubical.HITs.Truncation
open import Cubical.Homotopy.Connected

import Cubical.Foundations.Equiv

open import Limits

{- contains definitions of diagrams and limits and helpful lemmas

   TODO: merge this and "Limits" file, the main difference is this
         uses a defintion of diagrams packaged as a dependent sum,
         which makes for convenient notation later on  -}

transportHomotopy : {X : Type ℓ-zero} {w x y z : X}
      (p : w ≡ x) (q : y ≡ z) (r : w ≡ y)
      → transport (λ i → (p i) ≡ q i) r ≡ p ⁻¹ ∙ r ∙ q
transportHomotopy {w = w} {x = x} {y = y} {z = z} =
  J (λ x' p → (q : y ≡ z) (r : w ≡ y)
           → transport (λ i → (p i) ≡ q i) r ≡ p ⁻¹ ∙ r ∙ q)
    (J (λ z' q → (r : w ≡ y)
              → transport (λ i → w ≡ q i) r ≡ refl ∙ r ∙ q)
       λ r → transportRefl r ∙ rUnit r ∙ lUnit (r ∙ refl))


transportTwoDeps : {X Y : Type ℓ-zero} {Z Z' : X → Y → Type ℓ-zero}
  (Q : Z ≡ Z') (f : (x : X) (y : Y) → Z x y) →
  transport (λ i → (x : X) (y : Y) → Q i x y) f
  ≡ (λ (x : X) (y : Y) → transport (λ i → Q i x y) (f x y))
transportTwoDeps {X = X} {Y = Y} {Z = Z} =
  J (λ Z' Q → (f : (x : X) (y : Y) → Z x y)
            → transport (λ i → (x : X) (y : Y) → Q i x y) f
             ≡ (λ (x : X) (y : Y) → transport (λ i → Q i x y) (f x y)))
    λ f → transportRefl f ∙ funExt₂ λ x y → transportRefl (f x y) ⁻¹

equivΣFun-aux3 : (A B C : Type ℓ-zero) (f : A → B) (p : B ≡ C)
    → isEquiv f
    → isEquiv (λ (x : A) → transport (λ i → p i) (f x))
equivΣFun-aux3 A B C f p e = snd (compEquiv (f , e) (_ , isEquivTransport p))

equivΣFun-aux2 : (A B : Type ℓ-zero) (C : A → Type ℓ-zero)
  (D : B → Type ℓ-zero) (f : A → B) (g : (a : A) → C a → D (f a))
  → (b : B) (d : D b)
  → Iso ((Σ (Σ A C)
       (λ a →
          Σ-syntax (f (fst a) ≡ b)
          (λ p → PathP (λ i → D (p i)) (g (fst a) (snd a)) d))))
        (Σ[ x ∈ (Σ[ y ∈ A ] f y ≡ b) ]
          (Σ[ y ∈ C (fst x) ] (PathP (λ i → D ((snd x) i)))
                                         (g (fst x) y) d))
Iso.fun (equivΣFun-aux2 A B C D f g b d) ((a , c) , (p , q)) =
  (a , p) , (c , q)
Iso.inv (equivΣFun-aux2 A B C D f g b d) ((a , p) , (c , q)) =
  (a , c) , (p , q)
Iso.rightInv (equivΣFun-aux2 A B C D f g b d) qd =
  refl
Iso.leftInv (equivΣFun-aux2 A B C D f g b d) qd = refl


equivΣFun-aux1 : (A B : Type ℓ-zero) (C : A → Type ℓ-zero)
  (D : B → Type ℓ-zero) (f : A → B) (g : (a : A) → C a → D (f a))
  → (b : B) (d : D b)
  → Iso (fiber (λ x → f (fst x) , g (fst x) (snd x)) (b , d))
     (Σ[ x ∈ (Σ[ y ∈ A ] f y ≡ b) ]
       (Σ[ y ∈ C (fst x) ] (transport (λ i → D ((snd x) i)))
                                          (g (fst x) y) ≡ d))
equivΣFun-aux1 A B C D f g b d =
  compIso (Σ-cong-iso-snd (λ x → invIso ΣPathIsoPathΣ))
          (compIso (equivΣFun-aux2 A B C D f g b d)
                   (Σ-cong-iso-snd
                    (λ x → Σ-cong-iso-snd λ y
                         → PathPIsoPath (λ i → D ((snd x) i))
                                         (g (fst x) y) d)))

equivInj : {X Y : Type ℓ-zero} (e : X ≃ Y) (x y : X)
         → (equivFun e) x ≡ (equivFun e) y
         → x ≡ y
equivInj e x y p = (Iso.leftInv (equivToIso e) x) ⁻¹
                   ∙ cong (invEq e) p
                   ∙ Iso.leftInv (equivToIso e) y
           
naturalInv : (W X Y Z : Type ℓ-zero) (iso1 : Iso W X) (iso2 : Iso Y Z)
             (f : W → Y) (g : X → Z)
          → ((w : W) → (g ∘ Iso.fun iso1) w ≡ (Iso.fun iso2 ∘ f) w)
          → ((x : X) → (Iso.inv iso2 ∘ g) x ≡ (f ∘ Iso.inv iso1) x)
naturalInv W X Y Z iso1 iso2 f g H x =
  Iso.inv (iso2) (g x)
      ≡⟨ cong (Iso.inv (iso2) ∘ g) ((Iso.rightInv iso1 x) ⁻¹) ⟩
  Iso.inv (iso2) (g (Iso.fun (iso1) (Iso.inv (iso1) x)))
      ≡⟨ cong (Iso.inv (iso2)) (H (Iso.inv (iso1) x)) ⟩
  Iso.inv (iso2) (Iso.fun (iso2) (f (Iso.inv (iso1) x)))
      ≡⟨ Iso.leftInv iso2 (f (Iso.inv (iso1) x)) ⟩
  f (Iso.inv (iso1) x) ∎

squaring : (W X Y Z : Type ℓ-zero) (e1 : W ≃ X) (e2 : Y ≃ Z)
           (f : W → Y) (g : X → Z)
           → (fst e2) ∘ f ≡ g ∘ (fst e1)
           → f ≡ (fst (invEquiv e2)) ∘ g ∘ (fst e1)
squaring W X Y Z e1 e2 f g H =
  funExt (λ x →
    f x
      ≡⟨ Iso.leftInv (equivToIso e2) (f x) ⁻¹ ⟩
    (fst (invEquiv e2)) ((fst e2) (f x))
      ≡⟨ cong (fst (invEquiv e2)) (funExt⁻ H x) ⟩
    (fst (invEquiv e2)) (g ((fst e1) x)) ∎)

ridiculous : (X : Type ℓ-zero)
             (w x y z : X) (p : w ≡ x) (q : x ≡ y) (r : z ≡ y) (s : w ≡ z)
          → p ∙ q ≡ s ∙ r
          → p ∙ q ∙ r ⁻¹ ≡ s
ridiculous X w x y z p q r s H =
  assoc p q (r ⁻¹) ∙ cong (_∙ r ⁻¹) H
                   ∙ assoc s r (r ⁻¹) ⁻¹
                   ∙ cong (s ∙_) (rCancel r)
                   ∙ rUnit s ⁻¹


transportHom : (X : Type ℓ-zero)
                (w x y z : X) (p : w ≡ x) (q : y ≡ z) (r : w ≡ y)
  → transport (λ i → p i ≡ q i) r ≡ p ⁻¹ ∙ r ∙ q
transportHom X w x y z p q r =
  J (λ x' p' → (q : y ≡ z) (r : w ≡ y)
             → transport (λ i → p' i ≡ q i) r ≡ p' ⁻¹ ∙ r ∙ q)
    (λ q' r'
     → J (λ z' q' → (r : w ≡ y)
          → transport (λ i → w ≡ q' i) r ≡ refl ⁻¹ ∙ r ∙ q')
          (λ r'' → transportRefl _ ∙ rUnit r'' ∙ lUnit _) q' r')
    p q r


someΣsEquiv : (A B : Type ℓ-zero) (C : A → Type ℓ-zero)
  (D : B → Type ℓ-zero) (f : A → B) (g : (a : A) → C a → D (f a))
  → isEquiv f → ((a : A) → isEquiv (g a))
  → isEquiv {B = Σ B D} (λ (x : Σ A C) → (f (fst x) , g (fst x) (snd x)))
equiv-proof (someΣsEquiv A B C D f g ef eg) p =
  transport (λ i → isContr (ua (isoToEquiv
                       (equivΣFun-aux1 A B C D f g (fst p) (snd p))) (~ i)))
  (transport
  (λ i →
       isContr (ua (Σ-contractSnd (λ (x : Σ A (λ y → f y ≡ fst p))
                                    → equivΣFun-aux3
                                         (C (fst x))
                                         (D (f (fst x)))
                                         (D (fst p))
                                         (g (fst x))
                                         (λ i → D (snd x i))
                                         (eg (fst x))
                                         .equiv-proof (snd p))) (~ i)))
  (ef .equiv-proof (fst p)))


transportHom' : {X Y : Type ℓ-zero} {Z : X → Type ℓ-zero}
    (s : X → X)
    (f g : (x : X) → Y → Z (s x))
    (h k : (x : X) → Y → Z x)
    (a : (x : X) → Z (s x) → Z x)
    (p : (x : X) (y : Y) → f x y ≡ g x y)
    (q : (x : X) (y : Y) → h x y ≡ k x y)
    (r : (x : X) (y : Y) → a x (g x y) ≡ k x y)
    → transport (λ i → (x : X) (y : Y) → a x (p x y (~ i)) ≡ q x y (~ i)) r
      ≡ λ x y → cong (a x) (p x y) ∙ r x y ∙ (q x y) ⁻¹
transportHom' {X = X} {Y = Y} s f g h k a p q r =
  transportTwoDeps (λ i (x : X) (y : Y) → a x (p x y (~ i)) ≡ q x y (~ i)) r
  ∙ funExt₂ (λ x y → transportHomotopy
                        (cong (a x) (p x y) ⁻¹) (q x y ⁻¹) (r x y))
{- end of the collection of helper lemmas -}


{- definition of a diagram packaged into a dependent sum type -}
ℕ-Diagram : Type (ℓ-suc ℓ-zero)
ℕ-Diagram = Σ[ A ∈ ℕ-Family ] ((n : ℕ) → A (1 + n) → A n)

{- useful translation in a diagram -}
numEqMap : (A : ℕ-Family) (m n : ℕ) → m ≡ n → A m → A n
numEqMap A m n p = J (λ (y : ℕ) (p : m ≡ y) → A m → A y) (λ x → x) p

KDiagram : Type ℓ-zero → ℕ-Diagram
KDiagram X = (λ _ → X) , (λ _ x → x)

{- redefining cones, this is unnecessary -}
ConeℕFam : ℕ-Family → Type (ℓ-zero) → Type (ℓ-zero)
ConeℕFam A X = fCone A X

ConeℕDiag : ℕ-Diagram → Type (ℓ-zero) → Type (ℓ-zero)
ConeℕDiag (A , a) X = dCone A a X

numMapFam : (A : ℕ-Family) (f : ℕ → ℕ) → ℕ-Family
numMapFam A f n = A (f n)

numMapDiag : (A : ℕ-Diagram) (f : ℕ → ℕ)
                  (p : (n : ℕ) → f (1 + n) ≡ (1 + (f n))) → ℕ-Diagram
fst (numMapDiag (A , a) f p) = numMapFam A f
snd (numMapDiag (A , a) f p) n = a (f n)
                               ∘ numEqMap A (f (1 + n)) (1 + (f n)) (p n)


{- characterizes the identity type of cones -}
ConeIdentityType : (A : ℕ-Diagram) (X : Type ℓ-zero)
                → ConeℕDiag A X → ConeℕDiag A X → Type (ℓ-zero)
ConeIdentityType (A , a) X (c , h) (c' , h') =
  Σ[ p ∈ ((n : ℕ) (x : X) → c' n x ≡ c n x) ]
   ((n : ℕ) (x : X) → h' n x ∙ (p n x) ≡ cong (a n) (p (suc n) x) ∙ h n x )

ConeIdentity : (A : ℕ-Diagram) (X : Type ℓ-zero) (c c' : ConeℕDiag A X)
              → ConeIdentityType A X c c' → c ≡ c'
ConeIdentity A X (c , h) (c' , h') (p , H) =
  ΣPathP ((funExt (λ n → funExt λ x → p n x ⁻¹))
         , toPathP (transportHom' suc (λ n → c' (suc n)) (λ n → c (suc n))
                                   c' c (snd A) (λ n → p (suc n)) p h
                  ∙ funExt
                    (λ n → funExt
                            (λ x → ridiculous (fst A n) _ _ _ _
                                               (cong (snd A n) (p (suc n) x))
                                               (h n x) (p n x) (h' n x)
                                               (H n x ⁻¹)))))
                                               

{- maps that will be used to define limits -}
ConeℕFam→Map→ConeℕFam : (A : ℕ-Family)
  (X Y : Type ℓ-zero) → (ConeℕFam A X) → (Y → X) → ConeℕFam A Y
ConeℕFam→Map→ConeℕFam = fCone→map→fCone 

ConeℕDiag→Map→ConeℕDiag : (A : ℕ-Diagram)
  (X Y : Type ℓ-zero) → (ConeℕDiag A X) → (Y → X) → ConeℕDiag A Y
ConeℕDiag→Map→ConeℕDiag (A , a) =
  dCone→map→dCone A a


Map→ConeℕFam-composes : (A : ℕ-Family)
  (X Y Z : Type ℓ-zero) (c : ConeℕFam A X) (f : Z → Y) (g : Y → X)
  → ConeℕFam→Map→ConeℕFam A X Z c (g ∘ f)
  ≡ ConeℕFam→Map→ConeℕFam A Y Z (ConeℕFam→Map→ConeℕFam A X Y c g) f
Map→ConeℕFam-composes A X Y Z c f g = refl

Map→ConeℕDiag-composes : (A : ℕ-Diagram)
  (X Y Z : Type ℓ-zero) (c : ConeℕDiag A X) (f : Z → Y) (g : Y → X)
  → ConeℕDiag→Map→ConeℕDiag A X Z c (g ∘ f)
   ≡ ConeℕDiag→Map→ConeℕDiag A Y Z (ConeℕDiag→Map→ConeℕDiag A X Y c g) f
Map→ConeℕDiag-composes A X Y Z c f g = refl

{- defining limits of diagrams, using the dependent sum definition -}
ℕ-Product : (A : ℕ-Family) → Type (ℓ-suc ℓ-zero)
ℕ-Product A =
  Σ[ P ∈ Type ℓ-zero ]
  Σ[ c ∈ ConeℕFam A P ]
    (isProdCone A P c)

is-ℕ-Product-of : ℕ-Family → Type ℓ-zero → Type (ℓ-suc ℓ-zero)
is-ℕ-Product-of A X =
  Σ[ c ∈ ConeℕFam A X ]
   (isProdCone A X c)

ℕ-Limit : (A : ℕ-Diagram) → Type (ℓ-suc ℓ-zero)
ℕ-Limit (A , a) =
  Σ[ L ∈ Type ℓ-zero ]
  Σ[ c ∈ ConeℕDiag (A , a) L ]
    (isLimitCone A a L c)

is-ℕ-Limit-of : ℕ-Diagram → Type ℓ-zero → Type (ℓ-suc ℓ-zero)
is-ℕ-Limit-of (A , a) X =
  Σ[ c ∈ ConeℕDiag (A , a) X ]
    (isLimitCone A a X c)

LimitInv-composing : (A : ℕ-Diagram) (X Y Z : Type ℓ-zero)
  (l : is-ℕ-Limit-of A X) (e : Z ≃ Y) (c : ConeℕDiag A Y)
  → (fst (invEquiv (_ , snd l Y)) c) ∘ (fst e)
   ≡ (fst (invEquiv (_ , snd l Z))
          (ConeℕDiag→Map→ConeℕDiag A Y Z c (fst e)))
LimitInv-composing A X Y Z l e c =
  EquivJ (λ Z' e' → (fst (invEquiv (_ , snd l Y)) c) ∘ (fst e')
                ≡ (fst (invEquiv (_ , snd l Z'))
                       (ConeℕDiag→Map→ConeℕDiag A Y Z' c (fst e'))))
         refl e

module ProductProperties (A : ℕ-Family) (X : ℕ-Product A) where
  
  Uniqueness : (Y : Type ℓ-zero) (f : Y → (fst X)) (g : Y → (fst X))
            → ConeℕFam→Map→ConeℕFam A (fst X) Y (fst (snd X)) f
             ≡ ConeℕFam→Map→ConeℕFam A (fst X) Y (fst (snd X)) g
           → f ≡ g
  Uniqueness Y f g p =
    equivInj (_ , snd (snd X) Y) f g p


conePath : (A : ℕ-Family) (P P' : Type ℓ-zero)
             (c : fCone A P) (p : P ≃ P')
          → transport (λ i → ConeℕFam A (ua p i)) c
           ≡ ConeℕFam→Map→ConeℕFam A P P' c (equivFun (invEquiv p))
conePath A P P' c p =
  EquivJ (λ Q q → (c' : fCone A Q)
                → transport (λ i → ConeℕFam A (ua q i)) c'
                 ≡ ConeℕFam→Map→ConeℕFam A Q P' c' (equivFun (invEquiv q)))
         (λ c' → cong (λ r → transport (λ i → ConeℕFam A (r i)) c')
                       uaIdEquiv ∙ transportRefl c') p c

conePathD : (A : ℕ-Diagram) (P P' : Type ℓ-zero)
              (c : ConeℕDiag A P) (p : P ≃ P')
           → transport (λ i → ConeℕDiag A (ua p i)) c
            ≡ ConeℕDiag→Map→ConeℕDiag A P P' c (equivFun (invEquiv p))
conePathD A P P' c p = 
  EquivJ (λ Q q → (c' : ConeℕDiag A Q)
                → transport (λ i → ConeℕDiag A (ua q i)) c'
                 ≡ ConeℕDiag→Map→ConeℕDiag A Q P' c' (equivFun (invEquiv q)))
         (λ c' → cong (λ r → transport (λ i → ConeℕDiag A (r i)) c')
                       uaIdEquiv ∙ transportRefl c') p c
     
