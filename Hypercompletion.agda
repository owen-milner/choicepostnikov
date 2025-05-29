{-# OPTIONS --lossy-unification #-}
module Hypercompletion where

open import Cubical.Data.Nat renaming (elim to ℕElim)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Everything
open import Cubical.Functions.FunExtEquiv
open import Cubical.HITs.Truncation
open import Cubical.HITs.Sn
open import Cubical.Homotopy.Connected

open import DiagramSigma
open import DiagramMaps
open import EasyLimMaps
open import PostnikovTowers
open import ChoicePostnikov

{- This file is a bit of a mess -}

mmhh : (X : Type₀) (Y : X → Type₀) (f g h : (x : X) → Y x)
       (p : g ≡ h) → Iso ((x : X) → f x ≡ g x) ((x : X) → f x ≡ h x)
mmhh X Y f g h = J (λ h' p → Iso ((x : X) → f x ≡ g x) ((x : X) → f x ≡ h' x)) idIso

mhhmh : {X : Type₀} {x y z : X} (p : y ≡ z) (q : y ≡ z) (r : x ≡ y)
        → Iso (p ≡ q) (r ∙ p ≡ r ∙ q)
mhhmh p q r = congPathIso λ i → compPathlEquiv r

mhmm : {X : Type₀} {w x y z : X} (p : x ≡ w) (q : x ≡ y) (r : y ≡ z)
       (s : w ≡ z)
       → Iso (p ⁻¹ ∙ q ∙ r ≡ s) (q ⁻¹ ∙ (p ∙ s) ≡ r)
mhmm p q r s = compIso (mhhmh (p ⁻¹ ∙ q ∙ r) s p) (compIso (pathToIso (cong (_≡ p ∙ s) (assoc _ _ _ ∙ cong (_∙ q ∙ r) (rCancel p) ∙ lUnit _ ⁻¹)))
       (compIso (compIso (mhhmh (q ∙ r) (p ∙ s) (q ⁻¹)) (pathToIso (cong (_≡ q ⁻¹ ∙ p ∙ s) (assoc (q ⁻¹) q r ∙ cong (_∙ r) (lCancel _) ∙ lUnit _ ⁻¹)))) symIso))

unitFunIso : (X : Type₀) (f g : Unit → X) → Iso (f ≡ g) (f tt ≡ g tt)
Iso.fun (unitFunIso X f g) p = λ i → p i tt
Iso.inv (unitFunIso X f g) q = funExt (λ _ → q)
Iso.rightInv (unitFunIso X f g) q = refl
Iso.leftInv (unitFunIso X f g) p = refl

hhmm : (A B C D : Type₀) (e₁ : A ≃ B) (e₂ : C ≃ D) (f₁ : A → C) (f₂ : B → D)
     → Iso ((x : A) → f₂ (equivFun e₁ x) ≡  equivFun e₂ (f₁ x))
            (f₂ ≡ (equivFun e₂) ∘ f₁ ∘ (invEq e₁))
hhmm A B C D = EquivJ (λ A' e → (e' : C ≃ D) (f : A' → C) (g : B → D) → Iso ((x : A') → g (equivFun e x) ≡ equivFun e' (f x)) (g ≡ (equivFun e') ∘ f ∘ (invEq e))) (EquivJ (λ C' e → (f : B → C') (g : B → D) → Iso ((x : B) → g x ≡ equivFun e (f x)) (g ≡ (equivFun e) ∘ f)) λ f g → equivToIso funExtEquiv)


hhef : (X Y Z : Type₀) (x' : X) (f : X → Y)
       (y' : Y) (p : (f x') ≡ y') (P : Y → Type₀) (q : Z ≡ P (f x'))
       (g : (y : Y) → P y) (h : Z)
      → Iso (g (f x') ≡ equivFun (pathToEquiv q) h)
         (g y' ≡ equivFun (pathToEquiv (q ∙ cong P p)) h)
hhef X Y Z x' f y'' = J
    (λ y' p → (P : Y → Type₀) (q : Z ≡ P (f x'))
       (g : (y : Y) → P y) (h : Z)
      → Iso (g (f x') ≡ equivFun (pathToEquiv q) h)
         (g y' ≡ equivFun (pathToEquiv (q ∙ cong P p)) h))
    λ P q g h → equivToIso (pathToEquiv (cong (λ q' → (g (f x')
                             ≡ equivFun (pathToEquiv q') h))
                            (rUnit q)))


Π-iso : (X : Type₀) (Y Z : X → Type₀) → ((x : X) → Iso (Y x) (Z x))
        → Iso ((x : X) → Y x) ((x : X) → Z x)
Iso.fun (Π-iso X Y Z theIso) f x = Iso.fun (theIso x) (f x)
Iso.inv (Π-iso X Y Z theIso) g x = Iso.inv (theIso x) (g x)
Iso.rightInv (Π-iso X Y Z theIso) g = funExt (λ x → Iso.rightInv (theIso x) (g x))
Iso.leftInv (Π-iso X Y Z theIso) f = funExt (λ x → Iso.leftInv (theIso x) (f x))


Π2-iso : (X Y : Type₀) (R : (X × Y) → Type₀)
         → Iso ((x : X) (y : Y) → R (x , y)) ((y : Y) (x : X) → R (x , y))
Iso.fun (Π2-iso X Y R) f = λ y x → f x y
Iso.inv (Π2-iso X Y R) g = λ x y → g y x
Iso.rightInv (Π2-iso X Y R) g = refl
Iso.leftInv (Π2-iso X Y R) f = refl

FTIT : {ℓ : Level} (X : Type ℓ) (x : X) → isContr (Σ[ y ∈ X ] x ≡ y)
FTIT X x = (x , refl)
         , (λ yp → J (λ y p → (x , refl) ≡ (y , p)) refl (snd yp))

FTIT' : {ℓ : Level} (X : Type ℓ) (x : X) → isContr (Σ[ y ∈ X ] y ≡ x)
FTIT' X x = (x , refl) , (λ yp → J (λ y p → (x , refl) ≡ (y , sym p)) refl (sym (snd yp)))

TTACIso : (X : Type₀) (Y : X → Type₀) (Z : (x : X) → Y x → Type₀)
       → Iso (Σ[ x ∈ ((x' : X) → Y x') ] ((x' : X) → Z x' (x x')))
          ((x : X) → (Σ[ y ∈ Y x ] Z x y))
Iso.fun (TTACIso X Y Z) (y , z) x = (y x) , (z x)
Iso.inv (TTACIso X Y Z) F = (fst ∘ F) , (snd ∘ F)
Iso.rightInv (TTACIso X Y Z) F = refl
Iso.leftInv (TTACIso X Y Z) (y , z) = refl

TTAC : (X : Type₀) (Y : X → Type₀) (Z : (x : X) → Y x → Type₀)
       → (Σ[ x ∈ ((x' : X) → Y x') ] ((x' : X) → Z x' (x x')))
        ≡ ((x : X) → (Σ[ y ∈ Y x ] Z x y))
TTAC X Y Z = ua (isoToEquiv (TTACIso X Y Z))


ΣContrIso' : (X : Type₀) (x : X) (Y : X → Type₀)
       → isContr X → (Iso (Σ X Y) (Σ Unit (λ _ → Y x)))
ΣContrIso' X x Y cX =
  Σ-cong-iso (isContr→Iso cX isContrUnit)
              λ x' → pathToIso (cong Y (isContr→isProp cX x' x))

ΣContrIso'' : (X : Type₀) → (Iso (Σ Unit (λ _ → X)) (X))
Iso.fun (ΣContrIso'' X) = snd
Iso.inv (ΣContrIso'' X) x = tt , x
Iso.rightInv (ΣContrIso'' X) = λ _ → refl
Iso.leftInv (ΣContrIso'' X) = λ _ → refl
   

ΣContrIso : (X : Type₀) (x : X) (Y : X → Type₀)
       → isContr X → (Iso (Σ X Y) (Y x))
ΣContrIso X x Y cX = compIso (ΣContrIso' X x Y cX) (ΣContrIso'' (Y x))

ΣContr : (X : Type₀) (x : X) (Y : X → Type₀)
       → isContr X → (Σ X Y ≡ (Y x))
ΣContr X x Y x₁ = ua (isoToEquiv (ΣContrIso X x Y x₁))

module identityTypes {ℓ ℓ' : Level} (X : Type ℓ) (x : X) (Y : X → Type ℓ')
                       (r : Y x) (cΣ : isContr (Σ X Y)) where

  F : {y : X} → (x ≡ y) → Y y
  F p = transport (cong Y p) r

  Ff' : (y : X) (q : Y y) → Iso (fiber F q) ((x , r) ≡ (y , q))
  Ff' y q = compIso
            (Σ-cong-iso idIso
             λ p → invIso (PathPIsoPath (λ i → Y (Iso.fun idIso p i)) r q))
             ΣPathPIsoPathPΣ

  Ff'' : (y : X) (q : Y y) → (fiber F q) ≡ ((x , r) ≡ (y , q))
  Ff'' y q = ua (isoToEquiv (Ff' y q))

  Ff : (y : X) (q : Y y) → isContr (fiber F q)
  Ff y q = transport (λ i → isContr (Ff'' y q (~ i)))
                     (isOfHLevelPath 0 cΣ (x , r) (y , q))

  Feq : (y : X) → isEquiv (F {y = y})
  Feq y = record { equiv-proof = Ff y }

  Frefl : F refl ≡ r
  Frefl = transportRefl r


ΠContrIso2 : (X : Type₀) (Z : X → Type₀)
          → Iso ((x : X) → Z x) ((x : X) → Unit → Z x)
Iso.fun (ΠContrIso2 X Z) f = λ x _ → f x
Iso.inv (ΠContrIso2 X Z) g = λ x → g x tt
Iso.rightInv (ΠContrIso2 X Z) g = refl
Iso.leftInv (ΠContrIso2 X Z) f = refl

ΠContrIso1 : (X : Type₀) (Y Z : X → Type₀)
          → ((x : X) → Y x ≡ Unit)
          → Iso ((x : X) → Z x) ((x : X) → (Y x) → Z x)
ΠContrIso1 X Y Z hY = transport (λ i → Iso ((x : X) → Z x) ((x : X) → (funExt hY (~ i)) x → Z x)) (ΠContrIso2 X Z)

ΠContrIso : (X : Type₀) (Y Z : X → Type₀)
         → ((x : X) → isContr (Y x))
         → Iso ((x : X) → Z x) ((x : X) → (Y x) → Z x)
ΠContrIso X Y Z cY = ΠContrIso1 X Y Z (λ x → isContr→≡Unit (cY x))

ΠContr : (X : Type₀) (Y Z : X → Type₀)
         → ((x : X) → isContr (Y x))
         → ((x : X) → Z x) ≡ ((x : X) → (Y x) → Z x)
ΠContr X Y Z cY = ua (isoToEquiv (ΠContrIso X Y Z cY))

◯-Postnikov : Type ℓ-zero → Type ℓ-zero
◯-Postnikov A = fst (ℓim (fst (PostnikovTowerOf A)))

η-Postnikov : (A : Type ℓ-zero) → (A → (◯-Postnikov A))
η-Postnikov A x = (λ n tt → tMap A n x) , λ _ _ → refl


contrDiag : (A : ℕ-Diagram) (x : (n : ℕ) → isContr (fst A n))
          → isContr (fst (ℓim A))
contrDiag A hA = isOfHLevelΣ 0 (isOfHLevelΠ 0 (λ x → isContrΠ (λ _ → hA x))) λ c → isContrΠ (λ n → isContrΠ λ _ → isOfHLevelPath 0 (hA n) (snd A n (c (1 + n) _)) (c n _))

diagEquivIso : (A : ℕ-Diagram)
   → Iso (Σ[ B ∈ ℕ-Diagram ] (EquivOfDiagrams A B))
          (Σ[ B' ∈ (ℕ → Type₀) ]
          Σ[ e ∈ ((n : ℕ) → fst A n ≃ B' n) ]
          Σ[ b ∈ ((n : ℕ) → B' (suc n) → B' n) ]
          ((n : ℕ) → b n ≡ (equivFun (e n)) ∘ (snd A n)
                                              ∘ (invEq (e (suc n)))))
Iso.fun (diagEquivIso A) ((B , b) , ((f , p) , hf)) =
  B , ((λ n → (f n) , (hf n)) ,
  b , λ n → Iso.fun (hhmm (fst A (suc n)) (B (suc n)) (fst A n) (B n)
                           (f (suc n) , hf (suc n)) (f n , hf n)
                           (snd A n) (b n))
                     (p n))
Iso.inv (diagEquivIso A) (B' , (e , b , p)) =
  (B' , b) , ((λ n → fst (e n))
  , λ n → Iso.inv (hhmm (fst A (suc n)) (B' (suc n)) (fst A n) (B' n)
                          (e (suc n)) (e n) (snd A n) (b n)) (p n))
  , λ n → snd (e n)
Iso.rightInv (diagEquivIso A) (B' , (e , b , p)) =
  ΣPathP (refl , (ΣPathP (refl ,
  (ΣPathP (refl ,
          (funExt (λ n → Iso.rightInv
                          (hhmm (fst A (suc n)) (B' (suc n)) (fst A n) (B' n)
                          (e (suc n)) (e n) (snd A n) (b n)) (p n))))))))
Iso.leftInv (diagEquivIso A) ((B , b) , ((f , p) , hf)) =
  ΣPathP (refl , ΣPathP (ΣPathP (refl ,
  (funExt (λ n → Iso.leftInv (hhmm (fst A (suc n)) (B (suc n)) (fst A n)
                                    (B n) (f (suc n) , hf (suc n))
                                          (f n , hf n) (snd A n) (b n))
                              (p n)))) , refl))
                                                       
diagEquivIso' : (A : ℕ-Diagram)
   → Iso (Σ[ B' ∈ (ℕ → Type₀) ]
          Σ[ e ∈ ((n : ℕ) → fst A n ≃ B' n) ]
          Σ[ b ∈ ((n : ℕ) → B' (suc n) → B' n) ]
          ((n : ℕ) → b n ≡ (equivFun (e n)) ∘ (snd A n)
                                              ∘ (invEq (e (suc n)))))
          (Σ[ B' ∈ (ℕ → Type₀) ]
          Σ[ e ∈ B' ≡ fst A ]
          Σ[ b ∈ ((n : ℕ) → B' (suc n) → B' n) ]
          (b ≡ transport (λ i → (n : ℕ) → (e (~ i) (suc n)) → (e (~ i) n))
                         (snd A)))
diagEquivIso' A = invIso (Σ-cong-iso idIso (λ B' → Σ-cong-iso (equivToIso (compEquiv (invEquiv funExtEquiv) (equivΠ (idEquiv ℕ) λ n → (compEquiv (isoToEquiv symIso) univalence)))) λ q → J (λ B p → Iso (Σ[ b ∈ ((n : ℕ) → B (suc n) → B n) ] (b ≡ transport (λ i → (n : ℕ) → (p i (suc n)) → (p i n)) (snd A))) (Σ[ b ∈ ((n : ℕ) → B (suc n) → B n) ] ((n : ℕ) → b n ≡ (equivFun ((equivFun (compEquiv (invEquiv funExtEquiv) (equivΠ (idEquiv ℕ) (λ n → univalence))) p) n)) ∘ (snd A n) ∘ (invEq ((equivFun (compEquiv (invEquiv funExtEquiv) (equivΠ (idEquiv ℕ) (λ n → univalence))) p) (suc n)))))) (Σ-cong-iso idIso (λ b → compIso (invIso (equivToIso funExtEquiv)) (mmhh ℕ (λ n → fst A (suc n) → fst A n) b _ _ (funExt (λ n → funExt λ a → sym (transportRefl _ ∙ transportRefl _ ∙ transportRefl _ ∙ transportRefl _ ∙ cong (transport (λ _ → fst A n) ∘ (snd A n)) (transportRefl _ ∙ transportRefl _ ∙ transportRefl _ ∙ transportRefl _ ∙ transportRefl _))))))) (sym q)))

contrDiagPath : (A : ℕ-Diagram) →
         (Σ[ B ∈ ℕ-Diagram ] (EquivOfDiagrams A B)) ≡
         (Σ[ B' ∈ (ℕ → Type₀) ]
          Σ[ e ∈ B' ≡ fst A ]
          Σ[ b ∈ ((n : ℕ) → B' (suc n) → B' n) ]
          (b ≡ transport (λ i → (n : ℕ) → (e (~ i) (suc n)) → (e (~ i) n))
                         (snd A)))
contrDiagPath A = isoToPath (compIso (diagEquivIso A) (diagEquivIso' A))

contrDiagIsom : (A : ℕ-Diagram) →
         Iso (Σ[ B' ∈ (ℕ → Type₀) ]
          Σ[ e ∈ B' ≡ fst A ]
          Σ[ b ∈ ((n : ℕ) → B' (suc n) → B' n) ]
          (b ≡ transport (λ i → (n : ℕ) → (e (~ i) (suc n)) → (e (~ i) n))
                         (snd A)))
         (Σ[ B ∈ (Σ[ B' ∈ (ℕ → Type₀) ] (B' ≡ fst A)) ]
           Σ[ b ∈ ((n : ℕ) → (fst B) (suc n) → (fst B) n) ]
           (b ≡ transport (λ i → (n : ℕ) → ((snd B) (~ i) (suc n))
                                          → ((snd B) (~ i) n))
                          (snd A)))
Iso.fun (contrDiagIsom A) (B' , e , b , p) = (B' , e) , (b , p)
Iso.inv (contrDiagIsom A) ((B' , e) , b , p) = B' , (e , (b , p))
Iso.rightInv (contrDiagIsom A) = λ t → refl
Iso.leftInv (contrDiagIsom A) = λ t → refl

contrDiagIDID : (A : ℕ-Diagram) → (Σ[ B ∈ (ℕ-Diagram) ] (EquivOfDiagrams A B))
              ≡ (Σ[ B ∈ (Σ[ B' ∈ (ℕ → Type₀) ] (B' ≡ fst A)) ]
                  Σ[ b ∈ ((n : ℕ) → (fst B) (suc n) → (fst B) n) ]
                   (b ≡ transport (λ i → (n : ℕ) → ((snd B) (~ i) (suc n))
                                                  → ((snd B) (~ i) n))
                                  (snd A)))
contrDiagIDID A = contrDiagPath A ∙ isoToPath (contrDiagIsom A)

contrDiagEquiv : (A : ℕ-Diagram) → isContr
                 (Σ[ B ∈ (ℕ-Diagram) ] (EquivOfDiagrams A B))
contrDiagEquiv A = transport (λ i → isContr (contrDiagIDID A (~ i))) (isContrΣ (FTIT' (ℕ → Type₀) (fst A)) λ B → FTIT' ((n : ℕ) → (fst B) (suc n) → (fst B) n) (transport (λ i → (n : ℕ) → ((snd B) (~ i) (suc n)) → ((snd B) (~ i) n)) (snd A)))

DiagEquivId : (A B : ℕ-Diagram) → (A ≡ B) ≃ (EquivOfDiagrams A B)
DiagEquivId A B = (identityTypes.F ℕ-Diagram A (λ B' → EquivOfDiagrams A B') (((λ n x → x) , (λ n x → refl)) , (λ n → snd (idEquiv _))) (contrDiagEquiv A)) , identityTypes.Feq ℕ-Diagram A (λ B' → EquivOfDiagrams A B') (((λ n x → x) , (λ n x → refl)) , (λ n → snd (idEquiv _))) (contrDiagEquiv A) B

-- idk if this isn't elsewhere already
module _ (A B : ℕ-Diagram) (η : EquivOfDiagrams A B) where

  ηE : (n : ℕ) → fst A n ≃ fst B n
  fst (ηE n) = fst (fst η) n
  snd (ηE n) = snd η n

  η⁻¹ : MapOfDiagrams B A
  fst η⁻¹ n = invEq (ηE n)
  snd η⁻¹ n b =
    snd A n (invEq (ηE (suc n)) b)
      ≡⟨ sym (retEq (ηE n) (snd A n (invEq (ηE (suc n)) b))) ⟩
    invEq (ηE n) (fst (fst η) n (snd A n (invEq (ηE (suc n)) b)))
      ≡⟨ cong (invEq (ηE n)) (sym (snd (fst η) n (invEq (ηE (suc n)) b))) ⟩
    invEq (ηE n) (snd B n (fst (fst η) (suc n) (invEq (ηE (suc n)) b)))
      ≡⟨ cong (invEq (ηE n) ∘ (snd B n)) (secEq (ηE (suc n)) b) ⟩
    invEq (ηE n ) (snd B n b) ∎

  {- η-Iso : Iso (fst (ℓim A)) (fst (ℓim B))
  η-Iso = {!!} -}

  η-Iso' : (x : fst (ℓim A)) → MapOfDiagrams→MapOfLimits' A A ((λ n x → x) , (λ n x → refl)) (ℓim A) (ℓim A) x ≡ x
  η-Iso' x = MapOfDiagrams→MapOfLimits' A A ((λ n x → x) , (λ n x → refl)) (ℓim A) (ℓim A) x ≡⟨ ΣPathP (funExt (λ n → funExt (λ _ → refl)) , toPathP (transportRefl _ ∙ (funExt λ n → funExt λ _ → sym (lUnit _)))) ⟩
           ((fst x) , (λ n x₁ → (snd x n x₁))) ≡⟨ refl ⟩
           x ∎

{- transportHomotopy (cong (snd B n) (secEq (ηE (suc n)) (b (suc n) tt))) (secEq (ηE n) (b n tt)) (snd (fst η) n (fst η⁻¹ (suc n) (b (suc n) tt)) ∙ cong (fst (fst η) n) (snd η⁻¹ n (b (suc n) tt) ∙ cong (invEq (ηE n)) (pb n))) ∙ {!!} -}

  
  η-Equiv' : isEquiv (MapOfDiagrams→MapOfLimits' A A ((λ n x → x) , (λ n x → refl)) (ℓim A) (ℓim A))
  η-Equiv' = transport (λ i → isEquiv (funExt (η-Iso') (~ i))) (snd (idEquiv (fst (ℓim A))))

  η-Equiv'' : isEquiv (MapOfDiagrams→MapOfLimits' A A (fst (fst (DiagEquivId A A) refl)) (ℓim A) (ℓim A))
  η-Equiv'' = transport (λ i → isEquiv (MapOfDiagrams→MapOfLimits' A A (fst (identityTypes.Frefl ℕ-Diagram A (λ B' → EquivOfDiagrams A B') (((λ n x → x) , (λ n x → refl)) , λ n → snd (idEquiv (fst A n))) (contrDiagEquiv A) (~ i))) (ℓim A) (ℓim A))) η-Equiv'

  η-Equiv''' : (p : A ≡ B) → isEquiv (MapOfDiagrams→MapOfLimits' A B (fst (fst (DiagEquivId A B) p)) (ℓim A) (ℓim B))
  η-Equiv''' = J (λ B' p → isEquiv (MapOfDiagrams→MapOfLimits' A B' (fst (fst (DiagEquivId A B') p)) (ℓim A) (ℓim B'))) η-Equiv''

  η-Equiv : isEquiv (MapOfDiagrams→MapOfLimits' A B (fst η) (ℓim A) (ℓim B))
  η-Equiv = transport (λ i → isEquiv (MapOfDiagrams→MapOfLimits' A B (fst (secEq (DiagEquivId A B) η i)) (ℓim A) (ℓim B))) (η-Equiv''' (invEq (DiagEquivId A B) η))

module _ (X : Type ℓ-zero) (D : X → ℕ-Diagram) where

  ℓim-D : X → (Type ℓ-zero)
  ℓim-D = λ x → fst (ℓim (D x))

  Π-D : ℕ-Diagram
  fst Π-D = λ n → ((x : X) → fst (D x) n)
  snd Π-D n = λ f x → snd (D x) n (f x)

  Π-ℓim-Iso : Iso ((x : X) → ℓim-D x) (fst (ℓim (Π-D)))
  Iso.fun Π-ℓim-Iso c = (λ n _ x → fst (c x) n _) ,
                         λ n _ → funExt λ x → snd (c x) n _
  Iso.inv Π-ℓim-Iso (k₁ , k₂) =
    λ x → ((λ n _ → k₁ n _ x) ,
            λ n _ → funExt⁻ (k₂ n _) x)
  Iso.rightInv Π-ℓim-Iso (k₁ , k₂) = refl
  Iso.leftInv Π-ℓim-Iso c = refl

module _ (◯ : Type ℓ-zero → Type ℓ-zero)
         (η : (A : Type ℓ-zero) → A → (◯ A))
  where

  eliminationMap : (X : Type ℓ-zero) (P : ◯ X → Type ℓ-zero)
                → ((x : ◯ X) → ◯ (P x)) → ((x : X) → ◯ (P (η X x)))
  eliminationMap X P f = f ∘ (η X)

  isUniquelyEliminating : Type (ℓ-suc ℓ-zero)
  isUniquelyEliminating = (X : Type ℓ-zero) (P : ◯ X → Type ℓ-zero)
                          → isEquiv (eliminationMap X P)

proj : (D : ℕ-Diagram) → (n : ℕ) → (fst (ℓim D)) → (fst D n)
proj D n x = fst x n tt

fillers : (X : Type ℓ-zero) {A B : Type ℓ-zero} → (A → B) → (A → X)
         → Type ℓ-zero
fillers X f g = Σ[ h ∈ (_ → X) ] (h ∘ f ≡ g)

-- fillers and limits
fill-Diag : (D : ℕ-Diagram) {A B : Type ℓ-zero}
            (f : A → B) (g : A → fst (ℓim D))
          → ℕ-Diagram
fst (fill-Diag D f g) n = fillers (fst D n) f ((proj D n) ∘ g)
fst (snd (fill-Diag (D , d) f g) n (h , ph)) = d n ∘ h
snd (snd (fill-Diag (D , d) f g) n (h , ph)) =
  funExt (λ a → cong (d n) (λ i → ph i a)
               ∙ snd (g a) n _)

fill-Contr : (X : Type₀) (cX : isContr X) {A B : Type₀}
                (f : A → B) (g : A → X)
                → isContr (fillers X f g)
fill-Contr X cX f g = ((λ b → fst cX) , (funExt (λ a → snd cX (g a)))) , (λ pr → ΣPathP ((funExt (λ b → snd cX (fst pr b))) , toPathP (isContr→isProp (isOfHLevelPath 0 (isContrΠ (λ _ → cX)) (λ x → funExt (λ b → snd cX (fst pr b)) i1 (f x)) g) (transport
                                                                                                                                                             (λ i → (λ x → funExt (λ b → snd cX (fst pr b)) i (f x)) ≡ g)
                                                                                                                                                             (funExt (λ a → snd cX (g a)))) (snd pr))))

fill-Equiv : (X : Type₀) {A B : Type₀}
             (f : A → B) (g : A → X)
             → isEquiv f
             → isContr (fillers X f g)
fill-Equiv X f g hf = equiv-proof (isEquivPreComp (f , hf)) g

fill-TruncIso1 : (n : ℕ) (X : TypeOfHLevel ℓ-zero (suc n)) {A B : Type₀}
                (f : A → B) (g : A → ⟨ X ⟩)
                → Iso (fillers ⟨ X ⟩ f g)
                       (Σ[ h ∈ (B → ⟨ X ⟩) ] ((a : A) → h (f a) ≡ g a))
fill-TruncIso1 n X f g = Σ-cong-iso idIso (λ h → equivToIso (invEquiv funExtEquiv))


fill-TruncIso2' : (n : ℕ) (X : TypeOfHLevel ℓ-zero (suc n)) {A B : Type₀}
                  (f : A → B) (g : A → ⟨ X ⟩) (h : B → ⟨ X ⟩)
                  → Iso ((a : A) → h (f a) ≡ g a)
                         ((a : A) → rec (snd X) (h ∘ f) ∣ a ∣ₕ ≡ rec (snd X) g ∣ a ∣ₕ)
fill-TruncIso2' n X f g h = idIso


fill-TruncIso2'' : (n : ℕ) (X : TypeOfHLevel ℓ-zero (suc n)) {A B : Type₀}
                  (f : A → B) (g : A → ⟨ X ⟩) (h : B → ⟨ X ⟩)
                  → Iso ((a : A) → rec (snd X) (h ∘ f) ∣ a ∣ₕ ≡ rec (snd X) g ∣ a ∣ₕ)
                         ((a : ∥ A ∥ (suc n)) → rec (snd X) (h ∘ f) a ≡ rec (snd X) g a)
Iso.fun (fill-TruncIso2'' n X f g h) p = elim (λ x → isOfHLevelPath (suc n) (snd X) _ _) p
Iso.inv (fill-TruncIso2'' n X f g h) q = λ a → q ∣ a ∣ₕ
Iso.rightInv (fill-TruncIso2'' n X f g h) q = funExt (elim (λ x → isOfHLevelPath (suc n) (isOfHLevelPath (suc n) (snd X) _ _) _ _) (λ a → refl))
Iso.leftInv (fill-TruncIso2'' n X f g h) p = refl

fill-TruncIso2 : (n : ℕ) (X : TypeOfHLevel ℓ-zero (suc n)) {A B : Type₀}
                (f : A → B) (g : A → ⟨ X ⟩)
                → Iso (Σ[ h ∈ (B → ⟨ X ⟩) ] ((a : A) → h (f a) ≡ g a))
                       (Σ[ h ∈ (B → ⟨ X ⟩) ] ((a : ∥ A ∥ (suc n)) → rec (snd X) (h ∘ f) a ≡ rec (snd X) g a))
fill-TruncIso2 n X f g = Σ-cong-iso idIso (λ h → fill-TruncIso2'' n X f g h)

fill-TruncIso3' : (n : ℕ) (X : TypeOfHLevel ℓ-zero (suc n)) {A B : Type₀}
                (f : A → B) (g : A → ⟨ X ⟩) (h : B → ⟨ X ⟩)
                → Iso ((a : ∥ A ∥ (suc n)) → rec (snd X) (h ∘ f) a ≡ rec (snd X) g a)
                       ((a : ∥ A ∥ (suc n)) → rec (snd X) h (map f a) ≡ rec (snd X) g a)
Iso.fun (fill-TruncIso3' n X f g h) p = elim (λ a → isOfHLevelPath (suc n) (snd X) _ _) (λ a → p ∣ a ∣ₕ)
Iso.inv (fill-TruncIso3' n X f g h) q = elim (λ a → isOfHLevelPath (suc n) (snd X) _ _) (λ a → q ∣ a ∣ₕ)
Iso.rightInv (fill-TruncIso3' n X f g h) q = funExt (elim (λ a → isOfHLevelPath (suc n) (isOfHLevelPath (suc n) (snd X) _ _) _ _) (λ a → refl))
Iso.leftInv (fill-TruncIso3' n X f g h) p = funExt (elim (λ a → isOfHLevelPath (suc n) (isOfHLevelPath (suc n) (snd X) _ _) _ _) (λ a → refl))


fill-TruncIso3 : (n : ℕ) (X : TypeOfHLevel ℓ-zero (suc n)) {A B : Type₀}
                (f : A → B) (g : A → ⟨ X ⟩)
                → Iso (Σ[ h ∈ (B → ⟨ X ⟩) ] ((a : ∥ A ∥ (suc n)) → rec (snd X) (h ∘ f) a ≡ rec (snd X) g a))
                       (Σ[ h ∈ (B → ⟨ X ⟩) ] ((a : ∥ A ∥ (suc n)) → rec (snd X) h (map f a) ≡ rec (snd X) g a))
fill-TruncIso3 n X f g = Σ-cong-iso idIso (λ h → fill-TruncIso3' n X f g h)


fill-TruncIso4 : (n : ℕ) (X : TypeOfHLevel ℓ-zero (suc n)) {A B : Type₀}
                (f : A → B) (g : A → ⟨ X ⟩)
                → Iso (Σ[ h ∈ (B → ⟨ X ⟩) ] ((a : ∥ A ∥ (suc n)) → rec (snd X) h (map f a) ≡ rec (snd X) g a))
                       (Σ[ h ∈ (∥ B ∥ (suc n) → ⟨ X ⟩) ] ((a : ∥ A ∥ (suc n)) → h (map f a) ≡ rec (snd X) g a))
fill-TruncIso4 n X f g = Σ-cong-iso (invIso (univTrunc (suc n))) λ h → idIso

fill-TruncIso : (n : ℕ) (X : TypeOfHLevel ℓ-zero n) {A B : Type₀}
                (f : A → B) (g : A → ⟨ X ⟩)
                → Iso (fillers ⟨ X ⟩ f g)
                       (fillers ⟨ X ⟩ (map {n = n} f) (rec (snd X) g))
fill-TruncIso zero X f g = isContr→Iso (fill-Contr ⟨ X ⟩ (snd X) f g)
                                        (fill-Contr ⟨ X ⟩ (snd X) (map f)
                                                    (rec (snd X) g))
fill-TruncIso (suc n) X f g = compIso (fill-TruncIso1 n X f g) (compIso (fill-TruncIso2 n X f g) (compIso (fill-TruncIso3 n X f g) (compIso (fill-TruncIso4 n X f g) (Σ-cong-iso idIso λ h → equivToIso funExtEquiv))))

fill-TruncEquiv : (n : ℕ) (X : TypeOfHLevel ℓ-zero n) {A B : Type₀}
                (f : A → B) (g : A → ⟨ X ⟩)
                → (fillers ⟨ X ⟩ f g)
                   ≃ (fillers ⟨ X ⟩ (map {n = n} f) (rec (snd X) g))
fill-TruncEquiv n X f g = isoToEquiv (fill-TruncIso n X f g)

fill-TruncIdentity : (n : ℕ) (X : TypeOfHLevel ℓ-zero n) {A B : Type₀}
                (f : A → B) (g : A → ⟨ X ⟩)
                → (fillers ⟨ X ⟩ f g)
                   ≡ (fillers ⟨ X ⟩ (map {n = n} f) (rec (snd X) g))
fill-TruncIdentity n X f g = ua (fill-TruncEquiv n X f g)

fill-limIso1 : (D : ℕ-Diagram) {A B : Type₀}
               (f : A → B) (g : A → fst (ℓim D))
            → Iso (fillers (fst (ℓim D)) f g)
                   (Σ[ h ∈ (_ → fst (ℓim D)) ] ((a : A) → h (f a) ≡ (g a)))
fill-limIso1 D f g = Σ-cong-iso idIso (λ h → equivToIso (invEquiv funExtEquiv))


fill-limIso2 : (D : ℕ-Diagram) {A B : Type₀}
               (f : A → B) (g : A → fst (ℓim D))
            → Iso (Σ[ h ∈ (_ → fst (ℓim D)) ] ((a : A) → h (f a) ≡ (g a)))
                   (Σ[ h ∈ (_ → fst (ℓim D)) ]
                   ((a : A) →
                   Σ[ p ∈ ((n : ℕ) → fst (h (f a)) n _ ≡ fst (g a) n _) ]
                    ((n : ℕ)
                    → transport (λ i → snd D n (p (suc n) i) ≡ (p n i))
                                 (snd (h (f a)) n _)
                     ≡ (snd (g a) n _))))
fill-limIso2 D {A = A} f g = Σ-cong-iso idIso (λ h → Π-iso A (λ a → h (f a) ≡ (g a)) (λ a → Σ[ p ∈ ((n : ℕ) → fst (h (f a)) n _ ≡ fst (g a) n _) ] ((n : ℕ) → transport (λ i → snd D n (p (suc n) i) ≡ (p n i)) (snd (h (f a)) n _ ) ≡ (snd (g a) n _))) λ a → compIso (invIso ΣPathPIsoPathPΣ) (compIso (Σ-cong-iso {B = λ p → PathP (λ i → (n : ℕ) (x : Unit) → snd D n (p i (suc n) x) ≡ (p i n x)) (λ n _ → snd (h (f a)) n _) λ n _ → snd (g a) n _} {B' = λ p → (n : ℕ) → PathP (λ i → (x : Unit) → snd D n (p (suc n) i x) ≡ (p n i x)) (λ _ → snd (h (f a)) n _) λ _ → snd (g a) n _} (equivToIso (invEquiv funExtEquiv)) (λ p → equivToIso (invEquiv funExtEquiv))) (compIso (Σ-cong-iso {B = λ p → (n : ℕ) → PathP (λ i → (x : Unit) → snd D n (p (suc n) i x) ≡ (p n i x)) (λ _ → snd (h (f a)) n _) (λ _ → snd (g a) n _)} {B' = λ p → (n : ℕ) → PathP (λ i → snd D n (p (suc n) i) ≡ (p n i)) (snd (h (f a)) n tt) (snd (g a) n tt)} (Π-iso ℕ (λ n → fst (h (f a)) n ≡ fst (g a) n) (λ n → fst (h (f a)) n tt ≡ fst (g a) n tt) (λ n → unitFunIso (fst D n) (λ _ → fst (h (f a)) n _) (λ _ → (fst (g a)) n _))) (λ p → Π-iso ℕ (λ n → PathP (λ i → (x : Unit) → snd D n (p (suc n) i x) ≡ (p n i x)) (snd (h (f a)) n) (snd (g a) n)) (λ n → PathP (λ i → snd D n (p (suc n) i _) ≡ (p n i _)) (snd (h (f a)) n _) (snd (g a) n _)) (λ n → iso (λ p → λ i → p i tt) (λ q → funExt (λ _ → q)) (λ q → refl) (λ p → refl)))) (Σ-cong-iso idIso (λ p → Π-iso ℕ (λ n → PathP (λ i → snd D n (p (suc n) i) ≡ (p n i)) (snd (h (f a)) n tt) (snd (g a) n tt)) (λ n → transport (λ i → snd D n (p (suc n) i) ≡ (p n i)) (snd (h (f a)) n tt) ≡ (snd (g a) n tt)) (λ n → PathPIsoPath (λ i → snd D n (p (suc n) i) ≡ (p n i)) (snd (h (f a)) n tt) (snd (g a) n tt)))))))

fill-limIso3 : (D : ℕ-Diagram) {A B : Type₀}
               (f : A → B) (g : A → fst (ℓim D))
            → Iso (Σ[ h ∈ (_ → fst (ℓim D)) ]
                   ((a : A) →
                   Σ[ p ∈ ((n : ℕ) → fst (h (f a)) n _ ≡ fst (g a) n _) ]
                    ((n : ℕ)
                    → transport (λ i → snd D n (p (suc n) i) ≡ (p n i))
                                 (snd (h (f a)) n _)
                     ≡ (snd (g a) n _))))
                   (Σ[ h ∈ (B → (n : ℕ) → (fst D) n) ]
                   (Σ[ h' ∈
                       ((b : B) (n : ℕ) → snd D n (h b (suc n)) ≡ h b n) ]
                   ((a : A) →
                   Σ[ p ∈ ((n : ℕ) → h (f a) n ≡ fst (g a) n _) ]
                    ((n : ℕ)
                    → transport (λ i → snd D n (p (suc n) i) ≡ (p n i))
                                 (h' (f a) n)
                     ≡ (snd (g a) n _)))))
Iso.fun (fill-limIso3 D f g) (h , p) = (λ b n → fst (h b) n tt) , (λ b n → snd (h b) n tt) , p
Iso.inv (fill-limIso3 D f g) (h , h2 , p) = (λ b → (λ n _ → h b n) , (λ n _ → h2 b n)) , p
Iso.rightInv (fill-limIso3 D f g) = λ t → refl
Iso.leftInv (fill-limIso3 D f g) = λ t → refl


fill-limIso4 : (D : ℕ-Diagram) {A B : Type₀}
               (f : A → B) (g : A → fst (ℓim D))
            → Iso (Σ[ h ∈ (B → (n : ℕ) → (fst D) n) ]
                   (Σ[ h' ∈
                       ((b : B) (n : ℕ) → snd D n (h b (suc n)) ≡ h b n) ]
                   ((a : A) →
                   Σ[ p ∈ ((n : ℕ) → h (f a) n ≡ fst (g a) n _) ]
                    ((n : ℕ)
                    → transport (λ i → snd D n (p (suc n) i) ≡ (p n i))
                                 (h' (f a) n)
                     ≡ (snd (g a) n _)))))
                   (Σ[ h ∈ (B → (n : ℕ) → (fst D) n) ]
                    Σ[ p ∈ ((a : A) (n : ℕ) → h (f a) n ≡ fst (g a) n _) ]
                   (Σ[ h' ∈
                       ((b : B) (n : ℕ) → snd D n (h b (suc n)) ≡ h b n) ]
                   ((a : A) →
                    ((n : ℕ)
                    → transport (λ i → snd D n (p a (suc n) i) ≡ (p a n i))
                                 (h' (f a) n)
                     ≡ (snd (g a) n _)))))
Iso.fun (fill-limIso4 D f g) (h , h' , p) = h , ((λ a → fst (p a)) , (h' , (λ a → snd (p a))))
Iso.inv (fill-limIso4 D f g) (h , p , h' , q) = h , (h' , (λ a → (p a) , (q a)))
Iso.rightInv (fill-limIso4 D f g) = λ t → refl
Iso.leftInv (fill-limIso4 D f g) = λ t → refl

fill-limIso5 : (D : ℕ-Diagram) {A B : Type₀}
               (f : A → B) (g : A → fst (ℓim D))
            → Iso (Σ[ h ∈ (B → (n : ℕ) → (fst D) n) ]
                    Σ[ p ∈ ((a : A) (n : ℕ) → h (f a) n ≡ fst (g a) n _) ]
                   (Σ[ h' ∈
                       ((b : B) (n : ℕ) → snd D n (h b (suc n)) ≡ h b n) ]
                   ((a : A) →
                    ((n : ℕ)
                    → transport (λ i → snd D n (p a (suc n) i) ≡ (p a n i))
                                 (h' (f a) n)
                     ≡ (snd (g a) n _)))))
                   (Σ[ h ∈ (B → (n : ℕ) → (fst D) n) ]
                    Σ[ p ∈ ((a : A) (n : ℕ) → h (f a) n ≡ fst (g a) n _) ]
                   (Σ[ h' ∈
                       ((b : B) (n : ℕ) → snd D n (h b (suc n)) ≡ h b n) ]
                   ((a : A) →
                    ((n : ℕ)
                    → cong (snd D n) (p a (suc n)) ⁻¹ ∙ (h' (f a) n)
                                                      ∙ p a n
                     ≡ (snd (g a) n _)))))
fill-limIso5 D {A = A} f g = Σ-cong-iso idIso (λ h → Σ-cong-iso idIso (λ p → Σ-cong-iso idIso (λ h' → Π-iso A (λ a → (n : ℕ) → transport (λ i → snd D n (p a (suc n) i) ≡ (p a n i)) (h' (f a) n) ≡ (snd (g a) n _)) (λ a → (n : ℕ) → cong (snd D n) (p a (suc n)) ⁻¹ ∙ (h' (f a) n) ∙ p a n ≡ (snd (g a) n _)) λ a → Π-iso ℕ (λ n → transport (λ i → snd D n (p a (suc n) i) ≡ (p a n i)) (h' (f a) n) ≡ (snd (g a) n _)) (λ n → cong (snd D n) (p a (suc n)) ⁻¹ ∙ (h' (f a) n) ∙ p a n ≡ (snd (g a) n _)) (λ n → pathToIso (cong (_≡ (snd (g a) n _)) (transportHomotopy (cong (snd D n) (p a (suc n))) (p a n) (h' (f a) n)))))))


fill-limIso' : (D : ℕ-Diagram) {A B : Type₀}
              (f : A → B) (g : A → fst (ℓim D))
           → Iso (Σ[ h ∈ (B → (n : ℕ) → (fst D) n) ]
                    Σ[ p ∈ ((a : A) (n : ℕ) → h (f a) n ≡ fst (g a) n _) ]
                   (Σ[ h' ∈
                       ((b : B) (n : ℕ) → snd D n (h b (suc n)) ≡ h b n) ]
                   ((a : A) →
                    ((n : ℕ)
                    → cong (snd D n) (p a (suc n)) ⁻¹ ∙ (h' (f a) n)
                                                      ∙ p a n
                     ≡ (snd (g a) n _)))))
                   (Σ[ h ∈ (B → (n : ℕ) → (fst D) n) ]
                    Σ[ p ∈ ((a : A) (n : ℕ) → h (f a) n ≡ fst (g a) n _) ]
                   (Σ[ h' ∈
                       ((b : B) (n : ℕ) → snd D n (h b (suc n)) ≡ h b n) ]
                   ((a : A) →
                   ((n : ℕ) →
                   (h' (f a) n) ⁻¹ ∙ (cong (snd D n) (p a (suc n))
                                      ∙ (snd (g a) n _))
                   ≡ (p a n)))))
fill-limIso' D f g = Σ-cong-iso idIso (λ h → Σ-cong-iso idIso (λ p → Σ-cong-iso idIso λ h' → Π-iso _ (λ a → (n : ℕ) → cong (snd D n) (p a (suc n)) ⁻¹ ∙ (h' (f a) n) ∙ p a n ≡ (snd (g a) n _)) (λ a → (n : ℕ) → (h' (f a) n) ⁻¹ ∙ (cong (snd D n) (p a (suc n)) ∙ (snd (g a) n _)) ≡ (p a n)) (λ a → Π-iso ℕ (λ n → cong (snd D n) (p a (suc n)) ⁻¹ ∙ (h' (f a) n) ∙ p a n ≡ (snd (g a) n _)) (λ n → (h' (f a) n) ⁻¹ ∙ (cong (snd D n) (p a (suc n)) ∙ (snd (g a) n _)) ≡ (p a n)) (λ n → mhmm _ _ _ _))))


fill-limIsoAA : (D : ℕ-Diagram) {A B : Type₀} (f : A → B) (g : A → fst (ℓim D)) → Iso (Σ[ h ∈ (B → (n : ℕ) → (fst D) n) ]
                    Σ[ p ∈ ((a : A) (n : ℕ) → h (f a) n ≡ fst (g a) n _) ]
                   (Σ[ h' ∈
                       ((b : B) (n : ℕ) → snd D n (h b (suc n)) ≡ h b n) ]
                   ((a : A) →
                   ((n : ℕ) →
                   (h' (f a) n) ⁻¹ ∙ (cong (snd D n) (p a (suc n))
                                      ∙ (snd (g a) n _))
                   ≡ (p a n)))))
         (Σ[ h ∈ (B → (n : ℕ) → (fst D) n) ]
                    Σ[ p ∈ ((n : ℕ) (a : A) →
                      h (f a) n ≡ fst (g a) n _) ]
                   (Σ[ h' ∈
                       ((b : B) (n : ℕ) → snd D n (h b (suc n)) ≡ h b n) ]
                   (((n : ℕ) (a : A) →
                   (h' (f a) n) ⁻¹ ∙ (cong (snd D n) ((p (suc n) a))
                                      ∙ (snd (g a) n _))
                   ≡ (p n a)))))
fill-limIsoAA D f g = Σ-cong-iso idIso (λ h → Σ-cong-iso (Π2-iso _ ℕ _) λ p → Σ-cong-iso idIso (λ h' → Π2-iso _ ℕ _))

fill-limIsoAB : (D : ℕ-Diagram) {A B : Type₀} (f : A → B) (g : A → fst (ℓim D)) → Iso (Σ[ h ∈ (B → (n : ℕ) → (fst D) n) ]
                    Σ[ p ∈ ((n : ℕ) (a : A) →
                      h (f a) n ≡ fst (g a) n _) ]
                   (Σ[ h' ∈
                       ((b : B) (n : ℕ) → snd D n (h b (suc n)) ≡ h b n) ]
                   (((n : ℕ) (a : A) →
                   (h' (f a) n) ⁻¹ ∙ (cong (snd D n) ((p (suc n) a))
                                      ∙ (snd (g a) n _))
                   ≡ (p n a)))))
         (Σ[ h ∈ ((n : ℕ) → B → (fst D) n) ]
                    Σ[ p ∈ ((n : ℕ) (a : A) →
                      h n (f a) ≡ fst (g a) n _) ]
                   (Σ[ h' ∈
                       ((n : ℕ) (b : B) → snd D n (h (suc n) b) ≡ h n b) ]
                   (((n : ℕ) (a : A) →
                   (h' n (f a)) ⁻¹ ∙ (cong (snd D n) ((p (suc n) a))
                                      ∙ (snd (g a) n _))
                   ≡ (p n a)))))
fill-limIsoAB D f g = Σ-cong-iso (Π2-iso _ ℕ (λ p → fst D (snd p)))
  λ h → Σ-cong-iso idIso (λ p → Σ-cong-iso (Π2-iso _ ℕ _) (λ h' → idIso))

fill-limIsoB : (D : ℕ-Diagram) {A B : Type₀} (f : A → B) (g : A → fst (ℓim D))
            → Iso (Σ[ h ∈ ((n : ℕ) → B → (fst D) n) ]
                    Σ[ p ∈ ((n : ℕ) (a : A) →
                      h n (f a) ≡ fst (g a) n _) ]
                   (Σ[ h' ∈
                       ((n : ℕ) (b : B) → snd D n (h (suc n) b) ≡ h n b) ]
                   (((n : ℕ) (a : A) →
                   (h' n (f a)) ⁻¹ ∙ (cong (snd D n) ((p (suc n) a))
                                      ∙ (snd (g a) n _))
                   ≡ (p n a)))))
                   (Σ[ c ∈ ((n : ℕ)
                   → Σ[ h ∈ (B → (fst D) n) ]
                   ((a : A) → h (f a) ≡ fst (g a) n _)) ]
                   ((n : ℕ) → Σ[ h' ∈ ((b : B)
                            → snd D n (fst (c (suc n)) b) ≡ fst (c n) b) ]
                    ((a : A) → (h' (f a)) ⁻¹
                                 ∙ (cong (snd D n) (snd (c (suc n)) a)
                                 ∙ (snd (g a) n _))
                              ≡ (snd (c n) a))))
Iso.fun (fill-limIsoB D f g) (h , p , h' , q) = (λ n → (h n) , (p n)) , (λ n → (h' n) , (q n))
Iso.inv (fill-limIsoB D f g) (c , d) = fst ∘ c , (snd ∘ c) , ((fst ∘ d) , (snd ∘ d))
Iso.rightInv (fill-limIsoB D f g) = λ t → refl
Iso.leftInv (fill-limIsoB D f g) = λ t → refl

fill-limIsoC : (D : ℕ-Diagram) {A B : Type₀} (f : A → B) (g : A → fst (ℓim D))
            → Iso (Σ[ c ∈ ((n : ℕ)
                   → Σ[ h ∈ (B → (fst D) n) ]
                   ((a : A) → h (f a) ≡ fst (g a) n _)) ]
                   ((n : ℕ) → Σ[ h' ∈ ((b : B)
                            → snd D n (fst (c (suc n)) b) ≡ fst (c n) b) ]
                    ((a : A) → (h' (f a)) ⁻¹
                                 ∙ (cong (snd D n) (snd (c (suc n)) a)
                                 ∙ (snd (g a) n _))
                              ≡ (snd (c n) a))))
                   (Σ[ c ∈ ((n : ℕ) → Σ[ h ∈ (B → (fst D) n) ]
                                       h ∘ f ≡ (λ a → fst (g a) n _)) ]
                    ((n : ℕ) →
                    Σ[ h' ∈ snd D n ∘ (fst (c (suc n))) ≡ fst (c n) ]
                    ((a : A) → funExt⁻ (h') (f a) ⁻¹
                                ∙ cong (snd D n) (funExt⁻ (snd (c (suc n))) a)
                                ∙ (snd (g a) n _)
                              ≡ funExt⁻ (snd (c n)) a)))
fill-limIsoC D f g = Σ-cong-iso (Π-iso ℕ _ _ (λ n → Σ-cong-iso idIso (λ h → funExtIso))) (λ c → Π-iso ℕ _ _ λ n → Σ-cong-iso funExtIso (λ h' → idIso))

fill-limIsoD : (D : ℕ-Diagram) {A B : Type₀} (f : A → B) (g : A → fst (ℓim D))
            → Iso (Σ[ c ∈ ((n : ℕ) → Σ[ h ∈ (B → (fst D) n) ]
                                       h ∘ f ≡ (λ a → fst (g a) n _)) ]
                    ((n : ℕ) →
                    Σ[ h' ∈ snd D n ∘ (fst (c (suc n))) ≡ fst (c n) ]
                    ((a : A) → funExt⁻ (h') (f a) ⁻¹
                                ∙ cong (snd D n) (funExt⁻ (snd (c (suc n))) a)
                                ∙ (snd (g a) n _)
                              ≡ funExt⁻ (snd (c n)) a)))
                  (Σ[ c ∈ ((n : ℕ) → Σ[ h ∈ (B → (fst D) n) ]
                                       h ∘ f ≡ (λ a → fst (g a) n _)) ]
                    ((n : ℕ) →
                    Σ[ h' ∈ snd D n ∘ (fst (c (suc n))) ≡ fst (c n) ]
                    ((a : A) → funExt⁻ (cong (_∘ f) h' ⁻¹ ∙ 
                                 funExt (λ a → cong (snd D n) (funExt⁻ (snd (c (suc n))) a)
                                ∙ (snd (g a) n _))) a
                              ≡ funExt⁻ (snd (c n)) a)))
fill-limIsoD D f g = idIso

fill-limIsoE : (D : ℕ-Diagram) {A B : Type₀} (f : A → B) (g : A → fst (ℓim D))
           → Iso  (Σ[ c ∈ ((n : ℕ) → Σ[ h ∈ (B → (fst D) n) ]
                                       h ∘ f ≡ (λ a → fst (g a) n _)) ]
                    ((n : ℕ) →
                    Σ[ h' ∈ snd D n ∘ (fst (c (suc n))) ≡ fst (c n) ]
                    ((a : A) → funExt⁻ (cong (_∘ f) h' ⁻¹ ∙ 
                                 funExt (λ a → cong (snd D n) (funExt⁻ (snd (c (suc n))) a)
                                ∙ (snd (g a) n _))) a
                              ≡ funExt⁻ (snd (c n)) a)))
                    (Σ[ c ∈ ((n : ℕ) → Σ[ h ∈ (B → (fst D) n) ]
                                       h ∘ f ≡ (λ a → fst (g a) n _)) ]
                    ((n : ℕ) →
                    Σ[ h' ∈ snd D n ∘ (fst (c (suc n))) ≡ fst (c n) ]
                    (funExt⁻ (cong (_∘ f) h' ⁻¹ ∙ 
                                 funExt (λ a → cong (snd D n) (funExt⁻ (snd (c (suc n))) a)
                                ∙ (snd (g a) n _)))
                              ≡ funExt⁻ (snd (c n)))))
fill-limIsoE D f g = Σ-cong-iso idIso (λ c → Π-iso ℕ _ _ λ n → Σ-cong-iso idIso (λ h' → funExtIso))


fill-limIsoF : (D : ℕ-Diagram) {A B : Type₀} (f : A → B) (g : A → fst (ℓim D))
           → Iso (Σ[ c ∈ ((n : ℕ) → Σ[ h ∈ (B → (fst D) n) ]
                                       h ∘ f ≡ (λ a → fst (g a) n _)) ]
                    ((n : ℕ) →
                    Σ[ h' ∈ snd D n ∘ (fst (c (suc n))) ≡ fst (c n) ]
                    (funExt⁻ (cong (_∘ f) h' ⁻¹ ∙ 
                                 funExt (λ a → cong (snd D n) (funExt⁻ (snd (c (suc n))) a)
                                ∙ (snd (g a) n _)))
                              ≡ funExt⁻ (snd (c n)))))
              (Σ[ c ∈ ((n : ℕ) → Σ[ h ∈ (B → (fst D) n) ]
                                       h ∘ f ≡ (λ a → fst (g a) n _)) ]
                    ((n : ℕ) →
                    Σ[ h' ∈ snd D n ∘ (fst (c (suc n))) ≡ fst (c n) ]
                    (cong (_∘ f) h' ⁻¹ ∙ 
                                 funExt (λ a → cong (snd D n) (funExt⁻ (snd (c (suc n))) a)
                                ∙ (snd (g a) n _))
                              ≡ snd (c n))))
fill-limIsoF D f g = Σ-cong-iso idIso (λ c → Π-iso ℕ _ _ λ n → Σ-cong-iso idIso (λ h' → congPathIso (λ i → funExtEquiv)))


fill-limIsoG : (D : ℕ-Diagram) {A B : Type₀} (f : A → B) (g : A → fst (ℓim D))
             → Iso  (Σ[ c ∈ ((n : ℕ) → Σ[ h ∈ (B → (fst D) n) ]
                                       h ∘ f ≡ (λ a → fst (g a) n _)) ]
                    ((n : ℕ) →
                    Σ[ h' ∈ snd D n ∘ (fst (c (suc n))) ≡ fst (c n) ]
                    (cong (_∘ f) h' ⁻¹ ∙ 
                                 funExt (λ a → cong (snd D n) (funExt⁻ (snd (c (suc n))) a)
                                ∙ (snd (g a) n _))
                              ≡ snd (c n))))
                     (Σ[ c ∈ (((n : ℕ) → Unit →
                             Σ[ h ∈ (B → fst D n) ] h ∘ f
                                         ≡ (λ x → fst (g x) n tt))) ]
                     ((n : ℕ) (x : Unit)
                     → Σ[ h' ∈ snd D n ∘ (fst (c (suc n) tt))
                              ≡ (fst (c n tt)) ]
                         cong (_∘ f) h' ⁻¹
                         ∙ (funExt (λ a → cong (snd D n)
                            (funExt⁻ (snd (c (suc n) tt)) a)
                         ∙ snd (g a) n tt)) ≡ (snd (c n tt))))
fill-limIsoG D f g = Σ-cong-iso (ΠContrIso2 ℕ _) (λ c → ΠContrIso2 ℕ _)

fill-limIsoA : (D : ℕ-Diagram) {A B : Type₀} (f : A → B) (g : A → fst (ℓim D))
           → Iso (Σ[ c ∈ (((n : ℕ) → Unit →
                             Σ[ h ∈ (B → fst D n) ] h ∘ f
                                         ≡ (λ x → fst (g x) n tt))) ]
                     ((n : ℕ) (x : Unit)
                     → (((snd D n) ∘ (fst (c (suc n) tt)))
                         , (funExt (λ a → cong (snd D n)
                                    (λ i → (snd (c (suc n) tt)) i a)
                           ∙ snd (g a) n _)))
                     ≡ c n x))
                  (Σ[ c ∈ (((n : ℕ) → Unit →
                             Σ[ h ∈ (B → fst D n) ] h ∘ f
                                         ≡ (λ x → fst (g x) n tt))) ]
                     ((n : ℕ) (x : Unit)
                     → Σ[ h' ∈ snd D n ∘ (fst (c (suc n) tt))
                              ≡ (fst (c n tt)) ]
                         cong (_∘ f) h' ⁻¹
                         ∙ (funExt (λ a → cong (snd D n)
                            (funExt⁻ (snd (c (suc n) tt)) a)
                         ∙ snd (g a) n tt)) ≡ (snd (c n tt))))
fill-limIsoA D f g = Σ-cong-iso idIso (λ c → Π-iso ℕ (λ n → (x : Unit)
                     → (((snd D n) ∘ (fst (c (suc n) tt)))
                         , (funExt (λ a → cong (snd D n)
                                    (λ i → (snd (c (suc n) tt)) i a)
                           ∙ snd (g a) n _)))
                     ≡ c n x) (λ n → (x : Unit)
                     → Σ[ h' ∈ snd D n ∘ (fst (c (suc n) tt))
                              ≡ (fst (c n tt)) ]
                         cong (_∘ f) h' ⁻¹
                         ∙ (funExt (λ a → cong (snd D n)
                            (funExt⁻ (snd (c (suc n) tt)) a)
                         ∙ snd (g a) n tt)) ≡ (snd (c n tt)))
                     λ n → Π-iso Unit (λ x → (((snd D n) ∘ (fst (c (suc n) tt)))
                         , (funExt (λ a → cong (snd D n)
                                    (λ i → (snd (c (suc n) tt)) i a)
                           ∙ snd (g a) n _)))
                     ≡ c n x) (λ x → Σ[ h' ∈ snd D n ∘ (fst (c (suc n) tt))
                              ≡ (fst (c n tt)) ]
                         cong (_∘ f) h' ⁻¹
                         ∙ (funExt (λ a → cong (snd D n)
                            (funExt⁻ (snd (c (suc n) tt)) a)
                         ∙ snd (g a) n tt)) ≡ (snd (c n tt)))
                    λ _ → compIso (invIso ΣPathPIsoPathPΣ) (Σ-cong-iso idIso (λ h' → compIso (PathPIsoPath (λ i → h' i ∘ f ≡ (λ x₁ → fst (g x₁) n tt)) (funExt
                                                                                                                                                         (λ a → (λ i → snd D n (snd (c (suc n) tt) i a)) ∙ snd (g a) n tt)) (c n _ .snd)) (pathToIso (cong (_≡ snd (c n tt)) (transportHomotopy (λ i x₁ → h' i (f x₁)) (λ i x₁ → fst (g x₁) n tt) (funExt
                                                                                                                                                                                                                                                                                                                                                    (λ a → (λ i → snd D n (snd (c (suc n) tt) i a)) ∙ snd (g a) n tt)) ∙ assoc _ _ _ ∙ rUnit _ ⁻¹))))))
           

fill-limIso : (D : ℕ-Diagram) {A B : Type ℓ-zero}
           (f : A → B) (g : A → fst (ℓim D))
         → Iso (fillers (fst (ℓim D)) f g)
                (fst (ℓim (fill-Diag D f g)))
fill-limIso D f g = compIso (compIso (compIso (compIso (compIso (compIso (compIso (compIso (compIso (compIso (compIso (compIso (compIso (compIso (fill-limIso1 D f g) (fill-limIso2 D f g)) (fill-limIso3 D f g)) (fill-limIso4 D f g)) (fill-limIso5 D f g)) (fill-limIso' D f g)) (fill-limIsoAA D f g)) (fill-limIsoAB D f g)) (fill-limIsoB D f g)) (fill-limIsoC D f g)) (fill-limIsoD D f g)) (fill-limIsoE D f g)) (fill-limIsoF D f g)) (fill-limIsoG D f g)) (invIso (fill-limIsoA D f g))

fill-limEquiv : (D : ℕ-Diagram) {A B : Type ℓ-zero}
           (f : A → B) (g : A → fst (ℓim D))
         → (fillers (fst (ℓim D)) f g) ≃ (fst (ℓim (fill-Diag D f g)))
fill-limEquiv D f g = isoToEquiv (fill-limIso D f g)

fill-limIdentity : (D : ℕ-Diagram) {A B : Type ℓ-zero}
           (f : A → B) (g : A → fst (ℓim D))
         → (fillers (fst (ℓim D)) f g) ≡ (fst (ℓim (fill-Diag D f g)))
fill-limIdentity D f g = ua (fill-limEquiv D f g)

--map→fibProj : {A B : Type₀} (f : A → B) → 
fill-DepTy : (X : Type₀) (Y : X → Type₀)
             {A B : Type₀} (f : A → B) (g : A → Σ X Y)
          → fillers X f (λ a → fst (g a)) → (b : B) → Type ℓ-zero
fill-DepTy X Y f g (h , ph) b =
  fillers
    (Y (h b))
    (λ (_ : fiber f b) → tt)
    λ a → equivFun (pathToEquiv (cong Y (funExt⁻ (sym ph) (fst a))
                                  ∙ cong (Y ∘ h) (snd a)))
                    (snd (g (fst a)))

fill-ΣIso1 : (X : Type₀) (Y : X → Type₀)
             {A B : Type₀} (f : A → B) (g : A → Σ X Y)
             → Iso (Σ[ h ∈ (B → (Σ X Y)) ] (h ∘ f ≡ g))
                (Σ[ h ∈ (Σ[ h1 ∈ (B → X) ] ((b : B) → Y (h1 b))) ]
                  (Σ[ p ∈ (fst h) ∘ f ≡ (λ a → fst (g a)) ]
                    (snd h) ∘ f ≡
                    λ a → equivFun (pathToEquiv (cong Y (funExt⁻ (sym p) a)))
                                    (snd (g a))))
Iso.fun (fill-ΣIso1 X Y f g) (h , p) =
  ((fst ∘ h) , (λ b → snd (h b)))
  , (cong (fst ∘_) p) , sym (funExt (λ a → fromPathP
                            (snd (PathPΣ (funExt⁻ (sym p) a)))))
Iso.inv (fill-ΣIso1 X Y f g) ((h , h2) , p , q) =
  (λ b → (h b) , h2 b) ,
  funExt (λ b → ΣPathP ((funExt⁻ p b)
         , symP (toPathP (sym (funExt⁻ q b)))))
Iso.rightInv (fill-ΣIso1 X Y {A = A} f g) ((h , h2) , p , q) = ΣPathP (refl , (ΣPathP (refl , ((sym (funExt (λ a → fromPathP
                            (snd (PathPΣ (funExt⁻ (sym (funExt (λ b → ΣPathP ((funExt⁻ p b)
         , symP (toPathP (sym (funExt⁻ q b))))))) a))))))
         ≡⟨ refl ⟩
      sym (funExt λ a → fromPathP (snd (PathPΣ (sym (ΣPathP {A = λ _ → A → X} {B = λ i hh → Y (hh a) } (p , symP (toPathP (sym (funExt⁻ q a)))))))))
         ≡⟨ refl ⟩
      sym (funExt λ a → fromPathP (toPathP (sym (funExt⁻ q a))))
         ≡⟨ cong (sym ∘ funExt) (funExt (λ a → Iso.rightInv (PathPIsoPath (λ i → Y ((p (~ i)) a)) (snd (g a)) (h2 (f a))) (sym (funExt⁻ q a)))) ⟩
      sym (funExt λ a → sym (funExt⁻ q a))
         ≡⟨ refl ⟩
      q ∎))))
Iso.leftInv (fill-ΣIso1 X Y f g) (h , p) = ΣPathP (refl ,
  ((funExt (λ b → ΣPathP ((funExt⁻ ((cong (fst ∘_) p)) b)
   , symP (toPathP (sym (funExt⁻ (sym (funExt (λ a → fromPathP
                            (snd (PathPΣ (funExt⁻ (sym p) a)))))) b)))))) ≡⟨ refl ⟩ funExt (λ b → ΣPathP ((funExt⁻ ((cong (fst ∘_) p)) b)
     , symP (toPathP (fromPathP (snd (PathPΣ (funExt⁻ (sym p) b))))))) ≡⟨ cong (funExt) (funExt (λ b → cong (ΣPathP) (ΣPathP (refl , (cong (symP) (Iso.leftInv (PathPIsoPath (λ i → Y (cong (fst ∘_) p (~ i) b)) (snd (g b)) (snd (h (f b)))) (snd (PathPΣ (funExt⁻ (sym p) b))))))))) ⟩ funExt (λ b → ΣPathP ((funExt⁻ ((cong (fst ∘_) p)) b)
     , symP (snd (PathPΣ (funExt⁻ (sym p) b))))) ≡⟨ refl ⟩ p ∎))

fill-ΣIso2 : (X : Type₀) (Y : X → Type₀)
             {A B : Type₀} (f : A → B) (g : A → Σ X Y)
             → Iso (Σ[ h ∈ (Σ[ h1 ∈ (B → X) ] ((b : B) → Y (h1 b))) ]
                  (Σ[ p ∈ (fst h) ∘ f ≡ (λ a → fst (g a)) ]
                    (snd h) ∘ f ≡
                    λ a → equivFun (pathToEquiv (cong Y (funExt⁻ (sym p) a)))
                                    (snd (g a))))
                (Σ[ h ∈ (Σ[ h1 ∈ (B → X) ] ((b : B) → Y (h1 b))) ]
                  (Σ[ p ∈ (fst h) ∘ f ≡ (λ a → fst (g a)) ]
                    ((a : A) → ((snd h) (f a)) ≡
                    equivFun (pathToEquiv (cong Y (funExt⁻ (sym p) a)))
                              (snd (g a)))))
fill-ΣIso2 X Y f g = Σ-cong-iso idIso (λ h → Σ-cong-iso idIso (λ p → invIso (equivToIso funExtEquiv)))


fill-ΣIso3 : (X : Type₀) (Y : X → Type₀)
             {A B : Type₀} (f : A → B) (g : A → Σ X Y)
             → Iso (Σ[ h ∈ (Σ[ h1 ∈ (B → X) ] ((b : B) → Y (h1 b))) ]
                  (Σ[ p ∈ (fst h) ∘ f ≡ (λ a → fst (g a)) ]
                    ((a : A) → ((snd h) (f a)) ≡
                    equivFun (pathToEquiv (cong Y (funExt⁻ (sym p) a)))
                              (snd (g a)))))
                (Σ[ F ∈ (Σ[ h1 ∈ (B → X) ] (h1 ∘ f ≡ (λ a → fst (g a)))) ]
                 Σ[ h2 ∈ ((b : B) → Y (fst F b)) ]
                 ((a : A) → (h2 (f a)) ≡
                 equivFun (pathToEquiv (cong Y (funExt⁻ (sym (snd F)) a)))
                          (snd (g a))))
Iso.fun (fill-ΣIso3 X Y f g) (h , p , q) = ((fst h) , p) , (snd h) , q
Iso.inv (fill-ΣIso3 X Y f g) ((h , p) , h2 , q) = (h , h2) , (p , q)
Iso.rightInv (fill-ΣIso3 X Y f g) = λ t → refl
Iso.leftInv (fill-ΣIso3 X Y f g) = λ t → refl


fill-ΣIso4 : (X : Type₀) (Y : X → Type₀)
             {A B : Type₀} (f : A → B) (g : A → Σ X Y)
             → Iso (Σ[ F ∈ (Σ[ h1 ∈ (B → X) ] (h1 ∘ f ≡ (λ a → fst (g a)))) ]
                 Σ[ h2 ∈ ((b : B) → Y (fst F b)) ]
                 ((a : A) → (h2 (f a)) ≡
                 equivFun (pathToEquiv (cong Y (funExt⁻ (sym (snd F)) a)))
                          (snd (g a))))
                (Σ[ F ∈ (Σ[ h1 ∈ (B → X) ] (h1 ∘ f ≡ (λ a → fst (g a)))) ]
                 Σ[ h2 ∈ ((b : B) → Y (fst F b)) ]
                 ((a : A) (r : Σ[ b ∈ B ] b ≡ f a) → (h2 (f a)) ≡
                 equivFun (pathToEquiv (cong Y (funExt⁻ (sym (snd F)) a)))
                          (snd (g a))))
fill-ΣIso4 X Y {A = A} {B = B} f g = Σ-cong-iso idIso (λ h → Σ-cong-iso idIso (λ h2 → ΠContrIso A (λ a → Σ[ b ∈ B ] b ≡ f a) (λ a → (h2 (f a)) ≡ equivFun (pathToEquiv (cong Y (funExt⁻ (sym (snd h)) a))) (snd (g a))) λ a → FTIT' B (f a)))

fill-ΣIso5 : (X : Type₀) (Y : X → Type₀)
             {A B : Type₀} (f : A → B) (g : A → Σ X Y)
             → Iso (Σ[ F ∈ (Σ[ h1 ∈ (B → X) ] (h1 ∘ f ≡ (λ a → fst (g a)))) ]
                 Σ[ h2 ∈ ((b : B) → Y (fst F b)) ]
                 ((a : A) (r : Σ[ b ∈ B ] b ≡ f a) → (h2 (f a)) ≡
                 equivFun (pathToEquiv (cong Y (funExt⁻ (sym (snd F)) a)))
                          (snd (g a))))
                (Σ[ F ∈ (Σ[ h1 ∈ (B → X) ] (h1 ∘ f ≡ (λ a → fst (g a)))) ]
                 Σ[ h2 ∈ ((b : B) → Y (fst F b)) ]
                 ((a : A) (r : Σ[ b ∈ B ] b ≡ f a) → (h2 (f a)) ≡
                 equivFun (pathToEquiv (cong Y (funExt⁻ (sym (snd F)) a)))
                          (snd (g a))))
fill-ΣIso5 X Y f g = idIso -- keep going


fill-ΣIso6 : (X : Type₀) (Y : X → Type₀)
             {A B : Type₀} (f : A → B) (g : A → Σ X Y)
             → Iso (Σ[ F ∈ (Σ[ h1 ∈ (B → X) ] (h1 ∘ f ≡ (λ a → fst (g a)))) ]
                 Σ[ h2 ∈ ((b : B) → Y (fst F b)) ]
                 ((a : A) (r : Σ[ b ∈ B ] b ≡ f a) → (h2 (f a)) ≡
                 equivFun (pathToEquiv (cong Y (funExt⁻ (sym (snd F)) a)))
                          (snd (g a))))
                (Σ[ F ∈ (Σ[ h1 ∈ (B → X) ] (h1 ∘ f ≡ (λ a → fst (g a)))) ]
                 Σ[ h2 ∈ ((b : B) → Y (fst F b)) ]
                 ((b : B) (r : fiber f b) → (h2 (f (fst r))) ≡
                 equivFun (pathToEquiv (cong Y (funExt⁻ (sym (snd F)) (fst r))))
                          (snd (g (fst r)))))
Iso.fun (fill-ΣIso6 X Y f g) (F , h2 , q) = F , (h2 , (λ b r → q (fst r) (b , sym (snd r))))
Iso.inv (fill-ΣIso6 X Y f g) (F , h2 , q)  = F , (h2 , (λ a r → q (fst r) (a , sym (snd r))))
Iso.rightInv (fill-ΣIso6 X Y f g) = λ t → refl
Iso.leftInv (fill-ΣIso6 X Y f g) = λ t → refl

fill-ΣIso7' : (X : Type₀) (Y : X → Type₀) {A B : Type₀} (f : A → B) (g : A → Σ X Y) (F : Σ[ h1 ∈ (B → X) ] (h1 ∘ f ≡ (λ a → fst (g a)))) (h2 : ((b : B) → Y (fst F b))) (b : B) (r : fiber f b) →
  Iso ((h2 (f (fst r))) ≡ equivFun (pathToEquiv (cong Y (funExt⁻ (sym (snd F)) (fst r)))) (snd (g (fst r))))
      ((h2 b) ≡ equivFun (pathToEquiv (cong Y (funExt⁻ (sym (snd F)) (fst r)) ∙ cong (Y ∘ (fst F)) (snd r))) (snd (g (fst r))))
fill-ΣIso7' X Y f g F h2 b r = J (λ b' q → Iso ((h2 (f (fst r))) ≡ equivFun (pathToEquiv (cong Y (funExt⁻ (sym (snd F)) (fst r)))) (snd (g (fst r)))) ((h2 b') ≡ equivFun (pathToEquiv (cong Y (funExt⁻ (sym (snd F)) (fst r)) ∙ cong (Y ∘ (fst F)) q)) (snd (g (fst r))))) (pathToIso (cong (h2 (f (fst r)) ≡_) (sym (transportRefl _ ∙ cong (transport (λ i → Y (snd F (~ i) (fst r)))) (transportRefl _))))) ((snd r))

fill-ΣIso7 : (X : Type₀) (Y : X → Type₀)
             {A B : Type₀} (f : A → B) (g : A → Σ X Y)
             → Iso (Σ[ F ∈ (Σ[ h1 ∈ (B → X) ] (h1 ∘ f ≡ (λ a → fst (g a)))) ]
                 Σ[ h2 ∈ ((b : B) → Y (fst F b)) ]
                 ((b : B) (r : fiber f b) → (h2 (f (fst r))) ≡
                 equivFun (pathToEquiv (cong Y (funExt⁻ (sym (snd F)) (fst r))))
                          (snd (g (fst r)))))
                (Σ[ F ∈ (Σ[ h1 ∈ (B → X) ] (h1 ∘ f ≡ (λ a → fst (g a)))) ]
                 Σ[ h2 ∈ ((b : B) → Y (fst F b)) ]
                 ((b : B) (r : fiber f b) → (h2 b) ≡
                 equivFun (pathToEquiv (cong Y (funExt⁻ (sym (snd F)) (fst r))
                           ∙ cong (Y ∘ (fst F)) (snd r)))
                          (snd (g (fst r)))))
fill-ΣIso7 X Y {B = B} f g = Σ-cong-iso idIso (λ F → Σ-cong-iso idIso (λ h2 → Π-iso B (λ b → (r : fiber f b) → (h2 (f (fst r))) ≡ equivFun (pathToEquiv (cong Y (funExt⁻ (sym (snd F)) (fst r)))) (snd (g (fst r)))) (λ b → (r : fiber f b) → (h2 b) ≡ equivFun (pathToEquiv (cong Y (funExt⁻ (sym (snd F)) (fst r)) ∙ cong (Y ∘ (fst F)) (snd r))) (snd (g (fst r)))) λ b → Π-iso (fiber f b) (λ r → (h2 (f (fst r))) ≡ equivFun (pathToEquiv (cong Y (funExt⁻ (sym (snd F)) (fst r)))) (snd (g (fst r)))) (λ r → (h2 b) ≡ equivFun (pathToEquiv (cong Y (funExt⁻ (sym (snd F)) (fst r)) ∙ cong (Y ∘ (fst F)) (snd r))) (snd (g (fst r)))) (λ r → fill-ΣIso7' X Y f g F h2 b r)))

fill-ΣIso8 : (X : Type₀) (Y : X → Type₀) {A B : Type₀}
             (f : A → B) (g : A → Σ X Y)
             → Iso (Σ[ F ∈ (Σ[ h1 ∈ (B → X) ] (h1 ∘ f ≡ (λ a → fst (g a)))) ]
                 Σ[ h2 ∈ ((b : B) → Y (fst F b)) ]
                 ((b : B) (r : fiber f b) → (h2 b) ≡
                 equivFun (pathToEquiv (cong Y (funExt⁻ (sym (snd F)) (fst r))
                           ∙ cong (Y ∘ (fst F)) (snd r)))
                          (snd (g (fst r)))))
                 (Σ (fillers X f (fst ∘ g))
                    (λ h → (b : B) → fill-DepTy X Y f g h b))
Iso.fun (fill-ΣIso8 X Y f g) ((h , p) , h2 , q) = (h , p) , (λ b → (λ _ → h2 b) , funExt (q b))
Iso.inv (fill-ΣIso8 X Y f g) ((h , p) , F) = (h , p) , ((λ b → fst (F b) tt) , (λ b → funExt⁻ (snd (F b))))
Iso.rightInv (fill-ΣIso8 X Y f g) = λ t → refl
Iso.leftInv (fill-ΣIso8 X Y f g) = λ t → refl
                
fill-ΣIso : (X : Type₀) (Y : X → Type₀)
            {A B : Type₀} (f : A → B) (g : A → Σ X Y)
            → Iso (fillers (Σ X Y) f g)
               (Σ (fillers X f (fst ∘ g))
                  (λ h → (b : B) → fill-DepTy X Y f g h b))
fill-ΣIso X Y f g = compIso (fill-ΣIso1 X Y f g) (compIso (fill-ΣIso2 X Y f g) (compIso (fill-ΣIso3 X Y f g) (compIso (fill-ΣIso4 X Y f g) (compIso (fill-ΣIso6 X Y f g) (compIso (fill-ΣIso7 X Y f g) (fill-ΣIso8 X Y f g))))))

fill-ΣEquiv : (X : Type₀) (Y : X → Type₀)
            {A B : Type₀} (f : A → B) (g : A → Σ X Y)
            → (fillers (Σ X Y) f g) ≃
               (Σ (fillers X f (fst ∘ g))
                  (λ h → (b : B) → fill-DepTy X Y f g h b))
fill-ΣEquiv X Y f g = isoToEquiv (fill-ΣIso X Y f g)

fill-ΣIdentity : (X : Type₀) (Y : X → Type₀)
            {A B : Type₀} (f : A → B) (g : A → Σ X Y)
            → (fillers (Σ X Y) f g) ≡
               (Σ (fillers X f (fst ∘ g))
                  (λ h → (b : B) → fill-DepTy X Y f g h b))
fill-ΣIdentity X Y f g = ua (fill-ΣEquiv X Y f g)

fiber-wise : (P : {A B : Type₀} → (A → B) → Type₀)
             → ({A B : Type₀} → (f : A → B) → isProp (P f))
             → Type (ℓ-suc ℓ-zero)
fiber-wise P isProp-P =
  {A B : Type₀} (f : A → B) → (P f)
    → ((b : B) → P (λ (_ : fiber f b) → tt))

-- Contractible space of solutions to lifting problems
module _ (P : {A B : Type ℓ-zero} → (A → B) → Type ℓ-zero)
         (isProp-P : {A B : Type ℓ-zero} (f : A → B) → isProp (P f))
         where

  R-orthog : (X : Type ℓ-zero) → Type₁
  R-orthog X = {A B : Type ℓ-zero} (f : A → B) (g : A → X)
               → (P f)
               → isContr (fillers X f g)

  module _ (FibW : fiber-wise P isProp-P) where
  
    R-orthog-Σ : (X : Type ℓ-zero) (Y : X → Type ℓ-zero)
               → R-orthog X → ((x : X) → R-orthog (Y x))
               → R-orthog (Σ[ x ∈ X ] (Y x))
    R-orthog-Σ X Y hX hY f g Pf =
      transport (λ i → isContr (fill-ΣIdentity X Y f g (~ i)))
                (isContrΣ (hX f (λ a → fst (g a)) Pf)
                λ F → isContrΠ (λ b → hY (fst F b) (λ _ → tt) _
                                (FibW f Pf b)))

module _ (P : {A B : Type ℓ-zero} → (A → B) → Type ℓ-zero)
         (isProp-P : {A B : Type ℓ-zero} (f : A → B) → isProp (P f))
         (FibW : fiber-wise P isProp-P)
         {A B : Type ℓ-zero} (f : A → B) (Pf : P f)
         (X : B → Type ℓ-zero) (hB : R-orthog P isProp-P B)
         (hX : (b : B) → R-orthog P isProp-P (X b))
         where

  ξ : (h : (a : A) → X (f a))
      → isContr (fillers (Σ B X) f λ a → (f a , h a))
  ξ h = R-orthog-Σ P isProp-P FibW B X hB hX f (λ a → (f a , h a)) Pf

  useful : (h : (a : A) → X (f a))
         → isContr (Σ (fillers B f f)
                  (λ F → (b : B) → fill-DepTy B X f (λ a → (f a , h a)) F b))
  useful h =
    transport (λ i → isContr (fill-ΣIdentity B X f (λ a → (f a , h a)) i))
              (ξ h)



  χ : fillers B f f
  χ = (λ x → x) , refl

  usefulIso' : (h : (a : A) → X (f a))
    → Iso (Σ[ g ∈ ((b : B) → X b) ] (g ∘ f ≡ h))
       (Σ[ g ∈ ((b : B) → X b) ] ((a : A) → g (f a) ≡ (h a)))
  Iso.fun (usefulIso' h) (g , p) =
    g , (funExt⁻ p)
  Iso.inv (usefulIso' h) (g , p) =
    g , (funExt p)
  Iso.rightInv (usefulIso' h) = λ _ → refl
  Iso.leftInv (usefulIso' h) = λ _ → refl

  usefulIso'' : (h : (a : A) → X (f a))
    → Iso (Σ[ g ∈ ((b : B) → X b) ] ((a : A) → g (f a) ≡ (h a)))
       (Σ[ g ∈ ((b : B) → X b) ]
         ((a : A) (bp : Σ[ b ∈ B ] f a ≡ b) → g (f a) ≡ (h a)))
  usefulIso'' h =
    Σ-cong-iso
    idIso
    (λ g → ΠContrIso A (λ a → (Σ[ b ∈ B ] f a ≡ b)) (λ a → g (f a) ≡ h a)
                        λ a → FTIT B (f a))

  usefulIso3 : (h : (a : A) → X (f a))
    → Iso (Σ[ g ∈ ((b : B) → X b) ]
           ((a : A) (bp : Σ[ b ∈ B ] f a ≡ b) → g (f a) ≡ (h a)))
           (Σ[ g ∈ ((b : B) → X b) ]
           ((a : A) (bp : Σ[ b ∈ B ] f a ≡ b)
             → g (f a)
              ≡ equivFun
                (pathToEquiv (cong X (funExt⁻ (refl {x = f}) a))) (h a)))
  usefulIso3 h = pathToIso
    (cong (λ (xx : (a : A) → X (f a))
    → (Σ[ g ∈ ((b : B) → X b) ]
       ((a : A) (bp : Σ[ b ∈ B ] f a ≡ b)
        → g (f a)
         ≡ (xx a)))) (sym (funExt λ a → transportRefl (h a))))

  usefulIso4 : (h : (a : A) → X (f a))
    → Iso (Σ[ g ∈ ((b : B) → X b) ]
           ((a : A) (bp : Σ[ b ∈ B ] f a ≡ b)
             → g (f a)
              ≡ equivFun
                (pathToEquiv (cong X (funExt⁻ (refl {x = f}) a))) (h a)))
           (Σ[ g ∈ ((b : B) → X b) ]
           ((b : B) (a : fiber f b)
             → g (f (fst a))
              ≡ equivFun
                (pathToEquiv (cong X (funExt⁻ (refl {x = f}) (fst a))))
                (h (fst a))))
  Iso.fun (usefulIso4 h) (g , p) =
    g , (λ b a → p (fst a) (b , snd a))
  Iso.inv (usefulIso4 h) (g , p) =
    g , (λ a pb → p (fst pb) (a , snd pb))
  Iso.rightInv (usefulIso4 h) (g , p) = refl
  Iso.leftInv (usefulIso4 h) (g , p) = refl

  usefulIso5 : (h : (a : A) → X (f a))
    → Iso (Σ[ g ∈ ((b : B) → X b) ]
           ((b : B) (a : fiber f b)
             → g (f (fst a))
              ≡ equivFun
                (pathToEquiv (cong X (funExt⁻ (refl {x = f}) (fst a))))
                (h (fst a))))
           (Σ[ g ∈ ((b : B) → X b) ]
           ((b : B) (a : fiber f b)
             → g b
              ≡ equivFun
                (pathToEquiv (cong X (funExt⁻ (refl {x = f}) (fst a))
                              ∙ cong X (snd a)))
                (h (fst a))))
  Iso.fun (usefulIso5 h) (g , p) =
    g , (λ b a → Iso.fun (hhef A B (X (f (fst a))) (fst a) f b (snd a)
                                X refl g (h (fst a))) (p b a))
  Iso.inv (usefulIso5 h) (g , p) =
    g , (λ b a → Iso.inv (hhef A B (X (f (fst a))) (fst a) f b (snd a)
                                X refl g (h (fst a))) (p b a))
  Iso.rightInv (usefulIso5 h) (g , p) =
    ΣPathP (refl ,
     (funExt (λ b →
      funExt (λ a → Iso.rightInv (hhef A B (X (f (fst a))) (fst a)
                                       f b (snd a) X refl g (h (fst a)))
                                  (p b a)))))
  Iso.leftInv (usefulIso5 h) (g , p) =
    ΣPathP (refl ,
     funExt (λ b →
     funExt (λ a → Iso.leftInv (hhef A B (X (f (fst a))) (fst a)
                                      f b (snd a) X refl g (h (fst a)))
                                (p b a))))

  usefulIso6 : (h : (a : A) → X (f a))
    → Iso (Σ[ g ∈ ((b : B) → X b) ]
           ((b : B) (a : fiber f b)
             → g b
              ≡ equivFun
                (pathToEquiv (cong X (funExt⁻ (refl {x = f}) (fst a))
                              ∙ cong X (snd a)))
                (h (fst a))))
           ((b : B) → fill-DepTy B X f (λ a → (f a , h a)) χ b)
  Iso.fun (usefulIso6 h) (g , p) =
    λ b → (λ _ → g b) , (funExt (p b))
  Iso.inv (usefulIso6 h) F =
    (λ b → fst (F b) tt) , λ b → funExt⁻ (snd (F b))
  Iso.rightInv (usefulIso6 h) F =
    refl
  Iso.leftInv (usefulIso6 h) (g , p) = refl
  
  usefulIso : (h : (a : A) → X (f a))
    → Iso (Σ[ g ∈ ((b : B) → X b) ] (g ∘ f ≡ h))
       ((b : B) → fill-DepTy B X f (λ a → (f a , h a)) χ b)
  usefulIso h = compIso (usefulIso' h)
               (compIso (usefulIso'' h)
               (compIso (usefulIso3 h)
               (compIso (usefulIso4 h)
               (compIso (usefulIso5 h)
               (compIso (usefulIso6 h) idIso)))))

  usefulEquiv :  (h : (a : A) → X (f a))
    → (Σ[ g ∈ ((b : B) → X b) ] (g ∘ f ≡ h)) ≃
       ((b : B) → fill-DepTy B X f (λ a → (f a , h a)) χ b)
  usefulEquiv h = isoToEquiv (usefulIso h)

  usefulIdentity : (h : (a : A) → X (f a))
    → (Σ[ g ∈ ((b : B) → X b) ] (g ∘ f ≡ h)) ≡
       ((b : B) → fill-DepTy B X f (λ a → (f a , h a)) χ b)
  usefulIdentity h = ua (usefulEquiv h)

  γ : (h : (a : A) → X (f a))
      → isContr (Σ[ g ∈ ((b : B) → X b) ] (g ∘ f ≡ h))
  γ h = transport (λ i → isContr (usefulIdentity h (~ i)))
        (transport (λ i → isContr (ΣContr (fillers B f f) χ
                                   (λ F → (b : B)
                                        → fill-DepTy B X f
                                           (λ a → (f a , h a)) F b)
                                   (hB f f Pf) i))
        (useful h))

∞Connected : {A B : Type ℓ-zero} → (A → B) → Type ℓ-zero
∞Connected f = (n : ℕ) → isConnectedFun n f

isProp-∞Conn : {A B : Type ℓ-zero} (f : A → B) → isProp (∞Connected f)
isProp-∞Conn f = isPropΠ (λ n → isPropΠ (λ b → isPropIsContr))

fiber-wise-∞Conn : fiber-wise (∞Connected) (isProp-∞Conn)
fiber-wise-∞Conn f hf b n =
  isConnected→isConnectedFun n (hf n b)

∞Truncated : (A : Type ℓ-zero) → Type (ℓ-suc ℓ-zero)
∞Truncated A = R-orthog (∞Connected) (isProp-∞Conn) A

Trunc' : (n : ℕ) (A : Type ℓ-zero) → Type (ℓ-suc ℓ-zero)
Trunc' n A = R-orthog (λ f → isConnectedFun n f)
                      (λ f → isPropΠ (λ b → isPropIsContr)) A

Trunc'⇒Trunc : (n : ℕ) (A : Type ℓ-zero) → isOfHLevel n A → (Trunc' n A)
Trunc'⇒Trunc zero A hA f g hf = fill-Contr A hA f g
Trunc'⇒Trunc (suc n) A hA f g hf =
  transport (λ i → isContr (fill-TruncIdentity (suc n) (A , hA) f g (~ i)))
            (fill-Equiv A (map f) (rec hA g)
            (equivIsEquiv (connectedTruncEquiv (suc n) f hf)))

Trunc⇒Trunc' : (n : ℕ) (A : Type ℓ-zero) → (Trunc' n A) → isOfHLevel n A
Trunc⇒Trunc' zero A hA =
  fst (fst (hA (λ _ → tt) (λ x → x) λ b → tt* , (λ _ → refl)))
           tt
  , funExt⁻ (snd (fst (hA (λ _ → tt) (λ x → x) λ b → tt* , (λ _ → refl))))
Trunc⇒Trunc' (suc n) A hA =
  isSphereFilled→isOfHLevel n
  (λ f → fst (fst (hA (λ _ → tt) f
          (isConnected→isConnectedFun (suc n) (sphereConnected n)))) tt
  , funExt⁻ (snd (fst (hA (λ _ → tt) f
            (isConnected→isConnectedFun (suc n) (sphereConnected n))))))

Trunc'⇒∞Trunc : (n : ℕ) (A : Type ℓ-zero) → (Trunc' n A) → ∞Truncated A
Trunc'⇒∞Trunc n A hA f g hf = hA f g (hf n)

◯-Post-is∞Trunc : (A : Type ℓ-zero) → ∞Truncated (◯-Postnikov A)
◯-Post-is∞Trunc A {A = A'} {B = B} f g hf =
  transport (λ i → isContr (fill-limIdentity
                            (fst (PostnikovTowerOf A)) f g (~ i)))
            (contrDiag (fill-Diag (fst (PostnikovTowerOf A))  f g)
               λ n → Trunc'⇒Trunc n (fst (fst (PostnikovTowerOf A)) n)
                      (isOfHLevelTrunc n)
                      f (λ x → proj (fst (PostnikovTowerOf A)) n (g x))
                      (hf n))

module _ (Ax : (A : ℕ-Diagram) (PA : isPostnikovTower A) (n : ℕ)
              → isEquiv (TowerFamilyMap A PA n))
  where

  ∥η∥⁻¹ : (A : ℕ-Diagram) (PA : isPostnikovTower A) (n : ℕ)
         → fst A n → ∥ fst (ℓim A) ∥ n
  ∥η∥⁻¹ A PA n = invEq ((TowerFamilyMap A PA n) , (Ax A PA n))

  η-sqr : (X : Type₀) (n : ℕ) (x : X)
       → ((TowerFamilyMap (fst (PostnikovTowerOf X))
                           (snd (PostnikovTowerOf X)) n)
        ∘ (tMap (◯-Postnikov X) n)
        ∘ (η-Postnikov X)) x
        ≡ (tMap X n) x
  η-sqr X n x =
    funExt⁻ (ObvsIdentity (fst (PostnikovTowerOf X))
            (snd (PostnikovTowerOf X)) n ⁻¹) (η-Postnikov X x)     
 
  η-∞Conn : {A : Type ℓ-zero} → ∞Connected (η-Postnikov A)
  η-∞Conn {A = A} n =
    isConnectedFunCancel' (η-Postnikov A)
    (TowerFamilyMap (fst (PostnikovTowerOf A)) (snd (PostnikovTowerOf A))
                    (suc n)
    ∘ (tMap (◯-Postnikov A) (suc n))) n
    (isConnectedComp
     (TowerFamilyMap (fst (PostnikovTowerOf A))
                     (snd (PostnikovTowerOf A)) (suc n))
     (tMap (◯-Postnikov A) (suc n))
     (suc n) (isEquiv→isConnected _
              (Ax (fst (PostnikovTowerOf A))
                   (snd (PostnikovTowerOf A)) (suc n)) (suc n))
             (TruncConnected (suc n)))
    (transport (λ i → isConnectedFun n (funExt (η-sqr A (suc n)) (~ i)))
               (isConnectedFunSubtr n 1 (tMap A (suc n))
                (TruncConnected (suc n))))

  module UniqueElim (X : Type ℓ-zero) (P : ◯-Postnikov X → Type ℓ-zero)
    where

    ∥P∥n : (n : ℕ) → (◯-Postnikov X) → Type₀
    ∥P∥n n x = ∥ P x ∥ n

    Π∥P∥n : ℕ-Diagram
    fst Π∥P∥n n = (x : ◯-Postnikov X) → (∥P∥n n x)
    snd Π∥P∥n n f x =
      rec (isOfHLevelSuc n (isOfHLevelTrunc n)) (tMap (P x) n) (f x)

    ∥P∘η∥n : (n : ℕ) → X → Type₀
    ∥P∘η∥n n x = ∥ P (η-Postnikov X x) ∥ n

    Π∥P∘η∥n : ℕ-Diagram
    fst Π∥P∘η∥n n = (x : X) → ∥P∘η∥n n x
    snd Π∥P∘η∥n n f x =
      rec (isOfHLevelSuc n (isOfHLevelTrunc n))
          (tMap (P (η-Postnikov X x)) n) (f x)


    PsQs : MapOfDiagrams Π∥P∥n Π∥P∘η∥n
    fst PsQs n f = f ∘ (η-Postnikov X)
    snd PsQs n f = refl

    PsQs-Equiv : (n : ℕ) → (g : fst Π∥P∘η∥n n) → isContr (fiber (fst PsQs n) g)
    PsQs-Equiv n g =
      γ ∞Connected isProp-∞Conn fiber-wise-∞Conn
        (η-Postnikov X) η-∞Conn (∥P∥n n) (◯-Post-is∞Trunc X)
        (λ b → Trunc'⇒∞Trunc n (∥P∥n n b) (Trunc'⇒Trunc n (∥P∥n n b )
                              (isOfHLevelTrunc n))) g

    PsQs-ED : EquivOfDiagrams Π∥P∥n Π∥P∘η∥n
    fst PsQs-ED = PsQs
    snd PsQs-ED n = record { equiv-proof = PsQs-Equiv n }

    iso1 : Iso ((x : ◯-Postnikov X) → ◯-Postnikov (P x))
               (fst (ℓim Π∥P∥n))
    iso1 = Π-ℓim-Iso (◯-Postnikov X) (λ x → fst (PostnikovTowerOf (P x)))

    iso2 : Iso ((x : X) → ◯-Postnikov (P (η-Postnikov X x)))
               (fst (ℓim Π∥P∘η∥n))
    iso2 = Π-ℓim-Iso X (λ x → fst (PostnikovTowerOf (P (η-Postnikov X x))))

    path-map : (f : (x : ◯-Postnikov X) → ◯-Postnikov (P x)) →
             (Iso.inv (iso2)
             ∘ (MapOfDiagrams→MapOfLimits' _ (Π∥P∘η∥n) PsQs (ℓim Π∥P∥n)
                                              (ℓim Π∥P∘η∥n))
             ∘ Iso.fun (iso1)) f
             ≡ (eliminationMap (◯-Postnikov) (η-Postnikov) X P) f
    path-map f =
      Iso.inv (iso2)
       (MapOfDiagrams→MapOfLimits' _ (Π∥P∘η∥n) PsQs (ℓim Π∥P∥n) (ℓim Π∥P∘η∥n)
       (Iso.fun (iso1) f)) ≡⟨ refl ⟩
      Iso.inv (iso2)
      (MapOfDiagrams→MapOfLimits' _ (Π∥P∘η∥n) PsQs (ℓim Π∥P∥n) (ℓim Π∥P∘η∥n)
      ((λ n _ x → fst (f x) n _) ,
        λ n _ → funExt λ x → snd (f x) n _)) ≡⟨ refl ⟩
      Iso.inv (iso2)
      ((λ n _ → (fst PsQs) n λ x → fst (f x) n _)
      , λ n _ → (snd PsQs) n (λ x → fst (f x) (suc n) _)
                 ∙ cong ((fst PsQs) n) (funExt λ x → snd (f x) n _))
     ≡⟨ refl ⟩
      (λ x → ((λ n _ → (fst PsQs) n (λ x' → fst (f x') n _) x) ,
       λ n _ → funExt⁻ ((snd PsQs) n (λ x' → fst (f x') (suc n) _)
                 ∙ cong ((fst PsQs) n) (funExt λ x' → snd (f x') n _)) x))
     ≡⟨ funExt
        (λ x → ΣPathP
                (refl
              , funExt
                λ n →
                funExt
                λ _ →
                cong (λ (p : (fst PsQs) n
                             (λ x' → (snd (fst (PostnikovTowerOf (P x')))) n
                                           (fst (f x') (suc n) _))
                           ≡ (fst PsQs) n (λ x' → fst (f x') n _))
                        → funExt⁻ p x)
                     (lUnit (cong ((fst PsQs) n)
                                  (funExt λ x' → snd (f x') n _)) ⁻¹))) ⟩
      (λ x → ((λ n _ → (fst PsQs) n (λ x' → fst (f x') n _) x) ,
       λ n _ → funExt⁻ (cong ((fst PsQs) n)
                              (funExt λ x' → snd (f x') n _)) x))
     ≡⟨ refl ⟩
     f ∘ (η-Postnikov X) ∎


  uniqueElimPostnikov : isUniquelyEliminating ◯-Postnikov η-Postnikov
  uniqueElimPostnikov X P = ρ
    where
     open UniqueElim X P

     --η-Equiv ? ? PsQs-ED

     
     ρ : isEquiv (eliminationMap ◯-Postnikov η-Postnikov X P)
     ρ = transport (λ i → isEquiv (funExt path-map i))
                   (equivIsEquiv
                   (compEquiv
                   (isoToEquiv iso1)
                   (compEquiv ((MapOfDiagrams→MapOfLimits' Π∥P∥n Π∥P∘η∥n PsQs
                                                            (ℓim Π∥P∥n)
                                                            (ℓim Π∥P∘η∥n))
                              , η-Equiv Π∥P∥n Π∥P∘η∥n PsQs-ED)
                   (invEquiv (isoToEquiv iso2)))))


-- THE KEY THEOREM: Countable choice implies that the ``Postnikov modality''
--                  is uniquely eliminating.

module _ (n : ℕ) (Ax : CC n) where

  UniqueElim : isUniquelyEliminating ◯-Postnikov η-Postnikov
  UniqueElim = uniqueElimPostnikov λ A PA n' → snd (CC→PosEff n Ax A PA) n'
