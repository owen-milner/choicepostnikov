
module PostnikovTowers where

open import Cubical.Data.Nat renaming (elim to ℕElim)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Unit 
open import Cubical.Data.Sigma
open import Cubical.Foundations.Everything
open import Cubical.HITs.Truncation
open import Cubical.Homotopy.Connected
open import Cubical.Functions.FunExtEquiv

open import Limits
open import DiagramSigma
open import UnitCones
open import shiftDiagram

{-
   File contains definition of Postnikov towers

   Also many helpful lemmas about limits, products and diagrams
-}


{- property of being a postnikov tower -}
isPostnikovTower : ℕ-Diagram → Type ℓ-zero
isPostnikovTower (A , a) = ((n : ℕ) → isOfHLevel n (A n))
                         × ((n : ℕ) → isConnectedFun n (a n))

{- Collection of helper lemmas -}
addOneAssoc : (k n : ℕ) → (k + (1 + n)) ≡ (1 + (k + n))
addOneAssoc k n = +-assoc k 1 n ∙ cong (_+ n) (+-comm k 1)

add2Assoc : (k n : ℕ) → (1 + (k + (1 + n))) ≡ (k + (2 + n))
add2Assoc k n = cong (suc) (+-comm k (1 + n)) ∙ +-comm (2 + n) k

PathIdTruncFunc' : {X : Type ℓ-zero} {x : X} (n : ℕ)
  → Iso.fun (PathIdTruncIso n) (refl {x = ∣ x ∣ₕ})
   ≡ ∣ refl {x = x} ∣ₕ
PathIdTruncFunc' zero = refl
PathIdTruncFunc' (suc n) = cong ∣_∣ (transportRefl refl)

342-case1 : {X Y Z : Type ℓ-zero} (e : X ≃ Z) (f : X ≃ Y) (g : Y → Z)
  → g ∘ (fst f) ≡ (fst e) → isEquiv g
342-case1 {Y = Y} {Z = Z} =
  EquivJ (λ X' e' → (f : X' ≃ Y) (g : Y → Z)
                  → g ∘ (fst f) ≡ (fst e') → isEquiv g)
         λ f g H → precomposesToId→Equiv g (fst f) H (snd f)

342-case2 : {X Y Z : Type ℓ-zero} (e : X ≃ Z) (f : Y ≃ Z) (g : X → Y)
  → (fst f) ∘ g ≡ (fst e) → isEquiv g
342-case2 {Y = Y} {Z = Z} =
  EquivJ (λ X' e' → (f : Y ≃ Z) (g : X' → Y)
                  → (fst f) ∘ g ≡ (fst e') → isEquiv g)
         λ f g H → isEquiv→sectionIsEquiv (snd f) (funExt⁻ H)

isIso→Iso : {A B : Type ℓ-zero} (f : A → B) → isIso f → Iso A B
Iso.fun (isIso→Iso f (g , p , q)) = f
Iso.inv (isIso→Iso f (g , p , q)) = g
Iso.rightInv (isIso→Iso f (g , p , q)) = p
Iso.leftInv (isIso→Iso f (g , p , q)) = q

Iso→isIso : {A B : Type ℓ-zero} (e : Iso A B) → isIso (Iso.fun e)
fst (Iso→isIso e) = Iso.inv e
fst (snd (Iso→isIso e)) = Iso.rightInv e
snd (snd (Iso→isIso e)) = Iso.leftInv e

{- from here helper lemmas are mostly about truncatedness and connectedness -}

mapEq : (A B : Type ℓ-zero) (n : ℕ)
          (hA : isOfHLevel n A)
          (hB : isOfHLevel n B)
          (f : A → B)
          → f
          ≡ Iso.fun (truncIdempotentIso n hB)
            ∘ map f ∘ Iso.inv (truncIdempotentIso n hA)
mapEq A B zero hA hB f = funExt (λ x → snd hB (f x) ⁻¹ ∙ snd hB _)
mapEq A B (suc n) hA hB f = refl

Trunc→Connected→Equiv : (A B : Type ℓ-zero) (n : ℕ)
                       → isOfHLevel n A
                       → isOfHLevel n B
                       → (f : A → B)
                       → isConnectedFun n f
                       → isEquiv f
Trunc→Connected→Equiv A B zero hA hB f _ =
   isoToIsEquiv (isContr→Iso' hA hB f)
Trunc→Connected→Equiv A B (suc n) hA hB f hf =
   isoToIsEquiv
   (isIso→Iso f
     (transport (λ i → isIso (mapEq A B (suc n) hA hB f (~ i)))
                (Iso→isIso (compIso (invIso (truncIdempotentIso (suc n) hA))
                                     (compIso (connectedTruncIso (suc n) f hf)
                                     (truncIdempotentIso (suc n) hB))))))

                         
tMap : (X : Type ℓ-zero) (n : ℕ) → X → ∥ X ∥ n
tMap X n = ∣_∣ₕ

TruncUniversal : {X : Type ℓ-zero} (n : ℕ) → (Y : Type ℓ-zero)
              → isOfHLevel n Y
              → isEquiv {A = ∥ X ∥ n → Y} {B = X → Y} (λ f → f ∘ ∣_∣ₕ)
TruncUniversal zero Y hY = isoToIsEquiv
  (isContr→Iso' (isContrΠ (λ _ → hY)) (isContrΠ (λ _ → hY))
                 (λ z z₁ → z ∣ z₁ ∣ₕ))
TruncUniversal (suc n) Y hY = isoToIsEquiv (univTrunc (suc n) {B = (Y , hY)})

TruncUniversalInvEq : {X : Type ℓ-zero} (n : ℕ) → (Y : Type ℓ-zero)
  (hY : isOfHLevel n Y)
  → equivFun (invEquiv (_ , TruncUniversal {X = X} n Y hY))
   ≡ rec hY
TruncUniversalInvEq zero Y hY = refl
TruncUniversalInvEq (suc n) Y hY = refl

TruncConnected : {X : Type ℓ-zero} (n : ℕ) → isConnectedFun n (tMap X n)
TruncConnected zero (lift tt) = isContrUnit*
TruncConnected (suc n) =
  elim (λ x → isOfHLevelIsConnectedStable (suc n))
       λ x → ∣ x , refl ∣ₕ ,
       elim (λ x' → isOfHLevelPath (suc n)
                      (isOfHLevelTrunc (suc n))
                      ∣ x , refl ∣ₕ
                      x')
            λ x' →
              transport
              (λ i → tMap _ (suc n) (x , refl {x = tMap _ (suc n) x })
                    ≡ tMap _ (suc n)
                        (fst x' , Iso.leftInv (PathIdTruncIso n) (snd x') i))
              (Iso.inv (PathIdTruncIso n)
              (elim
                {B = λ p → ∥ (x , refl)
                           ≡ (fst x' , Iso.inv (PathIdTruncIso n) p) ∥ n}
                (λ _ → isOfHLevelTrunc n)
                (λ p → J (λ y q →
                           ∥ (x , refl {x = tMap _ (suc n) x})
                          ≡ (y , Iso.inv (PathIdTruncIso n) (∣ q ⁻¹ ∣ₕ)) ∥ n)
                          ∣ ΣPathP
                           (refl
                          , transport
                            (λ i → Iso.inv (PathIdTruncIso n)
                                    (PathIdTruncFunc' n i)
                                    ≡ refl {x = ∣ x ∣})
                            (Iso.leftInv (PathIdTruncIso n) refl) ⁻¹) ∣ₕ (p ⁻¹))
                (Iso.fun (PathIdTruncIso n) (snd x'))))


TruncNatural : {X : Type ℓ-zero} (n : ℕ) → (Y Z : Type ℓ-zero)
            → (hY : isOfHLevel n Y)
            → (hZ : isOfHLevel n Z)
            → (f : X → Y)
            → (g : Y → Z)
            → fst (invEquiv (_ , (TruncUniversal n Z hZ))) (g ∘ f)
             ≡ g ∘ (fst (invEquiv (_ , (TruncUniversal n Y hY))) f)
TruncNatural n Y Z hY hZ f g =
  transport (λ i → (TruncUniversalInvEq n Z hZ (~ i)) (g ∘ f)
                   ≡ g ∘ (TruncUniversalInvEq n Y hY (~ i) f))
             (funExt (∘rec hY hZ f g))

TruncMap : {X : Type ℓ-zero} (n : ℕ) → ∥ X ∥ (1 + n) → ∥ X ∥ n
TruncMap n = rec (isOfHLevelSuc n (isOfHLevelTrunc n)) ∣_∣ₕ


TruncMapObvsIdentity : {X : Type ℓ-zero} (n : ℕ)
    → TruncMap n ∘ (tMap X (1 + n)) ≡ tMap X n
TruncMapObvsIdentity n = refl

TruncMapUniversal : {X : Type ℓ-zero} (n : ℕ) → (Y : Type ℓ-zero)
                 → isOfHLevel n Y
                 → isEquiv {A = ∥ X ∥ n → Y} {B = ∥ X ∥ (1 + n) → Y}
                            (λ f → f ∘ (TruncMap n))
TruncMapUniversal {X = X} n Y hY =
  342-case2 (_ , TruncUniversal n Y hY)
            (_ , TruncUniversal (1 + n) Y (isOfHLevelSuc n hY))
            (λ f → f ∘ TruncMap n)
            (funExt (λ f → cong (f ∘_) (TruncMapObvsIdentity n)))

Connected342 : (X Y Z : Type ℓ-zero) (n : ℕ) (f : X → Y) (g : Y → Z)
            → isConnectedFun n f → isConnectedFun n (g ∘ f)
            → isConnectedFun n g
Connected342 X Y Z zero f g cf cgf b = tt* , (λ _ → refl)
Connected342 X Y Z (suc n) f g cf cgf =
  isConnectedFunCancel f g n (isConnectedFunSubtr n 1 f cf) cgf


TruncMapConnected : {X : Type ℓ-zero} (n : ℕ)
                → isConnectedFun n (TruncMap {X = X} n)
TruncMapConnected {X = X} n =
  Connected342 X (∥ X ∥ (1 + n)) (∥ X ∥ n) n (tMap X (1 + n)) (TruncMap n)
    (isConnectedFunSubtr n 1 (tMap X (1 + n)) (TruncConnected (1 + n)))
    (transport (λ i → isConnectedFun n {A = X} {B = ∥ X ∥ n}
               (TruncMapObvsIdentity n (~ i)))
               (TruncConnected n))


ConnectedEquiv : (X Y : Type ℓ-zero) (f : X → Y) → isEquiv f
    → (n : ℕ) → isConnectedFun n f
ConnectedEquiv X Y f = isEquiv→isConnected f

Connected→ConnectedComp : (X Y Z : Type ℓ-zero) (f : X → Y) (g : Y → Z)
                          (n : ℕ) → isConnectedFun n f → isConnectedFun n g
                          → isConnectedFun n (g ∘ f)
Connected→ConnectedComp X Y Z f g n hf hg =
  isConnectedComp g f n hg hf
{- end of the collection of helper lemmas -}

{- postnikov tower of a fixed space -}
PostnikovTowerOf : Type ℓ-zero → Σ[ P ∈ ℕ-Diagram ] isPostnikovTower P
PostnikovTowerOf X =
  ((λ n → ∥ X ∥ n) , TruncMap) , isOfHLevelTrunc , TruncMapConnected


{- The product and limit over a fixed diagram are unique -}
module UniquenessProd (A : ℕ-Family) (P P' : Type ℓ-zero)
       (c : fCone A P) (c' : fCone A P')
       (e : isProdCone A P c) (e' : isProdCone A P' c') where

  map→cone-P : (X : Type ℓ-zero) → (X → P) → fCone A X
  map→cone-P X = equivFun (_ , e X)

  map→cone-P-composes : (X Y : Type ℓ-zero) (f : Y → X) (g : X → P)
    → map→cone-P Y (g ∘ f)
    ≡ ConeℕFam→Map→ConeℕFam A X Y (map→cone-P X g) f
  map→cone-P-composes X Y f g = refl

  injP : (X : Type ℓ-zero) (f g : X → P)
       → map→cone-P X f ≡ map→cone-P X g
       → f ≡ g
  injP X f g p = equivInj (_ , e X) f g p

  map→cone-P-id : map→cone-P P (λ x → x) ≡ c
  map→cone-P-id = refl

  cone→map-P : (X : Type ℓ-zero) → fCone A X → (X → P)
  cone→map-P X = equivFun (invEquiv (_ , e X))

  map→cone-P' : (X : Type ℓ-zero) → (X → P') → fCone A X
  map→cone-P' X = equivFun (_ , e' X)

  map→cone-P'-composes : (X Y : Type ℓ-zero) (f : Y → X) (g : X → P')
    → map→cone-P' Y (g ∘ f)
    ≡ ConeℕFam→Map→ConeℕFam A X Y (map→cone-P' X g) f
  map→cone-P'-composes X Y f g = refl

  injP' : (X : Type ℓ-zero) (f g : X → P')
       → map→cone-P' X f ≡ map→cone-P' X g
       → f ≡ g
  injP' X f g p = equivInj (_ , e' X) f g p

  map→cone-P'-id : map→cone-P' P' (λ x → x) ≡ c'
  map→cone-P'-id = refl

  cone→map-P' : (X : Type ℓ-zero) → (fCone A X) → (X → P')
  cone→map-P' X = equivFun (invEquiv (_ , e' X))

  f : P → P'
  f = cone→map-P' P c

  map→cone-P'-f : map→cone-P' P f ≡ c
  map→cone-P'-f = secEq (_ , e' P) c

  g : P' → P
  g = cone→map-P P' c'

  map→cone-P-g : map→cone-P P' g ≡ c'
  map→cone-P-g = secEq (_ , e P') c'

  fog-id : f ∘ g ≡ (λ x → x)
  fog-id =
    injP' P' (f ∘ g) (λ x → x)
      (map→cone-P'-composes P P' g f
      ∙ cong (λ c1 → ConeℕFam→Map→ConeℕFam A P P' c1 g) map→cone-P'-f 
      ∙ map→cone-P-g
      ∙ map→cone-P'-id ⁻¹)

  gof-id : g ∘ f ≡ (λ x → x)
  gof-id =
    injP P (g ∘ f) (λ x → x)
      (map→cone-P-composes P' P f g
      ∙ cong (λ c1 → ConeℕFam→Map→ConeℕFam A P' P c1 f) map→cone-P-g
      ∙ map→cone-P'-f
      ∙ map→cone-P-id ⁻¹)

  isoPP' : Iso P P'
  Iso.fun isoPP' = f
  Iso.inv isoPP' = g
  Iso.rightInv isoPP' = funExt⁻ fog-id
  Iso.leftInv isoPP' = funExt⁻ gof-id

  equivPP' : P ≃ P'
  equivPP' = isoToEquiv isoPP'

  mapPath-useful : equivFun (invEquiv (equivPP')) ≡ g
  mapPath-useful = refl
  
  pathPP' : transport (λ i → ConeℕFam A (ua (equivPP') i)) (c) ≡ c'
  pathPP' = conePath A P P' c equivPP'
            ∙ map→cone-P-g

module UniquenessLim (A : ℕ-Diagram) (P P' : Type ℓ-zero)
       (c : ConeℕDiag A P) (c' : ConeℕDiag A P')
       (e : isLimitCone (fst A) (snd A) P c)
       (e' : isLimitCone (fst A) (snd A) P' c') where


  map→cone-P : (X : Type ℓ-zero) → (X → P) → ConeℕDiag A X
  map→cone-P X = equivFun (_ , e X)

  map→cone-P-composes : (X Y : Type ℓ-zero) (f : Y → X) (g : X → P)
    → map→cone-P Y (g ∘ f)
    ≡ ConeℕDiag→Map→ConeℕDiag A X Y (map→cone-P X g) f
  map→cone-P-composes X Y f g = refl

  injP : (X : Type ℓ-zero) (f g : X → P)
       → map→cone-P X f ≡ map→cone-P X g
       → f ≡ g
  injP X f g p = equivInj (_ , e X) f g p

  map→cone-P-id : map→cone-P P (λ x → x) ≡ c
  map→cone-P-id = refl

  cone→map-P : (X : Type ℓ-zero) → ConeℕDiag A X → (X → P)
  cone→map-P X = equivFun (invEquiv (_ , e X))

  map→cone-P' : (X : Type ℓ-zero) → (X → P') → ConeℕDiag A X
  map→cone-P' X = equivFun (_ , e' X)

  map→cone-P'-composes : (X Y : Type ℓ-zero) (f : Y → X) (g : X → P')
    → map→cone-P' Y (g ∘ f)
    ≡ ConeℕDiag→Map→ConeℕDiag A X Y (map→cone-P' X g) f
  map→cone-P'-composes X Y f g = refl

  injP' : (X : Type ℓ-zero) (f g : X → P')
       → map→cone-P' X f ≡ map→cone-P' X g
       → f ≡ g
  injP' X f g p = equivInj (_ , e' X) f g p

  map→cone-P'-id : map→cone-P' P' (λ x → x) ≡ c'
  map→cone-P'-id = refl

  cone→map-P' : (X : Type ℓ-zero) → (ConeℕDiag A X) → (X → P')
  cone→map-P' X = equivFun (invEquiv (_ , e' X))

  f : P → P'
  f = cone→map-P' P c

  map→cone-P'-f : map→cone-P' P f ≡ c
  map→cone-P'-f = secEq (_ , e' P) c

  g : P' → P
  g = cone→map-P P' c'

  map→cone-P-g : map→cone-P P' g ≡ c'
  map→cone-P-g = secEq (_ , e P') c'

  fog-id : f ∘ g ≡ (λ x → x)
  fog-id =
    injP' P' (f ∘ g) (λ x → x)
      (map→cone-P'-composes P P' g f
      ∙ cong (λ c1 → ConeℕDiag→Map→ConeℕDiag A P P' c1 g) map→cone-P'-f 
      ∙ map→cone-P-g
      ∙ map→cone-P'-id ⁻¹)

  gof-id : g ∘ f ≡ (λ x → x)
  gof-id =
    injP P (g ∘ f) (λ x → x)
      (map→cone-P-composes P' P f g
      ∙ cong (λ c1 → ConeℕDiag→Map→ConeℕDiag A P' P c1 f) map→cone-P-g
      ∙ map→cone-P'-f
      ∙ map→cone-P-id ⁻¹)

  isoPP' : Iso P P'
  Iso.fun isoPP' = f
  Iso.inv isoPP' = g
  Iso.rightInv isoPP' = funExt⁻ fog-id
  Iso.leftInv isoPP' = funExt⁻ gof-id

  equivPP' : P ≃ P'
  equivPP' = isoToEquiv isoPP'

  mapPath-useful : equivFun (invEquiv (equivPP')) ≡ g
  mapPath-useful = refl
  
  pathPP' : transport (λ i → ConeℕDiag A (ua (equivPP') i)) (c) ≡ c'
  pathPP' = conePathD A P P' c equivPP'
            ∙ map→cone-P-g


UniqueProductPath : (A : ℕ-Family) (P P' : ℕ-Product A) → P ≡ P'
UniqueProductPath A P (P' , c' , e')  =
  ΣPathP (ua (equivPP' A (fst P) (P') (fst (snd P)) (c')
                         (snd (snd P)) (e'))
           , ΣPathP ((toPathP (pathPP' A (fst P) P' (fst (snd P)) c'
                                         (snd (snd P)) e'))
           , toPathP (funExt (λ Y → isPropIsEquiv _ _ (e' Y)))))
  where
    open UniquenessProd

UniqueProduct' : (A : ℕ-Family) → isContr (ℕ-Product A)
UniqueProduct' A = (ConeℕFam A Unit , One-Cones-Product A)
                 , λ P → UniqueProductPath A
                          (ConeℕFam A Unit , One-Cones-Product A) P

UniqueLimitPath : (A : ℕ-Diagram) (L L' : ℕ-Limit A) → L ≡ L'
UniqueLimitPath A (L , c , e) (L' , c' , e') =
  ΣPathP (ua (equivPP' A L L' c c' e e')
         , ΣPathP ((toPathP (pathPP' A L L' c c' e e'))
         , toPathP (funExt (λ Y → isPropIsEquiv _ _ (e' Y)))))
  where
    open UniquenessLim

UniqueLimit' : (A : ℕ-Diagram) → isContr (ℕ-Limit A)
UniqueLimit' A = (ConeℕDiag A Unit , One-Cones-Limit A)
               , λ L → UniqueLimitPath A
                        (ConeℕDiag A Unit , One-Cones-Limit A) L

UniqueLimit : (A : ℕ-Diagram) (L L' : ℕ-Limit A) → fst L ≃ fst L'
UniqueLimit A (L , c , e) (L' , c' , e') = equivPP' A L L' c c' e e'
  where
    open UniquenessLim

UniqueLimitComp : (A : ℕ-Diagram) (L L' : ℕ-Limit A) (n : ℕ)
  → fst (fst (snd L)) n ≡ fst (fst (snd L')) n ∘ equivFun (UniqueLimit A L L')
UniqueLimitComp A L L' n =
  funExt⁻ (fst (PathPΣ ((secEq (_ , snd (snd L') (fst L)) (fst (snd L))) ⁻¹))) n
  where
    open UniquenessLim

UniqueLimitInv : (A : ℕ-Diagram) (L L' : ℕ-Limit A)
  → invEquiv (UniqueLimit A L L') ≡ UniqueLimit A L' L
UniqueLimitInv A (L , c , e) (L' , c' , e') =
  ΣPathP (refl , isPropIsEquiv _ _ _)
  where
    open UniquenessLim


{- we fix a choice of product and limit, but this is inessential -}
Π : (A : ℕ-Family) → ℕ-Product A
Π A = fst (UniqueProduct' A)

Π-over : (X : Type ℓ-zero) → (A : X → ℕ-Family)
                           → ((x : X) → ℕ-Product (A x))
Π-over X A x = Π (A x)

ℓim : (A : ℕ-Diagram) → ℕ-Limit A
ℓim A = fst (UniqueLimit' A)

KLimitCone : (X : Type ℓ-zero) → ConeℕDiag (KDiagram X) X
fst (KLimitCone X) n x = x
snd (KLimitCone X) n x = refl

KLimitIso : (X Y : Type)
  → isIso (ConeℕDiag→Map→ConeℕDiag (KDiagram X) X Y (KLimitCone X))
fst (KLimitIso X Y) (c , h) = c 0
fst (snd (KLimitIso X Y)) (c , h) =
  ConeIdentity (KDiagram X) Y _ (c , h)
  ((ℕElim (λ y → refl) (λ n p y → h n y ∙ p y))
  , ℕElim (λ u → rUnit _) (λ n p y → rUnit _))
snd (snd (KLimitIso X Y)) f = refl

KLimit : (X : Type ℓ-zero) → is-ℕ-Limit-of (KDiagram X) X
fst (KLimit X) = KLimitCone X
snd (KLimit X) Y =
  isoToIsEquiv (iso _ (fst (KLimitIso X Y))
                      (fst (snd (KLimitIso X Y))) (snd (snd (KLimitIso X Y))))

Kℓim : (X : Type ℓ-zero) → fst (ℓim (KDiagram X)) ≃ X
Kℓim X = UniqueLimit (KDiagram X) (ℓim (KDiagram X)) (X , KLimit X)


equiv→Lim→Lim : (A : ℕ-Diagram) (X : Type ℓ-zero)
  → is-ℕ-Limit-of A X → (Y : Type ℓ-zero) → X ≃ Y
  → is-ℕ-Limit-of A Y
equiv→Lim→Lim A X XL Y e =
  EquivJ (λ Z e → is-ℕ-Limit-of A Z) XL (invEquiv e)

coneEquiv→LimMap : (A B : ℕ-Diagram)
                    → Σ[ e ∈ ((X : Type ℓ-zero)
                          → ConeℕDiag A X ≃ ConeℕDiag B X) ]
                       ((X Y : Type ℓ-zero) (f : Y → X) (c : ConeℕDiag A X)
                     → ConeℕDiag→Map→ConeℕDiag B X Y (fst (e X) c) f
                      ≡ (fst (e Y) (ConeℕDiag→Map→ConeℕDiag A X Y c f)))
                    → ((X : Type ℓ-zero)
                    → is-ℕ-Limit-of A X → is-ℕ-Limit-of B X)
coneEquiv→LimMap A B (e , he) X (c , hc) =
  (fst (e X) c) ,
  λ Y → transport (λ i → isEquiv (λ f → he X Y f c (~ i)))
                   (equivIsEquiv (compEquiv (_ , hc Y) (e Y)))

coneEquivLimProj :  (A B : ℕ-Diagram)
                    → (pe : Σ[ e ∈ ((X : Type ℓ-zero)
                          → ConeℕDiag A X ≃ ConeℕDiag B X) ]
                       ((X Y : Type ℓ-zero) (f : Y → X) (c : ConeℕDiag A X)
                     → ConeℕDiag→Map→ConeℕDiag B X Y (fst (e X) c) f
                      ≡ (fst (e Y) (ConeℕDiag→Map→ConeℕDiag A X Y c f))))
                    → (X : Type ℓ-zero) → (L : is-ℕ-Limit-of A X)
                    → (fst (fst (coneEquiv→LimMap A B pe X L)))
                     ≡ fst (fst ((fst pe) X) (fst L))
coneEquivLimProj A B pe X L = refl

indexShiftOfOne : ℕ-Diagram → ℕ-Diagram
fst (indexShiftOfOne (A , a)) n = A (1 + n)
snd (indexShiftOfOne (A , a)) n = a (1 + n)

indexShiftOfOneCone : (A : ℕ-Diagram) (X : Type ℓ-zero)
  → ConeℕDiag A X → ConeℕDiag (indexShiftOfOne A) X
fst (indexShiftOfOneCone (A , a) X (c , h)) n = c (1 + n)
snd (indexShiftOfOneCone (A , a) X (c , h)) n = h (1 + n)

{- Helper lemmas to show that the limit of a diagram is also the limit of
   the degree one shift of that diagram -}
indexShiftOneIso1 : (A : ℕ-Diagram) (X : Type ℓ-zero)
   (c : ConeℕDiag (indexShiftOfOne A) X)
   → (Σ[ f ∈ (X → (fst A) 0) ] (f ≡ (snd A) 0 ∘ (fst c 0)))
    ≡ (Σ[ f ∈ (X → (fst A) 0) ] ((x : X) → (snd A) 0 ((fst c 0 x)) ≡ f x))
indexShiftOneIso1 A X c =
  ua (isoToEquiv
     (Σ-cong-iso-snd
     (λ f → compIso symIso (invIso funExtIso))))

indexShiftOfOneContrFib : (A : ℕ-Diagram) (X : Type ℓ-zero)
  (c : ConeℕDiag (indexShiftOfOne A) X)
  → isContr (Σ[ f ∈  (X → (fst A) 0) ] f ≡ (snd A) 0 ∘ (fst c 0))
fst (indexShiftOfOneContrFib A X c) = ((snd A) 0 ∘ (fst c 0)) , refl
snd (indexShiftOfOneContrFib A X c) =
  λ p → J (λ (y : X → (fst A) 0)
              (q : (snd A 0 ∘ fst c 0) ≡ y)
              → ((snd A) 0 ∘ (fst c 0) , refl) ≡ (y , q ⁻¹))
            refl (snd p ⁻¹)

indexShiftOneCFunction : (A : ℕ-Diagram) (X : Type ℓ-zero)
  (c : ConeℕDiag (indexShiftOfOne A) X)
  → Σ[ c' ∈ (ConeℕDiag A X) ] (indexShiftOfOneCone A X c' ≡ c)
  → Σ[ f ∈ (X → (fst A) 0) ] ((x : X) → (snd A) 0 ((fst c 0 x)) ≡ f x)
indexShiftOneCFunction A X c (c' , p) =
  J (λ y p → Σ[ f ∈ (X → (fst A) 0) ]
              ((x : X) → (snd A) 0 ((fst y 0 x)) ≡ f x))
    (fst c' 0 , λ x → snd c' 0 x) p

indexShiftOneGFunction : (A : ℕ-Diagram) (X : Type ℓ-zero)
  (c : ConeℕDiag (indexShiftOfOne A) X)
  → Σ[ f ∈ (X → (fst A) 0) ] ((x : X) → (snd A) 0 ((fst c 0) x) ≡ f x)
  → Σ[ c' ∈ (ConeℕDiag A X) ] (indexShiftOfOneCone A X c' ≡ c)
indexShiftOneGFunction A X c (f , p) =
  ((ℕElim (λ x → f x) (λ n _ → fst c n))
  , ℕElim p λ n _ → snd c n)
  , refl

indexShiftOneIso2 : (A : ℕ-Diagram) (X : Type ℓ-zero)
  (c : ConeℕDiag (indexShiftOfOne A) X)
  → Iso (Σ[ c' ∈ (ConeℕDiag A X) ] (indexShiftOfOneCone A X c' ≡ c))
         (Σ[ f ∈ (X → (fst A) 0) ] ((x : X) → (snd A) 0 ((fst c 0 x)) ≡ f x))
Iso.fun (indexShiftOneIso2 A X c) (c' , p) =
  indexShiftOneCFunction A X c (c' , p)
Iso.inv (indexShiftOneIso2 A X c) (f , p) =
  indexShiftOneGFunction A X c (f , p)
Iso.rightInv (indexShiftOneIso2 A X c) (f , p) =
  transportRefl ((f , p))
Iso.leftInv (indexShiftOneIso2 A X c) (c' , p) =
  J (λ (y : ConeℕDiag (indexShiftOfOne A) X)
       (p : indexShiftOfOneCone A X c' ≡ y)
     → indexShiftOneGFunction A X y
        (indexShiftOneCFunction A X y (c' , p))
      ≡ (c' , p))
      (cong (indexShiftOneGFunction A X (indexShiftOfOneCone A X c'))
            (JRefl ((λ (y : ConeℕDiag (indexShiftOfOne A) X)
                       (p : indexShiftOfOneCone A X c' ≡ y)
              → Σ[ f ∈ (X → (fst A) 0) ]
              ((x : X) → (snd A) 0 ((fst y 0 x)) ≡ f x)))
              ((fst c' 0 , λ x → snd c' 0 x)))
      ∙ ΣPathP ((ΣPathP ((funExt (ℕElim refl (λ n _ → refl))) ,
                funExt (ℕElim refl (λ n _ → refl)))) ,
                toPathP (transportRefl _)))
      p


{- There is a natural equivalence between cones on a diagram and cones on the
   degree one shift of that diagram -}
indexShiftOfOneConeEq : (A : ℕ-Diagram) (X : Type ℓ-zero)
  → (ConeℕDiag A X) ≃ (ConeℕDiag (indexShiftOfOne A) X)
indexShiftOfOneConeEq A X =
  (indexShiftOfOneCone A X) ,
    record { equiv-proof =
             λ c → transport
                    (λ i → isContr
                            (ua (isoToEquiv
                                (invIso (indexShiftOneIso2 A X c))) i))
                    (transport (λ i → isContr (indexShiftOneIso1 A X c i))
                    (indexShiftOfOneContrFib A X c)) }

indexShiftOfOneNat : (A : ℕ-Diagram) (X Y : Type ℓ-zero) (f : Y → X)
  (c : ConeℕDiag A X)
  → ConeℕDiag→Map→ConeℕDiag (indexShiftOfOne A) X Y
       (fst (indexShiftOfOneConeEq A X) c) f
   ≡ fst (indexShiftOfOneConeEq A Y) (ConeℕDiag→Map→ConeℕDiag A X Y c f)
indexShiftOfOneNat A X Y f c = refl

{- Inductive definition of a diagram shifted by an arbitrary index -}
indexShiftDiag' : ℕ → ℕ-Diagram → ℕ-Diagram
indexShiftDiag' zero A = A
indexShiftDiag' (suc zero) A = indexShiftOfOne A
indexShiftDiag' (suc (suc n)) A = indexShiftOfOne (indexShiftDiag' (suc n) A)


numMapEquiv : (A : ℕ-Diagram) (m n : ℕ) → m ≡ n → fst A m ≃ fst A n
numMapEquiv A m n p = transport (cong (fst A) p)
                    , isEquivTransport (cong (fst A) p)

indexShiftEquiv : (n k : ℕ) (A : ℕ-Diagram) → fst (indexShiftDiag' k A) n
                                             ≃ fst A (k + n)
indexShiftEquiv n zero A = idEquiv (fst A n)
indexShiftEquiv n (suc zero) A = idEquiv (fst A (1 + n))
indexShiftEquiv n (suc (suc k)) A =
  indexShiftEquiv (suc n) (suc k) A
  ∙ₑ numMapEquiv A (1 + (k + (1 + n))) (1 + (1 + (k + n)))
                   (cong suc (+-comm k (1 + n))
                    ∙ cong (suc ∘ suc) (+-comm n k)) 

indexShiftEquiv' : (n k : ℕ) (A : ℕ-Diagram) → fst A (n + k) ≃ fst A (k + n)
indexShiftEquiv' n k A = numMapEquiv A (n + k) (k + n) (+-comm n k)

indexShiftingDiag : (f : ℕ → ℕ) → ((λ (n : ℕ) → f (1 + n))
                                    ≡ (λ (n : ℕ) → 1 + f n))
                  → ℕ-Diagram → ℕ-Diagram
fst (indexShiftingDiag f p A) = λ n → fst A (f n)
snd (indexShiftingDiag f p A) =
  λ n → snd A (f n) ∘ transport (λ i → fst A (p i n))

indexShift : (k : ℕ) → ℕ-Diagram → ℕ-Diagram
indexShift k A = indexShiftDiag' k A

indexShiftOfOneConn : (A : ℕ-Diagram) (k : ℕ)
  → ((n : ℕ) → isConnectedFun (k + n) (snd A n))
  → (n : ℕ) → isConnectedFun (1 + k + n) (snd (indexShiftOfOne A) n)
indexShiftOfOneConn A k p zero =
  transport (λ i → isConnectedFun ((+-comm k 1 ∙ cong suc (+-comm 0 k)) i)
                                   (snd A 1))
            (p 1)
indexShiftOfOneConn A k p (suc n) =
  transport (λ i → isConnectedFun (add2Assoc k n (~ i)) (snd A (2 + n)))
            (p (2 + n))

{- shifting a postnikov tower shifts the degree of connectivity of the maps -}
indexShiftDiagConn : (A : ℕ-Diagram) → isPostnikovTower A
  → (n k : ℕ) → isConnectedFun (k + n) (snd (indexShiftDiag' k A) n)
indexShiftDiagConn A p n zero = snd p n
indexShiftDiagConn A p n (suc zero) = snd p (1 + n)
indexShiftDiagConn A p n (suc (suc k)) =
  indexShiftOfOneConn (indexShiftDiag' (1 + k) A) (1 + k)
  (λ m → indexShiftDiagConn A p m (suc k)) n
