module Preliminary where

open import Cubical.Data.Nat renaming (elim to ℕElim)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Foundations.Everything
open import Cubical.HITs.Truncation
open import Cubical.Homotopy.Connected

△ : (X : Type ℓ-zero) → (X → X × X)
△ X x = x , x

pairOfMaps : {W X Y Z : Type ℓ-zero}
             → (W → Y) → (X → Z)
             → (W × X → Y × Z)
pairOfMaps f g (w , x) = f w , g x

-- defining different kinds of diagrams
ℕ-Family : Type (ℓ-suc ℓ-zero)
ℕ-Family = ℕ → Type ℓ-zero

Family-over-index : (X : Type ℓ-zero) (A : X → ℕ-Family)
                    (n : ℕ) → Σ[ x ∈ X ] (A x n) → X
Family-over-index X A n = fst

ℕ-Diagram : Type (ℓ-suc ℓ-zero)
ℕ-Diagram = Σ[ A ∈ ℕ-Family ] ((n : ℕ) → A (1 + n) → A n)

Diagram-over-index : (X : Type ℓ-zero) (A : X → ℕ-Diagram)
                     (n : ℕ) → Σ[ x ∈ X ] (fst (A x) n) → X
Diagram-over-index X A n = fst

KDiagram : Type ℓ-zero → ℕ-Diagram
KDiagram X = (λ _ → X) , (λ _ x → x)

-- defining cones over diagrams
ConeℕFam : ℕ-Family → Type (ℓ-zero) → Type (ℓ-zero)
ConeℕFam A X = (n : ℕ) → X → A n

ConeℕDiag : ℕ-Diagram → Type (ℓ-zero) → Type (ℓ-zero)
ConeℕDiag (A , a) X = Σ[ c ∈ ConeℕFam A X ]
                      ((n : ℕ) (x : X) → a n (c (1 + n) x) ≡ c n x)

-- maps that will be used to define limits 
ConeℕFam→Map→ConeℕFam : (A : ℕ-Family)
  (X Y : Type ℓ-zero) → (ConeℕFam A X) → (Y → X) → ConeℕFam A Y
ConeℕFam→Map→ConeℕFam A X Y c f n y = c n (f y)

ConeℕDiag→Map→ConeℕDiag : (A : ℕ-Diagram)
  (X Y : Type ℓ-zero) → (ConeℕDiag A X) → (Y → X) → ConeℕDiag A Y
ConeℕDiag→Map→ConeℕDiag (A , a) X Y (c , h) f =
  (ConeℕFam→Map→ConeℕFam A X Y c f) , (λ n y → h n (f y))

postulate
  Map→ConeℕDiag-composes : (A : ℕ-Diagram)
    (X Y Z : Type ℓ-zero) (c : ConeℕDiag A X) (f : Z → Y) (g : Y → X)
    → ConeℕDiag→Map→ConeℕDiag A Y Z (ConeℕDiag→Map→ConeℕDiag A X Y c g) f
    ≡ ConeℕDiag→Map→ConeℕDiag A X Z c (g ∘ f)

-- defining limits of diagrams
ℕ-Product : (A : ℕ-Family) → Type (ℓ-suc ℓ-zero)
ℕ-Product A =
  Σ[ P ∈ Type ℓ-zero ]
  Σ[ c ∈ ConeℕFam A P ]
    ((X : Type ℓ-zero) → isEquiv (ConeℕFam→Map→ConeℕFam A P X c))

ℕ-Limit : (A : ℕ-Diagram) → Type (ℓ-suc ℓ-zero)
ℕ-Limit A =
  Σ[ L ∈ Type ℓ-zero ]
  Σ[ c ∈ ConeℕDiag A L ]
    ((X : Type ℓ-zero) → isEquiv (ConeℕDiag→Map→ConeℕDiag A L X c))

is-ℕ-Limit-of : ℕ-Diagram → Type ℓ-zero → Type (ℓ-suc ℓ-zero)
is-ℕ-Limit-of A X =
  Σ[ c ∈ ConeℕDiag A X ]
    ((Y : Type ℓ-zero) → isEquiv (ConeℕDiag→Map→ConeℕDiag A X Y c))

-- there is a unique limit over any diagram
postulate
  UniqueProduct' : (A : ℕ-Family) → isContr (ℕ-Product A)

  UniqueLimit' : (A : ℕ-Diagram) → isContr (ℕ-Limit A)

  UniqueLimit : (A : ℕ-Diagram) (L L' : ℕ-Limit A) → fst L ≃ fst L'

  UniqueLimitInv : (A : ℕ-Diagram) (L L' : ℕ-Limit A)
    → invEquiv (UniqueLimit A L L') ≡ UniqueLimit A L' L

  UniqueLimitMap : (A : ℕ-Diagram) (L L' : ℕ-Limit A)
    → fst (UniqueLimit A L L')
     ≡ fst (invEquiv (_ , (snd (snd L')) (fst L))) (fst (snd L))

-- the unique limit has a name
Π : (A : ℕ-Family) → ℕ-Product A
Π A = fst (UniqueProduct' A)

Π-over : (X : Type ℓ-zero) → (A : X → ℕ-Family)
                           → ((x : X) → ℕ-Product (A x))
Π-over X A x = Π (A x)

ℓim : (A : ℕ-Diagram) → ℕ-Limit A
ℓim A = fst (UniqueLimit' A)

-- limits under base-change
ℓim-over : (X : Type ℓ-zero) → (A : X → ℕ-Diagram)
                        → ((x : X) → ℕ-Limit (A x))
ℓim-over X A x = ℓim (A x)

Π-proj-over : (X : Type ℓ-zero) → (A : X → ℕ-Family)
                               → Σ[ x ∈ X ] (fst (Π-over X A x)) → X
Π-proj-over X A = fst

ℓim-proj-over : (X : Type ℓ-zero) → (A : X → ℕ-Diagram)
                                  → Σ[ x ∈ X ] (fst (ℓim-over X A x)) → X
ℓim-proj-over X A = fst

postulate
  KLimit : (X : Type ℓ-zero) → is-ℕ-Limit-of (KDiagram X) X
{-fst (fst (KLimit X)) n x = x
snd (fst (KLimit X)) n x = refl
snd (KLimit X) = {!!}
  where
    limitIso : (Y : Type)
      → isIso (ConeℕDiag→Map→ConeℕDiag (KDiagram X) X Y ((λ n x → x) ,
                                                           (λ n x → refl)))
    fst (limitIso Y) (c , h) = c 0
    fst (snd (limitIso Y)) (c , h) =
      ΣPathP ((funExt
              (ℕElim refl
              (λ n p → p ∙ funExt (λ y → h n y ⁻¹))))
             , toPathP {!!}) -- last hole is filled by path induction
    snd (snd (limitIso Y)) f = refl-}

Kℓim : (X : Type ℓ-zero) → fst (ℓim (KDiagram X)) ≃ X
Kℓim X = UniqueLimit (KDiagram X) (ℓim (KDiagram X)) (X , KLimit X)

postulate
  indexShiftMaps : (k n : ℕ) (A : ℕ-Diagram)
    → fst A (k + (1 + n)) → fst A (k + n)

indexShift : (k : ℕ) → ℕ-Diagram → ℕ-Diagram
indexShift k A = (λ n → fst A (k + n)) , (λ n → indexShiftMaps k n A)

postulate
 Limit-is-indexShiftLimit : (k : ℕ) (A : ℕ-Diagram)
   → is-ℕ-Limit-of (indexShift k A) (fst (ℓim A))

-- limit over a tower is the same as a limit over a restriction of the tower
indexShiftLimit : (k : ℕ) (A : ℕ-Diagram)
  →  fst (ℓim A) ≃ fst (ℓim (indexShift k A))
indexShiftLimit k A =
  UniqueLimit (indexShift k A) (fst (ℓim A) , Limit-is-indexShiftLimit k A)
                               (ℓim (indexShift k A))

  --indexShiftGood : (k : ℕ) (A : ℕ-Diagram)

-- property of being a postnikov tower
isPostnikovTower : ℕ-Diagram → Type ℓ-zero
isPostnikovTower (A , a) = ((n : ℕ) → isOfHLevel n (A n))
                         × ((n : ℕ) → isConnectedFun n (a n))

-- cospans and pullbacks of maps
MapBetweenMaps : {W X Y Z : Type ℓ-zero}
                 (f : W → X) (g : Y → Z)
                 → Type ℓ-zero
MapBetweenMaps {W = W} {X = X} {Y = Y} {Z = Z} f g =
  Σ[ h ∈ (W → Y) ] Σ[ k ∈ (X → Z) ] ((w : W) → (g ∘ h) w ≡ (k ∘ f) w)

topMapBetweenMaps : {W X Y Z : Type ℓ-zero}
                    (f : W → X) (g : Y → Z)
                    → MapBetweenMaps f g
                    → W → Y
topMapBetweenMaps f g = fst

bottomMapBetweenMaps : {W X Y Z : Type ℓ-zero}
                       (f : W → X) (g : Y → Z)
                       → MapBetweenMaps f g
                       → X → Z
bottomMapBetweenMaps f g (h , k , H) = k

homotopyMapBetweenMaps : {W X Y Z : Type ℓ-zero}
                         (f : W → X) (g : Y → Z)
                         (M : MapBetweenMaps f g)
                         → (w : W) → ((g ∘ (topMapBetweenMaps f g M)) w
                          ≡ ((bottomMapBetweenMaps f g M) ∘ f) w)
homotopyMapBetweenMaps f g (h , k , H) = H

CoSpanOfMaps : {U V W X Y Z : Type ℓ-zero}
               (f : U → V) (g : W → X) (h : Y → Z)
               → Type ℓ-zero
CoSpanOfMaps f g h = MapBetweenMaps f h × MapBetweenMaps g h

FrontPullback : {U V W X Y Z : Type ℓ-zero}
               (f : U → V) (g : W → X) (h : Y → Z)
               → CoSpanOfMaps f g h
               → Type ℓ-zero
FrontPullback {V = V} {X = X} f g h ((j , k , H) , (j' , k' , H')) =
  Σ[ v ∈ V ] Σ[ x ∈ X ] k(v) ≡ k'(x)

BackPullback : {U V W X Y Z : Type ℓ-zero}
               (f : U → V) (g : W → X) (h : Y → Z)
               → CoSpanOfMaps f g h
               → Type ℓ-zero
BackPullback {U = U} {W = W} f g h ((j , k , H) , (j' , k' , H')) =
  Σ[ u ∈ U ] Σ[ w ∈ W ] j(u) ≡ j'(w)

PullbackOfMaps : {U V W X Y Z : Type ℓ-zero}
                 (f : U → V) (g : W → X) (h : Y → Z)
                 (cspn : CoSpanOfMaps f g h)
                 → BackPullback f g h cspn
                 → FrontPullback f g h cspn
PullbackOfMaps f g h ((j , k , H) , (j' , k' , H')) (u , w , p) =
  (f u) , ((g w) , (H u ⁻¹ ∙ cong h p ∙ H' w))

-- facts about truncation, connectedness and so on
postulate
  ConnectedPullback : {U V W X Y Z : Type ℓ-zero}
               (f : U → V) (g : W → X) (h : Y → Z)
               → (cspn : CoSpanOfMaps f g h) (n : ℕ)
               → isConnectedFun n f
               → isConnectedFun n g
               → isConnectedFun (n + 1) h
               → isConnectedFun n (PullbackOfMaps f g h cspn)

  Trunc→Connected→Equiv : (A B : Type ℓ-zero) (n : ℕ)
                         → isOfHLevel n A
                         → isOfHLevel n B
                         → (f : A → B)
                         → isConnectedFun n f
                         → isEquiv f
                         
silly : (X : Type ℓ-zero) (n : ℕ) → X → ∥ X ∥ n
silly X n = ∣_∣ₕ

postulate
  TruncUniversal : {X : Type ℓ-zero} (n : ℕ) → (Y : Type ℓ-zero)
                → isOfHLevel n Y
                → isEquiv {A = ∥ X ∥ n → Y} {B = X → Y} (λ f → f ∘ ∣_∣ₕ)

  TruncConnected : {X : Type ℓ-zero} (n : ℕ) → isConnectedFun n (silly X n) 

  TruncNatural : {X : Type ℓ-zero} (n : ℕ) → (Y Z : Type ℓ-zero)
              → (hY : isOfHLevel n Y)
              → (hZ : isOfHLevel n Z)
              → (f : X → Y)
              → (g : Y → Z)
              → fst (invEquiv (_ , (TruncUniversal n Z hZ))) (g ∘ f)
               ≡ g ∘ (fst (invEquiv (_ , (TruncUniversal n Y hY))) f)

  TruncMap : {X : Type ℓ-zero} (n : ℕ) → ∥ X ∥ (1 + n) → ∥ X ∥ n

  TruncMapUniversal : {X : Type ℓ-zero} (n : ℕ) → (Y : Type ℓ-zero)
                   → isOfHLevel n Y
                   → isEquiv {A = ∥ X ∥ n → Y} {B = ∥ X ∥ (1 + n) → Y}
                              (λ f → f ∘ (TruncMap n))

  TruncMapConnected : {X : Type ℓ-zero} (n : ℕ)
                   → isConnectedFun n (TruncMap {X = X} n)

  Connected342 : (X Y Z : Type ℓ-zero) (n : ℕ) (f : X → Y) (g : Y → Z)
              → isConnectedFun n f → isConnectedFun n (g ∘ f)
              → isConnectedFun n g

  ConnectedEquiv : (X Y : Type ℓ-zero) (f : X → Y) → isEquiv f
    → (n : ℕ) → isConnectedFun n f

  Connected→ConnectedComp : (X Y Z : Type ℓ-zero) (f : X → Y) (g : Y → Z)
                          (n : ℕ) → isConnectedFun n f → isConnectedFun n g
                          → isConnectedFun n (g ∘ f)

-- postnikov tower of a fixed space
PostnikovTowerOf : Type ℓ-zero → Σ[ P ∈ ℕ-Diagram ] isPostnikovTower P
PostnikovTowerOf X =
  ((λ n → ∥ X ∥ n) , TruncMap) , isOfHLevelTrunc , TruncMapConnected

-- morphisms between diagrams
MapOfFamilies : ℕ-Family → ℕ-Family → Type ℓ-zero
MapOfFamilies A B = (n : ℕ) → A n → B n

postulate
  MapOfFamilies→MapOfProducts : (A B : ℕ-Family)
    → MapOfFamilies A B → fst (Π A) → fst (Π B)

EquivOfFamilies : ℕ-Family → ℕ-Family → Type ℓ-zero
EquivOfFamilies A B =
  Σ[ e ∈ MapOfFamilies A B ] ((n : ℕ) → isEquiv (e n))

EquivOfDiagrams : ℕ-Diagram → ℕ-Diagram → Type ℓ-zero
EquivOfDiagrams (A , a) (B , b) =
  Σ[ e ∈ EquivOfFamilies A B ]
    ((n : ℕ) (x : A (1 + n)) → (fst e) n (a n x) ≡ b n ((fst e) (1 + n) x))

MapOfDiagrams : ℕ-Diagram → ℕ-Diagram → Type ℓ-zero
MapOfDiagrams (A , a) (B , b) =
  Σ[ f ∈ MapOfFamilies A B ]
   ((n : ℕ) (x : A (1 + n)) → b n (f (1 + n) x) ≡ f n (a n x))

MapOfDiagrams→Coneℓim :
  (A B : ℕ-Diagram) → MapOfDiagrams A B → ConeℕDiag B (fst (ℓim A))
MapOfDiagrams→Coneℓim A B (f , h) =
  (λ n a → f n (fst (fst (snd (ℓim A))) n a))
  , λ n a → h n _ ∙ cong (f n) (snd (fst (snd (ℓim A))) n a)

MapOfDiagrams→MapOfFamilies : (A B : ℕ-Diagram)
  → MapOfDiagrams A B → MapOfFamilies (fst A) (fst B)
MapOfDiagrams→MapOfFamilies A B f = fst f

-- maps for characterising limit as a pullback
map0 : (A : ℕ-Diagram) → fst (Π (fst A)) → (fst (Π (fst A)) × fst (Π (fst A)))
map0 A = △ (fst (Π (fst A)))

postulate
  map1 : (A : ℕ-Diagram)
    → (fst (Π (fst A)) × fst (Π (fst A)))
    → (fst (Π (fst A)) × fst (Π (fst A)))

FF1 : (A B : ℕ-Diagram) → MapOfDiagrams A B
  → (fst (Π (fst A)) × fst (Π (fst A)))
  → (fst (Π (fst B)) × fst (Π (fst B)))
FF1 A B f = pairOfMaps (MapOfFamilies→MapOfProducts (fst A) (fst B) (fst f))
                       (MapOfFamilies→MapOfProducts (fst A) (fst B) (fst f))

postulate
  specialCospan : (A B : ℕ-Diagram) (f : MapOfDiagrams A B) → 
    CoSpanOfMaps (FF1 A B f)
                 (MapOfFamilies→MapOfProducts (fst A) (fst B) (fst f))
                 (FF1 A B f)

  FrontPBLimit : (A B : ℕ-Diagram) (f : MapOfDiagrams A B) →
    is-ℕ-Limit-of B (FrontPullback _ _ (FF1 A B f) (specialCospan A B f))

ℓimIsFrontPB : (A B : ℕ-Diagram) (f : MapOfDiagrams A B) →
  fst (ℓim B) ≃ FrontPullback _ _ (FF1 A B f) (specialCospan A B f)
ℓimIsFrontPB A B f =
  UniqueLimit B (ℓim B)
                ( FrontPullback _ _ (FF1 A B f) (specialCospan A B f)
                , FrontPBLimit A B f)

postulate
  BackPBLimit : (A B : ℕ-Diagram) (f : MapOfDiagrams A B) →
    is-ℕ-Limit-of A (BackPullback _ _ (FF1 A B f) (specialCospan A B f))

ℓimIsBackPB : (A B : ℕ-Diagram) (f : MapOfDiagrams A B) →
  fst (ℓim A) ≃ BackPullback _ _ (FF1 A B f) (specialCospan A B f)
ℓimIsBackPB A B f =
  UniqueLimit A (ℓim A)
                ( BackPullback _ _ (FF1 A B f) (specialCospan A B f)
                , BackPBLimit A B f)

postulate
  MapOfDiagrams→LimitCone :
    (A B : ℕ-Diagram) (f : MapOfDiagrams A B) (X : ℕ-Limit A)
    → ConeℕDiag B (fst X)

MapOfDiagrams→MapOfLimits' :
  (A B : ℕ-Diagram) (f : MapOfDiagrams A B)
                    (X : ℕ-Limit A) (Y : ℕ-Limit B)
                 → (fst X) → (fst Y)
MapOfDiagrams→MapOfLimits' A B f X (Y , cY , eY) =
  (fst (invEquiv (_ , eY (fst X)))) (MapOfDiagrams→LimitCone A B f X)

MapOfDiagrams→MapOfLimits :
  (A B : ℕ-Diagram) → (f : MapOfDiagrams A B)
                    → fst (ℓim A) → fst (ℓim B)
MapOfDiagrams→MapOfLimits A B f =
  MapOfDiagrams→MapOfLimits' A B f (ℓim A) (ℓim B)

postulate
  MapOfDiagrams→EquivOfDiagrams :
    (A B : ℕ-Diagram) → (e : MapOfDiagrams A B)
                      → ((n : ℕ) → isEquiv ((fst e) n))
                      → EquivOfDiagrams A B

  PullbackMapOfDiagramsToMapOfLimits : (A B : ℕ-Diagram)
    (f : MapOfDiagrams A B)
    → MapOfDiagrams→MapOfLimits' A B f (_ , BackPBLimit A B f)
                                         (_ , FrontPBLimit A B f)
     ≡ PullbackOfMaps _ _ (FF1 A B f) (specialCospan A B f)

  MapOfDiagramsEquivOfLimitsCommutes : (A B : ℕ-Diagram)
    (f : MapOfDiagrams A B)
    (W X : ℕ-Limit A) (Y Z : ℕ-Limit B)
    → MapOfDiagrams→MapOfLimits' A B f W Z
     ≡ fst (UniqueLimit B Y Z)
       ∘ MapOfDiagrams→MapOfLimits' A B f X Y
       ∘ fst (UniqueLimit A W X)
  
-- ugly
MapOfDiagramsIsPullback : (A B : ℕ-Diagram)
  (f : MapOfDiagrams A B)
  → MapOfDiagrams→MapOfLimits A B f
   ≡ fst (invEquiv (ℓimIsFrontPB A B f))
     ∘ PullbackOfMaps _ _ (FF1 A B f) (specialCospan A B f)
     ∘ fst (ℓimIsBackPB A B f)
MapOfDiagramsIsPullback A B f =
  MapOfDiagrams→MapOfLimits A B f
    ≡⟨
       MapOfDiagramsEquivOfLimitsCommutes A B f
         (ℓim A) (_ , BackPBLimit A B f)
         (_ , FrontPBLimit A B f) (ℓim B)
     ⟩
  fst (UniqueLimit B (_ , FrontPBLimit A B f) (ℓim B))
  ∘ MapOfDiagrams→MapOfLimits' A B f
      (_ , BackPBLimit A B f) (_ , FrontPBLimit A B f)
  ∘ fst (UniqueLimit A (ℓim A) (_ , BackPBLimit A B f))
   ≡⟨
      cong (_∘ MapOfDiagrams→MapOfLimits' A B f
                (_ , BackPBLimit A B f) (_ , FrontPBLimit A B f)
             ∘ fst (ℓimIsBackPB A B f))
           (cong fst (UniqueLimitInv B (ℓim B) (_ , FrontPBLimit A B f) ⁻¹))
    ⟩
  fst (invEquiv (UniqueLimit B (ℓim B) (_ , FrontPBLimit A B f)))
  ∘ MapOfDiagrams→MapOfLimits' A B f
      (_ , BackPBLimit A B f) (_ , FrontPBLimit A B f)
  ∘ fst (ℓimIsBackPB A B f)
   ≡⟨
      cong (λ h → fst (invEquiv (ℓimIsFrontPB A B f))
                  ∘ h
                  ∘ fst (ℓimIsBackPB A B f))
           (PullbackMapOfDiagramsToMapOfLimits A B f)
    ⟩
  fst (invEquiv (ℓimIsFrontPB A B f))
  ∘ PullbackOfMaps _ _ (FF1 A B f) (specialCospan A B f)
  ∘ fst (ℓimIsBackPB A B f) ∎
          

postulate
  indexShiftToShiftedBase : (k : ℕ) (A : ℕ-Diagram)
    → MapOfDiagrams (indexShift k A) (KDiagram (fst A k))

  indexShiftToShiftedBaseConnected : (k : ℕ) (A : ℕ-Diagram)
    → isPostnikovTower A
    → (n : ℕ) → isConnectedFun k (fst (indexShiftToShiftedBase k A) n)

  indexShiftLimitMap : (k : ℕ) (A : ℕ-Diagram)
    → fst (fst (snd (ℓim A))) k
     ≡ MapOfDiagrams→MapOfLimits' (indexShift k A) (KDiagram (fst A k))
                                   (indexShiftToShiftedBase k A)
                                   (fst (ℓim A) , Limit-is-indexShiftLimit k A)
                                   (fst A k , KLimit (fst A k))


-- ugly, maybe hard
indexShiftHappy : (k : ℕ) (A : ℕ-Diagram)
  → fst (fst (snd (ℓim A))) k
   ≡ fst (Kℓim (fst A k))
     ∘ MapOfDiagrams→MapOfLimits
       (indexShift k A) (KDiagram (fst A k)) (indexShiftToShiftedBase k A)
     ∘ fst (indexShiftLimit k A)
indexShiftHappy k A =
  indexShiftLimitMap k A
  ∙ MapOfDiagramsEquivOfLimitsCommutes
      (indexShift k A) (KDiagram (fst A k))
      (indexShiftToShiftedBase k A)
      (fst (ℓim A) , Limit-is-indexShiftLimit k A) (ℓim (indexShift k A))
      (ℓim (KDiagram (fst A k))) (fst A k , KLimit (fst A k))

-- some variants of the axiom of choice in ∞-toposes
CC : ℕ → Type (ℓ-suc ℓ-zero)
CC n = (k : ℕ) (A B : ℕ-Family) (f : MapOfFamilies A B)
       → ((m : ℕ) → isConnectedFun (k + n) (f m))
       → isConnectedFun k (MapOfFamilies→MapOfProducts A B f)

postulate
  CC→ConnectedFF1 : (A B : ℕ-Diagram) (f : MapOfDiagrams A B)
    → (n : ℕ) → CC n
    → (k : ℕ) → ((m : ℕ) → isConnectedFun (k + n) ((fst f) m))
    → isConnectedFun k (FF1 A B f)

DC : ℕ → Type (ℓ-suc ℓ-zero)
DC n = (k : ℕ) (A B : ℕ-Diagram) (f : MapOfDiagrams A B)
       → ((m : ℕ) → isConnectedFun (k + n) (fst f m))
       → isConnectedFun k (MapOfDiagrams→MapOfLimits A B f)

DC' : ℕ → Type (ℓ-suc ℓ-zero)
DC' n = (X : Type ℓ-zero) (k : ℕ) (A : X → ℕ-Diagram)
        → ((m : ℕ) → isConnectedFun (k + n) (Diagram-over-index X A n))
        → isConnectedFun k (ℓim-proj-over X A)

postulate
  DC'→DC : (n : ℕ) → (DC' n) → DC n

  DC→DC' : (n : ℕ) → (DC n) → DC' n

postulate
  connectivityArithmetic1 : {A B : Type ℓ-zero} (f : A → B) (k n : ℕ)
    → isConnectedFun (k + (n + 1)) f
    → isConnectedFun (k + 1 + n) f

  connectivityArithmetic2 : {A B : Type ℓ-zero} (f : A → B) (k n : ℕ)
    → isConnectedFun (k + (n + 1)) f
    → isConnectedFun (k + n) f

CC→DC : (n : ℕ) → (CC n) → DC (n + 1)
CC→DC n Ax k A B f fconn =
  transport
  (λ i → isConnectedFun k (MapOfDiagramsIsPullback A B f (~ i)))
  (Connected→ConnectedComp _ _ _
    _
    (fst (invEquiv (ℓimIsFrontPB A B f))) k
    (Connected→ConnectedComp _ _ _
      (fst (ℓimIsBackPB A B f))
      (PullbackOfMaps _ _ (FF1 A B f) (specialCospan A B f))
      k
      (ConnectedEquiv _ _ _ (snd (ℓimIsBackPB A B f)) k)
      (ConnectedPullback _ _ (FF1 A B f) (specialCospan A B f)
        k (CC→ConnectedFF1 A B f n Ax k
                           λ m → connectivityArithmetic2 _ k n (fconn m))
          (Ax k (fst A) (fst B) (fst f)
              λ m → connectivityArithmetic2 _ k n (fconn m))
          (CC→ConnectedFF1 A B f n Ax (k + 1)
                            λ m → connectivityArithmetic1 _ k n (fconn m))))
    (ConnectedEquiv _ _ _ (snd (invEquiv (ℓimIsFrontPB A B f))) k))

PostnikovEffectiveness : Type (ℓ-suc ℓ-zero)
PostnikovEffectiveness =
  (A : ℕ-Diagram) → isPostnikovTower A
  → EquivOfDiagrams (fst (PostnikovTowerOf (fst (ℓim A)))) A

-- postnikov effectiveness is equivalent to this map having an inverse
TowerFamilyMap :
  (A : ℕ-Diagram) → isPostnikovTower A
  → MapOfFamilies (fst (fst (PostnikovTowerOf (fst (ℓim A))))) (fst A)
TowerFamilyMap A p n =
  fst (invEquiv (_ , (TruncUniversal n (fst A n) (fst p n))))
  (fst (fst (snd (ℓim A))) n)

postulate
  TowerFamilyMapNatural : (A : ℕ-Diagram) (p : isPostnikovTower A)
    (n : ℕ) (x : fst (fst (PostnikovTowerOf (fst (ℓim A)))) (1 + n))
    → snd A n (TowerFamilyMap A p (1 + n) x)
     ≡ TowerFamilyMap A p n
       (snd (fst (PostnikovTowerOf (fst (ℓim A)))) n x)
       
TowerOfLimit→Tower :
  (A : ℕ-Diagram) →  isPostnikovTower A
  → MapOfDiagrams (fst (PostnikovTowerOf (fst (ℓim A)))) A
TowerOfLimit→Tower A p =
  (TowerFamilyMap A p) , TowerFamilyMapNatural A p

-- we show that it has an inverse under the assumption that DC holds
postulate
  verySilly : (n k : ℕ) → (k + n) ≡ (n + k)

  ConnectedMap→ConnectedMapTower : (n : ℕ) (X : Type ℓ-zero)
    (A : ℕ-Diagram) (c : ConeℕDiag A X)
    → isPostnikovTower A → (k : ℕ)
    → isConnectedFun n (fst c (k + n))
    → isConnectedFun n (fst c n)

-- here's the trick
DC→ConnectedPostProjHyp' : (k : ℕ) → (DC k)
  → (A : ℕ-Diagram) (p : isPostnikovTower A)
  (n : ℕ) → isConnectedFun n (fst (Kℓim (fst A (k + n)))
     ∘ MapOfDiagrams→MapOfLimits
       (indexShift (k + n) A) (KDiagram (fst A (k + n)))
       (indexShiftToShiftedBase (k + n) A)
     ∘ fst (indexShiftLimit (k + n) A))
DC→ConnectedPostProjHyp' k Ax A p n =
  isConnectedComp (fst (Kℓim (fst A (k + n))))
                  _ n
                  (ConnectedEquiv _ _ _ (snd (Kℓim (fst A (k + n)))) n)
                  (isConnectedComp
                  (MapOfDiagrams→MapOfLimits
                  (indexShift (k + n) A) (KDiagram (fst A (k + n)))
                  (indexShiftToShiftedBase (k + n) A))
                  (fst (indexShiftLimit (k + n) A))
                  n
                  (Ax n
                  (indexShift (k + n) A) (KDiagram (fst A (k + n)))
                      (indexShiftToShiftedBase (k + n) A)
                      (transport
                      (λ i → ((m : ℕ) → isConnectedFun (verySilly n k i)
                                           (fst (indexShiftToShiftedBase
                                                   (k + n) A) m)))
                      (indexShiftToShiftedBaseConnected (k + n) A p)))
                  (ConnectedEquiv _ _ _ (snd (indexShiftLimit (k + n) A)) n))
  
DC→ConnectedPostProjHyp : (k : ℕ) → (DC k)
  → (A : ℕ-Diagram) (p : isPostnikovTower A)
  (n : ℕ) → isConnectedFun n (fst (fst (snd (ℓim A))) (k + n))
DC→ConnectedPostProjHyp k Ax A p n =
  transport (λ i → isConnectedFun n (indexShiftHappy (k + n) A (~ i)))
            (DC→ConnectedPostProjHyp' k Ax A p n)

DC→ConnectedPostProj :
  (k : ℕ) → (DC k) → (A : ℕ-Diagram) (p : isPostnikovTower A)
  → (n : ℕ) → isConnectedFun n (fst (fst (snd (ℓim A))) n)
DC→ConnectedPostProj k Ax A p n =
  ConnectedMap→ConnectedMapTower n (fst (ℓim A)) A (fst (snd (ℓim A)))
                                  p k
                                  (DC→ConnectedPostProjHyp k Ax A p n)

postulate
  ObvsIdentity :
    (A : ℕ-Diagram) (p : isPostnikovTower A)
    → (n : ℕ) → (fst (fst (snd (ℓim A))) n)
                ≡ (fst (TowerOfLimit→Tower A p) n ∘ ∣_∣ₕ)

DC→ConnectedTowerMap :
  (n : ℕ) → (DC n) → (A : ℕ-Diagram) (p : isPostnikovTower A)
  → (m : ℕ) → isConnectedFun m (fst (TowerOfLimit→Tower A p) m)
DC→ConnectedTowerMap n Ax A p m =
  Connected342 (fst (ℓim A)) _ _ m ∣_∣ₕ
               (fst (TowerOfLimit→Tower A p) m)
               (TruncConnected m)
               (transport (λ i → isConnectedFun m (ObvsIdentity A p m i))
               (DC→ConnectedPostProj n Ax A p m))

DC→PosEff : (n : ℕ) → (DC n) → PostnikovEffectiveness
DC→PosEff n Ax A p =
  MapOfDiagrams→EquivOfDiagrams
    (fst (PostnikovTowerOf (fst (ℓim A)))) A (TowerOfLimit→Tower A p)
    λ m → Trunc→Connected→Equiv _ _ m (isOfHLevelTrunc m) ((fst p) m)
                                  (fst (TowerOfLimit→Tower A p) m)
                                  (DC→ConnectedTowerMap n Ax A p m)

-- postnikov completeness follows from countable choice
CC→PosEff : (n : ℕ) → (CC n) → PostnikovEffectiveness
CC→PosEff n Ax = DC→PosEff (n + 1) (CC→DC n Ax)
