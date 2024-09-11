{-# OPTIONS --lossy-unification #-}
module Limits where

open import Cubical.Data.Nat renaming (elim to ℕElim)
open import Cubical.Data.Sigma
open import Cubical.Foundations.Everything
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Functions.FunExtEquiv

{- contains definitions of families, diagrams, limits and products -}


{- helper lemmas -}
comm1 : {X Y : Type ℓ-zero} (F : Type ℓ-zero → Type ℓ-zero)
  (f : (X : Type ℓ-zero) → F X → F X)
  (p : (X : Type ℓ-zero) → (f X) ≡ (λ x → x))
  (h : {X Y : Type ℓ-zero} → (f : Y → X) → F X → F Y)
  (g : Y → X) (x : F X)
  → cong (f _) (cong (h g) (λ i → (p _) i x)) ⁻¹
   ∙ (λ i → (p _) i (h g (f _ (x))))
   ∙ cong (h g) (λ i → (p _) i x)
   ≡ (λ i → (p _) i (h g x))
comm1 {X = X} {Y = Y} F f p =
  J (λ f' q
  → (h : {X Y : Type ℓ-zero} → (f : Y → X) → F X → F Y)
     (g : Y → X) (x : F X)
   → cong (f' _) (cong (h g) (λ i → q (~ i) _ x)) ⁻¹
      ∙ (λ i → q (~ i) _ (h g (f' _ x)))
      ∙ cong (h g) (λ i → q (~ i) _ x)
    ≡ (λ i → q (~ i) _ (h g x)))
  (λ h g x → cong (refl ∙_) (lUnit _ ⁻¹)
              ∙ lUnit _ ⁻¹)
  (funExt p ⁻¹)

comm2 : {X Y : Type ℓ-zero} (F : Type ℓ-zero → Type ℓ-zero)
  (f : (X : Type ℓ-zero) → F X → F X)
  (p : (X : Type ℓ-zero) → (f X) ≡ (λ x → x))
  (h : {X Y : Type ℓ-zero} → (f : Y → X) → F X → F Y)
  (g : Y → X) (x : F X)
  → (λ i → p _ i (h g x)) ⁻¹
   ∙ cong (f _) (cong (h g) (λ i → p _ i x)) ⁻¹
   ∙ (λ i → p _ i ((h g) (f _ x)))
   ≡ cong (h g) (λ i → p _ i x) ⁻¹
comm2 {X = X} {Y = Y} F f p =
  J
  (λ f' p'
  → (h : {X Y : Type ℓ-zero} → (f : Y → X) → F X → F Y)
  (g : Y → X) (x : F X)
  → (λ i → p' (~ i) _ (h g x)) ⁻¹
   ∙ cong (f' _) (cong (h g) (λ i → p' (~ i) _ x)) ⁻¹
   ∙ (λ i → p' (~ i) _ ((h g) (f' _ x)))
   ≡ cong (h g) (λ i → p' (~ i) _ x) ⁻¹)
  (λ h g x → lUnit _ ⁻¹ ∙ lUnit _ ⁻¹)
  (funExt p ⁻¹)

transportHomotopyFuncHom : {X : Type ℓ-zero}
  {S : X → X}
  {R : X → X}
  (pR : R ≡ (λ x → x))
  (f : {x : X} → S x ≡ x → S (R x) ≡ (R x))
  {x : X}
  (r : S x ≡ x)
  → transport (λ i → S ((pR i) x) ≡ (pR i) x) (f r)
   ≡ cong S (λ i → (pR (~ i) x)) ∙ (f r) ∙ (λ i → (pR i) x)
transportHomotopyFuncHom {X = X} {S = S} pR =
  J
  (λ R p → (f : {x : X} → S x ≡ x → S (R x) ≡ (R x))
            {x : X} (r : S x ≡ x)
         → transport (λ i → S ((p (~ i)) x) ≡ ((p (~ i)) x)) (f r)
         ≡ cong S (λ i → (p i x)) ∙ (f r) ∙ (λ i → (p (~ i)) x))
  (λ f r → transportRefl _ ∙ rUnit _ ∙ lUnit _)
  (pR ⁻¹)

transportHomotopyFuncHom' : {X Y : Type ℓ-zero}
  {SY : Y → Y}
  {SX : X → X}
  {R T : X → Y}
  (pR : R ≡ T)
  (f : {x : X} → SX x ≡ x → SY (R x) ≡ R x)
  {x : X}
  (r : SX x ≡ x)
  → transport (λ i → SY ((pR i) x) ≡ (pR i) x) (f r)
   ≡ cong SY (λ i → (pR (~ i) x)) ∙ (f r) ∙ (λ i → (pR i) x)
transportHomotopyFuncHom' {X = X} {Y = Y} {SY = SY} {SX = SX} {R = R} pR =
  J (λ T p → (f : {x : X} → SX x ≡ x → SY (R x) ≡ R x)
              {x : X} (r : SX x ≡ x)
           → transport (λ i → SY ((p i) x) ≡ (p i) x) (f r)
            ≡ cong SY (λ i → (p (~ i) x)) ∙ (f r) ∙ (λ i → (p i) x))
    (λ f r → transportRefl _ ∙ rUnit _ ∙ lUnit _) pR
{- end of helper lemmas -}     

{- definition of a family of objects used throughout the project -}
ℕ-Family : Type (ℓ-suc ℓ-zero)
ℕ-Family = ℕ → Type ℓ-zero

fCone : ℕ-Family → Type ℓ-zero → Type ℓ-zero
fCone A X = (n : ℕ) → X → A n

fCone→map→fCone : (A : ℕ-Family) (X Y : Type ℓ-zero)
  → fCone A X → (Y → X) → fCone A Y
fCone→map→fCone A X Y c f = λ n → (c n) ∘ f

{- one definition of the property of being a product -}
isProdCone : (A : ℕ-Family) (X : Type ℓ-zero)
  → fCone A X → Type (ℓ-suc ℓ-zero)
isProdCone A X c = (Y : Type ℓ-zero) → isEquiv (fCone→map→fCone A X Y c)

fCone→map : (A : ℕ-Family) (X Y : Type ℓ-zero) (c : fCone A X)
  → isProdCone A X c → (fCone A Y) → (Y → X)
fCone→map A X Y c L = fst (invEquiv (_ , L Y))


{- lemmas for reasoning about products -}
fCone-map-sec : (A : ℕ-Family) (X Y : Type ℓ-zero) (c : fCone A X)
  (PX : isProdCone A X c) (c' : fCone A Y)
  → (λ n → (c n) ∘ (fCone→map A X Y c PX c')) ≡ c'
fCone-map-sec A X Y c PX c' = secEq (_ , PX Y) c'

fCone-map-sec' : (A : ℕ-Family) (X Y : Type ℓ-zero) (c : fCone A X)
  (PX : isProdCone A X c) (c' : fCone A Y) (n : ℕ) (y : Y)
  → c n (fCone→map A X Y c PX c' y) ≡ c' n y
fCone-map-sec' A X Y c PX c' n =
  funExt⁻ (funExt⁻ (fCone-map-sec A X Y c PX c') n)

fCone-map-ret : (A : ℕ-Family) (X Y : Type ℓ-zero) (c : fCone A X)
  (PX : isProdCone A X c) (f : Y → X)
  → fCone→map A X Y c PX (λ n → (c n) ∘ f) ≡ f
fCone-map-ret A X Y c PX f = retEq (_ , PX Y) f

map→fCone-cong-equiv : (A : ℕ-Family) (X Y : Type ℓ-zero) (c : fCone A X)
  (PX : isProdCone A X c) (f g : Y → X) →
  ((λ (n : ℕ) → (c n) ∘ f) ≡ (λ n → (c n) ∘ g)) ≃ (f ≡ g)
map→fCone-cong-equiv A X Y c PX f g = invEquiv (congEquiv (_ , PX Y))

map-fCone-cong-equiv' : (A : ℕ-Family) (X Y : Type ℓ-zero) (c : fCone A X)
  (PX : isProdCone A X c) (f g : Y → X) →
  ((n : ℕ) (y : Y) → c n (f y) ≡ c n (g y))
  ≃ ((y : Y) → f y ≡ g y)
map-fCone-cong-equiv' A X Y c PX f g =
  (funExt₂Equiv ∙ₑ map→fCone-cong-equiv A X Y c PX f g) ∙ₑ invEquiv funExtEquiv

fCone-map-comp : (A : ℕ-Family) (X Y Z : Type ℓ-zero) (c : fCone A X)
  (PX : isProdCone A X c) (c' : fCone A Y) (f : Z → Y)
  → (λ (n : ℕ) → (c n) ∘ ((fCone→map A X Y c PX c') ∘ f))
   ≡ (λ n → (c' n) ∘ f)
fCone-map-comp A X Y Z c PX c' f =
  cong (λ (k : fCone A Y) → (λ (n : ℕ) → k n ∘ f))
       (fCone-map-sec A X Y c PX c')

fCone-map-comp* : (A : ℕ-Family) (X Y Z : Type ℓ-zero) (c : fCone A X)
  (PX : isProdCone A X c) (c' : fCone A Y) (f : Z → Y)
  → fCone→map A X Y c PX c' ∘ f ≡ fCone→map A X Z c PX (λ n → c' n ∘ f)
fCone-map-comp* A X Y Z c PX c' f =
  (fCone-map-ret A X Z c PX (fCone→map A X Y c PX c' ∘ f)) ⁻¹
  ∙ (cong (fCone→map A X Z c PX) (fCone-map-comp A X Y Z c PX c' f))
  

map-fCone-comp : (A : ℕ-Family) (X Y Z : Type ℓ-zero) (c : fCone A X)
  (PX : isProdCone A X c) (c' : fCone A Y) (f : Z → Y)
  → (fCone→map A X Y c PX c') ∘ f ≡ fCone→map A X Z c PX (λ n → (c' n) ∘ f)
map-fCone-comp A X Y Z c PX c' f =
  (fCone-map-ret A X Z c PX (fCone→map A X Y c PX c' ∘ f)) ⁻¹
  ∙ (cong (fCone→map A X Z c PX) (fCone-map-comp A X Y Z c PX c' f))

map-fCone-comp-nat : (A : ℕ-Family) (X Y Z : Type ℓ-zero) (c : fCone A X)
  (PX : isProdCone A X c) (c' c'' : fCone A Y) (f : Z → Y)
  (p : c' ≡ c'')
  → cong (fCone→map A X Z c PX)
          (cong (λ k → (λ (n : ℕ) → k n ∘ f)) p)
   ∙ map-fCone-comp A X Y Z c PX c'' f ⁻¹
   ≡ map-fCone-comp A X Y Z c PX c' f ⁻¹
   ∙ cong (_∘ f) (cong (fCone→map A X Y c PX) p)
map-fCone-comp-nat A X Y Z c PX c' c'' f =
  J (λ z p → cong (fCone→map A X Z c PX)
                   (cong (λ k → (λ (n : ℕ) → k n ∘ f)) p)
              ∙ map-fCone-comp A X Y Z c PX z f ⁻¹
            ≡ map-fCone-comp A X Y Z c PX c' f ⁻¹
              ∙ cong (_∘ f) (cong (fCone→map A X Y c PX) p))
     (lUnit _ ⁻¹ ∙ rUnit _)

map-fCone-comp' : (A : ℕ-Family) (B : ℕ-Family)
  (W X Y Z : Type ℓ-zero) (c : fCone A W)
  (PW : isProdCone A W c) (c' : fCone B X) (PX : isProdCone B X c')
  (c'' : fCone B Y) (f : Z → Y)
  (η : (n : ℕ) → B n → A n)
  → fCone→map A W X c PW (λ n → η n ∘ c' n)
     ∘ fCone→map B X Z c' PX (λ n → c'' n ∘ f)
  ≡ fCone→map A W Z c PW (λ n → η n ∘ c'' n ∘ f)
map-fCone-comp' A B W X Y Z c PW c' PX c'' f η =
  map-fCone-comp A W X Z c PW (λ n → η n ∘ c' n)
                 (fCone→map B X Z c' PX (λ n → c'' n ∘ f))
  ∙ cong (λ (k : fCone B Z) → fCone→map A W Z c PW (λ n → η n ∘ k n))
     (fCone-map-sec B X Z c' PX (λ n → c'' n ∘ f))

fCone-map-comp' : (A : ℕ-Family) (X Y Z : Type ℓ-zero) (c : fCone A X)
  (PX : isProdCone A X c) (c' : fCone A Y) (f : Z → Y)
  → (n : ℕ) (z : Z) → c n (fCone→map A X Y c PX c' (f z))
                      ≡ c' n (f z)
fCone-map-comp' A X Y Z c PX c' f n z =
  funExt⁻ (funExt⁻ (fCone-map-comp A X Y Z c PX c' f) n) z

map-fCone-comp* : (A : ℕ-Family) (X Y Z : Type ℓ-zero) (c : fCone A X)
  (f : Y → X) (g : Z → Y)
  → fCone→map→fCone A X Z c (f ∘ g)
     ≡ (λ n → fCone→map→fCone A X Y c f n ∘ g)
map-fCone-comp* A X Y Z c f g = refl

{- definition of the property of being a family that is an ℕ-indexed diagram -}
isDiagram : ℕ-Family → Type ℓ-zero
isDiagram A = (n : ℕ) → A (1 + n) → A n

is-dCone : {X : Type ℓ-zero} (A : ℕ-Family) → isDiagram A
  → fCone A X → Type ℓ-zero
is-dCone {X = X} A a c = (n : ℕ) (x : X) → a n (c (1 + n) x) ≡ c n x

is-dCone→map→is-dCone : (A : ℕ-Family) (a : isDiagram A) (X Y : Type ℓ-zero)
  (c : fCone A X) → is-dCone A a c → (f : (Y → X))
  → is-dCone A a (fCone→map→fCone A X Y c f)
is-dCone→map→is-dCone A a X Y c h f = λ n y → h n (f y)


{- one defintion of cones over a diagram -}
dCone : (A : ℕ-Family) (a : isDiagram A)
  → Type ℓ-zero → Type ℓ-zero
dCone A a X = Σ[ c ∈ fCone A X ] is-dCone A a c

dCone→map→dCone : (A : ℕ-Family) (a : isDiagram A) (X Y : Type ℓ-zero)
  (c : dCone A a X) → (Y → X) → dCone A a Y
dCone→map→dCone A a X Y (c , h) f =
  (fCone→map→fCone A X Y c f) , is-dCone→map→is-dCone A a X Y c h f

isLimitCone : (A : ℕ-Family) (a : isDiagram A) (X : Type ℓ-zero)
  → dCone A a X → Type (ℓ-suc ℓ-zero)
isLimitCone A a X c = (Y : Type ℓ-zero) → isEquiv (dCone→map→dCone A a X Y c)

dCone→map : (A : ℕ-Family) (a : isDiagram A) (X Y : Type ℓ-zero)
  (c : dCone A a X) → isLimitCone A a X c → dCone A a Y → (Y → X)
dCone→map A a X Y c L = fst (invEquiv (_ , L Y))

{- transforming cones over a family whose objects form a diagram -}
sCone : (A : ℕ-Family) (a : isDiagram A) (X : Type ℓ-zero)
  → fCone A X → fCone A X
sCone A a X c = λ n → a n ∘ c (1 + n)

sMap : (A : ℕ-Family) (a : isDiagram A) (X : Type ℓ-zero) (c : fCone A X)
  → isProdCone A X c → X → X
sMap A a X c P = fCone→map A X X c P (sCone A a X c)

sMap-comp-path : (A : ℕ-Family) (a : isDiagram A) (X Y Z : Type ℓ-zero)
  (c : fCone A X) (PX : isProdCone A X c) (c' : fCone A Y) (c'' : fCone A Y)
  (p : sCone A a Y c' ≡ c'') (g : Z → Y)
  → cong (λ (k : fCone A Y) → fCone→map A X Z c PX (λ n → k n ∘ g)) p
     ≡ map-fCone-comp A X Y Z c PX (sCone A a Y c') g ⁻¹
       ∙ cong (λ (k : fCone A Y) → fCone→map A X Y c PX k ∘ g) p
       ∙ map-fCone-comp A X Y Z c PX c'' g
sMap-comp-path A a X Y Z c PX c' c'' p =
  J (λ k q → (g : Z → Y) →
     cong (λ (k : fCone A Y) → fCone→map A X Z c PX (λ n → k n ∘ g)) q
     ≡ map-fCone-comp A X Y Z c PX (sCone A a Y c') g ⁻¹
       ∙ cong (λ (k : fCone A Y) → fCone→map A X Y c PX k ∘ g) q
       ∙ map-fCone-comp A X Y Z c PX k g)
    (λ g → (cong (map-fCone-comp A X Y Z c PX (sCone A a Y c') g ⁻¹ ∙_)
                  (lUnit _ ⁻¹)
            ∙ lCancel _) ⁻¹) p

sMap-comp-path* : (A : ℕ-Family) (a : isDiagram A) (X Y Z : Type ℓ-zero)
  (c : fCone A X) (PX : isProdCone A X c) (c' : fCone A Y) (c'' : fCone A Y)
  (g : Z → Y) (h : Z → Y) (p : g ≡ h)
  → cong (λ (g : Z → Y) →
           fCone→map A X Z c PX (λ n → c' n ∘ g)) p
     ≡ map-fCone-comp A X Y Z c PX c' g ⁻¹
       ∙ cong (fCone→map A X Y c PX c' ∘_) p
       ∙ map-fCone-comp A X Y Z c PX c' h
sMap-comp-path* A a X Y Z c PX c' c'' g h p =
  J (λ h' p' → cong (λ (g : Z → Y) →
                      fCone→map A X Z c PX (λ n → c' n ∘ g)) p'
              ≡ map-fCone-comp A X Y Z c PX c' g ⁻¹
              ∙ cong (fCone→map A X Y c PX c' ∘_) p'
              ∙ map-fCone-comp A X Y Z c PX c' h')
    ((cong (map-fCone-comp A X Y Z c PX c' g ⁻¹ ∙_) (lUnit _ ⁻¹)
    ∙ lCancel _) ⁻¹) p

corr-to-sMap-comp-path* : (A : ℕ-Family) (a : isDiagram A)
  (X Y Z : Type ℓ-zero)
  (c : fCone A X) (PX : isProdCone A X c) (c' : fCone A Y) (c'' : fCone A Y)
  (g : Z → Y) (h : Z → Y) (p : g ≡ h)
  → map-fCone-comp A X Y Z c PX c' g 
   ∙ cong (λ (g : Z → Y) →
           fCone→map A X Z c PX (λ n → c' n ∘ g)) p
     ≡ cong (fCone→map A X Y c PX c' ∘_) p
       ∙ map-fCone-comp A X Y Z c PX c' h
corr-to-sMap-comp-path* A a X Y Z c PX c' c'' g h =
  J (λ f p → map-fCone-comp A X Y Z c PX c' g
              ∙ cong
                (λ (g : Z → Y) → fCone→map A X Z c PX (λ n → c' n ∘ g))
                p
            ≡ cong (fCone→map A X Y c PX c' ∘_) p
              ∙ map-fCone-comp A X Y Z c PX c' f)
     (rUnit _ ⁻¹ ∙ lUnit _)

{- alternative definition of a cone over a diagram -}
is-dCone' : {X : Type ℓ-zero} (A : ℕ-Family) (a : isDiagram A)
  → fCone A X → Type ℓ-zero
is-dCone' {X = X} A a c = sCone A a X c ≡ c

dCone' : (A : ℕ-Family) (a : isDiagram A)
  → Type ℓ-zero → Type ℓ-zero
dCone' A a X = Σ[ c ∈ fCone A X ] is-dCone' A a c

is-dCone≅is-dCone' : (A : ℕ-Family) (a : isDiagram A) (X : Type ℓ-zero)
  (c : fCone A X) → Iso (is-dCone A a c) (is-dCone' A a c)
Iso.fun (is-dCone≅is-dCone' A a X c) h = funExt (λ n → funExt (h n))
Iso.inv (is-dCone≅is-dCone' A a X c) h = λ n x → cong (λ t → t n x) h
Iso.rightInv (is-dCone≅is-dCone' A a X c) h = refl
Iso.leftInv (is-dCone≅is-dCone' A a X c) h = refl

dCone≅dCone' : (A : ℕ-Family) (a : isDiagram A) (X : Type ℓ-zero)
  → Iso (dCone A a X) (dCone' A a X)
dCone≅dCone' A a X = Σ-cong-iso-snd (is-dCone≅is-dCone' A a X)

is-dCone≃is-dCone' : (A : ℕ-Family) (a : isDiagram A) (X : Type ℓ-zero)
  (c : fCone A X) → is-dCone A a c ≃ is-dCone' A a c
is-dCone≃is-dCone' A a X c = isoToEquiv (is-dCone≅is-dCone' A a X c)

dCone≃dCone' : (A : ℕ-Family) (a : isDiagram A) (X : Type ℓ-zero)
  → dCone A a X ≃ dCone' A a X
dCone≃dCone' A a X = Σ-cong-equiv-snd (is-dCone≃is-dCone' A a X)

is-dCone'→map→is-dCone' : (A : ℕ-Family) (a : isDiagram A) (X Y : Type ℓ-zero)
  (c : fCone A X) → is-dCone' A a c
  → (f : Y → X) → is-dCone' A a (fCone→map→fCone A X Y c f)
is-dCone'→map→is-dCone' A a X Y c h f =
  cong (λ (c' : fCone A X) → (λ n → c' n ∘ f)) h

dCone'→map→dCone' : (A : ℕ-Family) (a : isDiagram A) (X Y : Type ℓ-zero)
  → dCone' A a X → (Y → X) → dCone' A a Y
dCone'→map→dCone' A a X Y (c , h) f =
  fCone→map→fCone A X Y c f , is-dCone'→map→is-dCone' A a X Y c h f

module dConeIsoNatural (A : ℕ-Family) (a : isDiagram A)
                       (X : Type ℓ-zero) (Y : Type ℓ-zero)
                       (f : Y → X) where

  dConeIsoIsNatural : (d : dCone A a X)
    → dCone'→map→dCone' A a X Y (Iso.fun (dCone≅dCone' A a X) d) f
     ≡ Iso.fun (dCone≅dCone' A a Y) (dCone→map→dCone A a X Y d f)
  dConeIsoIsNatural d = refl
  
isLimitCone' : (A : ℕ-Family) (a : isDiagram A) (X : Type ℓ-zero)
  → dCone' A a X → Type (ℓ-suc ℓ-zero)
isLimitCone' A a X c =
  (Y : Type ℓ-zero) → isEquiv (dCone'→map→dCone' A a X Y c)

dCone'→map : (A : ℕ-Family) (a : isDiagram A) (X Y : Type ℓ-zero)
  (c : dCone' A a X) → isLimitCone' A a X c → dCone' A a Y → (Y → X)
dCone'→map A a X Y c L = fst (invEquiv (_ , L Y))
