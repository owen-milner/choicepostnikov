module DiagramMaps where

open import Cubical.Data.Nat renaming (elim to ℕElim)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Everything
open import Cubical.Functions.FunExtEquiv
open import Cubical.HITs.Truncation
open import Cubical.Homotopy.Connected

open import Limits
open import DiagramSigma
open import PostnikovTowers
open import shiftDiagram
open import EasyLimits

{- This file contains definitions of maps of diagrams and their limits, and
   lemmas about maps out of truncated/shifted diagrams into constant diagrams -}

Lim : (A : ℕ-Diagram) → ℕ-Limit A
Lim A = limitType A , easyLimit A

{- Collects a lot of helper lemmas -}
2+shift : (k n : ℕ) → (1 + k + (1 + n)) ≡ (n + (2 + k))
2+shift k n = cong suc (+-comm k (1 + n)) ∙ cong (2 +_) (+-comm n k)
               ∙ +-comm (2 + k) n 

3+shift : (k n : ℕ) → (3 + k + n) ≡ (1 + k + (2 + n))
3+shift k n = cong (3 +_) (+-comm k n) ∙ cong suc (+-comm (2 + n) k) 

sqtrns : {W X Y Z : Type ℓ-zero}
    (p : Y ≡ Z) (q : X ≡ Y) (f : W → Z) (g : W → X)
    → f ≡ transport p ∘ transport q ∘ g
    → transport (q ⁻¹) ∘ transport (p ⁻¹) ∘ f ≡ g
sqtrns {W = W} {X = X} {Y = Y} {Z = Z} =
  J (λ Z' p → (q : X ≡ Y) (f : W → Z') (g : W → X)
            → f ≡ transport p ∘ transport q ∘ g
            → transport (q ⁻¹) ∘ transport (p ⁻¹) ∘ f ≡ g)
  (J (λ Y' q → (f : W → Y') (g : W → X)
             → f ≡ transport refl ∘ transport q ∘ g
             → transport (q ⁻¹) ∘ transport refl ∘ f ≡ g)
  λ f g H → funExt (λ x → transportRefl _ ∙ transportRefl _
                            ∙ funExt⁻ H x ∙ transportRefl _ ∙ transportRefl _))

2trnsprt : {X Y Z : Type ℓ-zero} (p : X ≡ Y) (q : Y ≡ Z)
    → transport q ∘ transport p ≡ transport (p ∙ q)
2trnsprt {X = X} {Y = Y} {Z = Z} =
  J (λ Y' p → (q : Y' ≡ Z) → transport q ∘ transport p ≡ transport (p ∙ q))
  (J (λ Z' q → transport q ∘ transport refl ≡ transport (refl ∙ q))
  (funExt (λ x → transportRefl _
                ∙ transportRefl _
                ∙ (cong (λ r → transport r x) (lUnit refl ⁻¹)
                ∙ transportRefl x) ⁻¹)))

invtrnsprt : {X Y : Type ℓ-zero} (p : X ≡ Y)
    → transport (p ⁻¹) ∘ transport p ≡ (λ x → x)
invtrnsprt {X = X} {Y = Y} =
  J (λ Y' p → transport (p ⁻¹) ∘ transport p ≡ (λ x → x))
    (funExt (λ x → transportRefl _ ∙ transportRefl _))

invtrnsprt' : {X Y : Type ℓ-zero} (p : X ≡ Y)
    → transport p ∘ transport (p ⁻¹) ≡ (λ x → x)
invtrnsprt' {X = X} {Y = Y} =
  J (λ Y' p → transport p ∘ transport (p ⁻¹) ≡ (λ x → x))
    (funExt (λ x → transportRefl _ ∙ transportRefl _))

tAux : {X Z : Type ℓ-zero} (Y : X → Type ℓ-zero)
  (g : X → X) (f : (x : X) → (Y (g (g x))) → (Y (g x)))
  (h h' : (x : X) (y : Y (g x)) → Z)
  (s s' : (x : X) (y : Y (g x)) → Z)
  (p : h ≡ s) (q : h' ≡ s')
  (r : (x : X) (y : Y (g (g x))) → s (g x) y ≡ s' x (f x y))
  → transport (λ i → (x : X) (y : Y (g (g x)))
                    → p (~ i) (g x) y ≡ q (~ i) x (f x y))
               r
   ≡ (λ x y → (equivFun (invEquiv (funExt₂Equiv)) p) (g x) y
                 ∙ r x y
                 ∙ (equivFun (invEquiv (funExt₂Equiv)) (q ⁻¹)) x (f x y))
tAux {X = X} {Z = Z} Y g f h h' s s' p q r =
  (J (λ v p' → (k t : (x : X) (y : Y (g x)) → Z)
               (q' : k ≡ t)
               (u : (x : X) (y : Y (g (g x))) → v (g x) y ≡ t x (f x y))
     → transport (λ i → (x : X) (y : Y (g (g x)))
                       → p' (~ i) (g x) y ≡ q' (~ i) x (f x y))
                  u
      ≡ (λ x y → (equivFun (invEquiv (funExt₂Equiv)) p') (g x) y
                   ∙ u x y
                   ∙ (equivFun (invEquiv (funExt₂Equiv)) (q' ⁻¹)) x (f x y)))
     (λ k t → J (λ t' q'
               → (u : (x : X) (y : Y (g (g x))) → h (g x) y ≡ t' x (f x y))
               → transport
                (λ i → (x : X) (y : Y (g (g x)))
                     → h (g x) y ≡ q' (~ i) x (f x y)) u
              ≡ (λ x y  → refl ∙ u x y
                      ∙ (equivFun (invEquiv (funExt₂Equiv)) (q' ⁻¹)) x (f x y)))
     λ u → transportRefl u ∙ funExt₂ (λ x y → rUnit (u x y) ∙ lUnit _)) p)
     h' s' q r


trnsprtHmtpy : (X Z : Type ℓ-zero) (Y : X → Type ℓ-zero)
    (g : X → X) (f : (x : X) → (Y (g (g x))) → (Y (g x)))
    (h h' : (x : X) (y : Y (g x)) → Z)
    (s s' : (x : X) (y : Y (g x)) → Z)
    (p : (x : X) (y : Y (g x)) → h x y ≡ s x y)
    (q : (x : X) (y : Y (g x)) → h' x y ≡ s' x y)
    (r : (x : X) (y : Y (g (g x))) → funExt₂ p (~ i0) (g x) y
                                   ≡ funExt₂ q (~ i0) x (f x y))
    → transport
        (λ i → (x : X) (y : Y (g (g x)))
     → ((funExt₂
        (λ n (x : Y (g n)) → p n x)) (~ i)) (g x) y
     ≡ ((funExt₂
       (λ n x → q n x)) (~ i)) x (f x y))
       (λ n x → r n x)
    ≡ λ x y → p (g x) y ⁻¹ ⁻¹ ∙ r x y ∙ q x (f x y) ⁻¹
trnsprtHmtpy X Z Y g f h h' s s' p q r =
  tAux Y g f h h' s s' (funExt₂ p) (funExt₂ q) r


trnsprtHmtpy' : {X Z : Type ℓ-zero} (Y : X → Type ℓ-zero)
    (g : X → X) (f : (x : X) → (Y (g (g x))) → (Y (g x)))
    {h h' : (x : X) (y : Y (g x)) → Z}
    {s s' : (x : X) (y : Y (g x)) → Z}
    (p : (x : X) (y : Y (g x)) → h x y ≡ s x y)
    (q : (x : X) (y : Y (g x)) → h' x y ≡ s' x y)
    (r : (x : X) (y : Y (g (g x))) → h (g x) y
                                   ≡ h' x (f x y))
    → transport
        (λ i → (x : X) (y : Y (g (g x)))
     → ((funExt₂
        (λ n (x : Y (g n)) → p n x)) i) (g x) y
     ≡ ((funExt₂
       (λ n x → q n x)) i) x (f x y))
       (λ n x → r n x)
    ≡ λ x y → p (g x) y ⁻¹ ∙ r x y ∙ q x (f x y)
trnsprtHmtpy' Y g f p q r = tAux Y g f _ _ _ _ (funExt₂ p ⁻¹) (funExt₂ q ⁻¹) r
                    

transpReflMaybe : (X : Type ℓ-zero) (x : X)
  → PathP (λ i → (transportRefl x i) ≡ x)
           (λ j → transp (λ i → X) j x)
           (refl {x = x})
transpReflMaybe X x i j = transp (λ _ → X) (i ∨ j) x

iso-∙ : {X : Type ℓ-zero} {a b c : X} (p : a ≡ b)
            → isIso (λ (q : b ≡ c) → p ∙ q)
fst (iso-∙ p) = λ q → p ⁻¹ ∙ q
fst (snd (iso-∙ p)) q = assoc p (p ⁻¹) q ∙ cong (_∙ q) (rCancel p) ∙ lUnit q ⁻¹
snd (snd (iso-∙ p)) q = assoc (p ⁻¹) p q ∙ cong (_∙ q) (lCancel p) ∙ lUnit q ⁻¹


equiv-∙ : {X : Type ℓ-zero} {a b c : X} (p : a ≡ b)
            → isEquiv (λ (q : b ≡ c) → p ∙ q)
equiv-∙ p = isoToIsEquiv (isIso→Iso (λ q → p ∙ q) (iso-∙ p))
 

connectedΣFun-aux2 : (A B : Type ℓ-zero) (C : A → Type ℓ-zero)
  (D : B → Type ℓ-zero) (f : A → B) (g : (a : A) → C a → D (f a))
  → (b : B) (d : D b)
  → Iso ((Σ (Σ A C)
       (λ a →
          Σ-syntax (f (fst a) ≡ b)
          (λ p → PathP (λ i → D (p i)) (g (fst a) (snd a)) d))))
        (Σ[ x ∈ (Σ[ y ∈ A ] f y ≡ b) ]
          (Σ[ y ∈ C (fst x) ] (PathP (λ i → D ((snd x) i)))
                                         (g (fst x) y) d))
Iso.fun (connectedΣFun-aux2 A B C D f g b d) ((a , c) , (p , q)) =
  (a , p) , (c , q)
Iso.inv (connectedΣFun-aux2 A B C D f g b d) ((a , p) , (c , q)) =
  (a , c) , (p , q)
Iso.rightInv (connectedΣFun-aux2 A B C D f g b d) qd =
  refl
Iso.leftInv (connectedΣFun-aux2 A B C D f g b d) qd = refl

connectedΣFun-aux1 : (A B : Type ℓ-zero) (C : A → Type ℓ-zero)
  (D : B → Type ℓ-zero) (f : A → B) (g : (a : A) → C a → D (f a))
  → (b : B) (d : D b)
  → Iso (fiber (λ x → f (fst x) , g (fst x) (snd x)) (b , d))
     (Σ[ x ∈ (Σ[ y ∈ A ] f y ≡ b) ]
       (Σ[ y ∈ C (fst x) ] (transport (λ i → D ((snd x) i)))
                                          (g (fst x) y) ≡ d))
connectedΣFun-aux1 A B C D f g b d =
  compIso (Σ-cong-iso-snd (λ x → invIso ΣPathIsoPathΣ))
          (compIso (connectedΣFun-aux2 A B C D f g b d)
                   (Σ-cong-iso-snd
                    (λ x → Σ-cong-iso-snd λ y
                         → PathPIsoPath (λ i → D ((snd x) i))
                                         (g (fst x) y) d)))
{- end of the collection of helper lemmas -}



{- maps of families and maps of diagrams, products of maps of families and
   products of maps of diagrams -}
mapFams : (A : ℕ-Family) (B : ℕ-Family) → Type ℓ-zero
mapFams A B = (n : ℕ) → A n → B n

mapFams→prodMap :
  (A : ℕ-Family) (B : ℕ-Family) (PA PB : Type ℓ-zero)
  (cA : fCone A PA) (cB : fCone B PB)
  (PA' : isProdCone A PA cA) (PB' : isProdCone B PB cB)
  → mapFams A B → PA → PB
mapFams→prodMap A B PA PB cA cB PA' PB' f =
  fCone→map B PB PA cB PB' (λ n → f n ∘ cA n)

is-mapDiag : (A : ℕ-Family) (a : isDiagram A) (B : ℕ-Family) (b : isDiagram B)
  → mapFams A B → Type ℓ-zero
is-mapDiag A a B b f = (n : ℕ) (x : A (1 + n))
                    → b n (f (1 + n) x) ≡ f n (a n x)

is-mapDiag' : (A : ℕ-Family) (a : isDiagram A) (B : ℕ-Family) (b : isDiagram B)
  (PA PB : Type ℓ-zero) (cA : fCone A PA) (cB : fCone B PB)
  (PA' : isProdCone A PA cA) (PB' : isProdCone B PB cB)
  → mapFams A B → Type ℓ-zero
is-mapDiag' A a B b PA PB cA cB PA' PB' f =
  sMap B b PB cB PB'
  ∘ mapFams→prodMap A B PA PB cA cB PA' PB' f
  ≡ mapFams→prodMap A B PA PB cA cB PA' PB' f
  ∘ sMap A a PA cA PA'

MapOfFamilies : ℕ-Family → ℕ-Family → Type ℓ-zero
MapOfFamilies A B = mapFams A B

MapOfDiagrams : ℕ-Diagram → ℕ-Diagram → Type ℓ-zero
MapOfDiagrams A B = Σ[ f ∈ MapOfFamilies (fst A) (fst B) ]
                     (is-mapDiag (fst A) (snd A) (fst B) (snd B) f)



MapOfFamilies→fCone→fCone : (A B : ℕ-Family) (X : Type ℓ-zero)
  → MapOfFamilies A B → ConeℕFam A X → ConeℕFam B X
MapOfFamilies→fCone→fCone A B X f c =
  λ n x → f n (c n x)

MapOfDiagrams→dCone→dCone : (A B : ℕ-Diagram) (X : Type ℓ-zero)
  → MapOfDiagrams A B → ConeℕDiag A X → ConeℕDiag B X
MapOfDiagrams→dCone→dCone (A , a) (B , b) X (f , hf) (c , hc) =
  ( MapOfFamilies→fCone→fCone A B X f c)
  , λ n x → hf n (c (1 + n) x) ∙ cong (f n) (hc n x)

MapOfFamilies→MapOfProds :
  (A B : ℕ-Family) (X : ℕ-Product A) (Y : ℕ-Product B)
  → MapOfFamilies A B → (fst X) → (fst Y)
MapOfFamilies→MapOfProds A B (X , c , PX) (Y , c' , PY) f =
  fCone→map B Y X c' PY (MapOfFamilies→fCone→fCone A B X f c)


{- equivalences of diagrams -}
isEquivMap : (A B : ℕ-Family) (a : isDiagram A) (b : isDiagram B)
  (f : MapOfDiagrams (A , a) (B , b)) → Type ℓ-zero
isEquivMap A B a b f = (n : ℕ) → isEquiv ((fst f) n)

EquivOfDiagrams : (A B : ℕ-Diagram) → Type ℓ-zero
EquivOfDiagrams (A , a) (B , b) =
  Σ[ f ∈ MapOfDiagrams (A , a) (B , b) ] (isEquivMap A B a b f)

MapOfDiagrams→EquivOfDiagrams : (A B : ℕ-Diagram) (f : MapOfDiagrams A B)
  → ((n : ℕ) → isEquiv ((fst f) n))
  → EquivOfDiagrams A B
MapOfDiagrams→EquivOfDiagrams A B f p = f , p

MapOfDiagrams→MapOfLimits' :
  (A B : ℕ-Diagram) (f : MapOfDiagrams A B)
                    (X : ℕ-Limit A) (Y : ℕ-Limit B)
                 → (fst X) → (fst Y)
MapOfDiagrams→MapOfLimits' A (B , b) f X (Y , cY , eY) =
  dCone→map B b Y (fst X) cY eY
    (MapOfDiagrams→dCone→dCone A (B , b) (fst X) f (fst (snd X)))

{- distinguished limit of maps of diagrams -}
MapOfDiagrams→MapOfLimits :
  (A B : ℕ-Diagram) (f : MapOfDiagrams A B)
  → fst (ℓim A) → fst (ℓim B)
MapOfDiagrams→MapOfLimits A B f =
  MapOfDiagrams→MapOfLimits' A B f (ℓim A) (ℓim B)


{- Limit of a diagram is also limit of the truncation/shifting of that
   diagram -}
obvsLimit'' : (A : ℕ-Diagram) (k : ℕ)
    → is-ℕ-Limit-of (indexShiftDiag' k A) (limitType A)
obvsLimit'' A zero = easyLimit A
obvsLimit'' A (suc zero) = coneEquiv→LimMap A (indexShiftDiag' 1  A)
  (indexShiftOfOneConeEq A , indexShiftOfOneNat A) (limitType A) (easyLimit A)
obvsLimit'' A (suc (suc k)) =
  coneEquiv→LimMap (indexShiftDiag' (1 + k) A) (indexShiftDiag' (2 + k) A)
  (indexShiftOfOneConeEq (indexShiftDiag' (1 + k) A)
  , indexShiftOfOneNat (indexShiftDiag' (1 + k) A))
  (limitType A) (obvsLimit'' A (suc k))

obvsLimitChar : (A : ℕ-Diagram) (k n : ℕ)
  → fst (fst (obvsLimit'' A (2 + k))) n
   ≡ fst (fst (obvsLimit'' A (1 + k))) (1 + n)
obvsLimitChar A zero n = refl
obvsLimitChar A (suc k) n = refl


obvsLimit' : (A : ℕ-Diagram) (k : ℕ) (L : ℕ-Limit A)
    → is-ℕ-Limit-of (indexShiftDiag' k A) (fst L)
obvsLimit' A k L =
  transport
    (λ i → is-ℕ-Limit-of (indexShiftDiag' k A)
                          (fst (UniqueLimitPath A
                                  (limitType A , easyLimit A) L i)))
    (obvsLimit'' A k) 

obvsLimit : (A : ℕ-Diagram) (k : ℕ)
   → is-ℕ-Limit-of (indexShiftDiag' k A) (fst (ℓim A))
obvsLimit A k = obvsLimit' A k (ℓim A)

indexShiftOneMap : (A : ℕ-Diagram) → mapFams (fst (indexShiftOfOne A)) (fst A)
indexShiftOneMap A n = snd A n


{- map from a shifted-by-one diagram to a constant diagram on the first
   object -}
oneShiftDiag→kDiag1FamMap : (A : ℕ-Diagram)
  → mapFams (fst (indexShiftOfOne A)) (fst (KDiagram (fst A 1)))
oneShiftDiag→kDiag1FamMap A zero x = x
oneShiftDiag→kDiag1FamMap A (suc n) x =
  oneShiftDiag→kDiag1FamMap A n (snd A (1 + n) x)

oneShiftDiag→kDiagFamMapConnHyp : (A : ℕ-Diagram) (k : ℕ) →
  ((n : ℕ) → isConnectedFun n (snd A n)) →
  ((n : ℕ) → isConnectedFun (1 + k + n) (snd (indexShiftDiag' (1 + k) A) n))
oneShiftDiag→kDiagFamMapConnHyp A zero p n = p (1 + n)
oneShiftDiag→kDiagFamMapConnHyp A (suc zero) p n = p (2 + n)
oneShiftDiag→kDiagFamMapConnHyp A (suc (suc k)) p n =
  transport (λ i → isConnectedFun (3+shift k n (~ i))
                     (snd (indexShiftDiag' (suc k) A) (2 + n)))
            (oneShiftDiag→kDiagFamMapConnHyp A k p (2 + n))

{- all components of that map of diagrams are connected when the diagram is
   Postnikov -}
oneShiftDiag→kDiagFamMapConn' : (A : ℕ-Diagram) (k : ℕ)
  → (p : isPostnikovTower A)
  → (n : ℕ) → isConnectedFun 1 (oneShiftDiag→kDiag1FamMap A n)
oneShiftDiag→kDiagFamMapConn' A k p zero =
  isEquiv→isConnected (λ x → x) (snd (idEquiv _)) 1
oneShiftDiag→kDiagFamMapConn' A k p (suc n) =
  isConnectedComp (oneShiftDiag→kDiag1FamMap A n) (snd A (1 + n)) 1
    (oneShiftDiag→kDiagFamMapConn' A k p n)
    (isConnectedFunSubtr 1 n (snd A (1 + n))
    (transport (λ i → isConnectedFun (+-comm 1 n i) (snd A (1 + n)))
               (snd p (1 + n))))

oneShiftDiag→kDiagFamMapConn : (A : ℕ-Diagram) (k : ℕ)
  → ((n : ℕ) → isConnectedFun (1 + k + n) (snd A n))
  → (n : ℕ) → isConnectedFun (2 + k) (oneShiftDiag→kDiag1FamMap A n)
oneShiftDiag→kDiagFamMapConn A k p zero =
  isEquiv→isConnected (λ x → x) (snd (idEquiv _)) (2 + k)
oneShiftDiag→kDiagFamMapConn A k p (suc n) =
  isConnectedComp (oneShiftDiag→kDiag1FamMap A n) (snd A (1 + n))
    (2 + k) (oneShiftDiag→kDiagFamMapConn A k p n)
    (isConnectedFunSubtr (2 + k) n (snd A (1 + n))
    (transport (λ i → isConnectedFun (2+shift k n i) (snd A (1 + n)))
               (p (1 + n))))

oneShiftDiag→kDiag1FamMapDMap : (A : ℕ-Diagram)
  → MapOfDiagrams (indexShiftOfOne A) (KDiagram (fst A 1))
fst (oneShiftDiag→kDiag1FamMapDMap A) = oneShiftDiag→kDiag1FamMap A
snd (oneShiftDiag→kDiag1FamMapDMap A) n x = refl


{- the shifted diagram is what we expect -}
pathNewShift : (A : ℕ-Diagram) (k n : ℕ)
  → (fst (indexShiftDiag' k A) n) ≡ fst A (k + n)
pathNewShift A zero n = refl
pathNewShift A (suc zero) n = refl
pathNewShift A (suc (suc k)) n = pathNewShift A (suc k) (suc n)
                               ∙ cong (λ m → fst A (suc m))
                                       (+-suc k n)

pathNewShiftPath : (A : ℕ-Diagram) (k : ℕ)
  → pathNewShift A (2 + k) 0
  ≡ pathNewShift A (1 + k) 1 ∙ (cong (fst A) (+-comm 1 (1 + k)) ⁻¹)
                             ∙ cong (fst A) (+-comm 0 (2 + k))
pathNewShiftPath A k =
  pathNewShift A (2 + k) 0 ≡⟨ refl ⟩
  pathNewShift A (1 + k) 1 ∙ cong (fst A) (cong suc (+-suc k 0))
  ≡⟨ cong (λ q → pathNewShift A (1 + k) 1 ∙ cong (fst A) q)
          (isSetℕ (suc (k + suc 0)) (suc (suc (k + 0)))
             (cong suc (+-suc k 0))
             (+-comm 1 (1 + k) ⁻¹ ∙ +-comm 0 (2 + k))) ⟩
  pathNewShift A (1 + k) 1 ∙ cong (fst A) (+-comm 1 (1 + k) ⁻¹
                                         ∙ +-comm 0 (2 + k))
  ≡⟨ cong (pathNewShift A (1 + k) 1 ∙_)
          (cong-∙ (fst A) (+-comm 1 (1 + k) ⁻¹) (+-comm 0 (2 + k))) ⟩
  pathNewShift A (1 + k) 1 ∙ (cong (fst A) (+-comm 1 (1 + k)) ⁻¹)
                           ∙ (cong (fst A) (+-comm 0 (2 + k))) ∎ 

pathNewShiftPath' : (A : ℕ-Diagram) (k n : ℕ)
    → pathNewShift A (2 + k) n
       ∙ cong (fst A) (+-comm (2 + k) n)
    ≡ (pathNewShift A (1 + k) (1 + n)
      ∙ cong (fst A) (+-comm (1 + k) (1 + n)))
      ∙ cong (fst A) (cong suc (+-comm n (suc k))
                       ∙ +-comm (suc (suc k)) n)
pathNewShiftPath' A k n =
  pathNewShift A (2 + k) n
  ∙ cong (fst A) (+-comm (2 + k) n) ≡⟨ assoc _ _ _ ⁻¹ ⟩
  pathNewShift A (1 + k) (1 + n)
  ∙ cong (fst A) (cong suc (+-suc k n))
  ∙ cong (fst A) (+-comm (2 + k) n)
    ≡⟨ cong (pathNewShift A (1 + k) (1 + n) ∙_)
            ((cong-∙ (fst A) (cong suc (+-suc k n)) (+-comm (2 + k) n)) ⁻¹) ⟩
  pathNewShift A (1 + k) (1 + n)
  ∙ cong (fst A) (cong suc (+-suc k n) ∙ (+-comm (2 + k) n))
    ≡⟨ cong (λ q → pathNewShift A (1 + k) (1 + n) ∙ cong (fst A) q)
            (isSetℕ (1 + k + (1 + n)) (n + (2 + k))
                    (cong suc (+-suc k n) ∙ (+-comm (2 + k) n))
                    (+-comm (1 + k) (1 + n)
                    ∙ cong suc (+-comm n (suc k))
                    ∙ +-comm (2 + k) n)) ⟩
  pathNewShift A (1 + k) (1 + n)
  ∙ cong (fst A) (+-comm (1 + k) (1 + n)
                  ∙ cong suc (+-comm n (suc k))
                  ∙ +-comm (2 + k) n)
    ≡⟨ cong (pathNewShift A (1 + k) (1 + n) ∙_)
            (cong-∙ (fst A) (+-comm (1 + k) (1 + n))
                           (cong suc (+-comm n (suc k))
                            ∙ +-comm (suc (suc k)) n))
       ∙ assoc _ _ _ ⟩
  (pathNewShift A (1 + k) (1 + n)
  ∙ cong (fst A) (+-comm (1 + k) (1 + n)))
  ∙ cong (fst A) (cong suc (+-comm n (suc k))
                  ∙ +-comm (suc (suc k)) n) ∎

{- map to constant diagram for an arbitrary index -}
newShiftDiag→kDiagFamMap : (A : ℕ-Diagram) (k : ℕ)
  → mapFams (fst (indexShiftDiag' k A)) (fst (KDiagram (fst A k)))
newShiftDiag→kDiagFamMap A zero zero = λ x → x
newShiftDiag→kDiagFamMap A zero (suc n) x =
  newShiftDiag→kDiagFamMap A zero n (snd A n x)
newShiftDiag→kDiagFamMap A (suc zero) =
  oneShiftDiag→kDiag1FamMap A
newShiftDiag→kDiagFamMap A (suc (suc k)) n x =
  transport (λ i → fst A (+-comm 1 (1 + k) (~ i)))
  (transport (λ i → pathNewShift A (1 + k) 1 i)
  (oneShiftDiag→kDiag1FamMap (indexShiftDiag' (1 + k) A) n x))


newShiftDiag→kDiag : (A : ℕ-Diagram) (k : ℕ)
  → MapOfDiagrams (indexShiftDiag' k A) (KDiagram (fst A k))
fst (newShiftDiag→kDiag A k) = newShiftDiag→kDiagFamMap A k
snd (newShiftDiag→kDiag A zero) n x = refl
snd (newShiftDiag→kDiag A (suc zero)) n x = refl
snd (newShiftDiag→kDiag A (suc (suc k))) n x = refl


transportingDiagMap :  (k : ℕ) (A : ℕ-Diagram) (X : Type ℓ-zero)
                       (p : fst A (2 + k) ≡ X)
  → MapOfDiagrams (indexShiftDiag' (2 + k) A) (KDiagram X)
fst (transportingDiagMap k A X p) n =
  transport p ∘ (fst (newShiftDiag→kDiag A (2 + k)) n)
snd (transportingDiagMap k A X p) n x =
  refl {x = transport p ((fst (newShiftDiag→kDiag A (2 + k)) n)
                        (snd (indexShiftDiag' (1 + k) A) (1 + n) x))}

transportingDiagMap' :  (k : ℕ) (A : ℕ-Diagram)
  → MapOfDiagrams (indexShiftDiag' (2 + k) A) (KDiagram (fst A ((2 + k) + 0)))
fst (transportingDiagMap' k A) n =
  transport (λ i → fst A (+-comm 0 (2 + k) i))
  ∘ fst (newShiftDiag→kDiag A (2 + k)) n
snd (transportingDiagMap' k A) n x = refl
                 
transportingDiagMapPath : (k : ℕ) (A : ℕ-Diagram) (X : Type ℓ-zero)
                          (p : fst A (2 + k) ≡ X)
   → transport (λ i → MapOfDiagrams
                          (indexShiftDiag' (2 + k) A)
                          (KDiagram (p i)))
          (newShiftDiag→kDiag A (2 + k))
    ≡ transportingDiagMap k A X p
transportingDiagMapPath k A X =
  J (λ Y p → transport (λ i → MapOfDiagrams
                                 (indexShiftDiag' (2 + k) A)
                                 (KDiagram (p i)))
                       (newShiftDiag→kDiag A (2 + k))
           ≡ transportingDiagMap k A Y p)
    (transportRefl (newShiftDiag→kDiag A (2 + k))
    ∙ ΣPathP
      (((funExt₂
      (λ n x → transportRefl (newShiftDiag→kDiagFamMap A (2 + k) n x))) ⁻¹)
      , toPathP
        ((transport
        (λ i → (n : ℕ) (x : fst (indexShiftDiag' (1 + k) A) (2 + n))
             →
      (funExt₂
      (λ n (x : fst (indexShiftDiag' (suc k) A) (1 + n))
      → transportRefl (newShiftDiag→kDiagFamMap A (2 + k) n x)) (~ i))
      (1 + n) x ≡ (funExt₂
      (λ n (x : fst (indexShiftDiag' (suc k) A) (1 + n))
      → transportRefl (newShiftDiag→kDiagFamMap A (2 + k) n x)) (~ i))
      n (snd (indexShiftDiag' (1 + k) A) (1 + n) x))
      (λ n (x : fst (indexShiftDiag' (suc k) A) (2 + n))
      → (refl {x = fst (newShiftDiag→kDiag A (2 + k)) n
                   (snd (indexShiftDiag' (1 + k) A) (1 + n) x)})))
                     ≡⟨ trnsprtHmtpy ℕ (fst A (2 + k))
                     (λ n → fst (indexShiftDiag' (suc k) A) n)
              suc (λ n → snd (indexShiftDiag' (suc k) A) (1 + n))
              (λ n → transport refl ∘ newShiftDiag→kDiagFamMap A (2 + k) n)
              (λ n → transport refl ∘ newShiftDiag→kDiagFamMap A (2 + k) n)
              (λ n → newShiftDiag→kDiagFamMap A (2 + k) n)
              (λ n → newShiftDiag→kDiagFamMap A (2 + k) n)
              (λ n x → transportRefl (newShiftDiag→kDiagFamMap A (2 + k) n x))
              (λ n x → transportRefl (newShiftDiag→kDiagFamMap A (2 + k) n x))
              (λ n (x : fst (indexShiftDiag' (suc k) A) (2 + n))
               → refl {x = fst (newShiftDiag→kDiag A (2 + k)) n
                            (snd (indexShiftDiag' (1 + k) A) (1 + n) x)}) ⟩
      funExt₂ (λ n x
      → transportRefl (newShiftDiag→kDiagFamMap A (2 + k) (1 + n) x) ⁻¹ ⁻¹
         ∙ refl {x = fst (newShiftDiag→kDiag A (2 + k)) n
                     (snd (indexShiftDiag' (1 + k) A) (1 + n) x)}
         ∙ transportRefl (newShiftDiag→kDiagFamMap A (2 + k) n
                          (snd (indexShiftDiag' (1 + k) A) (1 + n) x)) ⁻¹
                     ≡⟨ cong (_∙ refl
                                 {x = fst (newShiftDiag→kDiag A (2 + k))
                                      n (snd (indexShiftDiag' (1 + k) A)
                                        (1 + n) x)}
                                 ∙ transportRefl
                                   (newShiftDiag→kDiagFamMap A (2 + k) n
                                    (snd (indexShiftDiag' (1 + k) A)
                                     (1 + n) x)) ⁻¹)
                             (symInvo _)
                         ∙ cong (transportRefl
                         (newShiftDiag→kDiagFamMap A (2 + k) (1 + n) x) ∙_)
                          (lUnit _ ⁻¹) ∙ rCancel _ ⟩
     refl ∎))))
