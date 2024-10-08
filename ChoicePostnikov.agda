module ChoicePostnikov where

open import Cubical.Data.Nat renaming (elim to ℕElim)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Everything
open import Cubical.HITs.Truncation
open import Cubical.Homotopy.Connected

open import DiagramSigma
open import PostnikovTowers
open import Limits
open import DiagramMaps
open import ProjIsDiagramMap
open import EasyLimits
open import EasyLimMaps

{- Contains definitions of countable choice, dependent choice and Postnikov
   effectiveness and a proof that countable choice implies Postnikov
   effectiveness -}

{- Two variants of the axiom of choice in ∞-topoi -}
CC : ℕ → Type (ℓ-suc ℓ-zero)
CC n = (k : ℕ) (A B : ℕ-Family) (f : MapOfFamilies A B)
       → ((m : ℕ) → isConnectedFun (k + n) (f m))
       → isConnectedFun k (MapOfFamilies→MapOfProds A B (Π A) (Π B) f)

DC : ℕ → Type (ℓ-suc ℓ-zero)
DC n = (k : ℕ) (A B : ℕ-Diagram) (f : MapOfDiagrams A B)
       → ((m : ℕ) → isConnectedFun (k + n) (fst f m))
       → isConnectedFun k (MapOfDiagrams→MapOfLimits A B f)


{- Postnikov effectiveness says that any Postnikov tower is the canonical
   Postnikov tower of its limit -}
PostnikovEffectiveness : Type (ℓ-suc ℓ-zero)
PostnikovEffectiveness =
  (A : ℕ-Diagram) → isPostnikovTower A
  → EquivOfDiagrams (fst (PostnikovTowerOf (fst (ℓim A)))) (A)
       


{- Some helper lemmas -}
private
  equivInj' : (A B : Type ℓ-zero) (f : A → B) → isEquiv f
      → ((a a' : A) → f a ≡ f a' → a ≡ a')
  equivInj' A B f e a a' p =
    a
      ≡⟨ Iso.leftInv (equivToIso (f , e)) a ⁻¹ ⟩
    (equivFun (invEquiv (f , e))) (f a)
      ≡⟨ cong (equivFun (invEquiv (f , e))) p ⟩
    (equivFun (invEquiv (f , e))) (f a')
      ≡⟨ Iso.leftInv (equivToIso (f , e)) a' ⟩
    a' ∎

  connectivityTransport : {A B : Type ℓ-zero} (f : A → B) (m n : ℕ)
    (p : m ≡ n) → isConnectedFun m f → isConnectedFun n f
  connectivityTransport f m n p hf =
    transport (λ i → isConnectedFun (p i) f) hf

  connectivityArithmetic : {A B : Type ℓ-zero} (f : A → B) (k n : ℕ)
    → isConnectedFun (k + (n + 1)) f
    → isConnectedFun (1 + (k + n)) f
  connectivityArithmetic f k n =
    connectivityTransport f (k + (n + 1)) (1 + (k + n))
      (cong (k +_) (+-comm n 1)
      ∙ +-assoc k 1 n
      ∙ cong (_+ n) (+-comm k 1))

  shift+1 : (n m k : ℕ) → (1 + (k + (m + n)))
                         ≡ (k + (1 + (m + n)))
  shift+1 n m k = +-assoc 1 k (m + n) ∙ cong (_+ (m + n)) (+-comm 1 k)
                                       ∙ (+-assoc k 1 (m + n)) ⁻¹



{- "countable choice" for degree n implies "dependent choice" for degree n+1 -}
CC→DC : (n : ℕ) → (CC n) → DC (n + 1)
CC→DC n CCn k A B f hf =
  transport
  (λ i → isConnectedFun k (MapOfDiagrams→MapOfLimits' A B f
                            (UniqueLimitPath A (limitType A , easyLimit A)
                                               (ℓim A) i)
                            (UniqueLimitPath B (limitType B , easyLimit B)
                                               (ℓim B) i)))
  (connectivityLemma A B f k
   (transport (λ i → isConnectedFun (suc k)
                      (MapOfFamilies→MapOfProds (fst A) (fst B)
                      (UniqueProductPath (fst A) (Π (fst A))
                      (((n : ℕ) → fst A n) , easyProduct (fst A)) i)
                      (UniqueProductPath (fst B) (Π (fst B))
                      (((n : ℕ) → fst B n) , easyProduct (fst B)) i)
                      (fst f)))
   (CCn (1 + k) (fst A) (fst B) (fst f)
        λ m → connectivityArithmetic (fst f m) k n (hf m))))

TowerFamilyMap :
  (A : ℕ-Diagram) → isPostnikovTower A
  → MapOfFamilies (fst (fst (PostnikovTowerOf (fst (ℓim A))))) (fst A)
TowerFamilyMap A p n =
  fst (invEquiv (_ , (TruncUniversal n (fst A n) (fst p n))))
  (fst (fst (snd (ℓim A))) n)

{- dependent choice (and hence countable choice) imply that "TowerFamilyMap"
   has an inverse, hence they imply Postnikov convergence -} 

{- some useful facts about "TowerFamilyMap" -}
private

  {- It was defined using the universal property of the truncation -}
  ObvsIdentity :
      (A : ℕ-Diagram) (p : isPostnikovTower A)
      → (n : ℕ) → (fst (fst (snd (ℓim A))) n)
                  ≡ (TowerFamilyMap A p n ∘ ∣_∣ₕ)
  ObvsIdentity (A , a) p n =
    (secEq (_ , (TruncUniversal n (A n) (fst p n)))
           (fst (fst (snd (ℓim (A , a)))) n)) ⁻¹

  {- It is natural (identity of functions) -}
  TowerFamilyMapNatural' : (A : ℕ-Diagram) (p : isPostnikovTower A)
    (n : ℕ) → (snd A n) ∘ (TowerFamilyMap A p (1 + n))
             ≡ (TowerFamilyMap A p n)
               ∘ (snd (fst (PostnikovTowerOf (fst (ℓim A)))) n)
  TowerFamilyMapNatural' (A , a) (p1 , p2) n =
    equivInj' (∥ (fst (ℓim (A , a))) ∥ (1 + n) → (A n))
             (fst (ℓim (A , a)) → (A n))
             (λ f → f ∘ ∣_∣ₕ)
             (TruncUniversal (1 + n) (A n) (isOfHLevelPlus 1 (p1 n)))
             ((a n) ∘ (TowerFamilyMap (A , a) (p1 , p2) (1 + n)))
             ((TowerFamilyMap (A , a) (p1 , p2) n)
             ∘ (snd (fst (PostnikovTowerOf (fst (ℓim (A , a))))) n))
             (cong (a n ∘_) ((ObvsIdentity (A , a) (p1 , p2) (1 + n)) ⁻¹)
             ∙ funExt (λ x → snd (fst (snd (ℓim (A , a)))) n x)
             ∙ ObvsIdentity (A , a) (p1 , p2) n
             ∙ cong (TowerFamilyMap (A , a) (p1 , p2) n ∘_)
                    ((TruncMapObvsIdentity n) ⁻¹))

  {- It is natural (homotopy of functions) -}
  TowerFamilyMapNatural : (A : ℕ-Diagram) (p : isPostnikovTower A)
      (n : ℕ) (x : fst (fst (PostnikovTowerOf (fst (ℓim A)))) (1 + n))
      → snd A n (TowerFamilyMap A p (1 + n) x)
       ≡ TowerFamilyMap A p n
         (snd (fst (PostnikovTowerOf (fst (ℓim A)))) n x)
  TowerFamilyMapNatural (A , a) (p1 , p2) n x =
    funExt⁻ (TowerFamilyMapNatural' (A , a) (p1 , p2) n) x


{- The map defined above is in fact a morphism of diagrams/a natural
   transformation -}
TowerOfLimit→Tower :
  (A : ℕ-Diagram) →  isPostnikovTower A
  → MapOfDiagrams (fst (PostnikovTowerOf (fst (ℓim A)))) A
TowerOfLimit→Tower A p =
  (TowerFamilyMap A p) , TowerFamilyMapNatural A p

ConnectedMap→ConnectedMapTower : (n m : ℕ) (X : Type ℓ-zero)
  (A : ℕ-Diagram) (c : ConeℕDiag A X)
  → isPostnikovTower A → (k : ℕ)
  → isConnectedFun n (fst c (k + (m + n)))
  → isConnectedFun n (fst c (m + n))
ConnectedMap→ConnectedMapTower n m X A c pA zero connc = connc
ConnectedMap→ConnectedMapTower n m X A c pA (suc k) connc =
  transport
    (λ i → isConnectedFun n ((funExt (snd c (m + n))) i))
    (isConnectedComp (snd A (m + n)) (fst c ((1 + m) + n)) n
                     (isConnectedFunSubtr n m (snd A (m + n)) (snd pA (m + n)))
                     (ConnectedMap→ConnectedMapTower n (1 + m) X A c pA k
                        (transport
                          (λ i → isConnectedFun n (fst c (shift+1 n m k i)))
                          connc)))


{- If A is a Postnikov tower, dependent choice in degree k implies that the
   projection map (Lim A) ---> A (n + k) is n-connected, since that map is
   (essentially) the limit of the maps in the tower -} 
DC→ConnectedPostShiftProj : (k : ℕ) → (DC k)
  → (A : ℕ-Diagram) (p : isPostnikovTower A) (n : ℕ)
  → isConnectedFun n (fst (fst (snd (Lim (indexShiftDiag' (k + n) A)))) 0)
DC→ConnectedPostShiftProj k hyp A p n =
  transport (λ i → isConnectedFun n
                     (newShiftDiagMapIs A (k + n) (~ i)))
            (isConnectedComp (transport (λ i → pathNewShift A (k + n) 0 (~ i))
                             ∘ transport (λ i → fst A (+-comm 0 (k + n) i)))
               (MapOfDiagrams→MapOfLimits' (indexShiftDiag' (k + n) A)
               (KDiagram (fst A (k + n)))
               (newShiftDiag→kDiag A (k + n))
               (Lim (indexShiftDiag' (k + n) A))
               (fst A (k + n) , KLimit (fst A (k + n))))
               n (isConnectedComp (transport (pathNewShift A (k + n) 0 ⁻¹))
                  (transport (cong (fst A) (+-comm 0 (k + n)))) n
                  (isEquiv→isConnected
                   (transport (pathNewShift A (k + n) 0 ⁻¹))
                   (isEquivTransport (pathNewShift A (k + n) 0 ⁻¹)) n)
                  (isEquiv→isConnected
                   (transport (cong (fst A) (+-comm 0 (k + n))))
                   (isEquivTransport (cong (fst A) (+-comm 0 (k + n)))) n))
               (transport
               (λ i → isConnectedFun n
               (MapOfDiagrams→MapOfLimits' (indexShiftDiag' (k + n) A)
               (KDiagram (fst A (k + n))) (newShiftDiag→kDiag A (k + n))
               (UniqueLimitPath (indexShiftDiag' (k + n) A)
                (Lim (indexShiftDiag' (k + n) A))
                (ℓim (indexShiftDiag' (k + n) A)) (~ i))
               (UniqueLimitPath (KDiagram (fst A (k + n)))
                (fst A (k + n) , KLimit (fst A (k + n)))
                (ℓim (KDiagram (fst A (k + n)))) (~ i))))
               (hyp n (indexShiftDiag' (k + n) A) (KDiagram (fst A (k + n)))
                  (newShiftDiag→kDiag A (k + n))
                  (transport (λ i → (m : ℕ)
                                  → isConnectedFun (+-comm k n i)
                                     (newShiftDiag→kDiagFamMap A (k + n) m))
                  (newShiftDiag→kDiagFamMapConn A p (k + n))))))

DC→ConnectedPostProjHypAux : (k : ℕ) → (DC k)
  → (A : ℕ-Diagram) (p : isPostnikovTower A)
  (n : ℕ) → isConnectedFun n (fst (fst (snd (Lim A))) (k + n))
DC→ConnectedPostProjHypAux k Ax A p n =
  transport (λ i → isConnectedFun n (projectionsAgree (k + n) A (~ i)))
            (isConnectedComp
             (transport (λ i → fst A (+-comm (k + n) 0 i))
             ∘ transport (λ i → pathNewShift A (k + n) 0 i))
             (fst (fst (snd (Lim (indexShiftDiag' (k + n) A)))) 0
             ∘ equivFun (UniqueLimit (indexShiftDiag' (k + n) A)
                        (limitType A , obvsLimit'' A (k + n))
                        (Lim (indexShiftDiag' (k + n) A)))) n
             (isConnectedComp
               (transport (cong (fst A) (+-comm (k + n) 0)))
               (transport (pathNewShift A (k + n) 0))
               n (isEquiv→isConnected
                  (transport (cong (fst A) (+-comm (k + n) 0)))
                  (isEquivTransport (cong (fst A) (+-comm (k + n) 0))) n)
                  (isEquiv→isConnected
                    (transport (pathNewShift A (k + n) 0))
                    (isEquivTransport (pathNewShift A (k + n) 0)) n))
             (isConnectedComp
              (fst (fst (snd (Lim (indexShiftDiag' (k + n) A)))) 0)
              (equivFun (UniqueLimit (indexShiftDiag' (k + n) A)
                        (limitType A , obvsLimit'' A (k + n))
                        (Lim (indexShiftDiag' (k + n) A)))) n
              (DC→ConnectedPostShiftProj k Ax A p n)
              (isEquiv→isConnected
               (equivFun (UniqueLimit (indexShiftDiag' (k + n) A)
                          (limitType A , obvsLimit'' A (k + n))
                          (Lim (indexShiftDiag' (k + n) A))))
               (equivIsEquiv (UniqueLimit (indexShiftDiag' (k + n) A)
                               (limitType A , obvsLimit'' A (k + n))
                               (Lim (indexShiftDiag' (k + n) A)))) n)))
  
DC→ConnectedPostProjHyp : (k : ℕ) → (DC k)
  → (A : ℕ-Diagram) (p : isPostnikovTower A)
  (n : ℕ) → isConnectedFun n (fst (fst (snd (ℓim A))) (k + n))
DC→ConnectedPostProjHyp k Ax A p n =
  transport (λ i → isConnectedFun n
                     (fst (fst (snd (UniqueLimitPath A (Lim A) (ℓim A) i)))
                     (k + n)))
            (DC→ConnectedPostProjHypAux k Ax A p n) 

{- But now using the "ConnectedMapTower" lemma from before, every projection
   is connected -}
DC→ConnectedPostProj :
  (k : ℕ) → (DC k) → (A : ℕ-Diagram) (p : isPostnikovTower A)
  → (n : ℕ) → isConnectedFun n (fst (fst (snd (ℓim A))) n)
DC→ConnectedPostProj k Ax A p n =
  ConnectedMap→ConnectedMapTower n 0 (fst (ℓim A)) A (fst (snd (ℓim A)))
     p k (DC→ConnectedPostProjHyp k Ax A p n)

{- Now, because the "TowerFamilyMap" from above factors the projection,
   it's connected -}
DC→ConnectedTowerMap :
  (n : ℕ) → (DC n) → (A : ℕ-Diagram) (p : isPostnikovTower A)
  → (m : ℕ) → isConnectedFun m (fst (TowerOfLimit→Tower A p) m)
DC→ConnectedTowerMap n Ax A p m =
  Connected342 (fst (ℓim A)) _ _ m ∣_∣ₕ
               (fst (TowerOfLimit→Tower A p) m)
               (TruncConnected m)
               (transport (λ i → isConnectedFun m (ObvsIdentity A p m i))
               (DC→ConnectedPostProj n Ax A p m))

{- So, because the objects in the tower are truncated, "TowerFamilyMap" is an
   equivalence of diagrams -}
DC→PosEff : (n : ℕ) → (DC n) → PostnikovEffectiveness
DC→PosEff n Ax A p =
  MapOfDiagrams→EquivOfDiagrams
    (fst (PostnikovTowerOf (fst (ℓim A)))) A (TowerOfLimit→Tower A p)
    λ m → Trunc→Connected→Equiv _ _ m (isOfHLevelTrunc m) ((fst p) m)
                                  (fst (TowerOfLimit→Tower A p) m)
                                  (DC→ConnectedTowerMap n Ax A p m)

{- So, Postnikov effectiveness follows from countable choice -}
CC→PosEff : (n : ℕ) → (CC n) → PostnikovEffectiveness
CC→PosEff n Ax = DC→PosEff (n + 1) (CC→DC n Ax)


{- This is independent of the choice of product -}
module _ (P* : (A : ℕ-Family) → ℕ-Product A) where

  CC* : ℕ → Type (ℓ-suc ℓ-zero)
  CC* n = (k : ℕ) (A B : ℕ-Family) (f : MapOfFamilies A B)
       → ((m : ℕ) → isConnectedFun (k + n) (f m))
       → isConnectedFun k (MapOfFamilies→MapOfProds A B (P* A) (P* B) f)

  CC*≃CC : (n : ℕ) → CC* n ≡ CC n
  CC*≃CC n i = (k : ℕ) (A B : ℕ-Family) (f : MapOfFamilies A B)
       → ((m : ℕ) → isConnectedFun (k + n) (f m))
       → isConnectedFun k (MapOfFamilies→MapOfProds A B
                            (UniqueProductPath A (P* A) (Π A) i)
                            (UniqueProductPath B (P* B) (Π B) i) f)

  CC*→PosEff : (n : ℕ) → (CC* n) → PostnikovEffectiveness
  CC*→PosEff = transport
                (λ i → (n : ℕ) → (CC*≃CC n (~ i)) → PostnikovEffectiveness)
                (CC→PosEff)



