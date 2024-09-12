module ProjIsDiagramMap where

open import Cubical.Data.Nat renaming (elim to ℕElim)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Everything
open import Cubical.Functions.FunExtEquiv
open import Cubical.HITs.Truncation
open import Cubical.Homotopy.Connected

open import DiagramSigma
open import PostnikovTowers
open import EasyLimits
open import DiagramMaps

{- Messy proofs in this file, a bottleneck for type-checking -}

{- Contains useful lemmas about projections, especially key is the lemma
   given in three parts at the end of the file: projections are essentially
   certain limits of morphisms of diagrams -}


{- There is a morphism from a truncated/shifted diagram to the constant diagram
   on it's first term, and if the original diagram was Postnikov, the
   components of this morphism are connected.

   Combined with the lemma at the end of the file, this is important for the
   proof that dependent choice implies Postnikov convergence -}
newShiftDiag→kDiagFamMapConn : (A : ℕ-Diagram) (p : isPostnikovTower A)
  (k : ℕ)
  → (n : ℕ) → isConnectedFun k (newShiftDiag→kDiagFamMap A k n)
newShiftDiag→kDiagFamMapConn A p zero zero =
  ConnectedEquiv (fst (KDiagram (fst A zero)) zero)
                 (fst (KDiagram (fst A zero)) zero)
                 (λ x → x) (snd (idEquiv _)) zero
newShiftDiag→kDiagFamMapConn A p zero (suc n) =
  isConnectedComp (newShiftDiag→kDiagFamMap A 0 n) (snd A n) zero
    (newShiftDiag→kDiagFamMapConn A p zero n)
    (isConnectedFunSubtr 0 n (snd A n)
       (transport (λ i → isConnectedFun (+-comm 0 n i) (snd A n))
         (snd p n)))
newShiftDiag→kDiagFamMapConn A p (suc zero) n =
  oneShiftDiag→kDiagFamMapConn' A n p n
newShiftDiag→kDiagFamMapConn A p (suc (suc k)) n =
  isConnectedComp
  (transport (λ i → fst A (+-comm 1 (1 + k) (~ i)))
  ∘ transport (λ i → pathNewShift A (1 + k) 1 i))
  ((oneShiftDiag→kDiag1FamMap (indexShiftDiag' (1 + k) A) n)) (2 + k)
  (isEquiv→isConnected
     (transport (λ i → fst A (+-comm 1 (1 + k) (~ i)))
     ∘ transport (λ i → pathNewShift A (1 + k) 1 i))
     (equivIsEquiv
        (compEquiv (transport (λ i → pathNewShift A (1 + k) 1 i)
                    , isEquivTransport (pathNewShift A (1 + k) 1))
                   (transport (λ i → fst A (+-comm 1 (1 + k) (~ i))) ,
                   isEquivTransport (cong (fst A) (+-comm 1 (1 + k) ⁻¹)))))
         (suc (suc k)))
  (oneShiftDiag→kDiagFamMapConn (indexShiftDiag' (1 + k) A) k
    (oneShiftDiag→kDiagFamMapConnHyp A k (snd p)) n)


{- Useful lemmas about commuting transports and projections and transports
   and the "MapOfDiagrams→MapOfLimits" functor -}
private
  projTranspNat : (A : ℕ-Diagram) (m n : ℕ) (p : m ≡ n)
      → transport (λ i → fst A (p i)) ∘
           fst (fst (easyLimit A)) m
       ≡ fst (fst (easyLimit A)) n
  projTranspNat A m n =
    J
    (λ n' p → transport (cong (fst A) p) ∘ fst (fst (easyLimit A)) m
            ≡ fst (fst (easyLimit A)) n')
    (funExt (λ x → transportRefl _))  


  mapOfDiagsTranspNat : (k : ℕ) (A : ℕ-Diagram) (X : Type ℓ-zero)
    (p : fst A (2 + k) ≡ X)
    → transport p
       ∘ MapOfDiagrams→MapOfLimits' (indexShiftDiag' (2 + k) A)
          (KDiagram (fst A (2 + k))) (newShiftDiag→kDiag A (2 + k))
          (Lim (indexShiftDiag' (2 + k) A))
          (fst A (2 + k) , KLimit (fst A (2 + k)))
     ≡ MapOfDiagrams→MapOfLimits' (indexShiftDiag' (2 + k) A)
          (KDiagram X)
          (transport (λ i → MapOfDiagrams
                            (indexShiftDiag' (2 + k) A)
                            (KDiagram (p i)))
            (newShiftDiag→kDiag A (2 + k)))
          (Lim (indexShiftDiag' (2 + k) A))
          (X , KLimit X)
  mapOfDiagsTranspNat k A X = J
    (λ Y p → transport p
            ∘ MapOfDiagrams→MapOfLimits' (indexShiftDiag' (2 + k) A)
              (KDiagram (fst A (2 + k))) (newShiftDiag→kDiag A (2 + k))
              (Lim (indexShiftDiag' (2 + k) A))
              (fst A (2 + k) , KLimit (fst A (2 + k)))
          ≡ MapOfDiagrams→MapOfLimits' (indexShiftDiag' (2 + k) A)
            (KDiagram Y)
            (transport (λ i → MapOfDiagrams
                               (indexShiftDiag' (2 + k) A)
                               (KDiagram (p i)))
                       (newShiftDiag→kDiag A (2 + k)))
            (Lim (indexShiftDiag' (2 + k) A))
            (Y , KLimit Y))
     (funExt (λ _ → transportRefl _)
      ∙ cong (λ (m : MapOfDiagrams (indexShiftDiag' (2 + k) A)
                                  (KDiagram (fst A (2 + k))))
                     → MapOfDiagrams→MapOfLimits'
                       (indexShiftDiag' (2 + k) A)
                       (KDiagram (fst A (2 + k))) (m)
                       (Lim (indexShiftDiag' (2 + k) A))
                       ((fst A (2 + k)) , KLimit (fst A (2 + k))))
    (transportRefl (newShiftDiag→kDiag A (2 + k))) ⁻¹)


{- The following two helpful (but ugly) pieces of path algebra will be used to
   simplify the construction of some other paths later on -}
private
  transportingDiagMapAux' : (k : ℕ) (A : ℕ-Diagram) (n : ℕ)
    (x : fst (indexShiftDiag' (1 + k) A) (1 + n))
    → (transport (λ i → (cong (fst A) (+-comm 0 (2 + k))
                          ∙ pathNewShift A (2 + k) 0 ⁻¹) i)
               (transport (λ i → fst A (+-comm 1 (1 + k) (~ i)))
               (transport (λ i → pathNewShift A (1 + k) 1 i)
               (oneShiftDiag→kDiag1FamMap (indexShiftDiag' (1 + k) A) n x))))
    ≡ oneShiftDiag→kDiag1FamMap (indexShiftDiag' (1 + k) A) n x
  transportingDiagMapAux' k A = (λ n x →
                funExt⁻ (2trnsprt (cong (fst A) (+-comm 0 (2 + k)))
                                  (pathNewShift A (2 + k) 0 ⁻¹) ⁻¹)
                (transport (λ i → fst A (+-comm 1 (1 + k) (~ i)))
                (transport (λ i → pathNewShift A (1 + k) 1 i)
                (oneShiftDiag→kDiag1FamMap (indexShiftDiag' (1 + k) A) n x)))
            ∙  funExt⁻
                 (cong (λ r → transport (λ i → r (~ i)))
                       (pathNewShiftPath A k))
                 (transport (λ i → (cong (fst A) (+-comm 0 (2 + k)) i))
                 (transport (λ i → fst A (+-comm 1 (1 + k) (~ i)))
                 (transport (λ i → pathNewShift A (1 + k) 1 i)
                 (oneShiftDiag→kDiag1FamMap (indexShiftDiag' (1 + k) A) n x))))
                ∙ funExt⁻
                  (cong transport (symDistr (pathNewShift A (1 + k) 1)
                     (cong (fst A) (+-comm 1 (1 + k)) ⁻¹
                     ∙ cong (fst A) (+-comm 0 (2 + k))))
                  ∙ (2trnsprt
                       ((cong (fst A) (+-comm 1 (1 + k)) ⁻¹
                        ∙ cong (fst A) (+-comm 0 (2 + k))) ⁻¹)
                       (pathNewShift A (1 + k) 1 ⁻¹)) ⁻¹
                  ∙ cong (transport (pathNewShift A (suc k) 1 ⁻¹) ∘_)
                    (cong transport (symDistr (cong (fst A)
                                              (+-comm 1 (1 + k)) ⁻¹)  
                                             (cong (fst A) (+-comm 0 (2 + k))))
                    ∙ (2trnsprt (cong (fst A) (+-comm 0 (2 + k)) ⁻¹)
                                (cong (fst A) (+-comm 1 (1 + k)) ⁻¹ ⁻¹)) ⁻¹))
                  (transport (λ i → (cong (fst A) (+-comm 0 (2 + k)) i))
                  (transport (λ i → fst A (+-comm 1 (1 + k) (~ i)))
                  (transport (λ i → pathNewShift A (1 + k) 1 i)
                  (oneShiftDiag→kDiag1FamMap
                    (indexShiftDiag' (1 + k) A) n x))))
             ∙ cong (transport (λ i → pathNewShift A (1 + k) 1 (~ i))
                    ∘ transport (λ i → fst A (+-comm 1 (1 + k) i)))
             (funExt⁻ (invtrnsprt (cong (fst A) (+-comm 0 (2 + k))))
             (transport (λ i → fst A (+-comm 1 (1 + k) (~ i)))
             (transport (λ i → pathNewShift A (1 + k) 1 i)
             (oneShiftDiag→kDiag1FamMap (indexShiftDiag' (1 + k) A) n x))))
             ∙ cong (transport (pathNewShift A (1 + k) 1 ⁻¹))
                 (funExt⁻
                  (invtrnsprt' (cong (fst A) (+-comm 1 (1 + k))))
                  (transport (λ i → pathNewShift A (1 + k) 1 i)
                  (oneShiftDiag→kDiag1FamMap (indexShiftDiag' (1 + k) A) n x)))
             ∙ funExt⁻
               (invtrnsprt (pathNewShift A (1 + k) 1))
               (oneShiftDiag→kDiag1FamMap (indexShiftDiag' (1 + k) A) n x))


  transportingDiagMapAux : (k : ℕ) (A : ℕ-Diagram)
    → (λ n x → transport (λ i → (cong (fst A) (+-comm 0 (2 + k))
                          ∙ pathNewShift A (2 + k) 0 ⁻¹) i)
               (transport (λ i → fst A (+-comm 1 (1 + k) (~ i)))
               (transport (λ i → pathNewShift A (1 + k) 1 i)
               (oneShiftDiag→kDiag1FamMap (indexShiftDiag' (1 + k) A) n x))))
    ≡ oneShiftDiag→kDiag1FamMap (indexShiftDiag' (1 + k) A)
  transportingDiagMapAux k A =
    funExt₂ (transportingDiagMapAux' k A)

{- mostly path algebra, using the above -}
transportingDiagMapPath' : (k : ℕ) (A : ℕ-Diagram)
 → transport (λ i → MapOfDiagrams
                          (indexShiftDiag' (2 + k) A)
                          (KDiagram ((cong (fst A) (+-comm 0 (2 + k))
                                      ∙ pathNewShift A (2 + k) 0 ⁻¹) i)))
          (newShiftDiag→kDiag A (2 + k))
 ≡ oneShiftDiag→kDiag1FamMapDMap (indexShiftDiag' (1 + k) A)
transportingDiagMapPath' k A =
  transportingDiagMapPath k A (fst (indexShiftDiag' (2 + k) A) 0)
  (cong (fst A) (+-comm 0 (2 + k)) ∙ pathNewShift A (2 + k) 0 ⁻¹)
  ∙ ΣPathP (transportingDiagMapAux k A
    , toPathP
      (transport
      (λ i → (n : ℕ) (x : fst (indexShiftDiag' (1 + k) A) (2 + n))
        → funExt₂ (transportingDiagMapAux' k A) i (1 + n) x
           ≡ funExt₂ (transportingDiagMapAux' k A) i n
                      (snd (indexShiftDiag' (1 + k) A) (1 + n) x))
          (λ n x → refl)
       ≡⟨ trnsprtHmtpy' (λ n → fst (indexShiftDiag' (1 + k) A) n)
                    suc (λ n → snd (indexShiftDiag' (1 + k) A) (1 + n))
                    (transportingDiagMapAux' k A)
                    (transportingDiagMapAux' k A)
                    (λ n x → refl) ⟩
      (λ n x → transportingDiagMapAux' k A (1 + n) x ⁻¹
                ∙ refl
                ∙ transportingDiagMapAux' k A n
                  (snd (indexShiftDiag' (1 + k) A) (1 + n) x))
       ≡⟨ funExt₂ (λ n x →
           cong (transportingDiagMapAux' k A (1 + n) x ⁻¹ ∙_)
                (lUnit _ ⁻¹)
           ∙ lCancel (transportingDiagMapAux' k A (1 + n) x)) ⟩
      (λ n x → refl) ∎))


{- Key lemma showing that the projection is, essentially, the limit of a map
   of diagrams, first part -}
newShiftDiagMapIs : (A : ℕ-Diagram) (k : ℕ)
  → (fst (fst (snd (Lim (indexShiftDiag' k A)))) 0)
   ≡ transport (λ i → pathNewShift A k 0 (~ i))
     ∘ transport (λ i → fst A (+-comm 0 k i))
     ∘ MapOfDiagrams→MapOfLimits' (indexShiftDiag' k A) (KDiagram (fst A k))
         (newShiftDiag→kDiag A k) (Lim (indexShiftDiag' k A))
         (fst A k , KLimit (fst A k))
newShiftDiagMapIs A zero = transportRefl _ ⁻¹
newShiftDiagMapIs A (suc zero) = transportRefl _ ⁻¹
newShiftDiagMapIs A (suc (suc k)) =
  sym (transport (λ i → pathNewShift A (2 + k) 0 (~ i))
      ∘ transport (λ i → fst A (+-comm 0 (2 + k) i))
      ∘ MapOfDiagrams→MapOfLimits' (indexShiftDiag' (2 + k) A)
        (KDiagram (fst A (2 + k))) (newShiftDiag→kDiag A (2 + k))
        (Lim (indexShiftDiag' (2 + k) A))
        (fst A (2 + k) , KLimit (fst A (2 + k)))
  ≡⟨ cong (_∘ MapOfDiagrams→MapOfLimits' (indexShiftDiag' (2 + k) A)
               (KDiagram (fst A (2 + k))) (newShiftDiag→kDiag A (2 + k))
               (Lim (indexShiftDiag' (2 + k) A))
               (fst A (2 + k) , KLimit (fst A (2 + k))))
           (2trnsprt (cong (fst A) (+-comm 0 (2 + k)))
                     (pathNewShift A (2 + k) 0 ⁻¹)) ⟩
      transport (λ i → (cong (fst A) (+-comm 0 (2 + k))
                      ∙ pathNewShift A (2 + k) 0 ⁻¹) i)
      ∘ MapOfDiagrams→MapOfLimits' (indexShiftDiag' (2 + k) A)
        (KDiagram (fst A (2 + k))) (newShiftDiag→kDiag A (2 + k))
        (Lim (indexShiftDiag' (2 + k) A))
        (fst A (2 + k) , KLimit (fst A (2 + k)))
  ≡⟨ mapOfDiagsTranspNat k A (fst (indexShiftDiag' (1 + k) A) 1)
               (cong (fst A) (+-comm 0 (2 + k))
                ∙ pathNewShift A (2 + k) 0 ⁻¹) ⟩
      MapOfDiagrams→MapOfLimits' (indexShiftDiag' (2 + k) A)
        (KDiagram (fst (indexShiftDiag' (1 + k) A) 1))
        (transport (λ i → MapOfDiagrams
                          (indexShiftDiag' (2 + k) A)
                          (KDiagram ((cong (fst A) (+-comm 0 (2 + k))
                                      ∙ pathNewShift A (2 + k) 0 ⁻¹) i)))
          (newShiftDiag→kDiag A (2 + k)))
        (Lim (indexShiftDiag' (2 + k) A))
        (fst (indexShiftDiag' (1 + k) A) 1
             , KLimit (fst (indexShiftDiag' (1 + k) A) 1))
  ≡⟨ cong (λ m → MapOfDiagrams→MapOfLimits' (indexShiftDiag' (2 + k) A)
                    (KDiagram (fst (indexShiftDiag' (1 + k) A) 1))
                    m
                    (Lim (indexShiftDiag' (2 + k) A))
                    (fst (indexShiftDiag' (1 + k) A) 1
                       , KLimit (fst (indexShiftDiag' (1 + k) A) 1)))
           (transportingDiagMapPath' k A) ⟩
      MapOfDiagrams→MapOfLimits' (indexShiftDiag' (2 + k) A)
      (KDiagram (fst (indexShiftDiag' (1 + k) A) 1))
      (oneShiftDiag→kDiag1FamMapDMap (indexShiftDiag' (1 + k) A))
      (Lim (indexShiftDiag' (2 + k) A))
      (fst (indexShiftDiag' (1 + k) A) 1 ,
           KLimit (fst (indexShiftDiag' (1 + k) A) 1))
  ≡⟨ refl ⟩
      fst (fst (snd (Lim (indexShiftOfOne (indexShiftDiag' (1 + k) A))))) 0 ∎)


{- Key lemma showing that the projection is, essentially, the limit of a map
   of diagrams, second part -}
obvsLimitProj : (A : ℕ-Diagram) (k n : ℕ)
  → fst (fst (snd (Lim A))) (n + k)
   ≡ transport (λ i → fst A (+-comm k n i))
     ∘ transport (λ i → pathNewShift A k n i)
     ∘ fst (fst (obvsLimit'' A k)) n
obvsLimitProj A zero n = sym
  (transport (λ i → fst A (+-comm 0 n i))
  ∘ transport (λ i → pathNewShift A 0 n i)
  ∘ fst (fst (easyLimit A)) n
     ≡⟨ cong (transport (λ i → fst A (+-comm 0 n i)) ∘_)
             (funExt (λ x → transportRefl (fst (fst (easyLimit A)) n x))) ⟩
  transport (λ i → fst A (+-comm 0 n i))
  ∘ fst (fst (easyLimit A)) n
     ≡⟨ projTranspNat A n (n + 0) (+-comm 0 n) ⟩
  fst (fst (snd (Lim A))) (n + 0) ∎)
obvsLimitProj A (suc zero) n = sym
  (transport (λ i → fst A (+-comm 1 n i))
  ∘ transport (λ i → pathNewShift A 1 n i)
  ∘ fst (fst (obvsLimit'' A 1)) n ≡⟨ refl ⟩
  transport (λ i → fst A (+-comm 1 n i))
  ∘ transport (λ i → pathNewShift A 1 n i)
  ∘ fst (fst (easyLimit A)) (1 + n)
     ≡⟨ cong (transport (λ i → fst A (+-comm 1 n i)) ∘_)
             (funExt
             (λ x → transportRefl (fst (fst (easyLimit A)) (1 + n) x))) ⟩
  transport (λ i → fst A (+-comm 1 n i))
  ∘ fst (fst (easyLimit A)) (1 + n)
     ≡⟨ projTranspNat A (1 + n) (n + 1) (+-comm 1 n) ⟩
  fst (fst (easyLimit A)) (n + 1) ∎)
obvsLimitProj A (suc (suc k)) n = sym
  (transport (λ i → fst A (+-comm (2 + k) n i))
  ∘ transport (λ i → pathNewShift A (2 + k) n i)
  ∘ fst (fst (obvsLimit'' A (2 + k))) n ≡⟨ refl ⟩
  transport (λ i → fst A (+-comm (2 + k) n i))
  ∘ transport (λ i → pathNewShift A (2 + k) n i)
  ∘ fst (fst (obvsLimit'' A (1 + k))) (1 + n)
    ≡⟨ cong (_∘ fst (fst (obvsLimit'' A (1 + k))) (1 + n))
            (2trnsprt (pathNewShift A (2 + k) n)
                     (cong (fst A) (+-comm (2 + k) n))) ⟩
  transport (λ i → (pathNewShift A (2 + k) n
                     ∙ cong (fst A) (+-comm (2 + k) n)) i)
  ∘ fst (fst (obvsLimit'' A (1 + k))) (1 + n)
    ≡⟨ cong (transport (λ i → (pathNewShift A (2 + k) n
                                ∙ cong (fst A) (+-comm (2 + k) n)) i) ∘_)
             ((sqtrns (cong (fst A) (+-comm (1 + k) (1 + n)))
                      (pathNewShift A (1 + k) (1 + n))
                      (fst (fst (snd (Lim A))) (1 + n + (1 + k)))
                      (fst (fst (obvsLimit'' A (1 + k))) (1 + n))
                      (obvsLimitProj A (suc k) (suc n))) ⁻¹) ⟩ -- induction step
  transport (λ i → (pathNewShift A (2 + k) n
                     ∙ cong (fst A) (+-comm (2 + k) n)) i)
  ∘ transport (pathNewShift A (1 + k) (1 + n) ⁻¹)
  ∘ transport (cong (fst A) (+-comm (1 + k) (1 + n)) ⁻¹)
  ∘ fst (fst (snd (Lim A))) (1 + n + (1 + k))
    ≡⟨ cong (transport (λ i → (pathNewShift A (2 + k) n
                                 ∙ cong (fst A) (+-comm (2 + k) n)) i) ∘_)
            (cong (_∘ fst (fst (snd (Lim A))) (1 + n + (1 + k)))
                  (2trnsprt (cong (fst A) (+-comm (1 + k) (1 + n)) ⁻¹)
                             (pathNewShift A (1 + k) (1 + n) ⁻¹)
                  ∙ cong transport
                     (symDistr (pathNewShift A (1 + k) (1 + n))
                              (cong (fst A) (+-comm (1 + k) (1 + n))) ⁻¹))) ⟩
  transport (λ i → (pathNewShift A (2 + k) n
                      ∙ cong (fst A) (+-comm (2 + k) n)) i)
  ∘ transport (λ i → (pathNewShift A (1 + k) (1 + n)
                       ∙ cong (fst A) (+-comm (1 + k) (1 + n))) (~ i))
  ∘ fst (fst (snd (Lim A))) (1 + n + (1 + k))
    ≡⟨ cong (_∘ transport ((pathNewShift A (1 + k) (1 + n)
                             ∙ cong (fst A) (+-comm (1 + k) (1 + n))) ⁻¹)
               ∘ fst (fst (snd (Lim A))) (1 + n + (1 + k)))
            (cong transport (pathNewShiftPath' A k n)
            ∙ 2trnsprt (pathNewShift A (1 + k) (1 + n)
                         ∙ cong (fst A) (+-comm (1 + k) (1 + n)))
                        (cong (fst A) (cong suc (+-comm n (suc k))
                                     ∙ +-comm (suc (suc k)) n)) ⁻¹) ⟩
  transport (cong (fst A) (cong suc (+-comm n (suc k))
                       ∙ +-comm (suc (suc k)) n))
  ∘ transport (pathNewShift A (1 + k) (1 + n)
                ∙ cong (fst A) (+-comm (1 + k) (1 + n)))
  ∘ transport ((pathNewShift A (1 + k) (1 + n)
                ∙ cong (fst A) (+-comm (1 + k) (1 + n))) ⁻¹)
  ∘ fst (fst (snd (Lim A))) (1 + n + (1 + k))
    ≡⟨ cong (transport (cong (fst A) (cong suc (+-comm n (suc k))
                                       ∙ +-comm (suc (suc k)) n)) ∘_)
             (cong (_∘ fst (fst (snd (Lim A))) (1 + n + (1 + k)))
                   (invtrnsprt' (pathNewShift A (1 + k) (1 + n) ∙
                                 cong (fst A) (+-comm (1 + k) (1 + n)))))
       ∙ projTranspNat A (1 + n + (1 + k)) (n + (2 + k))
           (cong suc (+-comm n (suc k))
           ∙ +-comm (suc (suc k)) n) ⟩
  fst (fst (snd (Lim A))) (n + (2 + k)) ∎)


{- Key lemma showing that the projection is, essentially, the limit of a map
   of diagrams, third part -}
projectionsAgree : (k : ℕ) (A : ℕ-Diagram)
  → fst (fst (snd (Lim A))) k
   ≡ (transport (λ i → fst A (+-comm k 0 i))
     ∘ transport (λ i → pathNewShift A k 0 i))
     ∘ fst (fst (snd (Lim (indexShiftDiag' k A)))) 0
     ∘ equivFun (UniqueLimit (indexShiftDiag' k A)
                (limitType A , obvsLimit'' A k)
                (Lim (indexShiftDiag' k A)))
projectionsAgree zero A = (transportRefl _) ⁻¹
projectionsAgree (suc zero) A = (transportRefl _) ⁻¹
projectionsAgree (suc (suc k)) A =
  fst (fst (snd (Lim A))) (2 + k) ≡⟨ obvsLimitProj A (2 + k) 0 ⟩
  (transport (λ i → fst A (+-comm (2 + k) 0 i))
  ∘ transport (λ i → pathNewShift A (2 + k) 0 i))
  ∘ fst (fst (obvsLimit'' A (2 + k))) 0
    ≡⟨ cong ((transport (cong (fst A) (+-comm (2 + k) 0))
             ∘ transport (pathNewShift A (2 + k) 0)) ∘_)
             (UniqueLimitComp (indexShiftDiag' (2 + k) A)
                                (limitType A , obvsLimit'' A (2 + k))
                                (Lim (indexShiftDiag' (2 + k) A))
                                0) ⟩
  transport (λ i → fst A (+-comm (2 + k) 0 i))
  ∘ transport (λ i → pathNewShift A (2 + k) 0 i)
  ∘ fst (fst (snd (Lim (indexShiftDiag' (2 + k) A)))) 0
  ∘ equivFun (UniqueLimit (indexShiftDiag' (2 + k) A)
             (limitType A , obvsLimit'' A (2 + k))
             (Lim (indexShiftDiag' (2 + k) A))) ∎
