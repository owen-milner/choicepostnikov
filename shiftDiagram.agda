module shiftDiagram where

open import Cubical.Data.Nat renaming (elim to ℕElim)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Foundations.Everything
open import Cubical.HITs.Truncation
open import Cubical.Homotopy.Connected

open import DiagramSigma
open import Limits

{- one definition of a shifted/truncated diagram -}

newShiftDiag : (A : ℕ-Diagram) (k : ℕ) → ℕ-Diagram
fst (newShiftDiag (A , a) k) n = A (n + k)
snd (newShiftDiag (A , a) k) n = a (n + k)

