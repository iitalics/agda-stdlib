------------------------------------------------------------------------
-- The Agda standard library
--
-- Vectors
------------------------------------------------------------------------

-- This implementation is designed for reasoning about dynamic
-- vectors which may increase or decrease in size.

-- See `Data.Vec.Functional` for an alternative implementation as
-- functions from finite sets, which is more suitable for reasoning
-- about fixed sized vectors and for when ease of retrevial is
-- important.

{-# OPTIONS --without-K --safe #-}

module Data.Vec where

open import Level
open import Data.Nat.Base using (suc; _+_)
import Data.Nat.Properties as ℕₚ
open import Data.Vec.Bounded.Base as Vec≤
  using (Vec≤; ≤-cast; fromVec)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)
open import Relation.Nullary using (yes; no; recompute)
open import Relation.Unary using (Decidable)

private
  variable
    a p : Level
    A : Set a

------------------------------------------------------------------------
-- Publicly re-export the contents of the base module

open import Data.Vec.Base public

------------------------------------------------------------------------
-- Additional operations

module _ {P : A → Set p} (P? : Decidable P) where

  filter : ∀ {n} → Vec A n → Vec≤ A n
  filter []       = Vec≤.[]
  filter (a ∷ as) with P? a
  ... | yes p = a Vec≤.∷ filter as
  ... | no ¬p = ≤-cast (ℕₚ.n≤1+n _) (filter as)

  takeWhile : ∀ {n} → Vec A n → Vec≤ A n
  takeWhile []       = Vec≤.[]
  takeWhile (a ∷ as) with P? a
  ... | yes p = a Vec≤.∷ takeWhile as
  ... | no ¬p = Vec≤.[]

  dropWhile : ∀ {n} → Vec A n → Vec≤ A n
  dropWhile Vec.[]       = Vec≤.[]
  dropWhile (a Vec.∷ as) with P? a
  ... | yes p = ≤-cast (ℕₚ.n≤1+n _) (dropWhile as)
  ... | no ¬p = fromVec (a Vec.∷ as)

-- "Reverse append" xs ʳ++ ys = reverse xs ++ ys

infixr 5 _⊢_ʳ++_ _ʳ++_

_⊢_ʳ++_ : ∀ {n m k} → .(n + m ≡ k) → Vec A n → Vec A m → Vec A k
eq ⊢ []     ʳ++ ys = P.subst (Vec _) (recompute (_ ℕₚ.≟ _) eq) ys
eq ⊢ x ∷ xs ʳ++ ys = P.trans (ℕₚ.+-suc _ _) eq ⊢ xs ʳ++ x ∷ ys

_ʳ++_ : ∀ {n m} → Vec A n → Vec A m → Vec A (n + m)
_ʳ++_ = refl ⊢_ʳ++_

-- Reverse

reverse : ∀ {n} → Vec A n → Vec A n
reverse {n = n} xs = ℕₚ.+-identityʳ n ⊢ xs ʳ++ []
