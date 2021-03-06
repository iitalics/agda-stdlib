------------------------------------------------------------------------
-- The Agda standard library
--
-- Greatest Common Divisor for integers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Integer.GCD where

open import Data.Integer
open import Data.Integer.Divisibility
open import Data.Nat
import Data.Nat.GCD as ℕ
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Definition
------------------------------------------------------------------------

gcd : ℤ → ℤ → ℤ
gcd i j = + ℕ.gcd ∣ i ∣ ∣ j ∣

------------------------------------------------------------------------
-- Properties
------------------------------------------------------------------------

gcd[i,j]∣i : ∀ i j → gcd i j ∣ i
gcd[i,j]∣i i j = ℕ.gcd[m,n]∣m ∣ i ∣ ∣ j ∣

gcd[i,j]∣j : ∀ i j → gcd i j ∣ j
gcd[i,j]∣j i j = ℕ.gcd[m,n]∣n ∣ i ∣ ∣ j ∣

gcd-greatest : ∀ {i j c} → c ∣ i → c ∣ j → c ∣ gcd i j
gcd-greatest c∣i c∣j = ℕ.gcd-greatest c∣i c∣j

gcd[0,0]≡0 : gcd 0ℤ 0ℤ ≡ 0ℤ
gcd[0,0]≡0 = cong (+_) ℕ.gcd[0,0]≡0

gcd-comm : ∀ i j → gcd i j ≡ gcd j i
gcd-comm i j = cong (+_) (ℕ.gcd-comm ∣ i ∣ ∣ j ∣)
