------------------------------------------------------------------------
-- The Agda standard library
--
-- Coinductive reflexive transitive closures.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

module Codata.Costar where

open import Size
open import Level
open import Function

open import Codata.Thunk using (Thunk; Thunk-syntax; force)
open import Codata.Conat as Conat using (Conat; zero; suc)

open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PEq using (_≡_)

infixr 5 _◅_

data Costar {a ℓ} {A : Set a} (R : Rel A ℓ) (i : Size) : Rel A (a ⊔ ℓ) where
  ε : Reflexive (Costar R i)
  _◅_ : ∀ {a b c} (x : R a b) (xs : Thunk[ j < i ] Costar R j b c) → Costar R i a c

module _ {a ℓ} {A : Set a} {R : Rel A ℓ} where

  infixr 5 _◅◅_ _▻▻_

  -- Append/transitivity

  _◅◅_ : ∀ {i} → Transitive (Costar R i)
  ε        ◅◅ ys = ys
  (x ◅ xs) ◅◅ ys = x ◅ λ where .force → xs .force ◅◅ ys

  _▻▻_ : ∀ {i} → Transitive (flip (Costar R i))
  _▻▻_ = flip _◅◅_

  preorder : ∀ {i} → Preorder _ _ _
  preorder {i} = record
    { Carrier = A
    ; _≈_ = _≡_
    ; _∼_ = Costar R i
    ; isPreorder = record
      { isEquivalence = PEq.isEquivalence
      ; reflexive = λ { PEq.refl → ε }
      ; trans = _◅◅_ {i} } }

  -- Colist-like operations

  replicate : ∀ {a i} → Conat i → R a a → Costar R i a a
  replicate zero    _ = ε
  replicate (suc n) x = x ◅ λ where .force → replicate (n .force) x

  -- Monad operations

  return : ∀ {a b i} → R a b → Costar R i a b
  return x = x ◅ λ where .force → ε

gmap : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b} {P : Rel A ℓ₁} {Q : Rel B ℓ₂}
       (f : A → B) → P =[ f ]⇒ Q → ∀ {i} → Costar P i =[ f ]⇒ Costar Q i
gmap f g ε        = ε
gmap f g (x ◅ xs) = g x ◅ λ where .force → gmap f g (xs .force)

map : ∀ {a ℓ₁ ℓ₂} {A : Set a} {P : Rel A ℓ₁} {Q : Rel A ℓ₂} →
      P ⇒ Q → ∀ {i} → Costar P i ⇒ Costar Q i
map = gmap id
