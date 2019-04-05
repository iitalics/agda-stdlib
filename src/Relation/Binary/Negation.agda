------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of negating binary relations
------------------------------------------------------------------------

module Relation.Binary.Negation where

open import Relation.Binary.Core
open import Relation.Nullary
open import Data.Product

infix 3 ¬₂_

¬₂_ : ∀ {a b r} {A : Set a} {B : Set b} → REL A B r → REL A B r
(¬₂ R) x y = ¬ (R x y)

module _ {a b} {A : Set a} {B : Set b} where
  symmetric : ∀ {p q} {P : REL A B p} {Q : REL B A q} →
              Sym P Q → Sym (¬₂ Q) (¬₂ P)
  symmetric sym np p = np (sym p)

module _ {a r} {A : Set a} {_≈_ : Rel A r}
         (isEquivalence : IsEquivalence _≈_)
         where
  private _≉_ = ¬₂ _≈_
  open IsEquivalence isEquivalence

  ≉-transˡ : Trans _≉_ _≈_ _≉_
  ≉-transˡ i≉j j≈k i≈k = i≉j (trans i≈k (sym j≈k))

  ≉-transʳ : Trans _≈_ _≉_ _≉_
  ≉-transʳ i≈j j≉k i≈k = j≉k (trans (sym i≈j) i≈k)

  ≉-respˡ-≈ : _≉_ Respectsˡ _≈_
  ≉-respˡ-≈ y≈z y≉x z≈x = y≉x (trans y≈z z≈x)

  ≉-respʳ-≈ : _≉_ Respectsʳ _≈_
  ≉-respʳ-≈ y≈z x≉y x≈z = x≉y (trans x≈z (sym y≈z))

  ≉-resp₂-≈ : _≉_ Respects₂ _≈_
  ≉-resp₂-≈ = ≉-respʳ-≈ , ≉-respˡ-≈
