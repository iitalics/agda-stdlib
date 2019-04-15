------------------------------------------------------------------------
-- The Agda standard library
--
-- AVL tree membership, along with some helpful properties
------------------------------------------------------------------------

open import Relation.Binary using (StrictTotalOrder)

module Data.AVL.Membership
  {a ℓ₁ ℓ₂}
  (strictTotalOrder : StrictTotalOrder a ℓ₁ ℓ₂)
  where

private
  module S = StrictTotalOrder strictTotalOrder
  open S using () renaming (Carrier to Key)

open import Data.AVL strictTotalOrder as Tree using (Tree)
open import Data.AVL.Value S.Eq.setoid using (Value)
import Data.AVL.Indexed strictTotalOrder as I
import Data.AVL.Key strictTotalOrder as Key

open import Data.Bool.Base using (T)
open import Data.Maybe as Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Data.Unit

open import Relation.Unary hiding (Decidable)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (Decidable; tri<; tri>; tri≈)

-----------------------------------------------------------------------

module _ {v} {V : Value v} where
  private
    Val = Value.family V

  infix 4 _∈ₖ_ _∉ₖ_ _∈ₖ?_

  _∈ₖ_ _∉ₖ_ : Key → Tree V → Set
  k ∈ₖ t = T (Maybe.is-just (Tree.lookup k t))
  k ∉ₖ t = ¬ k ∈ₖ t

  _∈ₖ?_ : Decidable _∈ₖ_
  k ∈ₖ? t with Tree.lookup k t
  ... | just _  = yes tt
  ... | nothing = no (λ ())

  value : ∀ {k t} → k ∈ₖ t → Val k
  value {k} {t} pf = Maybe.to-witness-T (Tree.lookup k t) pf

  ∉ₖ-empty : ∀ {k} → k ∉ₖ Tree.empty
  ∉ₖ-empty ()

  ∈ₖ-singleton : ∀ k v → k ∈ₖ Tree.singleton k v
  ∈ₖ-singleton k v with S.compare k k
  ... | tri< _ k≢k _ = contradiction S.Eq.refl k≢k
  ... | tri> _ k≢k _ = contradiction S.Eq.refl k≢k
  ... | tri≈ _ k≡k _ = tt

module _ {v w} {V : Value v} {W : Value w} where
  private
    Val = Value.family V
    Wal = Value.family W

  ∈ₖ-map⁺ : ∀ (f : ∀[ Val ⇒ Wal ]) {k t} →
            k ∈ₖ t →
            k ∈ₖ Tree.map {W = W} f t
  ∈ₖ-map⁺ f {k} {Tree.tree t} = help t Key.⊥⁺<[ k ]<⊤⁺
    where
    help : ∀ {l u h} (t : I.Tree V l u h) (l<k<u : _) →
           T (Maybe.is-just (I.lookup k t l<k<u)) →
           T (Maybe.is-just (I.lookup k (I.map {W = W} f t) l<k<u))
    help (I.node (k′ , _) lp pu _) (l<k , k<u) pf
      with S.compare k′ k
    ...  | tri< k′<k _ _ = help pu (Key.[ k′<k ]ᴿ , k<u) pf
    ...  | tri> _ _ k′>k = help lp (l<k , Key.[ k′>k ]ᴿ) pf
    ...  | tri≈ _ k′≡k _ = tt
