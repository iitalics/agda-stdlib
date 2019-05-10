
module Text.Printf where

open import Level as Level using (Level)
open import Function
open import Data.String.Base as String using (String)
open import Data.List.Base as List using (List; _∷_; []; [_])
open import Data.Bool.Base as Bool using (T)
open import Data.Nat.Base as Nat using (ℕ)
open import Data.Nat.Show
open import Data.Maybe as Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Char.Base using (Char)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤)
open import IO as IO using (IO)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

private
  variable
    a b : Level
    A B : Set a

--------------------------------------------------------------------------------
-- Representation of format strings

data Spec : Set where
  str dec hex : Spec

data Chunk : Set where
  spec : Spec → Chunk
  string : String → Chunk

Format = List Chunk

SpecArg : Spec → Set
SpecArg str = String
SpecArg dec = ℕ
SpecArg hex = ℕ

_-Printf⟶_ : Format → Set a → Set a
[]               -Printf⟶ A = A
(spec sp ∷ fmt)  -Printf⟶ A = SpecArg sp → fmt -Printf⟶ A
(string s ∷ fmt) -Printf⟶ A = fmt -Printf⟶ A

mapPrintf : ∀ fmt → (A → B) → fmt -Printf⟶ A → fmt -Printf⟶ B
mapPrintf []               x   = x
mapPrintf (spec _   ∷ fmt) f g = mapPrintf fmt f ∘ g
mapPrintf (string _ ∷ fmt) f   = mapPrintf fmt f


--------------------------------------------------------------------------------
-- Parsing format strings

tryCharToSpec : Char → Maybe Spec
tryCharToSpec 's' = just str
tryCharToSpec 'd' = just dec
tryCharToSpec 'x' = just hex
tryCharToSpec c   = nothing

tryCharsToFormat : List Char → Maybe Format
tryCharsToFormat = parse []
  where
  push : List Char → Format → Format
  push []        fmt = fmt
  push s@(_ ∷ _) fmt = string (String.fromList (List.reverse s)) ∷ fmt

  parse : List Char → List Char → Maybe Format
  parse acc ('%' ∷ [])     = nothing
  parse acc ('%' ∷ c ∷ cs) = do sp ← tryCharToSpec c
                                fmt ← parse [] cs
                                just (push acc $ spec sp ∷ fmt)
  parse acc (c ∷ cs)       = parse (c ∷ acc) cs
  parse acc []             = just (push acc [])

tryStringToFormat : String → Maybe Format
tryStringToFormat = tryCharsToFormat ∘ String.toList

IsFormatString : String → Set
IsFormatString s = T (Maybe.is-just (tryStringToFormat s))

to-format-T : ∀ s → IsFormatString s → Format
to-format-T s = Maybe.to-witness-T (tryStringToFormat s)

private
  module ParsingTests where
    _↝_ = λ s f → tryStringToFormat s ≡ just f

    t₁ : "%s"         ↝ [ spec str ]
    t₂ : "foo %d"     ↝ (string "foo " ∷ [ spec dec ])
    t₃ : "(|%x, %x|)" ↝ (string "(|" ∷ spec hex ∷
                         string ", " ∷ spec hex ∷ [ string "|)" ])
    t₄ : "no spec"    ↝ [ string "no spec" ]
    t₁ = refl
    t₂ = refl
    t₃ = refl
    t₄ = refl


--------------------------------------------------------------------------------
-- Interface for rendering format strings

record Formattable (A : Set a) : Set a where
  field
    ε : A
    _∙_ : A → A → A
    fromString : String → A

instance
  IO-Formattable : Formattable (IO ⊤)
  IO-Formattable = record
    { ε          = IO.return _
    ; _∙_        = λ p q → ♯ p IO.>> ♯ q
    ; fromString = IO.putStr }
    where
    open import Codata.Musical.Notation using (♯_)

instance
  String-Formattable : Formattable String
  String-Formattable = record
    { ε          = ""
    ; _∙_        = String._++_
    ; fromString = id }

renderArg : {sp : Spec} → SpecArg sp → String
renderArg {str} = id
renderArg {dec} = showInBase 10
renderArg {hex} = showInBase 16


--------------------------------------------------------------------------------
-- printf

module _ {{formattable : Formattable A}} where
  open Formattable formattable

  printf : (fmt : Format) → fmt -Printf⟶ A
  printf []               = ε
  printf (spec sp ∷ fmt)  = λ arg →
    mapPrintf fmt (fromString (renderArg arg) ∙_) (printf fmt)
  printf (string s ∷ fmt) =
    mapPrintf fmt (fromString s ∙_) (printf fmt)

  printf′ : ∀ s {{isFmt : IsFormatString s}} →
            (to-format-T s isFmt) -Printf⟶ A
  printf′ s ⦃ isFmt ⦄ = printf (to-format-T s isFmt)

private
  module PrintfTests where
    t₁ : printf′ "x = %d" 5 ≡ "x = 5"
    t₂ : printf′ "%x, %d" 20 20 ≡ "14, 20"
    t₁ = refl
    t₂ = refl

    types₁ : ℕ → String
    types₁ = printf′ "{%d}"
    types₂ : ℕ → String → IO ⊤
    types₂ = printf′ "{%d %s}"
    types₃ : ℕ → _ → IO ⊤  -- _ = String
    types₃ = printf′ "{%d %s}"
