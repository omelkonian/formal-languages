module Language where

open import Function.Equivalence public
  using (_⇔_)

open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Set'

Type  = Set₀
Type↑ = Set₁

variable
  A B : Type

Token : Type
Token = Char

Alphabet : Type
Alphabet = Set⟨ Token ⟩

Word : Type
Word = List Token

private
  -- NB: words might be infinite, use Codata.Colist maybe?
  _ : Word
  _ = [ 'a' ]

pattern ε = []

-- variable
--   Σ : Alphabet

record Language (A : Type) : Type↑ where
  field
    accept : A → Word → Type
open Language {{...}} public

_~_ : {{_ : Language A}} {{_ : Language B}} → A → B → Type
l ~ l′ = ∀ w → accept l w ⇔ accept l′ w
  -- LEFT: ∀ w. accept l w (DFA) → accept l′ w (Regex)
  -- RIGHT: ∀ w. accept l′ w → accept l w
