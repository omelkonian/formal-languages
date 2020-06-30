module Language where

open import Prelude.Init hiding (_⇔_)
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

_⇔_ : ∀ {A : Type} → Pred A 0ℓ → Pred A 0ℓ → Set
P ⇔ Q = ∀ x → (P x → Q x) × (Q x → P x)

_~_ : {{_ : Language A}} {{_ : Language B}} → A → B → Type
l ~ l′ = accept l ⇔ accept l′
  -- LEFT: ∀ w. accept l w (DFA) → accept l′ w (Regex)
  -- RIGHT: ∀ w. accept l′ w → accept l w

{-
_≈_ : {{_ : Language A}} {{_ : Language B}} → A → B → Type
a ≈ b = (a ↔ b) × (a ~ b)

_ : FSA ≈ Regex
_ = record {to = DFA⇒Regex; from = Regex⇒DFA}
  , ∀ fsa. DFA⇒Regex fsa ~ fsa
  , ∀ r.   Regex⇒DFA r   ~ r
-}
