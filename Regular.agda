module Regular where


open import Function using (_∘_; _$_)

open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Data.Char using (Char)
  renaming (_≟_ to _≟ᶜ_)

open import Data.List using (List; []; _∷_; [_]; map; _++_; concat; concatMap; zip)
open import Data.List.Properties using (≡-dec)

Type  = Set

Token : Type
Token = Char

import Prelude.Set' as SET

module SETᶜ = SET {A = Char} _≟ᶜ_
Alphabet = Set' where open SETᶜ

Word : Type
Word = List Token

_ : Word
_ = [ 'a' ]

ε : Word
ε = []


data Grammar (Σ : Alphabet) : Language → Type where
  ∅ :
    ------------
    Grammar Σ ∅ℓ

  `ε :
    ------------
    Grammar Σ εℓ


  I :
      (a : Token)
    → a SETᶜ.∈′ Σ
      ----------------------------------
    → Grammar Σ (SETʷ.singleton [ 'a' ])

  _∪_ : ∀ {ℓ₁ ℓ₂ : Language}

    → Grammar Σ ℓ₁
    → Grammar Σ ℓ₂
      -----------------------
    → Grammar Σ (ℓ₁ ∪ℓ ℓ₂)

  _∙_ : ∀ {ℓ₁ ℓ₂ : Language}

    → Grammar Σ ℓ₁
    → Grammar Σ ℓ₂
      --------------------
    → Grammar Σ (ℓ₁ ∙ℓ ℓ₂)

  _⁺ : ∀ {ℓ}
    → Grammar Σ ℓ
      ---------------
    → Grammar Σ (ℓ ⁺ℓ)

-- _⋆ : ∀ {Σ ℓ}
--   → Grammar Σ ℓ
--     --------------------
--   → Grammar Σ ((ℓ ⁺ℓ) ∪ℓ εℓ)
-- g ⋆ = `ε ∪ (g ⁺)


module SETʷ = SET {A = Word} (≡-dec _≟ᶜ_)
Language = Set' where open SETʷ

∅ℓ : Language
∅ℓ = SETʷ.∅

εℓ : Language
εℓ = SETʷ.singleton ε


cart : ∀ {A B : Type} → List A → List B → List (A × B)
cart []       _  = []
cart (x ∷ xs) ys = map (x ,_) ys ++ cart xs ys

_∙ℓ_ : Language → Language → Language
(SET.⟨ xs ⟩∶- _) ∙ℓ (SET.⟨ ys ⟩∶- _)
  = SETʷ.fromList $ map (λ{(x , y) → x ++ y}) $ cart xs ys

_∙ℓ′_ : Language → Language → Language
(SET.⟨ xs ⟩∶- _) ∙ℓ′ (SET.⟨ ys ⟩∶- _)
  = SETʷ.fromList $ map (λ{(x , y) → x ++ y}) $ zip xs ys

_⁺ℓ : Language → Language
ℓ ⁺ℓ = {!!} -- ℓ ∪ℓ (ℓ ∙ℓ′ ℓ) ∪ℓ (...) ∪

_∪ℓ_ : Language → Language → Language
_∪ℓ_ = SETʷ._∪_


-- postulate
--   weakening : ∀ {Σ' Σ ℓ} → Grammar Σ' ℓ → Σ' SETᶜ.⊆ Σ → Grammar Σ ℓ

{-


_ : a SETᶜ.∈ singleton a
_ = here refl

_ : a SETᶜ.∈ SETᶜ.fromList (b ∷ a ∷ [])
_ = there (here refl)

_ : a SETᶜ.∈ SETᶜ.fromList (c ∷ b ∷ a ∷ [])
_ = there (there (here refl))

JustA : Grammar {a}
JustA = unit a (here refl)

Σ : Alphabet
Σ = {a, b}

MyLang : Grammar Σ ({ab} ⋆ℓ)
MyLang = a*|b*,

s : Word
s = "aaa"

_∈_ : Word → Grammar Σ → Type
-- w ∈ g
"a" ∈ {a} = ⊤
"aa" ∈ {a} = ⊥


data ⊥ : Type where

data ⊤ : Type where
  tt : ⊤


¬

_ : "a" ∈ {a}
_ = tt

-- lemma : ¬ ("aa" ∈ {a}) -- ("aa" ∈ {a} → ⊥)
-- lemma ()







_ : "aaabbbb" ∈ MyLang

_ : "bb" ∈ MyLang



_∉_ = ¬_ ∘ _∈_

_ : "???" ∉ MyLang

-}

{-
** Compute alphabet, instead of pre-defining it

σ : Grammar → Alphabet
-}

{-
*** Parametrize words over alphabets

s : Word {a}
s = "aaa"

Word Σ

_∈_ : ∀ {pr : Σ' ⊆ Σ} → Word Σ' → Grammar Σ → Type
"a" ∈ {a} = true
"aa" ∈ {a} = false
w ∈ g

-}
