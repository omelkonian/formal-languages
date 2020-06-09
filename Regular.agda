module Regular where


open import Function using (_∘_; _$_)

open import Data.Empty   using (⊥)
open import Data.Unit    using (⊤; tt)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; Σ-syntax; map₁; map₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Char    using (Char)
  renaming (_≟_ to _≟ᶜ_)
open import Data.Nat     using (ℕ; suc; _+_)
open import Data.Fin     using (Fin)
  renaming (suc to fsuc; zero to fzero)

open import Data.List using (List; []; _∷_; [_]; map; _++_; concat; concatMap; zip; length)
open import Data.List.Properties using (≡-dec)

open import Data.List.Relation.Unary.Any
  using (Any; here; there)

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong)

open import Prelude.Lists

Type  = Set

private
  variable
    A B : Type

splitAt : ∀ (xs : List A) → Fin (suc $ length xs) → List A × List A
splitAt xs       fzero    = [] , xs
splitAt (x ∷ xs) (fsuc i) = map₁ (x ∷_) (splitAt xs i)

splitAt′ : ∀ (xs : List A) → Index xs
  → Σ[ xsˡ ∈ List A ] Σ[ xsʳ ∈ List A ]
      length xsˡ + length xsʳ ≡ length xs
splitAt′ (x ∷ xs) fzero    = [ x ] , xs , refl
splitAt′ (x ∷ xs) (fsuc i) = let xsˡ , xsʳ , p = splitAt′ xs i
                             in  x ∷ xsˡ , xsʳ , cong suc p

-- repeat : ℕ → List A → List A
-- repeat 0       _  = []
-- repeat (suc n) xs = xs ++ repeat n xs

Token : Type
Token = Char

import Prelude.Set' as SET

module SETᶜ = SET {A = Char} _≟ᶜ_
Alphabet = Set' where open SETᶜ

Word : Type
Word = List Token

_ : Word
_ = [ 'a' ]

pattern ε = []

data Grammar (Σ : Alphabet) : Type where
  ∅ : Grammar Σ

  `ε : Grammar Σ

  I : (a : Token) → a SETᶜ.∈′ Σ → Grammar Σ

  _∪_ : Grammar Σ → Grammar Σ → Grammar Σ

  _∙_ : Grammar Σ → Grammar Σ → Grammar Σ

  _⁺ : Grammar Σ → Grammar Σ

private
  variable
    Σ : Alphabet

_⋆ : Grammar Σ → Grammar Σ
g ⋆ = `ε ∪ (g ⁺)


{-# TERMINATING #-}
-- T0D0: explain well-founded recursion, apply to `accept`
-- _≺_ : List A → List A → Set
-- xs ≺ ys = length xs < length ys
-- wf : WellFounded _≺_
accept : Grammar Σ → Word → Type
accept ∅ _ = ⊥

accept `ε ε = ⊤
accept `ε _ = ⊥

accept (I a _) xs = xs ≡ [ a ]

accept (g₁ ∪ g₂) xs = accept g₁ xs ⊎ accept g₂ xs

accept (g₁ ∙ g₂) xs
  = Σ[ i ∈ Fin (suc $ length xs) ]
      let xsˡ , xsʳ = splitAt xs i
      in accept g₁ xsˡ × accept g₂ xsʳ

accept (g ⁺) xs
  -- = ∃ λ is → All (accept g) (takeApart is xs)
  = ∃ λ i → let xsˡ , xsʳ , p = splitAt′ xs i
            in  accept g xsˡ × accept (g ⁺) xsʳ
-- n ∈ [1 , ... , len]
-- NB: infer ys n, kind of easy

postulate
  Σ′ : Alphabet
  a b : Token

  a∈ : a SETᶜ.∈′ Σ′
  b∈ : b SETᶜ.∈′ Σ′

Gᵃ : Grammar Σ′
Gᵃ = I a a∈

Gᵇ : Grammar Σ′
Gᵇ = I b b∈

G′ : Grammar Σ′
G′ = (Gᵃ ∪ Gᵇ) ∙ `ε

G″ : Grammar Σ′
G″ = G′ ⋆

-- _ : accept Gᵃ (a ∷ [])
-- _ = refl

-- _ : accept G′ [ b ]
-- _ = fsuc fzero , inj₂ refl , tt

-- _ : accept G″ ('a' ∷ 'b' ∷ 'a' ∷ 'b' ∷ 'b' ∷ [])
-- _ = [0,5,7,14] , [ ? , ? , ? , ? ]

{-
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
-}

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
