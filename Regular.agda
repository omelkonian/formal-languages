module Regular where

open import Level    using (0ℓ)
open import Function using (_∘_; _$_; _on_)
open import Induction.WellFounded

open import Data.Empty   using (⊥)
open import Data.Unit    using (⊤; tt)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; Σ-syntax; map₁; map₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Char    using (Char)
  renaming (_≟_ to _≟ᶜ_)
open import Data.Nat     -- using (ℕ; suc; _+_; _<_; _≤_)
open import Data.Nat.Properties
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Fin     using (Fin; #_)
  renaming (suc to fsuc; zero to fzero)

open import Data.List using (List; []; _∷_; [_]; map; _++_; concat; concatMap; zip; length)
open import Data.List.NonEmpty as NE using (List⁺; _∷_; _∷⁺_)
  renaming ([_] to [_]⁺)
open import Data.List.Properties using (≡-dec)

open import Data.List.Relation.Unary.Any using (Any; here; there)

open import Relation.Unary using (Pred)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Prelude.Lists

Type = Set

private
  variable
    A B : Type

splitAt : ∀ (xs : List A) → Fin (suc $ length xs) → List A × List A
splitAt xs       fzero    = [] , xs
splitAt (x ∷ xs) (fsuc i) = map₁ (x ∷_) (splitAt xs i)

private
  _ : splitAt (0 ∷ 1 ∷ []) (# 0) ≡ ([] , 0 ∷ 1 ∷ [])
  _ = refl

  _ : splitAt (0 ∷ 1 ∷ []) (# 1) ≡ ([ 0 ] , [ 1 ])
  _ = refl

  _ : splitAt (0 ∷ 1 ∷ []) (# 2) ≡ (0 ∷ 1 ∷ [] , [])
  _ = refl

splitAt⁺ʳ : ∀ (xs : List A) → Index xs
  → Σ[ xsˡ ∈ List⁺ A ] Σ[ xsʳ ∈ List A ]
      NE.length xsˡ + length xsʳ ≡ length xs
splitAt⁺ʳ (x ∷ xs) fzero    = x ∷ [] , xs , refl
splitAt⁺ʳ (x ∷ xs) (fsuc i) = let xsˡ , xsʳ , p = splitAt⁺ʳ xs i
                              in  x ∷⁺ xsˡ , xsʳ , cong suc p

private
  _ : splitAt⁺ʳ (0 ∷ 1 ∷ []) (# 0) ≡ ([ 0 ]⁺ , [ 1 ] , refl)
  _ = refl

  _ : splitAt⁺ʳ (0 ∷ 1 ∷ []) (# 1) ≡ (0 ∷ 1 ∷ [] , [] , refl)
  _ = refl

Token : Type
Token = Char

import Prelude.Set' as SET

module SETᶜ = SET {A = Char} _≟ᶜ_
Alphabet = Set' where open SETᶜ

Word : Type
Word = List Token

-- NB: words might be infinite, use Codata.Colist maybe?
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

infixr 8 _∙_
infixr 7 _∪_

_≺_ : Rel Word 0ℓ
_≺_ = _<_ on length

≺-wf : WellFounded _≺_
≺-wf = InverseImage.wellFounded length <-wellFounded

+-≺ : ∀ {x y z} → suc x + y ≡ z → y < z
+-≺ {x}{y}{z} refl = <-transˡ {i = y} {j = suc y} {k = suc x + y} (n<1+n y) (s≤s $ m≤n+m y x)

accept : Grammar Σ → Word → Type
accept {Σ = Σ} g w = go g _ (≺-wf w)
  where
    go : Grammar Σ → (w : Word) → Acc _≺_ w → Type
    go g w a₀@(acc a)
      with g
    ... | ∅       = ⊥
    ... | `ε      = w ≡ ε
    ... | I x _   = w ≡ [ x ]
    ... | g₁ ∪ g₂ = go g₁ w a₀ ⊎ go g₂ w a₀
    ... | g₁ ∙ g₂ = Σ[ i ∈ Fin (suc $ length w) ]
          let wˡ , wʳ = splitAt w i
          in go g₁ wˡ (≺-wf wˡ) × go g₂ wʳ (≺-wf wʳ)
    ... | g′ ⁺    = Σ[ i ∈ Index w ]
          let wˡ⁺ , wʳ , p = splitAt⁺ʳ w i
              wˡ = NE.toList wˡ⁺
          in  go g′ wˡ (≺-wf wˡ) ×
              ( go `ε wʳ (a _ (+-≺ p))
              ⊎ go (g′ ⁺) wʳ (a _ (+-≺ p)) )

              -- go (`ε ∪ (g′ ⁺)) wʳ (a _ (+-≺ p))
              -- go (g′ ⋆) wʳ (a _ (+-≺ p))
            -- NB: Agda fails termination checking if we do not inline _∪_

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


pattern ⟦_⇒ˡ_⇒ʳ_⟧ x l r = x , l , r

module Binary where

  -- data Σ⁰¹ : Set where
  --   `0 `1 : Σ⁰¹
  -- NB: Maybe have Alphabet as an abstract datatype (i.e. module parameter)

  Σ⁰¹ : Alphabet
  Σ⁰¹ = SETᶜ.fromList $ '0' ∷ '1' ∷ []

  G⁰ : Grammar Σ⁰¹
  G⁰ = I '0' (here refl)

  G¹ : Grammar Σ⁰¹
  G¹ = I '1' (there (here refl))

  -- (0 | 1((01)⋆0)⋆1)⋆ : binary numbers that are multiples of 3
  Bin3 : Grammar Σ⁰¹
  Bin3 = ( G⁰
         ∪ (G¹ ∙ ((((G⁰ ∙ G¹) ⋆) ∙ G⁰) ⋆) ∙ G¹)
         ) ⋆

  _ : accept Bin3 ('0' ∷ '0' ∷ '1' ∷ '1' ∷ '0' ∷ [])
  _ = -- 00110 ∈ G⋆
      inj₂
      -- 00110 ∈ G⁺
      ⟦ # 0 ⇒ˡ -- 0 ∈ G
               inj₁ refl
            ⇒ʳ -- 0110 ∈ G⋆
               inj₂
               -- 0110 ∈ G⁺
               ⟦ # 0 ⇒ˡ -- 0 ∈ G
                        inj₁ refl
                     ⇒ʳ -- 110 ∈ G⋆
                        inj₂
                        -- 110 ∈ G⁺
                        ⟦ # 1 ⇒ˡ -- 11 ∈ G
                                 inj₂ ⟦ # 1 ⇒ˡ -- 1 ∈ G¹
                                               refl
                                            ⇒ʳ -- 1 ∈ (⋯)⋆1
                                               ⟦ # 0 ⇒ˡ -- ε ∈ (⋯)⋆
                                                        inj₁ refl
                                                     ⇒ʳ -- 1 ∈ G¹
                                                        refl ⟧
                                      ⟧
                              ⇒ʳ -- 0 ∈ G⋆
                                 inj₂
                                 -- 0 ∈ G⁺
                                 ⟦ # 0 ⇒ˡ -- 0 ∈ G
                                          inj₁ refl
                                       ⇒ʳ -- ε ∈ G⋆
                                          inj₁ refl
                                 ⟧

                        ⟧
               ⟧
      ⟧

{- ** Generic languages, infinite vs finite

record Language (A : Set) : Set where
  field
    accept : A → Word → Type

open Language {{...}} public

instance
  Languageᵍ : Language Grammar
  Languageᵍ = record { accept = accept }

  Languageᵃ : Language DFA
  Languageᵃ = record { accept = accept }

_~_ : {{_ : Language A}} → Rel A 0ℓ
l ~ l′ = accept l ⇔ accept l′

record Language∞ (A : Set) : Set where
  field
    language : a → List∞ Word
    accept : (a : A) → (w : Word) → w ∈ language a

open Language∞ {{...}} public

instance
  Languageᵍ : Language∞ Grammar
  Languageᵍ = record { language = ?
                     ; accept   = accept }

  Languageᵃ : Language∞ DFA
  Languageᵃ = record { language = ?
                     ; accept   = accept }


_~_ : {{_ : Language∞ A}} → Rel A 0ℓ
l ~ l′ = accept l ⇔ accept l′

-- language : Grammar Σ → List∞ Word
-- accept : (G : Grammar Σ) → (w : Word) → w ∈ language G
-}

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
