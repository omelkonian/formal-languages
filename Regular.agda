open import Level    using (0ℓ)
open import Function using (_∘_; _$_; _on_)
open import Induction.WellFounded

open import Data.Nat     -- using (ℕ; suc; _+_; _<_; _≤_)
open import Data.Nat.Properties
open import Data.Nat.Induction using (<-wellFounded)

open import Data.List using (List; []; _∷_; [_]; map; _++_; concat; concatMap; zip; length; foldr)
open import Data.List.Membership.Propositional using (mapWith∈)
open import Data.List.NonEmpty as NE using (List⁺; _∷_; _∷⁺_)
  renaming ([_] to [_]⁺)
open import Data.List.Properties using (≡-dec)

open import Language hiding (_≺_; ≺-wf)

module Regular (Σ : Alphabet) where

splitAt : ∀ (xs : List A) → Fin (suc $ length xs) → List A × List A
splitAt xs       fzero    = [] , xs
splitAt (x ∷ xs) (fsuc i) = map₁ (x ∷_) (splitAt xs i)

splitAt⁺ʳ : ∀ (xs : List A) → Index xs
  → Σ[ xsˡ ∈ List⁺ A ] Σ[ xsʳ ∈ List A ]
      NE.length xsˡ + length xsʳ ≡ length xs
splitAt⁺ʳ (x ∷ xs) fzero    = x ∷ [] , xs , refl
splitAt⁺ʳ (x ∷ xs) (fsuc i) = let xsˡ , xsʳ , p = splitAt⁺ʳ xs i
                              in  x ∷⁺ xsˡ , xsʳ , cong suc p

private
  _ : splitAt⁺ʳ ⟦ 0 , 1 ⟧ (# 0) ≡ ([ 0 ]⁺ , [ 1 ] , refl)
  _ = refl

  _ : splitAt⁺ʳ ⟦ 0 , 1 ⟧ (# 1) ≡ (0 ∷ ⟦ 1 ⟧ , [] , refl)
  _ = refl

data Regex : Type where
  ∅ : Regex

  `ε : Regex

  I : (a : Token) → a ∈′ Σ → Regex

  _∪_ : Regex → Regex → Regex

  _∙_ : Regex → Regex → Regex

  _⁺ : Regex → Regex

⋃_ : List Regex → Regex
⋃_ = foldr _∪_ ∅

∀Σ : Regex
∀Σ = ⋃ mapWith∈ (list Σ) (I _)

len : ℕ → Regex
len 0 = `ε
len (suc n) = len n ∙ ∀Σ

_⋆ : Regex → Regex
g ⋆ = `ε ∪ (g ⁺)

infixr 8 _∙_
infixr 7 _∪_

_≺_ : Rel Word 0ℓ
_≺_ = _<_ on length

≺-wf : WellFounded _≺_
≺-wf = InverseImage.wellFounded length <-wellFounded

+-≺ : ∀ {x y z} → suc x + y ≡ z → y < z
+-≺ {x}{y}{z} refl = <-transˡ {i = y} {j = suc y} {k = suc x + y} (n<1+n y) (s≤s $ m≤n+m y x)

instance
  L-Regex : Language Regex
  L-Regex .accept g w = go g _ (≺-wf w)
   where
    go : Regex → (w : Word) → Acc _≺_ w → Type
    go g w a₀@(acc a)
      with g
    ... | ∅      = ⊥
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

pattern ⟦_⇒ˡ_⇒ʳ_⟧ x l r = x , l , r




{- ** Next Steps **

- Meta-theory of Regex
- Regular grammar ~ Regex
- (N)DFA ~ Regex
- Monoid homomorphism ~ Regex
⋮
- CFL
- 2-MCFL
⋮
- CSL
- Recursive function
- Turing



- (Generalization) Kleene Algebra

-}

{- NB: Complement and intersection are very hard (impossible?) to define via Regex
∁ : Regex → Regex
_∩_ : Regex → Regex → Regex

∁ ∅ = {! Σ ⋆!}
∁ `ε = {! ∅ ∪ Σ ⁺!}
∁ (I a x) = {! ...!}
∁ (g ∪ g₁) = {!∁ g ∩ ∁ g₁!}
∁ (g ∙ g₁) = {!(∁ g ∙ ∁ g₁) ⊎!}
∁ (g ⁺) = {!!}

g ∩ g′ = {!!} -- ∁ (∁ g ∪ ∁ g′)

private
  variable
    g g′ : Regex
    w : Word

_ : accept (g ∪ g′) w ≡ (accept g w ⊎ accept g′ w)
_ = refl

_ : accept (∁ g) w ≡ (¬ (accept g w))
_ = {!!}

_ : accept (g ∩ g′) w ≡ (accept g w × accept g′ w)
_ = {!!}


-}

{- ⊥⊥⊥⊥⊥⊥⊥⊥⊥⊥⊥⊥⊥ Cannot restrict to finite words ⊥⊥⊥⊥⊥⊥⊥⊥⊥⊥⊥⊥⊥
postulate
  LIMIT : ℕ
  finite : ∀ w ∈ Word. length w < LIMIT

_ : ∃ w. length w ≡ LIMIT
  × finite
  ⇒ ⊥
_ = repeat LIMIT '⅋' , length-repeat
  where
    length-repeat : length (repeat n) ≡ n

-}

-- {ww | w ∈ L}, is not regular?

{- ** Parse with two grammars for all pairs of split
_∩′_ : Regex → Regex → Regex
g₁ ∩′ g₂ =
... (g₁ ∩ len 1) ∙ g₂ ~ ∃[ i ≡ 0 ]
  ∩ (g₁ ∩ len 2) ∙ g₂ ~ ∃[ i ≡ 1 ]
  ∩ (g₁ ∩ len 3) ∙ g₂ ~ ∃[ i ≡ 2 ]
  ⋮        ⋮
  ∩ (g₁ ∩ len (LIMIT - 1)) ∙ g₂ ~ ∃[ i ≡ LIMIT > length w ]
  -- ∩ (g₁ ∩ len (length w) -1) ∙ g₂ ~ ∃[ i ≡ length w ]


-- which then leads to an implementation of ∁

                                                       ∩
                    ∀ (w₁,w₂ ~ w)          . w₁ ∈ ∁ g₁ × w₂ ∈ ∁ g₂
w ∈ ∁ (g₁ ∙ g₂) = ¬ ∃ (w₁,w₂ = splitAt i w). w₁ ∈ g₁   ⊎ w₂ ∈ g₂


                                                  g₁ ∪ g₂

-}

{- ** Generic languages, infinite vs finite

record Language (A : Set) : Set where
  field
    accept : A → Word → Type

open Language {{...}} public

instance
  Languageᵍ : Language Regex
  Languageᵍ = record { accept = accept }

  Languageᵃ : Language DFA
  Languageᵃ = record { accept = accept }

_~_ : {{_ : Language A}} → Rel A 0ℓ
l ~ l′ = accept l ⇔ accept l′
  -- LEFT: ∀ w. accept l w (DFA) → accept l′ w (Regex)
  -- RIGHT: ∀ w. accept l′ w → accept l w

DFA⇒Regex : (d : DFA) → ∃[ g ∈ Regex ] (d ~ g)

DFA⇒Regex d     ↝ g  , g~d
DFA⇒Regex (∁ d) ↝ g′ , g′~∁d


Regex⇒DFA : (g : Regex) → ∃[ d ∈ DFA ] (d ~ g)

∁-DFA : DFA → DFA

∁ : Regex → Regex
∁ = let d , d~g  = Regex⇒DFA g
    let ∁d       = ∁-DFA d
    let g′ , g~∁d = DFA⇒Regex ∁d
    in g′
  -- DFA⇒Regex ∘ ∁-DFA ∘ Regex⇒DFA

record Language∞ (A : Set) : Set where
  field
    language : a → List∞ Word
    accept : (a : A) → (w : Word) → w ∈ language a

open Language∞ {{...}} public

instance
  Languageᵍ : Language∞ Regex
  Languageᵍ = record { language = ?
                     ; accept   = accept }

  Languageᵃ : Language∞ DFA
  Languageᵃ = record { language = ?
                     ; accept   = accept }


_~_ : {{_ : Language∞ A}} → Rel A 0ℓ
l ~ l′ = accept l ⇔ accept l′

-- language : Regex → List∞ Word
-- accept : (G : Regex) → (w : Word) → w ∈ language G
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
--   weakening : ∀ {Σ' Σ ℓ} → Regex' ℓ → Σ' SETᶜ.⊆ Σ → Regex ℓ

{-


_ : a SETᶜ.∈ singleton a
_ = here refl

_ : a SETᶜ.∈ SETᶜ.fromList (b ∷ a ∷ [])
_ = there (here refl)

_ : a SETᶜ.∈ SETᶜ.fromList (c ∷ b ∷ a ∷ [])
_ = there (there (here refl))

JustA : Regex {a}
JustA = unit a (here refl)

Σ : Alphabet
Σ = {a, b}

MyLang : Regex ({ab} ⋆ℓ)
MyLang = a*|b*,

s : Word
s = "aaa"

_∈_ : Word → Regex → Type
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

σ : Regex → Alphabet
-}

{-
*** Parametrize words over alphabets

s : Word {a}
s = "aaa"

Word Σ

_∈_ : ∀ {pr : Σ' ⊆ Σ} → Word Σ' → Regex → Type
"a" ∈ {a} = true
"aa" ∈ {a} = false
w ∈ g


  -- data Σ⁰¹ : Set where
  --   `0 `1 : Σ⁰¹
  -- NB: Maybe have Alphabet as an abstract datatype (i.e. module parameter)
-}
