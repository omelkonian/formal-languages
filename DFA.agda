{-# OPTIONS --allow-unsolved-metas #-}
open import Language

open import Data.Fin using (inject₁)
open import Data.List.Membership.Propositional.Properties

open import Prelude.Init hiding (_⇔_)
open L.NE using (snocView; _∷ʳ′_)
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Functor
open import Prelude.Bifunctor
open import Prelude.Set'

module DFA (Σ : Alphabet) where

view-mid : List⁺ A → (A × List A × A)
view-mid xs⁺@(h ∷ _) with snocView xs⁺
... | xs ∷ʳ′ l = h , drop 1 xs , l

record DFA (S : Type) {{_ : DecEq S}} : Type where
  field
    Q  : Set⟨ S ⟩
    -- Σ  : Alphabet
    δ  : S → Token → Maybe S
    Q₀ : ∃ (_∈′ Q)
    -- q₀ : S
    -- q₀∈
    F  : ∃ (_⊆′ Q)

  q₀ = proj₁ Q₀
  fs = proj₁ F

  Δ : S → Word → Maybe (List⁺ S)
  Δ s ε       = just (s ∷ [])
  Δ s (α ∷ w) with δ s α
  ... | nothing = nothing
  ... | just s′ = s ∷⁺_ <$> Δ s′ w

  δ̂ : Word → Maybe S
  δ̂ = (L.NE.last <$>_) ∘ Δ q₀

  Δᵢⱼᵏ : List S → S → S → Word → Type
  Δᵢⱼᵏ Q i j = M.Any.Any P ∘ Δ i
    where
      P : Pred (List⁺ S) 0ℓ
      P ss⁺ = let h , m , l = view-mid ss⁺
              in  (h ≡ i) × (m ⊆ Q) × (l ≡ j)

  isFinal : S → Type
  isFinal = _∈′ fs

open DFA public

-- Example DFA
-- _ : DFA 0|1
-- _ = ?

∁ : ∀ {S} {{_ : DecEq S}} → DFA S → DFA S
∁ record {Q = Q; δ = δ; Q₀ = Q₀; F = (F , F⊆)} =
  record {Q = Q; δ = δ; Q₀ = Q₀; F = (Q ─ F , ∈-─ {xs = Q} {ys = F})}

{-
data Accept : DFA S → Word → Type where
  [δ] : ∀ {w s dfa} → δ̂ dfa w ≡ just s → s ∈′ fs dfa → Accept dfa w
-}

instance
  L-DFA : ∀ {S} {{_ : DecEq S}} → Language (DFA S)
  L-DFA .accept dfa w = ∃ λ s → (δ̂ dfa w ≡ just s) × (isFinal dfa s)

-- To/from Regex
open import Regular Σ

-- Regex properties
⋃-intro : ∀ {w rs r} → r ∈ rs → accept r w → accept (`⋃ rs) w
⋃-intro = {!!}

⋃-elim : ∀ {w rs} → accept (`⋃ rs) w → ∃ λ r → (r ∈ rs) × (accept r w)
⋃-elim = {!!}


DFA⇒Regex : ∀ {S} {{_ : DecEq S}} → (dfa : DFA S) → Σ[ r ∈ Regex ] (dfa ~ r)
-- dfa → ∃ r. dfa ~ r
DFA⇒Regex {S = S} dfa@(record { Q = ⟨ Q ⟩∶- _ ; δ = δ ; Q₀ = Q₀ , _ ; F = ⟨ F ⟩∶- _ , _ }) =
  r , dfa~r
  where
    p : ∀ {f} → f ∈ F → (w : Word) → Δᵢⱼᵏ dfa Q Q₀ f w ≡ accept dfa w
    p = {!!}

    -- R _ i j ~ (dfa // i↝j)
    -- R _ i j ~ δ̂
    R : List S → S → S → Regex
    -- Rᵢⱼ⁰
    -- ^ k = 0 (all states > 1)
    R [] i j
      = let αs  = filter (λ α → δ i α ≟ just j) (list Σ)
            Rᵢⱼ = `⋃ mapWith∈ αs (I _ ∘ proj₁ ∘ ∈-filter⁻ _)
        in (if i == j then `ε else `∅) `∪ Rᵢⱼ
    -- Rᵢⱼᵏ = Rᵢⱼᵏ⁻¹ ∪ (Rᵢₖᵏ⁻¹ ∙ Rₖₖᵏ⁻¹ ⋆ ∙ Rₖⱼᵏ⁻¹)
    -- ^ (reverse Q ‼ k:ℕ) = k:S
    R (k ∷ q) i j =
      R q i j `∪ (R q i k ∙ R q k k ⋆ ∙ R q k j)

    R≡ : (Q : List S) → (i : S) → (j : S)
       → Δᵢⱼᵏ dfa Q i j ⇔ accept (R Q i j)
    R≡ [] i j w = l , r
      where
        l : Δᵢⱼᵏ dfa [] i j w → accept (R [] i j) w
        l p with Δ dfa i w | p
        ... | nothing | ()
        ... | just l  | M.Any.Any.just (h≡i , m⊆[] , l≡j)
            -- m⊆[] ⇒ m ≡ [] ⇒ (l≡[] | l≡[α])
            --                [∪ˡ] ε | [∪ʳ] ... (⁇ δ i α ≡ just j ⁇)
            = {!!}

        r : accept (R [] i j) w → Δᵢⱼᵏ dfa [] i j w
        r = {!!}


    R≡ (k ∷ q) i j = {!!}

{-

** base **
Δ′ dfa [] i j ⇔ accept ((ε|∅) ∪ a₀ ∪ a₁ ∪ ⋯)

l = []
l = [ i ]
l = [ i , j ]

Δ′ dfa [] i j → accept ((ε|∅) ∪ a₀ ∪ a₁ ∪ ⋯)

Δ′ dfa [] i j ← accept ((ε|∅) ∪ a₀ ∪ a₁ ∪ ⋯)

  1) i ≡ j

  Δ′ dfa [] i ⇔ accept (ε ∪ Rᵢⱼ)

  2) i ≢ j

  Δ′ dfa [] i ⇔ accept (∅ ∪ Rᵢⱼ)

** step **
Δ′ dfa (k ∷ q) i j ⇔ accept (R q i j ∪ (R q i k ∙ R q k k ⋆ ∙ R q k j))
                   ≈ accept R q i j  ⊎ accept (R q i k ∙ R q k k ⋆ ∙ R q k j))
                   ≈ accept R q i j  ⊎ (accept R q i k ... accept R Q k k ... accept R q k j)



                         Δ q i j     ⊎ ..      Δ q i k ∙ Δ q k k ⋆ ∙ Δ q k j

-}


{-
  → Δ (k ∷ q) k k w
  → ws -partitions- w
  → All (Δ q k k) ws

  → ws -partitions- w
  → All (Δ q k k) ws
  → All (R q k k) ws

  → ws -partitions- w
  → All (R q k k) ws
  → (R q k k ⋆) w

(Δ′ (k ∷ q) i j) w
  ↝ s₀⋯sₙ

  -- 1. k ∉ s₀⋯sₙ
  Δ′ q i j ≈ R q i j

  -- 2. k ∈ s₀⋯sₙ

    ⇒ Δ q i k × Δ (k ∷ q) k k × Δ q k j
                  Δ q k k ⋆
                  R q k k ⋆

Δ⋆ :
Δ⋆ Q x y =

Δ′ (k ∷ q) i j ≈ Δ′ q i j ⊎ ...
          R Q x y         R Q y z       (R Q x y ∙ R Q y z)
_∙_ : (Δ′ Q x y w₁) → (Δ′ Q y z w₂) → Δ′ Q x z (w₁ ++ w₂)

_⁺ : (Δ′ Q x x w₁) → Δ′ Q x x ε


_∪_

ε
_⋆ : Δ′ Q x x w
   → Δ′ Q x x (replicate n w)


→ Δ′ Q x x ε

Δ∙ : Q x y z → Type
-- Δ Q x y ∙ Δ Q y z
Δ∙ Q x y z =
  ∃ λ w → (w ≡ w₁ ++ w₂)
        × Δ′ Q x y w₁  ≈ R Q x y
        × Δ′ Q y z w₂  ≈ R Q y z


Δ⋆ :
Δ⋆ Q k =
  ∃ λ w → (w ≡ w₁ ++ w₂)
        × Δ′ Q k k w₁ ≈ R Q k k  }- (R Q k k)⋆
        × Δ⋆ Q k k w₂ ≈ ...      }-




-}

    R-δ̂ : ∀ {f} → f ∈ F → accept dfa ⇔ accept (R Q Q₀ f)
    R-δ̂ {f} f∈ w rewrite sym (p f∈ w) = R≡ Q Q₀ f w

    r : Regex
    r = `⋃ (R Q Q₀ <$> F)

    dfa~r : dfa ~ r
    dfa~r w = p₁ , p₂
      where
        p₁ : accept dfa w → accept r w
        p₁ w∈@(_ , _ , f∈) = ⋃-intro (∈-map⁺ (R Q Q₀) f∈) ((proj₁ $ R-δ̂ f∈ w) w∈)

        p₂ : accept r w → accept dfa w
        p₂ w∈rs = let r , r∈ , w∈r = ⋃-elim w∈rs
                      f , f∈ , r≡  = ∈-map⁻ (R Q Q₀) r∈
                  in  (proj₂ $ R-δ̂ {f = f} f∈ w) (subst (flip accept w) r≡ w∈r)

-- _ : proj₁ (DFA⇒Regex dfa)


-- DFA⇒Regex′ : ∀ {S} {{_ : DecEq S}} → (dfa : DFA S) → (dfa ~ DFA⇒Regex dfa)
-- DFA⇒Regex′ dfa = {!!}


-- Regex⇒DFA : Regex → DFA
{-
  ⋃ concatMap (λ f → map (R (q₀ , f)) (enumerate q)) (list fs)
  -- T0D0: find out a recursion principle on lists along with their (relative) indices
  where
    R : ∀ {q = q} → S × S → Index q × S → Regex
    R {q = []} =
      let αs  = filter (λ α → δ i α ≟ just j) (list Σ)
          Rᵢⱼ = ⋃ mapWith∈ αs (I _ ∘ proj₁ ∘ ∈-filter⁻ _)
      in if i == j then
        `ε ∪ Rᵢⱼ
      else
        Rᵢⱼ
    R {q = sₖ ∷ ss} (i , j) (k , sₖ) = {!!}
    R {q = x ∷ x₁ ∷ q} (i , j) (k , sₖ) = {!k!}
-}

{-
    R : ∀ {q} → Index q × S → S → S → Regex
    -- ** base
    R (fzero , _) i j =
      let αs  = filter (λ α → δ i α ≟ just j) (list Σ)
          Rᵢⱼ = ⋃ mapWith∈ αs (I _ ∘ proj₁ ∘ ∈-filter⁻ _)
      in if i == j then
        `ε ∪ Rᵢⱼ
      else
        Rᵢⱼ
    -- ** step
    R {q = .sₖ ∷ q} (fsuc k , sₖ) i j =
      let Rᵢⱼᵏ⁻¹ = R (inject₁ k) i j
          Rᵢₖᵏ⁻¹ = R (inject₁ k) i sₖ
          Rₖₖᵏ⁻¹ = R (inject₁ k) sₖ sₖ
          Rₖⱼᵏ⁻¹ = R (inject₁ k) sₖ j
      in Rᵢⱼᵏ⁻¹ ∪ (Rᵢₖᵏ⁻¹ ∙ Rₖₖᵏ⁻¹ ⋆ ∙ Rₖⱼᵏ⁻¹)
-}

{-
  -- Stage 0
  R⁰


  -- Stage 1
  R¹


  -- Stage 2
  R²




  ⋮


  -- Stage n
  Rⁿ

  ⇒ Rⁿ(q₀↦f₀) ∪ Rⁿ(q₀↦f₁) ∪ ⋯
-}
