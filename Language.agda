module Language where

open import Function public

open import Data.Empty using (⊥) public
open import Data.Unit  using (⊤; tt) public
open import Data.Bool  using (Bool; true; false) public
open import Data.Char  using (Char) public
open import Data.Maybe using (Maybe; just; nothing) public
open import Data.Nat   using (ℕ; suc; zero) public
open import Data.Fin   using (Fin; #_) public
  renaming (suc to fsuc; zero to fzero)
open import Data.List

open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax; Σ-syntax; map₁; map₂) public
open import Data.Sum using (_⊎_; inj₁; inj₂) public
open import Data.List.Relation.Unary.Any using (Any; here; there) public

open import Relation.Nullary using (¬_) public
open import Relation.Unary using (Pred) public
open import Relation.Binary using (Rel) public
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong) public

open import Prelude.Lists public
open import Prelude.DecEq public
open import Prelude.Measurable public
open import Prelude.Set'  hiding (∅; _∪_) public

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
