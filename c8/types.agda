open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Product using (_×_)
open import arith

-- Only two simple types in this toy language
data Type : Set where
  ℕ : Type
  𝔹 : Type

-- Typing relation is a binary relation between
-- terms and types
infix 4 _⦂_
data _⦂_ : 𝕋 → Type → Set where
  -- axioms
  ⊢zero  : zero ⦂ ℕ
  ⊢false : false ⦂ 𝔹
  ⊢true  : true ⦂ 𝔹

  -- compound rules
  ⊢suc    : ∀ {t} → t ⦂ ℕ → suc t ⦂ ℕ
  ⊢pred   : ∀ {t} → t ⦂ ℕ → pred t ⦂ ℕ
  ⊢iszero : ∀ {t} → t ⦂ ℕ → iszero t ⦂ 𝔹
  ⊢if     : ∀ {t₁ t₂ t₃ T} → t₁ ⦂ 𝔹 → t₂ ⦂ T → t₃ ⦂ T → if t₁ then t₂ else t₃ ⦂ T

-- Uniquess of types theorem
unique-type : ∀ {t T T'} → t ⦂ T → t ⦂ T' → T ≡ T'
unique-type ⊢zero ⊢zero = refl
unique-type ⊢false ⊢false = refl
unique-type ⊢true ⊢true = refl
unique-type (⊢suc t⦂T) (⊢suc t⦂T') = refl
unique-type (⊢pred t⦂T) (⊢pred t⦂T') = refl
unique-type (⊢iszero t⦂T) (⊢iszero t⦂T') = refl
unique-type (⊢if t⦂T t⦂T₁ t⦂T₂) (⊢if t⦂T' t⦂T'' t⦂T''') = unique-type t⦂T₁ t⦂T''

unique-derivation : ∀ {t T} → (p1 : t ⦂ T) → (p2 : t ⦂ T) → p1 ≡ p2
unique-derivation ⊢zero ⊢zero = refl
unique-derivation ⊢false ⊢false = refl
unique-derivation ⊢true ⊢true = refl
unique-derivation (⊢suc p1) (⊢suc p2) = cong ⊢suc (unique-derivation p1 p2)
unique-derivation (⊢pred p1) (⊢pred p2) = cong ⊢pred (unique-derivation p1 p2)
unique-derivation (⊢iszero p1) (⊢iszero p2) = cong ⊢iszero (unique-derivation p1 p2)
unique-derivation (⊢if p1 p3 p4) (⊢if p2 p5 p6) with
    unique-derivation p1 p2
  | unique-derivation p3 p5
  | unique-derivation p4 p6
... | refl | refl | refl = refl
