open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥; ⊥-elim)
open import arith
open import types

-- Progess + Preservation = Type Safety (Soundness)

-- Progress theorem
data Progress (t : 𝕋) : Set where
  isValue : Value t → Progress t
  canStep : ∀ {t'} → t —→ t' → Progress t

can-forms-nat : ∀ {t} → t ⦂ ℕ → Value t → NValue t
can-forms-nat ⊢zero (V-num x) = V-zero
can-forms-nat (⊢suc t⦂ℕ) (V-num (V-suc x)) = V-suc x
can-forms-nat (⊢pred t⦂ℕ) (V-num ())
can-forms-nat (⊢if t⦂ℕ t⦂ℕ₁ t⦂ℕ₂) (V-num ())

lemma : ∀ {t} → t ⦂ 𝔹 → ¬ NValue t
lemma ⊢false = λ{ ()}
lemma ⊢true = λ{ ()}
lemma (⊢iszero t⦂𝔹) = λ{ ()}
lemma (⊢if t⦂𝔹 t⦂𝔹₁ t⦂𝔹₂) = λ{ ()}

can-forms-bool : ∀ {t} → t ⦂ 𝔹 → Value t → t ≡ true ⊎ t ≡ false
can-forms-bool t⦂𝔹 V-true = inj₁ refl
can-forms-bool t⦂𝔹 V-false = inj₂ refl
can-forms-bool t⦂𝔹 (V-num x) = ⊥-elim (lemma t⦂𝔹 x)

progress : ∀ {t T} → t ⦂ T → Progress t
progress ⊢zero = isValue (V-num V-zero)
progress ⊢false = isValue V-false
progress ⊢true = isValue V-true
progress (⊢suc t⦂T) with progress t⦂T
... | isValue v = isValue (V-num (V-suc (can-forms-nat t⦂T v)))
... | canStep t' = canStep (ξ-suc t')
progress (⊢pred t⦂T) with progress t⦂T
... | isValue (V-num V-zero) = canStep β-predz
... | isValue (V-num (V-suc v)) = canStep (β-pred v)
... | canStep t' = canStep (ξ-pred t')
progress (⊢iszero t⦂T) with progress t⦂T
... | canStep t' = canStep (ξ-iszero t')
... | isValue v with can-forms-nat t⦂T v
... | V-zero = canStep β-zero
... | V-suc p = canStep (β-nv p)
progress (⊢if t⦂T t⦂T₁ t⦂T₂) with progress t⦂T
... | canStep t' = canStep (ξ-if t')
... | isValue v with can-forms-bool t⦂T v
... | inj₁ refl = canStep β-true
... | inj₂ refl = canStep β-false

-- Preservation theorem
preservation : ∀ {t t' T} → t ⦂ T → t —→ t' → t' ⦂ T
preservation (⊢suc t⦂T) (ξ-suc t—→t') = ⊢suc (preservation t⦂T t—→t')
preservation (⊢pred t⦂T) (ξ-pred t—→t') = ⊢pred (preservation t⦂T t—→t')
preservation (⊢pred (⊢suc t⦂T)) (β-pred x) = t⦂T
preservation (⊢pred t⦂T) β-predz = ⊢zero
preservation (⊢iszero t⦂T) (ξ-iszero t—→t') = ⊢iszero (preservation t⦂T t—→t')
preservation (⊢iszero t⦂T) β-zero = ⊢true
preservation (⊢iszero t⦂T) (β-nv x) = ⊢false
preservation (⊢if t⦂T t⦂T₁ t⦂T₂) (ξ-if t—→t') = ⊢if (preservation t⦂T t—→t') t⦂T₁ t⦂T₂
preservation (⊢if t⦂T t⦂T₁ t⦂T₂) β-true = t⦂T₁
preservation (⊢if t⦂T t⦂T₁ t⦂T₂) β-false = t⦂T₂
