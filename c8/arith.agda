open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)

-- Inductive term definition from the book
data 𝕋 : Set where
  true   : 𝕋
  false  : 𝕋
  zero   : 𝕋
  suc    : 𝕋 → 𝕋
  pred   : 𝕋 → 𝕋
  iszero : 𝕋 → 𝕋
  if_then_else_ : 𝕋 → 𝕋 → 𝕋 → 𝕋

-- Inductive functions can be defined easily on an inductive definition of our terms

-- A rather weird and inefficient way
-- to define max but doesn't require any comparison
-- and suffices for the following depth function
max : ℕ → ℕ → ℕ
max zero n = n
max (suc m) zero = suc m
max (suc m) (suc n) = suc (max m n)

-- Corresponds to the amount of nodes of the abstract syntax tree
size : 𝕋 → ℕ
size true = 1
size false = 1
size zero = 1
size (suc t) = (size t) + 1
size (pred t) = (size t) + 1
size (iszero t) = (size t) + 1
size (if t then t₁ else t₂) = (size t) + (size t₁) + (size t₂) + 1

-- Corresponds to the first index of the set that the term appears in
-- within the constructive definition of our terms (see notes)
depth : 𝕋 → ℕ
depth true = 1
depth false = 1
depth zero = 1
depth (suc t) = depth t + 1
depth (pred t) = depth t + 1
depth (iszero t) = depth t + 1
depth (if t then t₁ else t₂) = max (max (depth t) (depth t₁)) (depth t₂) + 1

-- Small step semantics of the toy language
data NValue : 𝕋 → Set where
  V-zero : NValue zero
  V-suc  : ∀ {t} → NValue t → NValue (suc t)

data Value : 𝕋 → Set where
  V-true  : Value true
  V-false : Value false
  V-num   : ∀ {t} → NValue t → Value t

infix 4 _—→_
data _—→_ : 𝕋 → 𝕋 → Set where
  ξ-if     : ∀ {t t' t₁ t₂} → t —→ t' → if t then t₁ else t₂ —→ if t' then t₁ else t₂
  β-true   : ∀ {t₁ t₂} → if true then t₁ else t₂ —→ t₁
  β-false  : ∀ {t₁ t₂} → if false then t₁ else t₂ —→ t₂
  ξ-suc    : ∀ {t t'} → t —→ t' → suc t —→ suc t'
  ξ-pred   : ∀ {t t'} → t —→ t' → pred t —→ pred t'
  β-pred   : ∀ {t} → NValue t → pred (suc t) —→ t
  β-predz  : pred zero —→ zero
  ξ-iszero : ∀ {t t'} → t —→ t' → iszero t —→ iszero t'
  β-zero   : iszero zero —→ true
  β-nv     : ∀ {t} → NValue t → iszero (suc t) —→ false

-- We can now do proofs about our semantics

-- Evaluation is deterministic

-- Lemma: Values do not step
¬val—→t : ∀ {t t'} → Value t → ¬ (t —→ t')
¬val—→t V-true = λ{ ()}
¬val—→t V-false = λ{ ()}
¬val—→t (V-num V-zero) = λ{ ()}
¬val—→t (V-num (V-suc x)) = λ{ (ξ-suc x₁) → ¬val—→t (V-num x) x₁}

determinacy : ∀ {t t' t''} → t —→ t' → t —→ t'' → t' ≡ t'' 
determinacy (ξ-if {t₁ = t₁} {t₂} t—→t') (ξ-if t—→t'') = cong (λ x → if x then t₁ else t₂) (determinacy t—→t' t—→t'')
determinacy β-true β-true = refl
determinacy β-false β-false = refl
determinacy (ξ-suc t—→t') (ξ-suc t—→t'') = cong suc (determinacy t—→t' t—→t'')
determinacy (ξ-pred t—→t') (ξ-pred t—→t'') = cong pred (determinacy t—→t' t—→t'')
determinacy (ξ-pred t—→t') (β-pred x) = ⊥-elim (¬val—→t (V-num (V-suc x)) t—→t')
determinacy (β-pred x) (ξ-pred t—→t'') = ⊥-elim (¬val—→t (V-num (V-suc x)) t—→t'')
determinacy (β-pred x) (β-pred x₁) = refl
determinacy β-predz β-predz = refl
determinacy (ξ-iszero t—→t') (ξ-iszero t—→t'') = cong iszero (determinacy t—→t' t—→t'')
determinacy (ξ-iszero t—→t') (β-nv x) = ⊥-elim (¬val—→t (V-num (V-suc x)) t—→t')
determinacy β-zero β-zero = refl
determinacy (β-nv x) (ξ-iszero t—→t'') = ⊥-elim (¬val—→t (V-num (V-suc x)) t—→t'')
determinacy (β-nv x) (β-nv x₁) = refl

-------------------------------------------------------------------------------------------------------------------------------------------------

-- We can also define the transitive and reflexive closure
-- of our small step relation

infix 4 _—→*_
data _—→*_ : 𝕋 → 𝕋 → Set where
  —→*-refl : ∀ {t} → t —→* t
  —→*-step : ∀ {t t₁ t₂} → t —→ t₁ → t₁ —→* t₂ → t —→* t₂

-- The closure is transitive

—→*-trans : ∀ {t t₁ t₂} → t —→* t₁ → t₁ —→* t₂ → t —→* t₂
—→*-trans —→*-refl t₁—→*t₂ = t₁—→*t₂
—→*-trans (—→*-step x t—→*t₁) t₁—→*t₂ = —→*-step x (—→*-trans t—→*t₁ t₁—→*t₂)

-------------------------------------------------------------------------------------------------------------------------------------------------

-- Big-step semantics
data NValue' : Set where
  zero : NValue'
  suc  : NValue' → NValue'

data Value' : Set where
  num   : NValue' → Value'
  true  : Value'
  false : Value'

⌜_⌝ : NValue' → Value'
⌜ zero ⌝ = num zero
⌜ suc nv ⌝ = num (suc nv)

⌞_⌟ₙ : NValue' → 𝕋
⌞ zero ⌟ₙ = zero
⌞ suc nv ⌟ₙ = suc ⌞ nv ⌟ₙ

⌞_⌟ : Value' → 𝕋
⌞ num x ⌟ = ⌞ x ⌟ₙ
⌞ true ⌟ = true
⌞ false ⌟ = false

NV'→NV : ∀ (nv : NValue') → NValue ⌞ nv ⌟ₙ
NV'→NV zero = V-zero
NV'→NV (suc nv) = V-suc (NV'→NV nv)

infix 4 _⇓_
data _⇓_ : 𝕋 → Value' → Set where
  ⇓-zero       : zero ⇓ num zero
  ⇓-true       : true ⇓ true
  ⇓-false      : false ⇓ false
  ⇓-ifTrue     : ∀ {t₁ t₂ t₃ v₂} → t₁ ⇓ true → t₂ ⇓ v₂ → if t₁ then t₂ else t₃ ⇓ v₂
  ⇓-ifFalse    : ∀ {t₁ t₂ t₃ v₃} → t₁ ⇓ false → t₃ ⇓ v₃ → if t₁ then t₂ else t₃ ⇓ v₃
  ⇓-suc        : ∀ {t nv} → t ⇓ num nv →  suc t ⇓ (num (suc nv))
  ⇓-predZero   : ∀ {t} → t ⇓ num zero → pred t ⇓ num zero
  ⇓-predSuc    : ∀ {t nv} → t ⇓ num (suc nv) → pred t ⇓ num nv
  ⇓-isZeroZero : ∀ {t} → t ⇓ num zero → iszero t ⇓ true
  ⇓-isZeroSuc  : ∀ {t nv} → t ⇓ num (suc nv) → iszero t ⇓ false

-- Semantic equivalence can be shown

-- ⇓ to —→*
ξ-if₁* : ∀ {t₁ t₁' t₂ t₃} → t₁ —→* t₁' → if t₁ then t₂ else t₃ —→* if t₁' then t₂ else t₃
ξ-if₁* —→*-refl = —→*-refl
ξ-if₁* (—→*-step x t₁—→*t₁') = —→*-trans (—→*-step (ξ-if x) —→*-refl) (ξ-if₁* t₁—→*t₁')

ξ-suc* : ∀ {t t'} → t —→* t' → suc t —→* suc t'
ξ-suc* —→*-refl = —→*-refl
ξ-suc* (—→*-step x t—→*t') = —→*-trans (—→*-step (ξ-suc x) —→*-refl) (ξ-suc* t—→*t')

ξ-pred* : ∀ {t t'} → t —→* t' → pred t —→* pred t'
ξ-pred* —→*-refl = —→*-refl
ξ-pred* (—→*-step x t—→*t') = —→*-trans (—→*-step (ξ-pred x) —→*-refl) (ξ-pred* t—→*t')

β-pred* : ∀ {t} → t —→* zero → pred t —→* zero
β-pred* —→*-refl = —→*-step β-predz —→*-refl
β-pred* (—→*-step x t—→*z) = —→*-trans (—→*-step (ξ-pred x) —→*-refl) (β-pred* t—→*z)

ξ-iszero* : ∀ {t t'} → t —→* t' → iszero t —→* iszero t'
ξ-iszero* —→*-refl = —→*-refl
ξ-iszero* (—→*-step x t—→*t') = —→*-trans (—→*-step (ξ-iszero x) —→*-refl) (ξ-iszero* t—→*t')

β-true* : ∀ {t} → t —→* zero → iszero t —→* true
β-true* —→*-refl = —→*-step β-zero —→*-refl
β-true* (—→*-step x t—→*z) = —→*-trans (—→*-step (ξ-iszero x) —→*-refl) (β-true* t—→*z)

⇓-—→* : ∀ {t v} → t ⇓ v → t —→* ⌞ v ⌟
⇓-—→* ⇓-zero = —→*-refl
⇓-—→* ⇓-true = —→*-refl
⇓-—→* ⇓-false = —→*-refl
⇓-—→* (⇓-ifTrue t⇓v t⇓v₁) = —→*-trans (ξ-if₁* (⇓-—→* t⇓v)) (—→*-trans (—→*-step β-true —→*-refl) (⇓-—→* t⇓v₁))
⇓-—→* (⇓-ifFalse t⇓v t⇓v₁) = —→*-trans (ξ-if₁* (⇓-—→* t⇓v)) (—→*-trans (—→*-step β-false —→*-refl) (⇓-—→* t⇓v₁))
⇓-—→* (⇓-suc t⇓v) = —→*-trans (ξ-suc* (⇓-—→* t⇓v)) —→*-refl
⇓-—→* (⇓-predZero t⇓v) = β-pred* (⇓-—→* t⇓v) 
⇓-—→* (⇓-predSuc {nv = nv} t⇓v) = —→*-trans (ξ-pred* (⇓-—→* t⇓v)) (—→*-step (β-pred (NV'→NV nv)) —→*-refl)
⇓-—→* (⇓-isZeroZero t⇓v) = β-true* (⇓-—→* t⇓v)
⇓-—→* (⇓-isZeroSuc {nv = nv} t⇓v) = —→*-trans (ξ-iszero* (⇓-—→* t⇓v)) (—→*-step (β-nv (NV'→NV nv)) —→*-refl)

-- —→* to ⇓
⇓-refl-helper : ∀ {nv} → ⌞ nv ⌟ₙ ⇓ num nv
⇓-refl-helper {zero} = ⇓-zero
⇓-refl-helper {suc nv} = ⇓-suc ⇓-refl-helper

⇓-refl : ∀ {v} → ⌞ v ⌟ ⇓ v
⇓-refl {num x} = ⇓-refl-helper
⇓-refl {true} = ⇓-true
⇓-refl {false} = ⇓-false

val-lemma : ∀ {t} (nv : NValue t) → ∃[ V ] ( t ≡ ⌞ V ⌟ₙ)
val-lemma V-zero = zero , refl
val-lemma (V-suc nv) with val-lemma nv
... | fst , refl = (suc fst) , refl

—→-⇓-ext : ∀ {t t' v} → t —→ t' → t' ⇓ v → t ⇓ v
—→-⇓-ext β-true ⇓-zero = ⇓-ifTrue ⇓-true ⇓-zero
—→-⇓-ext β-false ⇓-zero = ⇓-ifFalse ⇓-false ⇓-zero
—→-⇓-ext (β-pred x) ⇓-zero = ⇓-predSuc (⇓-suc ⇓-zero)
—→-⇓-ext β-predz ⇓-zero = ⇓-predZero ⇓-zero
—→-⇓-ext β-true ⇓-true = ⇓-ifTrue ⇓-true ⇓-true
—→-⇓-ext β-false ⇓-true = ⇓-ifFalse ⇓-false ⇓-true
—→-⇓-ext β-zero ⇓-true = ⇓-isZeroZero ⇓-zero
—→-⇓-ext β-true ⇓-false = ⇓-ifTrue ⇓-true ⇓-false
—→-⇓-ext β-false ⇓-false = ⇓-ifFalse ⇓-false ⇓-false
—→-⇓-ext (β-nv x) ⇓-false with val-lemma x
... | fst , refl = ⇓-isZeroSuc (⇓-suc ⇓-refl)
—→-⇓-ext (ξ-if t—→t') (⇓-ifTrue t'⇓v t'⇓v₁) = ⇓-ifTrue (—→-⇓-ext t—→t' t'⇓v) t'⇓v₁
—→-⇓-ext β-true (⇓-ifTrue t'⇓v t'⇓v₁) = ⇓-ifTrue ⇓-true (⇓-ifTrue t'⇓v t'⇓v₁)
—→-⇓-ext β-false (⇓-ifTrue t'⇓v t'⇓v₁) = ⇓-ifFalse ⇓-false (⇓-ifTrue t'⇓v t'⇓v₁)
—→-⇓-ext (ξ-if t—→t') (⇓-ifFalse t'⇓v t'⇓v₁) = ⇓-ifFalse (—→-⇓-ext t—→t' t'⇓v) t'⇓v₁
—→-⇓-ext β-true (⇓-ifFalse t'⇓v t'⇓v₁) = ⇓-ifTrue ⇓-true (⇓-ifFalse t'⇓v t'⇓v₁)
—→-⇓-ext β-false (⇓-ifFalse t'⇓v t'⇓v₁) = ⇓-ifFalse ⇓-false (⇓-ifFalse t'⇓v t'⇓v₁)
—→-⇓-ext β-true (⇓-suc t'⇓v) = ⇓-ifTrue ⇓-true (⇓-suc t'⇓v)
—→-⇓-ext β-false (⇓-suc t'⇓v) = ⇓-ifFalse ⇓-false (⇓-suc t'⇓v)
—→-⇓-ext (ξ-suc t—→t') (⇓-suc t'⇓v) = ⇓-suc (—→-⇓-ext t—→t' t'⇓v)
—→-⇓-ext (β-pred x) (⇓-suc t'⇓v) = ⇓-predSuc (⇓-suc (⇓-suc t'⇓v))
—→-⇓-ext β-true (⇓-predZero t'⇓v) = ⇓-ifTrue ⇓-true (⇓-predZero t'⇓v)
—→-⇓-ext β-false (⇓-predZero t'⇓v) = ⇓-ifFalse ⇓-false (⇓-predZero t'⇓v)
—→-⇓-ext (ξ-pred t—→t') (⇓-predZero t'⇓v) = ⇓-predZero (—→-⇓-ext t—→t' t'⇓v)
—→-⇓-ext β-true (⇓-predSuc t'⇓v) = ⇓-ifTrue ⇓-true (⇓-predSuc t'⇓v)
—→-⇓-ext β-false (⇓-predSuc t'⇓v) = ⇓-ifFalse ⇓-false (⇓-predSuc t'⇓v)
—→-⇓-ext (ξ-pred t—→t') (⇓-predSuc t'⇓v) = ⇓-predSuc (—→-⇓-ext t—→t' t'⇓v)
—→-⇓-ext β-true (⇓-isZeroZero t'⇓v) = ⇓-ifTrue ⇓-true (⇓-isZeroZero t'⇓v)
—→-⇓-ext β-false (⇓-isZeroZero t'⇓v) = ⇓-ifFalse ⇓-false (⇓-isZeroZero t'⇓v)
—→-⇓-ext (ξ-iszero t—→t') (⇓-isZeroZero t'⇓v) = ⇓-isZeroZero (—→-⇓-ext t—→t' t'⇓v)
—→-⇓-ext β-true (⇓-isZeroSuc t'⇓v) = ⇓-ifTrue ⇓-true (⇓-isZeroSuc t'⇓v)
—→-⇓-ext β-false (⇓-isZeroSuc t'⇓v) = ⇓-ifFalse ⇓-false (⇓-isZeroSuc t'⇓v)
—→-⇓-ext (ξ-iszero t—→t') (⇓-isZeroSuc t'⇓v) = ⇓-isZeroSuc (—→-⇓-ext t—→t' t'⇓v)

—→*-⇓ : ∀ {t v} → t —→* ⌞ v ⌟ → t ⇓ v
—→*-⇓ —→*-refl = ⇓-refl
—→*-⇓ (—→*-step x t—→*v) = —→-⇓-ext x (—→*-⇓ t—→*v)
