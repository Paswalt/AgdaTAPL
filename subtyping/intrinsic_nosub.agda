open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; []; _∷_; lookup)

-- Fin n stands for the set {0,...,n-1} and helps to represent
-- variables in an intrinsically scoped way. This way we have to
-- write seperate type-preservation proofs for our definitions again
-- but can write out terms and types seperately. It also allows us to
-- omit names. We index Terms with ℕ to talk about the amount of free
-- variables inside a term
data Term (n : ℕ) : Set where
  `_    : Fin n → Term n
  ƛ_    : Term (suc n) → Term n 
  _·_   : Term n → Term n → Term n
  ⟨_,_⟩ : Term n → Term n → Term n
  π₁_   : Term n → Term n
  π₂_   : Term n → Term n
    
infixr 5 _⇒_
infixr 5 _×_
data Type : Set where
  top  : Type -- Used for subtyping
  _⇒_ : Type → Type → Type
  _×_ : Type → Type → Type

data Value {n : ℕ} : Term n → Set where
  V-ƛ : ∀ {t : Term (suc n)} → Value (ƛ t)
  V-× : ∀ {t₁ t₂} → Value t₁ → Value t₂ → Value (⟨ t₁ , t₂ ⟩)

-- Contexts are now just finite vectors of types
Ctx : ℕ → Set
Ctx n = Vec Type n

infix 4 _⊢_⦂_
data _⊢_⦂_ {n : ℕ} (Γ : Ctx n) : Term n → Type → Set where
  ⊢`  : ∀ {x A} → lookup Γ x ≡ A → Γ ⊢ ` x ⦂ A
  ⊢λ  : ∀ {t : Term (suc n)} {A B : Type} → (A ∷ Γ) ⊢ t ⦂ B → Γ ⊢ ƛ t ⦂ A ⇒ B
  ⊢·  : ∀ {t₁ t₂ A B} → Γ ⊢ t₁ ⦂ A ⇒ B → Γ ⊢ t₂ ⦂ A → Γ ⊢ t₁ · t₂ ⦂ B
  ⊢⟨⟩ : ∀ {t₁ t₂ A B} → Γ ⊢ t₁ ⦂ A → Γ ⊢ t₂ ⦂ B → Γ ⊢ ⟨ t₁ , t₂ ⟩ ⦂ A × B
  ⊢π₁ : ∀ {t A B} → Γ ⊢ t ⦂ A × B → Γ ⊢ π₁ t ⦂ A
  ⊢π₂ : ∀ {t A B} → Γ ⊢ t ⦂ A × B → Γ ⊢ π₂ t ⦂ B


-- Substitution + sub preservation
_⇒ᵣ_ : ℕ → ℕ → Set
n ⇒ᵣ m = Fin n → Fin m

extr : ∀ {n m} → n ⇒ᵣ m → (suc n) ⇒ᵣ (suc m)
extr ρ zero = zero
extr ρ (suc fn) = suc (ρ fn)

ren : ∀ {n m} → n ⇒ᵣ m → (Term n → Term m)
ren ρ (` x) = ` ρ x
ren ρ (ƛ t) = ƛ (ren (extr ρ) t)
ren ρ (t · t₁) = (ren ρ t) · ren ρ t₁
ren ρ ⟨ t , t₁ ⟩ = ⟨ (ren ρ t) , (ren ρ t₁) ⟩
ren ρ (π₁ t) = π₁ (ren ρ t)
ren ρ (π₂ t) = π₂ (ren ρ t)

_⇒ₛ_ : ℕ → ℕ → Set
n ⇒ₛ m = Fin n → Term m

exts : ∀ {n m} → n ⇒ₛ m → (suc n) ⇒ₛ (suc m)
exts σ zero = ` zero
exts σ (suc fn) = ren suc (σ fn)

sub : ∀ {n m} → n ⇒ₛ m → (Term n → Term m)
sub σ (` x) = σ x
sub σ (ƛ t) = ƛ (sub (exts σ) t)
sub σ (t · t₁) = (sub σ t) · (sub σ t₁)
sub σ ⟨ t , t₁ ⟩ = ⟨ (sub σ t) , sub σ t₁ ⟩
sub σ (π₁ t) = π₁ (sub σ t)
sub σ (π₂ t) = π₂ (sub σ t)

_[_] : ∀ {m} → Term (suc m) → Term m → Term m
M [ N ] = sub (λ{ zero → N ; (suc x) → ` x}) M

-- Evaluation
infix 4 _—→_
data _—→_ {n : ℕ} : Term n → Term n → Set where
  ξ-·₁  : ∀ {t₁ t₁' t₂} → t₁ —→ t₁' → t₁ · t₂ —→ t₁' · t₂
  ξ-·₂  : ∀ {v t₂ t₂' } → t₂ —→ t₂' → Value v → v · t₂ —→ v · t₂'
  β-λ   : ∀ {t v} → Value v → (ƛ t) · v —→ t [ v ]
  ξ-π₁  : ∀ {t t'} → t —→ t' → π₁ t —→ π₁ t'
  ξ-π₂  : ∀ {t t'} → t —→ t' → π₂ t —→ π₂ t'
  ξ-⟨⟩₁ : ∀ {t₁ t₁' t₂} → t₁ —→ t₁' → ⟨ t₁ , t₂ ⟩ —→ ⟨ t₁' , t₂ ⟩
  ξ-⟨⟩₂ : ∀ {v t₂ t₂'} → t₂ —→ t₂' → Value v → ⟨ v , t₂ ⟩ —→ ⟨ v , t₂' ⟩
  β-π₁ : ∀ {v₁ v₂} → Value v₁ → Value v₂ → π₁ (⟨ v₁ , v₂ ⟩) —→ v₁
  β-π₂ : ∀ {v₁ v₂} → Value v₁ → Value v₂ → π₂ (⟨ v₁ , v₂ ⟩) —→ v₂

-- Progress + Preservation
data Progress {n : ℕ} (t : Term n) : Set where
  isValue : Value t → Progress t
  canStep : ∀ {t'} → t —→ t' → Progress t

progress : ∀ {t A} → [] ⊢ t ⦂ A → Progress t
progress (⊢λ ⊢A) = isValue V-ƛ
progress (⊢· ⊢A ⊢A₁) with progress ⊢A
... | canStep t—→t' = canStep (ξ-·₁ t—→t')
... | isValue v₁ with progress ⊢A₁
... | canStep t₂—→t₂' = canStep (ξ-·₂ t₂—→t₂' v₁)
progress (⊢· ⊢A ⊢A₁) | isValue V-ƛ | isValue v₂ = canStep (β-λ v₂)
progress (⊢⟨⟩ ⊢A ⊢A₁) with progress ⊢A
... | canStep t—→t' = canStep (ξ-⟨⟩₁ t—→t')
... | isValue v with progress ⊢A₁
... | canStep t₂—→t₂' = canStep (ξ-⟨⟩₂ t₂—→t₂' v)
... | isValue v₂ = isValue (V-× v v₂)
progress (⊢π₁ ⊢A) with progress ⊢A
... | isValue (V-× vt vt') = canStep (β-π₁ vt vt')
... | canStep t—→t' = canStep (ξ-π₁ t—→t')
progress (⊢π₂ ⊢A) with progress ⊢A
... | isValue (V-× vt vt') = canStep (β-π₂ vt vt')
... | canStep t—→t'  = canStep (ξ-π₂ t—→t')

--σ fn ⦂ lookup Γ fn
_⦂_⇒ₛ_ : ∀ {n m} → n ⇒ₛ m → (Γ : Ctx n) → (Δ : Ctx m) → Set
σ ⦂ Γ ⇒ₛ Δ = ∀ x → Δ ⊢ σ x ⦂ lookup Γ x

_⦂_⇒ᵣ_ : ∀ {n m} → n ⇒ᵣ m → Ctx n → Ctx m → Set
ρ ⦂ Γ ⇒ᵣ Δ = ∀ x → Δ ⊢ ` ρ x ⦂ lookup Γ x

extr-pres-lemma : ∀ {n} {Γ : Ctx n} {x A B} → Γ ⊢ ` x ⦂ B → (A ∷ Γ) ⊢ ` suc x ⦂ B  
extr-pres-lemma (⊢` refl) = ⊢` refl

extr-pres : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {ρ A} → ρ ⦂ Γ ⇒ᵣ Δ → extr ρ ⦂ (A ∷ Γ) ⇒ᵣ (A ∷ Δ)
extr-pres ⊢ρ zero = ⊢` refl
extr-pres ⊢ρ (suc fn) = extr-pres-lemma (⊢ρ fn)

ren-pres : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {ρ t A} → ρ ⦂ Γ ⇒ᵣ Δ → Γ ⊢ t ⦂ A → Δ ⊢ ren ρ t ⦂ A 
ren-pres ⊢ρ (⊢` {x = x} refl) = ⊢ρ x
ren-pres ⊢ρ (⊢λ ⊢A) = ⊢λ (ren-pres (extr-pres ⊢ρ) ⊢A)
ren-pres ⊢ρ (⊢· ⊢A ⊢A₁) = ⊢· (ren-pres ⊢ρ ⊢A) (ren-pres ⊢ρ ⊢A₁)
ren-pres ⊢ρ (⊢⟨⟩ ⊢A ⊢A₁) = ⊢⟨⟩ (ren-pres ⊢ρ ⊢A) (ren-pres ⊢ρ ⊢A₁)
ren-pres ⊢ρ (⊢π₁ ⊢A) = ⊢π₁ (ren-pres ⊢ρ ⊢A)
ren-pres ⊢ρ (⊢π₂ ⊢A) = ⊢π₂ (ren-pres ⊢ρ ⊢A)

exts-pres : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {σ A} → σ ⦂ Γ ⇒ₛ Δ → exts σ ⦂ (A ∷ Γ) ⇒ₛ (A ∷ Δ)   
exts-pres ⊢σ zero = ⊢` refl
exts-pres ⊢σ (suc fn) = ren-pres (λ{ zero → ⊢` refl ; (suc x) → ⊢` refl}) (⊢σ fn)

sub-pres : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {t A σ} →  σ ⦂ Γ ⇒ₛ Δ → Γ ⊢ t ⦂ A → Δ ⊢ sub σ t ⦂ A
sub-pres ⊢σ (⊢` {x = x} refl) = ⊢σ x
sub-pres {n} {m} {Γ} {Δ} {t} {σ} ⊢σ (⊢λ ⊢A) = ⊢λ (sub-pres (exts-pres ⊢σ) ⊢A)
sub-pres ⊢σ (⊢· ⊢A ⊢A₁) = ⊢· (sub-pres ⊢σ ⊢A) (sub-pres ⊢σ ⊢A₁)
sub-pres ⊢σ (⊢⟨⟩ ⊢A ⊢A₁) = ⊢⟨⟩ (sub-pres ⊢σ ⊢A) (sub-pres ⊢σ ⊢A₁)
sub-pres ⊢σ (⊢π₁ ⊢A) = ⊢π₁ (sub-pres ⊢σ ⊢A)
sub-pres ⊢σ (⊢π₂ ⊢A) = ⊢π₂ (sub-pres ⊢σ ⊢A)

sr : ∀ {n} {Γ : Ctx n} {t t' A} → Γ ⊢ t ⦂ A → t —→ t' → Γ ⊢ t' ⦂ A
sr (⊢· ⊢A ⊢A₁) (ξ-·₁ t—→t') = ⊢· (sr ⊢A t—→t') ⊢A₁
sr (⊢· ⊢A ⊢A₁) (ξ-·₂ t—→t' x) = ⊢· ⊢A (sr ⊢A₁ t—→t')
sr (⊢· (⊢λ ⊢A) ⊢A₁) (β-λ x) = sub-pres (λ{ zero → ⊢A₁ ; (suc x₁) → ⊢` refl}) ⊢A
sr (⊢⟨⟩ ⊢A ⊢A₁) (ξ-⟨⟩₁ t—→t') = ⊢⟨⟩ (sr ⊢A t—→t') ⊢A₁
sr (⊢⟨⟩ ⊢A ⊢A₁) (ξ-⟨⟩₂ t—→t' x) = ⊢⟨⟩ ⊢A (sr ⊢A₁ t—→t')
sr (⊢π₁ ⊢A) (ξ-π₁ t—→t') = ⊢π₁ (sr ⊢A t—→t')
sr (⊢π₁ (⊢⟨⟩ ⊢A ⊢A₁)) (β-π₁ x x₁) = ⊢A
sr (⊢π₂ ⊢A) (ξ-π₂ t—→t') = ⊢π₂ (sr ⊢A t—→t')
sr (⊢π₂ (⊢⟨⟩ ⊢A ⊢A₁)) (β-π₂ x x₁) = ⊢A₁
