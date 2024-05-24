open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; []; _∷_; lookup)



infixr 5 _⇒_
infixr 5 _`×_
data Type : Set where
  top  : Type -- Used for subtyping
  _⇒_ : Type → Type → Type
  _`×_ : Type → Type → Type

-- Fin n stands for the set {0,...,n-1} and helps to represent
-- variables in an intrinsically scoped way. This way we have to
-- write seperate type-preservation proofs for our definitions again
-- but can write out terms and types seperately. It also allows us to
-- omit names. We index Terms with ℕ to talk about the amount of free
-- variables inside a term
data Term (n : ℕ) : Set where
  `_    : Fin n → Term n
  ƛ_∶_  : Type → Term (suc n) → Term n 
  _·_   : Term n → Term n → Term n
  ⟨_,_⟩ : Term n → Term n → Term n
  π₁_   : Term n → Term n
  π₂_   : Term n → Term n


data Value {n : ℕ} : Term n → Set where
  V-ƛ : ∀ {t : Term (suc n)} {A} → Value (ƛ A ∶ t)
  V-× : ∀ {t₁ t₂} → Value t₁ → Value t₂ → Value (⟨ t₁ , t₂ ⟩)

---------------------------- Subtying ------------------------------------------------------------------------
infix 4 _<:_
data _<:_ : Type → Type → Set where
  S-top   : ∀ {A} → A <: top
  <:-refl  : ∀ {A} → A <: A
  <:-⇒ : ∀ {A₁ A₂ B₁ B₂} → B₁ <: A₁ → A₂ <: B₂ → A₁ ⇒ A₂ <: B₁ ⇒ B₂
  <:-⟨⟩  : ∀ {A₁ A₂ B₁ B₂} → A₁ <: B₁ → A₂ <: B₂ → A₁ `× A₂ <: B₁ `× B₂

-- Usually better to show that the relation is transitive by defining the relation in
-- an equivalent manner that lets us easily deduce transitivity. In this case it was a
-- trivial case splitting proof
<:-trans : ∀ {A B C} → A <: B → B <: C → A <: C
<:-trans S-top S-top = S-top
<:-trans S-top <:-refl = S-top
<:-trans <:-refl B<:C = B<:C
<:-trans (<:-⇒ A<:B A<:B₁) S-top = S-top
<:-trans (<:-⇒ A<:B A<:B₁) <:-refl = <:-⇒ A<:B A<:B₁
<:-trans (<:-⇒ A<:B A<:B₁) (<:-⇒ B<:C B<:C₁) = <:-⇒ (<:-trans B<:C A<:B) (<:-trans A<:B₁ B<:C₁)
<:-trans (<:-⟨⟩ A<:B A<:B₁) S-top = S-top
<:-trans (<:-⟨⟩ A<:B A<:B₁) <:-refl = <:-⟨⟩ A<:B A<:B₁
<:-trans (<:-⟨⟩ A<:B A<:B₁) (<:-⟨⟩ B<:C B<:C₁) = <:-⟨⟩ (<:-trans A<:B B<:C) (<:-trans A<:B₁ B<:C₁)
--------------------------------------------------------------------------------------------------------------

-- Contexts are now just finite vectors of types
Ctx : ℕ → Set
Ctx n = Vec Type n

infix 4 _⊢_⦂_
data _⊢_⦂_ {n : ℕ} (Γ : Ctx n) : Term n → Type → Set where
  ⊢`   : ∀ {x A} → lookup Γ x ≡ A → Γ ⊢ ` x ⦂ A
  ⊢λ   : ∀ {t : Term (suc n)} {A B : Type} → (A ∷ Γ) ⊢ t ⦂ B → Γ ⊢ ƛ A ∶ t ⦂ A ⇒ B
  ⊢·   : ∀ {t₁ t₂ A B} → Γ ⊢ t₁ ⦂ A ⇒ B → Γ ⊢ t₂ ⦂ A → Γ ⊢ t₁ · t₂ ⦂ B
  ⊢⟨⟩  : ∀ {t₁ t₂ A B} → Γ ⊢ t₁ ⦂ A → Γ ⊢ t₂ ⦂ B → Γ ⊢ ⟨ t₁ , t₂ ⟩ ⦂ A `× B
  ⊢π₁  : ∀ {t A B} → Γ ⊢ t ⦂ A `× B → Γ ⊢ π₁ t ⦂ A
  ⊢π₂  : ∀ {t A B} → Γ ⊢ t ⦂ A `× B → Γ ⊢ π₂ t ⦂ B
  ⊢sub : ∀ {t A B} → Γ ⊢ t ⦂ A → A <: B → Γ ⊢ t ⦂ B


-- Substitution + sub preservation
_⇒ᵣ_ : ℕ → ℕ → Set
n ⇒ᵣ m = Fin n → Fin m

extr : ∀ {n m} → n ⇒ᵣ m → (suc n) ⇒ᵣ (suc m)
extr ρ zero = zero
extr ρ (suc fn) = suc (ρ fn)

ren : ∀ {n m} → n ⇒ᵣ m → (Term n → Term m)
ren ρ (` x) = ` ρ x
ren ρ (ƛ A ∶ t) = ƛ A ∶ (ren (extr ρ) t)
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
sub σ (ƛ A ∶ t) = ƛ A ∶ (sub (exts σ) t)
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
  β-λ   : ∀ {t v A} → Value v → (ƛ A ∶ t) · v —→ t [ v ]
  ξ-π₁  : ∀ {t t'} → t —→ t' → π₁ t —→ π₁ t'
  ξ-π₂  : ∀ {t t'} → t —→ t' → π₂ t —→ π₂ t'
  ξ-⟨⟩₁ : ∀ {t₁ t₁' t₂} → t₁ —→ t₁' → ⟨ t₁ , t₂ ⟩ —→ ⟨ t₁' , t₂ ⟩
  ξ-⟨⟩₂ : ∀ {v t₂ t₂'} → t₂ —→ t₂' → Value v → ⟨ v , t₂ ⟩ —→ ⟨ v , t₂' ⟩
  β-π₁ : ∀ {v₁ v₂} → Value v₁ → Value v₂ → π₁ (⟨ v₁ , v₂ ⟩) —→ v₁
  β-π₂ : ∀ {v₁ v₂} → Value v₁ → Value v₂ → π₂ (⟨ v₁ , v₂ ⟩) —→ v₂

-- Progress + Preservation
sub-lemma-⇒ : ∀ {A B C} → A <: B ⇒ C → ∃[ B' ] (∃[ C' ] (A ≡ B' ⇒ C' × B <: B' × C' <: C))
sub-lemma-⇒ {A} {B} {C} <:-refl = B , C , (refl , (<:-refl , <:-refl))
sub-lemma-⇒ {B = B} (<:-⇒ {A₁} {A₂} A<: A<:₁) = (A₁ , A₂ , (refl , (A<: , A<:₁)))

canon-forms-λ : ∀ {n} {v : Term n} {Γ A B} → Value v → Γ ⊢ v ⦂ A ⇒ B → ∃[ t ] (∃[ A' ] ((v ≡ ƛ A' ∶ t) × A <: A'))
canon-forms-λ {A = A} v (⊢λ {t} ⊢AB) = t , (A , (refl , <:-refl))
canon-forms-λ v (⊢sub ⊢AB x) with sub-lemma-⇒ x
... | fst , fst₁ , refl , fst₃ , snd with canon-forms-λ v ⊢AB
... | fst₂ , fst₄ , refl , snd₁ = fst₂ , (fst₄ , (refl , <:-trans fst₃ snd₁))


sub-lemma-⟨⟩ : ∀ {A B C} → A <: B `× C → ∃[ A₁ ] (∃[ A₂ ] ( A ≡ A₁ `× A₂ × A₁ <: B × A₂ <: C))
sub-lemma-⟨⟩ {.(B `× C)} {B} {C} <:-refl = B , (C , (refl , (<:-refl , <:-refl)))
sub-lemma-⟨⟩ {.(A₁ `× A₂)} {B} {C} (<:-⟨⟩ {A₁} {A₂} A<: A<:₁) = A₁ , (A₂ , (refl , (A<: , A<:₁)))

canon-forms-⟨⟩ : ∀ {n} {v : Term n} {Γ A B} → Value v → Γ ⊢ v ⦂ A `× B → ∃[ t₁ ] (∃[ t₂ ] ( v ≡ ⟨ t₁ , t₂ ⟩ × Value t₁ × Value t₂))
canon-forms-⟨⟩ (V-× {t₁} {t₂} v v₁) (⊢⟨⟩ ⊢AB ⊢AB₁) = t₁ , (t₂ , (refl , (v , v₁)))
canon-forms-⟨⟩ v (⊢sub ⊢AB x) with sub-lemma-⟨⟩ x
... | fst , fst₁ , refl , fst₃ , snd with canon-forms-⟨⟩ v ⊢AB
... | fst₂ , fst₄ , refl , fst₆ , snd₁ = fst₂ , (fst₄ , (refl , (fst₆ , snd₁)))


data Progress {n : ℕ} (t : Term n) : Set where
  isValue : Value t → Progress t
  canStep : ∀ {t'} → t —→ t' → Progress t

progress : ∀ {t A} → [] ⊢ t ⦂ A → Progress t
progress (⊢λ ⊢A) = isValue V-ƛ
progress (⊢· ⊢A ⊢A₁) with progress ⊢A
... | canStep x = canStep (ξ-·₁ x)
... | isValue v with progress ⊢A₁
... | canStep x₂ = canStep (ξ-·₂ x₂ v)
... | isValue v₂ with canon-forms-λ v ⊢A
... | fst , fst₁ , refl , snd = canStep (β-λ v₂)
progress (⊢⟨⟩ ⊢A ⊢A₁) with progress ⊢A
... | canStep x = canStep (ξ-⟨⟩₁ x)
... | isValue v with progress ⊢A₁
... | canStep x₁ = canStep (ξ-⟨⟩₂ x₁ v)
... | isValue v₁ = isValue (V-× v v₁)
progress (⊢π₁ ⊢A) with progress ⊢A
... | canStep x = canStep (ξ-π₁ x)
... | isValue v with canon-forms-⟨⟩ v ⊢A
... | fst , fst₁ , refl , fst₃ , snd = canStep (β-π₁ fst₃ snd)
progress (⊢π₂ ⊢A) with progress ⊢A
... | canStep x = canStep (ξ-π₂ x)
... | isValue v with canon-forms-⟨⟩ v ⊢A
... | fst , fst₁ , refl , fst₃ , snd = canStep (β-π₂ fst₃ snd)
progress (⊢sub ⊢A x) = progress ⊢A


--σ fn ⦂ lookup Γ fn
_⦂_⇒ₛ_ : ∀ {n m} → n ⇒ₛ m → (Γ : Ctx n) → (Δ : Ctx m) → Set
σ ⦂ Γ ⇒ₛ Δ = ∀ x → Δ ⊢ σ x ⦂ lookup Γ x

_⦂_⇒ᵣ_ : ∀ {n m} → n ⇒ᵣ m → Ctx n → Ctx m → Set
ρ ⦂ Γ ⇒ᵣ Δ = ∀ x → Δ ⊢ ` ρ x ⦂ lookup Γ x

extr-pres-lemma : ∀ {n} {Γ : Ctx n} {x A B} → Γ ⊢ ` x ⦂ B → (A ∷ Γ) ⊢ ` suc x ⦂ B  
extr-pres-lemma (⊢` refl) = ⊢` refl
extr-pres-lemma (⊢sub ⊢B x) = ⊢sub (extr-pres-lemma ⊢B) x

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
ren-pres ⊢ρ (⊢sub ⊢A x) = ⊢sub (ren-pres ⊢ρ ⊢A) x


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
sub-pres ⊢σ (⊢sub ⊢A x) = ⊢sub (sub-pres ⊢σ ⊢A) x

⟨⟩-pres-lemma₁ : ∀ {n} {Γ : Ctx n} {t₁ t₂ : Term n} {A B} → Γ ⊢ ⟨ t₁ , t₂ ⟩ ⦂ A `× B → Γ ⊢ t₁ ⦂ A
⟨⟩-pres-lemma₁ (⊢⟨⟩ ⊢AB ⊢AB₁) = ⊢AB
⟨⟩-pres-lemma₁ (⊢sub ⊢AB x) with sub-lemma-⟨⟩ x
... | fst , fst₁ , refl , fst₃ , snd = ⊢sub (⟨⟩-pres-lemma₁ ⊢AB) fst₃

⟨⟩-pres-lemma₂ : ∀ {n} {Γ : Ctx n} {t₁ t₂ : Term n} {A B} → Γ ⊢ ⟨ t₁ , t₂ ⟩ ⦂ A `× B → Γ ⊢ t₂ ⦂ B
⟨⟩-pres-lemma₂ (⊢⟨⟩ ⊢AB ⊢AB₁) = ⊢AB₁
⟨⟩-pres-lemma₂ (⊢sub ⊢AB x) with sub-lemma-⟨⟩ x
... | fst , fst₁ , refl , fst₃ , snd = ⊢sub (⟨⟩-pres-lemma₂ ⊢AB) snd

λ-sr-lemma : ∀ {n} {Γ : Ctx n} {t A B C} → Γ ⊢ ƛ A ∶ t ⦂ B ⇒ C → (B <: A × (A ∷ Γ) ⊢ t ⦂ C)
λ-sr-lemma (⊢λ ⊢BC) = <:-refl , ⊢BC
λ-sr-lemma (⊢sub ⊢BC x) with sub-lemma-⇒ x
... | fst , fst₁ , refl , fst₃ , snd with λ-sr-lemma ⊢BC
... | fst₂ , snd₁ = <:-trans fst₃ fst₂ , ⊢sub snd₁ snd

sr : ∀ {n} {Γ : Ctx n} {t t' A} → Γ ⊢ t ⦂ A → t —→ t' → Γ ⊢ t' ⦂ A
sr (⊢· ⊢A ⊢A₁) (ξ-·₁ t—→t') = ⊢· (sr ⊢A t—→t') ⊢A₁
sr (⊢· ⊢A ⊢A₁) (ξ-·₂ t—→t' x) = ⊢· ⊢A (sr ⊢A₁ t—→t')
sr (⊢· ⊢A ⊢A₁) (β-λ x) with λ-sr-lemma ⊢A
... | fst , snd = sub-pres (λ{ zero → ⊢sub ⊢A₁ fst ; (suc x₁) → ⊢` refl}) snd
sr (⊢⟨⟩ ⊢A ⊢A₁) (ξ-⟨⟩₁ t—→t') = ⊢⟨⟩ (sr ⊢A t—→t') ⊢A₁
sr (⊢⟨⟩ ⊢A ⊢A₁) (ξ-⟨⟩₂ t—→t' x) = ⊢⟨⟩ ⊢A (sr ⊢A₁ t—→t')
sr (⊢π₁ ⊢A) (ξ-π₁ t—→t') = ⊢π₁ (sr ⊢A t—→t')
sr (⊢π₁ ⊢A) (β-π₁ x x₁) = ⟨⟩-pres-lemma₁ ⊢A
sr (⊢π₂ ⊢A) (ξ-π₂ t—→t') = ⊢π₂ (sr ⊢A t—→t')
sr (⊢π₂ ⊢A) (β-π₂ x x₁) = ⟨⟩-pres-lemma₂ ⊢A
sr (⊢sub ⊢A x) t—→t' = ⊢sub (sr ⊢A t—→t') x
