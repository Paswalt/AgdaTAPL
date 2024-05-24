-- In this file, the STLC will be formalized intrinsically
-- and several additions will be made to it

infix  4 _⊢_
infix  4 _∋_
infixl 5 _,_
infixr 7 _⇒_
infixl 7 _·_
infix  9 `_



--Extensions added:
--   (1) Base types   [X]
--   (2) Unit type    [X]
--   (3) Let bindings [X]
--   (4) Pairs        [X]

-- Since we are using intrinsically-typed terms we
-- immediately have to talk about types
data Type : Set where
  𝔸  : Type -- Base type extension
  ⊤  : Type -- Unit type
  _⇒_ : Type → Type → Type
  _×_ : Type → Type → Type -- Pairs
  _+_ : Type → Type → Type -- Sums


-- Contexts are now just lists of types
data Ctx : Set where
  ∅ : Ctx
  _,_ : Ctx → Type → Ctx

-- We need again judgements for variables
-- these are basically just type lookups
-- inside the context
data _∋_ : Ctx → Type → Set where
  Z : ∀ {Γ A} → Γ , A ∋ A
  S : ∀ {Γ A B} → Γ ∋ A → Γ , B ∋ A

-- Terms and types now become intermixed. It makes no
-- sense to talk about one without the other anymore.
-- Essentially, everything is defined on typing derivations.
-- With that every definition is already the proof of a property
data _⊢_ : Ctx → Type → Set where
  -- STLC
  `_ : ∀ {Γ A} → Γ ∋ A → Γ ⊢ A
  _·_ : ∀ {Γ A B} → Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
  ƛ_ : ∀ {Γ A B} → Γ , A ⊢ B → Γ ⊢ A ⇒ B
  -- Unit
  ⊤ : ∀ {Γ} → Γ ⊢ ⊤
  -- Let
  `let : ∀ {Γ A B} → Γ ⊢ A → Γ , A ⊢ B → Γ ⊢ B
  -- Pairs
  ⟨_,_⟩ : ∀ {Γ A B} → Γ ⊢ A → Γ ⊢ B → Γ ⊢ A × B
  π₁_   : ∀ {Γ A B} → Γ ⊢ A × B → Γ ⊢ A
  π₂_   : ∀ {Γ A B} → Γ ⊢ A × B → Γ ⊢ B
  -- Sums
  inl : ∀ {Γ A B} → Γ ⊢ A → Γ ⊢ A + B
  inr : ∀ {Γ A B} → Γ ⊢ B → Γ ⊢ A + B
  case_[inl⇒_|inr⇒_] : ∀ {Γ A B C} → Γ ⊢ A + B → Γ , A ⊢ C → Γ , B ⊢ C → Γ ⊢ C 

-- Renamings and Substitutions
extr : ∀ {Γ Δ B} → (∀ {A} → Γ ∋ A → Δ ∋ A) → (∀ {A} → Γ , B ∋ A → Δ , B ∋ A)
extr ρ Z = Z
extr ρ (S ∋A) = S (ρ ∋A)

ren : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ∋ A) → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
-- STLC
ren ρ (` x) = ` (ρ x)
ren ρ (t₁ · t₂) = (ren ρ t₁) · (ren ρ t₂)
ren ρ (ƛ ⊢A) = ƛ (ren (extr ρ) ⊢A)
-- Unit
ren ρ ⊤ = ⊤
-- Let
ren ρ (`let t₁ t₂) = `let (ren ρ t₁) (ren (extr ρ) t₂)
-- Pairs
ren ρ ⟨ t , t₁ ⟩ = ⟨ (ren ρ t) , (ren ρ t₁) ⟩
ren ρ (π₁ t) = π₁ (ren ρ t)
ren ρ (π₂ t) = π₂ (ren ρ t)
-- Sums
ren ρ (inl t) = inl (ren ρ t)
ren ρ (inr t) = inr (ren ρ t)
ren ρ case t [inl⇒ t₁ |inr⇒ t₂ ] = case ren ρ t [inl⇒ ren (extr ρ) t₁ |inr⇒ ren (extr ρ) t₂ ]

exts : ∀ {Γ Δ B} → (∀ {A} → Γ ∋ A → Δ ⊢ A) → (∀ {A} → Γ , B ∋ A → Δ , B ⊢ A)
exts σ Z = ` Z
exts σ (S ∋A) = ren S (σ ∋A)

sub : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ⊢ A) → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
-- STLC
sub σ (` x) = σ x
sub σ (⊢A · ⊢A₁) = (sub σ ⊢A) · (sub σ ⊢A₁)
sub σ (ƛ ⊢A) = ƛ (sub (exts σ) ⊢A)
-- Unit
sub σ ⊤ = ⊤
-- Let
sub σ (`let t₁ t₂) = `let (sub σ t₁) (sub (exts σ) t₂)
-- Pairs
sub σ ⟨ t , t₁ ⟩ = ⟨ (sub σ t) , (sub σ t₁) ⟩
sub σ (π₁ t) = π₁ (sub σ t)
sub σ (π₂ t) = π₂ (sub σ t)
-- Sums
sub σ (inl t) = inl (sub σ t)
sub σ (inr t) = inr (sub σ t)
sub σ case t [inl⇒ t₁ |inr⇒ t₂ ] = case (sub σ t) [inl⇒ sub (exts σ) t₁ |inr⇒ sub (exts σ) t₂ ]

-- Single substitution
_[_] : ∀ {Γ A B}
     → Γ , A ⊢ B
     → Γ ⊢ A
     → Γ ⊢ B

M [ N ] = sub (λ{ Z → N ; (S x) → ` x}) M

-- Evaluation / Preservation

data Value : ∀ {Γ A} → (Γ ⊢ A) → Set where
  -- STLC
  V-ƛ : ∀ {Γ A B} {t : Γ , B ⊢ A} → Value (ƛ t)
  -- Unit
  V-⊤ : ∀ {Γ} → Value (⊤ {Γ}) 
  -- Pairs
  V-⟨⟩ : ∀ {Γ A B} {t₁ : Γ ⊢ A} {t₂ : Γ ⊢ B} → Value t₁ → Value t₂ → Value (⟨ t₁ , t₂ ⟩)
  -- Sums
  V-inl : ∀ {Γ A B} {t : Γ ⊢ A} → Value t → Value (inl {B = B} t)
  V-inr : ∀ {Γ A B} {t : Γ ⊢ B} → Value t → Value (inr {A = A} t) 

-- The definition of the evaluation relation already
-- talks about well typed terms. Furthermore, it
-- already states that a term t of type A steps
-- to only terms t' of also type A, meaning preservation
-- is already included in this intrinsic definition
infix 4 _—→_
data _—→_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where
  -- STLC
  ξ-·₁ : ∀ {Γ A B} {t₁ t₁' : Γ ⊢ A ⇒ B} {t₂ : Γ ⊢ A} → t₁ —→ t₁' → t₁ · t₂ —→ t₁' · t₂
  ξ-·₂ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {t₂ t₂' : Γ ⊢ A} → Value V → t₂ —→ t₂' → V · t₂ —→ V · t₂'
  β-ƛ  : ∀ {Γ A B} {t₁ : Γ , A ⊢ B} {V : Γ ⊢ A} → Value V → (ƛ t₁) · V —→ t₁ [ V ]
  -- Let bindings
  ξ-let : ∀ {Γ A B} {t₁ t₁' : Γ ⊢ A} {t₂ : Γ , A ⊢ B}  → t₁ —→ t₁' → (`let t₁ t₂) —→ (`let t₁' t₂)
  β-let : ∀ {Γ A B} {V : Γ ⊢ A} {t₂ : Γ , A ⊢ B} → Value V → (`let V t₂) —→ t₂ [ V ]
  -- Pairs
  ξ-π₁  : ∀ {Γ A B} {t t' : Γ ⊢ A × B} → t —→ t' → (π₁ t) —→ (π₁ t')
  ξ-π₂  : ∀ {Γ A B} {t t' : Γ ⊢ A × B} → t —→ t' → (π₂ t) —→ (π₂ t')
  ξ-⟨⟩₁ : ∀ {Γ A B} {t₁ t₁' : Γ ⊢ A} {t₂ : Γ ⊢ B} → t₁ —→ t₁' → ⟨ t₁ , t₂ ⟩ —→ ⟨ t₁' , t₂ ⟩
  ξ-⟨⟩₂ : ∀ {Γ A B} {V : Γ ⊢ A} {t₂ t₂' : Γ ⊢ B} → t₂ —→ t₂' → ⟨ V , t₂ ⟩ —→ ⟨ V , t₂' ⟩
  β-π₁  : ∀ {Γ A B} {V₁ : Γ ⊢ A} {V₂ : Γ ⊢ B} → Value V₁ → Value V₂ → π₁ ⟨ V₁ , V₂ ⟩ —→ V₁
  β-π₂  : ∀ {Γ A B} {V₁ : Γ ⊢ A} {V₂ : Γ ⊢ B} → Value V₁ → Value V₂ → π₂ ⟨ V₁ , V₂ ⟩ —→ V₂
  -- Sums
  ξ-inl   : ∀ {Γ A B} {t t' : Γ ⊢ A} → t —→ t' → (inl {B = B} t) —→ inl t'
  ξ-inr   : ∀ {Γ A B} {t t' : Γ ⊢ B} → t —→ t' → (inr {A = A} t) —→ inr t'
  ξ-case  : ∀ {Γ A B C} {t₁ t₁' : Γ ⊢ A + B} {t₂ : Γ , A ⊢ C} {t₃ : Γ , B ⊢ C} → t₁ —→ t₁' → (case t₁ [inl⇒ t₂ |inr⇒ t₃ ]) —→ (case t₁' [inl⇒ t₂ |inr⇒ t₃ ])
  β-caseₗ : ∀ {Γ A B C} {V : Γ ⊢ A} {t₂ : Γ , A ⊢ C} {t₃ : Γ , B ⊢ C} → Value V → case (inl V) [inl⇒ t₂ |inr⇒ t₃ ] —→ t₂ [ V ]
  β-caseᵣ : ∀ {Γ A B C} {V : Γ ⊢ B} {t₂ : Γ , A ⊢ C} {t₃ : Γ , B ⊢ C} → Value V → case (inr V) [inl⇒ t₂ |inr⇒ t₃ ] —→ t₃ [ V ]
