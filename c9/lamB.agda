open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.String using (String; _≟_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Empty using (⊥; ⊥-elim)

-- Part 1: Syntax and Semantics, Types

-- Using a named representation for educational
-- purposes only, usually it is very bothersome
-- to carry names for free and bound variables
Id : Set
Id = String


-- The pure lambda calculus has the following small syntax:
-- t ::=
--  x      (Variable)
--  λx.t   (Abstraction)
--  (t t)  (Application)


infix 5 ƛ_⇒_
infixl 7 _·_
infix 9 `_
data Term : Set where
  true   : Term
  false  : Term
  if_then_else_ : Term → Term → Term → Term
  `_     : Id → Term
  ƛ_⇒_   : Id → Term → Term
  _·_    : Term → Term → Term


-- The lambda calculus introduces the first
-- compund type: function (arrow) types
-- Terms includes a few more constructs, and types the type 𝔹
-- to make things more interesting. Also, without 𝔹 and in just
-- the pure simply typed lambda calculus, the only type would
-- be an arrow type with no types to fill them out
infixr 7 _⇒_
data Type : Set where
  𝔹  : Type
  _⇒_ : Type → Type → Type


---------------------------------Intermezzo: Programming in lambda calculus---------------------------------
-- Church numerals represent the natural numbers
zeroᶜ : Term
zeroᶜ = ƛ "s" ⇒ ƛ "z" ⇒ ` "z"

oneᶜ : Term
oneᶜ = ƛ "s" ⇒ ƛ "z" ⇒ (` "s") · (` "z")

twoᶜ : Term
twoᶜ = ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · ((` "s") · ` "z")

-- We can write a function that adds two church numerals
addᶜ : Term
-- λm λn λs λz (m s) (n s z)
addᶜ = ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒ (` "m" · ` "s") · ((` "n" · ` "s") · ` "z")

-- Or multiply them
multᶜ : Term
multᶜ = ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ` "m" · (` "n" · ` "s")


-- We can also model boolean logic within the lambda calculus
tru : Term
tru = ƛ "t" ⇒ ƛ "f" ⇒ ` "t"

fls : Term
fls = ƛ "t" ⇒ ƛ "f" ⇒ ` "f"

notᵇ : Term
notᵇ = ƛ "b" ⇒ (` "b" · fls) · tru

orᵇ : Term
orᵇ = ƛ "b" ⇒ ƛ "u" ⇒ (` "b" · tru) · (` "u")

andᵇ : Term
andᵇ = ƛ "b" ⇒ ƛ "u" ⇒ (` "b" · ` "u") · fls


-- Lists can be represented as well
-- The empty list (here: nil) is basically the same as fls, or zeroᶜ
nil : Term
nil = fls

-- A list is then represented as a fold
exampleList : Term
exampleList = ƛ "c" ⇒ ƛ "n" ⇒ (` "c" · ` "x") · (((` "c" · ` "y") · ((` "c" · ` "z") · ` "n")))

-- A function on a list could look like this
head : Term
-- λl 
head = ƛ "l" ⇒ (` "l" · tru) · nil
------------------------------------------------------------------------------------------------------------

-- Substitution is the working horse of the lambda calculus
-- The main difficulties here are:
--  (1) We do not want to substitute bound variable occurences
--  (2) If we substitute M for x in N, it is possible that the
--      term M contains names that will be captured by a lambda
--      binder in N where we substituted for x. That would capture
--      free variables of M that should remain free

[_≔_]_ : Id → Term → Term → Term
[ id ≔ M ] true = true
[ id ≔ M ] false = false
[ id ≔ M ] (if N then N₁ else N₂) = if [ id ≔ M ] N then [ id ≔ M ] N₁ else ([ id ≔ M ] N₂)
[ id ≔ M ] (` x) with x ≟ id
... | yes refl = M
... | no _     = ` x
[ id ≔ M ] (ƛ x ⇒ N) with x ≟ id
... | yes _ = ƛ x ⇒ N -- Bound variables aren't substituted
... | no _  = ƛ x ⇒ ([ id ≔ M ] N) -- SILENT ASSUMPTION* 
[ id ≔ M ] (N · N₁) = ([ id ≔ M ] N) · ([ id ≔ M ] N₁)

-- * The assumption is that we assume M to be a VALUE
-- (or: closed term / combinator). That means we assume
-- no free variables inside of M. That's unfortunate and
-- restricts the way we can do substitution right now but
-- for the semantics and typing proofs later on it suffices,
-- mainly because before substitution, we will always evaluate
-- the right hand side of an application to a value (call by value)

-- Evaluation relation

data Value : Term → Set where
  V-true  : Value true
  V-false : Value false
  V-λ : ∀ {x t} → Value (ƛ x ⇒ t)

infix 4 _—→_
data _—→_ : Term → Term → Set where
  ξ-·₁ : ∀ {t₁ t₁' t₂} → t₁ —→ t₁' → t₁ · t₂ —→ t₁' · t₂
  ξ-·₂ : ∀ {v t₂ t₂'} → Value v → t₂ —→ t₂' → v · t₂ —→ v · t₂'
  β-ƛ  : ∀ {x M v} → Value v → (ƛ x ⇒ M) · v —→ [ x ≔ v ] M
  ξ-if : ∀ {t₁ t₁' t₂ t₃} → t₁ —→ t₁' → if t₁ then t₂ else t₃ —→ if t₁' then t₂ else t₃
  β-true : ∀ {t₂ t₃} → if true then t₂ else t₃ —→ t₂
  β-false : ∀ {t₂ t₃} → if false then t₂ else t₃ —→ t₃
------------------------------------------------------------------------------------------------------------------

-- Part 2: Type system
-- Since we included the lambda calculus in our language we now have
-- variables and the type system becomes a lot more involved than
-- what was done in arith. Namely, to keep track of the types of
-- free variables we need a context which is just a list of variables
-- and their assumed types

-- Contexts extend to the right
data Ctx : Set where
  ∅ : Ctx
  _▸_⦂_ : Ctx → Id → Type → Ctx

-- We need judgements to consider whether a variable
-- has a certain type in a given context
infix 4 _∋_⦂_
data _∋_⦂_ : Ctx → Id → Type → Set where
  Z : ∀ {x T Γ} → Γ ▸ x ⦂ T ∋ x ⦂ T
  S : ∀ {x T Γ y S} → x ≢ y → Γ ∋ x ⦂ T → Γ ▸ y ⦂ S ∋ x ⦂ T

-- Typing is now a ternary relation
infix 4 _⊢_⦂_
data _⊢_⦂_ : Ctx → Term → Type → Set where
  ⊢` : ∀ {Γ x T} → Γ ∋ x ⦂ T → Γ ⊢ ` x ⦂ T -- Free variables have whatever type we assume for them
  ⊢true  : ∀ {Γ} → Γ ⊢ true ⦂ 𝔹
  ⊢false : ∀ {Γ} → Γ ⊢ false ⦂ 𝔹
  _·_ : ∀ {Γ t₁ T S t₂} → Γ ⊢ t₁ ⦂ T ⇒ S → Γ ⊢ t₂ ⦂ T → Γ ⊢ t₁ · t₂ ⦂ S
  ⊢ƛ : ∀ {Γ x T M S} → Γ ▸ x ⦂ T ⊢ M ⦂ S → Γ ⊢ ƛ x ⇒ M ⦂ T ⇒ S
  ⊢if : ∀ {Γ t₁ t₂ t₃ T} → Γ ⊢ t₁ ⦂ 𝔹 → Γ ⊢ t₂ ⦂ T → Γ ⊢ t₃ ⦂ T → Γ ⊢ if t₁ then t₂ else t₃ ⦂ T

-- Part 3: Properties
-- Progress is easy, preservation requires a lot more work now with
-- several new lemmata that reason about contexts and variable typings
data Progress (t : Term) : Set where
  isValue : Value t → Progress t
  canStep : ∀ {t'} → t —→ t' → Progress t

progress : ∀ {t T} → ∅ ⊢ t ⦂ T → Progress t
progress ⊢true = isValue V-true
progress ⊢false = isValue V-false
progress (⊢T · ⊢T₁) with progress ⊢T
... | canStep t' = canStep (ξ-·₁ t')
... | isValue v with progress ⊢T₁
... | canStep t'' = canStep (ξ-·₂ v t'')
progress (⊢T · ⊢T₁) | isValue V-λ | isValue v' = canStep (β-ƛ v')
progress (⊢ƛ ⊢T) = isValue V-λ
progress (⊢if ⊢T ⊢T₁ ⊢T₂) with progress ⊢T
... | canStep t' = canStep (ξ-if t')
... | isValue V-true = canStep β-true
... | isValue V-false = canStep β-false

ext : ∀ {Γ Δ y S} → (∀ {x T} → Γ ∋ x ⦂ T → Δ ∋ x ⦂ T) → (∀ {x T} → Γ ▸ y ⦂ S ∋ x ⦂ T → Δ ▸ y ⦂ S ∋ x ⦂ T)
ext ρ Z = Z
ext ρ (S x ∋x) = S x (ρ ∋x)

ren : ∀ {Γ Δ} → (∀ {x T} → Γ ∋ x ⦂ T → Δ ∋ x ⦂ T) → (∀ {M S} → Γ ⊢ M ⦂ S → Δ ⊢ M ⦂ S)
ren ρ (⊢` x) = ⊢` (ρ x)
ren ρ ⊢true = ⊢true
ren ρ ⊢false = ⊢false
ren ρ (⊢S · ⊢S₁) = (ren ρ ⊢S) · (ren ρ ⊢S₁)
ren ρ (⊢ƛ ⊢S) = ⊢ƛ (ren (ext ρ) ⊢S)
ren ρ (⊢if ⊢S ⊢S₁ ⊢S₂) = ⊢if (ren ρ ⊢S) (ren ρ ⊢S₁) (ren ρ ⊢S₂)

drop : ∀ {Γ x T S M U} → ((Γ ▸ x ⦂ T) ▸ x ⦂ S) ⊢ M ⦂ U → (Γ ▸ x ⦂ S) ⊢ M ⦂ U  
drop ⊢U = ren (λ{ Z → Z ; (S x Z) → ⊥-elim (x refl) ; (S x (S x₁ x₂)) → S x x₂}) ⊢U

perm : ∀ {Γ x T y S M U} → y ≢ x → ((Γ ▸ x ⦂ T) ▸ y ⦂ S) ⊢ M ⦂ U → ((Γ ▸ y ⦂ S) ▸ x ⦂ T) ⊢ M ⦂ U
perm y≢x ⊢U = ren (λ{ Z → S y≢x Z ; (S x Z) → Z ; (S x (S x₁ x₂)) → S x₁ (S x x₂)}) ⊢U

weaken : ∀ {Γ V T} → ∅ ⊢ V ⦂ T → Γ ⊢ V ⦂ T
weaken ⊢T = ren (λ{ ()}) ⊢T

subst : ∀ {Γ x T S M V}
      → Γ ▸ x ⦂ T ⊢ M ⦂ S
      → ∅ ⊢ V ⦂ T
        -------------------
      → Γ ⊢ [ x ≔ V ] M ⦂ S

subst {x = x₁} (⊢` {x = x₂} x) ⊢T with x₂ ≟ x₁
subst {x = x₁} (⊢` {x = _} Z) ⊢T | yes refl = weaken ⊢T
subst {x = x₁} (⊢` {x = _} (S x x₂)) ⊢T | yes refl = ⊥-elim (x refl)
subst {x = x₁} (⊢` {x = _} Z) ⊢T | no ¬p = ⊥-elim (¬p refl)
subst {x = x₁} (⊢` {x = _} (S x x₂)) ⊢T | no ¬p = ⊢` x₂
subst ⊢true ⊢T = ⊢true
subst ⊢false ⊢T = ⊢false
subst (⊢S · ⊢S₁) ⊢T = (subst ⊢S ⊢T) · (subst ⊢S₁ ⊢T)
subst {x = x₁} (⊢ƛ {x = x₂} ⊢S) ⊢T with x₂ ≟ x₁
... | yes refl = ⊢ƛ (drop ⊢S)
... | no  ¬p   = ⊢ƛ (subst (perm ¬p ⊢S) ⊢T) 
subst (⊢if ⊢S ⊢S₁ ⊢S₂) ⊢T = ⊢if (subst ⊢S ⊢T) (subst ⊢S₁ ⊢T) (subst ⊢S₂ ⊢T)


preservation : ∀ {t t' T} → ∅ ⊢ t ⦂ T → t —→ t' → ∅ ⊢ t' ⦂ T
preservation (⊢T · ⊢T₁) (ξ-·₁ t—→t') = (preservation ⊢T t—→t') · ⊢T₁
preservation (⊢T · ⊢T₁) (ξ-·₂ x t—→t') = ⊢T · (preservation ⊢T₁ t—→t')
preservation (⊢ƛ ⊢T · ⊢T₁) (β-ƛ x) = subst ⊢T ⊢T₁
preservation (⊢if ⊢T ⊢T₁ ⊢T₂) (ξ-if t—→t') = ⊢if (preservation ⊢T t—→t') ⊢T₁ ⊢T₂
preservation (⊢if ⊢T ⊢T₁ ⊢T₂) β-true = ⊢T₁
preservation (⊢if ⊢T ⊢T₁ ⊢T₂) β-false = ⊢T₂
