open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂)
open import lamB
open import lamBcurry using (Term'; _—→'_; Value')
open import Data.String using (String; _≟_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax)


{-
The file lamB contains a language that does not carry type-annotations
for its lambda abstractions. The file lamBcurry does carry type-annotations
for its lambda abstractions. This is a minor subtle change and it doesn't
really change anything for the proofs at all, but the typing behaves slightly
differently.

In lamB the term t = ƛ "x" ⇒ ` "x"
would actually be typable as the identity function T ⇒ T
for ANY concrete type! That is because the ⊢ƛ typing rule
simply adds x ⦂ T to our assumptions.

In lamBcurry the term t = ƛ "x" ⇒ ` "x" is not valid
because it needs a type annotation! When we add it:

t = ƛ "x" ⦂ 𝔹 ⇒ ` "x"

we obtain a term that corresponds to the identity function for
a SINGULAR type, in this case booleans (𝔹). If we would try to
look for a derivation of Γ ⊢ t ⦂ ℕ ⇒ ℕ (assuming we add ℕ as a type)
it would NOT work, simply because the ⊢ƛ typing rule now asks the
judgement x ⦂ T of the premise to have the same type of the annotation.
That means agda would realize this is not possible since 𝔹 ≠ ℕ

We can show that these two ways really behave the same by
e.g. relating their evaluations. This is what I wanted to
achieve with this file.
-}


-- First we define an erase function
erase : Term' → Term
erase Term'.true = true
erase Term'.false = false
erase (Term'.if t then t₁ else t₂) = if (erase t) then (erase t₁) else (erase t₂)
erase (Term'.` x) = ` x
erase (Term'.ƛ x ⦂ x₁ ⇒ t) = ƛ x ⇒ erase t
erase (t Term'.· t₁) = (erase t) · (erase t₁)

V'→V : ∀ {v} → Value' v → Value (erase v)
V'→V Value'.V-true = V-true
V'→V Value'.V-false = V-false
V'→V Value'.V-λ = V-λ

cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {x x' : A} {y y' : B} {z z' : C}
      → x ≡ x'
      → y ≡ y'
      → z ≡ z'
        --------------------
      → f x y z ≡ f x' y' z'
cong₃ f refl refl refl = refl

lemma1 : ∀ {x V M} → (erase (lamBcurry.[ x ≔ V ] M)) ≡ [ x ≔ (erase V) ] (erase M) 
lemma1 {x} {V} {Term'.true} = refl
lemma1 {x} {V} {Term'.false} = refl
lemma1 {x} {V} {Term'.if M then M₁ else M₂} with lemma1 {x} {V} {M} | lemma1 {x} {V} {M₁} | lemma1 {x} {V} {M₂}
... | p | p1 | p2 = cong₃ (λ x y z → if x then y else z) p p1 p2
lemma1 {x} {V} {Term'.` x₁} with x₁ ≟ x
... | yes refl = refl
... | no ¬p = refl
lemma1 {x} {V} {Term'.ƛ x₁ ⦂ x₂ ⇒ M} with x₁ ≟ x
... | yes refl = refl
... | no ¬p = cong (ƛ_⇒_ x₁) (lemma1 {x} {V} {M})
lemma1 {x} {V} {M Term'.· M₁} with lemma1 {x} {V} {M} | lemma1 {x} {V} {M₁}
... | p | p1 = cong₂ _·_ p p1

lemma2 : ∀ {t t' t''} → t —→ t' → t' ≡ t'' → t —→ t''
lemma2 (ξ-·₁ t—→t') refl = ξ-·₁ t—→t'
lemma2 (ξ-·₂ x t—→t') refl = ξ-·₂ x t—→t'
lemma2 (β-ƛ x) refl = β-ƛ x
lemma2 (ξ-if t—→t') refl = ξ-if t—→t'
lemma2 β-true refl = β-true
lemma2 β-false refl = β-false

theorem1 : ∀ {t t'} → t —→' t' → (erase t) —→ (erase t')
theorem1 (_—→'_.ξ-·₁' t—→'t') = ξ-·₁ (theorem1 t—→'t')
theorem1 (_—→'_.ξ-·₂' x t—→'t') = ξ-·₂ (V'→V x) (theorem1 t—→'t')
theorem1 (_—→'_.β-ƛ' {x = x₁} {M = M} {v = v} x) with lemma1 {x₁} {V = v} {M = M}
... | p = lemma2 (β-ƛ (V'→V x)) (sym p)
theorem1 (_—→'_.ξ-if' t—→'t') = ξ-if (theorem1 t—→'t')
theorem1 _—→'_.β-true' = β-true
theorem1 _—→'_.β-false' = β-false
