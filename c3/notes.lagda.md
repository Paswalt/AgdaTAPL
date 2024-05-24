# 3.2 Syntax
We have multiple ways to define and represent the syntax of a language:

(1) The grammar of terms

    t ::=
      true
      false
      if t then t else t
      0
      suc t
      pred t
      iszero t
  
is more akin of a description of the set of trees, not strings of terms.

(2) This grammar is equivalent to the following definition:
The set of Terms 𝕋 is the smalles set such that
- {true, false, 0} ⊆ 𝕋
- if t₁ ∈ 𝕋, then {succ t₁, pred t₁, iszero t₁} ⊆ 𝕋
- if t₁, t₂, t₃ ∈ 𝕋, then if t₁ then t₂ else t₃ ∈ 𝕋

(3) Yet another way to portray the same is using inference rules:
```agda
--------
true ∈ 𝕋

--------
false ∈ 𝕋

t₁ ∈ 𝕋
-----------
succ t₁ ∈ 𝕋

t₁ ∈ 𝕋
-----------
pred t₁ ∈ 𝕋

t₁ ∈ 𝕋
-------------
iszero t₁ ∈ 𝕋

t₁ ∈ 𝕋   t₂ ∈ 𝕋   t₃ ∈ 𝕋
-------------------------
if t₁ then t₂ else t₃ ∈ 𝕋
```
(4) The last one differs in that it is a more constructive/concrete way to describe the set of terms:

    S₀ = ∅

    Sᵢ₊₁ = {true, false, 0}
            ∪  {succ t₁, pred t₁, iszero t₁ | t₁ Sᵢ}
            ∪  {if t₁ then t₂ else t₃ | t₁, t₂, t₃ ∈ Sᵢ}

Finally, let S = ⋃Sᵢ. Note that both definitions are equivalent (as proven in the book).

Two brief exercises:

Ex 3.2.4: |S₀| = 0, |S₁| = 3, |S₂| = 39, |S₃| = 59439

Ex 3.2.5: This can be done via induction on i. For i = 0 it is trivial.
          For the induction step i → i+1, one just has to write out the definition of
          Sᵢ₊₂ and notice that Sᵢ ⊆ Sᵢ₊₁ by the inductive hypothesis. Then, we can make a case distinction
          whether we consider a constant or a compound term and conclude that an Element of Sᵢ₊₁ also
          lies in Sᵢ₊₂ □
(Only the proof *idea* is mentioned here because I have already written it out twice already on paper
 and want to save some time with not having to type it into this document)
