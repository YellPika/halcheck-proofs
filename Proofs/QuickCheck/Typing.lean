import Proofs.QuickCheck.Syntax

namespace QuickCheck

/--
A context indicates what type every variable has.
Variables may only refer to values.
-/
def Context := ℕ → QType val

/--
`infer Γ t` returns a type `τ` such that `Γ ⊢ t : τ`, if it exists.
If no such `τ` exists, the result is arbitrary.
-/
@[simp]
def infer (Γ : Context) : QTerm k → QType k := fun
  | var x => Γ x
  | tt => bool
  | ff => bool
  | if_ _ _ t₃ => infer Γ t₃
  | return_ t => gen (infer Γ t)
  | let_ t₁ t₂ => gen <|
      match infer Γ t₁ with
      | gen τ₁ =>
          match infer (Nat.cases τ₁ Γ) t₂ with
          | gen τ₂ => τ₂
          | _ => default
      | _ => default
  | choose p => gen bool
  | lam τ t => arrow τ (infer Γ t)
  | app t _ =>
      match infer Γ t with
      | arrow _ τ => τ
      | _ => default
  | fix τ _ => τ
  | force t =>
      match infer Γ t with
      | thunk τ => τ
      | _ => default
  | delay t => thunk (infer Γ t)

/-- `genType (gen τ) = τ`. The result is undefined otherwise. -/
def genType : CType → VType := fun
  | gen τ => τ
  | _ => default

/-- `thunkType (thunk τ) = τ`. The result is undefined otherwise. -/
def thunkType : VType → CType := fun
  | thunk τ => τ
  | _ => default

/--
`Valid Γ t τ` (also written `Γ ⊢ t : τ`) means `t` has type `τ` in context `Γ`.
NOTE: this definition is carefully constructed so that it can be pattern-matched
on in non-Prop contexts. In particular, we avoid existential quantification in
favor of explicit witnesses using `infer`.
-/
def Valid (Γ : Context) : QTerm k → QType k → Prop := fun
  | var i, τ => τ = Γ i
  | tt, τ => τ = bool
  | ff, τ => τ = bool
  | return_ t, τ =>
      let τ' := infer Γ t
      τ = gen τ' ∧
      Valid Γ t τ'
  | let_ t₁ t₂, τ =>
      let τ₁ := genType (infer Γ t₁)
      let τ₂ := genType (infer (Nat.cases τ₁ Γ) t₂)
      τ = gen τ₂ ∧
      Valid Γ t₁ (gen τ₁) ∧
      Valid (Nat.cases τ₁ Γ) t₂ (gen τ₂)
  | if_ t₁ t₂ t₃, τ =>
      Valid Γ t₁ bool ∧
      Valid Γ t₂ τ ∧
      Valid Γ t₃ τ
  | choose _, τ => τ = gen bool
  | lam τ₁ t, τ =>
      let τ₂ := infer (Nat.cases τ₁ Γ) t
      τ = arrow τ₁ τ₂ ∧
      Valid (Nat.cases τ₁ Γ) t τ₂
  | app t₁ t₂, τ₂ =>
      let τ₁ := infer Γ t₂
      Valid Γ t₁ (arrow τ₁ τ₂) ∧
      Valid Γ t₂ τ₁
  | fix τ t, τ' =>
      τ = τ' ∧
      Valid (Nat.cases (thunk τ') Γ) t τ'
  | force t, τ => Valid Γ t (thunk τ)
  | delay t, τ =>
      let τ' := infer Γ t
      τ = thunk τ' ∧
      Valid Γ t τ'

/-- See `Valid`. -/
notation Γ:80 " ⊢ " t:80 " : " τ:80 => Valid Γ t τ

/-- A term cannot have more than one type. -/
lemma Valid.unique (h : Valid Γ t τ) : τ = infer Γ t := by
  sorry

/-- Validity is preserved by renaming. -/
lemma Valid.map (ht : Valid (Γ ∘ ρ) t τ) : Valid Γ (QTerm.map ρ t) τ := by
  sorry

/-- Validity is preserved by substitution. -/
lemma Valid.bind (hσ : ∀i, Valid Δ (σ i) (Γ i)) (ht : Valid Γ t τ) : Valid Δ (QTerm.bind σ t) τ := by
  sorry

end QuickCheck
