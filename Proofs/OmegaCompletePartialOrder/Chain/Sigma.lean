import Mathlib

namespace OmegaCompletePartialOrder.Chain.Sigma

variable {P : A → Type*} [∀x, Preorder (P x)]

/-- Injection for chains of sums. -/
def inj (c : Chain (P x)) : Chain ((x : A) × P x) :=
  c.map ⟨fun y ↦ ⟨x, y⟩, by
    intro u v h
    simp only [Sigma.mk_le_mk_iff, h]⟩

@[simp]
lemma inj_apply (c : Chain (P x)) : inj c n = ⟨x, c n⟩ := rfl

private lemma fst_eq {P : X → Type*} [∀x, Preorder (P x)] (c : Chain ((x : X) × P x)) : (c i).fst = (c j).fst := by
  by_cases h : i ≤ j
  . have := c.monotone h
    rw [Sigma.le_def] at this
    rcases this with ⟨this, _⟩
    exact this
  . simp only [not_le] at h
    have r₁ := c.monotone h
    have r₂ : c j ≤ c (j + 1) := c.monotone (by simp only [le_add_iff_nonneg_right, zero_le])
    rw [Sigma.le_def] at r₁ r₂
    rcases r₁ with ⟨e₁, _⟩
    rcases r₂ with ⟨e₂, _⟩
    rw [e₂, e₁]

/-- Projects values out of a chain. -/
def proj (c : Chain ((x : A) × P x)) : Chain (P (c 0).fst) where
  toFun n := cast (by congr 1; apply fst_eq) (c n).snd
  monotone' i j h := by
    dsimp only
    have {u v w : A} {x : P u} {y : P v}
         (hu : u = w) (hv : v = w) (hxy : ⟨u, x⟩ ≤ (⟨v, y⟩ : (x : A) × P x)) :
         cast (congr_arg P hu) x ≤ cast (congr_arg P hv) y
    . cases hu
      cases hv
      simp only [Sigma.mk_le_mk_iff] at hxy
      simp only [cast_eq, hxy]
    apply this
    . apply fst_eq
    . apply fst_eq
    . simp only [Sigma.eta]
      apply c.monotone h

@[simp]
lemma proj_apply (c : Chain ((x : A) × P x)) :
  proj c n = cast (by congr 1; apply fst_eq) (c n).snd := rfl

/-- Splits a chain of sums into a sum of chains. -/
def distrib (c : Chain ((x : A) × P x)) : (x : A) × Chain (P x) where
  fst := (c 0).fst
  snd := proj c

lemma distrib_at (c : Chain ((x : A) × P x)) n : c n = ⟨(distrib c).fst, (distrib c).snd n⟩ := by
  simp only [distrib]
  ext
  . apply fst_eq
  . simp only [proj_apply, heq_cast_iff_heq, heq_eq_eq]

@[simp]
lemma inj_distrib (c : Chain ((x : A) × P x)) : inj (distrib c).snd = c := by
  apply OrderHom.ext
  ext n
  . simp only [inj_apply (distrib c).snd]
    apply fst_eq
  . rw [inj_apply (distrib c).snd]
    simp only
    rw [distrib_at c n]

@[simp]
lemma distrib_inj (c : Chain (P x)) : distrib (inj c) = ⟨x, c⟩ := rfl

end OmegaCompletePartialOrder.Chain.Sigma
