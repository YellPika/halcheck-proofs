import Proofs.OmegaCompletePartialOrder.Chain
import Proofs.OmegaCompletePartialOrder.Instances

namespace OmegaCompletePartialOrder

variable
  {I : Type*} {P : I → Type*}
  [OmegaCompletePartialOrder A]
  [OmegaCompletePartialOrder B]
  [OmegaCompletePartialOrder C]
  [(x : I) → OmegaCompletePartialOrder (P x)]

@[simp]
lemma ωSup_const {x : A} : ωSup (Chain.const x) = x := by
  apply antisymm (r := (· ≤ ·))
  . simp only [ωSup_le_iff, Chain.const_apply, le_refl, implies_true]
  . apply le_ωSup_of_le 0
    simp only [Chain.const_apply, le_refl]

@[simp]
lemma ωSup_pi (c : Chain (∀x, P x)) (x : I) :
  ωSup c x = ωSup (c.map (Pi.evalOrderHom x)) := rfl

@[simp]
lemma ωSup_opi [Preorder I] (c : Chain (I →o A)) (x : I) :
  ωSup c x = ωSup (c.map (OrderHom.apply x)) := rfl

@[simp]
lemma ωSup_sum (c : Chain (A ⊕ B)) : ωSup c = Sum.map ωSup ωSup (Chain.Sum.distrib c) := rfl

@[simp]
lemma ωSup_sigma (c : Chain ((x : I) × P x)) : ωSup c = ⟨(Chain.Sigma.distrib c).1, ωSup (Chain.Sigma.distrib c).2⟩ := rfl

lemma ωScottContinuous_iff_monotone_map_ωSup' {f : A → B} :
    ωScottContinuous f ↔ ∃ hf : Monotone f, ∀ c : Chain A, f (ωSup c) ≤ ωSup (c.map ⟨f, hf⟩) := by
  rw [ωScottContinuous_iff_monotone_map_ωSup]
  constructor
  . rintro ⟨hf₁, hf₂⟩
    exists hf₁
    simp only [hf₂, le_refl, implies_true]
  . rintro ⟨hf₁, hf₂⟩
    exists hf₁
    intro c
    apply le_antisymm
    . apply hf₂
    . simp only [ωSup_le_iff, Chain.map_coe, OrderHom.coe_mk, Function.comp_apply]
      intro i
      apply hf₁
      apply le_ωSup

attribute [fun_prop] ωScottContinuous ContinuousHom.ωScottContinuous

@[fun_prop]
lemma ωScottContinuous_id : ωScottContinuous (fun (x : A) ↦ x) := ωScottContinuous.id

@[fun_prop]
lemma ωScottContinuous_const (x : B) : ωScottContinuous (fun (_ : A) ↦ (x : B)) := ωScottContinuous.const

@[fun_prop]
lemma ωScottContinuous_comp {f : B → C} {g : A → B} (hf : ωScottContinuous f) (hg : ωScottContinuous g) : ωScottContinuous (fun x ↦ f (g x)) := ωScottContinuous.comp hf hg

@[fun_prop]
lemma ωScottContinuous_apply : ωScottContinuous (fun (f : ∀x, P x) ↦ f x) := by
  rw [ωScottContinuous_iff_monotone_map_ωSup]
  refine ⟨?_, ?_⟩
  . intro f₁ f₂ hf
    apply hf
  . intro c
    rfl

@[fun_prop]
lemma ωScottContinuous_apply_o : ωScottContinuous (fun (f : A →o B) ↦ f x) := by
  rw [ωScottContinuous_iff_monotone_map_ωSup]
  refine ⟨?_, ?_⟩
  . intro f₁ f₂ hf
    apply hf
  . intro c
    rfl

@[fun_prop]
lemma ωScottContinuous_apply_c : ωScottContinuous (fun (f : A →𝒄 B) ↦ f x) := by
  rw [ωScottContinuous_iff_monotone_map_ωSup]
  refine ⟨?_, ?_⟩
  . intro f₁ f₂ hf
    apply hf
  . intro c
    rfl

@[fun_prop]
lemma ωScottContinuous_pi {f : A → (x : I) → P x} (hf : ∀ a, ωScottContinuous fun x ↦ f x a) : ωScottContinuous f :=
  OmegaCompletePartialOrder.ωScottContinuous.of_apply₂ hf

@[fun_prop]
lemma ωScottContinuous_pi_o [Preorder I] {f : A → I →o C} (hf : ∀ a, ωScottContinuous fun x ↦ f x a) : ωScottContinuous f := by
  rw [ωScottContinuous_iff_monotone_map_ωSup]
  refine ⟨?_, ?_⟩
  . intro x₁ x₂ hx y
    apply (hf y).monotone hx
  . intro c
    ext x
    rw [(hf x).map_ωSup]
    rfl

@[fun_prop]
lemma ωScottContinuous_pi_c {f : A → B →𝒄 C} (hf : ∀ a, ωScottContinuous fun x ↦ f x a) : ωScottContinuous f := by
  rw [ωScottContinuous_iff_monotone_map_ωSup]
  refine ⟨?_, ?_⟩
  . intro x₁ x₂ hx y
    apply (hf y).monotone hx
  . intro c
    ext x
    rw [(hf x).map_ωSup]
    rfl

lemma ωScottContinuous_toOrderHom : ωScottContinuous (α := A →𝒄 B) ContinuousHom.toOrderHom := by
  refine ωScottContinuous_pi_o fun x ↦ ?_
  apply ωScottContinuous_apply_c

lemma ωScottContinuous_toFun : ωScottContinuous (α := A →o B) OrderHom.toFun := by
  refine ωScottContinuous_pi fun x ↦ ?_
  apply ωScottContinuous_apply_o

lemma ωScottContinuous_s {f : A → B → C} {g : A →  B}
    (hf₁ : ωScottContinuous f)
    (hf₂ : ∀x, ωScottContinuous (fun y ↦ f x y))
    (hg : ωScottContinuous g) :
    ωScottContinuous (fun x ↦ f x (g x)) := by
  rw [ωScottContinuous_iff_monotone_map_ωSup']
  refine ⟨?_, ?_⟩
  . intro x₁ x₂ hx
    trans
    . apply hf₁.monotone hx
    . apply (hf₂ _).monotone
      apply hg.monotone
      apply hx
  . intro c
    rw [hf₁.map_ωSup, hg.map_ωSup]
    simp only [ωSup_pi, ωSup_le_iff, Chain.map_coe, Pi.evalOrderHom_coe, OrderHom.coe_mk, Function.comp_apply, Function.eval]
    intro i
    rw [(hf₂ _).map_ωSup]
    simp only [ωSup_le_iff, Chain.map_coe, OrderHom.coe_mk, Function.comp_apply]
    intro j
    apply le_ωSup_of_le (i ⊔ j)
    simp only [Chain.map_coe, OrderHom.coe_mk, Function.comp_apply]
    trans
    . apply hf₁.monotone
      apply c.monotone
      show i ≤ i ⊔ j
      apply le_sup_left
    . apply (hf₂ _).monotone
      apply hg.monotone
      apply c.monotone
      apply le_sup_right

@[fun_prop]
lemma ωScottContinuous_ωSup {f : A → ℕ →o B} (hf : ωScottContinuous f) : ωScottContinuous (fun x ↦ ωSup (f x)) := by
  rw [ωScottContinuous_iff_monotone_map_ωSup']
  refine ⟨?_, fun c ↦ ?_⟩
  . intro x₁ x₂ hx
    apply ωSup_le_ωSup_of_le
    intro i
    exists i
    apply hf.monotone hx
  . simp only [ωSup_le_iff]
    intro i
    simp only [hf.map_ωSup]
    rw [ωSup_opi]
    simp only [ωSup_le_iff, Chain.map_coe, OrderHom.apply_coe, OrderHom.coe_mk, Function.comp_apply, Function.eval]
    intro j
    apply le_ωSup_of_le j
    simp only [Chain.map_coe, OrderHom.coe_mk, Function.comp_apply]
    apply le_ωSup

lemma ωScottContinuous_subtype {P : B → Prop}
    (f : A → B) (p : ∀x, P (f x))
    (hf : ωScottContinuous f)
    (hp : ∀ (c : Chain B), (∀ i ∈ c, P i) → P (ωSup c))
    : let _ : OmegaCompletePartialOrder (Subtype P) := subtype P hp
      ωScottContinuous (fun x ↦ Subtype.mk (f x) (p x)) := by
  intro inst
  rw [ωScottContinuous_iff_monotone_map_ωSup']
  refine ⟨?_, fun c ↦ ?_⟩
  . intro x₁ x₂ hx
    simp only [Subtype.mk_le_mk]
    apply hf.monotone hx
  . show f (ωSup c) ≤ ωSup _
    rw [hf.map_ωSup]
    rfl

lemma ωScottContinuous_val {P : A → Prop}
    (hp : ∀ (c : Chain A), (∀ i ∈ c, P i) → P (ωSup c))
    : let _ : OmegaCompletePartialOrder (Subtype P) := subtype P hp
      ωScottContinuous (Subtype.val : Subtype P → A) := by
  intro inst
  rw [ωScottContinuous_iff_monotone_map_ωSup']
  refine ⟨?_, fun c ↦ ?_⟩
  . intro x₁ x₂ h
    exact h
  . rfl

@[fun_prop]
lemma ωScottContinuous_empty_elim : ωScottContinuous (Empty.elim (C := A)) := by
  intro _ _ _ _ _
  contradiction

@[fun_prop]
lemma ωScottContinuous_inl : ωScottContinuous (Sum.inl (α := A) (β := B)) := by
  rw [ωScottContinuous_iff_monotone_map_ωSup]
  refine ⟨?_, ?_⟩
  . apply Sum.inl_mono
  . intro c
    show _ = Sum.map ωSup ωSup (Chain.Sum.distrib (Chain.Sum.inl _))
    simp only [Chain.Sum.distrib_inl, Sum.map_inl]

@[fun_prop]
lemma ωScottContinuous_inr : ωScottContinuous (Sum.inr (α := A) (β := B)) := by
  rw [ωScottContinuous_iff_monotone_map_ωSup]
  refine ⟨?_, ?_⟩
  . apply Sum.inr_mono
  . intro c
    show _ = Sum.map ωSup ωSup (Chain.Sum.distrib (Chain.Sum.inr _))
    simp only [Chain.Sum.distrib_inr, Sum.map_inr]

@[fun_prop]
lemma ωScottContinuous_sum_elim {f : A → C} {g : B → C} (hf : ωScottContinuous f) (hg : ωScottContinuous g) : ωScottContinuous (Sum.elim f g) := by
  rw [ωScottContinuous_iff_monotone_map_ωSup]
  refine ⟨?_, ?_⟩
  . intro x₁ x₂ hx
    cases hx with
    | inl hx => apply hf.monotone hx
    | inr hx => apply hg.monotone hx
  . intro c
    rw [←Chain.Sum.elim_distrib c]
    cases Chain.Sum.distrib c with
    | inl c' =>
      simp only [Sum.elim_inl, ωSup_sum, Chain.Sum.distrib_inl, Sum.map_inl]
      rw [hf.map_ωSup]
      rfl
    | inr c' =>
      simp only [Sum.elim_inr, ωSup_sum, Chain.Sum.distrib_inr, Sum.map_inr]
      rw [hg.map_ωSup]
      rfl

@[fun_prop]
lemma ωScottContinuous_inj : ωScottContinuous (fun y ↦ (⟨x, y⟩ : (x : I) × P x)) := by
  rw [ωScottContinuous_iff_monotone_map_ωSup]
  refine ⟨?_, ?_⟩
  . intro y₁ y₂ hy
    simp only [Sigma.mk_le_mk_iff, hy]
  . intro c
    rfl

@[fun_prop]
lemma ωScottContinuous_fst : ωScottContinuous (Prod.fst (α := A) (β := B)) := by
  rw [ωScottContinuous_iff_monotone_map_ωSup]
  refine ⟨?_, ?_⟩
  . apply monotone_fst
  . intro c
    apply Prod.ωSup_fst

@[fun_prop]
lemma ωScottContinuous_snd : ωScottContinuous (Prod.snd (α := A) (β := B)) := by
  rw [ωScottContinuous_iff_monotone_map_ωSup]
  refine ⟨?_, ?_⟩
  . apply monotone_snd
  . intro c
    apply Prod.ωSup_snd

@[fun_prop]
lemma ωScottContinuous_prod_intro {f : A → B} {g : A → C} (hf : ωScottContinuous f) (hg : ωScottContinuous g) : ωScottContinuous (fun x ↦ (f x, g x)) := by
  rw [ωScottContinuous_iff_monotone_map_ωSup]
  refine ⟨?_, ?_⟩
  . intro x₁ x₂ hx
    simp only [Prod.mk_le_mk]
    refine ⟨?_, ?_⟩
    . apply hf.monotone hx
    . apply hg.monotone hx
  . intro c
    rw [hf.map_ωSup, hg.map_ωSup]
    rfl

@[fun_prop]
lemma ωScottContinuous_iterate {f : A → A} (h : ωScottContinuous f) n : ωScottContinuous (f^[n]) := by
  induction n with
  | zero => apply ωScottContinuous_id
  | succ n ih => apply ωScottContinuous.comp ih h

/--
Fixed point operator.
Returns ⊥ if the given function is not actually monotone.
-/
noncomputable def fix [OrderBot A] (f : A → A) : A :=
  open Classical in
  if h : Monotone f
  then ωSup (fixedPoints.iterateChain ⟨f, h⟩ ⊥ bot_le)
  else ⊥

@[simp]
lemma fix_unfold [OrderBot A] {f : A → A} (hf : ωScottContinuous f) : f (fix f) = fix f := by
  simp only [fix, hf.monotone, ↓reduceDIte]
  apply OmegaCompletePartialOrder.fixedPoints.ωSup_iterate_mem_fixedPoint ⟨⟨f, hf.monotone⟩, hf.map_ωSup⟩

@[fun_prop]
lemma ωScottContinuous_fix [OrderBot B] {f : A → B → B} (hf₁ : ωScottContinuous f) (hf₂ : ∀x, ωScottContinuous (f x)) : ωScottContinuous (fun x ↦ fix (f x)) := by
  unfold fix
  simp only [(hf₂ _).monotone, ↓reduceDIte]
  apply ωScottContinuous_ωSup
  rw [ωScottContinuous_iff_monotone_map_ωSup']
  refine ⟨?_, fun c ↦ ?_⟩
  . intro x₁ x₂ hx
    intro n
    show (f x₁)^[n] ⊥ ≤ (f x₂)^[n] ⊥
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [Function.iterate_succ', Function.comp_apply]
      trans
      . apply (hf₂ x₁).monotone ih
      . apply hf₁.monotone hx
  . intro n
    show (f (ωSup c))^[n] ⊥ ≤ _
    simp only [hf₁.map_ωSup, OrderHom.toFun_eq_coe, ωSup_opi]
    induction n with
    | zero => simp only [Function.iterate_zero, id_eq, bot_le]
    | succ n ih =>
      simp only [Function.iterate_succ', Function.comp_apply, ωSup_pi, ωSup_le_iff, Chain.map_coe, Pi.evalOrderHom_coe, OrderHom.coe_mk, Function.eval]
      intro i
      trans
      . apply (hf₂ (c i)).monotone
        apply ih
      . rw [(hf₂ _).map_ωSup]
        simp only [ωSup_le_iff, Chain.map_coe, OrderHom.coe_mk, OrderHom.apply_coe, Function.comp_apply, Function.eval]
        intro j
        show f (c i) ((f (c j))^[n] ⊥) ≤ _
        apply le_ωSup_of_le (i ⊔ j)
        simp only [Chain.map_coe, OrderHom.apply_coe, OrderHom.coe_mk, Function.comp_apply, Function.eval]
        show _ ≤ (f (c (i ⊔ j)))^[n + 1] ⊥
        simp only [Function.iterate_succ', Function.comp_apply]
        trans
        . apply hf₁.monotone
          apply c.monotone
          show i ≤ i ⊔ j
          simp only [le_sup_left]
        . apply (hf₂ (c (i ⊔ j))).monotone
          apply Monotone.iterate_le_of_le ((hf₂ (c j)).monotone)
          apply hf₁.monotone
          apply c.monotone
          simp only [le_sup_right]

end OmegaCompletePartialOrder
