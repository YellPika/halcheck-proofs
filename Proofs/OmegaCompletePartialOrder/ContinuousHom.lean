import Proofs.OmegaCompletePartialOrder.OmegaScottContinuity

namespace OmegaCompletePartialOrder.ContinuousHom

variable
  [OmegaCompletePartialOrder A]
  [OmegaCompletePartialOrder B]
  [OmegaCompletePartialOrder C]

instance [OrderBot B] : OrderBot (A →𝒄 B) where
  bot := const ⊥
  bot_le := fun f x ↦ by simp only [OrderHom.toFun_eq_coe, coe_toOrderHom, const_apply, bot_le]

/-- Utility for creating continuous functions from proofs of continuity. -/
@[simps!]
def ofProof {f : A → B} (hf : ωScottContinuous f) : A →𝒄 B where
  toFun := f
  monotone' := hf.monotone
  map_ωSup' := hf.map_ωSup

/-- Utility for specifying continuous functions with an automatic continuity proof. -/
@[simps!]
def mk' (f : A → B) (hf : ωScottContinuous f := by fun_prop) : A →𝒄 B where
  toFun := f
  monotone' := hf.monotone
  map_ωSup' := hf.map_ωSup

@[fun_prop]
lemma ωScottContinuous_mk' (f : C → A → B) (hf₀ : ωScottContinuous f) (hf₁ : ∀x, ωScottContinuous (f x)) : ωScottContinuous (fun x ↦ mk' (f x) (hf₁ x)) := by
  apply ωScottContinuous_pi_c fun x ↦ ?_
  simp only [mk'_apply]
  apply ωScottContinuous.apply₂ hf₀

/--
Converts a normal function into a continuous one.
If the given function is not continuous, the behaviour is not defined.
-/
@[simps!]
noncomputable def ofFun (f : A → B) : A →𝒄 B := by
  open Classical in
  apply mk' (if ωScottContinuous f then f else fun x ↦ Classical.choice ⟨f x⟩) ?_
  by_cases h : ωScottContinuous f
  . simp only [h, ↓reduceIte]
  . simp only [h, ↓reduceIte]
    by_cases h' : Nonempty B
    . apply ωScottContinuous_const (Classical.choice h')
    . rw [ωScottContinuous_iff_monotone_map_ωSup]
      refine ⟨?_, ?_⟩
      . intro x
        have : Nonempty B := ⟨f x⟩
        contradiction
      . intro c
        have : Nonempty B := ⟨f (c 0)⟩
        contradiction

/-- The elimination function for `Empty`. -/
@[simps!]
def Empty.elim : Empty →𝒄 A := ofProof ωScottContinuous_empty_elim

/-- The introduction function for `Unit`. -/
@[simps!]
def Unit.intro : A →𝒄 Unit := ContinuousHom.const ()

/-- The left injection for `Sum`. -/
@[simps!]
def Sum.inl : A →𝒄 A ⊕ B := ofProof ωScottContinuous_inl

/-- The right injection for `Sum`. -/
@[simps!]
def Sum.inr : B →𝒄 A ⊕ B := ofProof ωScottContinuous_inr

/-- The elimination function for `Sum`. -/
@[simps!]
def Sum.elim (f : A →𝒄 C) (g : B →𝒄 C) : A ⊕ B →𝒄 C :=
  ofProof (ωScottContinuous_sum_elim f.ωScottContinuous g.ωScottContinuous)

@[simp]
lemma Sum.elim_inl (f : A →𝒄 C) (g : B →𝒄 C) : (Sum.elim f g).comp Sum.inl = f := rfl

@[simp]
lemma Sum.elim_inr (f : A →𝒄 C) (g : B →𝒄 C) : (Sum.elim f g).comp Sum.inr = g := rfl

lemma Sum.elim_uniq {f : A →𝒄 C} {g : B →𝒄 C} (hf : h.comp Sum.inl = f) (hg : h.comp Sum.inr = g) : h = Sum.elim f g := by
  ext x
  cases x with
  | inl x =>
    show (h.comp Sum.inl) x = f x
    congr
  | inr x =>
    show (h.comp Sum.inr) x = g x
    congr

/-- The left eliminator for `Prod`. -/
@[simps!]
def Prod.fst : A × B →𝒄 A := ofProof ωScottContinuous_fst

/-- The right eliminator for `Prod`. -/
@[simps!]
def Prod.snd : A × B →𝒄 B := ofProof ωScottContinuous_snd

/-- The introduction function for `Prod`. -/
@[simps!]
def Prod.intro (f : A →𝒄 B) (g : A →𝒄 C) : A →𝒄 B × C := ofProof (ωScottContinuous_prod_intro f.ωScottContinuous g.ωScottContinuous)

lemma Prod.intro_uniq {f : A →𝒄 B} {g : A →𝒄 C} {h : A →𝒄 B × C} (hf : fst.comp h = f) (hg : snd.comp h = g) : h = intro f g := by
  ext x
  . simp only [← hf, intro_apply, comp_apply, fst_apply]
  . simp only [← hg, intro_apply, comp_apply, snd_apply]

/-- Currying for continuous functions. -/
@[simps!]
def curry : (A × B →𝒄 C) →𝒄 (A →𝒄 B →𝒄 C) := by
  apply mk' (fun f ↦ mk' (fun x ↦ mk' (fun y ↦ f (x, y)) ?a) ?b) ?c
  case a => fun_prop
  case b => fun_prop
  case c => fun_prop

/-- Uncurrying for continuous functions. -/
@[simps!]
def uncurry : (A →𝒄 B →𝒄 C) →𝒄 (A × B →𝒄 C) := by
  apply mk' (fun f ↦ mk' (fun x ↦ f x.1 x.2) ?a) ?b
  case a => apply ωScottContinuous_s <;> fun_prop
  case b =>
    refine ωScottContinuous_pi_c fun x ↦ ?_
    dsimp only [mk'_apply]
    apply ωScottContinuous_s <;> fun_prop

@[simp]
lemma curry_comp_uncurry : curry.comp (uncurry (A := A) (B := B) (C := C)) = id := rfl

@[simp]
lemma uncurry_comp_curry : uncurry.comp (curry (A := A) (B := B) (C := C)) = id := rfl

/-- Function application. -/
@[simps!]
def apply : (A →𝒄 B) × A →𝒄 B := uncurry id

/-- Applying constants to arbitrary functions. -/
@[simps!]
def Pi.apply {P : D → Type*} [∀x, OmegaCompletePartialOrder (P x)] x : (∀x, P x) →𝒄 P x :=
  ofProof ωScottContinuous_apply

/-- The fixpoint function is continuous! -/
def fix [OrderBot A] : (A →𝒄 A) →𝒄 A := by
  apply mk' (fun (f : A →𝒄 A) ↦ ωSup (fixedPoints.iterateChain (f : A →o A) ⊥ bot_le)) ?_
  have := ωScottContinuous_fix (f := fun (f : A →𝒄 A) ↦ f)
  unfold OmegaCompletePartialOrder.fix at this
  simp only [ContinuousHom.monotone, ↓reduceDIte] at this
  apply this <;> fun_prop

@[simp]
lemma fix_fold [OrderBot A] (f : A →𝒄 A) : f (fix f) = fix f := by
  apply fixedPoints.ωSup_iterate_mem_fixedPoint

@[simp]
lemma fix_fold_comp [OrderBot A] (f : A →𝒄 A) : f.comp (fix.comp (const f)) = fix.comp (const (α := B) f) := by
  ext x
  simp only [comp_assoc, comp_apply, const_apply, fix_fold]

end OmegaCompletePartialOrder.ContinuousHom
