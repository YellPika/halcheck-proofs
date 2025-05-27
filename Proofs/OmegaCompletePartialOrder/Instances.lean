import Proofs.OmegaCompletePartialOrder.Chain

namespace OmegaCompletePartialOrder

variable
  {I : Type*} {P : I → Type*}
  [OmegaCompletePartialOrder A]
  [OmegaCompletePartialOrder B]
  [OmegaCompletePartialOrder C]
  [(x : I) → OmegaCompletePartialOrder (P x)]

/-- Any type can be assigned an ω-complete partial order. -/
def discrete {A} : OmegaCompletePartialOrder A where
  le := (· = ·)
  le_refl := by simp only [implies_true]
  le_trans := by simp only [forall_apply_eq_imp_iff, imp_self, implies_true]
  le_antisymm := by simp only [forall_eq', imp_self, implies_true]
  ωSup := fun c ↦ c 0
  ωSup_le := by
    intros
    simp_all only
  le_ωSup := by
    rintro ⟨c, hc⟩ i
    symm
    apply hc
    simp only [zero_le]

instance : OmegaCompletePartialOrder Empty := discrete

instance : OmegaCompletePartialOrder Unit := discrete

instance : OmegaCompletePartialOrder (A ⊕ B) where
  ωSup := Sum.map ωSup ωSup ∘ Chain.Sum.distrib
  ωSup_le := by
    intro c x h
    simp only [Function.comp_apply, ge_iff_le]
    cases x with
    | inl x =>
      cases h₀ : Chain.Sum.distrib c with
      | inl c' =>
        conv at h => { enter [x]; rw [←Chain.Sum.elim_distrib c, h₀] }
        simp only [Sum.elim_inl, Chain.Sum.inl_apply, ge_iff_le, Sum.inl_le_inl_iff] at h
        simp only [Sum.map_inl, Sum.inl_le_inl_iff, ωSup_le_iff, h, implies_true]
      | inr c' =>
        specialize h 0
        conv at h => { rw [←Chain.Sum.elim_distrib c, h₀] }
        simp only [Sum.elim_inr, Chain.Sum.inr_apply, ge_iff_le, Sum.not_inr_le_inl] at h
    | inr x =>
      cases h₀ : Chain.Sum.distrib c with
      | inr c' =>
        conv at h => { enter [x]; rw [←Chain.Sum.elim_distrib c, h₀] }
        simp only [Sum.elim_inr, Chain.Sum.inr_apply, ge_iff_le, Sum.inr_le_inr_iff] at h
        simp only [Sum.map_inr, Sum.inr_le_inr_iff, ωSup_le_iff, h, implies_true]
      | inl c' =>
        specialize h 0
        conv at h => { rw [←Chain.Sum.elim_distrib c, h₀] }
        simp only [Sum.elim_inl, Chain.Sum.inl_apply, ge_iff_le, Sum.not_inl_le_inr] at h
  le_ωSup := by
    intro c i
    simp only [Function.comp_apply, ge_iff_le]
    cases h₀ : c 0 with
    | inl x =>
      rw [←Chain.Sum.elim_distrib c]
      cases h₁ : Chain.Sum.distrib c with
      | inl c' =>
        simp only [Sum.elim_inl, Chain.Sum.inl_apply, Chain.Sum.distrib_inl, Sum.map_inl, Sum.inl_le_inl_iff]
        apply le_ωSup
      | inr c' =>
        rw [←Chain.Sum.elim_distrib c, h₁] at h₀
        simp only [Sum.elim_inr, Chain.Sum.inr_apply, reduceCtorEq] at h₀
    | inr x =>
      rw [←Chain.Sum.elim_distrib c]
      cases h₁ : Chain.Sum.distrib c with
      | inr c' =>
        simp only [Sum.elim_inr, Chain.Sum.inr_apply, Chain.Sum.distrib_inr, Sum.map_inr, Sum.inr_le_inr_iff]
        apply le_ωSup
      | inl c' =>
        rw [←Chain.Sum.elim_distrib c, h₁] at h₀
        simp only [Sum.elim_inl, Chain.Sum.inl_apply, reduceCtorEq] at h₀

instance [OrderBot A] : OmegaCompletePartialOrder { x : A // x ≠ ⊥ } where
  ωSup c :=
    ⟨ ωSup (c.map (OrderHom.Subtype.val _))
    , by
        intro h
        have : ωSup (c.map (OrderHom.Subtype.val fun x ↦ x ≠ ⊥)) ≤ ⊥
        . simp only [ne_eq, h, le_refl]
        simp only [ωSup_le_iff, Chain.map_coe, OrderHom.Subtype.val_coe, Function.comp_apply] at this
        simp only [ne_eq, le_bot_iff] at this
        specialize this 0
        have := (c 0).property
        contradiction
    ⟩

  le_ωSup c i := by
    apply le_ωSup_of_le i
    apply le_refl

  ωSup_le c x hc := by
    apply ωSup_le
    apply hc

instance : OmegaCompletePartialOrder (∀x, P x) where
  ωSup c x := ωSup (c.map (Pi.evalOrderHom x))
  le_ωSup c x n := by
    apply le_ωSup_of_le x
    simp only [Chain.map_coe, Pi.evalOrderHom_coe, Function.comp_apply, Function.eval, le_refl]
  ωSup_le c f h₀ x := by
    simp only [ωSup_le_iff, Chain.map_coe, OrderHom.coe_mk, Function.comp_apply]
    intro i
    apply h₀

instance [Preorder I] : OmegaCompletePartialOrder (I →o A) where
  ωSup c :=
    ⟨ fun x ↦ ωSup (c.map (OrderHom.apply x))
    , by
        intro x₁ x₂ hx
        simp only [ωSup_le_iff, Chain.map_coe, OrderHom.apply_coe, Function.comp_apply, Function.eval]
        intro i
        apply le_ωSup_of_le i
        simp only [Chain.map_coe, OrderHom.apply_coe, Function.comp_apply, Function.eval]
        apply (c i).monotone hx
    ⟩
  le_ωSup c i x := by
    simp only [OrderHom.toFun_eq_coe]
    apply le_ωSup_of_le i
    simp only [Chain.map_coe, OrderHom.apply_coe, Function.comp_apply, Function.eval, le_refl]
  ωSup_le c f h₀ x := by
    simp only [OrderHom.toFun_eq_coe, ωSup_le_iff, Chain.map_coe, OrderHom.apply_coe, Function.comp_apply, Function.eval]
    intro i
    apply h₀

instance : OmegaCompletePartialOrder ((x : I) × P x) where
  ωSup c :=
    let x := Chain.Sigma.distrib c
    ⟨x.1, ωSup x.2⟩
  le_ωSup c i := by
    simp only [ge_iff_le]
    rw [Chain.Sigma.distrib_at]
    constructor
    apply le_ωSup
  ωSup_le c x hx := by
    rcases x with ⟨x₁, x₂⟩
    simp only [ge_iff_le]
    simp only [Chain.Sigma.distrib_at] at hx
    cases hx 0
    simp only [Sigma.mk_le_mk_iff, ωSup_le_iff] at ⊢ hx
    exact hx

end OmegaCompletePartialOrder
