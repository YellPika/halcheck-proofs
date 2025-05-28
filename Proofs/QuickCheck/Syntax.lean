import Proofs.Nat

namespace QuickCheck

/--
Types are divided into two kind: values and computations. Intuitively, values
"are", computations "do". One particular property unique to computation types is
that we can compute fixed points of computations, i.e., they support recursive
definitions.
-/
inductive Kind : Type where
  /-- Tag for value types. -/
  | val : Kind
  /-- Tag for computation types. -/
  | comp : Kind
  deriving DecidableEq

export Kind (val comp)

/-- Language types. -/
inductive QType : Kind → Type where
  /-- The type of booleans. -/
  | bool : QType val
  /-- The type `gen t` is the type of generators returning type `t`. -/
  | gen : QType val → QType comp
  /-- The type of functions. -/
  | arrow : QType val → QType comp → QType comp
  /-- Lifting computation types to value types. -/
  | thunk : QType comp → QType val
  deriving DecidableEq

instance QType.inhabited : Inhabited (QType k) where
  default :=
    match k with
    | val => bool
    | comp => gen bool

/-- Abbreviation for value types. -/
abbrev VType := QType val

/-- Abbreviation for computation types. -/
abbrev CType := QType comp

export QType (bool gen arrow thunk)

/--
Language terms.
-/
inductive QTerm : Kind → Type where
  /--
  Variables, represented as
  [DeBruijn Indices](https://en.wikipedia.org/wiki/De_Bruijn_index).
  Variables always refer to values, not computations.
  -/
  | var : ℕ → QTerm val

  /-- Truth. -/
  | tt : QTerm val

  /-- Falsity. -/
  | ff : QTerm val

  /-- Conditionals. -/
  | if_ : QTerm val → QTerm comp → QTerm comp → QTerm comp

  /-- A computation which returns a pure value. -/
  | return_ : QTerm val → QTerm comp

  /--
  The term `let t₁ t₂` denotes the sequential composition of computations `t₁` and `t₂`.
  The result of `t₁` is bound to variable zero in `t₂`.
  All remaining variables are shifted up one place in `t₂`.
  Normally, this is written as `let x ← t₁ in t₂`.
  -/
  | let_ : QTerm comp → QTerm comp → QTerm comp

  /-- Probabilistic choice. -/
  | choose : {q : ℚ // 0 ≤ q ∧ q ≤ 1} → QTerm comp

  /-- λ-abstraction. -/
  | lam : VType → QTerm comp → QTerm comp

  /-- Function application. -/
  | app : QTerm comp → QTerm val → QTerm comp

  /-- Fixed points. -/
  | fix : CType → QTerm comp → QTerm comp

  /-- Forcing. -/
  | force : QTerm val → QTerm comp

  /-- Delaying (or "thunking"). -/
  | delay : QTerm comp → QTerm val

  deriving DecidableEq

/-- Abbreviation for value terms. -/
abbrev VTerm := QTerm val

/-- Abbreviation for computation terms. -/
abbrev CTerm := QTerm comp

export QTerm (var tt ff return_ let_ if_ choose lam app fix force delay)

/-- **Renaming**: `map ρ t` replaces every free variable `x` in `t` with `ρ x`. -/
@[simp]
def QTerm.map (ρ : ℕ → ℕ) : QTerm k → QTerm k := fun
  | var x => var (ρ x)
  | tt => tt
  | ff => ff
  | if_ t₁ t₂ t₃ => if_ (map ρ t₁) (map ρ t₂) (map ρ t₃)
  | return_ t => return_ (map ρ t)
  | let_ t₁ t₂ => let_ (map ρ t₁) (map (Nat.cases 0 (ρ + 1)) t₂)
  | choose p => choose p
  | lam τ t => lam τ (map (Nat.cases 0 (ρ + 1)) t)
  | app t₁ t₂ => app (map ρ t₁) (map ρ t₂)
  | fix τ t => fix τ (map (Nat.cases 0 (ρ + 1)) t)
  | force t => force (map ρ t)
  | delay t => delay (map ρ t)

/-- Renaming every variable to itself is the identity function. -/
lemma QTerm.map_id' : map (fun x ↦ x) t = t := by
  induction t with
  | var x => rfl
  | tt => rfl
  | ff => rfl
  | if_ t₁ t₂ t₃ ih₁ ih₂ ih₃ =>
      rw [QTerm.map, ih₁, ih₂, ih₃]
  | return_ t ih =>
      rw [QTerm.map, ih]
  | let_ t₁ t₂ ih₁ ih₂ =>
      rw [QTerm.map, ih₁]
      have : (Nat.cases 0 (1 + fun x ↦ x)) = (fun x => x) := by
        funext x
        rw [@Pi.add_def]
        simp only [Pi.one_apply, Nat.cases_eta', id_eq]
      simp only [let_.injEq, true_and]
      rw [← ih₂]
      congr 1
      ring_nf
      apply this

  | choose p => rfl
  | lam τ t ih =>
      rw [QTerm.map]
      have : (Nat.cases 0 (1 + fun x ↦ x)) = (fun x => x) := by
        funext x
        cases x with
        | zero => rfl
        | succ n => exact (Nat.add_comm n 1).symm
      simp only [lam.injEq, true_and]
      rw [← ih]
      congr 1
      ring_nf
      apply this
  | app t₁ t₂ ih₁ ih₂ =>
      rw [QTerm.map, ih₁, ih₂]
  | fix τ t ih =>
      rw [QTerm.map]
      have : (Nat.cases 0 (1 + fun x ↦ x)) = (fun x => x) := by
        funext x
        cases x with
        | zero => rfl
        | succ n => exact Nat.add_comm 1 n
      simp only [fix.injEq, true_and]
      rw [← ih]
      congr 1
      ring_nf
      apply this
  | force t ih =>
      rw [QTerm.map, ih]
  | delay t ih =>
      rw [QTerm.map, ih]

lemma QTerm.map_id : map id t = t := map_id'

@[simp]
lemma QTerm.map_id_fun' : map (k := k) (fun x ↦ x) = id := by
  ext t
  apply map_id

@[simp]
lemma QTerm.map_id_fun : map (k := k) id = id := map_id_fun'

/-- Composition distributes over renaming. -/
@[simp]
lemma QTerm.map_map : map f (map g t) = map (f ∘ g) t := by
  induction t generalizing f g with
  | var x =>
      rfl
  | tt =>
      rfl
  | ff =>
      rfl
  | if_ t₁ t₂ t₃ ih₁ ih₂ ih₃ => simp [QTerm.map, ih₁, ih₂, ih₃]
  | return_ t ih => simp [QTerm.map, ih]
  | let_ t₁ t₂ ih₁ ih₂ =>
      simp only [QTerm.map]
      rw [ih₁, ih₂]
      congr 2
      funext x
      dsimp only [Function.comp_apply]
      cases x with
      | zero => rfl
      | succ n =>
        simp only [Nat.cases_succ]
        simp only [Pi.add_apply, Pi.one_apply, Function.comp_apply]
        simp only [Nat.cases_succ, Pi.add_apply, Pi.one_apply, Nat.add_left_inj]
  | choose p =>
      rfl
  | lam τ t ih =>
    simp only [map, lam.injEq, true_and, ih]
    congr 1
    funext x
    dsimp only [Function.comp_apply]
    cases x with
    | zero => rfl
    | succ n =>
      simp only [Nat.cases_succ, Pi.add_apply, Pi.one_apply, Function.comp_apply, Nat.add_left_inj]
  | app t₁ t₂ ih₁ ih₂ =>
    simp [QTerm.map, ih₁, ih₂]
  | fix τ t ih =>
    simp only [map, fix.injEq, true_and, ih]
    congr 1
    funext x
    dsimp only [Function.comp_apply]
    cases x with
    | zero => rfl
    | succ n =>
      simp only [Nat.cases_succ, Pi.add_apply, Pi.one_apply, Function.comp_apply, Nat.add_left_inj]

  | force _ ih => simp only [map, force.injEq, ih]
  | delay _ ih => simp only [map, delay.injEq, ih]

@[simp]
lemma QTerm.map_comp_map : map (k := k) f ∘ map g = map (f ∘ g) := by
  ext t
  simp only [Function.comp_apply, map_map]

/-- **Substitution:** `bind σ t` subsitutes every free variable `x` in `t` with `σ x`. -/
@[simp]
def QTerm.bind (σ : ℕ → QTerm val) : QTerm k → QTerm k := fun
  | var x => σ x
  | tt => tt
  | ff => ff
  | return_ t => return_ (bind σ t)
  | let_ t₁ t₂ => let_ (bind σ t₁) (bind (Nat.cases (var 0) (map (· + 1) ∘ σ)) t₂)
  | if_ t₁ t₂ t₃ => if_ (bind σ t₁) (bind σ t₂) (bind σ t₃)
  | choose p => choose p
  | lam τ t => lam τ (bind (Nat.cases (var 0) (map (· + 1) ∘ σ)) t)
  | app t₁ t₂ => app (bind σ t₁) (bind σ t₂)
  | fix τ t => fix τ (bind (Nat.cases (var 0) (map (· + 1) ∘ σ)) t)
  | force t => force (bind σ t)
  | delay t => delay (bind σ t)

/-- Substituting every variable with itself is the identity function. -/
lemma QTerm.bind_var : bind var t = t := by
  induction t with
  | var x =>
    rfl
  | tt =>
    rfl
  | ff =>
    rfl
  | if_ t₁ t₂ t₃ ih₁ ih₂ ih₃ =>
    simp [QTerm.bind, ih₁, ih₂, ih₃]
  | return_ t ih =>
    simp [QTerm.bind, ih]
  | let_ t₁ t₂ ih₁ ih₂ =>
    simp only [QTerm.bind]
    rw [ih₁]
    rw [← ih₁]
    rw [← ih₂]
    simp only [let_.injEq, true_and]
    congr 1
    funext x
    cases x with
    | zero => rfl
    | succ n =>
      simp only [Nat.cases_succ, Function.comp_apply, map, var.injEq]
  | choose p =>
    rfl
  | lam τ t ih =>
    simp only [QTerm.bind]
    congr 1
    have h : (Nat.cases (var 0) ((map fun x ↦ x + 1) ∘ var)) = var := by
      funext x
      cases x with
      | zero => rfl
      | succ n =>
        simp only [Nat.cases_succ, Function.comp_apply, map, var.injEq]
    rw [h, ih]
  | app t₁ t₂ ih₁ ih₂ =>
    simp [QTerm.bind, ih₁, ih₂]
  | fix τ t ih =>
    simp only [QTerm.bind]
    congr 1
    have h : (Nat.cases (var 0) ((map fun x ↦ x + 1) ∘ var)) = var := by
      funext x
      cases x with
      | zero => rfl
      | succ n =>
        simp only [Nat.cases_succ, Function.comp_apply, map, var.injEq]
    rw [h, ih]
  | force t ih =>
    simp [QTerm.bind, ih]
  | delay t ih =>
    simp [QTerm.bind, ih]

@[simp]
lemma QTerm.bind_var_fun' : bind (k := k) var = id := by
  ext t
  apply bind_var

/--
Distributivity of substitution composed with renaming.
Necessary to prove `bind_bind`.
-/
@[simp]
lemma QTerm.bind_map : bind f (map g t) = bind (f ∘ g) t := by
  induction t generalizing f g with
  | var x => rfl
  | tt => rfl
  | ff => rfl
  | if_ t₁ t₂ t₃ ih₁ ih₂ ih₃ => simp [QTerm.bind, QTerm.map, ih₁, ih₂, ih₃]
  | return_ t ih => simp [QTerm.bind, QTerm.map, ih]
  | let_ t₁ t₂ ih₁ ih₂ =>
    simp only [QTerm.bind, QTerm.map]
    rw [ih₁, ih₂]
    congr
    funext x
    cases x with
    | zero => rfl
    | succ n =>
      simp only [Function.comp_apply, Nat.cases_succ, Pi.add_apply, Pi.one_apply]
  | choose p => rfl
  | lam τ t ih =>
    simp only [QTerm.bind, QTerm.map, lam.injEq, true_and]
    rw [ih]
    congr
    funext x
    cases x with
    | zero => rfl
    | succ n =>
      simp only [Function.comp_apply, Nat.cases_succ, Pi.add_apply, Pi.one_apply]
  | app t₁ t₂ ih₁ ih₂ => simp only [QTerm.bind, QTerm.map, ih₁, ih₂]
  | fix τ t ih =>
    simp only [QTerm.bind, QTerm.map, fix.injEq, true_and]
    rw [ih]
    congr
    funext x
    cases x with
    | zero => rfl
    | succ n =>
      simp only [Function.comp_apply, Nat.cases_succ, Pi.add_apply, Pi.one_apply]
  | force t ih =>
    simp only [QTerm.bind, QTerm.map]
    rw [ih]
  | delay t ih =>
    simp only [QTerm.bind, QTerm.map]
    rw [ih]

@[simp]
lemma QTerm.bind_comp_map : bind (k := k) f ∘ map g = bind (f ∘ g) := by
  ext t
  apply bind_map

/--
Distributivity of substitution composed with renaming.
Necessary to prove `bind_bind`.
-/
@[simp]
lemma QTerm.map_bind : map f (bind g t) = bind (map f ∘ g) t := by
  induction t generalizing f g with
  | var x => rfl
  | tt => rfl
  | ff => rfl
  | if_ t₁ t₂ t₃ ih₁ ih₂ ih₃ => simp [QTerm.bind, QTerm.map, ih₁, ih₂, ih₃]
  | return_ t ih => simp [QTerm.bind, QTerm.map, ih]
  | let_ t₁ t₂ ih₁ ih₂ =>
    simp only [QTerm.bind, QTerm.map]
    rw [ih₁, ih₂]
    congr
    funext x
    cases x with
    | zero => rfl
    | succ n =>
      simp only [Function.comp_apply, Nat.cases_succ, map_map]
      congr 1
  | choose p => rfl
  | lam τ t ih =>
    simp only [QTerm.bind, QTerm.map, ih]
    congr
    funext x
    cases x with
    | zero => rfl
    | succ n =>
      simp only [Function.comp_apply, Nat.cases_succ, map_map]
      congr 1
  | app t₁ t₂ ih₁ ih₂ => simp [QTerm.bind, QTerm.map, ih₁, ih₂]
  | fix τ t ih =>
    simp only [QTerm.bind, QTerm.map, ih]
    congr
    funext x
    cases x with
    | zero => rfl
    | succ n =>
      simp only [Function.comp_apply, Nat.cases_succ, map_map]
      congr 1
  | force t ih => simp [QTerm.bind, QTerm.map, ih]
  | delay t ih => simp [QTerm.bind, QTerm.map, ih]

@[simp]
lemma QTerm.map_comp_bind : map (k := k) f ∘ bind g = bind (map f ∘ g) := by
  ext t
  apply map_bind

/-- Composition distributes over substitution. -/
@[simp]
lemma QTerm.bind_bind : bind f (bind g t) = bind (bind f ∘ g) t := by
  induction t generalizing f g with
  | var x => simp [bind, Function.comp_apply]
  | tt => simp [bind]
  | ff => simp [bind]
  | if_ t₁ t₂ t₃ ih₁ ih₂ ih₃ => simp [bind, ih₁, ih₂, ih₃]
  | return_ t ih => simp [bind, ih]
  | let_ t₁ t₂ ih₁ ih₂ =>
    simp only [bind, let_.injEq]
    rw [ih₁, ih₂]
    simp only [Nat.comp_cases, bind, Nat.cases_zero, true_and]
    congr 1
    funext x
    cases x with
    | zero => simp [Nat.cases_zero, Function.comp_apply, bind]
    | succ n =>
      simp only [Nat.cases_succ, Function.comp_apply]
      rw [QTerm.map_bind, QTerm.bind_map]
      congr 1
  | choose p => simp [bind]
  | lam τ t ih =>
    simp only [bind]
    rw [ih]
    congr
    funext x
    cases x with
    | zero => simp [Nat.cases_zero, Function.comp_apply, bind]
    | succ n =>
      simp only [Nat.cases_succ, Function.comp_apply]
      rw [QTerm.map_bind, QTerm.bind_map]
      congr 1
  | app t₁ t₂ ih₁ ih₂ => simp [bind, ih₁, ih₂]
  | fix τ t ih =>
    simp only [bind, fix.injEq, true_and]
    rw [ih]
    congr 1
    funext x
    cases x with
    | zero => simp [Nat.cases_zero, Function.comp_apply, bind]
    | succ n =>
      simp only [Nat.cases_succ, Function.comp_apply]
      rw [QTerm.map_bind, QTerm.bind_map]
      congr 1
  | force t ih => simp [bind, ih]
  | delay t ih => simp [bind, ih]

@[simp]
lemma QTerm.bind_comp : bind (k := k) f ∘ bind g = bind (bind f ∘ g) := by
  ext t
  apply bind_bind

/-- The set of free variables in a term. -/
@[simp]
def QTerm.free : QTerm k → Set ℕ := fun
  | var x => {x}
  | tt => ∅
  | ff => ∅
  | if_ t₁ t₂ t₃ => free t₁ ∪ free t₂ ∪ free t₃
  | return_ t => free t
  | let_ t₁ t₂ => free t₁ ∪ {x | x + 1 ∈ free t₂}
  | choose p => ∅
  | lam _ t => {x | x + 1 ∈ free t}
  | app t₁ t₂ => free t₁ ∪ free t₂
  | fix _ t => {x | x + 1 ∈ free t}
  | force t => free t
  | delay t => free t

lemma QTerm.map_congr (h : ∀x ∈ free t, f x = g x) : map f t = map g t := by
  induction t generalizing f g with
  | var x =>
    simp only [map, var.injEq]
    exact h x (Set.mem_singleton x)
  | tt =>
    simp [QTerm.map]
  | ff =>
    simp [QTerm.map]
  | if_ t₁ t₂ t₃ ih₁ ih₂ ih₃ =>
    simp only [QTerm.map, QTerm.free, Set.union_def, Set.mem_setOf_eq] at h ⊢
    congr 1
    apply ih₁
    intro x hx
    rw [h x (Or.inl (Or.inl hx))]
    apply ih₂
    intro y hy
    rw [h y (Or.inl (Or.inr hy))]
    apply ih₃
    intro z hz
    rw [h z (Or.inr hz)]
  | return_ t ih =>
    simp only [QTerm.map, QTerm.free] at h ⊢
    congr 1
    apply ih
    intro x hx
    rw [h x hx]
  | let_ t₁ t₂ ih₁ ih₂ =>
    simp only [QTerm.map, QTerm.free, Set.union_def, Set.mem_setOf_eq] at h ⊢
    congr 1
    · apply ih₁
      intro x hx
      exact h x (Or.inl hx)
    · apply ih₂
      intro y hy
      cases y with
      | zero => simp [Nat.cases_zero]
      | succ n =>
        simp only [Nat.cases_succ, Pi.add_apply, Pi.one_apply, Nat.add_left_inj]
        rw [Mathlib.Tactic.Zify.natCast_eq, h n (Or.inr hy)]
  | choose p =>
    simp [QTerm.map]
  | lam τ t ih =>
    simp only [QTerm.map, QTerm.free, Set.mem_setOf_eq] at h ⊢
    congr 1
    apply ih
    intro y hy
    cases y with
    | zero => simp [Nat.cases_zero]
    | succ n =>
      simp only [Nat.cases_succ]
      rw [@Pi.add_apply]
      simp only [Pi.one_apply, Pi.add_apply, Nat.add_right_inj]
      rw [h n hy]
  | app t₁ t₂ ih₁ ih₂ =>
    simp only [QTerm.map, QTerm.free, Set.union_def, Set.mem_setOf_eq] at h ⊢
    congr 1
    · apply ih₁
      intro x hx
      exact h x (Or.inl hx)
    · apply ih₂
      intro x hx
      exact h x (Or.inr hx)
  | fix τ t ih =>
    simp only [QTerm.map, QTerm.free, Set.mem_setOf_eq] at h ⊢
    congr 1
    apply ih
    intro y hy
    cases y with
    | zero => simp [Nat.cases_zero]
    | succ n =>
      simp only [Nat.cases_succ]
      rw [@Pi.add_apply]
      simp only [Pi.one_apply, Pi.add_apply, Nat.add_right_inj]
      rw [h n hy]
  | force t ih =>
    simp only [QTerm.map, QTerm.free] at h ⊢
    congr 1
    apply ih
    intro x hx
    rw [h x hx]
  | delay t ih =>
    simp only [QTerm.map, QTerm.free] at h ⊢
    congr 1
    apply ih
    intro x hx
    rw [h x hx]

lemma QTerm.bind_congr (h : ∀x ∈ free t, f x = g x) : bind f t = bind g t := by
  induction t generalizing f g with
  | var x =>
    simp only [bind, free, Set.mem_singleton_iff] at h ⊢
    exact h x rfl
  | tt =>
    simp [bind]
  | ff =>
    simp [bind]
  | if_ t₁ t₂ t₃ ih₁ ih₂ ih₃ =>
    simp only [bind, free, Set.union_def, Set.mem_setOf_eq] at h ⊢
    congr 1
    · apply ih₁
      intro x hx
      exact h x (Or.inl (Or.inl hx))
    · apply ih₂
      intro x hx
      exact h x (Or.inl (Or.inr hx))
    · apply ih₃
      intro x hx
      exact h x (Or.inr hx)
  | return_ t ih =>
    simp only [bind, free] at h ⊢
    congr 1
    apply ih
    intro x hx
    exact h x hx
  | let_ t₁ t₂ ih₁ ih₂ =>
    simp only [bind, free, Set.union_def, Set.mem_setOf_eq] at h ⊢
    congr 1
    · apply ih₁
      intro x hx
      exact h x (Or.inl hx)
    · apply ih₂
      intro y hy
      cases y with
      | zero => simp [Nat.cases_zero]
      | succ n =>
        simp only [Nat.cases_succ, Function.comp_apply]
        congr 1
        exact h n (Or.inr hy)
  | choose p =>
    simp [bind]
  | lam τ t ih =>
    simp only [bind, free, Set.mem_setOf_eq] at h ⊢
    congr 1
    apply ih
    intro y hy
    cases y with
    | zero => simp [Nat.cases_zero]
    | succ n =>
      simp only [Nat.cases_succ, Function.comp_apply]
      congr 1
      exact h n hy
  | app t₁ t₂ ih₁ ih₂ =>
    simp only [bind, free, Set.union_def, Set.mem_setOf_eq] at h ⊢
    congr 1
    · apply ih₁
      intro x hx
      exact h x (Or.inl hx)
    · apply ih₂
      intro x hx
      exact h x (Or.inr hx)
  | fix τ t ih =>
    simp only [bind, free, Set.mem_setOf_eq] at h ⊢
    congr 1
    apply ih
    intro y hy
    cases y with
    | zero => simp [Nat.cases_zero]
    | succ n =>
      simp only [Nat.cases_succ, Function.comp_apply]
      congr 1
      exact h n hy
  | force t ih =>
    simp only [bind, free] at h ⊢
    congr 1
    apply ih
    intro x hx
    exact h x hx
  | delay t ih =>
    simp only [bind, free] at h ⊢
    congr 1
    apply ih
    intro x hx
    exact h x hx

end QuickCheck
