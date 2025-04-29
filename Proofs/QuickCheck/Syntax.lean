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
  | let_ t₁ t₂ => let_ (map ρ t₁) (map (Nat.cases 0 (1 + ρ)) t₂)
  | choose p => choose p
  | lam τ t => lam τ (map (Nat.cases 0 (1 + ρ)) t)
  | app t₁ t₂ => app (map ρ t₁) (map ρ t₂)
  | fix τ t => fix τ (map (Nat.cases 0 (1 + ρ)) t)
  | force t => force (map ρ t)
  | delay t => delay (map ρ t)

/-- Renaming every variable to itself is the identity function. -/
lemma QTerm.map_id' : map (fun x ↦ x) t = t := by
  sorry

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
  sorry

@[simp]
lemma QTerm.map_comp_map : map (k := k) f ∘ map g = map (f ∘ g) := by
  ext t
  simp only [Function.comp_apply, map_map]

/-- **Substitution:** `bind σ t` subsitutes every free variable `x` in `t` with `σ x`. -/
@[simp]
def QTerm.bind (σ : ℕ → QTerm val) : QTerm k → QTerm k := fun
  | var x        => σ x
  | tt        => tt
  | ff       => ff
  | return_ t    => return_ (bind σ t)
  | let_ t₁ t₂   => let_ (bind σ t₁) (bind (Nat.cases (var 0) (map (· + 1) ∘ σ)) t₂)
  | if_ t₁ t₂ t₃ => if_ (bind σ t₁) (bind σ t₂) (bind σ t₃)
  | choose p    => choose p
  | lam τ t => lam τ (bind (Nat.cases (var 0) (map (· + 1) ∘ σ)) t)
  | app t₁ t₂ => app (bind σ t₁) (bind σ t₂)
  | fix τ t => fix τ (bind (Nat.cases (var 0) (map (· + 1) ∘ σ)) t)
  | force t => force (bind σ t)
  | delay t => delay (bind σ t)

/-- Substituting every variable with itself is the identity function. -/
lemma QTerm.bind_var : bind var t = t := by
  sorry

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
  sorry

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
  sorry

@[simp]
lemma QTerm.map_comp_bind : map (k := k) f ∘ bind g = bind (map f ∘ g) := by
  ext t
  apply map_bind

/-- Composition distributes over substitution. -/
@[simp]
lemma QTerm.bind_bind : bind f (bind g t) = bind (bind f ∘ g) t := by
  sorry

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
  sorry

lemma QTerm.bind_congr (h : ∀x ∈ free t, f x = g x) : bind f t = bind g t := by
  sorry

end QuickCheck
