import Mathlib

/-- The type of node-labelled, finitely branching trees. -/
structure Rose (A : Type) : Type where
  /-- The label of the root node. -/
  label : A

  /-- The list of child trees. -/
  children : List (Rose A)

namespace Rose

/-- Grafts a tree to every sub-node in a `Rose` tree. -/
@[simp]
def bind (f : A → Rose B) : Rose A → Rose B := fun
  | ⟨x, xs⟩ =>
      match f x with
      | ⟨y, ys⟩ => ⟨y, ys ++ List.map (bind f) xs⟩

instance : Monad Rose where
  pure x := ⟨x, []⟩
  bind := flip bind

lemma bind_pure : bind (fun x ↦ ⟨x, []⟩) t = t := by
  sorry

@[simp]
lemma bind_pure_fun : bind (A := A) (fun x ↦ ⟨x, []⟩) = id := by
  ext
  apply bind_pure

@[simp]
lemma bind_bind : bind f (bind g t) = bind (bind f ∘ g) t := by
  sorry

@[simp]
lemma bind_comp : bind f ∘ bind g = bind (bind f ∘ g) := by
  ext t
  apply bind_bind

@[simp]
lemma match_id (t : Rose A) : (match t with | ⟨x, xs⟩ => ⟨x, xs⟩) = t := by
  cases t
  rfl

@[simp]
lemma bind_eq : Bind.bind t f = bind f t := rfl

@[simp]
lemma pure_eq : (pure x : Rose A) = ⟨x, []⟩ := rfl

@[simp]
lemma seq_eq : f <*> t = bind (fun f ↦ f <$> t) f := rfl

@[simp]
lemma map_eq : f <$> t = bind (fun x ↦ pure (f x)) t := rfl

@[simp]
lemma seqLeft_eq : t <* u = bind (fun x ↦ (fun _ ↦ x) <$> u) t := rfl

@[simp]
lemma seqRight_eq : t *> u = bind (fun _ ↦ u) t := rfl

instance : LawfulMonad Rose where
  bind_pure_comp := by
    simp only [pure_eq, bind_eq, map_eq, implies_true]

  bind_map := by
    simp only [map_eq, pure_eq, bind_eq, seq_eq, implies_true]

  pure_bind := by
    intro A B t f
    simp only [pure_eq, bind_eq, bind, List.map_nil, List.append_nil, match_id]

  bind_assoc := by
    intro A B C t f g
    simp only [bind_eq, bind_bind]
    rfl

  seqLeft_eq := by
    intro A B t u
    simp only [seqLeft_eq, map_eq, pure_eq, seq_eq, bind_bind]
    congr
    ext x
    simp only [Function.comp_apply, bind, Function.const_apply, List.map_nil, List.append_nil, match_id]

  seqRight_eq := by
    intro A B t u
    simp only [seqRight_eq, map_eq, Function.const_apply, pure_eq, seq_eq, bind_bind]
    congr
    ext x
    simp only [Function.comp_apply, bind, id_eq, bind_pure_fun, List.map_nil, List.append_nil, match_id]

  pure_seq := by
    intro A B f t
    simp only [pure_eq, seq_eq, map_eq, bind, List.map_nil, List.append_nil, match_id]

  id_map := by
    simp only [map_eq, id_eq, pure_eq, bind_pure_fun, implies_true]

  map_const := rfl

end Rose
