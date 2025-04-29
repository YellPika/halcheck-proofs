import Mathlib

namespace Nat

/-- Case analyis helper function. -/
def cases {P : ℕ → Sort*} (x : P 0) (f : ∀n, P (n + 1)) : ∀n, P n := fun
  | 0 => x
  | (n + 1) => f n

@[simp]
lemma cases_zero : cases x f 0 = x := by simp only [cases]

@[simp]
lemma cases_succ : cases x f (n + 1) = f n := by simp only [cases]

@[simp]
lemma comp_cases {f : A → B} : f ∘ cases x g = cases (f x) (f ∘ g) := by
  ext i
  induction i with
  | zero => simp only [Function.comp_apply, cases_zero]
  | succ n _ => simp only [Function.comp_apply, cases_succ]

@[simp]
lemma cases_eta : cases 0 Nat.succ = id := by
  ext n
  cases n <;> rfl

@[simp]
lemma cases_eta' : cases 0 (fun n ↦ 1 + n) = id := by
  ext n
  cases n <;> simp only [cases, id_eq]
  apply add_comm

end Nat
