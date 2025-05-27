import Mathlib

namespace OmegaCompletePartialOrder.Chain

variable [Preorder A]

/-- The chain that always returns the same value. -/
def const (x : A) : Chain A := OrderHom.const ℕ x

@[simp]
lemma const_apply  (x : A) : const x n = x := rfl

end OmegaCompletePartialOrder.Chain
