/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.Dual
public import AlgebraicGroups.Algebra.Coalgebra.ComoduleCoefficients

/-!
# Coefficients of dual right comodules

Evaluation-pair coefficients of the finite-projective dual are antipodes of the
original coefficients. Canonical double-dual evaluation accounts for every
functional on the dual, so its coefficient span is the linear image of the
original span under the antipode. Only the linear map of the antipode is used:
it is not asserted to be an ordinary coalgebra homomorphism.
-/

@[expose] public section

universe u v w

namespace Coalgebra.RightComodule

variable {R : Type u} {C : Type v} {V : Type w}
variable [CommSemiring R] [Semiring C] [HopfAlgebra R C]
variable [AddCommMonoid V] [Module R V]
variable [Module.Finite R V] [Module.Projective R V]

/-- Evaluating a coefficient of the dual at an original vector gives the
antipode of the original coefficient, with the vector and functional exchanged. -/
@[simp] theorem dual_coefficient_eval (X : RightComodule R C V)
    (v : V) (f : Module.Dual R V) :
    (dual X).coefficient (Module.Dual.eval R V v) f =
      HopfAlgebra.antipode R (A := C) (X.coefficient f v) := by
  change dualContraction (Module.Dual.eval R V v) (dualCoaction X f) = _
  rw [dualContraction_eval, dualCoaction_characteristic]
  rfl

/-- Every coefficient of the dual is the antipode of an original coefficient,
using the canonical finite-projective identification with the double dual. -/
theorem dual_coefficient (X : RightComodule R C V)
    (ell : Module.Dual R (Module.Dual R V)) (f : Module.Dual R V) :
    (dual X).coefficient ell f = HopfAlgebra.antipode R (A := C)
      (X.coefficient f ((Module.evalEquiv R V).symm ell)) := by
  conv_lhs => rw [← (Module.evalEquiv R V).apply_symm_apply ell]
  exact dual_coefficient_eval X _ f

/-- The coefficient span of the finite-projective dual is the image of the
original coefficient span under the antipode linear map. -/
theorem coefficientSpan_dual (X : RightComodule R C V) :
    (dual X).coefficientSpan =
      Submodule.map (HopfAlgebra.antipode R (A := C)) X.coefficientSpan := by
  apply le_antisymm
  · apply ((dual X).coefficientSpan_le_iff _).2
    intro ell f
    rw [dual_coefficient]
    exact Submodule.mem_map_of_mem (X.coefficient_mem_coefficientSpan f _)
  · apply (Submodule.map_le_iff_le_comap).2
    apply (X.coefficientSpan_le_iff _).2
    intro f v
    change HopfAlgebra.antipode R (A := C) (X.coefficient f v) ∈ (dual X).coefficientSpan
    rw [← dual_coefficient_eval]
    exact (dual X).coefficient_mem_coefficientSpan _ _

end Coalgebra.RightComodule
