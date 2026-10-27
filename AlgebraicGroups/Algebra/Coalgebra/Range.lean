/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.Equiv
public import AlgebraicGroups.Algebra.Coalgebra.Quotient
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Weak coalgebra data on the range of a linear map

For a linear map whose kernel is a coideal, the quotient by the kernel carries
Mathlib's canonical weak coalgebra data. Transport along the inverse of
`LinearMap.quotKerEquivRange` gives weak coalgebra data on the ordinary linear range.

Only the source has coalgebra data; the target is an ordinary module. The coideal
hypothesis includes vanishing of the source counit on the kernel. No coalgebra laws,
field hypothesis, flatness or finiteness assumptions are needed for this construction.
The projection formulas describe the transported data by conjugation with the stock
quotient-range equivalence.
-/

@[expose] public section

universe uR uC uD

namespace LinearMap

variable {R : Type uR} {C : Type uC} {D : Type uD}
variable [CommRing R] [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D]
variable [CoalgebraStruct R C]
variable (l : C →ₗ[R] D) [hker : (LinearMap.ker l).IsCoideal]

/-- Weak coalgebra data on the ordinary linear range, transported from the canonical
coalgebra data on the quotient by the coideal kernel. -/
@[instance_reducible]
noncomputable def rangeCoalgebraStruct : CoalgebraStruct R (LinearMap.range l) :=
  l.quotKerEquivRange.symm.coalgebraStruct R

/-- Range comultiplication is conjugated from quotient comultiplication by the
stock quotient-range equivalence and its tensor square. -/
theorem rangeCoalgebraStruct_comul :
    @CoalgebraStruct.comul R (LinearMap.range l) _ _ _ (rangeCoalgebraStruct l) =
      TensorProduct.map l.quotKerEquivRange.toLinearMap l.quotKerEquivRange.toLinearMap ∘ₗ
        Coalgebra.comul (R := R) (A := C ⧸ LinearMap.ker l) ∘ₗ
          l.quotKerEquivRange.symm.toLinearMap :=
  rfl

/-- The range counit is the quotient counit composed with the inverse of the stock
quotient-range equivalence. -/
theorem rangeCoalgebraStruct_counit :
    @CoalgebraStruct.counit R (LinearMap.range l) _ _ _ (rangeCoalgebraStruct l) =
      Coalgebra.counit (R := R) (A := C ⧸ LinearMap.ker l) ∘ₗ
        l.quotKerEquivRange.symm.toLinearMap :=
  rfl

/-- The selected range counit on a range representative is the source counit. -/
theorem rangeCoalgebraStruct_counit_apply_rangeRestrict (x : C) :
    @CoalgebraStruct.counit R (LinearMap.range l) _ _ _ (rangeCoalgebraStruct l)
        (l.rangeRestrict x) =
      Coalgebra.counit (R := R) x := by
  have hinv : l.quotKerEquivRange.symm (l.rangeRestrict x) = (LinearMap.ker l).mkQ x :=
    l.quotKerEquivRange_symm_apply_image x (LinearMap.mem_range_self l x)
  rw [rangeCoalgebraStruct_counit]
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, hinv] using
    congrArg (fun f : C →ₗ[R] R => f x)
      (Coalgebra.Quotient.counit_comp_mkQ (LinearMap.ker l))

/-- The selected range comultiplication on a range representative is the tensor
square of the ordinary range restriction applied to the source comultiplication. -/
theorem rangeCoalgebraStruct_comul_apply_rangeRestrict (x : C) :
    @CoalgebraStruct.comul R (LinearMap.range l) _ _ _ (rangeCoalgebraStruct l)
        (l.rangeRestrict x) =
      TensorProduct.map l.rangeRestrict l.rangeRestrict (Coalgebra.comul (R := R) x) := by
  have hcomp :
      l.quotKerEquivRange.toLinearMap ∘ₗ (LinearMap.ker l).mkQ = l.rangeRestrict := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    exact l.quotKerEquivRange_apply_mk y
  have hinv : l.quotKerEquivRange.symm (l.rangeRestrict x) = (LinearMap.ker l).mkQ x :=
    l.quotKerEquivRange_symm_apply_image x (LinearMap.mem_range_self l x)
  rw [rangeCoalgebraStruct_comul]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hinv]
  rw [Submodule.mkQ_apply, Coalgebra.Quotient.comul_mk, TensorProduct.map_map, hcomp]

end LinearMap
