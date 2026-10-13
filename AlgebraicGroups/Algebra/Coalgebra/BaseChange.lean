/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.CounitRange
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Coalgebra.TensorProduct

/-!
# The counit ideal under extension of scalars

For commutative semirings `R` and `S` with an `R`-algebra structure on `S`, the
canonical `S`-coalgebra on `S ⊗[R] C` has counit ideal equal to the extension of
the counit ideal of `C`. Neither flatness of `S` nor projectivity, freeness or
finite generation of `C` is required. The additive structure of `C` need only
be a commutative monoid, and the three types may lie in independent universes.

## References

Mathlib supplies the scalar-extension coalgebra and its counit formula, the
range of a tensored linear map, submodule scalar extension as a span, and
ideal extension. The proof combines these APIs rather than imposing an
injectivity condition on tensor products.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

open scoped TensorProduct

namespace Coalgebra

variable (R : Type u) (S : Type v) (C : Type w)
variable [CommSemiring R] [CommSemiring S] [Algebra R S]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]

/-- The counit ideal of the canonical scalar-extension coalgebra is the extension
of the original counit ideal. This holds without flatness or freeness assumptions. -/
theorem counit_range_baseChange :
    (LinearMap.range (counit (R := S) (A := S ⊗[R] C)) : Ideal S) =
      Ideal.map (algebraMap R S) (LinearMap.range (counit (R := R) (A := C))) := by
  have hε : counit (R := S) (A := S ⊗[R] C) =
      (TensorProduct.AlgebraTensorModule.rid R S S).toLinearMap ∘ₗ
        (counit (R := R) (A := C)).baseChange S := by
    ext s
    simp [Algebra.smul_def]
  have hrange : LinearMap.range ((counit (R := R) (A := C)).baseChange S) =
      (LinearMap.range (counit (R := R) (A := C))).baseChange S := by
    apply Submodule.restrictScalars_injective R
    rw [← LinearMap.range_restrictScalars]
    change LinearMap.range ((counit (R := R) (A := C)).lTensor S) =
      LinearMap.range ((LinearMap.range (counit (R := R) (A := C))).subtype.lTensor S)
    exact LinearMap.lTensor_range S
  rw [hε, LinearMap.range_comp, hrange, Submodule.baseChange_eq_span,
    Submodule.map_span, Submodule.map_coe, Set.image_image, Ideal.submodule_span_eq]
  congr 1
  ext s
  simp [TensorProduct.AlgebraTensorModule.rid_tmul, Algebra.smul_def]

end Coalgebra
