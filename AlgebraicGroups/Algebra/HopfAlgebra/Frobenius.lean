/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.HopfAlgebra.DualCoinvariants
public import CoherentModules.LinearAlgebra.Dual.TensorProduct
public import ProjectiveModules.Module.Injective.Frobenius

/-!
# Frobenius functionals and self-injectivity of finite-dimensional Hopf algebras

A finite-dimensional Hopf algebra over a field admits a linear functional `λ`
for which the multiplication pairing `(a, x) ↦ λ (a * x)` separates both
arguments. Neither commutativity nor cocommutativity is required, and the
field may have any characteristic.

Such an algebra is also injective as a left module over itself. The theorem
`HopfAlgebra.injective_self` combines the functional with
`Module.injective_of_nondegenerate_mul`, using the original regular action.

The dual Hopf-module decomposition
`HopfAlgebra.antipodeDualCoinvariantsTensorEquiv` supplies the equivalence
from coinvariants tensored with the Hopf algebra to its original pointwise
linear dual. Its pure-tensor evaluation formula is precisely the hypothesis
of `Module.Dual.exists_nondegenerate_mul_of_tensorProduct_equiv`.
Applying this finite-dimensional criterion constructs the functional and
both separating implications. Projectivity over the field is supplied by
the usual vector-space instances, not an additional hypothesis.

The dimension argument behind the dual Hopf-module method takes dimensions
in this decomposition and cancels the positive natural number `dim H`,
giving a one-dimensional coinvariant space. Tensoring an equivalence from
the field to that space then gives the multiplication-pairing equivalence.
Thus the method does not divide by `dim H` in the field or require symmetry
of the multiplication pairing.

## References

* R. G. Larson and M. E. Sweedler, *An associative orthogonal bilinear form for
  Hopf algebras*, American Journal of Mathematics 91 (1969), 75–94, for the
  finite-dimensional dual Hopf-module method.
* M. E. Sweedler, *Hopf Algebras*, Benjamin, 1969, for the fundamental theorem
  of Hopf modules.
* T. Y. Lam, *Lectures on Modules and Rings*, Graduate Texts in Mathematics 189,
  Springer, 1999, for the Frobenius self-injectivity criterion.

The construction reuses the dual tensor-product criterion in CoherentModules
and the canonical dual Hopf-module decomposition in this library. The
self-injectivity corollary reuses `Module.injective_of_nondegenerate_mul`
from ProjectiveModules.
-/

@[expose] public section

universe u v

namespace HopfAlgebra

variable (K : Type u) (H : Type v)
variable [Field K] [Ring H] [HopfAlgebra K H] [Module.Finite K H]

/-- A finite-dimensional Hopf algebra has a Frobenius functional: its
multiplication pairing is nondegenerate in both arguments. This is the
Larson–Sweedler dual Hopf-module argument; no commutativity, restriction on the
characteristic, or bijectivity assumption on the antipode is needed. -/
theorem exists_nondegenerate_mul :
    ∃ φ : H →ₗ[K] K, ((LinearMap.mul K H).compr₂ φ).Nondegenerate := by
  exact Module.Dual.exists_nondegenerate_mul_of_tensorProduct_equiv
    ((antipodeDualRightComodule K H).weightSpace (1 : H))
    (antipodeDualCoinvariantsTensorEquiv K H)
    (antipodeDualCoinvariantsTensorEquiv_tmul_apply K H)

end HopfAlgebra

/-- The left regular module of a finite-dimensional Hopf algebra over a field
is injective. This is the Frobenius self-injectivity consequence from
T. Y. Lam, *Lectures on Modules and Rings* (1999), applied to
`HopfAlgebra.exists_nondegenerate_mul`. -/
theorem HopfAlgebra.injective_self (K : Type u) (H : Type v)
    [Field K] [Ring H] [HopfAlgebra K H] [Module.Finite K H] :
    Module.Injective H H := by
  obtain ⟨φ, hφ⟩ := HopfAlgebra.exists_nondegenerate_mul K H
  exact Module.injective_of_nondegenerate_mul φ hφ
