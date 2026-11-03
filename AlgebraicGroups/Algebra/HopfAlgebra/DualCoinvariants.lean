/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.HopfAlgebra.DualComodule
public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.HopfModule.DualEvaluation
public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.HopfModule.Decomposition
public import CoherentModules.LinearAlgebra.Dual.End

/-!
# Coinvariant decomposition of the antipode dual comodule

For a finite projective Hopf algebra, its antipode dual right comodule decomposes
as its coinvariants tensored with the Hopf algebra. The forward map sends
`c ⊗ h` to the functional `x ↦ c (h * x)`. Consequently, equality of two such
pure tensors is detected by equality of their right-translate functionals.

The dual retains its pointwise module structure over the base. The opposite
Hopf-algebra action and its scalar tower are constructed only in the proof of
the equivalence, from the right regular dual algebra homomorphism. Compatibility
with the chosen coaction follows from its tensor-evaluation identity. The
construction then uses the Hopf-module decomposition, including its inverse
with values in the tensor product of coinvariants.

## Main declarations

* `HopfAlgebra.antipodeDualCoinvariantsTensorEquiv` is the canonical decomposition.
* `HopfAlgebra.antipodeDualCoinvariantsTensorEquiv_tmul_apply` evaluates its forward map.
* `HopfAlgebra.antipodeDualCoinvariants_tmul_eq_iff` separates pure tensors by translation.

## References

* M. E. Sweedler, *Hopf Algebras*, Benjamin, 1969, for the fundamental theorem
  of Hopf modules.
* R. G. Larson and M. E. Sweedler, *An associative orthogonal bilinear form for
  Hopf algebras*, American Journal of Mathematics 91 (1969), 75–94, for the
  finite-dimensional dual Hopf-module method.

The construction reuses the formalizations `antipodeDualRightComodule`,
`Coalgebra.RightComodule.isHopfModule_of_dual_eval` and
`Coalgebra.RightComodule.coinvariantsTensorEquiv`. Here the base is any
commutative semiring and the Hopf algebra is finite projective over it; no
finite-dimensionality over a field is required.
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace HopfAlgebra

variable (R : Type u) (H : Type v)
variable [CommSemiring R] [Semiring H] [HopfAlgebra R H]
variable [Module.Finite R H] [Module.Projective R H]

/-- The antipode dual right comodule is linearly equivalent to its coinvariants
tensored with the Hopf algebra, by right translation of functionals. This is
the dual Hopf-module application of the fundamental theorem of Hopf modules
(Sweedler, *Hopf Algebras*), over a commutative semiring with finite projective
Hopf algebra. -/
noncomputable def antipodeDualCoinvariantsTensorEquiv :
    ((antipodeDualRightComodule R H).weightSpace (1 : H) ⊗[R] H) ≃ₗ[R] Module.Dual R H := by
  let ρ : Hᵐᵒᵖ →ₐ[R] Module.End R (Module.Dual R H) :=
    Module.Dual.rightRegularAlgHom R H
  letI : Module Hᵐᵒᵖ (Module.Dual R H) :=
    Module.compHom (Module.Dual R H) ρ.toRingHom
  letI : IsScalarTower R Hᵐᵒᵖ (Module.Dual R H) :=
    ⟨fun r a φ => by
      change ρ (r • a) φ = r • ρ a φ
      exact congrArg (fun f : Module.End R (Module.Dual R H) => f φ)
        (ρ.toLinearMap.map_smul r a)⟩
  have hact : ∀ (h : H) (φ : Module.Dual R H) (x : H),
      (MulOpposite.op h • φ) x = φ (h * x) := by
    intro h φ x
    change ρ (MulOpposite.op h) φ x = φ (h * x)
    exact Module.Dual.rightRegularAlgHom_apply R H h φ x
  have hρ : ∀ (φ : Module.Dual R H) (x : H),
      _root_.TensorProduct.map (Module.Dual.eval R H x) (LinearMap.id : H →ₗ[R] H)
          ((antipodeDualRightComodule R H).coaction φ) =
        _root_.TensorProduct.map φ (HopfAlgebra.antipode R) (Coalgebra.comul (R := R) x) := by
    intro φ x
    apply (_root_.TensorProduct.lid R H).injective
    simpa only [antipodeDualRightComodule_coaction] using antipodeDualTensor_eval R H φ x
  have hX := Coalgebra.RightComodule.isHopfModule_of_dual_eval
    (antipodeDualRightComodule R H) hact hρ
  exact (antipodeDualRightComodule R H).coinvariantsTensorEquiv hX

/-- On a pure tensor, the canonical dual decomposition is right translation of
the coinvariant functional. -/
@[simp] theorem antipodeDualCoinvariantsTensorEquiv_tmul_apply
    (c : (antipodeDualRightComodule R H).weightSpace (1 : H)) (h x : H) :
    antipodeDualCoinvariantsTensorEquiv R H (c ⊗ₜ[R] h) x =
      (c : Module.Dual R H) (h * x) := by
  simp only [antipodeDualCoinvariantsTensorEquiv,
    Coalgebra.RightComodule.coinvariantsTensorEquiv_apply,
    Coalgebra.RightComodule.coinvariantTensorToModule_tmul]
  change Module.Dual.rightRegularAlgHom R H (MulOpposite.op h)
    (c : Module.Dual R H) x = (c : Module.Dual R H) (h * x)
  exact Module.Dual.rightRegularAlgHom_apply R H h (c : Module.Dual R H) x

/-- Pure tensors of canonical dual coinvariants are equal exactly when their
right-translate functionals agree. This uses injectivity of the decomposition,
without an injectivity assertion about a tensored subtype inclusion. -/
theorem antipodeDualCoinvariants_tmul_eq_iff
    (c d : (antipodeDualRightComodule R H).weightSpace (1 : H)) (h k : H) :
    c ⊗ₜ[R] h = d ⊗ₜ[R] k ↔
      ∀ x : H, (c : Module.Dual R H) (h * x) = (d : Module.Dual R H) (k * x) := by
  constructor
  · intro hEq x
    have he := congrArg (fun z => antipodeDualCoinvariantsTensorEquiv R H z x) hEq
    simpa only [antipodeDualCoinvariantsTensorEquiv_tmul_apply] using he
  · intro hEq
    apply (antipodeDualCoinvariantsTensorEquiv R H).injective
    apply LinearMap.ext
    intro x
    simpa only [antipodeDualCoinvariantsTensorEquiv_tmul_apply] using hEq x

end HopfAlgebra
