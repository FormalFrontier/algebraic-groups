/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.ComoduleCoefficients
public import Mathlib.Data.Finsupp.Fintype
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Scalar and zero boundaries for right-comodule coefficients

Over `ℚ`, contraction of the scalar coaction by a functional `ℓ` gives `ℓ m`.
Both the one-dimensional comodule and the countable direct sum `ℕ →₀ ℚ` have
coefficient span equal to the scalar coalgebra. The latter module is not
module-finite: the construction of the all-dual coefficient span does not need
a finite-dimensional ambient comodule. The scalar coaction is injective, so it
is nonzero on every nonzero vector, not merely on the displayed coordinate vector.

The module `Fin 0 → ℚ` gives two zero boundaries. It is a scalar comodule over
`ℚ`, and it is the regular comodule over its own canonical finite-product
coalgebra. Both coefficient spans are zero. The second example uses a coalgebra
on a zero module, without requiring a bialgebra over `ℚ`.

Over `ℤ`, the scalar coaction on `ZMod 2` is nonzero, but every integral-valued
linear functional vanishes. Its coefficient span is therefore zero, and the
coaction cannot factor through the tensor inclusion of this span. This is a
counterexample to unrestricted coefficient-span factorization over rings, not
a field example.

## Limitations

The coefficient-span and zero examples concern dual contraction and its submodule
span. The scalar round trip also uses the coefficient subcoalgebra and the general
coaction-range criterion: restricting to this subcoalgebra and changing back along
its inclusion recovers the original scalar comodule. These examples do not supply a
proper matrix-coefficient model in an infinite-dimensional coalgebra.

## References

Mathlib supplies the scalar and finite-product coalgebras, tensor unitors,
Finsupp coordinate evaluation, the finiteness criterion for Finsupp modules,
and the characteristic-two identity for `ZMod 2`. The scalar and regular right
comodules are the constructors in `AlgebraicGroups.Algebra.Coalgebra.RightComodule`.
-/

@[expose] public section

universe u

open scoped TensorProduct

open Coalgebra (RightComodule)

namespace ComoduleCoefficientExamples

/-- Dual contraction of the rational scalar coaction is evaluation of the functional. -/
@[simp] theorem rational_scalar_coefficient {M : Type u} [AddCommMonoid M] [Module ℚ M]
    (ell : M →ₗ[ℚ] ℚ) (m : M) :
    (RightComodule.scalar ℚ M).coefficient ell m = ell m := by
  simp [RightComodule.coefficient]

/-- The scalar right comodule on a one-dimensional rational vector space. -/
noncomputable def finiteScalarComodule : RightComodule ℚ ℚ ℚ :=
  RightComodule.scalar ℚ ℚ

@[simp] theorem finiteScalarComodule_coaction (q : ℚ) :
    finiteScalarComodule.coaction q = q ⊗ₜ[ℚ] (1 : ℚ) := rfl

/-- Changing the coefficient corestriction along its inclusion recovers the scalar comodule. -/
private theorem finiteScalar_restrict_mapCoalgebra :
    ∃ h : ∀ q : ℚ, finiteScalarComodule.coaction q ∈
        LinearMap.range
          (finiteScalarComodule.coefficientSubcoalgebra.subtype.toLinearMap.lTensor ℚ),
      (finiteScalarComodule.restrictCoalgebra
        finiteScalarComodule.coefficientSubcoalgebra h).mapCoalgebra
          finiteScalarComodule.coefficientSubcoalgebra.subtype = finiteScalarComodule := by
  have h := (finiteScalarComodule.coaction_mem_range_iff_coefficientSpan_le
      finiteScalarComodule.coefficientSubcoalgebra).mpr (by
    simpa only [RightComodule.coefficientSubcoalgebra_toSubmodule] using
      (le_rfl : finiteScalarComodule.coefficientSpan ≤ finiteScalarComodule.coefficientSpan))
  exact ⟨h, finiteScalarComodule.mapCoalgebra_restrictCoalgebra
    finiteScalarComodule.coefficientSubcoalgebra h⟩

/-- The one-dimensional scalar comodule is module-finite. -/
theorem finiteScalar_moduleFinite : Module.Finite ℚ ℚ := inferInstance

/-- The identity functional and unit vector extract the unit coefficient. -/
theorem finiteScalar_unit_coefficient :
    finiteScalarComodule.coefficient (LinearMap.id : ℚ →ₗ[ℚ] ℚ) 1 = 1 := by
  simp [finiteScalarComodule]

/-- Every rational scalar is a coefficient of the one-dimensional scalar comodule. -/
theorem finiteScalar_coefficientSpan_eq_top : finiteScalarComodule.coefficientSpan = ⊤ := by
  apply top_unique
  intro q _
  simpa [finiteScalarComodule] using
    finiteScalarComodule.coefficient_mem_coefficientSpan
      (LinearMap.id : ℚ →ₗ[ℚ] ℚ) q

/-- The finite scalar model has a nonzero finitely generated coefficient span. -/
theorem finiteScalar_coefficientSpan_nonzero_fg :
    finiteScalarComodule.coefficientSpan ≠ ⊥ ∧ finiteScalarComodule.coefficientSpan.FG := by
  rw [finiteScalar_coefficientSpan_eq_top]
  exact ⟨top_ne_bot, Module.Finite.fg_top⟩

/-- The countable direct sum of copies of the rational scalar module. -/
abbrev RationalSequence := ℕ →₀ ℚ

/-- The scalar right coaction on the countable rational direct sum. -/
noncomputable def countableScalarComodule : RightComodule ℚ ℚ RationalSequence :=
  RightComodule.scalar ℚ RationalSequence

@[simp] theorem countableScalarComodule_coaction (m : RationalSequence) :
    countableScalarComodule.coaction m = m ⊗ₜ[ℚ] (1 : ℚ) := rfl

/-- The scalar coaction vanishes exactly on the zero vector, for every vector of the direct sum. -/
theorem countableScalar_coaction_eq_zero_iff (m : RationalSequence) :
    countableScalarComodule.coaction m = 0 ↔ m = 0 := by
  constructor
  · intro h
    have hr := congrArg (TensorProduct.rid ℚ RationalSequence) h
    simpa [countableScalarComodule] using hr
  · intro h
    simp [h]

/-- Evaluation at the zeroth coordinate extracts the unit from the zeroth coordinate vector. -/
theorem countableScalar_unit_coefficient :
    countableScalarComodule.coefficient
      (Finsupp.lapply 0 : RationalSequence →ₗ[ℚ] ℚ) (Finsupp.single 0 1) = 1 := by
  simp [countableScalarComodule]

/-- The displayed coordinate vector has nonzero scalar coaction. -/
theorem countableScalar_coordinate_coaction_ne_zero :
    countableScalarComodule.coaction (Finsupp.single 0 1) ≠ 0 := by
  intro h
  have hm := (countableScalar_coaction_eq_zero_iff (Finsupp.single 0 1)).mp h
  have hzero := congrArg (fun m : RationalSequence ↦ m 0) hm
  simp at hzero

/-- The all-dual coefficient span is the whole scalar coalgebra even for this infinite-dimensional
comodule. Each scalar is extracted by the same coordinate functional. -/
theorem countableScalar_coefficientSpan_eq_top :
    countableScalarComodule.coefficientSpan = ⊤ := by
  apply top_unique
  intro q _
  simpa [countableScalarComodule] using
    countableScalarComodule.coefficient_mem_coefficientSpan
      (Finsupp.lapply 0 : RationalSequence →ₗ[ℚ] ℚ) (Finsupp.single 0 q)

/-- In particular, the countable scalar model has nonzero coefficient span. -/
theorem countableScalar_coefficientSpan_ne_bot :
    countableScalarComodule.coefficientSpan ≠ ⊥ := by
  rw [countableScalar_coefficientSpan_eq_top]
  exact top_ne_bot

/-- The direct sum has infinite carrier. -/
theorem rationalSequence_infinite : Infinite RationalSequence := inferInstance

/-- The direct sum is not module-finite; this is stronger than infinitude of its carrier. -/
theorem rationalSequence_not_moduleFinite : ¬ Module.Finite ℚ RationalSequence := by
  intro h
  rcases (Module.finite_finsupp_self_iff (R := ℚ) (ι := ℕ)).mp h with hQ | hN
  · exact (zero_ne_one : (0 : ℚ) ≠ 1) (@Subsingleton.elim ℚ hQ 0 1)
  · exact hN.false

/-- The rational vector space with no coordinates. -/
abbrev ZeroRationalModule := Fin 0 → ℚ

/-- The zero rational module with its scalar coaction over the nonzero scalar coalgebra. -/
noncomputable def zeroModuleComodule : RightComodule ℚ ℚ ZeroRationalModule :=
  RightComodule.scalar ℚ ZeroRationalModule

/-- Every dual coefficient of the zero scalar comodule is zero. -/
theorem zeroModule_coefficient_eq_zero (ell : ZeroRationalModule →ₗ[ℚ] ℚ)
    (m : ZeroRationalModule) : zeroModuleComodule.coefficient ell m = 0 := by
  have hm : m = 0 := Subsingleton.elim _ _
  change (RightComodule.scalar ℚ ZeroRationalModule).coefficient ell m = 0
  exact (rational_scalar_coefficient ell m).trans
    ((congrArg ell hm).trans ell.map_zero)

/-- The all-dual coefficient span of the zero module is the zero submodule of `ℚ`. -/
theorem zeroModule_coefficientSpan_eq_bot : zeroModuleComodule.coefficientSpan = ⊥ := by
  apply le_antisymm _ bot_le
  rw [RightComodule.coefficientSpan_le_iff]
  intro ell m
  exact (Submodule.mem_bot ℚ).mpr (zeroModule_coefficient_eq_zero ell m)

/-- The regular right comodule of the canonical coalgebra on the empty finite product. -/
noncomputable def zeroCoalgebraComodule :
    RightComodule ℚ ZeroRationalModule ZeroRationalModule :=
  RightComodule.regular ℚ ZeroRationalModule

/-- The coaction in the zero-coalgebra model is zero on every vector. -/
theorem zeroCoalgebra_coaction_eq_zero (m : ZeroRationalModule) :
    zeroCoalgebraComodule.coaction m = 0 := by
  have hm : m = 0 := Subsingleton.elim _ _
  exact (congrArg zeroCoalgebraComodule.coaction hm).trans
    zeroCoalgebraComodule.coaction.map_zero

/-- The zero-coalgebra model also has zero coefficient span, in its zero ambient coalgebra. -/
theorem zeroCoalgebra_coefficientSpan_eq_bot :
    zeroCoalgebraComodule.coefficientSpan = ⊥ := by
  apply le_antisymm _ bot_le
  rw [RightComodule.coefficientSpan_le_iff]
  intro ell m
  exact (Submodule.mem_bot ℚ).mpr (Subsingleton.elim _ _)

/-- The scalar right comodule on the integral module `ℤ/2ℤ`. -/
noncomputable def integralTorsionComodule : RightComodule ℤ ℤ (ZMod 2) :=
  RightComodule.scalar ℤ (ZMod 2)

@[simp] theorem integralTorsionComodule_coaction (m : ZMod 2) :
    integralTorsionComodule.coaction m = m ⊗ₜ[ℤ] (1 : ℤ) := rfl

/-- Every integral-valued integral-linear functional on `ℤ/2ℤ` is zero. Doubling an image gives
zero in the torsion-free additive group of the integers. -/
theorem integral_dual_eq_zero (ell : ZMod 2 →ₗ[ℤ] ℤ) : ell = 0 := by
  ext m
  have hdouble : ell m + ell m = 0 := by
    rw [← map_add, ZModModule.add_self, map_zero]
  have hmul : (2 : ℤ) * ell m = 0 := by
    simpa only [two_mul] using hdouble
  exact (mul_eq_zero.mp hmul).resolve_left (by decide)

/-- Every integral scalar coefficient of this torsion comodule is zero. -/
theorem integralTorsion_coefficient_eq_zero (ell : ZMod 2 →ₗ[ℤ] ℤ) (m : ZMod 2) :
    integralTorsionComodule.coefficient ell m = 0 := by
  rw [integral_dual_eq_zero ell]
  simp [RightComodule.coefficient]

/-- Despite the nonzero coaction, the integral all-dual coefficient span is zero. -/
theorem integralTorsion_coefficientSpan_eq_bot : integralTorsionComodule.coefficientSpan = ⊥ := by
  apply le_antisymm _ bot_le
  rw [RightComodule.coefficientSpan_le_iff]
  intro ell m
  exact (Submodule.mem_bot ℤ).mpr (integralTorsion_coefficient_eq_zero ell m)

/-- The scalar coaction of the unit residue class is nonzero, as seen by the right unitor. -/
theorem integralTorsion_coaction_one_ne_zero :
    integralTorsionComodule.coaction (1 : ZMod 2) ≠ 0 := by
  intro h
  have hr := congrArg (TensorProduct.rid ℤ (ZMod 2)) h
  simp [integralTorsionComodule] at hr

/-- No linear coaction lift through the tensor inclusion of the integral coefficient span exists.
Thus arbitrary-ring factorization is false even for a scalar coalgebra. -/
theorem integralTorsion_no_coefficientSpan_factorization :
    ¬ ∃ rho : ZMod 2 →ₗ[ℤ] (ZMod 2) ⊗[ℤ] integralTorsionComodule.coefficientSpan,
      integralTorsionComodule.coefficientSpan.subtype.lTensor (ZMod 2) ∘ₗ rho =
        integralTorsionComodule.coaction := by
  rintro ⟨rho, h⟩
  let : Subsingleton integralTorsionComodule.coefficientSpan :=
    Submodule.subsingleton_iff_eq_bot.mpr integralTorsion_coefficientSpan_eq_bot
  have hrho : rho (1 : ZMod 2) = 0 := Subsingleton.elim _ _
  apply integralTorsion_coaction_one_ne_zero
  calc
    integralTorsionComodule.coaction (1 : ZMod 2) =
        integralTorsionComodule.coefficientSpan.subtype.lTensor (ZMod 2)
          (rho (1 : ZMod 2)) :=
      (LinearMap.congr_fun h (1 : ZMod 2)).symm
    _ = integralTorsionComodule.coefficientSpan.subtype.lTensor (ZMod 2) 0 :=
      congrArg (integralTorsionComodule.coefficientSpan.subtype.lTensor (ZMod 2)) hrho
    _ = 0 := map_zero _

end ComoduleCoefficientExamples
