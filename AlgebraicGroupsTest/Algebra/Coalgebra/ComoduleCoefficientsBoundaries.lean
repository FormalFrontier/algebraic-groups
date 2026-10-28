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

Over `ℚ`, contraction of the scalar coact by a functional `ℓ` gives `ℓ m`.
Both the one-dimensional comodule and the countable direct sum `ℕ →₀ ℚ` have
coefficient span equal to the scalar coalgebra. The latter module is not
module-finite: the construction of the all-dual coefficient span does not need
a finite-dimensional ambient comodule. The scalar coact is injective, so it
is nonzero on every nonzero vector, not merely on the displayed coordinate vector.

The module `Fin 0 → ℚ` gives two zero boundaries. It is a scalar comodule over
`ℚ`, and it is the regular comodule over its own canonical finite-product
coalgebra. Both coefficient spans are zero. The second example uses a coalgebra
on a zero module, without requiring a bialgebra over `ℚ`.

Over `ℤ`, the scalar coact on `ZMod 2` is nonzero, but every integral-valued
linear functional vanishes. Its coefficient span is therefore zero, and the
coact cannot factor through the tensor inclusion of this span. This is a
counterexample to unrestricted coefficient-span factorization over rings, not
a field example.

## Limitations

The coefficient-span and zero examples concern dual contraction and its submodule
span. The scalar round trip also uses the coefficient subcoalgebra and the general
coact-range criterion: restricting to this subcoalgebra and changing back along
its inclusion recovers the original scalar comodule. These examples do not supply a
proper matrix-coefficient model in an infinite-dimensional coalgebra.

## References

Mathlib supplies the scalar and finite-product coalgebras, tensor unitors,
Finsupp coordinate evaluation, the finiteness criterion for Finsupp modules,
and the characteristic-two identity for `ZMod 2`. The scalar and regular right
comodules are the constructors in `AlgebraicGroups.Algebra.TauCeti.Comodule`.
-/

@[expose] public section

open TauCeti


universe u

open scoped TensorProduct

open TauCeti (Comodule)

namespace ComoduleCoefficientExamples

/-- Dual contraction of the rational scalar coact is evaluation of the functional. -/
theorem rational_scalar_coefficient {M : Type u} [AddCommMonoid M] [Module ℚ M]
    (ell : M →ₗ[ℚ] ℚ) (m : M) :
    (@Comodule.matrixCoefficient ℚ ℚ M _ _ _ _ _ _ (Comodule.trivial (R := ℚ) (C := ℚ) (M :=
        M))) ell m = ell m := by
  simp

/-- The scalar right comodule on a one-dimensional rational vector space. -/
@[instance_reducible] noncomputable def finiteScalarComodule : Comodule ℚ ℚ ℚ :=
  Comodule.trivial (R := ℚ) (C := ℚ) (M := ℚ)

@[simp] theorem finiteScalarComodule_coact (q : ℚ) :
    finiteScalarComodule.coact q = q ⊗ₜ[ℚ] (1 : ℚ) := rfl

/-- Changing the coefficient corestriction along its inclusion recovers the scalar comodule. -/
private theorem finiteScalar_restrict_mapCoalgebra :
    ∃ h : ∀ q : ℚ, finiteScalarComodule.coact q ∈
        LinearMap.range
          (finiteScalarComodule.coefficientSubcoalgebra.subtype.toLinearMap.lTensor ℚ),
      (letI := finiteScalarComodule.restrictCoalgebra
        finiteScalarComodule.coefficientSubcoalgebra h
       Comodule.Corestrict (M := ℚ) finiteScalarComodule.coefficientSubcoalgebra.subtype) =
           finiteScalarComodule := by
  have h := (finiteScalarComodule.coact_mem_range_iff_coefficientSpan_le
      finiteScalarComodule.coefficientSubcoalgebra).mpr (by
    simpa only [Comodule.coefficientSubcoalgebra_toSubmodule] using
      (le_rfl : (@Comodule.matrixCoefficientSubmodule ℚ ℚ ℚ _ _ _ _ _ _ finiteScalarComodule) ≤
          (@Comodule.matrixCoefficientSubmodule ℚ ℚ ℚ _ _ _ _ _ _ finiteScalarComodule)))
  exact ⟨h, finiteScalarComodule.mapCoalgebra_restrictCoalgebra
    finiteScalarComodule.coefficientSubcoalgebra h⟩

/-- The one-dimensional scalar comodule is module-finite. -/
theorem finiteScalar_moduleFinite : Module.Finite ℚ ℚ := inferInstance

/-- The identity functional and unit vector extract the unit coefficient. -/
theorem finiteScalar_unit_coefficient :
    (@Comodule.matrixCoefficient ℚ ℚ ℚ _ _ _ _ _ _ finiteScalarComodule) (LinearMap.id : ℚ →ₗ[ℚ]
        ℚ) 1 = 1 := by
  simp

/-- Every rational scalar is a coefficient of the one-dimensional scalar comodule. -/
theorem finiteScalar_coefficientSpan_eq_top : (@Comodule.matrixCoefficientSubmodule ℚ ℚ ℚ _ _ _
    _ _ _ finiteScalarComodule) = ⊤ := by
  apply top_unique
  intro q _
  simpa [finiteScalarComodule] using
    (@Comodule.matrixCoefficient_mem_submodule ℚ ℚ ℚ _ _ _ _ _ _ finiteScalarComodule)
      (LinearMap.id : ℚ →ₗ[ℚ] ℚ) q

/-- The finite scalar model has a nonzero finitely generated coefficient span. -/
theorem finiteScalar_coefficientSpan_nonzero_fg :
    (@Comodule.matrixCoefficientSubmodule ℚ ℚ ℚ _ _ _ _ _ _ finiteScalarComodule) ≠ ⊥ ∧
        (@Comodule.matrixCoefficientSubmodule ℚ ℚ ℚ _ _ _ _ _ _ finiteScalarComodule).FG := by
  rw [finiteScalar_coefficientSpan_eq_top]
  exact ⟨top_ne_bot, Module.Finite.fg_top⟩

/-- The countable direct sum of copies of the rational scalar module. -/
abbrev RationalSequence := ℕ →₀ ℚ

/-- The scalar right coact on the countable rational direct sum. -/
@[instance_reducible] noncomputable def countableScalarComodule : Comodule ℚ ℚ RationalSequence :=
  Comodule.trivial (R := ℚ) (C := ℚ) (M := RationalSequence)

@[simp] theorem countableScalarComodule_coact (m : RationalSequence) :
    countableScalarComodule.coact m = m ⊗ₜ[ℚ] (1 : ℚ) := rfl

/-- The scalar coact vanishes exactly on the zero vector, for every vector of the direct sum. -/
theorem countableScalar_coact_eq_zero_iff (m : RationalSequence) :
    countableScalarComodule.coact m = 0 ↔ m = 0 := by
  constructor
  · intro h
    have hr := congrArg (TensorProduct.rid ℚ RationalSequence) h
    simpa [countableScalarComodule] using hr
  · intro h
    simp [h]

/-- Evaluation at the zeroth coordinate extracts the unit from the zeroth coordinate vector. -/
theorem countableScalar_unit_coefficient :
    (@Comodule.matrixCoefficient ℚ ℚ RationalSequence _ _ _ _ _ _ countableScalarComodule)
      (Finsupp.lapply 0 : RationalSequence →ₗ[ℚ] ℚ) (Finsupp.single 0 1) = 1 := by
  simp

/-- The displayed coordinate vector has nonzero scalar coact. -/
theorem countableScalar_coordinate_coact_ne_zero :
    countableScalarComodule.coact (Finsupp.single 0 1) ≠ 0 := by
  intro h
  have hm := (countableScalar_coact_eq_zero_iff (Finsupp.single 0 1)).mp h
  have hzero := congrArg (fun m : RationalSequence ↦ m 0) hm
  simp at hzero

/-- The all-dual coefficient span is the whole scalar coalgebra even for this infinite-dimensional
comodule. Each scalar is extracted by the same coordinate functional. -/
theorem countableScalar_coefficientSpan_eq_top :
    (@Comodule.matrixCoefficientSubmodule ℚ ℚ RationalSequence _ _ _ _ _ _
        countableScalarComodule) = ⊤ := by
  apply top_unique
  intro q _
  simpa [countableScalarComodule] using
    (@Comodule.matrixCoefficient_mem_submodule ℚ ℚ RationalSequence _ _ _ _ _ _
        countableScalarComodule)
      (Finsupp.lapply 0 : RationalSequence →ₗ[ℚ] ℚ) (Finsupp.single 0 q)

/-- In particular, the countable scalar model has nonzero coefficient span. -/
theorem countableScalar_coefficientSpan_ne_bot :
    (@Comodule.matrixCoefficientSubmodule ℚ ℚ RationalSequence _ _ _ _ _ _
        countableScalarComodule) ≠ ⊥ := by
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

/-- The zero rational module with its scalar coact over the nonzero scalar coalgebra. -/
@[instance_reducible] noncomputable def zeroModuleComodule : Comodule ℚ ℚ ZeroRationalModule :=
  Comodule.trivial (R := ℚ) (C := ℚ) (M := ZeroRationalModule)

/-- Every dual coefficient of the zero scalar comodule is zero. -/
theorem zeroModule_coefficient_eq_zero (ell : ZeroRationalModule →ₗ[ℚ] ℚ)
    (m : ZeroRationalModule) : (@Comodule.matrixCoefficient ℚ ℚ ZeroRationalModule _ _ _ _ _ _
        zeroModuleComodule) ell m = 0 := by
  have hm : m = 0 := Subsingleton.elim _ _
  change (@Comodule.matrixCoefficient ℚ ℚ ZeroRationalModule _ _ _ _ _ _ (Comodule.trivial (R :=
      ℚ) (C := ℚ) (M := ZeroRationalModule))) ell m = 0
  exact (rational_scalar_coefficient ell m).trans
    ((congrArg ell hm).trans ell.map_zero)

/-- The all-dual coefficient span of the zero module is the zero submodule of `ℚ`. -/
theorem zeroModule_coefficientSpan_eq_bot : (@Comodule.matrixCoefficientSubmodule ℚ ℚ
    ZeroRationalModule _ _ _ _ _ _ zeroModuleComodule) = ⊥ := by
  apply le_antisymm _ bot_le
  rw [@Comodule.matrixCoefficientSubmodule_le_iff ℚ ℚ ZeroRationalModule _ _ _ _ _ _
      zeroModuleComodule _]
  intro ell m
  exact (Submodule.mem_bot ℚ).mpr (zeroModule_coefficient_eq_zero ell m)

/-- The regular right comodule of the canonical coalgebra on the empty finite product. -/
@[instance_reducible] noncomputable def zeroCoalgebraComodule :
    Comodule ℚ ZeroRationalModule ZeroRationalModule :=
  Comodule.instSelf ℚ ZeroRationalModule

/-- The coact in the zero-coalgebra model is zero on every vector. -/
theorem zeroCoalgebra_coact_eq_zero (m : ZeroRationalModule) :
    zeroCoalgebraComodule.coact m = 0 := by
  have hm : m = 0 := Subsingleton.elim _ _
  exact (congrArg zeroCoalgebraComodule.coact hm).trans
    zeroCoalgebraComodule.coact.map_zero

/-- The zero-coalgebra model also has zero coefficient span, in its zero ambient coalgebra. -/
theorem zeroCoalgebra_coefficientSpan_eq_bot :
    (@Comodule.matrixCoefficientSubmodule ℚ ZeroRationalModule ZeroRationalModule _ _ _ _ _ _
        zeroCoalgebraComodule) = ⊥ := by
  apply le_antisymm _ bot_le
  rw [@Comodule.matrixCoefficientSubmodule_le_iff ℚ ZeroRationalModule ZeroRationalModule _ _ _
      _ _ _ zeroCoalgebraComodule _]
  intro ell m
  exact (Submodule.mem_bot ℚ).mpr (Subsingleton.elim _ _)

/-- The scalar right comodule on the integral module `ℤ/2ℤ`. -/
@[instance_reducible] noncomputable def integralTorsionComodule : Comodule ℤ ℤ (ZMod 2) :=
  Comodule.trivial (R := ℤ) (C := ℤ) (M := (ZMod 2))

@[simp] theorem integralTorsionComodule_coact (m : ZMod 2) :
    integralTorsionComodule.coact m = m ⊗ₜ[ℤ] (1 : ℤ) := rfl

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
    (@Comodule.matrixCoefficient ℤ ℤ (ZMod 2) _ _ _ _ _ _ integralTorsionComodule) ell m = 0 := by
  rw [integral_dual_eq_zero ell]
  simp

/-- Despite the nonzero coact, the integral all-dual coefficient span is zero. -/
theorem integralTorsion_coefficientSpan_eq_bot : (@Comodule.matrixCoefficientSubmodule ℤ ℤ (ZMod
    2) _ _ _ _ _ _ integralTorsionComodule) = ⊥ := by
  apply le_antisymm _ bot_le
  rw [@Comodule.matrixCoefficientSubmodule_le_iff ℤ ℤ (ZMod 2) _ _ _ _ _ _
      integralTorsionComodule _]
  intro ell m
  exact (Submodule.mem_bot ℤ).mpr (integralTorsion_coefficient_eq_zero ell m)

/-- The scalar coact of the unit residue class is nonzero, as seen by the right unitor. -/
theorem integralTorsion_coact_one_ne_zero :
    integralTorsionComodule.coact (1 : ZMod 2) ≠ 0 := by
  intro h
  have hr := congrArg (TensorProduct.rid ℤ (ZMod 2)) h
  simp at hr

/-- No linear coact lift through the tensor inclusion of the integral coefficient span exists.
Thus arbitrary-ring factorization is false even for a scalar coalgebra. -/
theorem integralTorsion_no_coefficientSpan_factorization :
    ¬ ∃ rho : ZMod 2 →ₗ[ℤ] (ZMod 2) ⊗[ℤ] (@Comodule.matrixCoefficientSubmodule ℤ ℤ (ZMod 2) _ _
        _ _ _ _ integralTorsionComodule),
      (@Comodule.matrixCoefficientSubmodule ℤ ℤ (ZMod 2) _ _ _ _ _ _
          integralTorsionComodule).subtype.lTensor (ZMod 2) ∘ₗ rho =
        integralTorsionComodule.coact := by
  rintro ⟨rho, h⟩
  let : Subsingleton (@Comodule.matrixCoefficientSubmodule ℤ ℤ (ZMod 2) _ _ _ _ _ _
      integralTorsionComodule) :=
    Submodule.subsingleton_iff_eq_bot.mpr integralTorsion_coefficientSpan_eq_bot
  have hrho : rho (1 : ZMod 2) = 0 := Subsingleton.elim _ _
  apply integralTorsion_coact_one_ne_zero
  calc
    integralTorsionComodule.coact (1 : ZMod 2) =
        (@Comodule.matrixCoefficientSubmodule ℤ ℤ (ZMod 2) _ _ _ _ _ _
            integralTorsionComodule).subtype.lTensor (ZMod 2)
          (rho (1 : ZMod 2)) :=
      (LinearMap.congr_fun h (1 : ZMod 2)).symm
    _ = (@Comodule.matrixCoefficientSubmodule ℤ ℤ (ZMod 2) _ _ _ _ _ _
        integralTorsionComodule).subtype.lTensor (ZMod 2) 0 :=
      congrArg ((@Comodule.matrixCoefficientSubmodule ℤ ℤ (ZMod 2) _ _ _ _ _ _
          integralTorsionComodule).subtype.lTensor (ZMod 2)) hrho
    _ = 0 := map_zero _

end ComoduleCoefficientExamples
