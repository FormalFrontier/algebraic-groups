/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroupsTest.Algebra.Coalgebra.GroupLikeCoordinatesModels
public import AlgebraicGroups.Algebra.Coalgebra.GroupLikeCoordinates
public import AlgebraicGroups.Algebra.Coalgebra.Subcoalgebra.Finite
public import AlgebraicGroups.Algebra.Coalgebra.Subcoalgebra.Finsupp

/-!
# Coalgebra evaluation and span coordinates on an infinite diagonal example

The coordinate points and weighted vector of `GroupLikeCoordinatesModels` give
concrete uses of coalgebra evaluation and its universal correspondence. The target
is the infinite-dimensional coalgebra `ℤ →₀ ℚ`; no multiplication on the target
is used. The weighted vector also belongs to the canonical group-like span, where
the coalgebra equivalence recovers its two distinct coordinates. Applying the
ambient coordinate formulas gives the diagonal comultiplication and counit five.
An empty indexing type supplies the zero-source boundary of evaluation.
The singleton-supported subcoalgebras also give two finite stages of the directed
exhaustion: a common finite stage contains every weighted pair from these whole
stages and hence contains the stored vector with its counit five.

## References

The points, vector and their nondegeneracy come from
`AlgebraicGroupsTest.Algebra.Coalgebra.GroupLikeCoordinatesModels`. The coalgebra
maps and span equivalence come from
`AlgebraicGroups.Algebra.Coalgebra.GroupLikeCoordinates` and its imports.
Coefficient calculations use Mathlib's `MonoidAlgebra.coeff` API and
`Finsupp.sum_add_index'`, `Finsupp.sum_single_index` and `Finsupp.smul_single_one`.
-/

@[expose] public noncomputable section

open scoped MonoidAlgebra TensorProduct

namespace Coalgebra.FinsuppCoordinates

local notation "C∞" => ℤ →₀ ℚ
local notation "S∞" => Subcoalgebra.groupLikeSpan ℚ C∞
local notation "δ₀" => GroupLike.val (point 0)
local notation "δ₁" => GroupLike.val (point 1)

/-- Coalgebra-only evaluation sends the weighted free generators to the existing vector. -/
theorem lift_point_weighted :
    MonoidAlgebra.liftGroupLikeCoalgHom point
      ((2 : ℚ) • (MonoidAlgebra.single (0 : ℤ) 1 : ℚ[ℤ]) +
        (3 : ℚ) • MonoidAlgebra.single 1 1) = vector := by
  simp only [map_add, map_smul, MonoidAlgebra.liftGroupLikeCoalgHom_single,
    one_smul, vector]

/-- The forward universal correspondence evaluates the same nonmonomial input to the vector. -/
theorem lift_point_equiv_weighted :
    MonoidAlgebra.liftGroupLikeCoalgHomEquiv point
      ((2 : ℚ) • (MonoidAlgebra.single (0 : ℤ) 1 : ℚ[ℤ]) +
        (3 : ℚ) • MonoidAlgebra.single 1 1) = vector := by
  rw [MonoidAlgebra.liftGroupLikeCoalgHomEquiv_apply]
  exact lift_point_weighted

/-- The inverse universal correspondence recovers the coordinate-point family from its map. -/
theorem point_family_recovered :
    (MonoidAlgebra.liftGroupLikeCoalgHomEquiv (R := ℚ) (C := C∞) (G := ℤ)).symm
      (MonoidAlgebra.liftGroupLikeCoalgHom point) = point := by
  funext i
  apply GroupLike.val_injective
  simp only [MonoidAlgebra.liftGroupLikeCoalgHomEquiv_symm_apply_val,
    MonoidAlgebra.liftGroupLikeCoalgHom_single, one_smul]

/-- The two-coordinate vector as a member of the canonical group-like subcoalgebra. -/
def spanVector : S∞ :=
  ⟨vector, by
    apply Subcoalgebra.mem_toSubmodule.mp
    simpa only [vector] using
      (S∞).toSubmodule.add_mem
        ((S∞).toSubmodule.smul_mem (2 : ℚ)
          (Subcoalgebra.groupLike_mem_groupLikeSpan (point 0)))
        ((S∞).toSubmodule.smul_mem (3 : ℚ)
          (Subcoalgebra.groupLike_mem_groupLikeSpan (point 1)))⟩

/-- Inclusion of the span vector recovers the original ambient vector. -/
@[simp] theorem spanVector_coe : (spanVector : C∞) = vector := rfl

/-- The inverse coalgebra coordinates retain both weights on the two coordinate points. -/
theorem spanVector_coordinates :
    (GroupLike.spanCoalgebraEquiv (K := ℚ) (C := C∞)).symm spanVector =
      (2 : ℚ) • (MonoidAlgebra.single (point 0) 1 : ℚ[GroupLike ℚ C∞]) +
        (3 : ℚ) • MonoidAlgebra.single (point 1) 1 := by
  apply EquivLike.injective (GroupLike.spanCoalgebraEquiv (K := ℚ) (C := C∞))
  rw [CoalgEquiv.apply_symm_apply]
  apply Subcoalgebra.coe_injective
  simp only [map_add, map_smul, GroupLike.spanCoalgebraEquiv_single, one_smul,
    Subcoalgebra.coe_add, Subcoalgebra.coe_smul, spanVector_coe, vector]

/-- The characteristic ambient evaluation of these span coordinates reconstructs the vector. -/
theorem spanVector_reconstruction :
    (GroupLike.spanCoalgebraEquiv
      ((2 : ℚ) • (MonoidAlgebra.single (point 0) 1 : ℚ[GroupLike ℚ C∞]) +
        (3 : ℚ) • MonoidAlgebra.single (point 1) 1) : C∞) = vector := by
  rw [GroupLike.spanCoalgebraEquiv_apply_coe]
  simp only [map_add, map_smul, MonoidAlgebra.liftGroupLikeCoalgHom_single,
    id_eq, one_smul, vector]

/-- In canonical Finsupp form the inverse coefficients are the two weighted singletons. -/
theorem spanVector_coefficients :
    ((GroupLike.spanCoalgebraEquiv (K := ℚ) (C := C∞)).symm spanVector).coeff =
      Finsupp.single (point 0) 2 + Finsupp.single (point 1) 3 := by
  rw [spanVector_coordinates]
  simp only [MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_smul,
    MonoidAlgebra.coeff_single, Finsupp.smul_single_one]

/-- Distinctness of the coordinate points makes the two inverse coefficients two and three. -/
theorem spanVector_coefficients_at_points :
    ((GroupLike.spanCoalgebraEquiv (K := ℚ) (C := C∞)).symm spanVector).coeff
        (point 0) = 2 ∧
      ((GroupLike.spanCoalgebraEquiv (K := ℚ) (C := C∞)).symm spanVector).coeff
        (point 1) = 3 := by
  classical
  have h01 : point 0 ≠ point 1 := by
    intro h
    exact point_zero_val_ne_point_one_val (congrArg GroupLike.val h)
  simp [spanVector_coefficients, h01, Ne.symm h01]

/-- The ambient span-coordinate formula gives the two diagonal comultiplication terms. -/
theorem spanVector_comul :
    comul (R := ℚ) vector =
      (2 : ℚ) • (δ₀ ⊗ₜ[ℚ] δ₀) + (3 : ℚ) • (δ₁ ⊗ₜ[ℚ] δ₁) := by
  calc
    comul (R := ℚ) vector =
        ((GroupLike.spanCoalgebraEquiv (K := ℚ) (C := C∞)).symm spanVector).coeff.sum
          (fun g r => r • (g.val ⊗ₜ[ℚ] g.val)) := by
      simpa only [spanVector_coe] using GroupLike.comul_eq_sum_spanCoefficients spanVector
    _ = _ := by
      rw [spanVector_coefficients]
      rw [Finsupp.sum_add_index']
      · simp only [Finsupp.sum_single_index, zero_smul]
      · intro g
        exact zero_smul ℚ _
      · intro g r s
        exact add_smul r s _

/-- The ambient span-coordinate counit formula adds the inverse coefficients to give five. -/
theorem spanVector_counit : counit (R := ℚ) vector = 5 := by
  calc
    counit (R := ℚ) vector =
        ((GroupLike.spanCoalgebraEquiv (K := ℚ) (C := C∞)).symm spanVector).coeff.sum
          (fun _ r => r) := by
      simpa only [spanVector_coe] using GroupLike.counit_eq_sum_spanCoefficients spanVector
    _ = 5 := by
      rw [spanVector_coefficients]
      norm_num [Finsupp.sum_add_index', Finsupp.sum_single_index]

/-- The two singleton-supported stages lie in one finite-dimensional subcoalgebra.
It contains every weighted pair from the whole stages, including the stored vector
with counit five. -/
theorem exists_finite_subcoalgebra_weighted :
    ∃ E : Subcoalgebra ℚ C∞, Module.Finite ℚ E ∧
      (Finsupp.supportedSubcoalgebra ℚ ({0} : Set ℤ)).toSubmodule ≤ E.toSubmodule ∧
      (Finsupp.supportedSubcoalgebra ℚ ({1} : Set ℤ)).toSubmodule ≤ E.toSubmodule ∧
      (∀ (a : Finsupp.supportedSubcoalgebra ℚ ({0} : Set ℤ))
        (b : Finsupp.supportedSubcoalgebra ℚ ({1} : Set ℤ)),
        (2 : ℚ) • (a : C∞) + (3 : ℚ) • (b : C∞) ∈ E) ∧
      ∃ w : E, (w : C∞) = vector ∧ counit (R := ℚ) (w : C∞) = 5 := by
  let A : {D : Subcoalgebra ℚ C∞ // Module.Finite ℚ D} :=
    ⟨Finsupp.supportedSubcoalgebra ℚ ({0} : Set ℤ),
      Finsupp.supportedSubcoalgebra_finite ℚ _ (Set.finite_singleton 0)⟩
  let B : {D : Subcoalgebra ℚ C∞ // Module.Finite ℚ D} :=
    ⟨Finsupp.supportedSubcoalgebra ℚ ({1} : Set ℤ),
      Finsupp.supportedSubcoalgebra_finite ℚ _ (Set.finite_singleton 1)⟩
  obtain ⟨E, hA, hB⟩ := Subcoalgebra.directed_finite_toSubmodule A B
  have htransport (a : A.val) (b : B.val) :
      (2 : ℚ) • (a : C∞) + (3 : ℚ) • (b : C∞) ∈ E.val := by
    apply Subcoalgebra.mem_toSubmodule.mp
    exact E.val.toSubmodule.add_mem
      (E.val.toSubmodule.smul_mem (2 : ℚ) (hA a.property))
      (E.val.toSubmodule.smul_mem (3 : ℚ) (hB b.property))
  have h0 : δ₀ ∈ A.val :=
    Finsupp.single_mem_supportedSubcoalgebra ℚ ({0} : Set ℤ) 1 (Set.mem_singleton 0)
  have h1 : δ₁ ∈ B.val :=
    Finsupp.single_mem_supportedSubcoalgebra ℚ ({1} : Set ℤ) 1 (Set.mem_singleton 1)
  have hv : vector ∈ E.val := htransport ⟨δ₀, h0⟩ ⟨δ₁, h1⟩
  exact ⟨E.val, E.property, hA, hB, htransport, ⟨vector, hv⟩, rfl, vector_counit⟩

/-- Empty-index evaluation into the same target sends every source element to zero. -/
theorem lift_empty_eq_zero (x : ℚ[Empty]) :
    MonoidAlgebra.liftGroupLikeCoalgHom (Empty.elim : Empty → GroupLike ℚ C∞) x = 0 :=
  MonoidAlgebra.liftGroupLikeCoalgHom_apply_of_isEmpty _ x

end Coalgebra.FinsuppCoordinates
