/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.ComoduleCoefficients
public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.Transport
public import Mathlib.Algebra.Module.ULift
public import AlgebraicGroups.Algebra.GeneralLinearCoordinateRing
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.RingTheory.Coalgebra.GroupLike
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# Coefficients of the standard right representation of GL₂

The determinant-localized coordinate Hopf algebra of `GL₂` over `ℚ` coacts on
`Fin 2 → ℚ`. On the standard basis, the right column coaction sends `eⱼ` to
`∑ᵢ eᵢ ⊗ xᵢⱼ`. Its laws follow directly from the coordinate coproduct and
counit. Coordinate functionals extract each of the four matrix entries, and
arbitrary dual contractions lie in their span.

The resulting coefficient span is finitely generated, nonzero and proper.
Evaluation at the identity and twice the identity separates the unit from
that span. The off-diagonal coefficient `x₀₁` is not group-like: its counit is
zero, whereas evaluation at an upper unipotent matrix is one.

Transport to a universe-lifted carrier keeps the coalgebra fixed. The resulting
bijective comodule morphism compares coefficients, spans and coefficient
subcoalgebras on the two carriers. Its off-diagonal coefficient remains nonzero,
and its coefficient span remains finitely generated and proper.

No restricted coalgebra structure on the coefficient span is constructed here.

## References

* J. S. Milne, *Algebraic Groups* (2017), §2, item 2.8: the determinant
  localization and the ordered matrix-entry coproduct.
* `GeneralLinearCoordinateRing` supplies the coordinate Hopf algebra, its
  universal matrix, evaluation maps, coproduct and counit.
* Mathlib supplies the standard Pi basis and tensor-product linear maps.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace ComoduleCoefficientsGL2

/-- The determinant-localized coordinate ring of `GL₂` over `ℚ`. -/
abbrev C := GeneralLinearCoordinateRing.CoordinateRing ℚ (Fin 2)

/-- The carrier of the standard two-dimensional representation. -/
abbrev M := Fin 2 → ℚ

/-- The standard Pi basis vector. -/
def vector (i : Fin 2) : M := Pi.basisFun ℚ (Fin 2) i

/-- An entry of the universal invertible matrix. -/
def entry (i j : Fin 2) : C := GeneralLinearCoordinateRing.matrix ℚ (Fin 2) i j

@[simp] theorem vector_apply (i j : Fin 2) :
    vector i j = if j = i then 1 else 0 := by
  simp [vector, Pi.single_apply]

/-- Coordinate projection on the standard representation. -/
def coordinate (i : Fin 2) : M →ₗ[ℚ] ℚ := LinearMap.proj i

@[simp] theorem coordinate_vector (i j : Fin 2) :
    coordinate i (vector j) = if i = j then 1 else 0 := by
  simp [coordinate]

/-- The ordered matrix-entry coproduct in the coordinate Hopf algebra. -/
theorem entry_comul (i j : Fin 2) :
    Coalgebra.comul (R := ℚ) (entry i j) =
      ∑ k : Fin 2, entry i k ⊗ₜ[ℚ] entry k j :=
  GeneralLinearCoordinateRing.native_comul_matrix ℚ (Fin 2) i j

/-- The matrix-entry counit is evaluation at the identity matrix. -/
theorem entry_counit (i j : Fin 2) :
    Coalgebra.counit (R := ℚ) (entry i j) = (1 : Matrix (Fin 2) (Fin 2) ℚ) i j :=
  GeneralLinearCoordinateRing.native_counit_matrix ℚ (Fin 2) i j

/-- The linear column coaction, specified on the standard Pi basis. -/
def coactionLinearMap : M →ₗ[ℚ] M ⊗[ℚ] C :=
  (Pi.basisFun ℚ (Fin 2)).constr ℚ
    (fun j ↦ ∑ i : Fin 2, vector i ⊗ₜ[ℚ] entry i j)

@[simp] theorem coactionLinearMap_vector (j : Fin 2) :
    coactionLinearMap (vector j) = ∑ i : Fin 2, vector i ⊗ₜ[ℚ] entry i j := by
  exact (Pi.basisFun ℚ (Fin 2)).constr_basis ℚ _ j

/-- The column coaction on an arbitrary vector, in its standard coordinates. -/
theorem coactionLinearMap_apply (m : M) :
    coactionLinearMap m =
      ∑ j : Fin 2, m j • (∑ i : Fin 2, vector i ⊗ₜ[ℚ] entry i j) := by
  simp only [coactionLinearMap, Module.Basis.constr_apply_fintype,
    Pi.basisFun_equivFun, LinearEquiv.refl_apply]

private theorem column_coassoc :
    TensorProduct.assoc ℚ M C C ∘ₗ coactionLinearMap.rTensor C ∘ₗ coactionLinearMap =
      (Coalgebra.comul (R := ℚ) (A := C)).lTensor M ∘ₗ coactionLinearMap := by
  apply (Pi.basisFun ℚ (Fin 2)).ext
  intro j
  change TensorProduct.assoc ℚ M C C
      (coactionLinearMap.rTensor C (coactionLinearMap (vector j))) =
    (Coalgebra.comul (R := ℚ) (A := C)).lTensor M
      (coactionLinearMap (vector j))
  simp only [coactionLinearMap_vector, map_sum, LinearMap.rTensor_tmul,
    TensorProduct.sum_tmul, TensorProduct.assoc_tmul, LinearMap.lTensor_tmul,
    entry_comul, TensorProduct.tmul_sum]
  rw [Finset.sum_comm]

private theorem column_counit :
    (Coalgebra.counit (R := ℚ) (A := C)).lTensor M ∘ₗ coactionLinearMap =
      (TensorProduct.rid ℚ M).symm.toLinearMap := by
  apply (Pi.basisFun ℚ (Fin 2)).ext
  intro j
  change (Coalgebra.counit (R := ℚ) (A := C)).lTensor M
      (coactionLinearMap (vector j)) = vector j ⊗ₜ[ℚ] (1 : ℚ)
  fin_cases j <;> simp [coactionLinearMap_vector, entry_counit]

/-- The standard right column comodule over the coordinate Hopf algebra of `GL₂`. -/
def comodule : Coalgebra.RightComodule ℚ C M where
  coaction := coactionLinearMap
  coassoc := by exact column_coassoc
  counit_comp := by exact column_counit

@[simp] theorem comodule_coaction_vector (j : Fin 2) :
    comodule.coaction (vector j) = ∑ i : Fin 2, vector i ⊗ₜ[ℚ] entry i j :=
  coactionLinearMap_vector j

/-- The standard comodule's coaction on arbitrary linear combinations. -/
theorem comodule_coaction_apply (m : M) :
    comodule.coaction m =
      ∑ j : Fin 2, m j • (∑ i : Fin 2, vector i ⊗ₜ[ℚ] entry i j) :=
  coactionLinearMap_apply m

/-- Every dual contraction is a linear combination of the four matrix entries. -/
theorem coefficient_eq_sum (ell : M →ₗ[ℚ] ℚ) (m : M) :
    comodule.coefficient ell m =
      ∑ j : Fin 2, m j • (∑ i : Fin 2, ell (vector i) • entry i j) := by
  unfold Coalgebra.RightComodule.coefficient
  rw [comodule_coaction_apply]
  simp

/-- Contraction with a coordinate functional extracts the corresponding entry. -/
@[simp] theorem coefficient_coordinate_vector (i j : Fin 2) :
    comodule.coefficient (coordinate i) (vector j) = entry i j := by
  rw [coefficient_eq_sum]
  simp [ite_smul]

/-- The span of the four entries of the universal matrix. -/
def entrySpan : Submodule ℚ C :=
  Submodule.span ℚ (Set.range (Function.uncurry entry))

/-- The matrix-entry span is exactly the span of the displayed four entries. -/
theorem entrySpan_eq_span_four :
    entrySpan = Submodule.span ℚ {entry 0 0, entry 0 1, entry 1 0, entry 1 1} := by
  unfold entrySpan
  congr 1
  ext c
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨i, j⟩, rfl⟩
    fin_cases i <;> fin_cases j <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨(0, 0), rfl⟩
    · exact ⟨(0, 1), rfl⟩
    · exact ⟨(1, 0), rfl⟩
    · exact ⟨(1, 1), rfl⟩

/-- The intrinsic all-dual coefficient span is exactly the matrix-entry span. -/
theorem coefficientSpan_eq_entrySpan : comodule.coefficientSpan = entrySpan := by
  apply le_antisymm
  · apply (comodule.coefficientSpan_le_iff entrySpan).mpr
    intro ell m
    rw [coefficient_eq_sum]
    apply Submodule.sum_mem
    intro j _
    apply Submodule.smul_mem
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, j), rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨i, j⟩, rfl⟩
    simpa only [Function.uncurry_def, SetLike.mem_coe, coefficient_coordinate_vector] using
      comodule.coefficient_mem_coefficientSpan (coordinate i) (vector j)

/-- The intrinsic coefficient span is the span of precisely the four matrix entries. -/
theorem coefficientSpan_eq_span_four :
    comodule.coefficientSpan =
      Submodule.span ℚ {entry 0 0, entry 0 1, entry 1 0, entry 1 1} :=
  coefficientSpan_eq_entrySpan.trans entrySpan_eq_span_four

/-- The four-entry span is finitely generated. -/
theorem entrySpan_fg : entrySpan.FG :=
  Submodule.fg_span (Set.finite_range (Function.uncurry entry))

private def upperUnipotent : Matrix.GeneralLinearGroup (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : ℚ), 1; 0, 1]
    (by norm_num [Matrix.det_fin_two])

private theorem evaluate_upperUnipotent_entry01 :
    GeneralLinearCoordinateRing.evaluate (K := ℚ) upperUnipotent (entry 0 1) = 1 := by
  rw [entry, GeneralLinearCoordinateRing.evaluate_matrix]
  rfl

/-- The off-diagonal coefficient is nonzero, detected by a unipotent matrix. -/
theorem entry01_ne_zero : entry 0 1 ≠ 0 := by
  intro h
  have he := congrArg (GeneralLinearCoordinateRing.evaluate (K := ℚ) upperUnipotent) h
  rw [evaluate_upperUnipotent_entry01, map_zero] at he
  exact (one_ne_zero : (1 : ℚ) ≠ 0) he

/-- The off-diagonal coefficient has counit zero. -/
theorem entry01_counit : Coalgebra.counit (R := ℚ) (entry 0 1) = 0 := by
  rw [entry_counit]
  simp

/-- The nonzero off-diagonal coefficient is not a group-like element. -/
theorem entry01_not_groupLike : ¬ IsGroupLikeElem (R := ℚ) (entry 0 1) := by
  intro h
  have hc := h.counit_eq_one
  rw [entry01_counit] at hc
  norm_num at hc

private def twiceIdentity : Matrix.GeneralLinearGroup (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    ((2 : ℚ) • (1 : Matrix (Fin 2) (Fin 2) ℚ))
    (by norm_num [Matrix.det_fin_two, Matrix.smul_apply])

-- This linear functional vanishes on all entries, but not on the unit.
private def scalingDifference : C →ₗ[ℚ] ℚ :=
  (GeneralLinearCoordinateRing.evaluate (K := ℚ) twiceIdentity).toLinearMap -
    (2 : ℚ) • (GeneralLinearCoordinateRing.evaluate (K := ℚ)
      (1 : Matrix.GeneralLinearGroup (Fin 2) ℚ)).toLinearMap

private theorem scalingDifference_entry (i j : Fin 2) :
    scalingDifference (entry i j) = 0 := by
  change GeneralLinearCoordinateRing.evaluate (K := ℚ) twiceIdentity (entry i j) -
    2 * GeneralLinearCoordinateRing.evaluate (K := ℚ)
      (1 : Matrix.GeneralLinearGroup (Fin 2) ℚ) (entry i j) = 0
  simp only [entry, GeneralLinearCoordinateRing.evaluate_matrix]
  change ((2 : ℚ) • (1 : Matrix (Fin 2) (Fin 2) ℚ)) i j -
    2 * (1 : Matrix (Fin 2) (Fin 2) ℚ) i j = 0
  simp [Matrix.smul_apply, smul_eq_mul]

/-- The unit is outside the entry span, separated by evaluation at `I` and `2I`. -/
theorem one_not_mem_entrySpan : (1 : C) ∉ entrySpan := by
  have hker : entrySpan ≤ scalingDifference.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨i, j⟩, rfl⟩
    exact scalingDifference_entry i j
  intro h
  have hz : scalingDifference (1 : C) = 0 := hker h
  norm_num [scalingDifference] at hz

/-- The matrix-entry span is nonzero and proper inside the full coordinate ring. -/
theorem entrySpan_nonzero_proper : entrySpan ≠ ⊥ ∧ entrySpan ≠ ⊤ := by
  constructor
  · intro h
    have hm : entry 0 1 ∈ entrySpan := Submodule.subset_span ⟨(0, 1), rfl⟩
    rw [h] at hm
    exact entry01_ne_zero ((Submodule.mem_bot ℚ).mp hm)
  · intro h
    apply one_not_mem_entrySpan
    rw [h]
    exact Submodule.mem_top

/-- The standard representation has a proper nonzero finitely generated coefficient span. -/
theorem coefficientSpan_fg_nonzero_proper :
    comodule.coefficientSpan.FG ∧ comodule.coefficientSpan ≠ ⊥ ∧
      comodule.coefficientSpan ≠ ⊤ := by
  rw [coefficientSpan_eq_entrySpan]
  exact ⟨entrySpan_fg, entrySpan_nonzero_proper⟩

/-- A member of the intrinsic coefficient span is nonzero and not group-like. -/
theorem coefficientSpan_contains_non_groupLike :
    entry 0 1 ∈ comodule.coefficientSpan ∧ entry 0 1 ≠ 0 ∧
      ¬ IsGroupLikeElem (R := ℚ) (entry 0 1) := by
  rw [coefficientSpan_eq_entrySpan]
  exact ⟨Submodule.subset_span ⟨(0, 1), rfl⟩, entry01_ne_zero, entry01_not_groupLike⟩

/-- The finite-basis coefficient formula recovers the ordered universal matrix coproduct. -/
example (i j : Fin 2) :
    Coalgebra.comul (R := ℚ) (entry i j) =
      ∑ k : Fin 2, entry i k ⊗ₜ[ℚ] entry k j := by
  have hc (k : Fin 2) : (Pi.basisFun ℚ (Fin 2)).coord k = coordinate k := by
    ext m
    simp [Module.Basis.coord_apply, coordinate]
  have hb (k : Fin 2) : Pi.basisFun ℚ (Fin 2) k = vector k := rfl
  simpa only [hc, hb, coefficient_coordinate_vector] using
    comodule.comul_coefficient_basis (Pi.basisFun ℚ (Fin 2)) i j

/-- The coefficient counit formula recovers evaluation of the universal matrix at the identity. -/
example (i j : Fin 2) :
    Coalgebra.counit (R := ℚ) (entry i j) = (1 : Matrix (Fin 2) (Fin 2) ℚ) i j := by
  have hc (k : Fin 2) : (Pi.basisFun ℚ (Fin 2)).coord k = coordinate k := by
    ext m
    simp [Module.Basis.coord_apply, coordinate]
  have hb (k : Fin 2) : Pi.basisFun ℚ (Fin 2) k = vector k := rfl
  simpa only [hc, hb, coefficient_coordinate_vector, Matrix.one_apply] using
    comodule.counit_coefficient_basis (Pi.basisFun ℚ (Fin 2)) i j

section Lift

universe uLift

private abbrev liftEquiv : M ≃ₗ[ℚ] ULift.{uLift} M :=
  (ULift.moduleEquiv : ULift.{uLift} M ≃ₗ[ℚ] M).symm

private abbrev liftedComodule : Coalgebra.RightComodule ℚ C (ULift.{uLift} M) :=
  comodule.transport liftEquiv

private def liftHom : Coalgebra.RightComoduleHom comodule liftedComodule.{uLift} :=
  Coalgebra.RightComodule.transportHom comodule liftEquiv

private theorem liftHom_bijective : Function.Bijective liftHom.{uLift} := by
  simpa only [liftHom, Coalgebra.RightComodule.coe_transportHom] using
    liftEquiv.{uLift}.bijective

-- The pointwise comparison extracts the same nonzero off-diagonal entry.
private theorem lifted_coefficient_entry01 :
    liftedComodule.{uLift}.coefficient ((coordinate 0).comp liftEquiv.symm.toLinearMap)
        (liftHom (vector 1)) = entry 0 1 ∧
      liftedComodule.{uLift}.coefficient ((coordinate 0).comp liftEquiv.symm.toLinearMap)
        (liftHom (vector 1)) ≠ 0 := by
  have h := Coalgebra.RightComoduleHom.coefficient_apply liftHom.{uLift}
    ((coordinate 0).comp liftEquiv.symm.toLinearMap) (vector 1)
  have hcomp : ((coordinate 0).comp liftEquiv.symm.toLinearMap).comp
      liftHom.{uLift}.toLinearMap = coordinate 0 := by
    simpa only [liftHom, Coalgebra.RightComodule.transportHom_toLinearMap] using
      (show ((coordinate 0).comp liftEquiv.symm.toLinearMap).comp
          liftEquiv.{uLift}.toLinearMap = coordinate 0 from by
        apply LinearMap.ext
        intro m
        exact congrArg (coordinate 0) (liftEquiv.{uLift}.symm_apply_apply m))
  rw [hcomp, coefficient_coordinate_vector] at h
  exact ⟨h, by rw [h]; exact entry01_ne_zero⟩

-- Each comparison retains the source and transported target before using
-- any description of the coefficient span by matrix entries.
private theorem lifted_coefficientSpan_le :
    liftedComodule.{uLift}.coefficientSpan ≤ comodule.coefficientSpan :=
  Coalgebra.RightComoduleHom.coefficientSpan_le_of_surjective liftHom
    liftHom_bijective.surjective

private theorem coefficientSpan_eq_lifted :
    comodule.coefficientSpan = liftedComodule.{uLift}.coefficientSpan :=
  Coalgebra.RightComoduleHom.coefficientSpan_eq_of_bijective liftHom liftHom_bijective

private theorem coefficientSpan_le_lifted :
    comodule.coefficientSpan ≤ liftedComodule.{uLift}.coefficientSpan :=
  Coalgebra.RightComoduleHom.coefficientSpan_le_of_injective liftHom
    liftHom_bijective.injective

private theorem lifted_coefficientSubcoalgebra_le :
    liftedComodule.{uLift}.coefficientSubcoalgebra.toSubmodule ≤
      comodule.coefficientSubcoalgebra.toSubmodule :=
  Coalgebra.RightComoduleHom.coefficientSubcoalgebra_toSubmodule_le_of_surjective
    liftHom liftHom_bijective.surjective

private theorem coefficientSubcoalgebra_eq_lifted :
    comodule.coefficientSubcoalgebra = liftedComodule.{uLift}.coefficientSubcoalgebra :=
  Coalgebra.RightComoduleHom.coefficientSubcoalgebra_eq_of_bijective
    liftHom liftHom_bijective

private theorem coefficientSubcoalgebra_le_lifted :
    comodule.coefficientSubcoalgebra.toSubmodule ≤
      liftedComodule.{uLift}.coefficientSubcoalgebra.toSubmodule :=
  Coalgebra.RightComoduleHom.coefficientSubcoalgebra_toSubmodule_le_of_injective
    liftHom liftHom_bijective.injective

private theorem lifted_coefficientSpan_fg_nonzero_proper :
    liftedComodule.{uLift}.coefficientSpan.FG ∧
      liftedComodule.{uLift}.coefficientSpan ≠ ⊥ ∧
      liftedComodule.{uLift}.coefficientSpan ≠ ⊤ := by
  rw [← coefficientSpan_eq_lifted]
  exact coefficientSpan_fg_nonzero_proper

end Lift

end ComoduleCoefficientsGL2
