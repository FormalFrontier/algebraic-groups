/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.UnitriangularStageNormality
public import Mathlib.Data.ZMod.Basic

/-!
# Ordinary-import clients for native stage normality
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory MonObj MonoidalCategory commutatorElement

example (K : Type) [CommRing K] (n r : ℕ) :
    IsMonHom.Normal (unitriangularStageInclusion K n r).hom.hom := inferInstance

example : IsMonHom.Normal (unitriangularStageInclusion (ZMod 1) 0 0).hom.hom :=
  inferInstance

example : IsMonHom.Normal (unitriangularStageInclusion (ZMod 1) 1 4).hom.hom :=
  inferInstance

example : IsMonHom.Normal (unitriangularStageInclusion ℤ 3 0).hom.hom :=
  inferInstance

example : IsMonHom.Normal (unitriangularStageInclusion ℤ 3 1).hom.hom :=
  inferInstance

example (K : Type) [CommRing K] (R : Type) [CommRing R] [Algebra K R]
    (g : Matrix.UnitriangularGroup (Fin 3) R)
    (s : Matrix.UnitriangularGroup.superdiagonalSubgroup 3 R 2) :
    CartesianMonoidalCategory.lift
        (unitriangularGroupMulEquivPoints K (Fin 3) R g)
        (unitriangularStagePointMulEquiv K 3 2 R s) ≫
      unitriangularStageConjugation K 3 2 =
        unitriangularStagePointMulEquiv K 3 2 R
          ⟨g * s.1 * g⁻¹,
            (inferInstance : (Matrix.UnitriangularGroup.superdiagonalSubgroup 3 R 2).Normal).conj_mem
              s.1 s.2 g⟩ :=
  unitriangularStageConjugation_point K 3 2 R g s

example (R : Type) [CommRing R]
    (g : Matrix.UnitriangularGroup (Fin 3) R)
    (s : Matrix.UnitriangularGroup.superdiagonalSubgroup 3 R 2) :
    (((g * s.1 * g⁻¹).1.1 : Matrix (Fin 3) (Fin 3) R) 0 2) =
      ((s.1.1 : Matrix (Fin 3) (Fin 3) R) 0 2) := by
  have hg : g ∈ Matrix.UnitriangularGroup.superdiagonalSubgroup 3 R 1 := by
    rw [Matrix.UnitriangularGroup.superdiagonalSubgroup_one]
    trivial
  have hc : ⁅g, s.1⁆ ∈ Matrix.UnitriangularGroup.superdiagonalSubgroup 3 R (1 + 2) :=
    (Subgroup.commutator_le.mp
      (Matrix.UnitriangularGroup.superdiagonalSubgroup_commutator 3 R 1 2)) g hg s.1 s.2
  have hcomm : g * s.1 = s.1 * g := by
    apply commutatorElement_eq_one_iff_mul_comm.mp
    have hbot : ⁅g, s.1⁆ ∈ (⊥ : Subgroup (Matrix.UnitriangularGroup (Fin 3) R)) := by
      simpa only [show 1 + 2 = 3 by decide,
        Matrix.UnitriangularGroup.superdiagonalSubgroup_end] using hc
    exact Subgroup.mem_bot.mp hbot
  have hconj : g * s.1 * g⁻¹ = s.1 := by
    calc
      g * s.1 * g⁻¹ = s.1 * g * g⁻¹ := by rw [hcomm]
      _ = s.1 := by simp [mul_assoc]
  rw [hconj]
