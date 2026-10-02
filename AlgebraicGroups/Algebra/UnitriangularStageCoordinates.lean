/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.UnitriangularStageCoordinateRing
public import AlgebraicGroups.GroupScheme.Additive
public import AlgebraicGroups.GroupTheory.UnitriangularSuperdiagonalQuotients

/-!
# Primitive superdiagonal coordinates in unitriangular stage Hopf algebras

At every positive stage, an entry on the stage's superdiagonal is primitive.
The two endpoints of its matrix coproduct survive the stage quotient, while
every strictly intermediate summand contains an entry of gap smaller than the
stage index. This holds over arbitrary commutative base rings.
-/

@[expose] public section

noncomputable section

open GeneralLinearCoordinateRing UnitriangularCoordinateRing
open scoped TensorProduct

namespace UnitriangularStageCoordinateRing

set_option linter.style.haveILetI false

variable (K : Type) [CommRing K] (n r : ℕ)

noncomputable local instance : Coalgebra K (CoordinateRing K n r) :=
  (inferInstance : Bialgebra K (CoordinateRing K n r)).toCoalgebra

noncomputable local instance : CoalgebraStruct K (CoordinateRing K n r) :=
  (inferInstance : Coalgebra K (CoordinateRing K n r)).toCoalgebraStruct

/-- The universal entry on the `r`-th superdiagonal of the stage algebra. -/
def coordinate (ij : Matrix.UnitriangularGroup.superdiagonalIndex n r) :
    CoordinateRing K n r :=
  quotient K n r (entry K n ij.1.1 ij.1.2)

private theorem quotient_diag (i : Fin n) :
    quotient K n r (entry K n i i) = 1 := by
  change quotient K n r (UnitriangularCoordinateRing.quotient K (Fin n)
    (GeneralLinearCoordinateRing.matrix K (Fin n) i i)) = 1
  rw [UnitriangularCoordinateRing.quotient_diag, map_one]

private theorem quotient_lower (i j : Fin n) (hji : j < i) :
    quotient K n r (entry K n i j) = 0 := by
  change quotient K n r (UnitriangularCoordinateRing.quotient K (Fin n)
    (GeneralLinearCoordinateRing.matrix K (Fin n) i j)) = 0
  rw [UnitriangularCoordinateRing.quotient_lower K (Fin n) i j hji, map_zero]

/-- The positive-stage coordinate has zero counit. -/
theorem coordinate_counit (hr : 1 ≤ r)
    (ij : Matrix.UnitriangularGroup.superdiagonalIndex n r) :
    Coalgebra.counit (R := K) (coordinate K n r ij) = 0 := by
  have h := BialgHom.counitAlgHom_comp (quotientBialgHom K n r)
  have hentry := congrArg (fun f : Ambient K n →ₐ[K] K => f (entry K n ij.1.1 ij.1.2)) h
  change Coalgebra.counit (R := K) (coordinate K n r ij) =
    Coalgebra.counit (R := K) (entry K n ij.1.1 ij.1.2) at hentry
  rw [hentry]
  change Coalgebra.counit (R := K)
    (Ideal.Quotient.mk (UnitriangularCoordinateRing.ideal K (Fin n))
      (GeneralLinearCoordinateRing.matrix K (Fin n) ij.1.1 ij.1.2)) = 0
  rw [Bialgebra.Quotient.counit_mk, GeneralLinearCoordinateRing.native_counit_matrix]
  have hij : ij.1.1 ≠ ij.1.2 := by
    intro heq
    have := ij.2
    rw [heq] at this
    omega
  simp [hij]

/-- All interior coproduct terms vanish in the positive-stage quotient. -/
theorem coordinate_comul (hr : 1 ≤ r)
    (ij : Matrix.UnitriangularGroup.superdiagonalIndex n r) :
    Coalgebra.comul (R := K) (coordinate K n r ij) =
      coordinate K n r ij ⊗ₜ[K] 1 + 1 ⊗ₜ[K] coordinate K n r ij := by
  letI : AddCommMonoid (CoordinateRing K n r) :=
    (inferInstance : CommRing (CoordinateRing K n r)).toCommSemiring.toAddCommMonoid
  letI : Module K (CoordinateRing K n r) := Algebra.toModule
  letI : CommRing (CoordinateRing K n r ⊗[K] CoordinateRing K n r) := inferInstance
  let q := quotient K n r
  have h := BialgHom.map_comp_comulAlgHom (quotientBialgHom K n r)
  have hentry := congrArg
    (fun f : Ambient K n →ₐ[K] CoordinateRing K n r ⊗[K] CoordinateRing K n r =>
      f (entry K n ij.1.1 ij.1.2)) h
  change (Algebra.TensorProduct.map q q)
      (Coalgebra.comul (R := K) (entry K n ij.1.1 ij.1.2)) =
    Coalgebra.comul (R := K) (coordinate K n r ij) at hentry
  rw [← hentry, comul_entry K n, map_sum]
  simp only [Algebra.TensorProduct.map_tmul]
  let i := ij.1.1
  let j := ij.1.2
  have hij : i < j := by dsimp [i, j]; omega
  have hji : j ≠ i := ne_of_gt hij
  rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ i)]
  rw [← Finset.sum_erase_add (Finset.univ.erase i) _
    (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)]
  have hinterior :
      ∑ k ∈ (Finset.univ.erase i).erase j,
        q (entry K n i k) ⊗ₜ[K] q (entry K n k j) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hki : k ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
    by_cases hless : k < i
    · rw [quotient_lower K n r i k hless, TensorProduct.zero_tmul]
    · have hik : i < k := lt_of_le_of_ne (le_of_not_gt hless) (Ne.symm hki)
      by_cases hgreater : j < k
      · rw [quotient_lower K n r k j hgreater, TensorProduct.tmul_zero]
      · have hkgap : k.val < i.val + r := by
          have hgap := ij.2
          dsimp [i, j] at *
          omega
        rw [quotient_entry K n r i k hik hkgap, TensorProduct.zero_tmul]
  rw [hinterior, quotient_diag K n r i, quotient_diag K n r j]
  simp only [zero_add]
  rfl

/-- The rank-one symmetric-algebra map classifying an entry. -/
def coordinateAlgHom (ij : Matrix.UnitriangularGroup.superdiagonalIndex n r) :
    AlgebraicGeometry.additiveGroupCoordinateRing K →ₐ[K] CoordinateRing K n r := by
  letI : AddCommMonoid (CoordinateRing K n r) :=
    (inferInstance : CommRing (CoordinateRing K n r)).toCommSemiring.toAddCommMonoid
  letI : Module K (CoordinateRing K n r) := Algebra.toModule
  exact SymmetricAlgebra.lift
    ((LinearMap.ringLmapEquivSelf K K (CoordinateRing K n r)).symm
      (coordinate K n r ij))

@[simp] theorem coordinateAlgHom_coordinate
    (ij : Matrix.UnitriangularGroup.superdiagonalIndex n r) :
    coordinateAlgHom K n r ij (AlgebraicGeometry.additiveGroupCoordinate K) =
      coordinate K n r ij := by
  simp [coordinateAlgHom, AlgebraicGeometry.additiveGroupCoordinate]

/-- A positive-stage coordinate is a genuine bialgebra homomorphism. -/
def coordinateBialgHom (hr : 1 ≤ r)
    (ij : Matrix.UnitriangularGroup.superdiagonalIndex n r) :
    AlgebraicGeometry.additiveGroupCoordinateRing K →ₐc[K] CoordinateRing K n r := by
  letI : AddCommMonoid (CoordinateRing K n r) :=
    (inferInstance : CommRing (CoordinateRing K n r)).toCommSemiring.toAddCommMonoid
  letI : Module K (CoordinateRing K n r) := Algebra.toModule
  letI : CommRing (CoordinateRing K n r ⊗[K] CoordinateRing K n r) := inferInstance
  exact BialgHom.ofAlgHom (coordinateAlgHom K n r ij)
    (by
      apply SymmetricAlgebra.algHom_ext
      ext
      change Coalgebra.counit (R := K)
        (coordinateAlgHom K n r ij (AlgebraicGeometry.additiveGroupCoordinate K)) =
        Coalgebra.counit (R := K) (AlgebraicGeometry.additiveGroupCoordinate K)
      rw [coordinateAlgHom_coordinate, coordinate_counit K n r hr ij,
        AlgebraicGeometry.additiveGroupCoordinate_counit])
    (by
      apply SymmetricAlgebra.algHom_ext
      ext
      change ((Algebra.TensorProduct.map (coordinateAlgHom K n r ij)
          (coordinateAlgHom K n r ij)).comp
            (Bialgebra.comulAlgHom K (AlgebraicGeometry.additiveGroupCoordinateRing K)))
          (AlgebraicGeometry.additiveGroupCoordinate K) =
        ((Bialgebra.comulAlgHom K (CoordinateRing K n r)).comp
          (coordinateAlgHom K n r ij)) (AlgebraicGeometry.additiveGroupCoordinate K)
      rw [AlgHom.comp_apply, AlgHom.comp_apply]
      simp only [Bialgebra.comulAlgHom_apply,
        AlgebraicGeometry.additiveGroupCoordinate_comul, map_add,
        Algebra.TensorProduct.map_tmul, map_one, coordinateAlgHom_coordinate,
        coordinate_comul K n r hr ij])

/-- A successor stage has zero `r`-th coordinate. -/
theorem successor_coordinate (hr : 1 ≤ r)
    (ij : Matrix.UnitriangularGroup.superdiagonalIndex n r) :
    (successor K n r) (coordinate K n r ij) = 0 := by
  have hij : ij.1.1 < ij.1.2 := by omega
  have hgap : ij.1.2.val < ij.1.1.val + (r + 1) := by omega
  change quotient K n (r + 1) (entry K n ij.1.1 ij.1.2) = 0
  exact quotient_entry K n (r + 1) _ _ hij hgap

end UnitriangularStageCoordinateRing
