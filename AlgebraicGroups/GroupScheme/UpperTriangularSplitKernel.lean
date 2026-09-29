/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.UpperTriangular
public import AlgebraicGroups.GroupScheme.Diagonal
public import AlgebraicGroups.GroupScheme.Unitriangular
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits

/-! # The diagonal split quotient and unitriangular kernel of upper-triangular groups -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [LinearOrder n]

/-- The diagonal of the universal upper-triangular matrix induces the coordinate
map of the diagonal projection. -/
def upperTriangularDiagonalCoordinateMap :
    DiagonalCoordinateRing.CoordinateRing K n →ₐ[K]
      UpperTriangularCoordinateRing.CoordinateRing K n :=
  diagonalFromGL K n _
    (Matrix.UpperTriangularGroup.diagonal (UpperTriangularCoordinateRing.universal K n))

/-- The native diagonal section, evaluated at the universal diagonal matrix. -/
def upperTriangularDiagonalSectionCoordinateMap :
    UpperTriangularCoordinateRing.CoordinateRing K n →ₐ[K]
      DiagonalCoordinateRing.CoordinateRing K n :=
  upperTriangularFromGL K n _
    (Matrix.UpperTriangularGroup.diagonalSection (DiagonalCoordinateRing.universal K n))

/-- The published unitriangular universal matrix gives a quotient of the upper-triangular
coordinate ring. -/
def upperTriangularUnitriangularCoordinateMap :
    UpperTriangularCoordinateRing.CoordinateRing K n →ₐ[K]
      UnitriangularCoordinateRing.CoordinateRing K n :=
  upperTriangularFromGL K n _
    (Matrix.UnitriangularGroup.inUpperTriangular
      (unitriangularToGL K n _ (AlgHom.id K _)))

theorem upperTriangularDiagonalSectionCoordinateMap_comp_quotient :
    (upperTriangularDiagonalSectionCoordinateMap K n).comp
      (UpperTriangularCoordinateRing.quotient K n) =
        DiagonalCoordinateRing.quotient K n := by
  rw [upperTriangularDiagonalSectionCoordinateMap,
    upperTriangularFromGL_comp_quotient]
  apply GeneralLinearCoordinateRing.hom_ext
  intro i j
  rw [GeneralLinearCoordinateRing.evaluate_matrix]
  rfl

theorem upperTriangularUnitriangularCoordinateMap_comp_quotient :
    (upperTriangularUnitriangularCoordinateMap K n).comp
      (UpperTriangularCoordinateRing.quotient K n) =
        UnitriangularCoordinateRing.quotient K n := by
  rw [upperTriangularUnitriangularCoordinateMap,
    upperTriangularFromGL_comp_quotient]
  exact GeneralLinearCoordinateRing.evaluate_toGL
    (UnitriangularCoordinateRing.quotient K n)

theorem upperTriangularDiagonalSectionCoordinateMap_surjective :
    Function.Surjective (upperTriangularDiagonalSectionCoordinateMap K n) := by
  intro x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨UpperTriangularCoordinateRing.quotient K n y,
    congrArg (fun f : GeneralLinearCoordinateRing.CoordinateRing K n →ₐ[K]
      DiagonalCoordinateRing.CoordinateRing K n => f y)
      (upperTriangularDiagonalSectionCoordinateMap_comp_quotient K n)⟩

theorem upperTriangularUnitriangularCoordinateMap_surjective :
    Function.Surjective (upperTriangularUnitriangularCoordinateMap K n) := by
  intro x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨UpperTriangularCoordinateRing.quotient K n y,
    congrArg (fun f : GeneralLinearCoordinateRing.CoordinateRing K n →ₐ[K]
      UnitriangularCoordinateRing.CoordinateRing K n => f y)
      (upperTriangularUnitriangularCoordinateMap_comp_quotient K n)⟩

theorem upperTriangularDiagonalCoordinateMap_matrix (i j : n) :
    upperTriangularDiagonalCoordinateMap K n
      (DiagonalCoordinateRing.quotient K n (GeneralLinearCoordinateRing.matrix K n i j)) =
        if i = j then UpperTriangularCoordinateRing.quotient K n
          (GeneralLinearCoordinateRing.matrix K n i i) else 0 := by
  rw [upperTriangularDiagonalCoordinateMap, ← AlgHom.comp_apply,
    diagonalFromGL_comp_quotient, GeneralLinearCoordinateRing.evaluate_matrix,
    Matrix.UpperTriangularGroup.diagonal_apply,
    UpperTriangularCoordinateRing.universal_apply]

/-- A factorization of the upper-triangular quotient through a bialgebra morphism
inherits its bialgebra structure without imposing tensor-product injectivity. -/
def bialgHomOfCompQuotient
    {B : Type u} [CommRing B] [Bialgebra K B]
    (target : GeneralLinearCoordinateRing.CoordinateRing K n →ₐc[K] B)
    (f : UpperTriangularCoordinateRing.CoordinateRing K n →ₐ[K] B)
    (h : f.comp (UpperTriangularCoordinateRing.quotient K n) = target.toAlgHom) :
    UpperTriangularCoordinateRing.CoordinateRing K n →ₐc[K] B :=
  BialgHom.ofAlgHom f (by
    apply Ideal.Quotient.algHom_ext K
    change ((Bialgebra.counitAlgHom K B).comp f).comp
      (UpperTriangularCoordinateRing.quotient K n) =
        (Bialgebra.counitAlgHom K
          (UpperTriangularCoordinateRing.CoordinateRing K n)).comp
            (UpperTriangularCoordinateRing.quotient K n)
    rw [AlgHom.comp_assoc, h]
    exact (BialgHom.counitAlgHom_comp target).trans
      (BialgHom.counitAlgHom_comp (upperTriangularQuotientBialgHom K n)).symm)
    (by
    apply Ideal.Quotient.algHom_ext K
    change ((Algebra.TensorProduct.map f f).comp
      (Bialgebra.comulAlgHom K (UpperTriangularCoordinateRing.CoordinateRing K n))).comp
        (UpperTriangularCoordinateRing.quotient K n) =
        ((Bialgebra.comulAlgHom K B).comp f).comp
          (UpperTriangularCoordinateRing.quotient K n)
    rw [AlgHom.comp_assoc, AlgHom.comp_assoc, h]
    have hq := BialgHom.map_comp_comulAlgHom
      (upperTriangularQuotientBialgHom K n)
    change (Algebra.TensorProduct.map
      (UpperTriangularCoordinateRing.quotient K n)
      (UpperTriangularCoordinateRing.quotient K n)).comp
        (Bialgebra.comulAlgHom K (GeneralLinearCoordinateRing.CoordinateRing K n)) =
          (Bialgebra.comulAlgHom K (UpperTriangularCoordinateRing.CoordinateRing K n)).comp
            (UpperTriangularCoordinateRing.quotient K n) at hq
    rw [← hq, ← AlgHom.comp_assoc,
      ← Algebra.TensorProduct.map_comp f (UpperTriangularCoordinateRing.quotient K n)
        f (UpperTriangularCoordinateRing.quotient K n)]
    rw [h]
    exact BialgHom.map_comp_comulAlgHom target)

/-- The diagonal section is a morphism of Hopf coordinate algebras. -/
def upperTriangularDiagonalSectionBialgHom :
    UpperTriangularCoordinateRing.CoordinateRing K n →ₐc[K]
      DiagonalCoordinateRing.CoordinateRing K n :=
  bialgHomOfCompQuotient K n (diagonalQuotientBialgHom K n)
    (upperTriangularDiagonalSectionCoordinateMap K n)
    (upperTriangularDiagonalSectionCoordinateMap_comp_quotient K n)

/-- The unitriangular quotient is a morphism of Hopf coordinate algebras. -/
def upperTriangularUnitriangularBialgHom :
    UpperTriangularCoordinateRing.CoordinateRing K n →ₐc[K]
      UnitriangularCoordinateRing.CoordinateRing K n :=
  bialgHomOfCompQuotient K n (unitriangularQuotientBialgHom K n)
    (upperTriangularUnitriangularCoordinateMap K n)
    (upperTriangularUnitriangularCoordinateMap_comp_quotient K n)

private theorem upperTriangular_comul_diagonal (i : n) :
    (Bialgebra.comulAlgHom K (UpperTriangularCoordinateRing.CoordinateRing K n))
      (UpperTriangularCoordinateRing.quotient K n
        (GeneralLinearCoordinateRing.matrix K n i i)) =
      (UpperTriangularCoordinateRing.quotient K n
        (GeneralLinearCoordinateRing.matrix K n i i)) ⊗ₜ[K]
      (UpperTriangularCoordinateRing.quotient K n
        (GeneralLinearCoordinateRing.matrix K n i i)) := by
  change (Algebra.TensorProduct.map (UpperTriangularCoordinateRing.quotient K n)
    (UpperTriangularCoordinateRing.quotient K n))
      (Coalgebra.comul (R := K) (GeneralLinearCoordinateRing.matrix K n i i)) = _
  rw [GeneralLinearCoordinateRing.native_comul_matrix, map_sum]
  simp only [Algebra.TensorProduct.map_tmul]
  rw [Finset.sum_eq_single i]
  · intro index _ hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [UpperTriangularCoordinateRing.quotient_lower K n i index hlt,
        TensorProduct.zero_tmul]
    · rw [UpperTriangularCoordinateRing.quotient_lower K n index i hgt,
        TensorProduct.tmul_zero]
  · simp

/-- The native diagonal projection preserves both counit and coproduct, including
the lower-factor vanishing in the quotient tensor algebra. -/
def upperTriangularDiagonalBialgHom :
    DiagonalCoordinateRing.CoordinateRing K n →ₐc[K]
      UpperTriangularCoordinateRing.CoordinateRing K n :=
  BialgHom.ofAlgHom (upperTriangularDiagonalCoordinateMap K n) (by
    apply Ideal.Quotient.algHom_ext K
    apply GeneralLinearCoordinateRing.hom_ext
    intro i j
    change Coalgebra.counit (R := K)
      (upperTriangularDiagonalCoordinateMap K n
        (DiagonalCoordinateRing.quotient K n
          (GeneralLinearCoordinateRing.matrix K n i j))) =
      Coalgebra.counit (R := K)
        (DiagonalCoordinateRing.quotient K n
          (GeneralLinearCoordinateRing.matrix K n i j))
    rw [upperTriangularDiagonalCoordinateMap_matrix]
    by_cases hij : i = j
    · subst j
      simp only [ite_true]
      change Coalgebra.counit (R := K) (Ideal.Quotient.mk
        (UpperTriangularCoordinateRing.ideal K n) (GeneralLinearCoordinateRing.matrix K n i i)) =
        Coalgebra.counit (R := K) (Ideal.Quotient.mk
          (DiagonalCoordinateRing.ideal K n) (GeneralLinearCoordinateRing.matrix K n i i))
      rw [Bialgebra.Quotient.counit_mk, Bialgebra.Quotient.counit_mk]
    · simp only [hij, ite_false, map_zero]
      change 0 = Coalgebra.counit (R := K)
        (Ideal.Quotient.mk (DiagonalCoordinateRing.ideal K n)
          (GeneralLinearCoordinateRing.matrix K n i j))
      rw [Bialgebra.Quotient.counit_mk,
        GeneralLinearCoordinateRing.native_counit_matrix]
      simp [hij])
    (by
    letI : CommRing (UpperTriangularCoordinateRing.CoordinateRing K n ⊗[K]
      UpperTriangularCoordinateRing.CoordinateRing K n) := inferInstance
    apply Ideal.Quotient.algHom_ext K
    apply GeneralLinearCoordinateRing.hom_ext (K := K) (n := n)
    intro i j
    by_cases hij : i = j
    · subst j
      change (Algebra.TensorProduct.map
        (upperTriangularDiagonalCoordinateMap K n)
        (upperTriangularDiagonalCoordinateMap K n))
          (Coalgebra.comul (R := K)
            (DiagonalCoordinateRing.quotient K n
              (GeneralLinearCoordinateRing.matrix K n i i))) =
        Coalgebra.comul (R := K)
          (upperTriangularDiagonalCoordinateMap K n
            (DiagonalCoordinateRing.quotient K n
              (GeneralLinearCoordinateRing.matrix K n i i)))
      rw [upperTriangularDiagonalCoordinateMap_matrix, if_pos rfl]
      change (Algebra.TensorProduct.map
        (upperTriangularDiagonalCoordinateMap K n)
        (upperTriangularDiagonalCoordinateMap K n))
          ((Algebra.TensorProduct.map (DiagonalCoordinateRing.quotient K n)
            (DiagonalCoordinateRing.quotient K n))
              (Coalgebra.comul (R := K)
                (GeneralLinearCoordinateRing.matrix K n i i))) = _
      rw [GeneralLinearCoordinateRing.native_comul_matrix, map_sum, map_sum]
      simp only [Algebra.TensorProduct.map_tmul]
      rw [Finset.sum_eq_single i]
      · rw [upperTriangularDiagonalCoordinateMap_matrix, if_pos rfl]
        exact (upperTriangular_comul_diagonal K n i).symm
      · intro index _ hne
        by_cases h : i = index
        · exact (hne h.symm).elim
        · rw [DiagonalCoordinateRing.quotient_offDiagonal K n i index h,
            map_zero, TensorProduct.zero_tmul]
      · simp
    · change (Algebra.TensorProduct.map
        (upperTriangularDiagonalCoordinateMap K n)
        (upperTriangularDiagonalCoordinateMap K n))
          (Coalgebra.comul (R := K)
            (DiagonalCoordinateRing.quotient K n
              (GeneralLinearCoordinateRing.matrix K n i j))) =
        Coalgebra.comul (R := K)
          (upperTriangularDiagonalCoordinateMap K n
            (DiagonalCoordinateRing.quotient K n
              (GeneralLinearCoordinateRing.matrix K n i j)))
      rw [DiagonalCoordinateRing.quotient_offDiagonal K n i j hij,
        map_zero, map_zero]
      simp)

/-- Diagonal projection on group schemes. -/
def upperTriangularDiagonalProjection :
    upperTriangularGroupScheme K n ⟶ diagonalGroupScheme K n :=
  (hopfSpec (.of K)).map
    (Opposite.op (CommHopfAlgCat.ofHom (upperTriangularDiagonalBialgHom K n)))

/-- Diagonal section on group schemes. -/
def upperTriangularDiagonalSection :
    diagonalGroupScheme K n ⟶ upperTriangularGroupScheme K n :=
  (hopfSpec (.of K)).map
    (Opposite.op (CommHopfAlgCat.ofHom (upperTriangularDiagonalSectionBialgHom K n)))

/-- The unitriangular closed subgroup of the upper-triangular group. -/
def unitriangularToUpperTriangular :
    unitriangularGroupScheme K n ⟶ upperTriangularGroupScheme K n :=
  (hopfSpec (.of K)).map
    (Opposite.op (CommHopfAlgCat.ofHom (upperTriangularUnitriangularBialgHom K n)))

theorem upperTriangularDiagonalProjection_left :
    (upperTriangularDiagonalProjection K n).hom.hom.left =
      Spec.map (CommRingCat.ofHom (upperTriangularDiagonalCoordinateMap K n).toRingHom) := rfl

theorem upperTriangularDiagonalSection_left :
    (upperTriangularDiagonalSection K n).hom.hom.left =
      Spec.map (CommRingCat.ofHom
        (upperTriangularDiagonalSectionCoordinateMap K n).toRingHom) := rfl

theorem unitriangularToUpperTriangular_left :
    (unitriangularToUpperTriangular K n).hom.hom.left =
      Spec.map (CommRingCat.ofHom
        (upperTriangularUnitriangularCoordinateMap K n).toRingHom) := rfl

theorem unitriangularToUpperTriangular_isClosedImmersion :
    IsClosedImmersion (unitriangularToUpperTriangular K n).hom.hom.left := by
  rw [unitriangularToUpperTriangular_left]
  exact IsClosedImmersion.spec_of_surjective _
    (upperTriangularUnitriangularCoordinateMap_surjective K n)

theorem upperTriangularDiagonalCoordinateMap_section :
    (upperTriangularDiagonalSectionCoordinateMap K n).comp
      (upperTriangularDiagonalCoordinateMap K n) = AlgHom.id K _ := by
  apply Ideal.Quotient.algHom_ext K
  apply GeneralLinearCoordinateRing.hom_ext (K := K) (n := n)
  intro i j
  change upperTriangularDiagonalSectionCoordinateMap K n
    (upperTriangularDiagonalCoordinateMap K n
      (DiagonalCoordinateRing.quotient K n
        (GeneralLinearCoordinateRing.matrix K n i j))) =
    DiagonalCoordinateRing.quotient K n (GeneralLinearCoordinateRing.matrix K n i j)
  rw [upperTriangularDiagonalCoordinateMap_matrix]
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    have h := congrArg (fun f : GeneralLinearCoordinateRing.CoordinateRing K n →ₐ[K]
      DiagonalCoordinateRing.CoordinateRing K n =>
        f (GeneralLinearCoordinateRing.matrix K n i i))
      (upperTriangularDiagonalSectionCoordinateMap_comp_quotient K n)
    exact h
  · simp only [hij, ite_false, map_zero]
    exact (DiagonalCoordinateRing.quotient_offDiagonal K n i j hij).symm

theorem upperTriangularDiagonal_section :
    upperTriangularDiagonalSection K n ≫ upperTriangularDiagonalProjection K n =
      𝟙 (diagonalGroupScheme K n) := by
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  change (upperTriangularDiagonalSection K n).hom.hom.left ≫
    (upperTriangularDiagonalProjection K n).hom.hom.left =
      𝟙 (Spec (.of (DiagonalCoordinateRing.CoordinateRing K n)))
  rw [upperTriangularDiagonalSection_left,
    upperTriangularDiagonalProjection_left]
  change Spec.map (CommRingCat.ofHom
    (upperTriangularDiagonalSectionCoordinateMap K n).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (upperTriangularDiagonalCoordinateMap K n).toRingHom) =
    𝟙 (Spec (.of (DiagonalCoordinateRing.CoordinateRing K n)))
  rw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    ((upperTriangularDiagonalSectionCoordinateMap K n).comp
      (upperTriangularDiagonalCoordinateMap K n)).toRingHom) = _
  rw [upperTriangularDiagonalCoordinateMap_section]
  exact Spec.map_id (CommRingCat.of (DiagonalCoordinateRing.CoordinateRing K n))

theorem unitriangularToUpperTriangular_inclusion :
    unitriangularToUpperTriangular K n ≫ upperTriangularInclusion K n =
      unitriangularInclusion K n := by
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  change (unitriangularToUpperTriangular K n).hom.hom.left ≫
    (upperTriangularInclusion K n).hom.hom.left =
      (unitriangularInclusion K n).hom.hom.left
  rw [unitriangularToUpperTriangular_left,
    upperTriangularInclusion_left, unitriangularInclusion_left]
  change Spec.map (CommRingCat.ofHom
    (upperTriangularUnitriangularCoordinateMap K n).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (UpperTriangularCoordinateRing.quotient K n).toRingHom) =
    Spec.map (CommRingCat.ofHom (UnitriangularCoordinateRing.quotient K n).toRingHom)
  rw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    ((upperTriangularUnitriangularCoordinateMap K n).comp
      (UpperTriangularCoordinateRing.quotient K n)).toRingHom) = _
  rw [upperTriangularUnitriangularCoordinateMap_comp_quotient]

theorem upperTriangularDiagonalSection_inclusion :
    upperTriangularDiagonalSection K n ≫ upperTriangularInclusion K n =
      diagonalInclusion K n := by
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  change (upperTriangularDiagonalSection K n).hom.hom.left ≫
    (upperTriangularInclusion K n).hom.hom.left =
      (diagonalInclusion K n).hom.hom.left
  rw [upperTriangularDiagonalSection_left,
    upperTriangularInclusion_left, diagonalInclusion_left]
  change Spec.map (CommRingCat.ofHom
    (upperTriangularDiagonalSectionCoordinateMap K n).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (UpperTriangularCoordinateRing.quotient K n).toRingHom) =
    Spec.map (CommRingCat.ofHom (DiagonalCoordinateRing.quotient K n).toRingHom)
  rw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    ((upperTriangularDiagonalSectionCoordinateMap K n).comp
      (UpperTriangularCoordinateRing.quotient K n)).toRingHom) = _
  rw [upperTriangularDiagonalSectionCoordinateMap_comp_quotient]

private theorem diagonalCounit_matrix (i j : n) :
    (Bialgebra.counitAlgHom K (DiagonalCoordinateRing.CoordinateRing K n))
      (DiagonalCoordinateRing.quotient K n
        (GeneralLinearCoordinateRing.matrix K n i j)) = if i = j then 1 else 0 := by
  change Coalgebra.counit (R := K)
    (Ideal.Quotient.mk (DiagonalCoordinateRing.ideal K n)
      (GeneralLinearCoordinateRing.matrix K n i j)) = _
  rw [Bialgebra.Quotient.counit_mk,
    GeneralLinearCoordinateRing.native_counit_matrix]
  simp [Matrix.one_apply]

theorem upperTriangularDiagonalSquare_alg :
    (upperTriangularUnitriangularCoordinateMap K n).comp
      (upperTriangularDiagonalCoordinateMap K n) =
        (Algebra.ofId K (UnitriangularCoordinateRing.CoordinateRing K n)).comp
          (Bialgebra.counitAlgHom K (DiagonalCoordinateRing.CoordinateRing K n)) := by
  apply Ideal.Quotient.algHom_ext K
  apply GeneralLinearCoordinateRing.hom_ext (K := K) (n := n)
  intro i j
  change (upperTriangularUnitriangularCoordinateMap K n)
    (upperTriangularDiagonalCoordinateMap K n
      (DiagonalCoordinateRing.quotient K n
        (GeneralLinearCoordinateRing.matrix K n i j))) =
    (Algebra.ofId K (UnitriangularCoordinateRing.CoordinateRing K n))
      ((Bialgebra.counitAlgHom K (DiagonalCoordinateRing.CoordinateRing K n))
        (DiagonalCoordinateRing.quotient K n
          (GeneralLinearCoordinateRing.matrix K n i j)))
  rw [upperTriangularDiagonalCoordinateMap_matrix, diagonalCounit_matrix]
  by_cases hij : i = j
  · subst j
    simp only [ite_true, map_one]
    have h := congrArg (fun f : GeneralLinearCoordinateRing.CoordinateRing K n →ₐ[K]
      UnitriangularCoordinateRing.CoordinateRing K n =>
        f (GeneralLinearCoordinateRing.matrix K n i i))
      (upperTriangularUnitriangularCoordinateMap_comp_quotient K n)
    change upperTriangularUnitriangularCoordinateMap K n
      (UpperTriangularCoordinateRing.quotient K n
        (GeneralLinearCoordinateRing.matrix K n i i)) = _ at h
    rw [h, UnitriangularCoordinateRing.quotient_diag]
  · simp [hij]

/-- The square of coordinate rings with the diagonal counit commutes. -/
theorem upperTriangularDiagonalSquare_commutes :
    CommRingCat.ofHom (upperTriangularDiagonalCoordinateMap K n).toRingHom ≫
      CommRingCat.ofHom (upperTriangularUnitriangularCoordinateMap K n).toRingHom =
    CommRingCat.ofHom
        (Bialgebra.counitAlgHom K (DiagonalCoordinateRing.CoordinateRing K n)).toRingHom ≫
      CommRingCat.ofHom
        (algebraMap K (UnitriangularCoordinateRing.CoordinateRing K n)) := by
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom (upperTriangularDiagonalSquare_alg K n)

/-- The published unitriangular quotient is the pushout of the diagonal
projection's coordinate map along the diagonal Hopf counit, for arbitrary
commutative target rings and arbitrary compatible scalar maps. -/
theorem upperTriangularDiagonalSquare_isPushout :
    IsPushout
      (CommRingCat.ofHom (upperTriangularDiagonalCoordinateMap K n).toRingHom)
      (CommRingCat.ofHom
        (Bialgebra.counitAlgHom K (DiagonalCoordinateRing.CoordinateRing K n)).toRingHom)
      (CommRingCat.ofHom (upperTriangularUnitriangularCoordinateMap K n).toRingHom)
      (CommRingCat.ofHom
        (algebraMap K (UnitriangularCoordinateRing.CoordinateRing K n))) := by
  refine IsPushout.mk' (upperTriangularDiagonalSquare_commutes K n) ?_ ?_
  · intro B phi psi hphi _
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    have h := congrArg (fun f : CommRingCat.of
        (UpperTriangularCoordinateRing.CoordinateRing K n) ⟶ B =>
          f.hom (UpperTriangularCoordinateRing.quotient K n y)) hphi
    change phi.hom (upperTriangularUnitriangularCoordinateMap K n
      (UpperTriangularCoordinateRing.quotient K n y)) =
      psi.hom (upperTriangularUnitriangularCoordinateMap K n
        (UpperTriangularCoordinateRing.quotient K n y)) at h
    rw [← AlgHom.comp_apply,
      upperTriangularUnitriangularCoordinateMap_comp_quotient] at h
    exact h
  · intro B a b hcompatible
    have hdiag (i : n) : a.hom (UpperTriangularCoordinateRing.quotient K n
        (GeneralLinearCoordinateRing.matrix K n i i)) = 1 := by
      have h := congrArg (fun f : CommRingCat.of
        (DiagonalCoordinateRing.CoordinateRing K n) ⟶ B =>
          f.hom (DiagonalCoordinateRing.quotient K n
            (GeneralLinearCoordinateRing.matrix K n i i))) hcompatible
      change a.hom (upperTriangularDiagonalCoordinateMap K n
        (DiagonalCoordinateRing.quotient K n
          (GeneralLinearCoordinateRing.matrix K n i i))) =
        b.hom ((Bialgebra.counitAlgHom K (DiagonalCoordinateRing.CoordinateRing K n))
          (DiagonalCoordinateRing.quotient K n
            (GeneralLinearCoordinateRing.matrix K n i i))) at h
      rw [upperTriangularDiagonalCoordinateMap_matrix, if_pos rfl,
        diagonalCounit_matrix, if_pos rfl, map_one] at h
      exact h
    have hbase (r : K) : a.hom (algebraMap K
        (UpperTriangularCoordinateRing.CoordinateRing K n) r) = b.hom r := by
      have h := congrArg (fun f : CommRingCat.of
        (DiagonalCoordinateRing.CoordinateRing K n) ⟶ B =>
          f.hom (algebraMap K (DiagonalCoordinateRing.CoordinateRing K n) r))
        hcompatible
      change a.hom (upperTriangularDiagonalCoordinateMap K n
        (algebraMap K (DiagonalCoordinateRing.CoordinateRing K n) r)) =
        b.hom ((Bialgebra.counitAlgHom K (DiagonalCoordinateRing.CoordinateRing K n))
          (algebraMap K (DiagonalCoordinateRing.CoordinateRing K n) r)) at h
      simpa only [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] using h
    let source : GeneralLinearCoordinateRing.CoordinateRing K n →+* B :=
      a.hom.comp (UpperTriangularCoordinateRing.quotient K n).toRingHom
    have hkill (i j : n) : source (UnitriangularCoordinateRing.relation K n i j) = 0 := by
      change a.hom ((UpperTriangularCoordinateRing.quotient K n)
        (UnitriangularCoordinateRing.relation K n i j)) = 0
      by_cases hji : j < i
      · simp only [UnitriangularCoordinateRing.relation, hji, ite_true]
        rw [UpperTriangularCoordinateRing.quotient_lower K n i j hji, map_zero]
      · by_cases hij : i = j
        · subst j
          simp only [UnitriangularCoordinateRing.relation, lt_irrefl, ite_false, ite_true]
          rw [map_sub, map_one, map_sub, map_one, hdiag, sub_self]
        · simp [UnitriangularCoordinateRing.relation, hji, hij]
    let lift : UnitriangularCoordinateRing.CoordinateRing K n →+* B :=
      Ideal.Quotient.lift (UnitriangularCoordinateRing.ideal K n) source (by
        intro element membership
        have h : UnitriangularCoordinateRing.ideal K n ≤ RingHom.ker source := by
          apply Ideal.span_le.mpr
          rintro _ ⟨⟨i, j⟩, rfl⟩
          exact RingHom.mem_ker.mpr (hkill i j)
        exact RingHom.mem_ker.mp (h membership))
    refine ⟨CommRingCat.ofHom lift, ?_, ?_⟩
    · apply CommRingCat.hom_ext
      apply RingHom.ext
      intro element
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective element
      change lift (upperTriangularUnitriangularCoordinateMap K n
        (UpperTriangularCoordinateRing.quotient K n y)) =
          a.hom (UpperTriangularCoordinateRing.quotient K n y)
      rw [← AlgHom.comp_apply,
        upperTriangularUnitriangularCoordinateMap_comp_quotient]
      rfl
    · apply CommRingCat.hom_ext
      apply RingHom.ext
      intro r
      change lift (algebraMap K (UnitriangularCoordinateRing.CoordinateRing K n) r) =
        b.hom r
      change source (algebraMap K (GeneralLinearCoordinateRing.CoordinateRing K n) r) =
        b.hom r
      exact hbase r

/-- The identity fiber of the diagonal projection is the existing unitriangular
scheme, as a pullback of arbitrary schemes. -/
theorem upperTriangularDiagonalSquare_isPullback :
    IsPullback (unitriangularToUpperTriangular K n).hom.hom.left
      (unitriangularGroupUnderlyingScheme K n).hom
      (upperTriangularDiagonalProjection K n).hom.hom.left
      η[diagonalGroupUnderlyingScheme K n].left := by
  change IsPullback
    (Spec.map (CommRingCat.ofHom
      (upperTriangularUnitriangularCoordinateMap K n).toRingHom))
    (Spec.map (CommRingCat.ofHom
      (algebraMap K (UnitriangularCoordinateRing.CoordinateRing K n))))
    (Spec.map (CommRingCat.ofHom
      (upperTriangularDiagonalCoordinateMap K n).toRingHom))
    (Spec.map (CommRingCat.ofHom
      (Bialgebra.counitAlgHom K (DiagonalCoordinateRing.CoordinateRing K n)).toRingHom))
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (upperTriangularDiagonalSquare_isPushout K n)

/-- The identity fiber square remains a pullback over the fixed base `Spec K`. -/
theorem upperTriangularDiagonalSquare_isPullback_over :
    IsPullback (unitriangularToUpperTriangular K n).hom.hom
      (toUnit (unitriangularGroupScheme K n).toMon.X)
      (upperTriangularDiagonalProjection K n).hom.hom
      η[(diagonalGroupScheme K n).toMon.X] := by
  exact IsPullback.of_map_of_faithful (F := Over.forget (Spec (.of K)))
    (upperTriangularDiagonalSquare_isPullback K n)

/-- Unique morphism to the trivial group object. -/
def unitriangularToTrivialGroupHom :
    unitriangularGroupScheme K n ⟶ Grp.trivial (Over (Spec (.of K))) :=
  Grp.homMk' (default : (unitriangularGroupScheme K n).toMon ⟶
    Mon.trivial (Over (Spec (.of K))))

/-- The identity section of the diagonal group scheme. -/
def diagonalUnitGroupHom :
    Grp.trivial (Over (Spec (.of K))) ⟶ diagonalGroupScheme K n :=
  Grp.homMk' (0 : Mon.trivial (Over (Spec (.of K))) ⟶
    (diagonalGroupScheme K n).toMon)

/-- The published unitriangular group scheme is the genuine categorical kernel
of the upper-triangular diagonal projection. -/
theorem upperTriangularDiagonalSquare_isPullback_group :
    IsPullback (unitriangularToUpperTriangular K n)
      (unitriangularToTrivialGroupHom K n)
      (upperTriangularDiagonalProjection K n) (diagonalUnitGroupHom K n) := by
  apply IsPullback.of_map_of_faithful (Grp.forget (Over (Spec (.of K))))
  change IsPullback (unitriangularToUpperTriangular K n).hom.hom
    (toUnit (unitriangularGroupScheme K n).toMon.X)
    (upperTriangularDiagonalProjection K n).hom.hom
    (toUnit (MonoidalCategoryStruct.tensorUnit (Over (Spec (.of K)))) ≫
      η[(diagonalGroupScheme K n).toMon.X])
  simpa only [toUnit_unit, Category.id_comp]
    using upperTriangularDiagonalSquare_isPullback_over K n

variable (R : Type u) [CommRing R] [Algebra K R]

/-- Projection on every commutative test algebra is the native diagonal map. -/
theorem upperTriangularDiagonalCoordinateMap_point
    (s : Matrix.UpperTriangularGroup n R) :
    (upperTriangularFromGL K n R s).comp (upperTriangularDiagonalCoordinateMap K n) =
      diagonalFromGL K n R (Matrix.UpperTriangularGroup.diagonal s) := by
  apply Ideal.Quotient.algHom_ext K
  apply GeneralLinearCoordinateRing.hom_ext (K := K) (n := n)
  intro i j
  change (upperTriangularFromGL K n R s)
    (upperTriangularDiagonalCoordinateMap K n
      (DiagonalCoordinateRing.quotient K n
        (GeneralLinearCoordinateRing.matrix K n i j))) =
    (diagonalFromGL K n R (Matrix.UpperTriangularGroup.diagonal s))
      (DiagonalCoordinateRing.quotient K n
        (GeneralLinearCoordinateRing.matrix K n i j))
  rw [upperTriangularDiagonalCoordinateMap_matrix]
  have h := diagonalFromGL_comp_quotient K n R
    (Matrix.UpperTriangularGroup.diagonal s)
  have ht := upperTriangularFromGL_comp_quotient K n R s
  rw [← AlgHom.comp_apply, h, GeneralLinearCoordinateRing.evaluate_matrix,
    Matrix.UpperTriangularGroup.diagonal_apply]
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    have hs := congrArg (fun f : GeneralLinearCoordinateRing.CoordinateRing K n →ₐ[K] R =>
      f (GeneralLinearCoordinateRing.matrix K n i i)) ht
    simpa only [AlgHom.comp_apply, GeneralLinearCoordinateRing.evaluate_matrix] using hs
  · simp [hij]

/-- Section on every commutative test algebra is the native diagonal inclusion. -/
theorem upperTriangularDiagonalSectionCoordinateMap_point
    (s : Matrix.DiagonalGroup n R) :
    (diagonalFromGL K n R s).comp
      (upperTriangularDiagonalSectionCoordinateMap K n) =
        upperTriangularFromGL K n R
          (Matrix.UpperTriangularGroup.diagonalSection s) := by
  apply Ideal.Quotient.algHom_ext K
  apply GeneralLinearCoordinateRing.hom_ext (K := K) (n := n)
  intro i j
  change (diagonalFromGL K n R s)
    (upperTriangularDiagonalSectionCoordinateMap K n
      (UpperTriangularCoordinateRing.quotient K n
        (GeneralLinearCoordinateRing.matrix K n i j))) =
    (upperTriangularFromGL K n R (Matrix.UpperTriangularGroup.diagonalSection s))
      (UpperTriangularCoordinateRing.quotient K n
        (GeneralLinearCoordinateRing.matrix K n i j))
  have h := congrArg (fun f : GeneralLinearCoordinateRing.CoordinateRing K n →ₐ[K]
    DiagonalCoordinateRing.CoordinateRing K n =>
      f (GeneralLinearCoordinateRing.matrix K n i j))
    (upperTriangularDiagonalSectionCoordinateMap_comp_quotient K n)
  change upperTriangularDiagonalSectionCoordinateMap K n
    (UpperTriangularCoordinateRing.quotient K n
      (GeneralLinearCoordinateRing.matrix K n i j)) = _ at h
  rw [h]
  have hd := congrArg (fun f : GeneralLinearCoordinateRing.CoordinateRing K n →ₐ[K] R =>
    f (GeneralLinearCoordinateRing.matrix K n i j))
    (diagonalFromGL_comp_quotient K n R s)
  have ht := congrArg (fun f : GeneralLinearCoordinateRing.CoordinateRing K n →ₐ[K] R =>
    f (GeneralLinearCoordinateRing.matrix K n i j))
    (upperTriangularFromGL_comp_quotient K n R
      (Matrix.UpperTriangularGroup.diagonalSection s))
  simpa only [AlgHom.comp_apply, GeneralLinearCoordinateRing.evaluate_matrix]
    using hd.trans ht.symm

/-- Inclusion on every commutative test algebra is the native U-to-T map. -/
theorem upperTriangularUnitriangularCoordinateMap_point
    (s : Matrix.UnitriangularGroup n R) :
    (unitriangularFromGL K n R s).comp
      (upperTriangularUnitriangularCoordinateMap K n) =
        upperTriangularFromGL K n R
          (Matrix.UnitriangularGroup.inUpperTriangular s) := by
  apply Ideal.Quotient.algHom_ext K
  apply GeneralLinearCoordinateRing.hom_ext (K := K) (n := n)
  intro i j
  change (unitriangularFromGL K n R s)
    (upperTriangularUnitriangularCoordinateMap K n
      (UpperTriangularCoordinateRing.quotient K n
        (GeneralLinearCoordinateRing.matrix K n i j))) =
    (upperTriangularFromGL K n R (Matrix.UnitriangularGroup.inUpperTriangular s))
      (UpperTriangularCoordinateRing.quotient K n
        (GeneralLinearCoordinateRing.matrix K n i j))
  have h := congrArg (fun f : GeneralLinearCoordinateRing.CoordinateRing K n →ₐ[K]
    UnitriangularCoordinateRing.CoordinateRing K n =>
      f (GeneralLinearCoordinateRing.matrix K n i j))
    (upperTriangularUnitriangularCoordinateMap_comp_quotient K n)
  change upperTriangularUnitriangularCoordinateMap K n
    (UpperTriangularCoordinateRing.quotient K n
      (GeneralLinearCoordinateRing.matrix K n i j)) = _ at h
  rw [h]
  have hu := congrArg (fun f : GeneralLinearCoordinateRing.CoordinateRing K n →ₐ[K] R =>
    f (GeneralLinearCoordinateRing.matrix K n i j))
    (unitriangularFromGL_comp_quotient K n R s)
  have ht := congrArg (fun f : GeneralLinearCoordinateRing.CoordinateRing K n →ₐ[K] R =>
    f (GeneralLinearCoordinateRing.matrix K n i j))
    (upperTriangularFromGL_comp_quotient K n R
      (Matrix.UnitriangularGroup.inUpperTriangular s))
  simpa only [AlgHom.comp_apply, GeneralLinearCoordinateRing.evaluate_matrix]
    using hu.trans ht.symm

/-- All-algebra represented points of the projection recover the native diagonal. -/
theorem upperTriangularDiagonalProjection_point
    (s : Matrix.UpperTriangularGroup n R) :
    upperTriangularGroupMulEquivPoints K n R s ≫
      (upperTriangularDiagonalProjection K n).hom.hom =
        diagonalGroupMulEquivPoints K n R
          (Matrix.UpperTriangularGroup.diagonal s) := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, upperTriangularGroupMulEquivPoints_apply_left,
    upperTriangularDiagonalProjection_left, diagonalGroupMulEquivPoints_apply_left]
  change Spec.map (CommRingCat.ofHom (upperTriangularFromGL K n R s).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (upperTriangularDiagonalCoordinateMap K n).toRingHom) =
      Spec.map (CommRingCat.ofHom (diagonalFromGL K n R
        (Matrix.UpperTriangularGroup.diagonal s)).toRingHom)
  rw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    ((upperTriangularFromGL K n R s).comp
      (upperTriangularDiagonalCoordinateMap K n)).toRingHom) = _
  rw [upperTriangularDiagonalCoordinateMap_point]

/-- All-algebra represented points of the section recover native diagonal inclusion. -/
theorem upperTriangularDiagonalSection_point (s : Matrix.DiagonalGroup n R) :
    diagonalGroupMulEquivPoints K n R s ≫
      (upperTriangularDiagonalSection K n).hom.hom =
        upperTriangularGroupMulEquivPoints K n R
          (Matrix.UpperTriangularGroup.diagonalSection s) := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, diagonalGroupMulEquivPoints_apply_left,
    upperTriangularDiagonalSection_left, upperTriangularGroupMulEquivPoints_apply_left]
  change Spec.map (CommRingCat.ofHom (diagonalFromGL K n R s).toRingHom) ≫
    Spec.map (CommRingCat.ofHom
      (upperTriangularDiagonalSectionCoordinateMap K n).toRingHom) =
      Spec.map (CommRingCat.ofHom (upperTriangularFromGL K n R
        (Matrix.UpperTriangularGroup.diagonalSection s)).toRingHom)
  rw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    ((diagonalFromGL K n R s).comp
      (upperTriangularDiagonalSectionCoordinateMap K n)).toRingHom) = _
  rw [upperTriangularDiagonalSectionCoordinateMap_point]

/-- All-algebra represented points of the kernel inclusion recover native U-to-T. -/
theorem unitriangularToUpperTriangular_point (s : Matrix.UnitriangularGroup n R) :
    unitriangularGroupMulEquivPoints K n R s ≫
      (unitriangularToUpperTriangular K n).hom.hom =
        upperTriangularGroupMulEquivPoints K n R
          (Matrix.UnitriangularGroup.inUpperTriangular s) := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, unitriangularGroupMulEquivPoints_apply_left,
    unitriangularToUpperTriangular_left, upperTriangularGroupMulEquivPoints_apply_left]
  change Spec.map (CommRingCat.ofHom (unitriangularFromGL K n R s).toRingHom) ≫
    Spec.map (CommRingCat.ofHom
      (upperTriangularUnitriangularCoordinateMap K n).toRingHom) =
      Spec.map (CommRingCat.ofHom (upperTriangularFromGL K n R
        (Matrix.UnitriangularGroup.inUpperTriangular s)).toRingHom)
  rw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    ((unitriangularFromGL K n R s).comp
      (upperTriangularUnitriangularCoordinateMap K n)).toRingHom) = _
  rw [upperTriangularUnitriangularCoordinateMap_point]

end AlgebraicGeometry
