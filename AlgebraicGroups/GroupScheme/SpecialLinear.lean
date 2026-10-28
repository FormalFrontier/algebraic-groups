/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.SpecialLinearCoordinateRing
public import TauCeti.AlgebraicGeometry.GroupScheme.Points

/-!
# Special linear points with arbitrary finite matrix indices

All coordinate algebras, quotient maps, inclusions and group schemes are the
canonical Tau Ceti objects. Native determinant-one matrices are relabelled by
an equivalence of finite index types, preserving the arbitrary-index API used
by comparisons with module automorphisms.

## References

* J. S. Milne, *Algebraic Groups* (2017), item 2.8.
* Mathlib contributors, `Matrix.reindexRingEquiv` and `Matrix.det_reindex_self`.
* Tau Ceti contributors, `SpecialLinear.Basic` and `SpecialLinear.Scheme`.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace Matrix.SpecialLinearGroup
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  (R : Type*) [CommRing R]
/-- Relabelling both matrix indices preserves the determinant-one group. -/
def reindexMulEquiv (e : m ≃ n) : SpecialLinearGroup m R ≃* SpecialLinearGroup n R where
  toFun g := ⟨Matrix.reindex e e g, by rw [Matrix.det_reindex_self]; exact g.property⟩
  invFun g := ⟨Matrix.reindex e.symm e.symm g,
    by rw [Matrix.det_reindex_self]; exact g.property⟩
  left_inv g := by
    apply Subtype.ext
    ext i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      Equiv.symm_apply_apply]
  right_inv g := by
    apply Subtype.ext
    ext i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      Equiv.apply_symm_apply]
  map_mul' g h := by
    apply Subtype.ext
    exact (Matrix.reindexRingEquiv R e).map_mul g h
end Matrix.SpecialLinearGroup

namespace TauCeti.SpecialLinear

universe u v w

variable (K : Type u) [CommRing K] (n : Type v) [Fintype n] [DecidableEq n]

/-- Native special-linear points with arbitrary finite matrix indices. -/
def reindexedPointsMulEquiv (A : Type w) [CommRing A] [Algebra K A] :
    WithConv (coordinateHopfAlgebra K (Fintype.card n) →ₐ[K] A) ≃*
      Matrix.SpecialLinearGroup n A :=
  (pointsMulEquiv (R := K) (A := A) (Fintype.card n)).trans
    (Matrix.SpecialLinearGroup.reindexMulEquiv A (Fintype.equivFin n).symm)

/-- A relabelled special-linear point evaluates the corresponding generic matrix entry. -/
@[simp]
theorem reindexedPointsMulEquiv_apply (A : Type w) [CommRing A] [Algebra K A]
    (f : WithConv (coordinateHopfAlgebra K (Fintype.card n) →ₐ[K] A)) (i j : n) :
    reindexedPointsMulEquiv K n A f i j =
      f.ofConv ((coordinateMap K (Fintype.card n)).hom
        (GeneralLinear.reindexedGenericMatrix K n i j)) := by
  simp only [reindexedPointsMulEquiv, MulEquiv.trans_apply]
  change (pointsMulEquiv (R := K) (A := A) (Fintype.card n) f)
      (Fintype.equivFin n i) (Fintype.equivFin n j) = _
  rw [coe_pointsMulEquiv_apply]
  simp only [Matrix.map_apply, GeneralLinear.reindexedGenericMatrix,
    Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]

/-- Evaluation of the inverse relabelled points equivalence reads the native matrix entry. -/
@[simp]
theorem reindexedPointsMulEquiv_symm_apply (A : Type w) [CommRing A] [Algebra K A]
    (g : Matrix.SpecialLinearGroup n A) (i j : n) :
    ((reindexedPointsMulEquiv K n A).symm g).ofConv
      ((Ideal.Quotient.mk (definingHopfIdeal K (Fintype.card n)).toIdeal)
        (GeneralLinear.reindexedGenericMatrix K n i j)) = g i j := by
  have h := congrArg (fun q : Matrix.SpecialLinearGroup n A => q i j)
    ((reindexedPointsMulEquiv K n A).apply_symm_apply g)
  exact (reindexedPointsMulEquiv_apply K n A _ i j).symm.trans h

/-- Relabelled special-linear points commute with extension of the value algebra. -/
theorem reindexedPointsMulEquiv_mapValue
    {A B : Type w} [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    (φ : A →ₐ[K] B) (f : WithConv (coordinateHopfAlgebra K (Fintype.card n) →ₐ[K] A)) :
    reindexedPointsMulEquiv K n B (AlgHom.mapValue φ f) =
      Matrix.SpecialLinearGroup.map φ.toRingHom (reindexedPointsMulEquiv K n A f) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [reindexedPointsMulEquiv_apply]
  change _ = φ ((reindexedPointsMulEquiv K n A f) i j)
  rw [reindexedPointsMulEquiv_apply, AlgHom.mapValue_apply]
  rfl

/-- The inverse relabelled special-linear equivalence is natural in the value algebra. -/
theorem mapValue_reindexedPointsMulEquiv_symm_apply
    {A B : Type w} [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    (φ : A →ₐ[K] B) (g : Matrix.SpecialLinearGroup n A) :
    AlgHom.mapValue φ ((reindexedPointsMulEquiv K n A).symm g) =
      (reindexedPointsMulEquiv K n B).symm (Matrix.SpecialLinearGroup.map φ.toRingHom g) := by
  apply (reindexedPointsMulEquiv K n B).injective
  rw [reindexedPointsMulEquiv_mapValue, MulEquiv.apply_symm_apply,
    MulEquiv.apply_symm_apply]

/-- A native SL point restricted along the canonical quotient is its native GL point. -/
theorem reindexedPointsMulEquiv_symm_comp_coordinateMap
    (A : Type w) [CommRing A] [Algebra K A] (g : Matrix.SpecialLinearGroup n A) :
    ((reindexedPointsMulEquiv K n A).symm g).ofConv.comp
      (coordinateMap K (Fintype.card n)).hom.toAlgHom =
        ((GeneralLinear.reindexedPointsMulEquiv K n A).symm
          (Matrix.SpecialLinearGroup.toGL g)).ofConv := by
  apply GeneralLinear.reindexedGenericMatrix_algHom_ext K n
  intro i j
  rw [AlgHom.comp_apply]
  erw [reindexedPointsMulEquiv_symm_apply,
    GeneralLinear.reindexedPointsMulEquiv_symm_apply]
  rfl

/-- The inverse determinant evaluates to one on every relabelled special-linear point. -/
theorem reindexedPointsMulEquiv_symm_apply_ringInverse_det
    (A : Type w) [CommRing A] [Algebra K A] (g : Matrix.SpecialLinearGroup n A) :
    ((reindexedPointsMulEquiv K n A).symm g).ofConv
      ((coordinateMap K (Fintype.card n)).hom.toAlgHom
        (Ring.inverse (GeneralLinear.reindexedGenericMatrix K n).det)) = 1 := by
  have h := congrArg (fun f =>
    f (Ring.inverse (GeneralLinear.reindexedGenericMatrix K n).det))
      (reindexedPointsMulEquiv_symm_comp_coordinateMap K n A g)
  rw [AlgHom.comp_apply,
    GeneralLinear.reindexedPointsMulEquiv_symm_apply_ringInverse_det] at h
  have hdet : Matrix.GeneralLinearGroup.det (Matrix.SpecialLinearGroup.toGL g) = 1 := by
    apply Units.ext
    simpa only [Matrix.GeneralLinearGroup.val_det_apply,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Units.val_one] using g.property
  simpa only [hdet, inv_one, Units.val_one] using h

/-- The canonical special-linear inclusion sends every relabelled point to its
native general-linear inclusion. -/
theorem reindexedSchemePoint_comp_groupSchemeι
    (A : Type u) [CommRing A] [Algebra K A] (g : Matrix.SpecialLinearGroup n A) :
    groupSchemePointMulEquiv (Fintype.card n) A
        ((reindexedPointsMulEquiv K n A).symm g) ≫
      (groupSchemeι K (Fintype.card n)).hom.hom =
    GeneralLinear.groupSchemePointMulEquiv (Fintype.card n) A
      ((GeneralLinear.reindexedPointsMulEquiv K n A).symm
        (Matrix.SpecialLinearGroup.toGL g)) := by
  apply (GeneralLinear.schemePointsMulEquiv (Fintype.card n) A).injective
  rw [schemePointsMulEquiv_comp_groupSchemeι,
    schemePointsMulEquiv_groupSchemePointMulEquiv,
    GeneralLinear.schemePointsMulEquiv_groupSchemePointMulEquiv]
  have hq : CommHopfAlgCat.quotientPointsHom
      (GeneralLinear.coordinateHopfAlgebra K (Fintype.card n))
      (definingHopfIdeal K (Fintype.card n)) (CommAlgCat.of K A)
      ((reindexedPointsMulEquiv K n A).symm g) =
        (GeneralLinear.reindexedPointsMulEquiv K n A).symm
          (Matrix.SpecialLinearGroup.toGL g) := by
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro x
    rw [CommHopfAlgCat.quotientPointsHom_apply_apply]
    exact AlgHom.congr_fun (reindexedPointsMulEquiv_symm_comp_coordinateMap K n A g) x
  have h := pointsMulEquiv_toGL K (Fintype.card n)
    ((reindexedPointsMulEquiv K n A).symm g)
  rw [hq] at h
  exact h.symm

end TauCeti.SpecialLinear



namespace AlgebraicGeometry

universe u

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]

/-- Native matrix SL as a functor on arbitrary commutative `K`-algebras. -/
def specialLinearIndexedFunctor : CommAlgCat K ⥤ GrpCat where
  obj R := GrpCat.of (Matrix.SpecialLinearGroup n R)
  map f := GrpCat.ofHom (Matrix.SpecialLinearGroup.map f.hom.toRingHom)
  map_id R := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro s
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rfl
  map_comp f g := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro s
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rfl


/-- The native special linear functor with arbitrary finite indices is
represented by the canonical coordinate Hopf algebra in the same rank. -/
def specialLinearIndexedPointsIso :
    specialLinearIndexedFunctor K n ≅
      TauCeti.GroupScheme.algebraPointsFunctor K
        (TauCeti.SpecialLinear.groupScheme K (Fintype.card n)) :=
  NatIso.ofComponents
    (fun R => ((TauCeti.SpecialLinear.reindexedPointsMulEquiv K n R).symm.trans
      (TauCeti.SpecialLinear.groupSchemePointMulEquiv
        (R := K) (Fintype.card n) R)).toGrpIso)
    (fun {R S} f => by
      ext s
      apply Over.OverMorphism.ext
      change ((TauCeti.SpecialLinear.groupSchemePointMulEquiv
        (R := K) (Fintype.card n) S)
          ((TauCeti.SpecialLinear.reindexedPointsMulEquiv K n S).symm
            (Matrix.SpecialLinearGroup.map f.hom.toRingHom s))).left =
        ((algSpec (.of K)).map f.op).left ≫
          ((TauCeti.SpecialLinear.groupSchemePointMulEquiv
            (R := K) (Fintype.card n) R)
            ((TauCeti.SpecialLinear.reindexedPointsMulEquiv K n R).symm s)).left
      rw [TauCeti.SpecialLinear.groupSchemePointMulEquiv_apply_left,
        TauCeti.SpecialLinear.groupSchemePointMulEquiv_apply_left]
      change Spec.map (CommRingCat.ofHom
        ((TauCeti.SpecialLinear.reindexedPointsMulEquiv K n S).symm
          (Matrix.SpecialLinearGroup.map f.hom.toRingHom s)).ofConv.toRingHom) ≫ _ =
        Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫ _ ≫ _
      rw [← Category.assoc, ← Spec.map_comp]
      congr 2
      have h :=
        TauCeti.SpecialLinear.mapValue_reindexedPointsMulEquiv_symm_apply K n f.hom s
      rw [AlgHom.mapValue_apply] at h
      exact congrArg (fun q => CommRingCat.ofHom q.ofConv.toRingHom) h.symm)

end AlgebraicGeometry
