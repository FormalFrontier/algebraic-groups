/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Scheme
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.SmoothConnected
public import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# General linear coordinates with arbitrary finite matrix indices

The coordinate Hopf algebra is Tau Ceti's canonical determinant localization in
rank `Fintype.card n`. Relabelling its generic matrix and native matrix points
allows statements with an arbitrary finite index type, without introducing a
second coordinate algebra or a second Hopf structure.

## References

* J. S. Milne, *Algebraic Groups* (2017), item 2.8.
* Mathlib contributors, `Matrix.reindexRingEquiv`.
* Tau Ceti contributors, `GeneralLinear.Coordinate.HopfAlgebra` and
  `GeneralLinear.FunctorOfPoints`.
-/

public section

noncomputable section

open scoped TensorProduct

namespace TauCeti.GeneralLinear

universe u v w

variable (K : Type u) [CommRing K] (n : Type v) [Fintype n] [DecidableEq n]

/-- The canonical generic matrix labelled by an arbitrary finite index type. -/
@[expose] def reindexedGenericMatrix :
    Matrix n n (coordinateHopfAlgebra K (Fintype.card n)) :=
  Matrix.reindex (Fintype.equivFin n).symm (Fintype.equivFin n).symm
    (genericMatrix K (Fintype.card n))

omit [DecidableEq n] in
/-- The coproduct multiplies two copies of the generic matrix with the chosen labels. -/
theorem reindexedGenericMatrix_comul (i j : n) :
    Coalgebra.comul (R := K) (reindexedGenericMatrix K n i j) =
      ∑ k : n, reindexedGenericMatrix K n i k ⊗ₜ[K]
        reindexedGenericMatrix K n k j := by
  rw [reindexedGenericMatrix, Matrix.reindex_apply, Matrix.submatrix_apply,
    genericMatrix_apply, coordinateHopfAlgebra_comul_X]
  apply Fintype.sum_equiv (Fintype.equivFin n).symm
  intro k
  simp only [Matrix.submatrix_apply,
    Equiv.symm_symm, Equiv.apply_symm_apply, genericMatrix_apply]

/-- The counit of a relabelled generic entry is the corresponding identity entry. -/
theorem reindexedGenericMatrix_counit (i j : n) :
    Coalgebra.counit (R := K) (reindexedGenericMatrix K n i j) =
      (1 : Matrix n n K) i j := by
  simp only [reindexedGenericMatrix, Matrix.reindex_apply, Matrix.submatrix_apply,
    genericMatrix_apply, coordinateHopfAlgebra_counit_X, Matrix.one_apply,
    EmbeddingLike.apply_eq_iff_eq]

/-- Reading a coordinate point as an invertible matrix with arbitrary finite
indices uses the existing ring equivalence for relabelling matrices. -/
@[expose] def reindexedPointsMulEquiv (A : Type w) [CommRing A] [Algebra K A] :
    WithConv (coordinateHopfAlgebra K (Fintype.card n) →ₐ[K] A) ≃*
      Matrix.GeneralLinearGroup n A :=
  (pointsMulEquiv (R := K) (Fintype.card n)).trans
    (Units.mapEquiv (Matrix.reindexRingEquiv A (Fintype.equivFin n).symm).toMulEquiv)

/-- Relabelled points evaluate the corresponding relabelled generic entry. -/
@[simp]
theorem reindexedPointsMulEquiv_apply (A : Type w) [CommRing A] [Algebra K A]
    (f : WithConv (coordinateHopfAlgebra K (Fintype.card n) →ₐ[K] A)) (i j : n) :
    reindexedPointsMulEquiv K n A f i j = f.ofConv (reindexedGenericMatrix K n i j) := by
  simp only [reindexedPointsMulEquiv, MulEquiv.trans_apply, pointsMulEquiv_apply]
  change pointToGeneralLinear (Fintype.card n) f (Fintype.equivFin n i)
      (Fintype.equivFin n j) =
    f.ofConv (genericMatrix K (Fintype.card n) (Fintype.equivFin n i)
      (Fintype.equivFin n j))
  rw [pointToGeneralLinear_apply, genericMatrix_apply]

/-- Evaluation of a relabelled matrix point reads its original matrix entry. -/
@[simp]
theorem reindexedPointsMulEquiv_symm_apply (A : Type w) [CommRing A] [Algebra K A]
    (g : Matrix.GeneralLinearGroup n A) (i j : n) :
    ((reindexedPointsMulEquiv K n A).symm g).ofConv
      (reindexedGenericMatrix K n i j) = g i j := by
  have h := congrArg (fun q : Matrix.GeneralLinearGroup n A => q i j)
    ((reindexedPointsMulEquiv K n A).apply_symm_apply g)
  simpa only [reindexedPointsMulEquiv_apply] using h

omit [DecidableEq n] in
/-- Agreement on all relabelled generic entries determines a coordinate map. -/
theorem reindexedGenericMatrix_algHom_ext {A : Type w} [CommRing A] [Algebra K A]
    {f g : coordinateHopfAlgebra K (Fintype.card n) →ₐ[K] A}
    (h : ∀ i j : n, f (reindexedGenericMatrix K n i j) =
      g (reindexedGenericMatrix K n i j)) : f = g := by
  apply coordinateHopfAlgebra_algHom_ext K (Fintype.card n)
  intro i j
  have hentry := h ((Fintype.equivFin n).symm i) ((Fintype.equivFin n).symm j)
  simpa only [reindexedGenericMatrix, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm, Equiv.apply_symm_apply, genericMatrix_apply] using hentry

/-- Changing the value algebra commutes with relabelled point evaluation. -/
theorem reindexedPointsMulEquiv_mapValue
    {A B : Type w} [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    (φ : A →ₐ[K] B) (f : WithConv (coordinateHopfAlgebra K (Fintype.card n) →ₐ[K] A)) :
    reindexedPointsMulEquiv K n B (AlgHom.mapValue φ f) =
      Matrix.GeneralLinearGroup.map φ.toRingHom (reindexedPointsMulEquiv K n A f) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [reindexedPointsMulEquiv_apply, Matrix.GeneralLinearGroup.map_apply,
    reindexedPointsMulEquiv_apply]
  rw [AlgHom.mapValue_apply]
  rfl

/-- The inverse relabelled points equivalence is natural in the value algebra. -/
theorem mapValue_reindexedPointsMulEquiv_symm_apply
    {A B : Type w} [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    (φ : A →ₐ[K] B) (g : Matrix.GeneralLinearGroup n A) :
    AlgHom.mapValue φ ((reindexedPointsMulEquiv K n A).symm g) =
      (reindexedPointsMulEquiv K n B).symm (Matrix.GeneralLinearGroup.map φ.toRingHom g) := by
  apply (reindexedPointsMulEquiv K n B).injective
  rw [reindexedPointsMulEquiv_mapValue, MulEquiv.apply_symm_apply,
    MulEquiv.apply_symm_apply]

/-- Relabelling the canonical generic matrix preserves its unit determinant. -/
theorem isUnit_det_reindexedGenericMatrix :
    IsUnit (reindexedGenericMatrix K n).det := by
  rw [reindexedGenericMatrix, Matrix.det_reindex_self]
  exact isUnit_det_genericMatrix K (Fintype.card n)

/-- Native-index point evaluation commutes with determinants. -/
theorem reindexedPointsMulEquiv_symm_apply_det (A : Type w)
    [CommRing A] [Algebra K A] (g : Matrix.GeneralLinearGroup n A) :
    ((reindexedPointsMulEquiv K n A).symm g).ofConv
      (reindexedGenericMatrix K n).det = (g : Matrix n n A).det := by
  rw [AlgHom.map_det]
  congr 1
  ext i j
  exact reindexedPointsMulEquiv_symm_apply K n A g i j

/-- Native-index point evaluation reads the inverse determinant as the inverse determinant unit. -/
theorem reindexedPointsMulEquiv_symm_apply_ringInverse_det (A : Type w)
    [CommRing A] [Algebra K A] (g : Matrix.GeneralLinearGroup n A) :
    ((reindexedPointsMulEquiv K n A).symm g).ofConv
      (Ring.inverse (reindexedGenericMatrix K n).det) =
        ↑(Matrix.GeneralLinearGroup.det g)⁻¹ := by
  rw [(isUnit_det_reindexedGenericMatrix K n).map_ringInverse,
    reindexedPointsMulEquiv_symm_apply_det]
  exact Ring.inverse_unit (Matrix.GeneralLinearGroup.det g)

end TauCeti.GeneralLinear
