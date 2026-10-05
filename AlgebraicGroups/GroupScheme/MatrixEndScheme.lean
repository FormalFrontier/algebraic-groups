/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.MatrixEndAdditive
public import AlgebraicGroups.GroupScheme.VectorProduct

@[expose] public section

/-!
# Source-order endomorphisms and their matrix-group scheme

The explicit `SourceOrderedTensor K V R` carries the transported `R`-module structure
on the literal tensor order `V ⊗[K] R`. Conjugation with its canonical comparison
gives an additive End functor without choosing a basis. For finite-dimensional
`V`, a basis identifies the representing vector-group scheme with the native
square-matrix vector-group scheme.

Milne's item 2.7 gives the chosen-basis identification of finite-dimensional
additive End and matrix algebraic groups over a field. Here this identification
is realized as a group-scheme isomorphism with contravariant polynomial
coordinate pullback, and the source-order tensor model is compared separately.
The construction uses Mathlib's matrix equivalence for linear endomorphisms
and the vector-group functor of this library; matrix multiplication is not the
group law.

## References

- J. S. Milne, *Algebraic Groups* (2017), item 2.7 (additive End and
  chosen-basis square-matrix groups).
- Mathlib, `Mathlib.LinearAlgebra.Matrix.ToLin` (`LinearMap.toMatrixAlgEquiv`)
  and `Mathlib.LinearAlgebra.Dual.Basis` (matrix-entry coordinates).
-/

noncomputable section

open CategoryTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

section SourceOrderTransport

variable (K : Type u) [CommRing K] (V : Type u) [AddCommGroup V] [Module K V]
  (R : Type u) [CommRing R] [Algebra K R]

/-- Change coefficients of a source-order endomorphism by conjugating canonical
endomorphism base change with the literal-order tensor comparisons. -/
def sourceOrderedEndBaseChange (S : Type u) [CommRing S] [Algebra K S]
    (g : R →ₐ[K] S) (f : Module.End R (SourceOrderedTensor K V R)) :
    Module.End S (SourceOrderedTensor K V S) :=
  (sourceOrderedEndEquiv K V S).symm
    (endBaseChange K V R S g (sourceOrderedEndEquiv K V R f))

/-- The coefficient map preserves addition even for a non-flat algebra map. -/
def sourceOrderedEndBaseChangeAddHom (S : Type u) [CommRing S] [Algebra K S]
    (g : R →ₐ[K] S) :
    Module.End R (SourceOrderedTensor K V R) →+
      Module.End S (SourceOrderedTensor K V S) :=
  (sourceOrderedEndEquiv K V S).symm.toAddMonoidHom.comp
    ((endBaseChangeAddHom K V R S g).comp
      (sourceOrderedEndEquiv K V R).toAddMonoidHom)

@[simp]
theorem sourceOrderedEndBaseChangeAddHom_apply (S : Type u) [CommRing S] [Algebra K S]
    (g : R →ₐ[K] S) (f : Module.End R (SourceOrderedTensor K V R)) :
    sourceOrderedEndBaseChangeAddHom K V R S g f =
      sourceOrderedEndBaseChange K V R S g f := rfl

@[simp]
theorem sourceOrderedEndBaseChange_id (f : Module.End R (SourceOrderedTensor K V R)) :
    sourceOrderedEndBaseChange K V R R (AlgHom.id K R) f = f := by
  simp [sourceOrderedEndBaseChange]

@[simp]
theorem sourceOrderedEndBaseChange_comp (S T : Type u)
    [CommRing S] [Algebra K S] [CommRing T] [Algebra K T]
    (g : R →ₐ[K] S) (h : S →ₐ[K] T)
    (f : Module.End R (SourceOrderedTensor K V R)) :
    sourceOrderedEndBaseChange K V S T h (sourceOrderedEndBaseChange K V R S g f) =
      sourceOrderedEndBaseChange K V R T (h.comp g) f := by
  simp [sourceOrderedEndBaseChange, endBaseChange_comp]

/-- The action on a literal-order pure tensor, measured in the canonical
tensor model. The right-hand side uses the transported coefficient action. -/
theorem sourceOrderedEndBaseChange_tmul (S : Type u) [CommRing S] [Algebra K S]
    (g : R →ₐ[K] S) (f : Module.End R (SourceOrderedTensor K V R))
    (v : V) (s : S) :
    sourceOrderedCanonicalLinearEquiv K V S
        (sourceOrderedEndBaseChange K V R S g f (sourceOrderedTmul K V S v s)) =
      s • (g.toLinearMap.rTensor V)
        (sourceOrderedCanonicalLinearEquiv K V R
          (f (sourceOrderedTmul K V R v 1))) := by
  rw [← sourceOrderedEndEquiv_apply K V S, sourceOrderedCanonicalLinearEquiv_tmul]
  simp only [sourceOrderedEndBaseChange, LinearEquiv.apply_symm_apply,
    endBaseChange_tmul]
  rw [← sourceOrderedEndEquiv_apply K V R,
    sourceOrderedCanonicalLinearEquiv_tmul]

end SourceOrderTransport

section SourceOrderFunctor

variable (K : Type u) [Field K] (V : Type u) [AddCommGroup V] [Module K V]

/-- The additive endomorphism group on literal-order scalar extensions,
functorial in arbitrary commutative coefficient algebras. -/
def sourceOrderedAdditiveEndFunctor : CommAlgCat K ⥤ GrpCat where
  obj R := GrpCat.of (Multiplicative (Module.End R (SourceOrderedTensor K V R)))
  map g := GrpCat.ofHom (AddMonoidHom.toMultiplicative
    (sourceOrderedEndBaseChangeAddHom K V _ _ g.hom))
  map_id R := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro f
    change sourceOrderedEndBaseChange K V R R (AlgHom.id K R) f.toAdd = f.toAdd
    exact sourceOrderedEndBaseChange_id K V R f.toAdd
  map_comp g h := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro f
    change sourceOrderedEndBaseChange K V _ _ (h.hom.comp g.hom) f.toAdd =
      sourceOrderedEndBaseChange K V _ _ h.hom
        (sourceOrderedEndBaseChange K V _ _ g.hom f.toAdd)
    exact (sourceOrderedEndBaseChange_comp K V _ _ _ g.hom h.hom f.toAdd).symm

/-- Conjugation with the explicit tensor-order equivalence is natural for
every coefficient algebra map, not merely a pointwise group bijection. -/
def sourceOrderedEndGroupIso :
    sourceOrderedAdditiveEndFunctor K V ≅ additiveEndFunctor K V :=
  NatIso.ofComponents
    (fun R ↦ ((sourceOrderedEndEquiv K V R).toAddEquiv.toMultiplicative).toGrpIso)
    (fun {R S} g ↦ by
      apply GrpCat.hom_ext
      apply MonoidHom.ext
      intro f
      change sourceOrderedEndEquiv K V S
        (sourceOrderedEndBaseChange K V R S g.hom f.toAdd) =
          endBaseChange K V R S g.hom (sourceOrderedEndEquiv K V R f.toAdd)
      simp [sourceOrderedEndBaseChange])

variable [FiniteDimensional K V]

/-- The basis-free representing scheme of the literal-order End group. -/
def sourceOrderedEndPointsIso :
    sourceOrderedAdditiveEndFunctor K V ≅
      vectorGroupPointsFunctor K (Module.End K V) :=
  sourceOrderedEndGroupIso K V ≪≫ endGroupPointsIso K V

end SourceOrderFunctor

section MatrixScheme

variable (K : Type u) [Field K] (V : Type u) [AddCommGroup V] [Module K V]
  (i : Type u) [Fintype i] [DecidableEq i] (b : Module.Basis i K V)

/-- A basis identifies the original endomorphism space with square matrices. -/
def endMatrixBaseLinearEquiv : Module.End K V ≃ₗ[K] Matrix i i K :=
  (LinearMap.toMatrixAlgEquiv b).toLinearEquiv

@[simp]
theorem endMatrixBaseLinearEquiv_apply (f : Module.End K V) (row col : i) :
    endMatrixBaseLinearEquiv K V i b f row col =
      b.repr (f (b col)) row :=
  LinearMap.toMatrix_apply b b f row col

/-- The chosen-basis additive End/matrix group-scheme isomorphism from
Milne, *Algebraic Groups* (2017), item 2.7, obtained by functoriality of the
vector-group construction. Unlike a bijection on field points, this is an
isomorphism of group objects over `Spec K`. -/
def endMatrixSchemeIso :
    vectorGroupScheme K (Module.End K V) ≅ vectorGroupScheme K (Matrix i i K) :=
  (vectorGroupSchemeFunctor K).mapIso (endMatrixBaseLinearEquiv K V i b).toModuleIso

@[simp]
theorem endMatrixSchemeIso_hom :
    (endMatrixSchemeIso K V i b).hom =
      vectorGroupSchemeMap K (Module.End K V) (Matrix i i K)
        (endMatrixBaseLinearEquiv K V i b).toLinearMap := rfl

/-- The underlying morphism is the `Spec.map` of the contravariant map on
polynomial coordinate algebras. -/
theorem endMatrixSchemeIso_spec :
    (endMatrixSchemeIso K V i b).hom.hom.hom.left =
      Spec.map (CommRingCat.ofHom
        (vectorGroupCoordinateMap K (Module.End K V) (Matrix i i K)
          (endMatrixBaseLinearEquiv K V i b).toLinearMap).toRingHom) := by
  rw [endMatrixSchemeIso_hom, vectorGroupSchemeMap_left]

/-- Pullback of a matrix linear coordinate, before choosing an entry. -/
theorem endMatrixSchemeIso_coordinate (φ : Module.Dual K (Matrix i i K)) :
    vectorGroupCoordinateBialgHom K (Module.End K V) (Matrix i i K)
        (endMatrixBaseLinearEquiv K V i b).toLinearMap
        (SymmetricAlgebra.ι K _ φ) =
      SymmetricAlgebra.ι K _ (φ.comp (endMatrixBaseLinearEquiv K V i b).toLinearMap) :=
  vectorGroupCoordinateBialgHom_ι K (Module.End K V) (Matrix i i K)
    (endMatrixBaseLinearEquiv K V i b).toLinearMap φ

/-- The pullback of an entry functional is its corresponding endomorphism
coordinate in the original basis. -/
theorem endMatrixSchemeIso_entry_dual (f : Module.End K V) (row col : i) :
    (((Matrix.stdBasis K i i).dualBasis (row, col)).comp
      (endMatrixBaseLinearEquiv K V i b).toLinearMap) f =
        b.repr (f (b col)) row := by
  simp only [LinearMap.comp_apply, matrixStdBasis_dual_apply]
  exact endMatrixBaseLinearEquiv_apply K V i b f row col

variable [FiniteDimensional K V]

/-- Tensoring the base-field matrix equivalence is exactly the accepted
matrix coordinate equivalence, for any commutative coefficient algebra. -/
theorem endMatrixSchemeIso_tensor (R : Type u) [CommRing R] [Algebra K R]
    (x : Module.End K V ⊗[K] R) :
    matrixVectorLinearEquiv K i i R
        (TensorProduct.map (endMatrixBaseLinearEquiv K V i b).toLinearMap
          (LinearMap.id : R →ₗ[K] R) x) =
      endMatrixLinearEquiv K V i b R (endVectorLinearEquiv K V R x) := by
  induction x using TensorProduct.inductionOn with
  | tmul f r =>
    ext row col
    change matrixScalarEquiv K i i R
      (r ⊗ₜ[K] (endMatrixBaseLinearEquiv K V i b f)) row col = _
    rw [matrixScalarEquiv_tmul, endMatrixLinearEquiv_tmul,
      endMatrixBaseLinearEquiv_apply]
  | add x y hx hy =>
    simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- Pulling a matrix polynomial back along the native scheme map and
evaluating at an End point agrees with its accepted matrix-coordinate map. -/
theorem endMatrixSchemeIso_evaluation (R : Type u) [CommRing R] [Algebra K R]
    (f : Module.End R (R ⊗[K] V)) :
    (endCoordinateEval K V R f).comp
        (vectorGroupCoordinateMap K (Module.End K V) (Matrix i i K)
          (endMatrixBaseLinearEquiv K V i b).toLinearMap) =
      matrixCoordinateEval K i i R (endMatrixLinearEquiv K V i b R f) := by
  obtain ⟨x, rfl⟩ := (endVectorLinearEquiv K V R).surjective f
  have h := vectorGroupMulEquivAlgHom_linearMap K (Module.End K V) R
    (Matrix i i K) (endMatrixBaseLinearEquiv K V i b).toLinearMap x
  have hend : endCoordinateEval K V R (endVectorLinearEquiv K V R x) =
      (vectorGroupMulEquivAlgHom K (Module.End K V) R (.ofAdd x)).ofConv := by
    simp [endCoordinateEval, endVectorMulEquiv]
  have hmatrix : matrixCoordinateEval K i i R
      (endMatrixLinearEquiv K V i b R (endVectorLinearEquiv K V R x)) =
      (vectorGroupMulEquivAlgHom K (Matrix i i K) R
        (.ofAdd ((matrixVectorLinearEquiv K i i R).symm
          (endMatrixLinearEquiv K V i b R (endVectorLinearEquiv K V R x))))).ofConv := by
    rfl
  rw [hend, hmatrix, ← endMatrixSchemeIso_tensor K V i b R x,
    LinearEquiv.symm_apply_apply]
  exact h.symm

/-- The native scheme morphism evaluates a matrix-entry generator as the
accepted endomorphism matrix entry, including over finite or zero algebras. -/
theorem endMatrixSchemeIso_evaluation_entry (R : Type u) [CommRing R] [Algebra K R]
    (f : Module.End R (R ⊗[K] V)) (row col : i) :
    ((endCoordinateEval K V R f).comp
      (vectorGroupCoordinateMap K (Module.End K V) (Matrix i i K)
        (endMatrixBaseLinearEquiv K V i b).toLinearMap))
        (SymmetricAlgebra.ι K _ ((Matrix.stdBasis K i i).dualBasis (row, col))) =
      endMatrixLinearEquiv K V i b R f row col := by
  rw [endMatrixSchemeIso_evaluation]
  exact matrixCoordinateEval_ι K i i R _ row col

/-- A general formal polynomial, not just a field-valued point function,
evaluates under the native map by substitution of the accepted matrix entries. -/
theorem endMatrixSchemeIso_polynomial (R : Type u) [CommRing R] [Algebra K R]
    (f : Module.End R (R ⊗[K] V)) :
    ((endCoordinateEval K V R f).comp
      (vectorGroupCoordinateMap K (Module.End K V) (Matrix i i K)
        (endMatrixBaseLinearEquiv K V i b).toLinearMap)).comp
        (matrixCoordinateRingEquiv K i i).symm.toAlgHom =
      MvPolynomial.aeval
        (fun p : i × i ↦ endMatrixLinearEquiv K V i b R f p.1 p.2) := by
  rw [endMatrixSchemeIso_evaluation]
  exact matrixCoordinateEval_polynomial K i i R _

/-- The native scheme map agrees on *every algebra point* with the already
accepted endomorphism-to-matrix functor comparison, not just field points. -/
theorem endMatrixSchemeIso_points (R : Type u) [CommRing R] [Algebra K R]
    (f : Module.End R (R ⊗[K] V)) :
    (endGroupPointsIso K V).hom.app (CommAlgCat.of K R) (.ofAdd f) ≫
        (endMatrixSchemeIso K V i b).hom.hom.hom =
      (matrixGroupPointsIso K i i).hom.app (CommAlgCat.of K R)
        (.ofAdd (endMatrixLinearEquiv K V i b R f)) := by
  apply Over.OverMorphism.ext
  have hspec :
      ((endGroupPointsIso K V).hom.app (CommAlgCat.of K R) (.ofAdd f)).left ≫
        ((endMatrixSchemeIso K V i b).hom.hom.hom).left =
      ((matrixGroupPointsIso K i i).hom.app (CommAlgCat.of K R)
        (.ofAdd (endMatrixLinearEquiv K V i b R f))).left := by
    have h :
        Spec.map (CommRingCat.ofHom (endCoordinateEval K V R f).toRingHom) ≫
          Spec.map (CommRingCat.ofHom
            (vectorGroupCoordinateMap K (Module.End K V) (Matrix i i K)
              (endMatrixBaseLinearEquiv K V i b).toLinearMap).toRingHom) =
        Spec.map (CommRingCat.ofHom
          (matrixCoordinateEval K i i R (endMatrixLinearEquiv K V i b R f)).toRingHom) := by
      rw [← Spec.map_comp]
      congr 1
      exact congrArg (fun a : vectorGroupCoordinateRing K (Matrix i i K) →ₐ[K] R ↦
        CommRingCat.ofHom a.toRingHom)
          (endMatrixSchemeIso_evaluation K V i b R f)
    rw [endGroupPointsIso_apply_left, endMatrixSchemeIso_spec,
      matrixGroupPointsIso_apply_left]
    convert h using 1
    exact Iff.rfl
  exact hspec

/-- Source-order endomorphisms have the same matrix-scheme diagram through
the natural tensor-order comparison. -/
theorem sourceOrderedEndMatrixScheme_points (R : Type u) [CommRing R] [Algebra K R]
    (f : Module.End R (SourceOrderedTensor K V R)) :
    (sourceOrderedEndPointsIso K V).hom.app (CommAlgCat.of K R) (.ofAdd f) ≫
        (endMatrixSchemeIso K V i b).hom.hom.hom =
      (matrixGroupPointsIso K i i).hom.app (CommAlgCat.of K R)
        (.ofAdd (endMatrixLinearEquiv K V i b R
          (sourceOrderedEndEquiv K V R f))) := by
  exact endMatrixSchemeIso_points K V i b R (sourceOrderedEndEquiv K V R f)

/-- The explicit tensor-order equivalence followed by the accepted
chosen-basis additive matrix comparison. -/
def sourceOrderedEndMatrixGroupIso :
    sourceOrderedAdditiveEndFunctor K V ≅ additiveMatrixFunctor K i i :=
  sourceOrderedEndGroupIso K V ≪≫ endMatrixGroupIso K V i b

/-- The same comparison followed by the existing native matrix points. -/
def sourceOrderedEndMatrixPointsIso :
    sourceOrderedAdditiveEndFunctor K V ≅
      vectorGroupPointsFunctor K (Matrix i i K) :=
  sourceOrderedEndMatrixGroupIso K V i b ≪≫ matrixGroupPointsIso K i i

/-- The chosen-basis representation is exactly the literal-order End map
followed by the accepted canonical End matrix comparison. -/
theorem sourceOrderedEndMatrixGroupIso_apply (R : CommAlgCat K)
    (f : Module.End R (SourceOrderedTensor K V R)) :
    (sourceOrderedEndMatrixGroupIso K V i b).hom.app R (.ofAdd f) =
      .ofAdd (endMatrixLinearEquiv K V i b R (sourceOrderedEndEquiv K V R f)) :=
  rfl

end MatrixScheme

section MatrixSchemeBasisChange

variable (K : Type u) [Field K] (V : Type u) [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] (i j : Type u) [Fintype i] [Fintype j]
  [DecidableEq i] [DecidableEq j]
  (b : Module.Basis i K V) (c : Module.Basis j K V)

/-- A genuine isomorphism of native matrix-group schemes for two bases. -/
def endMatrixSchemeBasisChangeIso :
    vectorGroupScheme K (Matrix i i K) ≅ vectorGroupScheme K (Matrix j j K) :=
  (endMatrixSchemeIso K V i b).symm ≪≫ endMatrixSchemeIso K V j c

/-- Change a base-field square matrix by first reading its endomorphism in
the old basis, then recording it in the new basis. -/
def endMatrixSchemeBasisLinearMap : Matrix i i K →ₗ[K] Matrix j j K :=
  (endMatrixBaseLinearEquiv K V j c).toLinearMap.comp
    (endMatrixBaseLinearEquiv K V i b).symm.toLinearMap

omit [FiniteDimensional K V] in
@[simp]
theorem endMatrixSchemeBasisChangeIso_hom :
    (endMatrixSchemeBasisChangeIso K V i j b c).hom =
      vectorGroupSchemeMap K (Matrix i i K) (Matrix j j K)
        (endMatrixSchemeBasisLinearMap K V i j b c) := by
  change vectorGroupSchemeMap K (Matrix i i K) (Module.End K V)
      (endMatrixBaseLinearEquiv K V i b).symm.toLinearMap ≫
    vectorGroupSchemeMap K (Module.End K V) (Matrix j j K)
      (endMatrixBaseLinearEquiv K V j c).toLinearMap = _
  rw [← vectorGroupSchemeMap_comp]
  rfl

omit [FiniteDimensional K V] in
/-- Basis change is `Spec.map` of the linear-polynomial pullback. -/
theorem endMatrixSchemeBasisChangeIso_spec :
    (endMatrixSchemeBasisChangeIso K V i j b c).hom.hom.hom.left =
      Spec.map (CommRingCat.ofHom
        (vectorGroupCoordinateMap K (Matrix i i K) (Matrix j j K)
          (endMatrixSchemeBasisLinearMap K V i j b c)).toRingHom) := by
  rw [endMatrixSchemeBasisChangeIso_hom, vectorGroupSchemeMap_left]

omit [FiniteDimensional K V] in
/-- Pullback of a coordinate generator under native basis change. -/
theorem endMatrixSchemeBasisChangeIso_coordinate (φ : Module.Dual K (Matrix j j K)) :
    vectorGroupCoordinateBialgHom K (Matrix i i K) (Matrix j j K)
        (endMatrixSchemeBasisLinearMap K V i j b c)
        (SymmetricAlgebra.ι K _ φ) =
      SymmetricAlgebra.ι K _
        (φ.comp (endMatrixSchemeBasisLinearMap K V i j b c)) :=
  vectorGroupCoordinateBialgHom_ι K (Matrix i i K) (Matrix j j K)
    (endMatrixSchemeBasisLinearMap K V i j b c) φ

omit [FiniteDimensional K V] in
/-- Pullback of all polynomial coordinates commutes with the two chosen
presentations of the same basis-independent End vector group. -/
theorem endMatrixSchemeBasisChangeIso_coordinate_comp :
    vectorGroupCoordinateMap K (Module.End K V) (Matrix j j K)
        (endMatrixBaseLinearEquiv K V j c).toLinearMap =
      (vectorGroupCoordinateMap K (Module.End K V) (Matrix i i K)
        (endMatrixBaseLinearEquiv K V i b).toLinearMap).comp
          (vectorGroupCoordinateMap K (Matrix i i K) (Matrix j j K)
            (endMatrixSchemeBasisLinearMap K V i j b c)) := by
  apply SymmetricAlgebra.algHom_ext
  ext φ
  simp [vectorGroupCoordinateMap_ι, endMatrixSchemeBasisLinearMap,
    LinearMap.comp_apply]
  congr 1
  ext f
  simp [LinearMap.comp_apply]

set_option maxRecDepth 1024 in
/-- Matrix-coordinate evaluation after the native scheme basis change is
exactly evaluation in the accepted second-basis endomorphism coordinates. -/
theorem endMatrixSchemeBasisChangeIso_evaluation (R : Type u)
    [CommRing R] [Algebra K R] (f : Module.End R (R ⊗[K] V)) :
    (matrixCoordinateEval K i i R (endMatrixLinearEquiv K V i b R f)).comp
        (vectorGroupCoordinateMap K (Matrix i i K) (Matrix j j K)
          (endMatrixSchemeBasisLinearMap K V i j b c)) =
      matrixCoordinateEval K j j R (endMatrixLinearEquiv K V j c R f) := by
  rw [← endMatrixSchemeIso_evaluation K V i b R f, AlgHom.comp_assoc,
    ← endMatrixSchemeBasisChangeIso_coordinate_comp K V i j b c]
  exact endMatrixSchemeIso_evaluation K V j c R f

omit [FiniteDimensional K V] in
@[simp]
theorem endMatrixSchemeBasisChangeIso_refl :
    endMatrixSchemeBasisChangeIso K V i i b b =
      Iso.refl (vectorGroupScheme K (Matrix i i K)) := by
  simp [endMatrixSchemeBasisChangeIso]

omit [FiniteDimensional K V] in
theorem endMatrixSchemeBasisChangeIso_comp (l : Type u) [Fintype l]
    [DecidableEq l] (d : Module.Basis l K V) :
    endMatrixSchemeBasisChangeIso K V i j b c ≪≫
      endMatrixSchemeBasisChangeIso K V j l c d =
        endMatrixSchemeBasisChangeIso K V i l b d := by
  simp [endMatrixSchemeBasisChangeIso, Iso.trans_assoc]

set_option maxRecDepth 1024 in
/-- Scheme basis change acts on every algebra point by the *accepted*
endomorphism matrix basis change, not by an unrelated coordinate bijection. -/
theorem endMatrixSchemeBasisChangeIso_points (R : Type u)
    [CommRing R] [Algebra K R] (f : Module.End R (R ⊗[K] V)) :
    (matrixGroupPointsIso K i i).hom.app (CommAlgCat.of K R)
        (.ofAdd (endMatrixLinearEquiv K V i b R f)) ≫
        (endMatrixSchemeBasisChangeIso K V i j b c).hom.hom.hom =
      (matrixGroupPointsIso K j j).hom.app (CommAlgCat.of K R)
        ((endMatrixBasisChangeIso K V i b j c).hom.app (CommAlgCat.of K R)
          (.ofAdd (endMatrixLinearEquiv K V i b R f))) := by
  rw [endMatrixBasisChangeIso_apply]
  have hb := endMatrixSchemeIso_points K V i b R f
  have hc := endMatrixSchemeIso_points K V j c R f
  have hchange : (endMatrixSchemeIso K V i b).hom ≫
      (endMatrixSchemeBasisChangeIso K V i j b c).hom =
      (endMatrixSchemeIso K V j c).hom := by
    change (endMatrixSchemeIso K V i b).hom ≫
      ((endMatrixSchemeIso K V i b).inv ≫ (endMatrixSchemeIso K V j c).hom) = _
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have hchange' : (endMatrixSchemeIso K V i b).hom.hom.hom ≫
      (endMatrixSchemeBasisChangeIso K V i j b c).hom.hom.hom =
      (endMatrixSchemeIso K V j c).hom.hom.hom := by
    exact congrArg (fun h : vectorGroupScheme K (Module.End K V) ⟶
      vectorGroupScheme K (Matrix j j K) ↦ h.hom.hom) hchange
  have hpoints := congrArg (fun q :
      (Spec (.of R)).asOver (Spec (.of K)) ⟶ (vectorGroupScheme K (Matrix i i K)).X ↦
      q ≫ (endMatrixSchemeBasisChangeIso K V i j b c).hom.hom.hom) hb
  have hpost :
      ((endGroupPointsIso K V).hom.app (CommAlgCat.of K R) (.ofAdd f) ≫
        (endMatrixSchemeIso K V i b).hom.hom.hom) ≫
          (endMatrixSchemeBasisChangeIso K V i j b c).hom.hom.hom =
      (endGroupPointsIso K V).hom.app (CommAlgCat.of K R) (.ofAdd f) ≫
        (endMatrixSchemeIso K V j c).hom.hom.hom := by
    calc
      _ = (endGroupPointsIso K V).hom.app (CommAlgCat.of K R) (.ofAdd f) ≫
          ((endMatrixSchemeIso K V i b).hom.hom.hom ≫
            (endMatrixSchemeBasisChangeIso K V i j b c).hom.hom.hom) :=
        Category.assoc _ _ _
      _ = _ := congrArg (fun q :
          (vectorGroupScheme K (Module.End K V)).X ⟶
            (vectorGroupScheme K (Matrix j j K)).X ↦
          (endGroupPointsIso K V).hom.app (CommAlgCat.of K R) (.ofAdd f) ≫ q)
            hchange'
  exact hpoints.symm.trans (hpost.trans hc)

end MatrixSchemeBasisChange

end AlgebraicGeometry

#lint
