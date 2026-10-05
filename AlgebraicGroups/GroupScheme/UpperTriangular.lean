/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.UpperTriangularCoordinateRing
public import AlgebraicGroups.GroupScheme.GeneralLinear
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The finite-type upper-triangular subgroup scheme of general linear groups

The below-diagonal relations cut out an invertible upper-triangular subgroup
of GL. Unlike the unitriangular quotient, its diagonal entries remain units,
and its determinant need not be one. The represented group and its pointwise
matrix description hold over any commutative base ring.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§2.8–2.9: the GL functor and the
  upper-triangular subgroup over a field and its commutative algebras.
* Mathlib, `Mathlib.LinearAlgebra.Matrix.Block`: triangular determinants,
  products and inverses; `Mathlib.RingTheory.HopfAlgebra.Quotient`: Hopf ideals
  and their quotients; `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  closed immersions from surjective affine coordinate maps.
* `AlgebraicGroups.Algebra.GeneralLinearCoordinateRing` and
  `AlgebraicGroups.GroupScheme.GeneralLinear`: the localized GL Hopf algebra
  and its represented group and point comparison.
-/

@[expose] public section

noncomputable section

open CategoryTheory GeneralLinearCoordinateRing UpperTriangularCoordinateRing
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [LinearOrder n]

/-- The affine scheme represented by the below-diagonal Hopf quotient of GL. -/
abbrev upperTriangularGroupUnderlyingScheme : Over (Spec (.of K)) :=
  (Spec (.of (UpperTriangularCoordinateRing.CoordinateRing K n))).asOver (Spec (.of K))

instance upperTriangularGroupUnderlyingScheme_locallyOfFiniteType :
    LocallyOfFiniteType (upperTriangularGroupUnderlyingScheme K n).hom := by
  change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
    (algebraMap K (UpperTriangularCoordinateRing.CoordinateRing K n))))
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  change (algebraMap K (UpperTriangularCoordinateRing.CoordinateRing K n)).FiniteType
  exact RingHom.finiteType_algebraMap.mpr (UpperTriangularCoordinateRing.finiteType K n)

instance upperTriangularGroupUnderlyingScheme_quasiCompact :
    QuasiCompact (upperTriangularGroupUnderlyingScheme K n).hom := by
  change QuasiCompact (Spec.map (CommRingCat.ofHom
    (algebraMap K (UpperTriangularCoordinateRing.CoordinateRing K n))))
  infer_instance

/-- The affine finite-type group object of upper-triangular invertible matrices
over a commutative ring. Over a field and `Fin n`, its points recover the
upper-triangular subgroup of Milne, *Algebraic Groups* (2017), §2.9. -/
abbrev upperTriangularGroupScheme : Grp (Over (Spec (.of K))) :=
  ⟨upperTriangularGroupUnderlyingScheme K n⟩

/-- The bialgebra map presenting the upper-triangular group as a GL subgroup. -/
def upperTriangularQuotientBialgHom :
    GeneralLinearCoordinateRing.CoordinateRing K n →ₐc[K]
      UpperTriangularCoordinateRing.CoordinateRing K n :=
  Bialgebra.Quotient.mkBialgHom (ideal K n)

/-- The closed group-scheme inclusion induced by the Hopf quotient. -/
def upperTriangularInclusion :
    upperTriangularGroupScheme K n ⟶ generalLinearGroupScheme K n :=
  (hopfSpec (.of K)).map
    (Opposite.op (CommHopfAlgCat.ofHom (upperTriangularQuotientBialgHom K n)))

theorem upperTriangularInclusion_left : (upperTriangularInclusion K n).hom.hom.left =
    Spec.map (CommRingCat.ofHom (quotient K n).toRingHom) := rfl

/-- The upper-triangular quotient defines a closed subgroup of GL over any
commutative base ring. For the field-base subgroup compare Milne,
*Algebraic Groups* (2017), §2.9; the scheme-level proof uses Mathlib's
`IsClosedImmersion.spec_of_surjective` on the coordinate quotient. -/
theorem upperTriangularInclusion_isClosedImmersion :
    IsClosedImmersion (upperTriangularInclusion K n).hom.hom.left := by
  rw [upperTriangularInclusion_left]
  exact IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

variable (R : Type u) [CommRing R] [Algebra K R]

/-- Evaluate a quotient-algebra point as an invertible upper-triangular matrix. -/
def upperTriangularToGL (f : UpperTriangularCoordinateRing.CoordinateRing K n →ₐ[K] R) :
    Matrix.UpperTriangularGroup n R :=
  ⟨toGL (f.comp (quotient K n)), by
    intro i j hji
    change f (quotient K n (matrix K n i j)) = 0
    rw [quotient_lower K n i j hji, map_zero]⟩

@[simp] theorem upperTriangularToGL_entry
    (f : UpperTriangularCoordinateRing.CoordinateRing K n →ₐ[K] R) (i j : n) :
    (upperTriangularToGL K n R f).1 i j = f (quotient K n (matrix K n i j)) := rfl

/-- Descend native upper-triangular matrix evaluation through the ideal. -/
def upperTriangularFromGL (s : Matrix.UpperTriangularGroup n R) :
    UpperTriangularCoordinateRing.CoordinateRing K n →ₐ[K] R :=
  Ideal.Quotient.liftₐ (ideal K n) (evaluate (K := K) s.1) (by
    intro x hx
    have h : ideal K n ≤ RingHom.ker (evaluate (K := K) s.1).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨⟨i, j⟩, rfl⟩
      apply RingHom.mem_ker.mpr
      by_cases hji : j < i
      · simp only [relation, hji, ↓reduceIte]
        change (evaluate (K := K) s.1) (matrix K n i j) = 0
        rw [evaluate_matrix]
        exact s.2 hji
      · simp [relation, hji]
    exact RingHom.mem_ker.mp (h hx))

theorem upperTriangularFromGL_comp_quotient (s : Matrix.UpperTriangularGroup n R) :
    (upperTriangularFromGL K n R s).comp (quotient K n) = evaluate (K := K) s.1 :=
  Ideal.Quotient.liftₐ_comp _ _ _

@[simp] theorem upperTriangularToGL_fromGL (s : Matrix.UpperTriangularGroup n R) :
    upperTriangularToGL K n R (upperTriangularFromGL K n R s) = s := by
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change (upperTriangularFromGL K n R s) (quotient K n (matrix K n i j)) = s.1 i j
  rw [← AlgHom.comp_apply, upperTriangularFromGL_comp_quotient, evaluate_matrix]

@[simp] theorem upperTriangularFromGL_toGL
    (f : UpperTriangularCoordinateRing.CoordinateRing K n →ₐ[K] R) :
    upperTriangularFromGL K n R (upperTriangularToGL K n R f) = f := by
  apply Ideal.Quotient.algHom_ext K
  change (upperTriangularFromGL K n R (upperTriangularToGL K n R f)).comp
      (quotient K n) = f.comp (quotient K n)
  rw [upperTriangularFromGL_comp_quotient]
  exact evaluate_toGL _

/-- A multiplicative equivalence of native upper-triangular elements and algebra points. -/
def upperTriangularGroupMulEquivAlgHom :
    Matrix.UpperTriangularGroup n R ≃*
      WithConv (UpperTriangularCoordinateRing.CoordinateRing K n →ₐ[K] R) where
  toFun s := WithConv.toConv (upperTriangularFromGL K n R s)
  invFun φ := upperTriangularToGL K n R φ.ofConv
  left_inv s := upperTriangularToGL_fromGL K n R s
  right_inv φ := by
    apply WithConv.ofConv_injective
    exact upperTriangularFromGL_toGL K n R φ.ofConv
  map_mul' s t := by
    apply WithConv.ofConv_injective
    apply Ideal.Quotient.algHom_ext K
    change (upperTriangularFromGL K n R (s * t)).comp (quotient K n) =
      ((WithConv.toConv (upperTriangularFromGL K n R s) *
        WithConv.toConv (upperTriangularFromGL K n R t)).ofConv).comp
          (upperTriangularQuotientBialgHom K n).toAlgHom
    rw [AlgHom.convMul_comp_bialgHom_distrib]
    rw [upperTriangularFromGL_comp_quotient]
    change (generalLinearGroupMulEquivAlgHom K n R (s.1 * t.1)).ofConv =
      (WithConv.toConv ((upperTriangularFromGL K n R s).comp (quotient K n)) *
        WithConv.toConv ((upperTriangularFromGL K n R t).comp (quotient K n))).ofConv
    rw [upperTriangularFromGL_comp_quotient, upperTriangularFromGL_comp_quotient]
    exact congrArg WithConv.ofConv
      ((generalLinearGroupMulEquivAlgHom K n R).map_mul s.1 t.1)

@[simp] theorem upperTriangularGroupMulEquivAlgHom_entry
    (s : Matrix.UpperTriangularGroup n R) (i j : n) :
    (upperTriangularGroupMulEquivAlgHom K n R s).ofConv
      (quotient K n (matrix K n i j)) = s.1 i j := by
  change (upperTriangularFromGL K n R s) (quotient K n (matrix K n i j)) = _
  rw [← AlgHom.comp_apply, upperTriangularFromGL_comp_quotient, evaluate_matrix]

theorem upperTriangularGroupMulEquivAlgHom_detInverse
    (s : Matrix.UpperTriangularGroup n R) :
    (upperTriangularGroupMulEquivAlgHom K n R s).ofConv
      (quotient K n (detInverse K n)) =
        ↑(Matrix.GeneralLinearGroup.det s.1)⁻¹ := by
  change (evaluate (K := K) s.1) (detInverse K n) = _
  exact evaluate_detInverse s.1

/-- Multiplicative classification of affine scheme-valued points over any
commutative `K`-algebra; compare the field-base functor in Milne,
*Algebraic Groups* (2017), §§2.8–2.9. -/
def upperTriangularGroupMulEquivPoints :
    Matrix.UpperTriangularGroup n R ≃*
      ((Spec (.of R)).asOver (Spec (.of K)) ⟶ upperTriangularGroupUnderlyingScheme K n) :=
  (upperTriangularGroupMulEquivAlgHom K n R).trans
    (Spec.mapMulEquiv (R := K) (S := UpperTriangularCoordinateRing.CoordinateRing K n)
      (T := R))

theorem upperTriangularGroupMulEquivPoints_apply_left
    (s : Matrix.UpperTriangularGroup n R) :
    (upperTriangularGroupMulEquivPoints K n R s).left =
      Spec.map (CommRingCat.ofHom (upperTriangularFromGL K n R s).toRingHom) := rfl

/-- Every test-algebra point of the subgroup includes as the native GL point. -/
theorem upperTriangularInclusion_point (s : Matrix.UpperTriangularGroup n R) :
    upperTriangularGroupMulEquivPoints K n R s ≫
      (upperTriangularInclusion K n).hom.hom =
      generalLinearGroupMulEquivPoints K n R s.1 := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, upperTriangularGroupMulEquivPoints_apply_left,
    upperTriangularInclusion_left, generalLinearGroupMulEquivPoints_apply_left]
  change Spec.map (CommRingCat.ofHom (upperTriangularFromGL K n R s).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (quotient K n).toRingHom) =
    Spec.map (CommRingCat.ofHom (evaluate (K := K) s.1).toRingHom)
  rw [← Spec.map_comp]
  exact congrArg (fun h : GeneralLinearCoordinateRing.CoordinateRing K n →ₐ[K] R =>
    Spec.map (CommRingCat.ofHom h.toRingHom))
      (upperTriangularFromGL_comp_quotient K n R s)

theorem upperTriangularToGL_natural {S : Type u} [CommRing S] [Algebra K S]
    (v : R →ₐ[K] S) (f : UpperTriangularCoordinateRing.CoordinateRing K n →ₐ[K] R) :
    upperTriangularToGL K n S (v.comp f) =
      Matrix.UpperTriangularGroup.map v.toRingHom (upperTriangularToGL K n R f) := by
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rfl

theorem upperTriangularFromGL_natural {S : Type u} [CommRing S] [Algebra K S]
    (v : R →ₐ[K] S) (s : Matrix.UpperTriangularGroup n R) :
    upperTriangularFromGL K n S (Matrix.UpperTriangularGroup.map v.toRingHom s) =
      v.comp (upperTriangularFromGL K n R s) := by
  apply Ideal.Quotient.algHom_ext K
  change (upperTriangularFromGL K n S
    (Matrix.UpperTriangularGroup.map v.toRingHom s)).comp (quotient K n) =
      (v.comp (upperTriangularFromGL K n R s)).comp (quotient K n)
  rw [upperTriangularFromGL_comp_quotient, AlgHom.comp_assoc,
    upperTriangularFromGL_comp_quotient]
  exact evaluate_natural v s.1

/-- Native upper-triangular groups on all commutative `K`-algebras. -/
def upperTriangularGroupFunctor : CommAlgCat K ⥤ GrpCat where
  obj R := GrpCat.of (Matrix.UpperTriangularGroup n R)
  map f := GrpCat.ofHom (Matrix.UpperTriangularGroup.map f.hom.toRingHom)
  map_id R := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro s
    exact Matrix.UpperTriangularGroup.map_id s
  map_comp f g := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro s
    exact (Matrix.UpperTriangularGroup.map_comp f.hom.toRingHom g.hom.toRingHom s).symm

/-- The represented group-valued point functor on commutative `K`-algebras. -/
abbrev upperTriangularGroupPointsFunctor : CommAlgCat K ⥤ GrpCat :=
  (algSpec (.of K)).rightOp ⋙ yonedaGrp.obj (upperTriangularGroupScheme K n)

/-- Multiplicative natural isomorphism on all `K`-algebras and their maps,
extending the field-base functor in Milne, *Algebraic Groups* (2017),
§§2.8–2.9. -/
def upperTriangularGroupPointsIso :
    upperTriangularGroupFunctor K n ≅ upperTriangularGroupPointsFunctor K n :=
  NatIso.ofComponents
    (fun R => (upperTriangularGroupMulEquivPoints K n R).toGrpIso)
    (fun {R S} f => by
      ext s
      apply Over.OverMorphism.ext
      change (upperTriangularGroupMulEquivPoints K n S
        (Matrix.UpperTriangularGroup.map f.hom.toRingHom s)).left =
          ((algSpec (.of K)).map f.op).left ≫
            (upperTriangularGroupMulEquivPoints K n R s).left
      rw [upperTriangularGroupMulEquivPoints_apply_left]
      change Spec.map (CommRingCat.ofHom
        (upperTriangularFromGL K n S
          (Matrix.UpperTriangularGroup.map f.hom.toRingHom s)).toRingHom) =
            Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫
              Spec.map (CommRingCat.ofHom (upperTriangularFromGL K n R s).toRingHom)
      rw [← Spec.map_comp]
      exact congrArg
        (fun h : UpperTriangularCoordinateRing.CoordinateRing K n →ₐ[K] S =>
          Spec.map (CommRingCat.ofHom h.toRingHom))
          (upperTriangularFromGL_natural K n R f.hom s))

end AlgebraicGeometry
