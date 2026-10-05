/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.DiagonalCoordinateRing
public import AlgebraicGroups.GroupScheme.GeneralLinear
public import AlgebraicGroups.GroupScheme.Multiplicative
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The finite-type closed diagonal group scheme of the native general linear group

Milne's diagonal subgroup of `GL_n` over a field is an algebraic subgroup on
all algebras over that field. The Hopf quotient here gives a closed affine
finite-type group scheme over any commutative base. Its group-valued point
identification is natural in test algebras at a **fixed** base, not a base-change
isomorphism.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§2.8–2.9 (pp. 41–42).
* Mathlib, `Mathlib.AlgebraicGeometry.Group.Affine` (`hopfSpec`,
  `Spec.mapMulEquiv`, and `algSpec`) and
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
  (`IsClosedImmersion.spec_of_surjective`).
* `AlgebraicGroups.Algebra.GeneralLinearCoordinateRing` and
  `AlgebraicGroups.GroupScheme.GeneralLinear`, for GL evaluation and the
  represented native matrix group.
-/

@[expose] public section

noncomputable section

open CategoryTheory GeneralLinearCoordinateRing DiagonalCoordinateRing
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]

/-- The affine scheme represented by the off-diagonal Hopf quotient of GL. -/
abbrev diagonalGroupUnderlyingScheme : Over (Spec (.of K)) :=
  (Spec (.of (DiagonalCoordinateRing.CoordinateRing K n))).asOver (Spec (.of K))

instance diagonalGroupUnderlyingScheme_locallyOfFiniteType :
    LocallyOfFiniteType (diagonalGroupUnderlyingScheme K n).hom := by
  change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
    (algebraMap K (DiagonalCoordinateRing.CoordinateRing K n))))
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  change (algebraMap K (DiagonalCoordinateRing.CoordinateRing K n)).FiniteType
  exact RingHom.finiteType_algebraMap.mpr (DiagonalCoordinateRing.finiteType K n)

instance diagonalGroupUnderlyingScheme_quasiCompact :
    QuasiCompact (diagonalGroupUnderlyingScheme K n).hom := by
  change QuasiCompact (Spec.map (CommRingCat.ofHom
    (algebraMap K (DiagonalCoordinateRing.CoordinateRing K n))))
  infer_instance

/-- The affine finite-type diagonal group object over `Spec K`, extending
Milne's field-based algebraic subgroup `D_n` (*Algebraic Groups*, §2.9). -/
abbrev diagonalGroupScheme : Grp (Over (Spec (.of K))) :=
  ⟨diagonalGroupUnderlyingScheme K n⟩

/-- Bialgebra map presenting diagonal matrices as a closed GL subgroup. -/
def diagonalQuotientBialgHom :
    GeneralLinearCoordinateRing.CoordinateRing K n →ₐc[K]
      DiagonalCoordinateRing.CoordinateRing K n :=
  Bialgebra.Quotient.mkBialgHom (ideal K n)

/-- Closed group-scheme inclusion induced by the off-diagonal Hopf quotient;
compare Milne, *Algebraic Groups* (2017), §2.9. -/
def diagonalInclusion : diagonalGroupScheme K n ⟶ generalLinearGroupScheme K n :=
  (hopfSpec (.of K)).map
    (Opposite.op (CommHopfAlgCat.ofHom (diagonalQuotientBialgHom K n)))

theorem diagonalInclusion_left : (diagonalInclusion K n).hom.hom.left =
    Spec.map (CommRingCat.ofHom (quotient K n).toRingHom) := rfl

theorem diagonalInclusion_isClosedImmersion :
    IsClosedImmersion (diagonalInclusion K n).hom.hom.left := by
  rw [diagonalInclusion_left]
  exact IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

variable (R : Type u) [CommRing R] [Algebra K R]

/-- Evaluate a quotient-algebra point as a native invertible diagonal matrix. -/
def diagonalToGL (f : DiagonalCoordinateRing.CoordinateRing K n →ₐ[K] R) :
    Matrix.DiagonalGroup n R :=
  ⟨toGL (f.comp (quotient K n)), by
    intro i j hij
    change f (quotient K n (matrix K n i j)) = 0
    rw [quotient_offDiagonal K n i j hij, map_zero]⟩

@[simp] theorem diagonalToGL_entry
    (f : DiagonalCoordinateRing.CoordinateRing K n →ₐ[K] R) (i j : n) :
    (diagonalToGL K n R f).1 i j = f (quotient K n (matrix K n i j)) := rfl

/-- Descend native diagonal matrix evaluation through the off-diagonal ideal. -/
def diagonalFromGL (s : Matrix.DiagonalGroup n R) :
    DiagonalCoordinateRing.CoordinateRing K n →ₐ[K] R :=
  Ideal.Quotient.liftₐ (ideal K n) (evaluate (K := K) s.1) (by
    intro x hx
    have h : ideal K n ≤ RingHom.ker (evaluate (K := K) s.1).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨⟨i, j⟩, rfl⟩
      apply RingHom.mem_ker.mpr
      by_cases hij : i = j
      · simp [relation, hij]
      · simp only [relation, hij, ite_false]
        change (evaluate (K := K) s.1) (matrix K n i j) = 0
        rw [evaluate_matrix]
        exact s.2 i j hij
    exact RingHom.mem_ker.mp (h hx))

theorem diagonalFromGL_comp_quotient (s : Matrix.DiagonalGroup n R) :
    (diagonalFromGL K n R s).comp (quotient K n) = evaluate (K := K) s.1 :=
  Ideal.Quotient.liftₐ_comp _ _ _

@[simp] theorem diagonalToGL_fromGL (s : Matrix.DiagonalGroup n R) :
    diagonalToGL K n R (diagonalFromGL K n R s) = s := by
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change (diagonalFromGL K n R s) (quotient K n (matrix K n i j)) = s.1 i j
  rw [← AlgHom.comp_apply, diagonalFromGL_comp_quotient, evaluate_matrix]

@[simp] theorem diagonalFromGL_toGL
    (f : DiagonalCoordinateRing.CoordinateRing K n →ₐ[K] R) :
    diagonalFromGL K n R (diagonalToGL K n R f) = f := by
  apply Ideal.Quotient.algHom_ext K
  change (diagonalFromGL K n R (diagonalToGL K n R f)).comp
      (quotient K n) = f.comp (quotient K n)
  rw [diagonalFromGL_comp_quotient]
  exact evaluate_toGL _

/-- Natural multiplicative identification of native diagonal elements and quotient points. -/
def diagonalGroupMulEquivAlgHom :
    Matrix.DiagonalGroup n R ≃*
      WithConv (DiagonalCoordinateRing.CoordinateRing K n →ₐ[K] R) where
  toFun s := WithConv.toConv (diagonalFromGL K n R s)
  invFun φ := diagonalToGL K n R φ.ofConv
  left_inv s := diagonalToGL_fromGL K n R s
  right_inv φ := by
    apply WithConv.ofConv_injective
    exact diagonalFromGL_toGL K n R φ.ofConv
  map_mul' s t := by
    apply WithConv.ofConv_injective
    apply Ideal.Quotient.algHom_ext K
    change (diagonalFromGL K n R (s * t)).comp (quotient K n) =
      ((WithConv.toConv (diagonalFromGL K n R s) *
        WithConv.toConv (diagonalFromGL K n R t)).ofConv).comp
          (diagonalQuotientBialgHom K n).toAlgHom
    rw [AlgHom.convMul_comp_bialgHom_distrib]
    rw [diagonalFromGL_comp_quotient]
    change (generalLinearGroupMulEquivAlgHom K n R (s.1 * t.1)).ofConv =
      (WithConv.toConv ((diagonalFromGL K n R s).comp (quotient K n)) *
        WithConv.toConv ((diagonalFromGL K n R t).comp (quotient K n))).ofConv
    rw [diagonalFromGL_comp_quotient, diagonalFromGL_comp_quotient]
    exact congrArg WithConv.ofConv
      ((generalLinearGroupMulEquivAlgHom K n R).map_mul s.1 t.1)

@[simp] theorem diagonalGroupMulEquivAlgHom_entry
    (s : Matrix.DiagonalGroup n R) (i j : n) :
    (diagonalGroupMulEquivAlgHom K n R s).ofConv
      (quotient K n (matrix K n i j)) = s.1 i j := by
  change (diagonalFromGL K n R s) (quotient K n (matrix K n i j)) = _
  rw [← AlgHom.comp_apply, diagonalFromGL_comp_quotient, evaluate_matrix]

theorem diagonalGroupMulEquivAlgHom_detInverse
    (s : Matrix.DiagonalGroup n R) :
    (diagonalGroupMulEquivAlgHom K n R s).ofConv
      (quotient K n (detInverse K n)) =
        ↑(Matrix.GeneralLinearGroup.det s.1)⁻¹ := by
  change (evaluate (K := K) s.1) (detInverse K n) = _
  exact evaluate_detInverse s.1

/-- The group equivalence with affine scheme-valued points. -/
def diagonalGroupMulEquivPoints :
    Matrix.DiagonalGroup n R ≃*
      ((Spec (.of R)).asOver (Spec (.of K)) ⟶ diagonalGroupUnderlyingScheme K n) :=
  (diagonalGroupMulEquivAlgHom K n R).trans
    (Spec.mapMulEquiv (R := K) (S := DiagonalCoordinateRing.CoordinateRing K n)
      (T := R))

theorem diagonalGroupMulEquivPoints_apply_left (s : Matrix.DiagonalGroup n R) :
    (diagonalGroupMulEquivPoints K n R s).left =
      Spec.map (CommRingCat.ofHom (diagonalFromGL K n R s).toRingHom) := rfl

/-- Inclusion on every test-algebra point is literal native GL inclusion. -/
theorem diagonalInclusion_point (s : Matrix.DiagonalGroup n R) :
    diagonalGroupMulEquivPoints K n R s ≫
      (diagonalInclusion K n).hom.hom =
      generalLinearGroupMulEquivPoints K n R s.1 := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, diagonalGroupMulEquivPoints_apply_left,
    diagonalInclusion_left, generalLinearGroupMulEquivPoints_apply_left]
  change Spec.map (CommRingCat.ofHom (diagonalFromGL K n R s).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (quotient K n).toRingHom) =
    Spec.map (CommRingCat.ofHom (evaluate (K := K) s.1).toRingHom)
  rw [← Spec.map_comp]
  exact congrArg (fun h : GeneralLinearCoordinateRing.CoordinateRing K n →ₐ[K] R =>
    Spec.map (CommRingCat.ofHom h.toRingHom))
      (diagonalFromGL_comp_quotient K n R s)

theorem diagonalToGL_natural {S : Type u} [CommRing S] [Algebra K S]
    (v : R →ₐ[K] S) (f : DiagonalCoordinateRing.CoordinateRing K n →ₐ[K] R) :
    diagonalToGL K n S (v.comp f) =
      Matrix.DiagonalGroup.map v.toRingHom (diagonalToGL K n R f) := by
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rfl

theorem diagonalFromGL_natural {S : Type u} [CommRing S] [Algebra K S]
    (v : R →ₐ[K] S) (s : Matrix.DiagonalGroup n R) :
    diagonalFromGL K n S (Matrix.DiagonalGroup.map v.toRingHom s) =
      v.comp (diagonalFromGL K n R s) := by
  apply Ideal.Quotient.algHom_ext K
  change (diagonalFromGL K n S
    (Matrix.DiagonalGroup.map v.toRingHom s)).comp (quotient K n) =
      (v.comp (diagonalFromGL K n R s)).comp (quotient K n)
  rw [diagonalFromGL_comp_quotient, AlgHom.comp_assoc,
    diagonalFromGL_comp_quotient]
  exact evaluate_natural v s.1

/-- Functorial native diagonal groups on all commutative `K`-algebras. -/
def diagonalGroupFunctor : CommAlgCat K ⥤ GrpCat where
  obj R := GrpCat.of (Matrix.DiagonalGroup n R)
  map f := GrpCat.ofHom (Matrix.DiagonalGroup.map f.hom.toRingHom)
  map_id R := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro s
    apply Subtype.ext
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rfl
  map_comp f g := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro s
    apply Subtype.ext
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rfl

/-- The group-valued points functor of the closed diagonal group scheme. -/
abbrev diagonalGroupPointsFunctor : CommAlgCat K ⥤ GrpCat :=
  (algSpec (.of K)).rightOp ⋙ yonedaGrp.obj (diagonalGroupScheme K n)

/-- Natural group-valued identification on every `K`-algebra at fixed base;
it extends Milne's `D_n` example (*Algebraic Groups*, §2.9). -/
def diagonalGroupPointsIso :
    diagonalGroupFunctor K n ≅ diagonalGroupPointsFunctor K n :=
  NatIso.ofComponents
    (fun R => (diagonalGroupMulEquivPoints K n R).toGrpIso)
    (fun {R S} f => by
      ext s
      apply Over.OverMorphism.ext
      change (diagonalGroupMulEquivPoints K n S
        (Matrix.DiagonalGroup.map f.hom.toRingHom s)).left =
          ((algSpec (.of K)).map f.op).left ≫
            (diagonalGroupMulEquivPoints K n R s).left
      rw [diagonalGroupMulEquivPoints_apply_left]
      change Spec.map (CommRingCat.ofHom
        (diagonalFromGL K n S
          (Matrix.DiagonalGroup.map f.hom.toRingHom s)).toRingHom) =
            Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫
              Spec.map (CommRingCat.ofHom (diagonalFromGL K n R s).toRingHom)
      rw [← Spec.map_comp]
      exact congrArg (fun h : DiagonalCoordinateRing.CoordinateRing K n →ₐ[K] S =>
        Spec.map (CommRingCat.ofHom h.toRingHom))
          (diagonalFromGL_natural K n R f.hom s))

/-- Natural unit-tuple coordinates on every represented diagonal group point. -/
def diagonalGroupUnitsEquivPoints :
    (n → Rˣ) ≃*
      ((Spec (.of R)).asOver (Spec (.of K)) ⟶ diagonalGroupUnderlyingScheme K n) :=
  (Matrix.DiagonalGroup.unitsEquiv : Matrix.DiagonalGroup n R ≃* (n → Rˣ)).symm.trans
    (diagonalGroupMulEquivPoints K n R)

end AlgebraicGeometry
