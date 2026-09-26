/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.SpecialLinearCoordinateRing
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The finite special linear group scheme

The determinant-one Hopf quotient represents the native matrix special linear group
over arbitrary coefficient algebras. Its inclusion into the finite general linear
group scheme is a closed immersion.
-/

@[expose] public section

noncomputable section

open CategoryTheory GeneralLinearCoordinateRing SpecialLinearCoordinateRing
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]

/-- The affine scheme of the determinant-one Hopf quotient over `Spec K`. -/
abbrev specialLinearGroupUnderlyingScheme : Over (Spec (.of K)) :=
  (Spec (.of (SpecialLinearCoordinateRing.CoordinateRing K n))).asOver (Spec (.of K))

/-- The group object carried by the determinant-one Hopf quotient. -/
abbrev specialLinearGroupScheme : Grp (Over (Spec (.of K))) :=
  ⟨specialLinearGroupUnderlyingScheme K n⟩

/-- The quotient map as a morphism of the actual GL and SL bialgebras. -/
def specialLinearQuotientBialgHom :
    GeneralLinearCoordinateRing.CoordinateRing K n →ₐc[K]
      SpecialLinearCoordinateRing.CoordinateRing K n :=
  Bialgebra.Quotient.mkBialgHom (determinantOneIdeal K n)

/-- The native group-scheme inclusion induced by the determinant-one Hopf quotient. -/
def specialLinearInclusion : specialLinearGroupScheme K n ⟶ generalLinearGroupScheme K n :=
  (hopfSpec (.of K)).map
    (Opposite.op (CommHopfAlgCat.ofHom (specialLinearQuotientBialgHom K n)))

theorem specialLinearInclusion_left : (specialLinearInclusion K n).hom.hom.left =
    Spec.map (CommRingCat.ofHom (quotient K n).toRingHom) := rfl

/-- The inclusion is scheme-theoretically closed, including over zero rings. -/
theorem specialLinearInclusion_isClosedImmersion :
    IsClosedImmersion (specialLinearInclusion K n).hom.hom.left := by
  rw [specialLinearInclusion_left]
  exact IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

variable (R : Type u) [CommRing R] [Algebra K R]

/-- Read a point of the determinant-one quotient as a native SL matrix. -/
def specialLinearToSL (f : SpecialLinearCoordinateRing.CoordinateRing K n →ₐ[K] R) :
    Matrix.SpecialLinearGroup n R :=
  ⟨(toGL (f.comp (quotient K n)) : Matrix n n R), by
    calc
      (toGL (f.comp (quotient K n)) : Matrix n n R).det =
          (f.comp (quotient K n)) (matrix K n).det := by
            rw [AlgHom.map_det]
            congr 1
      _ = 1 := by rw [AlgHom.comp_apply, quotient_det, map_one]⟩

/-- The inclusion on quotient points is exactly native `SpecialLinearGroup.toGL`. -/
theorem specialLinearToSL_toGL
    (f : SpecialLinearCoordinateRing.CoordinateRing K n →ₐ[K] R) :
    Matrix.SpecialLinearGroup.toGL (specialLinearToSL K n R f) =
      toGL (f.comp (quotient K n)) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rfl

/-- Native SL matrices evaluate the universal GL matrix through the Hopf quotient. -/
def specialLinearFromSL (s : Matrix.SpecialLinearGroup n R) :
    SpecialLinearCoordinateRing.CoordinateRing K n →ₐ[K] R :=
  Ideal.Quotient.liftₐ (determinantOneIdeal K n)
    (evaluate (K := K) (Matrix.SpecialLinearGroup.toGL s)) (by
      intro element membership
      obtain ⟨multiplier, hmultiplier⟩ := Ideal.mem_span_singleton'.mp membership
      rw [← hmultiplier, map_mul, map_sub, map_one, evaluate_det]
      have hdet : (Matrix.SpecialLinearGroup.toGL s : Matrix n n R).det = 1 :=
        s.property
      rw [hdet, sub_self, mul_zero])

theorem specialLinearFromSL_comp_quotient (s : Matrix.SpecialLinearGroup n R) :
    (specialLinearFromSL K n R s).comp (quotient K n) =
      evaluate (K := K) (Matrix.SpecialLinearGroup.toGL s) := by
  exact Ideal.Quotient.liftₐ_comp _ _ _

theorem specialLinearToSL_fromSL (s : Matrix.SpecialLinearGroup n R) :
    specialLinearToSL K n R (specialLinearFromSL K n R s) = s := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [specialLinearToSL_toGL, specialLinearFromSL_comp_quotient, toGL_evaluate]

theorem specialLinearFromSL_toSL
    (f : SpecialLinearCoordinateRing.CoordinateRing K n →ₐ[K] R) :
    specialLinearFromSL K n R (specialLinearToSL K n R f) = f := by
  apply Ideal.Quotient.algHom_ext K
  change (specialLinearFromSL K n R (specialLinearToSL K n R f)).comp
      (quotient K n) = f.comp (quotient K n)
  rw [specialLinearFromSL_comp_quotient, specialLinearToSL_toGL, evaluate_toGL]

/-- All coefficient-algebra points are naturally the native special linear group,
with group multiplication given by the actual quotient convolution. -/
def specialLinearGroupMulEquivAlgHom :
    Matrix.SpecialLinearGroup n R ≃*
      WithConv (SpecialLinearCoordinateRing.CoordinateRing K n →ₐ[K] R) where
  toFun s := WithConv.toConv (specialLinearFromSL K n R s)
  invFun φ := specialLinearToSL K n R φ.ofConv
  left_inv s := specialLinearToSL_fromSL K n R s
  right_inv φ := by
    apply WithConv.ofConv_injective
    exact specialLinearFromSL_toSL K n R φ.ofConv
  map_mul' s t := by
    apply WithConv.ofConv_injective
    apply Ideal.Quotient.algHom_ext K
    change (specialLinearFromSL K n R (s * t)).comp (quotient K n) =
      ((WithConv.toConv (specialLinearFromSL K n R s) *
        WithConv.toConv (specialLinearFromSL K n R t)).ofConv).comp
          (specialLinearQuotientBialgHom K n).toAlgHom
    rw [AlgHom.convMul_comp_bialgHom_distrib]
    rw [specialLinearFromSL_comp_quotient]
    change (generalLinearGroupMulEquivAlgHom K n R
        (Matrix.SpecialLinearGroup.toGL (s * t))).ofConv =
      (WithConv.toConv ((specialLinearFromSL K n R s).comp (quotient K n)) *
        WithConv.toConv ((specialLinearFromSL K n R t).comp (quotient K n))).ofConv
    rw [specialLinearFromSL_comp_quotient, specialLinearFromSL_comp_quotient]
    exact congrArg WithConv.ofConv
      ((generalLinearGroupMulEquivAlgHom K n R).map_mul
        (Matrix.SpecialLinearGroup.toGL s) (Matrix.SpecialLinearGroup.toGL t))

/-- Entry readback for the native SL matrix. -/
theorem specialLinearGroupMulEquivAlgHom_entry
    (s : Matrix.SpecialLinearGroup n R) (i j : n) :
    (specialLinearGroupMulEquivAlgHom K n R s).ofConv (entry K n i j) = s i j := by
  change (specialLinearFromSL K n R s) (quotient K n (matrix K n i j)) = s i j
  rw [← AlgHom.comp_apply, specialLinearFromSL_comp_quotient, evaluate_matrix]
  rfl

/-- Inverse determinant evaluates to one on every SL point. -/
theorem specialLinearGroupMulEquivAlgHom_detInverse
    (s : Matrix.SpecialLinearGroup n R) :
    (specialLinearGroupMulEquivAlgHom K n R s).ofConv
      (quotient K n (detInverse K n)) = 1 := by
  rw [quotient_detInverse, map_one]

/-- The corresponding affine `Spec` point, preserving group multiplication. -/
def specialLinearGroupMulEquivPoints :
    Matrix.SpecialLinearGroup n R ≃*
      ((Spec (.of R)).asOver (Spec (.of K)) ⟶ specialLinearGroupUnderlyingScheme K n) :=
  (specialLinearGroupMulEquivAlgHom K n R).trans
    (Spec.mapMulEquiv (R := K) (S := SpecialLinearCoordinateRing.CoordinateRing K n)
      (T := R))

theorem specialLinearGroupMulEquivPoints_apply_left
    (s : Matrix.SpecialLinearGroup n R) :
    (specialLinearGroupMulEquivPoints K n R s).left =
      Spec.map (CommRingCat.ofHom (specialLinearFromSL K n R s).toRingHom) := rfl

/-- The universal SL entry pulls back to the corresponding native matrix entry. -/
theorem specialLinearGroupPoint_preimage_entry
    (s : Matrix.SpecialLinearGroup n R) (i j : n) :
    (Spec.preimage (specialLinearGroupMulEquivPoints K n R s).left).hom
      (entry K n i j) = s i j := by
  rw [specialLinearGroupMulEquivPoints_apply_left, Spec.preimage_map]
  exact specialLinearGroupMulEquivAlgHom_entry K n R s i j

theorem specialLinearGroupPoint_preimage_detInverse
    (s : Matrix.SpecialLinearGroup n R) :
    (Spec.preimage (specialLinearGroupMulEquivPoints K n R s).left).hom
      (quotient K n (detInverse K n)) = 1 := by
  rw [specialLinearGroupMulEquivPoints_apply_left, Spec.preimage_map]
  exact specialLinearGroupMulEquivAlgHom_detInverse K n R s

/-- The actual inclusion of SL affine points is the native `toGL` embedding. -/
theorem specialLinearInclusion_point (s : Matrix.SpecialLinearGroup n R) :
    specialLinearGroupMulEquivPoints K n R s ≫ (specialLinearInclusion K n).hom.hom =
      generalLinearGroupMulEquivPoints K n R (Matrix.SpecialLinearGroup.toGL s) := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, specialLinearGroupMulEquivPoints_apply_left,
    specialLinearInclusion_left, generalLinearGroupMulEquivPoints_apply_left]
  change Spec.map (CommRingCat.ofHom (specialLinearFromSL K n R s).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (quotient K n).toRingHom) =
    Spec.map (CommRingCat.ofHom
      (evaluate (K := K) (Matrix.SpecialLinearGroup.toGL s)).toRingHom)
  rw [← Spec.map_comp]
  exact congrArg (fun hom : GeneralLinearCoordinateRing.CoordinateRing K n →ₐ[K] R ↦
    Spec.map (CommRingCat.ofHom hom.toRingHom))
      (specialLinearFromSL_comp_quotient K n R s)

/-- Coefficient change commutes with the native determinant-one comparison. -/
theorem specialLinearToSL_natural {S : Type u} [CommRing S] [Algebra K S]
    (v : R →ₐ[K] S) (f : SpecialLinearCoordinateRing.CoordinateRing K n →ₐ[K] R) :
    specialLinearToSL K n S (v.comp f) =
      Matrix.SpecialLinearGroup.map v.toRingHom (specialLinearToSL K n R f) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rfl

theorem specialLinearFromSL_natural {S : Type u} [CommRing S] [Algebra K S]
    (v : R →ₐ[K] S) (s : Matrix.SpecialLinearGroup n R) :
    specialLinearFromSL K n S (Matrix.SpecialLinearGroup.map v.toRingHom s) =
      v.comp (specialLinearFromSL K n R s) := by
  apply Ideal.Quotient.algHom_ext K
  change (specialLinearFromSL K n S
    (Matrix.SpecialLinearGroup.map v.toRingHom s)).comp (quotient K n) =
      (v.comp (specialLinearFromSL K n R s)).comp (quotient K n)
  rw [specialLinearFromSL_comp_quotient, AlgHom.comp_assoc,
    specialLinearFromSL_comp_quotient]
  have h : Matrix.SpecialLinearGroup.toGL
        (Matrix.SpecialLinearGroup.map v.toRingHom s) =
      Matrix.GeneralLinearGroup.map v.toRingHom
        (Matrix.SpecialLinearGroup.toGL s) := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rfl
  rw [h]
  exact evaluate_natural v (Matrix.SpecialLinearGroup.toGL s)

/-- Native matrix SL as a functor on arbitrary commutative `K`-algebras. -/
def specialLinearGroupFunctor : CommAlgCat K ⥤ GrpCat where
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

/-- Group-valued affine functor of points of the determinant-one group scheme. -/
abbrev specialLinearGroupPointsFunctor : CommAlgCat K ⥤ GrpCat :=
  (algSpec (.of K)).rightOp ⋙ yonedaGrp.obj (specialLinearGroupScheme K n)

/-- The native finite special linear group is its represented functor of points. -/
def specialLinearGroupPointsIso :
    specialLinearGroupFunctor K n ≅ specialLinearGroupPointsFunctor K n :=
  NatIso.ofComponents
    (fun R ↦ (specialLinearGroupMulEquivPoints K n R).toGrpIso)
    (fun {R S} f ↦ by
      ext s
      apply Over.OverMorphism.ext
      change
        (specialLinearGroupMulEquivPoints K n S
          (Matrix.SpecialLinearGroup.map f.hom.toRingHom s)).left =
            ((algSpec (.of K)).map f.op).left ≫
              (specialLinearGroupMulEquivPoints K n R s).left
      rw [specialLinearGroupMulEquivPoints_apply_left]
      change Spec.map (CommRingCat.ofHom
        (specialLinearFromSL K n S
          (Matrix.SpecialLinearGroup.map f.hom.toRingHom s)).toRingHom) =
          Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫
            Spec.map (CommRingCat.ofHom (specialLinearFromSL K n R s).toRingHom)
      rw [← Spec.map_comp]
      exact congrArg (fun h : SpecialLinearCoordinateRing.CoordinateRing K n →ₐ[K] S ↦
        Spec.map (CommRingCat.ofHom h.toRingHom))
          (specialLinearFromSL_natural K n R f.hom s))

end AlgebraicGeometry

#lint
