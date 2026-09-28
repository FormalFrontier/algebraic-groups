/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.UnitriangularCoordinateRing
public import AlgebraicGroups.GroupScheme.GeneralLinear
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Upper-unitriangular group schemes

The universal group is the subgroup of the native matrix general linear group
with zeros below the diagonal and units on the diagonal. Its affine group
scheme is represented by the upper-unitriangular Hopf quotient.
-/

@[expose] public section

noncomputable section

open CategoryTheory GeneralLinearCoordinateRing UnitriangularCoordinateRing
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace Matrix

variable (n : Type u) [Fintype n] [LinearOrder n] (R : Type u) [CommRing R]

set_option linter.style.haveILetI false in
/-- Upper-unitriangular elements of the native matrix general linear group. -/
def unitriangularSubgroup : Subgroup (Matrix.GeneralLinearGroup n R) where
  carrier := {g | ((g : Matrix n n R).IsUpperTriangular) ∧ ∀ i, g i i = 1}
  one_mem' := by
    refine ⟨Matrix.blockTriangular_one, ?_⟩
    intro i
    simp
  mul_mem' := by
    intro a b ha hb
    refine ⟨ha.1.mul hb.1, ?_⟩
    intro i
    change ((a : Matrix n n R) * (b : Matrix n n R)) i i = 1
    rw [UnitriangularCoordinateRing.upper_mul_diag ha.1 hb.1, ha.2, hb.2, one_mul]
  inv_mem' := by
    intro g hg
    haveI : Invertible (g : Matrix n n R) := Units.invertible g
    have hinv : ((g⁻¹ : Matrix.GeneralLinearGroup n R) : Matrix n n R).IsUpperTriangular := by
      simpa only [Matrix.GeneralLinearGroup.coe_inv] using
        Matrix.blockTriangular_inv_of_blockTriangular hg.1
    refine ⟨hinv, ?_⟩
    intro i
    have hdiag := UnitriangularCoordinateRing.upper_mul_diag hg.1 hinv i
    have hm := congrArg (fun h : Matrix.GeneralLinearGroup n R =>
      (h : Matrix n n R) i i) (mul_inv_cancel g)
    simpa only [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_one,
      Matrix.one_apply, ite_true, hg.2, one_mul] using hdiag.symm.trans hm

/-- The group of upper-unitriangular native matrix units. -/
abbrev UnitriangularGroup := unitriangularSubgroup n R

namespace UnitriangularGroup

variable {n : Type u} [Fintype n] [LinearOrder n]
variable {R S : Type u} [CommRing R] [CommRing S]

/-- Entry-wise coefficient change, using native `GL.map`. -/
def map (f : R →+* S) : UnitriangularGroup n R →* UnitriangularGroup n S :=
  { toFun := fun g => ⟨Matrix.GeneralLinearGroup.map f g.1, by
      refine ⟨g.2.1.map f, ?_⟩
      intro i
      simp only [Matrix.GeneralLinearGroup.map_apply, g.2.2, map_one]⟩
    map_one' := by
      apply Subtype.ext
      exact (Matrix.GeneralLinearGroup.map f).map_one
    map_mul' := by
      intro a b
      apply Subtype.ext
      exact (Matrix.GeneralLinearGroup.map f).map_mul a.1 b.1 }

@[simp] theorem map_apply (f : R →+* S) (g : UnitriangularGroup n R) (i j : n) :
    (map f g : Matrix.GeneralLinearGroup n S) i j = f (g.1 i j) := by
  exact Matrix.GeneralLinearGroup.map_apply f i j g.1

end UnitriangularGroup

end Matrix

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [LinearOrder n]

/-- The affine scheme over `Spec K` represented by the Hopf quotient. -/
abbrev unitriangularGroupUnderlyingScheme : Over (Spec (.of K)) :=
  (Spec (.of (UnitriangularCoordinateRing.CoordinateRing K n))).asOver (Spec (.of K))

instance unitriangularGroupUnderlyingScheme_locallyOfFiniteType :
    LocallyOfFiniteType (unitriangularGroupUnderlyingScheme K n).hom := by
  change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
    (algebraMap K (UnitriangularCoordinateRing.CoordinateRing K n))))
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  change (algebraMap K (UnitriangularCoordinateRing.CoordinateRing K n)).FiniteType
  exact RingHom.finiteType_algebraMap.mpr (UnitriangularCoordinateRing.finiteType K n)

instance unitriangularGroupUnderlyingScheme_quasiCompact :
    QuasiCompact (unitriangularGroupUnderlyingScheme K n).hom := by
  change QuasiCompact (Spec.map (CommRingCat.ofHom
    (algebraMap K (UnitriangularCoordinateRing.CoordinateRing K n))))
  infer_instance

/-- The finite-type affine group scheme of upper-unitriangular matrices. -/
abbrev unitriangularGroupScheme : Grp (Over (Spec (.of K))) :=
  ⟨unitriangularGroupUnderlyingScheme K n⟩

/-- Bialgebra quotient induced by the defining Hopf ideal. -/
def unitriangularQuotientBialgHom :
    GeneralLinearCoordinateRing.CoordinateRing K n →ₐc[K]
      UnitriangularCoordinateRing.CoordinateRing K n :=
  Bialgebra.Quotient.mkBialgHom (ideal K n)

/-- The closed group-scheme inclusion in `GL`. -/
def unitriangularInclusion : unitriangularGroupScheme K n ⟶ generalLinearGroupScheme K n :=
  (hopfSpec (.of K)).map
    (Opposite.op (CommHopfAlgCat.ofHom (unitriangularQuotientBialgHom K n)))

theorem unitriangularInclusion_left : (unitriangularInclusion K n).hom.hom.left =
    Spec.map (CommRingCat.ofHom (quotient K n).toRingHom) := rfl

theorem unitriangularInclusion_isClosedImmersion :
    IsClosedImmersion (unitriangularInclusion K n).hom.hom.left := by
  rw [unitriangularInclusion_left]
  exact IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

variable (R : Type u) [CommRing R] [Algebra K R]

/-- Evaluate a point of the Hopf quotient as an upper-unitriangular native unit. -/
def unitriangularToGL
    (f : UnitriangularCoordinateRing.CoordinateRing K n →ₐ[K] R) :
    Matrix.UnitriangularGroup n R :=
  ⟨toGL (f.comp (quotient K n)), by
    refine ⟨?_, ?_⟩
    · intro i j hji
      change f (quotient K n (matrix K n i j)) = 0
      rw [quotient_lower K n i j hji, map_zero]
    · intro i
      change f (quotient K n (matrix K n i i)) = 1
      rw [quotient_diag, map_one]⟩

@[simp] theorem unitriangularToGL_entry
    (f : UnitriangularCoordinateRing.CoordinateRing K n →ₐ[K] R) (i j : n) :
    (unitriangularToGL K n R f).1 i j = f (quotient K n (matrix K n i j)) := rfl

/-- Evaluate a native unit on GL coordinates and descend through the relations. -/
def unitriangularFromGL (s : Matrix.UnitriangularGroup n R) :
    UnitriangularCoordinateRing.CoordinateRing K n →ₐ[K] R :=
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
        exact s.2.1 hji
      · by_cases hij : i = j
        · subst j
          simp only [relation, lt_irrefl, ite_false, ite_true]
          change (evaluate (K := K) s.1) (matrix K n i i - 1) = 0
          rw [map_sub, map_one, evaluate_matrix, s.2.2, sub_self]
        · simp [relation, hji, hij]
    exact RingHom.mem_ker.mp (h hx))

theorem unitriangularFromGL_comp_quotient (s : Matrix.UnitriangularGroup n R) :
    (unitriangularFromGL K n R s).comp (quotient K n) = evaluate (K := K) s.1 :=
  Ideal.Quotient.liftₐ_comp _ _ _

@[simp] theorem unitriangularToGL_fromGL (s : Matrix.UnitriangularGroup n R) :
    unitriangularToGL K n R (unitriangularFromGL K n R s) = s := by
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change (unitriangularFromGL K n R s) (quotient K n (matrix K n i j)) = s.1 i j
  rw [← AlgHom.comp_apply, unitriangularFromGL_comp_quotient, evaluate_matrix]

@[simp] theorem unitriangularFromGL_toGL
    (f : UnitriangularCoordinateRing.CoordinateRing K n →ₐ[K] R) :
    unitriangularFromGL K n R (unitriangularToGL K n R f) = f := by
  apply Ideal.Quotient.algHom_ext K
  change (unitriangularFromGL K n R (unitriangularToGL K n R f)).comp
      (quotient K n) = f.comp (quotient K n)
  rw [unitriangularFromGL_comp_quotient]
  exact evaluate_toGL _

/-- Every commutative `K`-algebra has a natural multiplicative identification
between quotient points and the native upper-unitriangular subgroup. -/
def unitriangularGroupMulEquivAlgHom :
    Matrix.UnitriangularGroup n R ≃*
      WithConv (UnitriangularCoordinateRing.CoordinateRing K n →ₐ[K] R) where
  toFun s := WithConv.toConv (unitriangularFromGL K n R s)
  invFun φ := unitriangularToGL K n R φ.ofConv
  left_inv s := unitriangularToGL_fromGL K n R s
  right_inv φ := by
    apply WithConv.ofConv_injective
    exact unitriangularFromGL_toGL K n R φ.ofConv
  map_mul' s t := by
    apply WithConv.ofConv_injective
    apply Ideal.Quotient.algHom_ext K
    change (unitriangularFromGL K n R (s * t)).comp (quotient K n) =
      ((WithConv.toConv (unitriangularFromGL K n R s) *
        WithConv.toConv (unitriangularFromGL K n R t)).ofConv).comp
          (unitriangularQuotientBialgHom K n).toAlgHom
    rw [AlgHom.convMul_comp_bialgHom_distrib]
    rw [unitriangularFromGL_comp_quotient]
    change (generalLinearGroupMulEquivAlgHom K n R (s.1 * t.1)).ofConv =
      (WithConv.toConv ((unitriangularFromGL K n R s).comp (quotient K n)) *
        WithConv.toConv ((unitriangularFromGL K n R t).comp (quotient K n))).ofConv
    rw [unitriangularFromGL_comp_quotient, unitriangularFromGL_comp_quotient]
    exact congrArg WithConv.ofConv
      ((generalLinearGroupMulEquivAlgHom K n R).map_mul s.1 t.1)

@[simp] theorem unitriangularGroupMulEquivAlgHom_entry
    (s : Matrix.UnitriangularGroup n R) (i j : n) :
    (unitriangularGroupMulEquivAlgHom K n R s).ofConv
      (quotient K n (matrix K n i j)) = s.1 i j := by
  change (unitriangularFromGL K n R s) (quotient K n (matrix K n i j)) = _
  rw [← AlgHom.comp_apply, unitriangularFromGL_comp_quotient, evaluate_matrix]

@[simp] theorem unitriangularGroupMulEquivAlgHom_detInverse
    (s : Matrix.UnitriangularGroup n R) :
    (unitriangularGroupMulEquivAlgHom K n R s).ofConv
      (quotient K n (detInverse K n)) = 1 := by
  rw [quotient_detInverse, map_one]

/-- The multiplicative equivalence with affine scheme-valued points. -/
def unitriangularGroupMulEquivPoints :
    Matrix.UnitriangularGroup n R ≃*
      ((Spec (.of R)).asOver (Spec (.of K)) ⟶ unitriangularGroupUnderlyingScheme K n) :=
  (unitriangularGroupMulEquivAlgHom K n R).trans
    (Spec.mapMulEquiv (R := K) (S := UnitriangularCoordinateRing.CoordinateRing K n)
      (T := R))

theorem unitriangularGroupMulEquivPoints_apply_left (s : Matrix.UnitriangularGroup n R) :
    (unitriangularGroupMulEquivPoints K n R s).left =
      Spec.map (CommRingCat.ofHom (unitriangularFromGL K n R s).toRingHom) := rfl

theorem unitriangularGroupPoint_preimage_entry
    (s : Matrix.UnitriangularGroup n R) (i j : n) :
    (Spec.preimage (unitriangularGroupMulEquivPoints K n R s).left).hom
      (quotient K n (matrix K n i j)) = s.1 i j := by
  rw [unitriangularGroupMulEquivPoints_apply_left, Spec.preimage_map]
  exact unitriangularGroupMulEquivAlgHom_entry K n R s i j

/-- The actual scheme inclusion agrees with the native GL subgroup embedding
on every commutative coefficient algebra. -/
theorem unitriangularInclusion_point (s : Matrix.UnitriangularGroup n R) :
    unitriangularGroupMulEquivPoints K n R s ≫
      (unitriangularInclusion K n).hom.hom =
      generalLinearGroupMulEquivPoints K n R s.1 := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, unitriangularGroupMulEquivPoints_apply_left,
    unitriangularInclusion_left, generalLinearGroupMulEquivPoints_apply_left]
  change Spec.map (CommRingCat.ofHom (unitriangularFromGL K n R s).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (quotient K n).toRingHom) =
    Spec.map (CommRingCat.ofHom (evaluate (K := K) s.1).toRingHom)
  rw [← Spec.map_comp]
  exact congrArg (fun h : GeneralLinearCoordinateRing.CoordinateRing K n →ₐ[K] R =>
    Spec.map (CommRingCat.ofHom h.toRingHom))
      (unitriangularFromGL_comp_quotient K n R s)

theorem unitriangularToGL_natural {S : Type u} [CommRing S] [Algebra K S]
    (v : R →ₐ[K] S) (f : UnitriangularCoordinateRing.CoordinateRing K n →ₐ[K] R) :
    unitriangularToGL K n S (v.comp f) =
      Matrix.UnitriangularGroup.map v.toRingHom (unitriangularToGL K n R f) := by
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rfl

theorem unitriangularFromGL_natural {S : Type u} [CommRing S] [Algebra K S]
    (v : R →ₐ[K] S) (s : Matrix.UnitriangularGroup n R) :
    unitriangularFromGL K n S (Matrix.UnitriangularGroup.map v.toRingHom s) =
      v.comp (unitriangularFromGL K n R s) := by
  apply Ideal.Quotient.algHom_ext K
  change (unitriangularFromGL K n S
    (Matrix.UnitriangularGroup.map v.toRingHom s)).comp (quotient K n) =
      (v.comp (unitriangularFromGL K n R s)).comp (quotient K n)
  rw [unitriangularFromGL_comp_quotient, AlgHom.comp_assoc,
    unitriangularFromGL_comp_quotient]
  exact evaluate_natural v s.1

/-- Native upper-unitriangular groups as a functor of `K`-algebras. -/
def unitriangularGroupFunctor : CommAlgCat K ⥤ GrpCat where
  obj R := GrpCat.of (Matrix.UnitriangularGroup n R)
  map f := GrpCat.ofHom (Matrix.UnitriangularGroup.map f.hom.toRingHom)
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

/-- Represented group-valued functor on all commutative coefficient algebras. -/
abbrev unitriangularGroupPointsFunctor : CommAlgCat K ⥤ GrpCat :=
  (algSpec (.of K)).rightOp ⋙ yonedaGrp.obj (unitriangularGroupScheme K n)

/-- Multiplicative and natural functorial identification of native group units
with the points of the finite-type upper-unitriangular group scheme. -/
def unitriangularGroupPointsIso :
    unitriangularGroupFunctor K n ≅ unitriangularGroupPointsFunctor K n :=
  NatIso.ofComponents
    (fun R => (unitriangularGroupMulEquivPoints K n R).toGrpIso)
    (fun {R S} f => by
      ext s
      apply Over.OverMorphism.ext
      change (unitriangularGroupMulEquivPoints K n S
        (Matrix.UnitriangularGroup.map f.hom.toRingHom s)).left =
          ((algSpec (.of K)).map f.op).left ≫
            (unitriangularGroupMulEquivPoints K n R s).left
      rw [unitriangularGroupMulEquivPoints_apply_left]
      change Spec.map (CommRingCat.ofHom
        (unitriangularFromGL K n S
          (Matrix.UnitriangularGroup.map f.hom.toRingHom s)).toRingHom) =
            Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫
              Spec.map (CommRingCat.ofHom (unitriangularFromGL K n R s).toRingHom)
      rw [← Spec.map_comp]
      exact congrArg (fun h : UnitriangularCoordinateRing.CoordinateRing K n →ₐ[K] S =>
        Spec.map (CommRingCat.ofHom h.toRingHom))
          (unitriangularFromGL_natural K n R f.hom s))

end AlgebraicGeometry
