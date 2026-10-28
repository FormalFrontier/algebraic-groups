/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.DiagonalTorus
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Dynamic.Weight.Levi.DiagonalTorus
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Dynamic.Weight.Levi.Kernel
public import TauCeti.Algebra.AlgebraicGroup.UpperUnitriangular.Scheme
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits

/-!
# The split diagonal quotient of the canonical upper-triangular group

The injective-weight Levi and unipotent presentations are identified with the canonical
split torus and polynomial upper-unitriangular group. The represented weight-parabolic
kernel theorem then supplies the scheme-theoretic kernel over every commutative base,
including rank zero and the zero ring.

The arbitrary-ring coordinate pushout and the arbitrary-source scheme and group-object
pullbacks below retain the universal properties of the original construction.

## References

* J. S. Milne, *Algebraic Groups* (2017), §2.9.
* Mathlib, `Mathlib.AlgebraicGeometry.Pullbacks`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WithConv
open scoped CategoryTheory.MonObj
noncomputable section
universe u
namespace TauCeti.GeneralLinear.UpperTriangular
variable (K : Type u) [CommRing K] (n : ℕ)

private theorem mem_unipotent_iff {A : Type u} [CommRing A] [Algebra K A]
    (g : WithConv (GeneralLinear.coordinateHopfAlgebra K n →ₐ[K] A)) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup (GeneralLinear.coordinateHopfAlgebra K n)
        (weightUnipotentDefiningHopfIdeal K (weights n)) (CommAlgCat.of K A) ↔
      GeneralLinear.pointsMulEquiv n g ∈ upperUnitriangularGroup (Fin n) A := by
  rw [GeneralLinear.mem_weightUnipotentDefiningPointsSubgroup_iff,
    UpperUnitriangularGroup.mem_iff, Matrix.isUpperUnitriangular_def]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro i j hji
      have hne : i ≠ j := fun h ↦ hji.ne h.symm
      simpa [Matrix.one_apply, hne] using
        h i j ((weights_lt_weights_iff n i j).mpr hji).le
    · intro i
      simpa using h i i le_rfl
  · rintro ⟨htri, hdiag⟩ i j hij
    rcases hij.eq_or_lt with hij | hij
    · have : i = j := weights_injective n hij
      subst j
      simpa using hdiag i
    · have hji : j < i := (weights_lt_weights_iff n i j).mp hij
      simpa [Matrix.one_apply, hji.ne'] using htri hji

/-- The polynomial unitriangular presentation cuts out the canonical weight-unipotent ideal. -/
theorem ker_unitriangularCoordinateMap :
    HopfIdeal.kerOfSurjective (UpperUnitriangular.coordinateMap K n).hom
        (UpperUnitriangular.coordinateMap_surjective K n) =
      weightUnipotentDefiningHopfIdeal K (weights n) := by
  apply le_antisymm
  · intro x hx
    let I := weightUnipotentDefiningHopfIdeal K (weights n)
    let Q := CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra K n) I
    let g := CommHopfAlgCat.quotientPointsHom (GeneralLinear.coordinateHopfAlgebra K n) I
      (CommAlgCat.of K Q) (toConv (AlgHom.id K Q))
    have hg : GeneralLinear.pointsMulEquiv n g ∈ upperUnitriangularGroup (Fin n) Q :=
      (mem_unipotent_iff K n g).mp
        (CommHopfAlgCat.quotientPointsHom_mem_quotientPointsSubgroup _ _ _ _)
    let f := (UpperUnitriangular.pointsMulEquiv K (Fin n) (A := Q)).symm
      ⟨GeneralLinear.pointsMulEquiv n g, hg⟩
    have hfg : UpperUnitriangular.inclusionPoints (R := K) n f = g := by
      apply (GeneralLinear.pointsMulEquiv (R := K) (A := Q) n).injective
      simp only [GeneralLinear.pointsMulEquiv_apply,
        UpperUnitriangular.pointToGeneralLinear_inclusionPoints]
      exact (congrArg Subtype.val
        ((UpperUnitriangular.pointsMulEquiv K (Fin n) (A := Q)).apply_symm_apply _)).trans
          (GeneralLinear.pointsMulEquiv_apply n g)
    have hx0 := (HopfIdeal.mem_kerOfSurjective _ _).mp hx
    have heval : g.ofConv x = 0 := by
      rw [← hfg, ← UpperUnitriangular.mapPointsFunctor_coordinateMap_app K n
        (CommAlgCat.of K Q) f]
      change f.ofConv ((UpperUnitriangular.coordinateMap K n).hom x) = 0
      rw [hx0, map_zero]
    change x ∈ I
    apply HopfIdeal.mem_toIdeal.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have he := CommHopfAlgCat.quotientPointsHom_apply_apply
      (GeneralLinear.coordinateHopfAlgebra K n) I (CommAlgCat.of K Q)
      (toConv (AlgHom.id K Q)) x
    exact he.symm.trans heval
  · intro x hx
    apply (HopfIdeal.mem_kerOfSurjective _ _).mpr
    let U := UpperUnitriangular.coordinateHopfAlgebra K (Fin n)
    let f : WithConv (U →ₐ[K] U) := toConv (AlgHom.id K U)
    have hg : UpperUnitriangular.inclusionPoints (R := K) n f ∈
        CommHopfAlgCat.quotientPointsSubgroup (GeneralLinear.coordinateHopfAlgebra K n)
          (weightUnipotentDefiningHopfIdeal K (weights n)) (CommAlgCat.of K U) := by
      apply (mem_unipotent_iff K n _).mpr
      rw [GeneralLinear.pointsMulEquiv_apply,
        UpperUnitriangular.pointToGeneralLinear_inclusionPoints]
      exact (UpperUnitriangular.pointsMulEquiv K (Fin n) f).property
    have h := (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).mp hg x hx
    rw [← UpperUnitriangular.mapPointsFunctor_coordinateMap_app K n
      (CommAlgCat.of K U) f] at h
    exact h

/-- The two canonical unitriangular coordinate presentations agree, compatibly with GL. -/
noncomputable def weightUnipotentCoordinateIso :
    weightUnipotentCoordinateHopfAlgebra K (weights n) ≅
      UpperUnitriangular.coordinateHopfAlgebra K (Fin n) :=
  (UpperUnitriangular.coordinateMap K n).quotientIsoOfKerOfSurjectiveEq
    (UpperUnitriangular.coordinateMap_surjective K n) (ker_unitriangularCoordinateMap K n)


@[reassoc (attr := simp)]
theorem coordinateMap_comp_weightUnipotentCoordinateIso :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra K n)
        (weightUnipotentDefiningHopfIdeal K (weights n)) ≫
      (weightUnipotentCoordinateIso K n).hom = UpperUnitriangular.coordinateMap K n :=
  _root_.CommHopfAlgCat.Hom.mkQuotient_comp_quotientIsoOfKerOfSurjectiveEq_hom _ _ _

/-- Restriction from the upper-triangular coordinate algebra to its polynomial unipotent part. -/
def unitriangularCoordinateMap : coordinateHopfAlgebra K n ⟶
    UpperUnitriangular.coordinateHopfAlgebra K (Fin n) :=
  CommHopfAlgCat.quotientMapOfLe (GeneralLinear.coordinateHopfAlgebra K n)
      (Dynamic.weightParabolicDefiningHopfIdeal_le_weightUnipotent K (weights n)) ≫
    (weightUnipotentCoordinateIso K n).hom

@[reassoc (attr := simp)]
theorem coordinateMap_comp_unitriangularCoordinateMap :
    coordinateMap K n ≫ unitriangularCoordinateMap K n =
      UpperUnitriangular.coordinateMap K n := by
  rw [unitriangularCoordinateMap, ← Category.assoc, coordinateMap_def,
    CommHopfAlgCat.mkQuotient_comp_quotientMapOfLe,
    coordinateMap_comp_weightUnipotentCoordinateIso]

/-- The diagonal projection's coordinate morphism, using the existing injective-weight Levi. -/
def diagonalProjectionCoordinateMap :
    _root_.CommHopfAlgCat.of K
        (MonoidAlgebra K (Multiplicative (ULift.{u} (Fin n) →₀ ℤ))) ⟶
      coordinateHopfAlgebra K n :=
  (weightLeviDiagonalCoordinateIso K (weights n) (weights_injective n)).inv ≫
    Dynamic.weightParabolicLimitCoordinateMap K (weights n)

private theorem diagonalTorusCoordinateMap_eq :
    diagonalTorusCoordinateMap K n =
      Dynamic.weightLeviToParabolicCoordinateMap K (weights n) ≫
        (weightLeviDiagonalCoordinateIso K (weights n) (weights_injective n)).hom := by
  apply _root_.CommHopfAlgCat.mkQuotient_hom_ext
  rw [← coordinateMap_def, coordinateMap_comp_diagonalTorusCoordinateMap,
    ← Category.assoc, coordinateMap_def, Dynamic.weightLeviToParabolicCoordinateMap_def,
    CommHopfAlgCat.mkQuotient_comp_quotientMapOfLe,
    weightLeviCoordinateMap_comp_weightLeviDiagonalCoordinateIso_hom]

/-- The diagonal section splits the projection over every commutative base ring. -/
@[reassoc (attr := simp)]
theorem diagonalProjectionCoordinateMap_comp_diagonalTorusCoordinateMap :
    diagonalProjectionCoordinateMap K n ≫ diagonalTorusCoordinateMap K n = 𝟙 _ := by
  rw [diagonalProjectionCoordinateMap, diagonalTorusCoordinateMap_eq]
  rw [Category.assoc, ← Category.assoc
    (Dynamic.weightParabolicLimitCoordinateMap K (weights n)),
    Dynamic.weightParabolicLimitCoordinateMap_comp_weightLeviToParabolicCoordinateMap,
    Category.id_comp, Iso.inv_hom_id]

/-- Projection to the canonical split torus. -/
def diagonalProjection : groupScheme K n ⟶ SplitTorus.groupScheme K (ULift.{u} (Fin n)) :=
  (hopfSpec (CommRingCat.of K)).map (diagonalProjectionCoordinateMap K n).op

/-- The canonical polynomial unitriangular closed subgroup inside the upper-triangular group. -/
def unitriangularInclusion : UpperUnitriangular.groupScheme K (Fin n) ⟶ groupScheme K n :=
  eqToHom (UpperUnitriangular.groupScheme_def K (Fin n)) ≫
    (hopfSpec (CommRingCat.of K)).map (unitriangularCoordinateMap K n).op

@[reassoc (attr := simp)]
theorem diagonalTorus_comp_diagonalProjection :
    diagonalTorus K n ≫ diagonalProjection K n = 𝟙 _ := by
  rw [diagonalTorus_def, diagonalProjection]
  simp only [eqToHom_refl, Category.comp_id]
  change (hopfSpec (CommRingCat.of K)).map (diagonalTorusCoordinateMap K n).op ≫
    (hopfSpec (CommRingCat.of K)).map (diagonalProjectionCoordinateMap K n).op = _
  rw [← Functor.map_comp, ← op_comp,
    diagonalProjectionCoordinateMap_comp_diagonalTorusCoordinateMap, op_id]
  exact (hopfSpec (CommRingCat.of K)).map_id _

@[reassoc (attr := simp)]
theorem unitriangularInclusion_comp_inclusion :
    unitriangularInclusion K n ≫ inclusion K n = UpperUnitriangular.inclusion K n := by
  simp only [unitriangularInclusion, inclusion, UpperUnitriangular.inclusion_def,
    GeneralLinear.weightParabolicInclusion_def, CommHopfAlgCat.quotientSpecι_def,
    Category.assoc]
  congr 1
  rw [← Category.assoc, ← Functor.map_comp, ← op_comp, ← coordinateMap_def,
    coordinateMap_comp_unitriangularCoordinateMap]

/-- The torus projection has the existing relative weight-unipotent defining ideal. -/
theorem kernelHopfIdeal_diagonalProjectionCoordinateMap :
    CommHopfAlgCat.kernelHopfIdeal (diagonalProjectionCoordinateMap K n) =
      Dynamic.weightUnipotentInParabolicHopfIdeal K (weights n) := by
  rw [diagonalProjectionCoordinateMap,
    CommHopfAlgCat.kernelHopfIdeal_comp_of_surjective _
      (ConcreteCategory.bijective_of_isIso _).2,
    Dynamic.kernelHopfIdeal_weightParabolicLimitCoordinateMap]

/-- The actual kernel coordinate quotient is the canonical polynomial unitriangular algebra. -/
def kernelCoordinateIso :
    CommHopfAlgCat.quotient (coordinateHopfAlgebra K n)
        (CommHopfAlgCat.kernelHopfIdeal (diagonalProjectionCoordinateMap K n)) ≅
      UpperUnitriangular.coordinateHopfAlgebra K (Fin n) :=
  eqToIso (congrArg (CommHopfAlgCat.quotient (coordinateHopfAlgebra K n))
      (kernelHopfIdeal_diagonalProjectionCoordinateMap K n)) ≪≫
    (Dynamic.weightUnipotentInParabolicCoordinateIso K (weights n)).symm ≪≫
    weightUnipotentCoordinateIso K n

@[reassoc (attr := simp)]
theorem mkQuotient_comp_kernelCoordinateIso :
    CommHopfAlgCat.mkQuotient (coordinateHopfAlgebra K n)
        (CommHopfAlgCat.kernelHopfIdeal (diagonalProjectionCoordinateMap K n)) ≫
      (kernelCoordinateIso K n).hom = unitriangularCoordinateMap K n := by
  apply _root_.CommHopfAlgCat.mkQuotient_hom_ext
  rw [← coordinateMap_def, ← Category.assoc,
    coordinateMap_comp_unitriangularCoordinateMap, kernelCoordinateIso,
    Iso.trans_hom, Iso.trans_hom, eqToIso.hom]
  simp only [Category.assoc]
  rw [← Category.assoc (CommHopfAlgCat.mkQuotient (coordinateHopfAlgebra K n)
      (CommHopfAlgCat.kernelHopfIdeal (diagonalProjectionCoordinateMap K n))),
    _root_.CommHopfAlgCat.mkQuotient_comp_eqToHom
      (kernelHopfIdeal_diagonalProjectionCoordinateMap K n).symm,
    ← Category.assoc,
    ← Dynamic.mkQuotient_weightUnipotent_comp_weightUnipotentInParabolicCoordinateIso_hom]
  simp only [Category.assoc, Iso.symm_hom, Iso.hom_inv_id_assoc,
    coordinateMap_comp_weightUnipotentCoordinateIso]

/-- The polynomial unitriangular group is the scheme-theoretic kernel of the diagonal
projection, with its canonical coordinate inclusion. -/
def kernelIso : UpperUnitriangular.groupScheme K (Fin n) ≅
    CommHopfAlgCat.kernelSpec (diagonalProjectionCoordinateMap K n) :=
  eqToIso (UpperUnitriangular.groupScheme_def K (Fin n)) ≪≫
    (hopfSpec (CommRingCat.of K)).mapIso (kernelCoordinateIso K n).op

@[reassoc (attr := simp)]
theorem kernelIso_hom_comp_kernelSpecι :
    (kernelIso K n).hom ≫
      CommHopfAlgCat.kernelSpecι (diagonalProjectionCoordinateMap K n) =
        unitriangularInclusion K n := by
  rw [kernelIso, Iso.trans_hom, eqToIso.hom, Functor.mapIso_hom, Iso.op_hom,
    CommHopfAlgCat.kernelSpecι_def, CommHopfAlgCat.quotientSpecι_def,
    Category.assoc, ← Functor.map_comp, ← op_comp, mkQuotient_comp_kernelCoordinateIso]
  rfl

/-- The unitriangular subgroup is the categorical kernel for arbitrary group-scheme sources. -/
theorem isPullback_diagonalProjection_group :
    IsPullback (unitriangularInclusion K n)
      (0 : UpperUnitriangular.groupScheme K (Fin n) ⟶
        Grp.trivial (Over (Spec (CommRingCat.of K))))
      (diagonalProjection K n)
      (0 : Grp.trivial (Over (Spec (CommRingCat.of K))) ⟶
        SplitTorus.groupScheme K (ULift.{u} (Fin n))) := by
  apply (CommHopfAlgCat.isPullback_kernelSpec (diagonalProjectionCoordinateMap K n)).of_iso
    (kernelIso K n).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
    exact (Iso.eq_inv_comp _).mpr (kernelIso_hom_comp_kernelSpecι K n)
  · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom, comp_zero]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp, diagonalProjection]
  · exact (Category.id_comp _).symm

/-- The unitriangular kernel inclusion is a closed immersion over arbitrary base rings. -/
instance isClosedImmersion_unitriangularInclusion :
    IsClosedImmersion (unitriangularInclusion K n).hom.hom.left := by
  rw [← kernelIso_hom_comp_kernelSpecι]
  change IsClosedImmersion ((kernelIso K n).hom.hom.hom.left ≫
    (CommHopfAlgCat.kernelSpecι (diagonalProjectionCoordinateMap K n)).hom.hom.left)
  have : IsIso (kernelIso K n).hom.hom.hom.left := by
    change IsIso ((Over.forget _).map ((Grp.forget _).map (kernelIso K n).hom))
    infer_instance
  have : IsClosedImmersion
      (CommHopfAlgCat.kernelSpecι (diagonalProjectionCoordinateMap K n)).hom.hom.left := by
    rw [CommHopfAlgCat.kernelSpecι_def]
    infer_instance
  infer_instance

/-- The kernel universal property for arbitrary schemes over the base. -/
theorem isPullback_diagonalProjection_over :
    IsPullback (unitriangularInclusion K n).hom.hom
      (CartesianMonoidalCategory.toUnit (UpperUnitriangular.groupScheme K (Fin n)).X)
      (diagonalProjection K n).hom.hom
      η[(SplitTorus.groupScheme K (ULift.{u} (Fin n))).X] := by
  have h := (isPullback_diagonalProjection_group K n).map
    (Grp.forget (Over (Spec (CommRingCat.of K))))
  exact h

/-- The same kernel square is a pullback among arbitrary schemes. -/
theorem isPullback_diagonalProjection :
    IsPullback (unitriangularInclusion K n).hom.hom.left
      (UpperUnitriangular.groupScheme K (Fin n)).X.hom
      (diagonalProjection K n).hom.hom.left
      η[(SplitTorus.groupScheme K (ULift.{u} (Fin n))).X].left := by
  exact (isPullback_diagonalProjection_over K n).map
    (Over.forget (Spec (CommRingCat.of K)))

/-- The coordinate square is a pushout for arbitrary commutative-ring targets and compatible
scalar maps, with no assumption that those maps are morphisms of `K`-algebras. -/
theorem isPushout_diagonalProjection :
    IsPushout
      (CommRingCat.ofHom (diagonalProjectionCoordinateMap K n).hom.toAlgHom.toRingHom)
      (CommRingCat.ofHom (Bialgebra.counitAlgHom K
        (MonoidAlgebra K (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)))).toRingHom)
      (CommRingCat.ofHom (unitriangularCoordinateMap K n).hom.toAlgHom.toRingHom)
      (CommRingCat.ofHom
        (algebraMap K (UpperUnitriangular.coordinateHopfAlgebra K (Fin n)))) := by
  have h := isPullback_diagonalProjection K n
  have h' : IsPullback
      (CommRingCat.ofHom (unitriangularCoordinateMap K n).hom.toAlgHom.toRingHom).op
      (CommRingCat.ofHom
        (algebraMap K (UpperUnitriangular.coordinateHopfAlgebra K (Fin n)))).op
      (CommRingCat.ofHom (diagonalProjectionCoordinateMap K n).hom.toAlgHom.toRingHom).op
      (CommRingCat.ofHom (Bialgebra.counitAlgHom K
        (MonoidAlgebra K (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)))).toRingHom).op := by
    apply IsPullback.of_map_of_faithful (F := Scheme.Spec)
    exact h
  exact h'.unop.flip

section Points

variable {A : Type u} [CommRing A] [Algebra K A]

/-- Restriction of a polynomial unitriangular point gives its ordinary upper-triangular matrix. -/
theorem pointsMulEquiv_unitriangularCoordinateMap
    (f : WithConv (UpperUnitriangular.coordinateHopfAlgebra K (Fin n) →ₐ[K] A)) :
    pointsMulEquiv (R := K) (n := n) (A := A)
        (toConv (f.ofConv.comp (unitriangularCoordinateMap K n).hom.toAlgHom)) =
      (Subgroup.inclusion UpperTriangularGroup.upperUnitriangularGroup_le_upperTriangularGroup)
        (UpperUnitriangular.pointsMulEquiv K (Fin n) f) := by
  apply Subtype.ext
  rw [← pointsMulEquiv_coe]
  have h := CommHopfAlgCat.mapPointsFunctor_eq_quotientPointsHom_of_mkQuotient_comp
    (definingHopfIdeal K n) (unitriangularCoordinateMap K n)
    (UpperUnitriangular.coordinateMap K n)
    (by simpa only [coordinateMap_def] using coordinateMap_comp_unitriangularCoordinateMap K n)
    (CommAlgCat.of K A) f
  have hu := CommHopfAlgCat.Hom.mapPointsFunctor_app_apply
    (unitriangularCoordinateMap K n) (CommAlgCat.of K A) f
  have h' := h.trans (congrArg
    (CommHopfAlgCat.quotientPointsHom (GeneralLinear.coordinateHopfAlgebra K n)
      (definingHopfIdeal K n) (CommAlgCat.of K A)) hu)
  have ha := (CommHopfAlgCat.Hom.mapPointsFunctor_app_apply
    (UpperUnitriangular.coordinateMap K n) (CommAlgCat.of K A) f).trans
      (UpperUnitriangular.mapPointsFunctor_coordinateMap_app K n (CommAlgCat.of K A) f)
  exact (congrArg (GeneralLinear.pointToGeneralLinear n)
    (h'.symm.trans ha)).trans
      (UpperUnitriangular.pointToGeneralLinear_inclusionPoints K n f)

/-- The diagonal projection on all algebra-valued points is the ordinary tuple of diagonal units. -/
theorem pointsMulEquiv_diagonalProjectionCoordinateMap
    (f : WithConv (coordinateHopfAlgebra K n →ₐ[K] A)) :
    SplitTorus.pointsMulEquiv (R := K) (A := A)
        (toConv (f.ofConv.comp (diagonalProjectionCoordinateMap K n).hom.toAlgHom)) =
      fun i : ULift.{u} (Fin n) ↦ UpperTriangularGroup.diag
        (pointsMulEquiv (R := K) (n := n) (A := A) f) i.down := by
  let e := weightLeviDiagonalCoordinateIso K (weights n) (weights_injective n)
  have hc : GeneralLinear.diagonalTorusCoordinateMap (R := K) (N := n) ≫
      diagonalProjectionCoordinateMap K n =
      CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra K n)
        (weightLeviDefiningHopfIdeal K (weights n)) ≫
          Dynamic.weightParabolicLimitCoordinateMap K (weights n) := by
    rw [← weightLeviCoordinateMap_comp_weightLeviDiagonalCoordinateIso_hom K
      (weights n) (weights_injective n), diagonalProjectionCoordinateMap]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have hp := congrArg (fun q ↦ (CommHopfAlgCat.Hom.mapPointsFunctor q).app
    (CommAlgCat.of K A) f) hc
  have hl := CommHopfAlgCat.Hom.mapPointsFunctor_comp_app_apply
    (GeneralLinear.diagonalTorusCoordinateMap (R := K) (N := n))
    (diagonalProjectionCoordinateMap K n) (CommAlgCat.of K A) f
  have hr := CommHopfAlgCat.Hom.mapPointsFunctor_comp_app_apply
    (CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra K n)
      (weightLeviDefiningHopfIdeal K (weights n)))
    (Dynamic.weightParabolicLimitCoordinateMap K (weights n)) (CommAlgCat.of K A) f
  have hp' := hl.symm.trans (hp.trans hr)
  have hd := GeneralLinear.mapPointsFunctor_diagonalTorusCoordinateMap_app
    (CommAlgCat.of K A)
    ((CommHopfAlgCat.Hom.mapPointsFunctor (diagonalProjectionCoordinateMap K n)).app
      (CommAlgCat.of K A) f)
  have he := CommHopfAlgCat.Hom.mapPointsFunctor_app_apply
    (diagonalProjectionCoordinateMap K n) (CommAlgCat.of K A) f
  have hp := (hd.trans (congrArg GeneralLinear.diagonalTorusPoints he)).symm.trans hp'
  have hpq : GeneralLinear.diagonalTorusPoints
      (toConv (f.ofConv.comp (diagonalProjectionCoordinateMap K n).hom.toAlgHom)) =
      CommHopfAlgCat.quotientPointsHom (GeneralLinear.coordinateHopfAlgebra K n)
        (weightLeviDefiningHopfIdeal K (weights n)) (CommAlgCat.of K A)
        ((CommHopfAlgCat.Hom.mapPointsFunctor
          (Dynamic.weightParabolicLimitCoordinateMap K (weights n))).app
            (CommAlgCat.of K A) f) := hp
  rw [Dynamic.mapPointsFunctor_weightParabolicLimitCoordinateMap_app,
    Dynamic.quotientPointsHom_weightLeviPointsIso_inv_app_apply] at hpq
  let p : Cocharacter.parabolic (CommAlgCat.of K A)
      (weightCocharacter (R := K) (weights n)) :=
    (Dynamic.weightParabolicPointsIso K (weights n)).hom.app (CommAlgCat.of K A) f
  have hpq' : GeneralLinear.diagonalTorusPoints
      (toConv (f.ofConv.comp (diagonalProjectionCoordinateMap K n).hom.toAlgHom)) =
      Cocharacter.limit (CommAlgCat.of K A)
        (weightCocharacter (R := K) (weights n)) p :=
    hpq.trans (Cocharacter.coe_limitToLevi_apply _ _ p)
  have hpcoe : (p : WithConv (GeneralLinear.coordinateHopfAlgebra K n →ₐ[K] A)) =
      CommHopfAlgCat.quotientPointsHom (GeneralLinear.coordinateHopfAlgebra K n)
        (definingHopfIdeal K n) (CommAlgCat.of K A) f := by
    exact Dynamic.coe_weightParabolicPointsIso_hom_app_apply K (weights n) f
  funext i
  apply Units.ext
  have hm := congrArg (fun q ↦ (GeneralLinear.pointsMulEquiv n q :
    Matrix (Fin n) (Fin n) A) i.down i.down) hpq'
  have hlim : (GeneralLinear.pointsMulEquiv n
      (Cocharacter.limit (CommAlgCat.of K A) (weightCocharacter (R := K) (weights n)) p) :
      Matrix (Fin n) (Fin n) A) i.down i.down =
      (GeneralLinear.pointsMulEquiv n p.1 : Matrix (Fin n) (Fin n) A) i.down i.down := by
    have hpeta : (⟨p.1, p.2⟩ : Cocharacter.parabolic (CommAlgCat.of K A)
        (weightCocharacter (R := K) (weights n))) = p := Subtype.ext rfl
    have hentry := Dynamic.pointsMulEquiv_limit_weightCocharacter_apply
      (weights n) p.1 p.2 i.down i.down
    have heta := congrArg (fun q ↦ (GeneralLinear.pointsMulEquiv n
      (Cocharacter.limit (CommAlgCat.of K A) (weightCocharacter (R := K) (weights n)) q) :
        Matrix (Fin n) (Fin n) A) i.down i.down) hpeta.symm
    exact heta.trans (by simpa only [ite_true, eq_self] using hentry)
  have hm := hm.trans hlim
  rw [GeneralLinear.pointsMulEquiv_diagonalTorusPoints, diagGL_apply, ite_eq_left rfl,
    hpcoe, GeneralLinear.pointsMulEquiv_apply, pointsMulEquiv_coe] at hm
  simpa only [diagonalTorusCoordinates_apply, ULift.up_down] using
    hm.trans (UpperTriangularGroup.diag_apply_val _ _).symm

/-- The existing diagonal-torus section is the native diagonal matrix on all algebra points. -/
theorem pointsMulEquiv_diagonalTorusCoordinateMap_native
    (f : WithConv
      (MonoidAlgebra K (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)) →ₐ[K] A)) :
    pointsMulEquiv (R := K) (n := n) (A := A)
        (toConv (f.ofConv.comp (diagonalTorusCoordinateMap K n).hom.toAlgHom)) =
      UpperTriangularGroup.diagonalHom
        (fun i ↦ SplitTorus.pointsMulEquiv (R := K) (A := A) f (ULift.up i)) := by
  apply Subtype.ext
  refine (pointsMulEquiv_diagonalTorusCoordinateMap K n f).trans
    ((GeneralLinear.pointsMulEquiv_diagonalTorusPoints f).trans ?_)
  rw [UpperTriangularGroup.coe_diagonalHom]
  congr 1
  funext i
  exact diagonalTorusCoordinates_apply _ i

/-- On represented points, inclusion of the kernel is the ordinary inclusion of matrices. -/
theorem unitriangularInclusion_point
    (s : upperUnitriangularGroup (Fin n) A) :
    Spec.mapMulEquiv ((UpperUnitriangular.pointsMulEquiv K (Fin n) (A := A)).symm s) ≫
      (unitriangularInclusion K n).hom.hom =
      Spec.mapMulEquiv ((pointsMulEquiv (R := K) (n := n) (A := A)).symm
        ((Subgroup.inclusion
          UpperTriangularGroup.upperUnitriangularGroup_le_upperTriangularGroup) s)) := by
  let f := (UpperUnitriangular.pointsMulEquiv K (Fin n) (A := A)).symm s
  have h := CommHopfAlgCat.mapMulEquiv_mapDomain (CommAlgCat.of K A)
    (unitriangularCoordinateMap K n).hom f
  have hc : toConv (f.ofConv.comp (unitriangularCoordinateMap K n).hom.toAlgHom) =
      (pointsMulEquiv (R := K) (n := n) (A := A)).symm
        ((Subgroup.inclusion
          UpperTriangularGroup.upperUnitriangularGroup_le_upperTriangularGroup) s) := by
    apply (pointsMulEquiv (R := K) (n := n) (A := A)).injective
    simpa only [f, MulEquiv.apply_symm_apply] using
      pointsMulEquiv_unitriangularCoordinateMap K n f
  exact h.symm.trans (congrArg Spec.mapMulEquiv
    ((BialgHom.mapDomain_apply _ f).trans hc))

/-- The represented diagonal projection recovers diagonal units on every algebra-valued point. -/
theorem diagonalProjection_point (s : upperTriangularGroup (Fin n) A) :
    Spec.mapMulEquiv ((pointsMulEquiv (R := K) (n := n) (A := A)).symm s) ≫
      (diagonalProjection K n).hom.hom =
      Spec.mapMulEquiv ((SplitTorus.pointsMulEquiv (R := K) (A := A)).symm
        (fun i : ULift.{u} (Fin n) ↦ UpperTriangularGroup.diag s i.down)) := by
  let f := (pointsMulEquiv (R := K) (n := n) (A := A)).symm s
  have h := CommHopfAlgCat.mapMulEquiv_mapDomain (CommAlgCat.of K A)
    (diagonalProjectionCoordinateMap K n).hom f
  have hc : toConv (f.ofConv.comp (diagonalProjectionCoordinateMap K n).hom.toAlgHom) =
      (SplitTorus.pointsMulEquiv (R := K) (A := A)).symm
        (fun i : ULift.{u} (Fin n) ↦ UpperTriangularGroup.diag s i.down) := by
    apply (SplitTorus.pointsMulEquiv (R := K) (A := A)).injective
    simpa only [f, MulEquiv.apply_symm_apply] using
      pointsMulEquiv_diagonalProjectionCoordinateMap K n f
  exact h.symm.trans (congrArg Spec.mapMulEquiv
    ((BialgHom.mapDomain_apply _ f).trans hc))

/-- The represented diagonal section is the ordinary diagonal matrix on every algebra point. -/
theorem diagonalTorus_point (d : ULift.{u} (Fin n) → Aˣ) :
    Spec.mapMulEquiv ((SplitTorus.pointsMulEquiv (R := K) (A := A)).symm d) ≫
      (diagonalTorus K n).hom.hom =
      Spec.mapMulEquiv ((pointsMulEquiv (R := K) (n := n) (A := A)).symm
        (UpperTriangularGroup.diagonalHom (fun i ↦ d (ULift.up i)))) := by
  let f := (SplitTorus.pointsMulEquiv (R := K) (A := A)).symm d
  have hc : toConv (f.ofConv.comp (diagonalTorusCoordinateMap K n).hom.toAlgHom) =
      (pointsMulEquiv (R := K) (n := n) (A := A)).symm
        (UpperTriangularGroup.diagonalHom (fun i ↦ d (ULift.up i))) := by
    apply (pointsMulEquiv (R := K) (n := n) (A := A)).injective
    simpa only [f, MulEquiv.apply_symm_apply] using
      pointsMulEquiv_diagonalTorusCoordinateMap_native K n f
  have hleft : (diagonalTorus K n).hom.hom.left =
      Spec.map (CommRingCat.ofHom (diagonalTorusCoordinateMap K n).hom.toAlgHom.toRingHom) := by
    rw [diagonalTorus_def]
    rfl
  apply Over.OverMorphism.ext
  erw [Over.comp_left]
  rw [hleft, CommHopfAlgCat.mapMulEquiv_left, CommHopfAlgCat.mapMulEquiv_left]
  erw [← Spec.map_comp]
  exact congrArg (fun q : WithConv
      (coordinateHopfAlgebra K n →ₐ[K] A) ↦
        Spec.map (CommRingCat.ofHom q.ofConv.toRingHom)) hc

end Points

end TauCeti.GeneralLinear.UpperTriangular
