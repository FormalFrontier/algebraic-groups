/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Bialgebra.Nilpotent
public import AlgebraicGroups.Algebra.HopfAlgebra.FiniteType
public import AlgebraicGroups.Algebra.HopfAlgebra.Reduced
public import AlgebraicGroups.Algebra.Smooth
public import AlgebraicGroups.GroupScheme.Smooth
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Noetherian.Nilpotent
public import SmoothRegularity.Algebra.Localization

/-!
# Smoothness and reducedness of Hopf algebras in characteristic zero

Cartier's theorem gives smoothness for finite-type commutative Hopf algebras over
characteristic-zero fields. Every commutative Hopf algebra over such a field is reduced:
each nilpotent element lies in a finite-type Hopf subalgebra. The scalar field and algebra
may lie in independent universes, and all assertions use the given coefficient algebra
structure.

## Main results

- `HopfAlgebra.smooth`: a finite-type commutative Hopf algebra over a characteristic-zero
  field is smooth.
- `HopfAlgebra.isReduced`: a commutative Hopf algebra over a characteristic-zero field is
  reduced.

## References

- J. S. Milne, *Algebraic Groups*, for Cartier's theorem in characteristic zero.
- Mathlib's `AlgebraicGeometry.smooth_of_grpObj`, for smoothness of geometrically reduced
  group schemes, and this library's `AlgebraicGeometry.smooth_of_unit_mem_smoothLocus`,
  for propagation of smoothness from the identity point.
- The related algebraic criteria are `HopfAlgebra.smooth_quotient_nilradical`,
  `Bialgebra.nilradical_le_ker_counit_sq`,
  `Algebra.Smooth.exists_sub_one_mem_and_smooth_away_of_quotient`, and
  `Algebra.Smooth.isReduced_of_isDomain`. The smooth principal neighborhood is centered
  at the original counit, and its unit point is retained when globalizing smoothness.
-/

@[expose] public section

open CategoryTheory MonoidalCategory MonObj

universe u v

namespace HopfAlgebra

open AlgebraicGeometry in
private lemma unit_mem_smoothLocus_of_smooth_away
    (K H : Type u) [Field K] [CommRing H] [HopfAlgebra K H]
    [Algebra.FiniteType K H] (r : H)
    (hr : r - 1 ∈ RingHom.ker ((Bialgebra.counitAlgHom K H).toRingHom))
    [Algebra.Smooth K (Localization.Away r)] :
    η[(Spec (.of H)).asOver (Spec (.of K))].left (IsLocalRing.closedPoint K)
      ∈ (Spec (.of H) ↘ Spec (.of K)).smoothLocus := by
  let L := Localization.Away r
  let ε : H →+* K := (Bialgebra.counitAlgHom K H).toRingHom
  have hr' : ε r = 1 := by
    simpa only [map_one] using (RingHom.sub_mem_ker_iff ε).mp hr
  let hεr : IsUnit (ε r) := by
    rw [hr']
    exact isUnit_one
  let εAway : L →+* K :=
    IsLocalization.Away.lift (S := L) (g := ε) r hεr
  have factorEq : εAway.comp (algebraMap H L) = ε :=
    IsLocalization.Away.lift_comp (S := L) (g := ε) r hεr
  let m : Spec (.of L) ⟶ Spec (.of H) :=
    Spec.map (CommRingCat.ofHom (algebraMap H L))
  let e : Spec (.of K) ⟶ Spec (.of L) :=
    Spec.map (CommRingCat.ofHom εAway)
  let f : Spec (.of H) ⟶ Spec (.of K) :=
    Spec (.of H) ↘ Spec (.of K)
  let unit : Spec (.of K) ⟶ Spec (.of H) :=
    η[(Spec (.of H)).asOver (Spec (.of K))].left
  let p : Spec (.of K) := IsLocalRing.closedPoint K
  have identityFactorEq : e ≫ m = unit := by
    change e ≫ m = η[(Spec (.of H)).asOver (Spec (.of K))].left
    rw [one_spec_asOver_spec_left]
    change Spec.map (CommRingCat.ofHom εAway) ≫
        Spec.map (CommRingCat.ofHom (algebraMap H L)) =
      Spec.map (CommRingCat.ofHom ε)
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, factorEq]
  let : IsOpenImmersion m :=
    Scheme.isOpenImmersion_SpecMap_localizationAway (R := .of H) r
  have compEq :
      m ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
    change Spec.map (CommRingCat.ofHom (algebraMap H L)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K H)) = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq K H L]
  let : Smooth (m ≫ f) := by
    rw [compEq, HasRingHomProperty.Spec_iff (P := @Smooth)]
    exact RingHom.smooth_algebraMap.mpr
      (inferInstance : Algebra.Smooth K L)
  have hpre : m ⁻¹ᵁ f.smoothLocus = ⊤ := by
    rw [Scheme.Hom.preimage_smoothLocus_eq m f,
      Scheme.Hom.smoothLocus_eq_top (m ≫ f)]
  have hpoint : m (e p) ∈ f.smoothLocus := by
    change e p ∈ m ⁻¹ᵁ f.smoothLocus
    rw [hpre]
    trivial
  have pointEq : m (e p) = unit p :=
    (Scheme.Hom.comp_apply e m p).symm.trans
      (congrArg (fun g : Spec (.of K) ⟶ Spec (.of H) => g p) identityFactorEq)
  have hunit : unit p ∈ f.smoothLocus :=
    (congrArg (fun x : Spec (.of H) => x ∈ f.smoothLocus) pointEq).mp hpoint
  exact hunit

private lemma exists_smooth_away_at_counit
    (K H : Type u) [Field K] [CharZero K] [CommRing H]
    [HopfAlgebra K H] [Algebra.FiniteType K H] :
    ∃ r : H, r - 1 ∈ RingHom.ker (Bialgebra.counitAlgHom K H).toRingHom ∧
      Algebra.Smooth K (Localization.Away r) := by
  let N : Ideal H := nilradical H
  let I : Ideal H := RingHom.ker (Bialgebra.counitAlgHom K H).toRingHom
  let : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing K H
  let : Algebra.Smooth K (H ⧸ N) := smooth_quotient_nilradical K H
  have hnil : IsNilpotent N := IsNoetherianRing.isNilpotent_nilradical H
  have hfg : N.FG := Ideal.fg_of_isNoetherianRing N
  have hle : N ≤ I ^ 2 := Bialgebra.nilradical_le_ker_counit_sq K H
  exact Algebra.Smooth.exists_sub_one_mem_and_smooth_away_of_quotient
    (K := K) (A := H) N I hnil hfg hle

open AlgebraicGeometry in
private lemma smooth_of_smooth_away_at_counit
    (K H : Type u) [fieldK : Field K] [CommRing H] [HopfAlgebra K H]
    [Algebra.FiniteType K H] (r : H)
    (hr : r - 1 ∈ RingHom.ker (Bialgebra.counitAlgHom K H).toRingHom)
    [Algebra.Smooth K (Localization.Away r)] : Algebra.Smooth K H := by
  have hunit :
      η[(Spec (.of H)).asOver (Spec (.of K))].left (IsLocalRing.closedPoint K)
        ∈ (Spec (.of H) ↘ Spec (.of K)).smoothLocus :=
    unit_mem_smoothLocus_of_smooth_away K H r hr
  have hspec : AlgebraicGeometry.Smooth
      (Spec.map (CommRingCat.ofHom (algebraMap K H))) :=
    @AlgebraicGeometry.smooth_of_unit_mem_smoothLocus K fieldK
      (Spec (.of H)) (Spec.map (CommRingCat.ofHom (algebraMap K H)))
      (show AlgebraicGeometry.LocallyOfFiniteType
          (Spec.map (CommRingCat.ofHom (algebraMap K H))) from
        AlgebraicGeometry.locallyOfFiniteType_specOverSpec (R := .of K) (A := .of H))
      (show GrpObj
          (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K H)))) from
        AlgebraicGeometry.instGrpObjSpecAsOverSpec (R := .of K) (A := .of H))
      hunit
  have hmap : (algebraMap K H).Smooth :=
    (HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Smooth)
      (φ := CommRingCat.ofHom (algebraMap K H))).mp hspec
  exact RingHom.smooth_algebraMap.mp hmap

private theorem smooth_aux
    (K H : Type u) [Field K] [CharZero K] [CommRing H]
    [HopfAlgebra K H] [Algebra.FiniteType K H] : Algebra.Smooth K H := by
  obtain ⟨r, hr, hs⟩ := exists_smooth_away_at_counit K H
  let : Algebra.Smooth K (Localization.Away r) := hs
  exact smooth_of_smooth_away_at_counit K H r hr

/-- A finite-type commutative Hopf algebra over a characteristic-zero field is smooth for
its given algebra structure (Cartier's theorem). -/
theorem smooth (K : Type u) (H : Type v) [Field K] [CharZero K] [CommRing H]
    [HopfAlgebra K H] [Algebra.FiniteType K H] : Algebra.Smooth K H := by
  let K' : Type (max u v) := ULift.{v} K
  let H' : Type (max u v) := ULift.{u} H
  let D : K' ≃+* K := ULift.ringEquiv
  let E : H' ≃+* H := ULift.ringEquiv
  let : HopfAlgebra K' H' := HopfAlgebra.ulift K H
  let : CharZero K' :=
    charZero_of_injective_ringHom (f := D.symm.toRingHom) D.symm.injective
  let hft : (algebraMap K' H').FiniteType := by
    have hmap : algebraMap K' H' =
        E.symm.toRingHom.comp ((algebraMap K H).comp D.toRingHom) := by
      ext k
      rfl
    rw [hmap]
    exact (RingHom.FiniteType.of_surjective E.symm.toRingHom E.symm.surjective).comp
      ((RingHom.finiteType_algebraMap.mpr
        (inferInstance : Algebra.FiniteType K H)).comp
          (RingHom.FiniteType.of_surjective D.toRingHom D.surjective))
  let : Algebra.FiniteType K' H' := RingHom.finiteType_algebraMap.mp hft
  let hs : Algebra.Smooth K' H' := smooth_aux K' H'
  let hl : (algebraMap K' H').Smooth := RingHom.smooth_algebraMap.mpr hs
  let hD : D.symm.toRingHom.Smooth := RingHom.Smooth.of_bijective D.symm.bijective
  let hE : E.toRingHom.Smooth := RingHom.Smooth.of_bijective E.bijective
  have hmap : E.toRingHom.comp
      ((algebraMap K' H').comp D.symm.toRingHom) = algebraMap K H := by
    ext k
    rfl
  apply RingHom.smooth_algebraMap.mp
  rw [← hmap]
  exact (hD.comp hl).comp hE

/-- A commutative Hopf algebra over a characteristic-zero field is reduced (Cartier's
theorem), by reduction to a finite-type Hopf subalgebra containing each nilpotent element. -/
theorem isReduced (K : Type u) (H : Type v) [Field K] [CharZero K] [CommRing H]
    [HopfAlgebra K H] : IsReduced H := by
  constructor
  intro x hx
  obtain ⟨A, hA, hAfin, hxA⟩ :=
    Subalgebra.exists_finiteType_isHopfSubalgebra_of_finite_of_commutative
      (K := K) (H := H) (Set.finite_singleton x)
  let : HopfAlgebra K A := A.hopfAlgebra hA
  let : Algebra.FiniteType K A := hAfin
  let : Algebra.Smooth K A := smooth K A
  let : IsReduced A := Algebra.Smooth.isReduced_of_isDomain K A
  let a : A := ⟨x, hxA (by simp)⟩
  have ha : IsNilpotent a :=
    (IsNilpotent.map_iff (f := A.val) (r := a) Subtype.val_injective).mp hx
  exact congrArg (fun y : A => (y : H)) ha.eq_zero

end HopfAlgebra
