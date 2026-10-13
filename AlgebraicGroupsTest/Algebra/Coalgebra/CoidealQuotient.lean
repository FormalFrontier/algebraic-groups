/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.Quotient
public import AlgebraicGroups.GroupScheme.AdditivePowerQuotient
public import AlgebraicGroups.GroupScheme.InfinitesimalAdditive
public import AlgebraicGroupsTest.Algebra.Coalgebra.CounitRange
public import AlgebraicGroupsTest.Algebra.Coalgebra.FiniteSubcoalgebra
public import Mathlib.Algebra.Polynomial.Monic

/-!
# Coalgebra morphisms on coideal quotients

`Submodule.liftQCoalgHom` descends a coalgebra morphism vanishing on a coideal;
`Submodule.mapQCoalgHom` descends a morphism carrying one coideal into another.
The examples use their underlying-linear-map, representative, projection,
uniqueness, identity and composition APIs. Preservation of the coalgebra
structure requires only `CoalgebraStruct`, with independent universes for the
source and target modules.

Over `Polynomial (ZMod 2)`, the additive coordinate coalgebra has the coideals
`(a ^ 4) < (a ^ 2)`. The square of the coordinate survives in the fourth-power
quotient, but is killed by the comparison to the square quotient. Both the
lift of the square projection and the quotient map of the source identity
construct this noninjective comparison, with the same scalar readbacks.
The quotient coalgebras are the canonical full coalgebras supplied by the
characteristic-power Hopf ideals. Polynomial presentations are used only to
prove nonvanishing in the underlying algebra, not to transport coalgebra
structures.

The counit of the full additive coordinate coalgebra and of its two quotients
has full scalar range. In contrast, the ideal `(3)` in `ZMod 6` is a full
coalgebra with proper nonzero counit range and injective scalar inclusion.
Surjective coalgebra morphisms preserve counit ranges; injective ones need
not reflect counit surjectivity. Lifting a quotient projection gives the
identity, and lifting the counit gives the quotient counit. Quotient
equivalence transport is not treated here.

## References

Mathlib supplies coalgebra morphisms, coideals, quotient structures and the
linear quotient universal property. The idempotent-ideal coalgebras and additive
characteristic-power Hopf ideals are supplied by
`AlgebraicGroups.Algebra.Coalgebra.IdempotentIdeal` and
`AlgebraicGroups.GroupScheme.InfinitesimalAdditive`. The algebra-only presentation
and quotient nonvanishing route use
`AlgebraicGroups.GroupScheme.AdditivePowerQuotient` and Mathlib `AdjoinRoot`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w z

open Coalgebra

section Descent

variable {R : Type u} [CommRing R]
variable {C : Type v} [AddCommGroup C] [Module R C] [CoalgebraStruct R C]
variable {D : Type w} [AddCommGroup D] [Module R D] [CoalgebraStruct R D]
variable {E : Type z} [AddCommGroup E] [Module R E] [CoalgebraStruct R E]

example (I : Submodule R C) [I.IsCoideal] (f : C →ₗc[R] D)
    (h : I ≤ LinearMap.ker f.toLinearMap) :
    (I.liftQCoalgHom f h).toLinearMap = I.liftQ f.toLinearMap h ∧
      (∀ x : C, I.liftQCoalgHom f h (Submodule.Quotient.mk (p := I) x) = f x) ∧
      (I.liftQCoalgHom f h).comp (Coalgebra.Quotient.mkQCoalgHom I) = f := by
  refine ⟨?_, ?_, ?_⟩
  · exact Submodule.liftQCoalgHom_toLinearMap I f h
  · intro x
    simp only [Submodule.liftQCoalgHom_mk]
  · exact Submodule.liftQCoalgHom_comp_mkQCoalgHom I f h

example (I : Submodule R C) [I.IsCoideal] (f : C →ₗc[R] D)
    (h : I ≤ LinearMap.ker f.toLinearMap) (g : (C ⧸ I) →ₗc[R] D)
    (hg : g.comp (Coalgebra.Quotient.mkQCoalgHom I) = f) :
    g = I.liftQCoalgHom f h := by
  exact Submodule.liftQCoalgHom_unique I f h g hg

example (I : Submodule R C) (J : Submodule R D) [I.IsCoideal] [J.IsCoideal]
    (f : C →ₗc[R] D) (h : I ≤ J.comap f.toLinearMap) :
    (I.mapQCoalgHom J f h).toLinearMap = I.mapQ J f.toLinearMap h ∧
      (∀ x : C, I.mapQCoalgHom J f h (Submodule.Quotient.mk (p := I) x) =
        Submodule.Quotient.mk (p := J) (f x)) ∧
      (I.mapQCoalgHom J f h).comp (Coalgebra.Quotient.mkQCoalgHom I) =
        (Coalgebra.Quotient.mkQCoalgHom J).comp f := by
  refine ⟨?_, ?_, ?_⟩
  · exact Submodule.mapQCoalgHom_toLinearMap I J f h
  · intro x
    simp only [Submodule.mapQCoalgHom_mk]
  · exact Submodule.mapQCoalgHom_comp_mkQCoalgHom I J f h

example (I : Submodule R C) [I.IsCoideal] :
    I.mapQCoalgHom I (CoalgHom.id R C) (Submodule.comap_id I).symm.le =
      CoalgHom.id R (C ⧸ I) := by
  apply Submodule.mapQCoalgHom_id

example (I : Submodule R C) (J : Submodule R D) (L : Submodule R E)
    [I.IsCoideal] [J.IsCoideal] [L.IsCoideal] (f : C →ₗc[R] D) (g : D →ₗc[R] E)
    (hf : I ≤ J.comap f.toLinearMap) (hg : J ≤ L.comap g.toLinearMap) :
    I.mapQCoalgHom L (g.comp f) (hf.trans (Submodule.comap_mono hg)) =
      (J.mapQCoalgHom L g hg).comp (I.mapQCoalgHom J f hf) := by
  apply Submodule.mapQCoalgHom_comp

end Descent

section CounitRanges

variable {R : Type u} [CommSemiring R]
variable {C : Type v} [AddCommMonoid C] [Module R C] [CoalgebraStruct R C]
variable {D : Type w} [AddCommMonoid D] [Module R D] [CoalgebraStruct R D]

example (f : C →ₗc[R] D) :
    LinearMap.range (counit (R := R) (A := C)) ≤
      LinearMap.range (counit (R := R) (A := D)) := by
  rw [← f.counit_comp]
  exact LinearMap.range_comp_le_range f.toLinearMap (counit (R := R) (A := D))

example (f : C →ₗc[R] D) (hf : Function.Surjective f) :
    LinearMap.range (counit (R := R) (A := C)) =
      LinearMap.range (counit (R := R) (A := D)) := by
  calc
    LinearMap.range (counit (R := R) (A := C)) =
        LinearMap.range ((counit (R := R) (A := D)).comp f.toLinearMap) :=
      congrArg LinearMap.range f.counit_comp.symm
    _ = LinearMap.range (counit (R := R) (A := D)) :=
      LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hf)

end CounitRanges

section ProperInclusion

local notation "D₆" => Ideal.span ({(3 : ZMod 6)} : Set (ZMod 6))

attribute [local instance] CoalgebraExamples.zmodSixIdealCoalgebra

-- Injective scalar inclusion does not reflect surjectivity of the source counit.
example :
    Function.Injective (Coalgebra.counitCoalgHom (ZMod 6) D₆) ∧
      (Coalgebra.counitCoalgHom (ZMod 6) D₆).toLinearMap = (D₆).subtype ∧
      counit (R := ZMod 6) (A := ZMod 6) = LinearMap.id ∧
      Function.Surjective (counit (R := ZMod 6) (A := ZMod 6)) ∧
      LinearMap.range (counit (R := ZMod 6) (A := D₆)) = D₆ ∧
      LinearMap.range (counit (R := ZMod 6) (A := D₆)) ≠ ⊥ ∧
      LinearMap.range (counit (R := ZMod 6) (A := D₆)) ≠ ⊤ ∧
      ¬ Function.Surjective (counit (R := ZMod 6) (A := D₆)) := by
  have hc : counit (R := ZMod 6) (A := D₆) = (D₆).subtype :=
    CoalgebraExamples.zmod_six_three_idempotent.coalgebraSpan_counit
  have hrange : LinearMap.range (counit (R := ZMod 6) (A := D₆)) = D₆ := by
    rw [hc, Submodule.range_subtype]
  have hproper := CoalgebraExamples.zmod_six_ideal_counit_range_ne_top
  refine ⟨?_, ?_, ?_, ?_, hrange, ?_, hproper, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    simpa only [Coalgebra.counitCoalgHom_apply, hc, Submodule.subtype_apply] using hxy
  · rw [CoalgHom.toLinearMap_eq_coe, Coalgebra.counitCoalgHom_toLinearMap]
    exact hc
  · exact LinearMap.ext fun r => CommSemiring.counit_apply (ZMod 6) r
  · exact fun r => ⟨r, CommSemiring.counit_apply (ZMod 6) r⟩
  · rw [hrange, ne_eq, Ideal.span_singleton_eq_bot]
    decide
  · intro hsurj
    exact hproper (LinearMap.range_eq_top.mpr hsurj)

example (d : D₆) :
    counit (R := ZMod 6) d = (d : ZMod 6) ∧
      counit (R := ZMod 6) (Coalgebra.counitCoalgHom (ZMod 6) D₆ d) =
        (d : ZMod 6) := by
  have hc : counit (R := ZMod 6) (A := D₆) = (D₆).subtype :=
    CoalgebraExamples.zmod_six_three_idempotent.coalgebraSpan_counit
  simp only [hc, Submodule.subtype_apply, Coalgebra.counitCoalgHom_apply,
    CommSemiring.counit_apply, and_self]

example : counit (R := ZMod 6)
    (Coalgebra.counitCoalgHom (ZMod 6) D₆ (Ideal.spanSingletonGenerator 3)) = 3 := by
  simp only [Coalgebra.counitCoalgHom_apply, CommSemiring.counit_apply]
  exact CoalgebraExamples.zmod_six_three_idempotent.coalgebraSpan_counit_apply _

end ProperInclusion

section AdditivePowerQuotients

open AlgebraicGeometry

local notation "K₂" => Polynomial (ZMod 2)
local notation "C₂" => additiveGroupCoordinateRing K₂
local notation "a" => additiveGroupCoordinate K₂
local notation "I₄" => Submodule.restrictScalars K₂ (infinitesimalAdditiveIdeal K₂ 2 2)
local notation "I₂" => Submodule.restrictScalars K₂ (infinitesimalAdditiveIdeal K₂ 2 1)
local notation "q₄" => Coalgebra.Quotient.mkQCoalgHom (R := K₂) I₄
local notation "q₂" => Coalgebra.Quotient.mkQCoalgHom (R := K₂) I₂

-- Restriction of scalars preserves containment of the coordinate-power ideals.
private theorem fourth_ideal_le_square_ideal : I₄ ≤ I₂ := by
  apply Submodule.restrictScalars_mono K₂
  change Ideal.span {a ^ 4} ≤ Ideal.span {a ^ 2}
  rw [← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow]
  exact Ideal.pow_le_pow_right (by decide : 2 ≤ 4)

-- Use the algebra-only power-quotient presentation at degree 2 < 4.
private theorem fourth_quotient_square_ne_zero : q₄ (a ^ 2) ≠ 0 := by
  have hpoly : AdjoinRoot.mk ((Polynomial.X : Polynomial K₂) ^ 4)
      ((Polynomial.X : Polynomial K₂) ^ 2) ≠ 0 :=
    AdjoinRoot.mk_ne_zero_of_natDegree_lt (Polynomial.monic_X_pow 4)
      (Polynomial.monic_X_pow 2).ne_zero (by simp)
  intro hzero
  apply hpoly
  have hIdeal : infinitesimalAdditiveIdeal K₂ 2 2 = additivePowerIdeal K₂ 4 := by
    simp [infinitesimalAdditiveIdeal, additivePowerIdeal]
  have hzero' : Ideal.Quotient.mk (infinitesimalAdditiveIdeal K₂ 2 2) (a ^ 2) = 0 := by
    simpa only [Coalgebra.Quotient.mkQCoalgHom_apply,
      Submodule.Quotient.restrictScalarsEquiv_mk, Ideal.Quotient.mk_eq_mk, map_zero] using
      congrArg (Submodule.Quotient.restrictScalarsEquiv K₂
        (infinitesimalAdditiveIdeal K₂ 2 2)) hzero
  -- Transport the whole equality, including its quotient type, along the ideal equality.
  rw [hIdeal] at hzero'
  simpa only [additivePowerCoordinateAlgEquiv_mk, map_pow,
    additiveGroupCoordinateAlgEquiv_coordinate, map_zero] using
      congrArg (additivePowerCoordinateAlgEquiv K₂ 4) hzero'

private theorem square_coordinate_mem_square_ideal : a ^ 2 ∈ I₂ := by
  change a ^ 2 ∈ Ideal.span {a ^ 2}
  exact Ideal.mem_span_singleton_self _

private theorem fourth_ideal_lt_square_ideal : I₄ < I₂ := by
  refine lt_of_le_of_ne fourth_ideal_le_square_ideal ?_
  intro h
  apply fourth_quotient_square_ne_zero
  apply (Submodule.Quotient.mk_eq_zero I₄).mpr
  rw [h]
  exact square_coordinate_mem_square_ideal

private theorem square_projection_square_eq_zero : q₂ (a ^ 2) = 0 := by
  simpa only [Coalgebra.Quotient.mkQCoalgHom_apply] using
    (Submodule.Quotient.mk_eq_zero I₂).mpr square_coordinate_mem_square_ideal

private theorem square_coordinate_ne_zero : a ^ 2 ≠ 0 := by
  have hpoly : ((Polynomial.X : Polynomial K₂) ^ 2) ≠ 0 :=
    (Polynomial.monic_X_pow 2).ne_zero
  intro hzero
  apply hpoly
  simpa only [map_pow, additiveGroupCoordinateAlgEquiv_coordinate, map_zero] using
    congrArg (additiveGroupCoordinateAlgEquiv K₂) hzero

private theorem square_quotient_counit_scalar (r : K₂) :
    counit (R := K₂) (q₂ (algebraMap K₂ C₂ r)) = r := by
  simp only [CoalgHomClass.counit_comp_apply, Bialgebra.counit_algebraMap]

private theorem fourth_quotient_counit_scalar (r : K₂) :
    counit (R := K₂) (q₄ (algebraMap K₂ C₂ r)) = r := by
  simp only [CoalgHomClass.counit_comp_apply, Bialgebra.counit_algebraMap]

private theorem square_quotient_one_ne_zero : q₂ (1 : C₂) ≠ 0 := by
  have hc : counit (R := K₂) (q₂ (1 : C₂)) = (1 : K₂) := by
    simpa only [map_one] using square_quotient_counit_scalar 1
  intro hzero
  exact one_ne_zero (hc.symm.trans (by rw [hzero, map_zero]))

private theorem fourth_quotient_one_ne_zero : q₄ (1 : C₂) ≠ 0 := by
  have hc : counit (R := K₂) (q₄ (1 : C₂)) = (1 : K₂) := by
    simpa only [map_one] using fourth_quotient_counit_scalar 1
  intro hzero
  exact one_ne_zero (hc.symm.trans (by rw [hzero, map_zero]))

-- The square is a nonzero kernel element, while both counits have full scalar image.
example :
    a ^ 2 ≠ 0 ∧ a ^ 2 ∈ I₂ ∧ q₂ (a ^ 2) = 0 ∧ ¬ Function.Injective q₂ ∧
      I₂ ≠ ⊥ ∧ I₂ ≠ ⊤ ∧ q₂ (1 : C₂) ≠ 0 ∧
      LinearMap.range (counit (R := K₂) (A := C₂)) = ⊤ ∧
      LinearMap.range (counit (R := K₂) (A := C₂ ⧸ I₂)) = ⊤ := by
  refine ⟨square_coordinate_ne_zero, square_coordinate_mem_square_ideal,
    square_projection_square_eq_zero, ?_, ?_, ?_, square_quotient_one_ne_zero, ?_, ?_⟩
  · intro hinj
    apply square_coordinate_ne_zero
    apply hinj
    rw [square_projection_square_eq_zero, map_zero]
  · intro hbot
    apply square_coordinate_ne_zero
    have hmem := square_coordinate_mem_square_ideal
    rw [hbot, Submodule.mem_bot] at hmem
    exact hmem
  · intro htop
    apply square_quotient_one_ne_zero
    apply (Submodule.Quotient.mk_eq_zero I₂).mpr
    rw [htop]
    exact Submodule.mem_top
  · exact LinearMap.range_eq_top.mpr (Bialgebra.counit_surjective (R := K₂) (A := C₂))
  · apply LinearMap.range_eq_top.mpr
    intro r
    exact ⟨q₂ (algebraMap K₂ C₂ r), square_quotient_counit_scalar r⟩

-- The universal boundary cases use the lift's uniqueness API.
example :
    (I₂).liftQCoalgHom q₂ (Submodule.ker_mkQ I₂).symm.le =
        CoalgHom.id K₂ (C₂ ⧸ I₂) ∧
      (I₂).liftQCoalgHom (Coalgebra.counitCoalgHom K₂ C₂)
          (Submodule.IsCoideal.counit_eq_zero (I := I₂)) =
        Coalgebra.counitCoalgHom K₂ (C₂ ⧸ I₂) ∧
      ((I₂).liftQCoalgHom (Coalgebra.counitCoalgHom K₂ C₂)
          (Submodule.IsCoideal.counit_eq_zero (I := I₂))).comp
        ((I₂).liftQCoalgHom q₂ (Submodule.ker_mkQ I₂).symm.le) =
          Coalgebra.counitCoalgHom K₂ (C₂ ⧸ I₂) := by
  have hprojection : (I₂).liftQCoalgHom q₂ (Submodule.ker_mkQ I₂).symm.le =
      CoalgHom.id K₂ (C₂ ⧸ I₂) := by
    symm
    apply Submodule.liftQCoalgHom_unique
    exact CoalgHom.id_comp q₂
  have hcounit : (I₂).liftQCoalgHom (Coalgebra.counitCoalgHom K₂ C₂)
      (Submodule.IsCoideal.counit_eq_zero (I := I₂)) =
        Coalgebra.counitCoalgHom K₂ (C₂ ⧸ I₂) := by
    symm
    apply Submodule.liftQCoalgHom_unique
    apply CoalgHom.ext
    intro x
    simp only [CoalgHom.comp_apply, Coalgebra.counitCoalgHom_apply,
      CoalgHomClass.counit_comp_apply]
  refine ⟨hprojection, hcounit, ?_⟩
  rw [hprojection, hcounit]
  exact CoalgHom.comp_id _

example :
    I₄ < I₂ ∧ q₄ (a ^ 2) ≠ 0 ∧ q₂ (a ^ 2) = 0 ∧ q₄ (1 : C₂) ≠ 0 ∧
      LinearMap.range (counit (R := K₂) (A := C₂)) = ⊤ ∧
      LinearMap.range (counit (R := K₂) (A := C₂ ⧸ I₄)) = ⊤ ∧
      LinearMap.range (counit (R := K₂) (A := C₂ ⧸ I₂)) = ⊤ := by
  refine ⟨fourth_ideal_lt_square_ideal, fourth_quotient_square_ne_zero,
    square_projection_square_eq_zero, fourth_quotient_one_ne_zero, ?_, ?_, ?_⟩
  · exact LinearMap.range_eq_top.mpr (Bialgebra.counit_surjective (R := K₂) (A := C₂))
  · apply LinearMap.range_eq_top.mpr
    intro r
    exact ⟨q₄ (algebraMap K₂ C₂ r), fourth_quotient_counit_scalar r⟩
  · apply LinearMap.range_eq_top.mpr
    intro r
    exact ⟨q₂ (algebraMap K₂ C₂ r), square_quotient_counit_scalar r⟩

/-- The fourth-power coideal is strictly smaller than the square coideal in the
additive coordinate coalgebra over `Polynomial (ZMod 2)`. Both quotient-morphism
constructions give a noninjective comparison: the surviving coordinate square
maps to zero. -/
theorem CoalgebraTest.additivePowerQuotientComparison_not_injective :
    let hLift : I₄ ≤ LinearMap.ker (q₂).toLinearMap := by
      exact (fourth_ideal_le_square_ideal).trans (Submodule.ker_mkQ I₂).symm.le
    let hMap : I₄ ≤ (I₂).comap (CoalgHom.id K₂ C₂).toLinearMap := by
      exact (fourth_ideal_le_square_ideal).trans (Submodule.comap_id I₂).symm.le
    I₄ < I₂ ∧
      ¬ Function.Injective ((I₄).liftQCoalgHom q₂ hLift) ∧
      ¬ Function.Injective ((I₄).mapQCoalgHom I₂ (CoalgHom.id K₂ C₂) hMap) := by
  refine ⟨fourth_ideal_lt_square_ideal, ?_, ?_⟩
  · intro hinj
    apply fourth_quotient_square_ne_zero
    apply hinj
    rw [map_zero]
    simpa only [Coalgebra.Quotient.mkQCoalgHom_apply, Submodule.liftQCoalgHom_mk] using
      square_projection_square_eq_zero
  · intro hinj
    apply fourth_quotient_square_ne_zero
    apply hinj
    rw [map_zero]
    simpa only [Coalgebra.Quotient.mkQCoalgHom_apply, Submodule.mapQCoalgHom_mk,
      CoalgHom.id_apply] using square_projection_square_eq_zero

-- The same comparison is constructed as a lift and as a map between distinct quotients.
example :
    let hLift : I₄ ≤ LinearMap.ker (q₂).toLinearMap :=
      (fourth_ideal_le_square_ideal).trans (Submodule.ker_mkQ I₂).symm.le
    let hMap : I₄ ≤ (I₂).comap (CoalgHom.id K₂ C₂).toLinearMap :=
      (fourth_ideal_le_square_ideal).trans (Submodule.comap_id I₂).symm.le
    let comparisonLift := (I₄).liftQCoalgHom q₂ hLift
    let comparisonMap := (I₄).mapQCoalgHom I₂ (CoalgHom.id K₂ C₂) hMap
    comparisonLift = comparisonMap ∧
      comparisonLift.toLinearMap = (I₄).liftQ (q₂).toLinearMap hLift ∧
      comparisonMap.toLinearMap = (I₄).mapQ I₂ (CoalgHom.id K₂ C₂).toLinearMap hMap ∧
      comparisonLift.comp q₄ = q₂ ∧ comparisonMap.comp q₄ = q₂ ∧
      (∀ x : C₂, comparisonLift (q₄ x) = q₂ x ∧ comparisonMap (q₄ x) = q₂ x) ∧
      comparisonLift (0 : C₂ ⧸ I₄) = 0 ∧ comparisonMap (0 : C₂ ⧸ I₄) = 0 ∧
      comparisonLift (q₄ (a ^ 2)) = 0 ∧ comparisonMap (q₄ (a ^ 2)) = 0 ∧
      ¬ Function.Injective comparisonLift ∧ ¬ Function.Injective comparisonMap ∧
      (∀ r : K₂, counit (R := K₂) (comparisonLift (q₄ (algebraMap K₂ C₂ r))) = r ∧
        counit (R := K₂) (comparisonMap (q₄ (algebraMap K₂ C₂ r))) = r) := by
  let hLift : I₄ ≤ LinearMap.ker (q₂).toLinearMap :=
    (fourth_ideal_le_square_ideal).trans (Submodule.ker_mkQ I₂).symm.le
  let hMap : I₄ ≤ (I₂).comap (CoalgHom.id K₂ C₂).toLinearMap :=
    (fourth_ideal_le_square_ideal).trans (Submodule.comap_id I₂).symm.le
  let comparisonLift := (I₄).liftQCoalgHom q₂ hLift
  let comparisonMap := (I₄).mapQCoalgHom I₂ (CoalgHom.id K₂ C₂) hMap
  have hMapComp : comparisonMap.comp q₄ = q₂ := by
    calc
      comparisonMap.comp q₄ = (q₂).comp (CoalgHom.id K₂ C₂) :=
        Submodule.mapQCoalgHom_comp_mkQCoalgHom I₄ I₂ (CoalgHom.id K₂ C₂) hMap
      _ = q₂ := CoalgHom.comp_id q₂
  have hEq : comparisonLift = comparisonMap :=
    (Submodule.liftQCoalgHom_unique I₄ q₂ hLift comparisonMap hMapComp).symm
  have hAction : ∀ x : C₂, comparisonLift (q₄ x) = q₂ x ∧
      comparisonMap (q₄ x) = q₂ x := by
    intro x
    constructor
    · simp only [comparisonLift, Coalgebra.Quotient.mkQCoalgHom_apply,
        Submodule.liftQCoalgHom_mk]
    · simp only [comparisonMap, Coalgebra.Quotient.mkQCoalgHom_apply,
        Submodule.mapQCoalgHom_mk, CoalgHom.id_apply]
  refine ⟨hEq, ?_, ?_, ?_, hMapComp, hAction, map_zero comparisonLift,
    map_zero comparisonMap, ?_, ?_,
    CoalgebraTest.additivePowerQuotientComparison_not_injective.2.1,
    CoalgebraTest.additivePowerQuotientComparison_not_injective.2.2, ?_⟩
  · exact Submodule.liftQCoalgHom_toLinearMap I₄ q₂ hLift
  · exact Submodule.mapQCoalgHom_toLinearMap I₄ I₂ (CoalgHom.id K₂ C₂) hMap
  · exact Submodule.liftQCoalgHom_comp_mkQCoalgHom I₄ q₂ hLift
  · rw [(hAction (a ^ 2)).1, square_projection_square_eq_zero]
  · rw [(hAction (a ^ 2)).2, square_projection_square_eq_zero]
  · intro r
    constructor
    · rw [(hAction (algebraMap K₂ C₂ r)).1]
      exact square_quotient_counit_scalar r
    · rw [(hAction (algebraMap K₂ C₂ r)).2]
      exact square_quotient_counit_scalar r

end AdditivePowerQuotients
