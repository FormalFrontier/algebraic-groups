/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AlgebraicGroups.GroupScheme.Additive
import AlgebraicGroups.Algebra.PolynomialRationalPointHeight
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Ideal.Height

/-!
# Unit-stalk dimensions of a field point and the additive line

Over every field, the terminal group scheme has unit-stalk and topological
Krull dimension zero, and the additive line has both dimensions one. The
stalks here are evaluated at the canonical unit, using the group structures
on spectra supplied by the self Hopf algebra and the additive coordinate ring.

The additive unit is the prime obtained from the kernel of evaluation at zero
under the polynomial coordinate presentation. In particular its stalk is the
localization at that prime, not the principal open where the coordinate is
invertible and not the residue field.

## References

These examples use the Mathlib community's affine group, stalk-localization,
height-transport and polynomial-dimension APIs, and this library's additive
coordinate presentation and rational-point height theorem.
-/

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

universe u

private theorem one_spec_asOver_spec_apply {R A : CommRingCat.{u}} [Bialgebra R A]
    (x : Spec R) :
    η[(Spec A).asOver (Spec R)].left x =
      PrimeSpectrum.comap (Bialgebra.counitAlgHom R A).toRingHom x := by
  exact (congrArg (fun f : Spec R ⟶ Spec A => f x)
    (one_spec_asOver_spec_left (R := R) (A := A))).trans (Spec.map_apply _ _)

variable (K : Type u) [Field K]

/-- The self Hopf algebra represents the terminal group over the field. -/
private abbrev fieldPointGroup : Grp (Over (Spec (.of K))) :=
  ⟨(Spec (.of K)).asOver (Spec (.of K))⟩

private instance fieldPointGroup_locallyOfFiniteType :
    LocallyOfFiniteType (fieldPointGroup K).X.hom :=
  inferInstanceAs (LocallyOfFiniteType (Spec (.of K) ↘ Spec (.of K)))

-- Expose the bundled group structure at the morphism's `Over.mk` presentation.
local instance fieldPointGroup_overMk_grpObj :
    GrpObj (Over.mk (fieldPointGroup K).X.hom) :=
  (fieldPointGroup K).grp

private theorem fieldPointGroup_unit :
    η[Over.mk (fieldPointGroup K).X.hom].left (IsLocalRing.closedPoint K) =
      IsLocalRing.closedPoint K := by
  change η[(Spec (.of K)).asOver (Spec (.of K))].left _ = _
  rw [one_spec_asOver_spec_left, Bialgebra.counitAlgHom_self]
  change Spec.map (𝟙 (CommRingCat.of K)) (IsLocalRing.closedPoint K) =
    IsLocalRing.closedPoint K
  rw [Spec.map_id]
  rfl

/-- The local ring at the canonical unit of the terminal group has dimension zero. -/
private theorem fieldPointGroup_unit_stalk_ringKrullDim :
    ringKrullDim ((fieldPointGroup K).X.left.presheaf.stalk
      (η[Over.mk (fieldPointGroup K).X.hom].left (IsLocalRing.closedPoint K))) = 0 := by
  rw [fieldPointGroup_unit K]
  change ringKrullDim ((Spec (.of K)).presheaf.stalk (IsLocalRing.closedPoint K)) = 0
  calc
    _ = ringKrullDim (Localization.AtPrime (IsLocalRing.closedPoint K).asIdeal) :=
      ringKrullDim_eq_of_ringEquiv
        (Spec.stalkIso (.of K) (IsLocalRing.closedPoint K)).commRingCatIsoToRingEquiv
    _ = ((IsLocalRing.closedPoint K).asIdeal.height : WithBot ℕ∞) :=
      IsLocalization.AtPrime.ringKrullDim_eq_height _ _
    _ = 0 := by simp [IsLocalRing.closedPoint, IsLocalRing.maximalIdeal_eq_bot]

/-- The terminal group over a field has topological Krull dimension zero. -/
private theorem fieldPointGroup_topologicalKrullDim :
    topologicalKrullDim (fieldPointGroup K).X.left = 0 := by
  change topologicalKrullDim (PrimeSpectrum K) = 0
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ringKrullDim_eq_zero_of_field]

/-- The terminal group's local dimension at the unit equals its topological dimension. -/
private theorem fieldPointGroup_unit_stalk_eq_topologicalKrullDim :
    ringKrullDim ((fieldPointGroup K).X.left.presheaf.stalk
      (η[Over.mk (fieldPointGroup K).X.hom].left (IsLocalRing.closedPoint K))) =
      topologicalKrullDim (fieldPointGroup K).X.left := by
  rw [fieldPointGroup_unit_stalk_ringKrullDim K, fieldPointGroup_topologicalKrullDim K]

private theorem polynomial_eval_zero_height :
    (RingHom.ker (Polynomial.evalRingHom (0 : K))).height = 1 := by
  let e := MvPolynomial.uniqueAlgEquiv K Unit
  have hker : RingHom.ker (MvPolynomial.eval (fun _ : Unit ↦ (0 : K))) =
      (RingHom.ker (Polynomial.evalRingHom (0 : K))).comap e.toRingHom := by
    ext p
    change (MvPolynomial.eval (fun _ : Unit ↦ (0 : K)) p = 0) ↔
      Polynomial.eval (0 : K) (e p) = 0
    have he : Polynomial.eval (0 : K) (e p) =
        MvPolynomial.eval (fun _ : Unit ↦ (0 : K)) p :=
      MvPolynomial.eval₂_const_uniqueAlgEquiv
        (φ := RingHom.id K) (a := (0 : K))
    rw [he]
  calc
    _ = ((RingHom.ker (Polynomial.evalRingHom (0 : K))).comap e.toRingHom).height :=
      (RingEquiv.height_comap e.toRingEquiv _).symm
    _ = (RingHom.ker (MvPolynomial.eval (fun _ : Unit ↦ (0 : K)))).height := by
      rw [← hker]
    _ = 1 := by
      simpa using MvPolynomial.height_ker_eval K Unit (fun _ ↦ (0 : K))

private theorem additiveGroup_counit_apply (a : additiveGroupCoordinateRing K) :
    Bialgebra.counitAlgHom K (additiveGroupCoordinateRing K) a =
      Polynomial.eval (0 : K) (additiveGroupCoordinateAlgEquiv K a) := by
  let e := additiveGroupCoordinateAlgEquiv K
  have hx : e.symm Polynomial.X = additiveGroupCoordinate K := by
    apply e.injective
    simp [e]
  have h : (Bialgebra.counitAlgHom K (additiveGroupCoordinateRing K)).comp
      e.symm.toAlgHom = Polynomial.aeval (R := K) (0 : K) := by
    apply Polynomial.algHom_ext
    change Bialgebra.counitAlgHom K (additiveGroupCoordinateRing K)
      (e.symm Polynomial.X) = (Polynomial.aeval (R := K) (0 : K)) Polynomial.X
    rw [hx, Polynomial.aeval_X]
    exact additiveGroupCoordinate_counit K
  have ha := AlgHom.congr_fun h (e a)
  simpa using ha

private theorem additiveGroup_counit_kernel :
    RingHom.ker (Bialgebra.counitAlgHom K (additiveGroupCoordinateRing K)) =
      (RingHom.ker (Polynomial.evalRingHom (0 : K))).comap
        (additiveGroupCoordinateAlgEquiv K).toRingHom := by
  ext a
  change (Bialgebra.counitAlgHom K (additiveGroupCoordinateRing K) a = 0) ↔
    Polynomial.eval (0 : K) (additiveGroupCoordinateAlgEquiv K a) = 0
  rw [additiveGroup_counit_apply K]

private theorem additiveGroup_counit_kernel_height :
    (RingHom.ker (Bialgebra.counitAlgHom K (additiveGroupCoordinateRing K))).height = 1 := by
  rw [additiveGroup_counit_kernel K]
  exact (RingEquiv.height_comap (additiveGroupCoordinateAlgEquiv K).toRingEquiv _).trans
    (polynomial_eval_zero_height K)

-- Use precisely the group structure stored in the existing additive group scheme.
local instance additiveGroupUnderlyingScheme_overMk_grpObj :
    GrpObj (Over.mk (additiveGroupUnderlyingScheme K).hom) :=
  (additiveGroupScheme K).grp

/-- The canonical unit prime is the counit kernel, hence evaluation at zero
in the polynomial coordinate presentation. -/
private theorem additiveGroup_unit_asIdeal :
    (η[Over.mk (additiveGroupUnderlyingScheme K).hom].left
      (IsLocalRing.closedPoint K)).asIdeal =
      RingHom.ker (Bialgebra.counitAlgHom K (additiveGroupCoordinateRing K)) := by
  change (η[(Spec (.of (additiveGroupCoordinateRing K))).asOver (Spec (.of K))].left
    (IsLocalRing.closedPoint K)).asIdeal = _
  calc
    _ = (IsLocalRing.closedPoint K).asIdeal.comap
        (Bialgebra.counitAlgHom K (additiveGroupCoordinateRing K)).toRingHom :=
      (congrArg PrimeSpectrum.asIdeal
        (one_spec_asOver_spec_apply (R := .of K) (A := .of (additiveGroupCoordinateRing K))
          (IsLocalRing.closedPoint K))).trans (PrimeSpectrum.comap_asIdeal _ _)
    _ = _ := by
      change (IsLocalRing.maximalIdeal K).comap
        (Bialgebra.counitAlgHom K (additiveGroupCoordinateRing K)).toRingHom = _
      rw [IsLocalRing.maximalIdeal_eq_bot]
      rfl

/-- The local ring at the canonical unit of the additive line has dimension one. -/
private theorem additiveGroup_unit_stalk_ringKrullDim :
    ringKrullDim ((additiveGroupUnderlyingScheme K).left.presheaf.stalk
      (η[Over.mk (additiveGroupUnderlyingScheme K).hom].left
        (IsLocalRing.closedPoint K))) = 1 := by
  let p : PrimeSpectrum (additiveGroupCoordinateRing K) :=
    η[Over.mk (additiveGroupUnderlyingScheme K).hom].left (IsLocalRing.closedPoint K)
  calc
    _ = ringKrullDim (Localization.AtPrime p.asIdeal) :=
      ringKrullDim_eq_of_ringEquiv
        (Spec.stalkIso (.of (additiveGroupCoordinateRing K)) p).commRingCatIsoToRingEquiv
    _ = (p.asIdeal.height : WithBot ℕ∞) :=
      IsLocalization.AtPrime.ringKrullDim_eq_height _ _
    _ = 1 := by
      have hp : p.asIdeal =
          RingHom.ker (Bialgebra.counitAlgHom K (additiveGroupCoordinateRing K)) :=
        additiveGroup_unit_asIdeal K
      rw [hp, additiveGroup_counit_kernel_height K]
      exact WithBot.coe_one

/-- The additive line has topological Krull dimension one over every field. -/
private theorem additiveGroup_topologicalKrullDim :
    topologicalKrullDim (additiveGroupUnderlyingScheme K).left = 1 := by
  change topologicalKrullDim (PrimeSpectrum (additiveGroupCoordinateRing K)) = 1
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    ringKrullDim_eq_of_ringEquiv (additiveGroupCoordinateAlgEquiv K).toRingEquiv,
    Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp

/-- The additive line's local dimension at the unit equals its topological dimension. -/
private theorem additiveGroup_unit_stalk_eq_topologicalKrullDim :
    ringKrullDim ((additiveGroupUnderlyingScheme K).left.presheaf.stalk
      (η[Over.mk (additiveGroupUnderlyingScheme K).hom].left
        (IsLocalRing.closedPoint K))) =
      topologicalKrullDim (additiveGroupUnderlyingScheme K).left := by
  rw [additiveGroup_unit_stalk_ringKrullDim K, additiveGroup_topologicalKrullDim K]

end AlgebraicGeometry
