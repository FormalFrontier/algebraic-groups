/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.Unitriangular
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Smooth.StandardSmooth
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Data.Fintype.Prod

/-!
# Affine geometry of upper-unitriangular group schemes

The underlying scheme of the unitriangular group is affine space on the strictly upper
matrix entries. This is an isomorphism over the coefficient ring, not an isomorphism
of group schemes with the additive group of affine space.

Milne's field-case polynomial presentation of the unitriangular group
motivates the existing `UnitriangularCoordinateRing.freeEquiv`. The over-scheme
isomorphism below applies that equivalence contravariantly; geometric
properties come from the specified Mathlib affine-space and smoothness APIs,
not from an additive group-scheme identification. Only the numerical
dimension statements require a field.

## References

* J. S. Milne, *Algebraic Groups* (2017), item 2.9 (unitriangular polynomial
  coordinates over a field).
* `AlgebraicGroups.Algebra.UnitriangularCoordinateRing` (the existing
  `freeEquiv` and its coordinate readback), and
  `AlgebraicGroups.GroupScheme.Unitriangular` (the represented over-scheme).
* Mathlib, `Mathlib.AlgebraicGeometry.AffineSpace` (Andrew Yang's `SpecIso`
  and Justus Springer's geometric-integrality instance), `Mathlib.RingTheory.Smooth.StandardSmooth`
  and `Mathlib.AlgebraicGeometry.Morphisms.Smooth` (smoothness transport), and
  `Mathlib.RingTheory.KrullDimension.Polynomial` and `Mathlib.Data.Fintype.Prod`
  (field dimension and strict-upper index count).
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory UnitriangularCoordinateRing

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (ι : Type u) [Fintype ι] [LinearOrder ι]

/-- The unitriangular scheme is affine space on its strictly upper entries over
its structural morphism to `Spec K`. This uses `freeEquiv` contravariantly with
Mathlib's `AffineSpace.SpecIso` and `Over.isoMk`; Milne, *Algebraic Groups*
(2017), item 2.9, supplies the field-case polynomial-coordinate antecedent. -/
def unitriangularUnderlyingAffineSpaceIso :
    unitriangularGroupUnderlyingScheme K ι ≅
      (AffineSpace (StrictUpperPair ι) (Spec (.of K))).asOver (Spec (.of K)) :=
  by
    unfold unitriangularGroupUnderlyingScheme Scheme.asOver OverClass.asOver
    refine Over.isoMk ((Scheme.Spec.mapIso (freeEquiv K ι).toRingEquiv.toCommRingCatIso.op) ≪≫
      (AffineSpace.SpecIso (StrictUpperPair ι) (.of K)).symm) ?_
    change (Scheme.Spec.mapIso (freeEquiv K ι).toRingEquiv.toCommRingCatIso.op).hom ≫
        (AffineSpace.SpecIso (StrictUpperPair ι) (.of K)).inv ≫
          (AffineSpace (StrictUpperPair ι) (Spec (.of K)) ↘ Spec (.of K)) =
        Spec.map (CommRingCat.ofHom (algebraMap K (CoordinateRing K ι)))
    rw [AffineSpace.SpecIso_inv_over]
    change Spec.map (CommRingCat.ofHom (freeEquiv K ι).toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap K (FreeCoordinateRing K ι))) =
      Spec.map (CommRingCat.ofHom (algebraMap K (CoordinateRing K ι)))
    rw [← Spec.map_comp]
    congr 1
    ext r
    exact (freeEquiv K ι).commutes r

/-- The affine-space coordinates pull back to the strictly upper matrix entries. -/
theorem unitriangularUnderlyingAffineSpaceIso_preimage_variable (p : StrictUpperPair ι) :
    Spec.preimage ((unitriangularUnderlyingAffineSpaceIso K ι).hom.left ≫
      (AffineSpace.SpecIso (StrictUpperPair ι) (.of K)).hom) (MvPolynomial.X p) =
        quotient K ι (GeneralLinearCoordinateRing.matrix K ι p.1.1 p.1.2) := by
  have hmap : (unitriangularUnderlyingAffineSpaceIso K ι).hom.left ≫
      (AffineSpace.SpecIso (StrictUpperPair ι) (.of K)).hom =
        (Scheme.Spec.mapIso (freeEquiv K ι).toRingEquiv.toCommRingCatIso.op).hom := by
    simp only [unitriangularUnderlyingAffineSpaceIso, id_eq, Over.isoMk_hom_left,
      Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  calc
    _ = Spec.preimage
        ((Scheme.Spec.mapIso (freeEquiv K ι).toRingEquiv.toCommRingCatIso.op).hom)
        (MvPolynomial.X p) := congrArg (fun morphism => Spec.preimage morphism (MvPolynomial.X p)) hmap
    _ = Spec.preimage (Spec.map (CommRingCat.ofHom (freeEquiv K ι).toRingHom))
        (MvPolynomial.X p) := by rfl
    _ = _ := by rw [Spec.preimage_map]; exact freeEquiv_variable K ι p

/-- In the reverse direction, regular functions pull back along the inverse algebra equivalence. -/
theorem unitriangularUnderlyingAffineSpaceIso_preimage_inverse
    (f : CoordinateRing K ι) :
    Spec.preimage ((AffineSpace.SpecIso (StrictUpperPair ι) (.of K)).inv ≫
      (unitriangularUnderlyingAffineSpaceIso K ι).inv.left) f =
        (freeEquiv K ι).symm f := by
  have hmap : (AffineSpace.SpecIso (StrictUpperPair ι) (.of K)).inv ≫
      (unitriangularUnderlyingAffineSpaceIso K ι).inv.left =
        (Scheme.Spec.mapIso (freeEquiv K ι).toRingEquiv.toCommRingCatIso.op).inv := by
    simp only [unitriangularUnderlyingAffineSpaceIso, id_eq, Over.isoMk_inv_left,
      Iso.trans_inv, Iso.symm_inv, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  calc
    _ = Spec.preimage
        ((Scheme.Spec.mapIso (freeEquiv K ι).toRingEquiv.toCommRingCatIso.op).inv) f :=
      congrArg (fun morphism => Spec.preimage morphism f) hmap
    _ = Spec.preimage (Spec.map (CommRingCat.ofHom (freeEquiv K ι).symm.toRingHom)) f := by
      rfl
    _ = _ := by rw [Spec.preimage_map]; rfl

/-- The free polynomial presentation is standard smooth over any commutative
base, by Mathlib's `Algebra.IsStandardSmooth.of_algEquiv` applied to `freeEquiv`. -/
instance unitriangularCoordinateRing_standardSmooth :
    Algebra.IsStandardSmooth K (CoordinateRing K ι) :=
  Algebra.IsStandardSmooth.of_algEquiv (freeEquiv K ι)

/-- Finite presentation of the unitriangular coordinate algebra over its base. -/
instance unitriangularCoordinateRing_finitePresentation :
    Algebra.FinitePresentation K (CoordinateRing K ι) := inferInstance

/-- Smoothness of the structural morphism, including over the zero ring.
The proof transports standard smoothness along `freeEquiv` and applies Mathlib's
`HasRingHomProperty.Spec_iff`; no field hypothesis is needed. -/
instance unitriangularGroupUnderlyingScheme_smooth :
    Smooth (unitriangularGroupUnderlyingScheme K ι).hom := by
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap K (CoordinateRing K ι))))
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  change (algebraMap K (CoordinateRing K ι)).Smooth
  exact RingHom.smooth_algebraMap.mpr inferInstance

/-- Relative geometric integrality over any commutative ring, transported
from Mathlib's affine-space morphism along the over-scheme isomorphism.
This does not assert absolute integrality over a reducible or zero base. -/
instance unitriangularGroupUnderlyingScheme_geometricallyIntegral :
    GeometricallyIntegral (unitriangularGroupUnderlyingScheme K ι).hom := by
  let e := unitriangularUnderlyingAffineSpaceIso K ι
  have : MorphismProperty.RespectsIso (@GeometricallyIntegral) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : IsIso e.hom := inferInstance
  have : IsIso e.hom.left := inferInstance
  have h : GeometricallyIntegral (e.hom.left ≫
      ((AffineSpace (StrictUpperPair ι) (Spec (.of K))).asOver (Spec (.of K))).hom) := by
    exact (MorphismProperty.cancel_left_of_respectsIso
      (P := @GeometricallyIntegral) e.hom.left _).mpr (by
        change GeometricallyIntegral
          (AffineSpace (StrictUpperPair ι) (Spec (.of K)) ↘ Spec (.of K))
        infer_instance)
  exact e.hom.w ▸ h

/-- Absolute integrality of the underlying spectrum when the base is a domain. -/
instance unitriangularGroupUnderlyingScheme_isIntegral [IsDomain K] :
    IsIntegral (unitriangularGroupUnderlyingScheme K ι).left := by
  change IsIntegral (Spec (.of (CoordinateRing K ι)))
  apply (affine_isIntegral_iff _).mpr
  exact (freeEquiv K ι).symm.toRingEquiv.injective.isDomain _

/-- The number of strictly upper coordinates of a finite linear order. -/
theorem card_strictUpperPair :
    Fintype.card (StrictUpperPair ι) = (Fintype.card ι).choose 2 := by
  rw [Fintype.card_subtype, Fintype.card_product_filter_lt]

section Dimensions

variable (F : Type u) [Field F] (index : Type u) [Fintype index] [LinearOrder index]

/-- Over a field, the coordinate ring has Krull dimension `card ι` choose two.
The polynomial-coordinate antecedent is Milne, *Algebraic Groups* (2017),
item 2.9; the dimension calculation uses Mathlib's finite-variable polynomial
dimension and strict-upper-pair count, not a general-base dimension formula. -/
theorem unitriangularCoordinateRing_ringKrullDim :
    ringKrullDim (CoordinateRing F index) =
      (((Fintype.card index).choose 2 : ℕ) : WithBot ℕ∞) := by
  rw [← ringKrullDim_eq_of_ringEquiv (freeEquiv F index).toRingEquiv,
    MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
    ringKrullDim_eq_zero_of_field]
  simp [Nat.card_eq_fintype_card, card_strictUpperPair]

/-- Over a field, the unitriangular group's underlying affine scheme has the
polynomial-coordinate dimension suggested by Milne, *Algebraic Groups* (2017),
item 2.9. Mathlib's `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`
transfers the preceding coordinate-ring calculation. -/
theorem unitriangularGroupUnderlyingScheme_topologicalKrullDim :
    topologicalKrullDim (unitriangularGroupUnderlyingScheme F index).left =
      (((Fintype.card index).choose 2 : ℕ) : WithBot ℕ∞) := by
  change topologicalKrullDim (PrimeSpectrum (CoordinateRing F index)) = _
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    unitriangularCoordinateRing_ringKrullDim]

end Dimensions

/-- In rank `n` the dimension specializes to `n.choose 2`, including ranks zero and one. -/
theorem unitriangularGroupUnderlyingScheme_topologicalKrullDim_fin
    (F : Type) [Field F] (n : ℕ) :
    topologicalKrullDim (unitriangularGroupUnderlyingScheme F (Fin n)).left =
      ((n.choose 2 : ℕ) : WithBot ℕ∞) := by
  simpa using unitriangularGroupUnderlyingScheme_topologicalKrullDim F (Fin n)

end AlgebraicGeometry
