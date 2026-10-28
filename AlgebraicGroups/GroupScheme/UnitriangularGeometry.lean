/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

public import TauCeti.Algebra.AlgebraicGroup.UpperUnitriangular.Scheme
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.SchemePoints
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
  `coordinateHopfAlgebraAlgEquiv` and its coordinate readback), and
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

open CategoryTheory CategoryTheory.Limits TauCeti.UpperUnitriangular
open scoped TensorProduct

universe u v

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (ι : Type u) [Fintype ι] [LinearOrder ι]

/-- The unitriangular scheme is affine space on its strictly upper entries over
its structural morphism to `Spec K`. This uses `coordinateHopfAlgebraAlgEquiv` contravariantly with
Mathlib's `AffineSpace.SpecIso` and `Over.isoMk`; Milne, *Algebraic Groups*
(2017), item 2.9, supplies the field-case polynomial-coordinate antecedent. -/
def unitriangularUnderlyingAffineSpaceIso :
    (TauCeti.UpperUnitriangular.groupScheme K ι).X ≅
      (AffineSpace (Index ι) (Spec (.of K))).asOver (Spec (.of K)) :=
  by
    refine Over.isoMk ((Scheme.Spec.mapIso (coordinateHopfAlgebraAlgEquiv K
      ι).toRingEquiv.toCommRingCatIso.op) ≪≫
      (AffineSpace.SpecIso (Index ι) (.of K)).symm) ?_
    change (Scheme.Spec.mapIso (coordinateHopfAlgebraAlgEquiv K
      ι).toRingEquiv.toCommRingCatIso.op).hom ≫
        (AffineSpace.SpecIso (Index ι) (.of K)).inv ≫
          (AffineSpace (Index ι) (Spec (.of K)) ↘ Spec (.of K)) =
        Spec.map (CommRingCat.ofHom (algebraMap K (coordinateHopfAlgebra K ι)))
    rw [AffineSpace.SpecIso_inv_over]
    change Spec.map (CommRingCat.ofHom (coordinateHopfAlgebraAlgEquiv K ι).toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap K (CoordinateRing K ι))) =
      Spec.map (CommRingCat.ofHom (algebraMap K (coordinateHopfAlgebra K ι)))
    rw [← Spec.map_comp]
    congr 1
    ext r
    exact (coordinateHopfAlgebraAlgEquiv K ι).commutes r

/-- The affine-space coordinates pull back to the strictly upper matrix entries. -/
theorem unitriangularUnderlyingAffineSpaceIso_preimage_variable (p : Index ι) :
    Spec.preimage ((unitriangularUnderlyingAffineSpaceIso K ι).hom.left ≫
      (AffineSpace.SpecIso (Index ι) (.of K)).hom) (MvPolynomial.X p) =
        (TauCeti.UpperUnitriangular.coordinateHopfAlgebraAlgEquiv K ι
          (TauCeti.UpperUnitriangular.genericMatrix K ι p.1.1 p.1.2)) := by
  have hmap : (unitriangularUnderlyingAffineSpaceIso K ι).hom.left ≫
      (AffineSpace.SpecIso (Index ι) (.of K)).hom =
        (Scheme.Spec.mapIso (coordinateHopfAlgebraAlgEquiv K
          ι).toRingEquiv.toCommRingCatIso.op).hom := by
    simp only [unitriangularUnderlyingAffineSpaceIso, Over.isoMk_hom_left,
      Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  calc
    _ = Spec.preimage
        ((Scheme.Spec.mapIso (coordinateHopfAlgebraAlgEquiv K
          ι).toRingEquiv.toCommRingCatIso.op).hom)
        (MvPolynomial.X p) :=
      congrArg (fun morphism => Spec.preimage morphism (MvPolynomial.X p)) hmap
    _ = Spec.preimage (Spec.map (CommRingCat.ofHom (coordinateHopfAlgebraAlgEquiv K ι).toRingHom))
        (MvPolynomial.X p) := by rfl
    _ = _ := by
      rw [Spec.preimage_map, TauCeti.UpperUnitriangular.genericMatrix_apply_of_lt K ι p.2]
      rfl

/-- In the reverse direction, regular functions pull back along the inverse algebra equivalence. -/
theorem unitriangularUnderlyingAffineSpaceIso_preimage_inverse
    (f : coordinateHopfAlgebra K ι) :
    Spec.preimage ((AffineSpace.SpecIso (Index ι) (.of K)).inv ≫
      (unitriangularUnderlyingAffineSpaceIso K ι).inv.left) f =
        (coordinateHopfAlgebraAlgEquiv K ι).symm f := by
  have hmap : (AffineSpace.SpecIso (Index ι) (.of K)).inv ≫
      (unitriangularUnderlyingAffineSpaceIso K ι).inv.left =
        (Scheme.Spec.mapIso (coordinateHopfAlgebraAlgEquiv K
          ι).toRingEquiv.toCommRingCatIso.op).inv := by
    simp only [unitriangularUnderlyingAffineSpaceIso, Over.isoMk_inv_left,
      Iso.trans_inv, Iso.symm_inv, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  calc
    _ = Spec.preimage
        ((Scheme.Spec.mapIso (coordinateHopfAlgebraAlgEquiv K
          ι).toRingEquiv.toCommRingCatIso.op).inv) f :=
      congrArg (fun morphism => Spec.preimage morphism f) hmap
    _ = Spec.preimage (Spec.map (CommRingCat.ofHom (coordinateHopfAlgebraAlgEquiv K
      ι).symm.toRingHom)) f := by
      rfl
    _ = _ := by rw [Spec.preimage_map]; rfl

section MixedUniverse

variable (K : Type (max u v)) [CommRing K] (ι : Type v) [Fintype ι] [LinearOrder ι]

/-- The free polynomial presentation is standard smooth over any commutative
base, by Mathlib's `Algebra.IsStandardSmooth.of_algEquiv` applied to
  `coordinateHopfAlgebraAlgEquiv`. -/
instance unitriangularCoordinateRing_standardSmooth :
    Algebra.IsStandardSmooth K (coordinateHopfAlgebra K ι) :=
  Algebra.IsStandardSmooth.of_algEquiv (coordinateHopfAlgebraAlgEquiv K ι)

/- Finite presentation of the unitriangular coordinate algebra over its base follows
from the standard-smoothness instance and Mathlib's general implication. -/

/-- Smoothness of the structural morphism, including over the zero ring.
The proof transports standard smoothness along `coordinateHopfAlgebraAlgEquiv` and applies Mathlib's
`HasRingHomProperty.Spec_iff`; no field hypothesis is needed. -/
instance unitriangularGroupUnderlyingScheme_smooth :
    Smooth ((TauCeti.UpperUnitriangular.groupScheme K ι).X).hom := by
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap K (coordinateHopfAlgebra K ι))))
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  change (algebraMap K (coordinateHopfAlgebra K ι)).Smooth
  exact RingHom.smooth_algebraMap.mpr inferInstance

/-- Relative geometric integrality over any commutative ring: extending the canonical
polynomial coordinates to a field gives an integral affine space. This does not
assert absolute integrality over a reducible or zero base. -/
instance unitriangularGroupUnderlyingScheme_geometricallyIntegral :
    GeometricallyIntegral ((TauCeti.UpperUnitriangular.groupScheme K ι).X).hom := by
  let : ObjectProperty.IsClosedUnderIsomorphisms (C := Scheme) IsIntegral :=
    ⟨fun iso integral ↦ by let := integral; exact IsIntegral.of_isIso iso.hom⟩
  refine ⟨(geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms
    (P := IsIntegral)).2 ?_⟩
  intro F _ _
  let e : F ⊗[K] coordinateHopfAlgebra K ι ≃ₐ[F] MvPolynomial (Index ι) F :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : F ≃ₐ[F] F)
      (coordinateHopfAlgebraAlgEquiv K ι).symm).trans
        (MvPolynomial.algebraTensorAlgEquiv K F)
  let : IsDomain (F ⊗[K] coordinateHopfAlgebra K ι) := e.injective.isDomain e.toRingHom
  let : IsDomain (coordinateHopfAlgebra K ι ⊗[K] F) :=
    (Algebra.TensorProduct.comm K (coordinateHopfAlgebra K ι) F).injective.isDomain
      (Algebra.TensorProduct.comm K (coordinateHopfAlgebra K ι) F).toRingHom
  change IsIntegral (pullback
    (Spec.map (CommRingCat.ofHom (algebraMap K (coordinateHopfAlgebra K ι))))
    (Spec.map (CommRingCat.ofHom (algebraMap K F))))
  exact IsIntegral.of_isIso (pullbackSpecIso K (coordinateHopfAlgebra K ι) F).inv

/-- Absolute integrality of the underlying spectrum when the base is a domain. -/
instance unitriangularGroupUnderlyingScheme_isIntegral [IsDomain K] :
    IsIntegral ((TauCeti.UpperUnitriangular.groupScheme K ι).X).left := by
  change IsIntegral (Spec (.of (coordinateHopfAlgebra K ι)))
  apply (affine_isIntegral_iff _).mpr
  exact (coordinateHopfAlgebraAlgEquiv K ι).symm.toRingEquiv.injective.isDomain _

end MixedUniverse

/-- The number of strictly upper coordinates of a finite linear order. -/
theorem card_strictUpperPair :
    Fintype.card (Index ι) = (Fintype.card ι).choose 2 := by
  rw [Fintype.card_subtype, Fintype.card_product_filter_lt]

section Dimensions

variable (F : Type u) [Field F] (index : Type u) [Fintype index] [LinearOrder index]

/-- Over a field, the coordinate ring has Krull dimension `card ι` choose two.
The polynomial-coordinate antecedent is Milne, *Algebraic Groups* (2017),
item 2.9; the dimension calculation uses Mathlib's finite-variable polynomial
dimension and strict-upper-pair count, not a general-base dimension formula. -/
theorem unitriangularCoordinateRing_ringKrullDim :
    ringKrullDim (coordinateHopfAlgebra F index) =
      (((Fintype.card index).choose 2 : ℕ) : WithBot ℕ∞) := by
  rw [← ringKrullDim_eq_of_ringEquiv (coordinateHopfAlgebraAlgEquiv F index).toRingEquiv,
    MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
    ringKrullDim_eq_zero_of_field]
  simp [Nat.card_eq_fintype_card, card_strictUpperPair]

/-- Over a field, the unitriangular group's underlying affine scheme has the
polynomial-coordinate dimension suggested by Milne, *Algebraic Groups* (2017),
item 2.9. Mathlib's `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`
transfers the preceding coordinate-ring calculation. -/
theorem unitriangularGroupUnderlyingScheme_topologicalKrullDim :
    topologicalKrullDim ((TauCeti.UpperUnitriangular.groupScheme F index).X).left =
      (((Fintype.card index).choose 2 : ℕ) : WithBot ℕ∞) := by
  change topologicalKrullDim (PrimeSpectrum (coordinateHopfAlgebra F index)) = _
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    unitriangularCoordinateRing_ringKrullDim]

end Dimensions

/-- In rank `n` the dimension specializes to `n.choose 2`, including ranks zero and one. -/
theorem unitriangularGroupUnderlyingScheme_topologicalKrullDim_fin
    (F : Type) [Field F] (n : ℕ) :
    topologicalKrullDim ((TauCeti.UpperUnitriangular.groupScheme F (Fin n)).X).left =
      ((n.choose 2 : ℕ) : WithBot ℕ∞) := by
  simpa using unitriangularGroupUnderlyingScheme_topologicalKrullDim F (Fin n)

end AlgebraicGeometry
