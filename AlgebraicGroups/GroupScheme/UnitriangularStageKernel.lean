/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.UnitriangularStageKernel
public import AlgebraicGroups.GroupScheme.UnitriangularStageCoordinates
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits

/-!
# The positive-stage unitriangular kernel square

The closed successor is the fiber of the product of additive
superdiagonal coordinates over the unit section. The proof tests arbitrary
schemes, using the adjunction between global sections and affine spectra.

The scheme factorization helper applies at every natural stage, testing only
strict-upper superdiagonal entries. At stage zero these tests are vacuous and
the successor is an isomorphism, since the stage-zero and stage-one ideals
are both zero. The positive-stage additive-coordinate and kernel constructions
still require a positive stage.

The factorization uses a quotient-spectrum lift and closed-immersion
monicity, not the separate algebraic successor-factorization lemma.

## References

* J. S. Milne, *Algebraic Groups* (2017), §6.49 (field-case one-entry
  additive quotients); no general whole-stage scheme-kernel square is
  attributed to this passage.
* Mathlib contributors, `Mathlib.AlgebraicGeometry.Scheme` (`Scheme.ΓSpecIso`),
  `Mathlib.AlgebraicGeometry.AffineScheme` (`Scheme.Hom.liftQuotient`),
  `Mathlib.AlgebraicGeometry.Morphisms.Finite` (closed-immersion monicity),
  and `Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits`
  (the product's categorical projections and unit).
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
  UnitriangularStageCoordinateRing
open scoped CategoryTheory CategoryTheory.MonObj

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

variable (K : Type) [CommRing K] (n r : ℕ)

/-- Pulling a global function back along a map of affine targets agrees with
precomposing the corresponding homomorphism of coordinate rings. -/
private theorem preimage_spec_comp {A B : CommRingCat} {X : Scheme}
    (f : X ⟶ Spec B) (v : A ⟶ B) :
    (Scheme.ΓSpecIso A).inv ≫ (f ≫ Spec.map v).appTop =
      v ≫ ((Scheme.ΓSpecIso B).inv ≫ f.appTop) := by
  rw [Scheme.Hom.comp_appTop, ← Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]

/-- An arbitrary scheme map into a stage spectrum factors uniquely through
the successor when its strict-upper superdiagonal coordinates vanish on global
sections. This applies at every natural stage, without an affineness assumption
on the test scheme. At a positive stage all indexed entries are strict upper.
At stage zero the indices are diagonal, so the strict-upper condition is
vacuous and the successor is an isomorphism; requiring every raw diagonal
coordinate to vanish would instead force the test scheme to be empty at
positive rank. The factor is constructed with `Scheme.Hom.liftQuotient` and
uniqueness uses the closed immersion. -/
theorem unitriangularStageSuccessor_existsUnique_of_coordinates
    {X : Scheme}
    (f : X ⟶ Spec (.of (CoordinateRing K n r)))
    (hcoord : ∀ ij : TauCeti.UpperUnitriangularGroup.superdiagonalIndex n r,
      ij.1.1 < ij.1.2 →
      (((Scheme.ΓSpecIso (.of (CoordinateRing K n r))).inv ≫ f.appTop).hom)
        (coordinate K n r ij) = 0) :
    ∃! g : X ⟶ Spec (.of (CoordinateRing K n (r + 1))),
      g ≫ (unitriangularStageSuccessor K n r).hom.hom.left = f := by
  let ambientMap : X ⟶ Spec (.of (Ambient K n)) :=
    f ≫ Spec.map (CommRingCat.ofHom (quotient K n r).toRingHom)
  have hpreimage :
      (Scheme.ΓSpecIso (.of (Ambient K n))).inv ≫ ambientMap.appTop =
        CommRingCat.ofHom (quotient K n r).toRingHom ≫
          ((Scheme.ΓSpecIso (.of (CoordinateRing K n r))).inv ≫ f.appTop) :=
    preimage_spec_comp f (CommRingCat.ofHom (quotient K n r).toRingHom)
  have hI : ideal K n (r + 1) ≤
      RingHom.ker ((Scheme.ΓSpecIso (.of (Ambient K n))).inv ≫
        ambientMap.appTop).hom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, j, hij, hgap, rfl⟩
    apply RingHom.mem_ker.mpr
    have heval := congrArg (fun arrow : CommRingCat.of (Ambient K n) ⟶ Γ(X, ⊤) =>
      arrow.hom (entry K n i j)) hpreimage
    rw [heval]
    simp only [CommRingCat.hom_comp, RingHom.comp_apply]
    change (((Scheme.ΓSpecIso (.of (CoordinateRing K n r))).inv ≫ f.appTop).hom)
      ((quotient K n r) (entry K n i j)) = 0
    by_cases hsmall : j.val < i.val + r
    · rw [quotient_entry K n r i j hij hsmall, map_zero]
    · have heq : j.val = i.val + r := by omega
      exact hcoord ⟨(i, j), heq⟩ hij
  let lift : X ⟶ Spec (.of (CoordinateRing K n (r + 1))) :=
    Scheme.Hom.liftQuotient ambientMap (ideal K n (r + 1)) hI
  have hstage : (unitriangularStageSuccessor K n r).hom.hom.left ≫
      (unitriangularStageInclusion K n r).hom.hom.left =
      (unitriangularStageInclusion K n (r + 1)).hom.hom.left := by
    simpa only [Grp.comp_hom_hom, Over.comp_left] using
      congrArg (fun arrow : unitriangularStageScheme K n (r + 1) ⟶
        (TauCeti.UpperUnitriangular.groupScheme K (Fin n)) => arrow.hom.hom.left)
        (unitriangularStageSuccessor_inclusion K n r)
  have hclosedAmbient : IsClosedImmersion
      (unitriangularStageInclusion K n r).hom.hom.left :=
    unitriangularStageInclusion_isClosedImmersion K n r
  have : Mono (unitriangularStageInclusion K n r).hom.hom.left :=
    (IsClosedImmersion.iff_isFinite_and_mono _).mp hclosedAmbient |>.2
  have hlift : lift ≫ (unitriangularStageSuccessor K n r).hom.hom.left = f := by
    apply (cancel_mono (unitriangularStageInclusion K n r).hom.hom.left).mp
    calc
      (lift ≫ (unitriangularStageSuccessor K n r).hom.hom.left) ≫
          (unitriangularStageInclusion K n r).hom.hom.left =
          lift ≫ (unitriangularStageInclusion K n (r + 1)).hom.hom.left := by
            rw [Category.assoc, hstage]
      _ = ambientMap := Scheme.Hom.liftQuotient_comp ambientMap _ hI
      _ = f ≫ (unitriangularStageInclusion K n r).hom.hom.left := rfl
  refine ⟨lift, hlift, ?_⟩
  intro g hg
  have hclosed : IsClosedImmersion
      (unitriangularStageSuccessor K n r).hom.hom.left :=
    unitriangularStageSuccessor_isClosedImmersion K n r
  have : Mono (unitriangularStageSuccessor K n r).hom.hom.left :=
    (IsClosedImmersion.iff_isFinite_and_mono _).mp hclosed |>.2
  exact (cancel_mono (unitriangularStageSuccessor K n r).hom.hom.left).mp
    (hg.trans hlift.symm)

/- Positive stages are covered by the factorization theorem above, with vanishing
of every superdiagonal coordinate. -/

/-- The successor stage is the fiber over the unit of the superdiagonal
coordinate product in `Over (Spec K)`, including nonaffine test schemes.
Milne, *Algebraic Groups* (2017), §6.49 supplies one-entry field-case additive
quotients, not this whole-stage categorical kernel square. -/
theorem unitriangularStageCoordinateMap_isPullback (hr : 1 ≤ r) :
    IsPullback (unitriangularStageSuccessor K n r).hom.hom
      (toUnit (unitriangularStageScheme K n (r + 1)).toMon.X)
      (unitriangularStageCoordinateMap K n r hr).hom.hom
      η[((∏ᶜ fun _ : TauCeti.UpperUnitriangularGroup.superdiagonalIndex n r =>
        TauCeti.AdditiveGroup.groupScheme K).toMon.X)] := by
  let coordinateProduct :=
    (∏ᶜ fun _ : TauCeti.UpperUnitriangularGroup.superdiagonalIndex n r =>
      TauCeti.AdditiveGroup.groupScheme K)
  have hcomm :
      (unitriangularStageSuccessor K n r).hom.hom ≫
        (unitriangularStageCoordinateMap K n r hr).hom.hom =
      toUnit (unitriangularStageScheme K n (r + 1)).toMon.X ≫
        η[coordinateProduct.toMon.X] := by
    have hzero := congrArg
      (fun arrow : unitriangularStageScheme K n (r + 1) ⟶ coordinateProduct =>
        arrow.hom.hom)
      (unitriangularStageCoordinateMap_successor_zero K n r hr)
    simpa only [Grp.comp_hom_hom, Grp.zero_hom, Mon.zero_hom] using hzero
  refine IsPullback.mk' hcomm ?_ ?_
  · intro T first second hfirst _
    apply Over.OverMorphism.ext
    have hclosed : IsClosedImmersion
        (unitriangularStageSuccessor K n r).hom.hom.left :=
      unitriangularStageSuccessor_isClosedImmersion K n r
    have : Mono (unitriangularStageSuccessor K n r).hom.hom.left :=
      (IsClosedImmersion.iff_isFinite_and_mono _).mp hclosed |>.2
    exact (cancel_mono (unitriangularStageSuccessor K n r).hom.hom.left).mp
      (congrArg Over.Hom.left hfirst)
  · intro T stagePoint basePoint hcompatible
    have hcoord (ij : TauCeti.UpperUnitriangularGroup.superdiagonalIndex n r) :
        (((Scheme.ΓSpecIso (.of (CoordinateRing K n r))).inv ≫
          stagePoint.left.appTop).hom) (coordinate K n r ij) = 0 := by
      let projection := Limits.Pi.π
        (fun _ : TauCeti.UpperUnitriangularGroup.superdiagonalIndex n r =>
          TauCeti.AdditiveGroup.groupScheme K) ij
      have hprojection :
          (unitriangularStageCoordinateMap K n r hr).hom.hom ≫
            projection.hom.hom =
          (unitriangularStageCoordinateProjection K n r hr ij).hom.hom := by
        exact congrArg (fun arrow : unitriangularStageScheme K n r ⟶
          TauCeti.AdditiveGroup.groupScheme K => arrow.hom.hom)
          (unitriangularStageCoordinateMap_π K n r hr ij)
      have hunit : η[coordinateProduct.toMon.X] ≫ projection.hom.hom =
          η[(TauCeti.AdditiveGroup.groupScheme K).toMon.X] := by
        exact IsMonHom.one_hom projection.hom.hom
      have hcomponent : stagePoint ≫
          (unitriangularStageCoordinateProjection K n r hr ij).hom.hom =
          basePoint ≫ η[(TauCeti.AdditiveGroup.groupScheme K).toMon.X] := by
        calc
          _ = stagePoint ≫
                ((unitriangularStageCoordinateMap K n r hr).hom.hom ≫
                  projection.hom.hom) := by rw [hprojection]
          _ = (stagePoint ≫
                (unitriangularStageCoordinateMap K n r hr).hom.hom) ≫
                  projection.hom.hom := (Category.assoc _ _ _).symm
          _ = (basePoint ≫ η[coordinateProduct.toMon.X]) ≫
                  projection.hom.hom := by rw [hcompatible]
          _ = _ := by rw [Category.assoc, hunit]
      let coordinateArrow : Spec (.of (CoordinateRing K n r)) ⟶
          Spec (.of ((SymmetricAlgebra K K))) :=
        (unitriangularStageCoordinateProjection K n r hr ij).hom.hom.left
      let zeroArrow : Spec (.of K) ⟶
          Spec (.of ((SymmetricAlgebra K K))) :=
        η[(TauCeti.AdditiveGroup.groupScheme K).toMon.X].left
      have hscheme : stagePoint.left ≫ coordinateArrow =
          basePoint.left ≫ zeroArrow :=
        congrArg Over.Hom.left hcomponent
      have hcoordinate : (Spec.preimage coordinateArrow).hom
          ((SymmetricAlgebra.ι K K 1)) = coordinate K n r ij := by
        dsimp only [coordinateArrow]
        rw [unitriangularStageCoordinateProjection_left, Spec.preimage_map]
        change (coordinateBialgHom K n r hr ij :
          (SymmetricAlgebra K K) →ₐ[K] CoordinateRing K n r)
            ((SymmetricAlgebra.ι K K 1)) = _
        rw [coordinateBialgHom_toAlgHom, coordinateAlgHom_coordinate]
      have hzero : (Spec.preimage zeroArrow).hom
          ((SymmetricAlgebra.ι K K 1)) = 0 := by
        dsimp only [zeroArrow]
        have hzeroMap : η[(TauCeti.AdditiveGroup.groupScheme K).X].left =
            Spec.map (CommRingCat.ofHom
              (Bialgebra.counitAlgHom K (SymmetricAlgebra K K)).toRingHom) := by
          change η[((hopfSpec (.of K)).obj
            (.op (TauCeti.AdditiveGroup.coordinateHopfAlgebra K))).X].left = _
          rw [TauCeti.hopfSpec_obj_one_left]
          rfl
        rw [hzeroMap, Spec.preimage_map]
        exact SymmetricAlgebra.counit_ι K K 1
      have hscheme' : stagePoint.left ≫ Spec.map (Spec.preimage coordinateArrow) =
          basePoint.left ≫ Spec.map (Spec.preimage zeroArrow) := by
        simpa only [Spec.map_preimage] using hscheme
      have heval' := congrArg
        (fun arrow : T.left ⟶ Spec (.of ((SymmetricAlgebra K K))) =>
          (((Scheme.ΓSpecIso (.of ((SymmetricAlgebra K K)))).inv ≫
            arrow.appTop).hom) ((SymmetricAlgebra.ι K K 1))) hscheme'
      have hcoordinateValue :
          (((Scheme.ΓSpecIso (.of (CoordinateRing K n r))).inv ≫
            stagePoint.left.appTop).hom) ((Spec.preimage coordinateArrow).hom
              ((SymmetricAlgebra.ι K K 1))) =
          (((Scheme.ΓSpecIso (.of K)).inv ≫ basePoint.left.appTop).hom)
            ((Spec.preimage zeroArrow).hom ((SymmetricAlgebra.ι K K 1))) := by
        simpa only [preimage_spec_comp, CommRingCat.hom_comp,
          RingHom.comp_apply] using heval'
      simpa only [hcoordinate, hzero, map_zero] using hcoordinateValue
    obtain ⟨factor, hfactor, _⟩ :=
      unitriangularStageSuccessor_existsUnique_of_coordinates K n r stagePoint.left
        (fun ij _ => hcoord ij)
    have hbase : factor ≫ (unitriangularStageUnderlyingScheme K n (r + 1)).hom =
        T.hom := by
      calc
        factor ≫ (unitriangularStageUnderlyingScheme K n (r + 1)).hom =
            (factor ≫ (unitriangularStageSuccessor K n r).hom.hom.left) ≫
              (unitriangularStageUnderlyingScheme K n r).hom := by
                rw [Category.assoc, (unitriangularStageSuccessor K n r).hom.hom.w]
        _ = stagePoint.left ≫ (unitriangularStageUnderlyingScheme K n r).hom := by
            rw [hfactor]
        _ = T.hom := stagePoint.w
    let lift : T ⟶ unitriangularStageUnderlyingScheme K n (r + 1) :=
      Over.homMk factor hbase
    refine ⟨lift, ?_, ?_⟩
    · apply Over.OverMorphism.ext
      exact hfactor
    · exact toUnit_unique _ _

end AlgebraicGeometry
