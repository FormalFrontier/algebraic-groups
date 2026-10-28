/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.UnitriangularStages
public import AlgebraicGroups.Algebra.UnitriangularStageCoordinates
public import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

/-!
# Positive-stage coordinates as a native group-scheme morphism

The primitive coordinates of the stage quotient induce group-scheme arrows
to the rank-one additive group scheme. Their categorical product is the
superdiagonal coordinate map over any commutative base ring. Its point formula
uses the stage representation and the existing superdiagonal homomorphism;
no identification with a field-only vector group is made.

Milne's finer field-case filtration has one-entry additive quotients;
the product of all positive-stage projections here is a distinct construction.

## References

* J. S. Milne, *Algebraic Groups* (2017), item 2.1 (the additive group)
  and §6.49 (one-entry additive quotients of the finer filtration).
* Mathlib contributors, `Mathlib.AlgebraicGeometry.Group.Affine`
  (`hopfSpec`) and `Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits`
  and `Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts` (group-object products).
* The existing `UnitriangularStageCoordinates` and
  `UnitriangularSuperdiagonalQuotients` provide the algebra maps and
  multiplicative point-coordinate formula.
-/

@[expose] public section

noncomputable section

open CategoryTheory UnitriangularStageCoordinateRing
open scoped CategoryTheory CategoryTheory.MonObj

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

variable (K : Type) [CommRing K] (n r : ℕ)

/-- A single positive-stage entry as a morphism of group schemes.
Milne, *Algebraic Groups* (2017), §6.49 gives one-entry additive
quotients in the finer field-case filtration. -/
def unitriangularStageCoordinateProjection (hr : 1 ≤ r)
    (ij : TauCeti.UpperUnitriangularGroup.superdiagonalIndex n r) :
    unitriangularStageScheme K n r ⟶ TauCeti.AdditiveGroup.groupScheme K := by
  let coordinateArrow :
      CommHopfAlgCat.of K ((SymmetricAlgebra K K)) ⟶
        CommHopfAlgCat.of K (CoordinateRing K n r) :=
    CommHopfAlgCat.ofHom (coordinateBialgHom K n r hr ij)
  exact (hopfSpec (.of K)).map (Opposite.op coordinateArrow) ≫
    eqToHom (TauCeti.AdditiveGroup.groupScheme_def K).symm

theorem unitriangularStageCoordinateProjection_left (hr : 1 ≤ r)
    (ij : TauCeti.UpperUnitriangularGroup.superdiagonalIndex n r) :
    (unitriangularStageCoordinateProjection K n r hr ij).hom.hom.left =
      Spec.map (CommRingCat.ofHom
        ((coordinateBialgHom K n r hr ij :
          SymmetricAlgebra K K →ₐ[K] CoordinateRing K n r)).toRingHom) := by
  rfl

/-- The categorical product of the positive-stage additive coordinates.
Milne, *Algebraic Groups* (2017), §6.49 gives field-case one-entry additive
quotients; this product map uses all entries on a positive superdiagonal. -/
def unitriangularStageCoordinateMap (hr : 1 ≤ r) :
    unitriangularStageScheme K n r ⟶
      (∏ᶜ fun _ : TauCeti.UpperUnitriangularGroup.superdiagonalIndex n r =>
        TauCeti.AdditiveGroup.groupScheme K) :=
  Limits.Pi.lift (fun ij => unitriangularStageCoordinateProjection K n r hr ij)

@[simp] theorem unitriangularStageCoordinateMap_π (hr : 1 ≤ r)
    (ij : TauCeti.UpperUnitriangularGroup.superdiagonalIndex n r) :
    unitriangularStageCoordinateMap K n r hr ≫
        Limits.Pi.π (fun _ : TauCeti.UpperUnitriangularGroup.superdiagonalIndex n r =>
          TauCeti.AdditiveGroup.groupScheme K) ij =
      unitriangularStageCoordinateProjection K n r hr ij := by
  simp [unitriangularStageCoordinateMap]

/-- The closed successor has zero `r`-th coordinate as a group-scheme arrow. -/
theorem unitriangularStageCoordinateProjection_successor_zero (hr : 1 ≤ r)
    (ij : TauCeti.UpperUnitriangularGroup.superdiagonalIndex n r) :
    unitriangularStageSuccessor K n r ≫
        unitriangularStageCoordinateProjection K n r hr ij = 0 := by
  have hzeroAlg :
      (successor K n r).comp (coordinateAlgHom K n r ij) =
        (Algebra.ofId K (CoordinateRing K n (r + 1))).comp
          (Bialgebra.counitAlgHom K ((SymmetricAlgebra K K))) := by
    let pointEquiv :=
      (TauCeti.AdditiveGroup.gaPointsMulEquiv
        (R := K) (A := CoordinateRing K n (r + 1))).symm
    have decode (f : SymmetricAlgebra K K →ₐ[K] CoordinateRing K n (r + 1)) :
        (pointEquiv.symm (WithConv.toConv f)).toAdd = f (SymmetricAlgebra.ι K K 1) := by
      exact TauCeti.AdditiveGroup.toAdd_gaPointsMulEquiv
        (R := K) (A := CoordinateRing K n (r + 1)) (WithConv.toConv f)
    apply WithConv.toConv_injective
    apply pointEquiv.symm.injective
    apply Multiplicative.toAdd.injective
    rw [decode, decode]
    change ((successor K n r).comp (coordinateAlgHom K n r ij))
        ((SymmetricAlgebra.ι K K 1)) =
      ((Algebra.ofId K (CoordinateRing K n (r + 1))).comp
        (Bialgebra.counitAlgHom K ((SymmetricAlgebra K K))))
          ((SymmetricAlgebra.ι K K 1))
    rw [AlgHom.comp_apply, AlgHom.comp_apply, coordinateAlgHom_coordinate,
      successor_coordinate K n r hr ij,
      Bialgebra.counitAlgHom_apply, SymmetricAlgebra.counit_ι]
    exact (map_zero (Algebra.ofId K (CoordinateRing K n (r + 1)))).symm
  have hzeroLeft :
      (0 : unitriangularStageScheme K n (r + 1) ⟶ TauCeti.AdditiveGroup.groupScheme
        K).hom.hom.left =
        Spec.map (CommRingCat.ofHom
          (((Algebra.ofId K (CoordinateRing K n (r + 1))).comp
            (Bialgebra.counitAlgHom K ((SymmetricAlgebra K K)))).toRingHom)) ≫
          eqToHom (TauCeti.AdditiveGroup.groupScheme_X_left K).symm := by
    change (1 :
      (Spec (CommRingCat.of (CoordinateRing K n (r + 1)))).asOver
        (Spec (CommRingCat.of K)) ⟶ (TauCeti.AdditiveGroup.groupScheme K).X).left = _
    rw [← map_one (TauCeti.AdditiveGroup.groupSchemePointMulEquiv
      (R := K) (CoordinateRing K n (r + 1)))]
    rw [TauCeti.AdditiveGroup.groupSchemePointMulEquiv_apply_left]
    rfl
  apply InducedCategory.Hom.ext
  apply Mon.Hom.ext
  apply Over.OverMorphism.ext
  change (unitriangularStageSuccessor K n r).hom.hom.left ≫
      (unitriangularStageCoordinateProjection K n r hr ij).hom.hom.left =
    (0 : unitriangularStageScheme K n (r + 1) ⟶ TauCeti.AdditiveGroup.groupScheme K).hom.hom.left
  rw [hzeroLeft]
  rw [unitriangularStageSuccessor_left, unitriangularStageCoordinateProjection_left]
  change _ = Spec.map (CommRingCat.ofHom
    (((Algebra.ofId K (CoordinateRing K n (r + 1))).comp
      (Bialgebra.counitAlgHom K (SymmetricAlgebra K K)))).toRingHom)
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom hzeroAlg

/-- The whole positive-stage map vanishes on the closed successor. -/
theorem unitriangularStageCoordinateMap_successor_zero (hr : 1 ≤ r) :
    unitriangularStageSuccessor K n r ≫
      unitriangularStageCoordinateMap K n r hr = 0 := by
  apply Limits.Pi.hom_ext
  intro ij
  rw [Category.assoc, unitriangularStageCoordinateMap_π]
  simpa using unitriangularStageCoordinateProjection_successor_zero K n r hr ij

variable (R : Type) [CommRing R] [Algebra K R]

/-- On every coefficient algebra, a genuine projection reads the matrix entry. -/
theorem unitriangularStageCoordinateProjection_point (hr : 1 ≤ r)
    (s : TauCeti.UpperUnitriangularGroup.superdiagonalSubgroup (n := n) (R := R) r)
    (ij : TauCeti.UpperUnitriangularGroup.superdiagonalIndex n r) :
    unitriangularStagePointMulEquiv K n r R s ≫
        (unitriangularStageCoordinateProjection K n r hr ij).hom.hom =
      (TauCeti.AdditiveGroup.schemePointsMulEquiv (R := K) R).symm
        (.ofAdd (Multiplicative.toAdd
          (TauCeti.UpperUnitriangularGroup.superdiagonalCoordinateHom n R r hr s) ij)) := by
  have hcoordinate :
      (unitriangularStageFromGL K n r R s).comp (coordinateAlgHom K n r ij) =
        ((TauCeti.AdditiveGroup.gaPointsMulEquiv (R := K) (A := R)).symm
          (.ofAdd (Multiplicative.toAdd
            (TauCeti.UpperUnitriangularGroup.superdiagonalCoordinateHom n R r hr s)
              ij))).ofConv := by
    apply SymmetricAlgebra.algHom_ext
    ext
    change ((unitriangularStageFromGL K n r R s).comp (coordinateAlgHom K n r ij))
        ((SymmetricAlgebra.ι K K 1)) =
      ((TauCeti.AdditiveGroup.gaPointsMulEquiv (R := K) (A := R)).symm
        (.ofAdd (Multiplicative.toAdd
          (TauCeti.UpperUnitriangularGroup.superdiagonalCoordinateHom n R r hr s) ij))).ofConv
          ((SymmetricAlgebra.ι K K 1))
    rw [AlgHom.comp_apply, coordinateAlgHom_coordinate]
    rw [TauCeti.AdditiveGroup.gaPointsMulEquiv_symm_apply_ι, toAdd_ofAdd,
      TauCeti.UpperUnitriangularGroup.superdiagonalCoordinateHom_apply]
    change (unitriangularStageFromGL K n r R s)
      (quotient K n r (entry K n ij.1.1 ij.1.2)) =
        (s.1.1 : Matrix (Fin n) (Fin n) R) ij.1.1 ij.1.2
    rw [← AlgHom.comp_apply, unitriangularStageFromGL_comp_quotient]
    have hij : ij.1.1 < ij.1.2 := by have := ij.2; omega
    rw [entry, TauCeti.UpperUnitriangular.genericMatrix_apply_of_lt K (Fin n) hij]
    exact TauCeti.UpperUnitriangular.upperUnitriangularToPoint_apply K (Fin n) s.1
      ⟨ij.1, hij⟩
  apply Over.OverMorphism.ext
  change (unitriangularStagePointMulEquiv K n r R s).left ≫
      (unitriangularStageCoordinateProjection K n r hr ij).hom.hom.left =
    ((TauCeti.AdditiveGroup.schemePointsMulEquiv (R := K) R).symm
      (.ofAdd (Multiplicative.toAdd
        (TauCeti.UpperUnitriangularGroup.superdiagonalCoordinateHom n R r hr s) ij))).left
  rw [unitriangularStagePointMulEquiv_apply_left,
    unitriangularStageCoordinateProjection_left,
    TauCeti.AdditiveGroup.schemePointsMulEquiv_symm_apply,
    TauCeti.AdditiveGroup.groupSchemePointMulEquiv_apply_left]
  change _ = Spec.map (CommRingCat.ofHom
    ((TauCeti.AdditiveGroup.gaPointsMulEquiv (R := K) (A := R)).symm
      (.ofAdd (Multiplicative.toAdd
        (TauCeti.UpperUnitriangularGroup.superdiagonalCoordinateHom n R r hr s)
          ij))).ofConv.toRingHom)
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom hcoordinate

/-- The product projections agree with the point-group coordinate hom. -/
theorem unitriangularStageCoordinateMap_point (hr : 1 ≤ r)
    (s : TauCeti.UpperUnitriangularGroup.superdiagonalSubgroup (n := n) (R := R) r)
    (ij : TauCeti.UpperUnitriangularGroup.superdiagonalIndex n r) :
    unitriangularStagePointMulEquiv K n r R s ≫
        (unitriangularStageCoordinateMap K n r hr).hom.hom ≫
        (Limits.Pi.π (fun _ : TauCeti.UpperUnitriangularGroup.superdiagonalIndex n r =>
          TauCeti.AdditiveGroup.groupScheme K) ij).hom.hom =
      (TauCeti.AdditiveGroup.schemePointsMulEquiv (R := K) R).symm
        (.ofAdd (Multiplicative.toAdd
          (TauCeti.UpperUnitriangularGroup.superdiagonalCoordinateHom n R r hr s) ij)) := by
  change unitriangularStagePointMulEquiv K n r R s ≫
      (unitriangularStageCoordinateMap K n r hr ≫
        Limits.Pi.π (fun _ : TauCeti.UpperUnitriangularGroup.superdiagonalIndex n r =>
          TauCeti.AdditiveGroup.groupScheme K) ij).hom.hom = _
  rw [unitriangularStageCoordinateMap_π]
  exact unitriangularStageCoordinateProjection_point K n r R hr s ij

/-- The all-algebra point equation is compatible with every base-algebra map. -/
theorem unitriangularStageCoordinateMap_point_natural
    {S : Type} [CommRing S] [Algebra K S] (hr : 1 ≤ r)
    (f : R →ₐ[K] S) (s : TauCeti.UpperUnitriangularGroup.superdiagonalSubgroup (n := n) (R := R) r)
    (ij : TauCeti.UpperUnitriangularGroup.superdiagonalIndex n r) :
    unitriangularStagePointMulEquiv K n r S
        (unitriangularStageMap n r R f.toRingHom s) ≫
        (unitriangularStageCoordinateMap K n r hr).hom.hom ≫
        (Limits.Pi.π (fun _ : TauCeti.UpperUnitriangularGroup.superdiagonalIndex n r =>
          TauCeti.AdditiveGroup.groupScheme K) ij).hom.hom =
      (TauCeti.AdditiveGroup.schemePointsMulEquiv (R := K) S).symm
        (.ofAdd (f (Multiplicative.toAdd
          (TauCeti.UpperUnitriangularGroup.superdiagonalCoordinateHom n R r hr s) ij))) := by
  rw [unitriangularStageCoordinateMap_point K n r S hr]
  congr 1
  simp [unitriangularStageMap,
    TauCeti.UpperUnitriangularGroup.superdiagonalCoordinateHom_apply]

end AlgebraicGeometry
