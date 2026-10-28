/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.HopfAlgebra.GroupLike
public import AlgebraicGroupsTest.Algebra.HopfAlgebra.GroupLikeUnits

/-!
# Universal evaluation of a nonmonomial group-like unit

Let `R = ZMod 2 × ZMod 2` and `A = MonoidAlgebra R (Multiplicative ℤ)`.
Mathlib's universal evaluation `MonoidAlgebra.liftGroupLikeBialgHom` maps
`R[GroupLike R A]` to `A`. Its source has the canonical group-algebra Hopf
structure, since Mathlib's group-like carrier is a group.

The fixed basis point indexed by `ProductIdempotents.mixedGroupLike` evaluates
to that two-support point. Transport by `(TauCeti.GroupLike.map BialgHom)` identifies the
bundled image, and naturality of `GroupLike.toUnits` computes the image of its
unit, its inverse, and its square under `Units.map`. In particular, a monomial
source unit evaluates to a nonmonomial target unit, with a distinct inverse.
The square retains two supports and doubles the nonconstant integer weight.

The scalar unit `5` over `ZMod 6` gives the complementary image test:
`GroupLike.mem_range_toUnits` excludes it because its counit is not `1`, even
though its antipode agrees with its inverse.

## References

* Mathlib, `Mathlib.RingTheory.Bialgebra.MonoidAlgebra`, by Amelia Livingston,
  Yaël Dillies and Michał Mrugała: universal group-like evaluation and
  `MonoidAlgebra.isGroupLikeElem_single_one`.
* Mathlib, `Mathlib.RingTheory.HopfAlgebra.GroupLike` and
  `Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra`, by Yaël Dillies,
  Michał Mrugała and Amelia Livingston: the group-like carrier, its unit
  homomorphism, and the canonical Hopf structure on group algebras.
* Mathlib, `Mathlib.Algebra.Group.Units.Hom`, by Johan Commelin, Chris Hughes
  and Kevin Buzzard: `Units.map`.
* AlgebraicGroups, `Algebra.HopfAlgebra.GroupLike`: canonical group-like
  transport and naturality in units. The explicit product-idempotent point
  and residue-six scalar unit are from
  `AlgebraicGroupsTest.Algebra.HopfAlgebra.GroupLikeUnits`.
-/

@[expose] public noncomputable section

namespace MonoidAlgebra.GroupLikeEvaluation

local notation "R₂" => ZMod 2 × ZMod 2
local notation "G₂" => Multiplicative ℤ
local notation "A₂" => MonoidAlgebra R₂ G₂
local notation "B₂" => MonoidAlgebra R₂ (GroupLike R₂ A₂)

/-- The standard group-algebra Hopf structure for the fixture's group-like indexing group. -/
local instance groupLikeIndexHopfAlgebra : HopfAlgebra R₂ B₂ :=
  MonoidAlgebra.instHopfAlgebra (R := R₂) (A := R₂) (G := GroupLike R₂ A₂)

local notation "q" => ProductIdempotents.mixedGroupLike
local notation "E₂" => MonoidAlgebra.liftGroupLikeBialgHom (R := R₂) (A := A₂)
local notation "e₀" => ((1, 0) : R₂)
local notation "e₁" => ((0, 1) : R₂)
local notation "g" => Multiplicative.ofAdd (1 : ℤ)

/-- The basis group-like point indexed by the two-support product-idempotent point. -/
def mixedBasisPoint : GroupLike R₂ B₂ where
  val := single q 1
  isGroupLikeElem_val := MonoidAlgebra.isGroupLikeElem_single_one (R := R₂) (A := R₂) q

/-- The fixed source point has a single basis term with coefficient `1`. -/
@[simp] theorem mixedBasisPoint_val : (mixedBasisPoint : B₂) = single q 1 := rfl

/-- The inverse source point is the basis term indexed by the inverse target point. -/
@[simp] theorem mixedBasisPoint_inv_val :
    ((mixedBasisPoint⁻¹ : GroupLike R₂ B₂) : B₂) = single q⁻¹ 1 := by
  rw [GroupLike.val_inv, mixedBasisPoint_val]
  simpa only [HopfAlgebra.antipode_one] using
    (MonoidAlgebra.antipode_single (R := R₂) q (1 : R₂))

/-- The unit of the source point has the same monomial value. -/
@[simp] theorem mixedBasisPoint_toUnits_val :
    ((GroupLike.toUnits R₂ mixedBasisPoint : B₂ˣ) : B₂) = single q 1 := rfl

/-- The inverse source unit has value equal to the inverse-indexed basis term. -/
theorem mixedBasisPoint_toUnits_inv_val :
    (((GroupLike.toUnits R₂ mixedBasisPoint)⁻¹ : B₂ˣ) : B₂) = single q⁻¹ 1 := by
  rw [← map_inv]
  exact mixedBasisPoint_inv_val

/-- Universal evaluation sends the fixed basis point to the two-support combination. -/
theorem evaluation_mixedBasisPoint_val :
    E₂ (mixedBasisPoint : B₂) = ProductIdempotents.mixed := by
  rw [mixedBasisPoint_val]
  simp [MonoidAlgebra.liftGroupLikeBialgHom]

/-- The induced group-like map identifies the evaluated point with its indexing point. -/
@[simp] theorem evaluation_mixedBasisPoint : (TauCeti.GroupLike.map (E₂)) mixedBasisPoint = q := by
  apply GroupLike.ext
  simpa only [TauCeti.GroupLike.val_map, ProductIdempotents.mixedGroupLike_val]
    using evaluation_mixedBasisPoint_val

/-- Naturality identifies the evaluated source unit with the unit of the mixed point. -/
theorem unitsMap_mixedBasisPoint :
    Units.map (E₂).toAlgHom.toMonoidHom (GroupLike.toUnits R₂ mixedBasisPoint) =
      GroupLike.toUnits R₂ q := by
  rw [← GroupLike.toUnits_groupLikeMap, evaluation_mixedBasisPoint]

/-- The evaluated source unit has the explicit two-support target value. -/
theorem unitsMap_mixedBasisPoint_val :
    ((Units.map (E₂).toAlgHom.toMonoidHom
      (GroupLike.toUnits R₂ mixedBasisPoint) : A₂ˣ) : A₂) = ProductIdempotents.mixed := by
  rw [unitsMap_mixedBasisPoint, ProductIdempotents.mixedGroupLike_toUnits_val]

/-- Evaluating the inverse source unit gives the computed two-support inverse. -/
theorem unitsMap_mixedBasisPoint_inv_val :
    ((Units.map (E₂).toAlgHom.toMonoidHom
      ((GroupLike.toUnits R₂ mixedBasisPoint)⁻¹) : A₂ˣ) : A₂) =
      ProductIdempotents.mixedInverse := by
  simp only [map_inv, unitsMap_mixedBasisPoint,
    ProductIdempotents.mixedGroupLike_toUnits_inv_val]

/-- Homomorphism-level naturality evaluates the source unit's square to the
combination with doubled nonconstant weight, rather than cancelling it. -/
theorem unitsMap_mixedBasisPoint_square_val :
    ((Units.map (E₂).toAlgHom.toMonoidHom
      ((GroupLike.toUnits R₂ mixedBasisPoint) ^ 2) : A₂ˣ) : A₂) =
      single (g ^ 2) e₀ + single 1 e₁ := by
  have hn := DFunLike.congr_fun (GroupLike.toUnits_comp_groupLikeMap E₂)
    (mixedBasisPoint * mixedBasisPoint)
  have hu :
      Units.map (E₂).toAlgHom.toMonoidHom ((GroupLike.toUnits R₂ mixedBasisPoint) ^ 2) =
        GroupLike.toUnits R₂ (q * q) := by
    simpa only [MonoidHom.comp_apply, map_mul, pow_two, evaluation_mixedBasisPoint]
      using hn.symm
  rw [hu]
  exact ProductIdempotents.mixedGroupLike_toUnits_mul_self_val

/-- No scalar multiple of a group basis term is the value of the evaluated source unit. -/
theorem unitsMap_mixedBasisPoint_ne_single (k : G₂) (c : R₂) :
    ((Units.map (E₂).toAlgHom.toMonoidHom
      (GroupLike.toUnits R₂ mixedBasisPoint) : A₂ˣ) : A₂) ≠ single k c := by
  rw [unitsMap_mixedBasisPoint_val]
  exact ProductIdempotents.mixed_ne_single k c

private theorem mixedGroupLike_ne_inverse : q ≠ q⁻¹ := by
  intro h
  apply ProductIdempotents.mixed_ne_inverse
  simpa only [ProductIdempotents.mixedGroupLike_val,
    ProductIdempotents.mixedGroupLike_inv_val]
    using congrArg (GroupLike.val (R := R₂) (A := A₂)) h

/-- Injectivity of the group-like-to-unit map distinguishes the evaluated
source unit from the evaluated inverse source unit. -/
theorem unitsMap_mixedBasisPoint_ne_inverse :
    Units.map (E₂).toAlgHom.toMonoidHom (GroupLike.toUnits R₂ mixedBasisPoint) ≠
      Units.map (E₂).toAlgHom.toMonoidHom ((GroupLike.toUnits R₂ mixedBasisPoint)⁻¹) := by
  intro h
  have hu : GroupLike.toUnits R₂ q = GroupLike.toUnits R₂ (q⁻¹) := by
    simpa only [map_inv, unitsMap_mixedBasisPoint] using h
  exact mixedGroupLike_ne_inverse (GroupLike.toUnits_injective (R := R₂) (A := A₂) hu)

local notation "R₆" => ZMod 6
local notation "A₆" => MonoidAlgebra R₆ (Multiplicative ℤ)

/-- The full group-like image criterion excludes the scalar unit `5`:
its counit fails normalization, despite agreement of antipode and inverse. -/
theorem scalarFiveUnit_not_mem_range_toUnits :
    ResidueSix.scalarFiveUnit ∉ Set.range (GroupLike.toUnits R₆ (A := A₆)) := by
  intro hu
  have hg := (GroupLike.mem_range_toUnits (R := R₆) (A := A₆) ResidueSix.scalarFiveUnit).mp hu
  exact ResidueSix.scalarFive_counit_ne_one (by
    simpa only [ResidueSix.scalarFiveUnit_val] using hg.counit_eq_one)

end MonoidAlgebra.GroupLikeEvaluation
