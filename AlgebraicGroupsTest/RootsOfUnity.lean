/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AlgebraicGroups.GroupScheme.RootsOfUnity
import Mathlib.Tactic.NormNum

/-!
# Rational roots of unity and their canonical inclusion

The order-zero unit two, root, character, algebra map and nonidentity affine
point below are constructed using Mathlib's units, integer powers, group-algebra
lift and affine `Spec` equivalence. Their construction and separation from the
identity do not use the roots-of-unity character equivalences or the zero-order
comparison. The comparison equations also identify its image under the canonical
inclusion. At order two, the rational root `−1` has a nonidentity image in `Gₘ`
whose square is one. These separations use no scheme-theoretic kernel theorem.
The kernel universal property identifies this explicit root point as the unique
lift of that multiplicative-group point. A positive-order polynomial coordinate
equation over the zero ring records the other boundary.
-/

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

private def rationalTwoUnit : ℚˣ :=
  Units.mk0 (2 : ℚ) (by norm_num)

private theorem rationalTwoUnit_value : (rationalTwoUnit : ℚ) = 2 := rfl

private def rationalTwoRoot : rootsOfUnity 0 ℚ :=
  ⟨rationalTwoUnit, by
    change rationalTwoUnit ^ 0 = 1
    exact pow_zero _⟩

private theorem rationalTwoRoot_value : ((rationalTwoRoot : ℚˣ) : ℚ) = 2 := rfl

private theorem rationalTwoRoot_ne_one : rationalTwoRoot ≠ 1 := by
  intro h
  have hv := congrArg (fun ζ : rootsOfUnity 0 ℚ ↦ ((ζ : ℚˣ) : ℚ)) h
  change (2 : ℚ) = 1 at hv
  norm_num at hv

private def rationalTwoCharacter : Multiplicative (ZMod 0) →* ℚ :=
  (Units.coeHom ℚ).comp (zpowersMulHom ℚˣ rationalTwoUnit)

private theorem rationalTwoCharacter_generator :
    rationalTwoCharacter (.ofAdd 1) = 2 := by
  -- At order zero, normalize the carrier and its instances to the integer domain.
  change ((Units.coeHom ℚ).comp (zpowersMulHom ℚˣ rationalTwoUnit))
    (Multiplicative.ofAdd (1 : ℤ)) = 2
  calc
    _ = (rationalTwoUnit : ℚ) := by
      rw [MonoidHom.comp_apply, zpowersMulHom_apply, toAdd_ofAdd, zpow_one,
        Units.coeHom_apply]
    _ = 2 := rationalTwoUnit_value

private def rationalTwoAlgHom : rootsOfUnityCoordinateRing ℚ 0 →ₐ[ℚ] ℚ :=
  AddMonoidAlgebra.lift ℚ ℚ (ZMod 0) rationalTwoCharacter

private theorem rationalTwoAlgHom_generator :
    rationalTwoAlgHom (rootsOfUnityCoordinateGenerator ℚ 0) = 2 := by
  change AddMonoidAlgebra.lift ℚ ℚ (ZMod 0) rationalTwoCharacter
    (AddMonoidAlgebra.single 1 1) = 2
  rw [AddMonoidAlgebra.lift_single, one_smul]
  exact rationalTwoCharacter_generator

private def rationalTwoPoint :
    (Spec (.of ℚ)).asOver (Spec (.of ℚ)) ⟶ rootsOfUnityScheme ℚ 0 :=
  Spec.mapMulEquiv
    (R := ℚ) (S := rootsOfUnityCoordinateRing ℚ 0) (T := ℚ)
    (WithConv.toConv rationalTwoAlgHom)

private theorem rationalTwoPoint_ne_one : rationalTwoPoint ≠ 1 := by
  intro hp
  have hconv : WithConv.toConv rationalTwoAlgHom =
      (1 : WithConv (rootsOfUnityCoordinateRing ℚ 0 →ₐ[ℚ] ℚ)) := by
    apply (Spec.mapMulEquiv
      (R := ℚ) (S := rootsOfUnityCoordinateRing ℚ 0) (T := ℚ)).injective
    simpa only [rationalTwoPoint, map_one] using hp
  have heval := congrArg
    (fun f : WithConv (rootsOfUnityCoordinateRing ℚ 0 →ₐ[ℚ] ℚ) ↦
      f.ofConv (rootsOfUnityCoordinateGenerator ℚ 0)) hconv
  have hcounit : Coalgebra.counit (R := ℚ)
      (AddMonoidAlgebra.single (1 : ZMod 0) (1 : ℚ)) = 1 :=
    (AddMonoidAlgebra.isGroupLikeElem_single_one
      (R := ℚ) (A := ℚ) (1 : ZMod 0)).counit_eq_one
  have hone : (1 : WithConv (rootsOfUnityCoordinateRing ℚ 0 →ₐ[ℚ] ℚ)).ofConv
      (rootsOfUnityCoordinateGenerator ℚ 0) = (1 : ℚ) := by
    change (1 : WithConv (rootsOfUnityCoordinateRing ℚ 0 →ₐ[ℚ] ℚ))
      (AddMonoidAlgebra.single (1 : ZMod 0) (1 : ℚ)) = 1
    rw [AlgHom.convOne_apply, hcounit, map_one]
  have htwo : (2 : ℚ) = 1 := by
    calc
      (2 : ℚ) = rationalTwoAlgHom (rootsOfUnityCoordinateGenerator ℚ 0) :=
        rationalTwoAlgHom_generator.symm
      _ = (1 : WithConv (rootsOfUnityCoordinateRing ℚ 0 →ₐ[ℚ] ℚ)).ofConv
          (rootsOfUnityCoordinateGenerator ℚ 0) := heval
      _ = 1 := hone
  norm_num at htwo

-- Comparison obligations are separate from the stock constructions and proofs above.
private theorem rationalTwo_character_comparison :
    RootsOfUnity.equivMonoidHom 0 rationalTwoRoot = rationalTwoCharacter := by
  change RootsOfUnity.rootMonoidHom rationalTwoRoot = rationalTwoCharacter
  apply MonoidHom.ext_mint
  calc
    RootsOfUnity.rootMonoidHom rationalTwoRoot (.ofAdd 1) =
        ((rationalTwoRoot : ℚˣ) : ℚ) :=
      RootsOfUnity.rootMonoidHom_generator rationalTwoRoot
    _ = 2 := rationalTwoRoot_value
    _ = rationalTwoCharacter (.ofAdd 1) := rationalTwoCharacter_generator.symm

private theorem rationalTwo_algHom_comparison :
    (rootsOfUnityMulEquivAlgHom ℚ ℚ 0 rationalTwoRoot).ofConv = rationalTwoAlgHom := by
  rw [rootsOfUnityMulEquivAlgHom_apply]
  exact congrArg (AddMonoidAlgebra.lift ℚ ℚ (ZMod 0)) rationalTwo_character_comparison

private theorem rationalTwo_point_comparison :
    rootsOfUnityMulEquivPoints ℚ ℚ 0 rationalTwoRoot = rationalTwoPoint := by
  apply Over.OverMorphism.ext
  rw [rootsOfUnityMulEquivPoints_apply_left, rationalTwo_algHom_comparison]
  rfl

private theorem rationalTwo_multiplicativePoint_comparison :
    rationalTwoPoint ≫ (rootsOfUnityGroupSchemeZeroIsoMultiplicativeGroup ℚ).hom.hom.hom =
      multiplicativeGroupMulEquivPoints ℚ ℚ rationalTwoUnit := by
  rw [← rationalTwo_point_comparison]
  exact rootsOfUnityGroupSchemeZeroIsoMultiplicativeGroup_point ℚ ℚ rationalTwoRoot

private theorem rationalTwo_inclusion_zero_comparison :
    rationalTwoPoint ≫ (rootsOfUnityGroupSchemeInclusion ℚ 0).hom.hom =
      rationalTwoPoint ≫
        (rootsOfUnityGroupSchemeZeroIsoMultiplicativeGroup ℚ).hom.hom.hom := by
  calc
    _ = multiplicativeGroupMulEquivPoints ℚ ℚ rationalTwoUnit := by
      rw [← rationalTwo_point_comparison]
      exact rootsOfUnityGroupSchemeInclusion_point ℚ ℚ 0 rationalTwoRoot
    _ = _ := rationalTwo_multiplicativePoint_comparison.symm

private def rationalNegOneRoot : rootsOfUnity 2 ℚ :=
  rootsOfUnity.mkOfPowEq (-1 : ℚ) (n := 2) (by norm_num)

private theorem rationalNegOneRoot_unit_ne_one : (rationalNegOneRoot : ℚˣ) ≠ 1 := by
  intro h
  have hv := congrArg (fun a : ℚˣ ↦ (a : ℚ)) h
  change (-1 : ℚ) = 1 at hv
  norm_num at hv

private theorem rationalNegOne_multiplicativePoint_ne_one :
    multiplicativeGroupMulEquivPoints ℚ ℚ (rationalNegOneRoot : ℚˣ) ≠ 1 := by
  intro h
  apply rationalNegOneRoot_unit_ne_one
  apply (multiplicativeGroupMulEquivPoints ℚ ℚ).injective
  simpa only [map_one] using h

/-- The canonical inclusion has a nonidentity rational image at order two,
and that image is killed by the stock square endomorphism. -/
private theorem rationalNegOne_inclusion_model :
    (rootsOfUnityMulEquivPoints ℚ ℚ 2 rationalNegOneRoot ≫
        (rootsOfUnityGroupSchemeInclusion ℚ 2).hom.hom =
      multiplicativeGroupMulEquivPoints ℚ ℚ (rationalNegOneRoot : ℚˣ)) ∧
    (rootsOfUnityMulEquivPoints ℚ ℚ 2 rationalNegOneRoot ≫
        (rootsOfUnityGroupSchemeInclusion ℚ 2).hom.hom ≠ 1) ∧
    ((rootsOfUnityMulEquivPoints ℚ ℚ 2 rationalNegOneRoot ≫
        (rootsOfUnityGroupSchemeInclusion ℚ 2).hom.hom) ≫
        ((𝟙 (multiplicativeGroupScheme ℚ)) ^ (2 : ℕ)).hom.hom = 1) := by
  refine ⟨rootsOfUnityGroupSchemeInclusion_point ℚ ℚ 2 rationalNegOneRoot, ?_, ?_⟩
  · rw [rootsOfUnityGroupSchemeInclusion_point]
    exact rationalNegOne_multiplicativePoint_ne_one
  · rw [rootsOfUnityGroupSchemeInclusion_point, Grp.Hom.hom_pow, Mon.Hom.hom_pow]
    change multiplicativeGroupMulEquivPoints ℚ ℚ (rationalNegOneRoot : ℚˣ) ≫
      (𝟙 (multiplicativeGroupUnderlyingScheme ℚ)) ^ (2 : ℕ) = 1
    rw [MonObj.comp_pow, Category.comp_id, ← map_pow, rationalNegOneRoot.prop, map_one]

/-- A lift of the rational `−1` point through the order-two inclusion is exactly
its explicitly constructed root point. -/
private theorem rationalNegOne_lift_iff
    (candidate : (Spec (.of ℚ)).asOver (Spec (.of ℚ)) ⟶ rootsOfUnityScheme ℚ 2) :
    candidate ≫ (rootsOfUnityGroupSchemeInclusion ℚ 2).hom.hom =
        multiplicativeGroupMulEquivPoints ℚ ℚ (rationalNegOneRoot : ℚˣ) ↔
      candidate = rootsOfUnityMulEquivPoints ℚ ℚ 2 rationalNegOneRoot := by
  have hpower := rationalNegOne_inclusion_model.2.2
  rw [rationalNegOne_inclusion_model.1] at hpower
  obtain ⟨lift, _, unique⟩ := rootsOfUnitySchemeKernel_universal ℚ 2
    ((Spec (.of ℚ)).asOver (Spec (.of ℚ)))
    (multiplicativeGroupMulEquivPoints ℚ ℚ (rationalNegOneRoot : ℚˣ)) (by
      simpa only [CategoryTheory.Hom.one_def] using hpower)
  constructor
  · intro h
    exact (unique candidate h).trans
      (unique (rootsOfUnityMulEquivPoints ℚ ℚ 2 rationalNegOneRoot)
        rationalNegOne_inclusion_model.1).symm
  · rintro rfl
    exact rationalNegOne_inclusion_model.1

private theorem positiveCoordinate_zeroRing :
    rootsOfUnityCoordinateAlgEquiv (ZMod 1) 2
        (rootsOfUnityCoordinateGenerator (ZMod 1) 2) =
      AdjoinRoot.root (rootsOfUnityPolynomial (ZMod 1) 2) :=
  rootsOfUnityCoordinateAlgEquiv_generator (ZMod 1) 2

end AlgebraicGeometry

namespace AlgebraicGeometry

/-- Order-zero roots of unity over `ℚ` retain finite presentation, flatness and
local finite presentation, with Laurent coordinates. -/
private theorem rootsOfUnity_rational_zero_properties :
    Algebra.FinitePresentation ℚ (rootsOfUnityCoordinateRing ℚ 0) ∧
      Flat (rootsOfUnityScheme ℚ 0).hom ∧
      LocallyOfFinitePresentation (rootsOfUnityScheme ℚ 0).hom :=
  ⟨rootsOfUnityCoordinateRing_finitePresentation ℚ 0,
    rootsOfUnityScheme_flat ℚ 0,
    rootsOfUnityScheme_locallyOfFinitePresentation ℚ 0⟩

end AlgebraicGeometry
