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

private def rationalTwoCharacter :
    TauCeti.RootsOfUnityGroup.characterGroup.{0} 0 →* ℚ :=
  (Units.coeHom ℚ).comp
    ((zpowersMulHom ℚˣ rationalTwoUnit).comp MulEquiv.ulift.toMonoidHom)

private theorem rationalTwoCharacter_generator :
    rationalTwoCharacter (ULift.up (TauCeti.RootsOfUnityGroup.generator 0)) = 2 := by
  -- At order zero, normalize the carrier and its instances to the integer domain.
  change ((Units.coeHom ℚ).comp (zpowersMulHom ℚˣ rationalTwoUnit))
    (Multiplicative.ofAdd (1 : ℤ)) = 2
  simp [zpowersMulHom_apply, rationalTwoUnit_value]

private def rationalTwoAlgHom :
    MonoidAlgebra ℚ (TauCeti.RootsOfUnityGroup.characterGroup.{0} 0) →ₐ[ℚ] ℚ :=
  MonoidAlgebra.lift ℚ ℚ _ rationalTwoCharacter

private theorem rationalTwoAlgHom_generator :
    rationalTwoAlgHom
      (MonoidAlgebra.single (ULift.up (TauCeti.RootsOfUnityGroup.generator 0)) 1) = 2 := by
  rw [rationalTwoAlgHom, MonoidAlgebra.lift_single, one_smul]
  exact rationalTwoCharacter_generator

private def rationalTwoPoint :
    (Spec (.of ℚ)).asOver (Spec (.of ℚ)) ⟶
      (TauCeti.RootsOfUnityGroup.groupScheme ℚ 0).X :=
  (TauCeti.DiagonalizableGroup.groupSchemePointsMulEquiv
    (R := ℚ) (A := ℚ) (TauCeti.RootsOfUnityGroup.characterGroup.{0} 0)).symm
      (WithConv.toConv rationalTwoAlgHom)

private theorem rationalTwoPoint_ne_one : rationalTwoPoint ≠ 1 := by
  intro hp
  have hconv : WithConv.toConv rationalTwoAlgHom =
      (1 : WithConv (MonoidAlgebra ℚ
        (TauCeti.RootsOfUnityGroup.characterGroup.{0} 0) →ₐ[ℚ] ℚ)) := by
    apply (TauCeti.DiagonalizableGroup.groupSchemePointsMulEquiv
      (R := ℚ) (A := ℚ) (TauCeti.RootsOfUnityGroup.characterGroup.{0} 0)).symm.injective
    simpa only [rationalTwoPoint, map_one] using hp
  have heval := congrArg
    (fun f : WithConv (MonoidAlgebra ℚ
        (TauCeti.RootsOfUnityGroup.characterGroup.{0} 0) →ₐ[ℚ] ℚ) ↦
      f.ofConv (MonoidAlgebra.single
        (ULift.up (TauCeti.RootsOfUnityGroup.generator 0)) 1)) hconv
  have hcounit : Coalgebra.counit (R := ℚ)
      (MonoidAlgebra.single (ULift.up (TauCeti.RootsOfUnityGroup.generator 0)) (1 : ℚ) :
        MonoidAlgebra ℚ (TauCeti.RootsOfUnityGroup.characterGroup.{0} 0)) = 1 :=
    (MonoidAlgebra.isGroupLikeElem_single_one _).counit_eq_one
  have htwo : (2 : ℚ) = 1 := by
    simpa only [WithConv.ofConv_toConv, rationalTwoAlgHom_generator,
      AlgHom.convOne_apply, hcounit, map_one] using heval
  norm_num at htwo

-- Comparison obligations are separate from the stock constructions and proofs above.
private theorem rationalTwo_point_comparison :
    (TauCeti.RootsOfUnityGroup.schemePointsMulEquiv (R := ℚ) (A := ℚ) 0).symm
      rationalTwoRoot = rationalTwoPoint := by
  apply (TauCeti.RootsOfUnityGroup.schemePointsMulEquiv (R := ℚ) (A := ℚ) 0).injective
  apply Subtype.ext
  apply Units.ext
  rw [MulEquiv.apply_symm_apply, TauCeti.RootsOfUnityGroup.schemePointsMulEquiv_apply_coe]
  simp only [rationalTwoPoint, MulEquiv.apply_symm_apply, WithConv.ofConv_toConv]
  exact rationalTwoRoot_value.trans rationalTwoAlgHom_generator.symm

private theorem rationalTwo_multiplicativePoint_comparison :
    rationalTwoPoint ≫ (TauCeti.RootsOfUnityGroup.inclusionGroupSchemeMap ℚ 0).hom.hom =
      (TauCeti.DiagonalizableGroup.multiplicativeGroupSchemePointsMulEquiv
        (R := ℚ) (A := ℚ)).symm rationalTwoUnit := by
  apply (TauCeti.DiagonalizableGroup.multiplicativeGroupSchemePointsMulEquiv
    (R := ℚ) (A := ℚ)).injective
  rw [TauCeti.RootsOfUnityGroup.multiplicativeGroupSchemePointsMulEquiv_inclusionGroupSchemeMap,
    ← rationalTwo_point_comparison, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  rfl

private theorem rationalTwo_inclusion_zero_comparison :
    rationalTwoPoint ≫ (TauCeti.RootsOfUnityGroup.inclusionGroupSchemeMap ℚ 0).hom.hom =
      rationalTwoPoint := by
  have hq : TauCeti.RootsOfUnityGroup.characterQuotient.{0} 0 =
      𝟙 TauCeti.DiagonalizableGroup.multiplicativeCharacterGroup := by
    apply TauCeti.FGCommGrpCat.hom_ext
    apply MonoidHom.ext
    rintro ⟨x⟩
    rw [TauCeti.RootsOfUnityGroup.characterQuotient_apply_up]
    obtain ⟨z, rfl⟩ := Multiplicative.ofAdd.surjective x
    rw [TauCeti.RootsOfUnityGroup.toMultiplicativeZMod_ofAdd]
    rfl
  rw [TauCeti.RootsOfUnityGroup.inclusionGroupSchemeMap_def, hq]
  erw [TauCeti.DiagonalizableGroup.groupSchemeMap_id]
  rfl

private def rationalNegOneRoot : rootsOfUnity 2 ℚ :=
  rootsOfUnity.mkOfPowEq (-1 : ℚ) (n := 2) (by norm_num)

private theorem rationalNegOneRoot_unit_ne_one : (rationalNegOneRoot : ℚˣ) ≠ 1 := by
  intro h
  have hv := congrArg (fun a : ℚˣ ↦ (a : ℚ)) h
  change (-1 : ℚ) = 1 at hv
  norm_num at hv

private theorem rationalNegOne_multiplicativePoint_ne_one :
    (TauCeti.DiagonalizableGroup.multiplicativeGroupSchemePointsMulEquiv (R := ℚ) (A := ℚ)).symm
      (rationalNegOneRoot : ℚˣ) ≠ 1 := by
  intro h
  apply rationalNegOneRoot_unit_ne_one
  apply ((TauCeti.DiagonalizableGroup.multiplicativeGroupSchemePointsMulEquiv (R := ℚ) (A :=
    ℚ)).symm).injective
  simpa only [map_one] using h

/-- The canonical inclusion has a nonidentity rational image at order two,
and that image is killed by the stock square endomorphism. -/
private theorem rationalNegOne_inclusion_model :
    ((TauCeti.RootsOfUnityGroup.schemePointsMulEquiv (R := ℚ) (A := ℚ) 2).symm rationalNegOneRoot ≫
        (TauCeti.RootsOfUnityGroup.inclusionGroupSchemeMap ℚ 2).hom.hom =
      (TauCeti.DiagonalizableGroup.multiplicativeGroupSchemePointsMulEquiv (R := ℚ) (A := ℚ)).symm
        (rationalNegOneRoot : ℚˣ)) ∧
    ((TauCeti.RootsOfUnityGroup.schemePointsMulEquiv (R := ℚ) (A := ℚ) 2).symm rationalNegOneRoot ≫
        (TauCeti.RootsOfUnityGroup.inclusionGroupSchemeMap ℚ 2).hom.hom ≠ 1) ∧
    (((TauCeti.RootsOfUnityGroup.schemePointsMulEquiv (R := ℚ) (A := ℚ) 2).symm rationalNegOneRoot ≫
        (TauCeti.RootsOfUnityGroup.inclusionGroupSchemeMap ℚ 2).hom.hom) ≫
        ((𝟙 (TauCeti.DiagonalizableGroup.multiplicativeGroupScheme ℚ)) ^ (2 : ℕ)).hom.hom = 1) := by
  have hpoint :
      (TauCeti.RootsOfUnityGroup.schemePointsMulEquiv (R := ℚ) (A := ℚ) 2).symm
          rationalNegOneRoot ≫
        (TauCeti.RootsOfUnityGroup.inclusionGroupSchemeMap ℚ 2).hom.hom =
      (TauCeti.DiagonalizableGroup.multiplicativeGroupSchemePointsMulEquiv
        (R := ℚ) (A := ℚ)).symm (rationalNegOneRoot : ℚˣ) := by
    apply (TauCeti.DiagonalizableGroup.multiplicativeGroupSchemePointsMulEquiv
      (R := ℚ) (A := ℚ)).injective
    simp
  refine ⟨hpoint, ?_, ?_⟩
  · rw [hpoint]
    exact rationalNegOne_multiplicativePoint_ne_one
  · rw [hpoint, Grp.Hom.hom_pow, Mon.Hom.hom_pow]
    change (TauCeti.DiagonalizableGroup.multiplicativeGroupSchemePointsMulEquiv
      (R := ℚ) (A := ℚ)).symm (rationalNegOneRoot : ℚˣ) ≫
        (𝟙 ((TauCeti.DiagonalizableGroup.multiplicativeGroupScheme ℚ).X)) ^ (2 : ℕ) = 1
    rw [MonObj.comp_pow, Category.comp_id, ← map_pow, rationalNegOneRoot.prop, map_one]

/-- A lift of the rational `−1` point through the order-two inclusion is exactly
its explicitly constructed root point. -/
private theorem rationalNegOne_lift_iff
    (candidate : (Spec (.of ℚ)).asOver (Spec (.of ℚ)) ⟶ (TauCeti.RootsOfUnityGroup.groupScheme ℚ
      2).X) :
    candidate ≫ (TauCeti.RootsOfUnityGroup.inclusionGroupSchemeMap ℚ 2).hom.hom =
        (TauCeti.DiagonalizableGroup.multiplicativeGroupSchemePointsMulEquiv (R := ℚ) (A :=
          ℚ)).symm (rationalNegOneRoot : ℚˣ) ↔
      candidate = (TauCeti.RootsOfUnityGroup.schemePointsMulEquiv (R := ℚ) (A := ℚ) 2).symm
        rationalNegOneRoot := by
  have hpower := rationalNegOne_inclusion_model.2.2
  rw [rationalNegOne_inclusion_model.1] at hpower
  obtain ⟨lift, _, unique⟩ := rootsOfUnitySchemeKernel_universal ℚ 2
    ((Spec (.of ℚ)).asOver (Spec (.of ℚ)))
    ((TauCeti.DiagonalizableGroup.multiplicativeGroupSchemePointsMulEquiv (R := ℚ) (A := ℚ)).symm
      (rationalNegOneRoot : ℚˣ)) (by
      simpa only [CategoryTheory.Hom.one_def] using hpower)
  constructor
  · intro h
    exact (unique candidate h).trans
      (unique ((TauCeti.RootsOfUnityGroup.schemePointsMulEquiv (R := ℚ) (A := ℚ) 2).symm
        rationalNegOneRoot)
        rationalNegOne_inclusion_model.1).symm
  · rintro rfl
    exact rationalNegOne_inclusion_model.1

private theorem positiveCoordinate_zeroRing :
    (TauCeti.RootsOfUnityGroup.adjoinRootEquiv (R := ZMod 1) 2).symm
      (MonoidAlgebra.single (TauCeti.RootsOfUnityGroup.generator 2) 1) =
        AdjoinRoot.root (Polynomial.X ^ 2 - 1 : Polynomial (ZMod 1)) :=
  TauCeti.RootsOfUnityGroup.adjoinRootEquiv_symm_single_generator 2

/-- Order-zero roots of unity over ℚ retain finite presentation, flatness and
local finite presentation, with canonical cyclic coordinates. -/
private theorem rootsOfUnity_rational_zero_properties :
    Algebra.FinitePresentation ℚ
        (MonoidAlgebra ℚ (TauCeti.RootsOfUnityGroup.characterGroup.{0} 0)) ∧
      Flat (TauCeti.RootsOfUnityGroup.groupScheme ℚ 0).X.hom ∧
      LocallyOfFinitePresentation (TauCeti.RootsOfUnityGroup.groupScheme ℚ 0).X.hom :=
  ⟨rootsOfUnityCoordinate_finitePresentation ℚ 0,
    rootsOfUnityScheme_flat ℚ 0,
    rootsOfUnityScheme_locallyOfFinitePresentation ℚ 0⟩

end AlgebraicGeometry
