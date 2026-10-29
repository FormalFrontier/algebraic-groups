/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.InfinitesimalAdditiveTranslation
import Mathlib.Algebra.Field.ZMod

/-!
# Infinitesimal-additive translation point tests

These clients check translation by one on coordinates and points, including height zero
and zero-ring targets.
-/

set_option warningAsError true

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable (K : Type u) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (m : ℕ)

private def generic_equiv_test :
    rootsOfUnityCoordinateRing K (p ^ m) ≃ₐ[K]
      infinitesimalAdditiveCoordinateRing K p m :=
  infinitesimalAdditiveTranslationAlgEquiv K p m

private theorem generic_generator_test :
    infinitesimalAdditiveTranslationAlgEquiv K p m
      (rootsOfUnityCoordinateGenerator K (p ^ m)) =
        1 + infinitesimalAdditiveCoordinate K p m := by
  simp

private theorem generic_inverse_generator_test :
    (infinitesimalAdditiveTranslationAlgEquiv K p m).symm
      (infinitesimalAdditiveCoordinate K p m) =
        rootsOfUnityCoordinateGenerator K (p ^ m) - 1 := by
  simp

private def generic_scheme_iso_test :
    infinitesimalAdditiveUnderlyingScheme K p m ≅ rootsOfUnityScheme K (p ^ m) :=
  infinitesimalAdditiveTranslationIso K p m

private theorem generic_scheme_map_test :
    (infinitesimalAdditiveTranslationIso K p m).hom.left =
      Spec.map (CommRingCat.ofHom
        (infinitesimalAdditiveTranslationAlgEquiv K p m).toAlgHom.toRingHom) :=
  infinitesimalAdditiveTranslationIso_hom_left K p m

private theorem generic_scheme_inverse_map_test :
    (infinitesimalAdditiveTranslationIso K p m).inv.left =
      Spec.map (CommRingCat.ofHom
        (infinitesimalAdditiveTranslationAlgEquiv K p m).symm.toAlgHom.toRingHom) :=
  infinitesimalAdditiveTranslationIso_inv_left K p m

private theorem generic_point_forward_test
    (R : Type u) [CommRing R] [Algebra K R]
    (sigma : infinitesimalAdditiveCoordinateRing K p m →ₐ[K] R) :
    (sigma.comp (infinitesimalAdditiveTranslationAlgEquiv K p m).toAlgHom)
      (rootsOfUnityCoordinateGenerator K (p ^ m)) =
        1 + sigma (infinitesimalAdditiveCoordinate K p m) := by
  simp

private theorem generic_point_inverse_test
    (R : Type u) [CommRing R] [Algebra K R]
    (rho : rootsOfUnityCoordinateRing K (p ^ m) →ₐ[K] R) :
    (rho.comp (infinitesimalAdditiveTranslationAlgEquiv K p m).symm.toAlgHom)
      (infinitesimalAdditiveCoordinate K p m) =
        rho (rootsOfUnityCoordinateGenerator K (p ^ m)) - 1 := by
  simp

private theorem generic_naturality_test
    (R S : Type u) [CommRing R] [Algebra K R] [CommRing S] [Algebra K S]
    (sigma : infinitesimalAdditiveCoordinateRing K p m →ₐ[K] R)
    (f : R →ₐ[K] S) :
    f.comp (sigma.comp (infinitesimalAdditiveTranslationAlgEquiv K p m).toAlgHom) =
      (f.comp sigma).comp (infinitesimalAdditiveTranslationAlgEquiv K p m).toAlgHom :=
  infinitesimalAdditiveTranslation_point_naturality K p m R S sigma f

private theorem generic_inverse_naturality_test
    (R S : Type u) [CommRing R] [Algebra K R] [CommRing S] [Algebra K S]
    (rho : rootsOfUnityCoordinateRing K (p ^ m) →ₐ[K] R)
    (f : R →ₐ[K] S) :
    f.comp (rho.comp (infinitesimalAdditiveTranslationAlgEquiv K p m).symm.toAlgHom) =
      (f.comp rho).comp (infinitesimalAdditiveTranslationAlgEquiv K p m).symm.toAlgHom :=
  infinitesimalAdditiveTranslation_point_symm_naturality K p m R S rho f

/-- Translation by one sends the roots-of-unity generator to one plus the additive point. -/
public theorem infinitesimalAdditiveTranslation_additive_point_generator
    (R : Type u) [CommRing R] [Algebra K R]
    (r : infinitesimalAdditiveSubgroup K p m R) :
    ((infinitesimalAdditiveMulEquivAlgHom K p m R (.ofAdd r)).ofConv.comp
      (infinitesimalAdditiveTranslationAlgEquiv K p m).toAlgHom)
        (rootsOfUnityCoordinateGenerator K (p ^ m)) = 1 + r.val := by
  rw [infinitesimalAdditiveTranslation_point_generator,
    infinitesimalAdditiveMulEquivAlgHom_coordinate]

private theorem existing_roots_point_coordinate_test
    (R : Type u) [CommRing R] [Algebra K R]
    (zeta : rootsOfUnity (p ^ m) R) :
    ((rootsOfUnityMulEquivAlgHom K R (p ^ m) zeta).ofConv.comp
      (infinitesimalAdditiveTranslationAlgEquiv K p m).symm.toAlgHom)
        (infinitesimalAdditiveCoordinate K p m) = zeta.val - 1 := by
  rw [infinitesimalAdditiveTranslation_point_coordinate]
  simp [rootsOfUnityCoordinateGenerator, rootsOfUnityMulEquivAlgHom_apply]

private instance translation_test_fact_prime_two : Fact (Nat.Prime 2) := ⟨by decide⟩
private instance translation_test_fact_prime_three : Fact (Nat.Prime 3) := ⟨by decide⟩

private theorem zero_target_forward_test
    (sigma : infinitesimalAdditiveCoordinateRing (ZMod 2) 2 1 →ₐ[ZMod 2] PUnit) :
    (sigma.comp (infinitesimalAdditiveTranslationAlgEquiv (ZMod 2) 2 1).toAlgHom)
      (rootsOfUnityCoordinateGenerator (ZMod 2) (2 ^ 1)) =
        1 + sigma (infinitesimalAdditiveCoordinate (ZMod 2) 2 1) := by
  simp

private theorem zero_target_inverse_test
    (rho : rootsOfUnityCoordinateRing (ZMod 2) (2 ^ 1) →ₐ[ZMod 2] PUnit) :
    (rho.comp (infinitesimalAdditiveTranslationAlgEquiv (ZMod 2) 2 1).symm.toAlgHom)
      (infinitesimalAdditiveCoordinate (ZMod 2) 2 1) =
        rho (rootsOfUnityCoordinateGenerator (ZMod 2) (2 ^ 1)) - 1 := by
  simp

private def zmod2_zero_scheme_test :
    infinitesimalAdditiveUnderlyingScheme (ZMod 2) 2 0 ≅
      rootsOfUnityScheme (ZMod 2) (2 ^ 0) :=
  infinitesimalAdditiveTranslationIso (ZMod 2) 2 0

private theorem zmod2_zero_coordinate_test :
    infinitesimalAdditiveTranslationAlgEquiv (ZMod 2) 2 0
        (rootsOfUnityCoordinateGenerator (ZMod 2) (2 ^ 0)) =
          1 + infinitesimalAdditiveCoordinate (ZMod 2) 2 0 ∧
      (infinitesimalAdditiveTranslationAlgEquiv (ZMod 2) 2 0).symm
        (infinitesimalAdditiveCoordinate (ZMod 2) 2 0) =
          rootsOfUnityCoordinateGenerator (ZMod 2) (2 ^ 0) - 1 :=
  ⟨infinitesimalAdditiveTranslationAlgEquiv_generator (ZMod 2) 2 0,
    infinitesimalAdditiveTranslationAlgEquiv_symm_coordinate (ZMod 2) 2 0⟩

private theorem zmod2_one_generator_test :
    infinitesimalAdditiveTranslationAlgEquiv (ZMod 2) 2 1
      (rootsOfUnityCoordinateGenerator (ZMod 2) (2 ^ 1)) =
        1 + infinitesimalAdditiveCoordinate (ZMod 2) 2 1 :=
  infinitesimalAdditiveTranslationAlgEquiv_generator (ZMod 2) 2 1

private theorem zmod3_one_inverse_test :
    (infinitesimalAdditiveTranslationAlgEquiv (ZMod 3) 3 1).symm
      (infinitesimalAdditiveCoordinate (ZMod 3) 3 1) =
        rootsOfUnityCoordinateGenerator (ZMod 3) (3 ^ 1) - 1 :=
  infinitesimalAdditiveTranslationAlgEquiv_symm_coordinate (ZMod 3) 3 1

private theorem zmod3_one_scheme_map_test :
    (infinitesimalAdditiveTranslationIso (ZMod 3) 3 1).hom.left =
      Spec.map (CommRingCat.ofHom
        (infinitesimalAdditiveTranslationAlgEquiv (ZMod 3) 3 1).toAlgHom.toRingHom) :=
  infinitesimalAdditiveTranslationIso_hom_left (ZMod 3) 3 1

#print axioms generic_equiv_test
#print axioms generic_generator_test
#print axioms generic_inverse_generator_test
#print axioms generic_scheme_iso_test
#print axioms generic_scheme_map_test
#print axioms generic_scheme_inverse_map_test
#print axioms generic_point_forward_test
#print axioms generic_point_inverse_test
#print axioms generic_naturality_test
#print axioms generic_inverse_naturality_test
#print axioms infinitesimalAdditiveTranslation_additive_point_generator
#print axioms existing_roots_point_coordinate_test
#print axioms translation_test_fact_prime_two
#print axioms translation_test_fact_prime_three
#print axioms zero_target_forward_test
#print axioms zero_target_inverse_test
#print axioms zmod2_zero_scheme_test
#print axioms zmod2_zero_coordinate_test
#print axioms zmod2_one_generator_test
#print axioms zmod3_one_inverse_test
#print axioms zmod3_one_scheme_map_test

#print axioms AdjoinRoot.liftAlgHom
#print axioms AdjoinRoot.liftAlgHom_root
#print axioms AdjoinRoot.eval₂_root
#print axioms AdjoinRoot.algHom_ext
#print axioms AlgEquiv.ofAlgHom
#print axioms CommAlgCat.isoMk
#print axioms AlgebraicGeometry.algSpec
#print axioms AlgebraicGeometry.algSpec_map_left
#print axioms AlgebraicGeometry.algSpec_obj_hom
#print axioms AlgebraicGeometry.rootsOfUnityCoordinateAlgEquiv
#print axioms AlgebraicGeometry.rootsOfUnityCoordinateAlgEquiv_generator
#print axioms AlgebraicGeometry.rootsOfUnityCoordinateAlgEquiv_symm_root
#print axioms AlgebraicGeometry.additivePowerCoordinateAlgEquiv
#print axioms AlgebraicGeometry.additivePowerCoordinateAlgEquiv_coordinate
#print axioms AlgebraicGeometry.additivePowerCoordinateAlgEquiv_symm_root
#print axioms AlgebraicGeometry.infinitesimalAdditiveCoordinate_pow
#print axioms AlgebraicGeometry.infinitesimalAdditiveMulEquivAlgHom_coordinate
#print axioms CharP.cast_eq_zero
#print axioms Commute.add_pow_prime_pow_eq'

end AlgebraicGeometry

namespace AlgebraicGeometry

/-- The coordinate algebra of second roots of unity over `𝔽₂` has dimension two. -/
private theorem rootsOfUnity_zmod_two_finrank :
    Module.finrank (ZMod 2) (rootsOfUnityCoordinateRing (ZMod 2) 2) = 2 := by
  simpa only [ZMod.card] using
    Module.finrank_eq_card_basis (AddMonoidAlgebra.basis (ZMod 2) (ZMod 2))

/-- Translation carries the nonzero square-zero additive coordinate to `U - 1`
in the coordinate algebra of second roots of unity over `𝔽₂`. -/
private theorem rootsOfUnity_zmod_two_nonzero_square_zero :
    rootsOfUnityCoordinateGenerator (ZMod 2) 2 - 1 ≠ 0 ∧
      (rootsOfUnityCoordinateGenerator (ZMod 2) 2 - 1) ^ 2 = 0 := by
  let e := (infinitesimalAdditiveTranslationAlgEquiv (ZMod 2) 2 1).symm
  have ht : infinitesimalAdditiveCoordinate (ZMod 2) 2 1 ≠ 0 :=
    additivePowerCoordinate_ne_zero (ZMod 2) (2 ^ 1) (by decide)
  have ht_square : infinitesimalAdditiveCoordinate (ZMod 2) 2 1 ^ 2 = 0 := by
    simpa only [pow_one] using infinitesimalAdditiveCoordinate_pow (ZMod 2) 2 1
  have he : e (infinitesimalAdditiveCoordinate (ZMod 2) 2 1) =
      rootsOfUnityCoordinateGenerator (ZMod 2) 2 - 1 := by
    exact infinitesimalAdditiveTranslationAlgEquiv_symm_coordinate (ZMod 2) 2 1
  constructor
  · intro hzero
    apply ht
    apply e.injective
    rw [he, hzero, map_zero]
  · rw [← he, ← map_pow, ht_square, map_zero]

end AlgebraicGeometry

namespace AlgebraicGeometry

/-- Second roots of unity over `𝔽₂` are finitely presented, finite and flat, with
rank two at the zero prime of the base. -/
private theorem rootsOfUnity_zmod_two_finite_properties :
    Algebra.FinitePresentation (ZMod 2) (rootsOfUnityCoordinateRing (ZMod 2) 2) ∧
      IsFinite (rootsOfUnityScheme (ZMod 2) 2).hom ∧
      Flat (rootsOfUnityScheme (ZMod 2) 2).hom ∧
      LocallyOfFinitePresentation (rootsOfUnityScheme (ZMod 2) 2).hom ∧
      (rootsOfUnityScheme (ZMod 2) 2).hom.finrank
        (⟨⊥, Ideal.isPrime_bot⟩ : Spec (.of (ZMod 2))) = 2 :=
  ⟨rootsOfUnityCoordinateRing_finitePresentation (ZMod 2) 2,
    rootsOfUnityScheme_isFinite (ZMod 2) 2,
    rootsOfUnityScheme_flat (ZMod 2) 2,
    rootsOfUnityScheme_locallyOfFinitePresentation (ZMod 2) 2,
    rootsOfUnityScheme_finrank (ZMod 2) 2 ⟨⊥, Ideal.isPrime_bot⟩⟩

end AlgebraicGeometry
