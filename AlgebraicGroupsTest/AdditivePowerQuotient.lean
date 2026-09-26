/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.AdditivePowerQuotient
public import AlgebraicGroups.GroupScheme.InfinitesimalAdditive
public import Mathlib.Data.ZMod.Basic

public section

set_option warningAsError true

noncomputable section

open scoped TensorProduct

universe u

namespace AlgebraicGeometry

theorem additivePower_generic_presentation_test (K : Type u) [CommRing K] (N : ℕ) :
    Nonempty (additivePowerCoordinateRing K N ≃ₐ[K]
      AdjoinRoot ((Polynomial.X : Polynomial K) ^ N)) :=
  ⟨additivePowerCoordinateAlgEquiv K N⟩

theorem additivePower_generic_mk_test (K : Type u) [CommRing K] (N : ℕ)
    (a : additiveGroupCoordinateRing K) :
    additivePowerCoordinateAlgEquiv K N (Ideal.Quotient.mk (additivePowerIdeal K N) a) =
      AdjoinRoot.mk ((Polynomial.X : Polynomial K) ^ N)
        (additiveGroupCoordinateAlgEquiv K a) :=
  additivePowerCoordinateAlgEquiv_mk K N a

theorem additivePower_generic_symm_mk_test (K : Type u) [CommRing K] (N : ℕ)
    (f : Polynomial K) :
    (additivePowerCoordinateAlgEquiv K N).symm
        (AdjoinRoot.mk ((Polynomial.X : Polynomial K) ^ N) f) =
      Ideal.Quotient.mk (additivePowerIdeal K N)
        ((additiveGroupCoordinateAlgEquiv K).symm f) :=
  additivePowerCoordinateAlgEquiv_symm_mk K N f

theorem additivePower_generic_nonzero_test (K : Type u) [CommRing K] [Nontrivial K]
    (N : ℕ) (hN : 1 < N) : additivePowerCoordinate K N ≠ 0 :=
  additivePowerCoordinate_ne_zero K N hN

theorem additivePower_zero_exponent_test (K : Type u) [CommRing K] :
    additivePowerCoordinate K 0 = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  simp [additivePowerIdeal, Ideal.span_singleton_one]

theorem additivePower_zero_exponent_one_eq_zero_test (K : Type u) [CommRing K] :
    (1 : additivePowerCoordinateRing K 0) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  simp [additivePowerIdeal, Ideal.span_singleton_one]

theorem additivePower_first_exponent_test (K : Type u) [CommRing K] :
    additivePowerCoordinate K 1 = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  change additiveGroupCoordinate K ∈ Ideal.span {(additiveGroupCoordinate K) ^ 1}
  simpa only [pow_one] using
    (Ideal.mem_span_singleton_self (additiveGroupCoordinate K))

theorem additivePower_subsingleton_base_test (K : Type u) [CommRing K]
    [Subsingleton K] (N : ℕ) : additivePowerCoordinate K N = 0 := by
  have hzero : (0 : additivePowerCoordinateRing K N) = 1 := by
    calc
      (0 : additivePowerCoordinateRing K N) = algebraMap K _ 0 := (map_zero _).symm
      _ = algebraMap K _ 1 := congrArg (algebraMap K _) (Subsingleton.elim _ _)
      _ = 1 := map_one _
  exact eq_zero_of_zero_eq_one hzero _

theorem additivePower_zero_base_test (N : ℕ) :
    additivePowerCoordinate PUnit N = 0 :=
  additivePower_subsingleton_base_test PUnit N

theorem additivePower_zmod_one_zero_base_test (N : ℕ) :
    additivePowerCoordinate (ZMod 1) N = 0 :=
  additivePower_subsingleton_base_test (ZMod 1) N

theorem additivePower_zmod_four_nondomain_test :
    additivePowerCoordinate (ZMod 4) 2 ≠ 0 :=
  @additivePowerCoordinate_ne_zero (ZMod 4) _
    (ZMod.nontrivial_iff.mpr (by decide)) 2 (by decide)

theorem additivePower_zmod_four_presentation_test :
    Nonempty (additivePowerCoordinateRing (ZMod 4) 2 ≃ₐ[ZMod 4]
      AdjoinRoot ((Polynomial.X : Polynomial (ZMod 4)) ^ 2)) :=
  ⟨additivePowerCoordinateAlgEquiv (ZMod 4) 2⟩

theorem additivePower_punit_presentation_test (N : ℕ) :
    Nonempty (additivePowerCoordinateRing PUnit N ≃ₐ[PUnit]
      AdjoinRoot ((Polynomial.X : Polynomial PUnit) ^ N)) :=
  ⟨additivePowerCoordinateAlgEquiv PUnit N⟩

theorem additivePower_zero_presentation_test (K : Type u) [CommRing K] :
    Nonempty (additivePowerCoordinateRing K 0 ≃ₐ[K]
      AdjoinRoot ((Polynomial.X : Polynomial K) ^ 0)) :=
  ⟨additivePowerCoordinateAlgEquiv K 0⟩

theorem additivePower_one_presentation_test (K : Type u) [CommRing K] :
    Nonempty (additivePowerCoordinateRing K 1 ≃ₐ[K]
      AdjoinRoot ((Polynomial.X : Polynomial K) ^ 1)) :=
  ⟨additivePowerCoordinateAlgEquiv K 1⟩

/-- A public-API client: in positive prime-characteristic power quotients the
distinguished coordinate is both nonzero and fully primitive. -/
theorem infinitesimalAdditiveCoordinate_nonzero_primitive_test (K : Type u) [CommRing K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (m : ℕ) (hm : 0 < m) :
    infinitesimalAdditiveCoordinate K p m ≠ 0 ∧
      Bialgebra.IsPrimitiveElem K (infinitesimalAdditiveCoordinate K p m) := by
  have hK : Nontrivial K :=
    CharP.nontrivial_of_char_ne_one (R := K) (Fact.out : p.Prime).ne_one
  have hN : 1 < p ^ m := one_lt_pow₀ (Fact.out : p.Prime).one_lt (Nat.ne_of_gt hm)
  constructor
  · exact @additivePowerCoordinate_ne_zero K _ hK (p ^ m) hN
  · constructor
    · exact infinitesimalAdditiveCoordinate_counit K p m
    · simpa only [add_comm] using infinitesimalAdditiveCoordinate_comul K p m

theorem infinitesimalAdditive_zero_exponent_test (K : Type u) [CommRing K]
    (p : ℕ) :
    infinitesimalAdditiveCoordinate K p 0 = 0 := by
  simpa only [pow_zero, pow_one] using infinitesimalAdditiveCoordinate_pow K p 0

theorem infinitesimalAdditive_zmod_two_nonzero_primitive_test :
    infinitesimalAdditiveCoordinate (ZMod 2) 2 1 ≠ 0 ∧
      Bialgebra.IsPrimitiveElem (ZMod 2)
        (infinitesimalAdditiveCoordinate (ZMod 2) 2 1) :=
  infinitesimalAdditiveCoordinate_nonzero_primitive_test (ZMod 2) 2 1 (by decide)

theorem infinitesimalAdditive_polynomial_nonzero_primitive_test :
    infinitesimalAdditiveCoordinate (Polynomial (ZMod 2)) 2 1 ≠ 0 ∧
      Bialgebra.IsPrimitiveElem (Polynomial (ZMod 2))
        (infinitesimalAdditiveCoordinate (Polynomial (ZMod 2)) 2 1) :=
  infinitesimalAdditiveCoordinate_nonzero_primitive_test (Polynomial (ZMod 2)) 2 1
    (by decide)

theorem infinitesimalAdditive_zero_target_point_test
    (r : infinitesimalAdditiveSubgroup (ZMod 2) 2 1 PUnit) :
    (infinitesimalAdditiveMulEquivAlgHom (ZMod 2) 2 1 PUnit (.ofAdd r)).ofConv
      (infinitesimalAdditiveCoordinate (ZMod 2) 2 1) = 0 := by
  rw [infinitesimalAdditiveMulEquivAlgHom_coordinate]

end AlgebraicGeometry
