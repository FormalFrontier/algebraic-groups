/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.QuasiFinite.Basic

/-!
# Semilocal rings from finite orbits

This file gives a criterion for a ring to have finitely many maximal ideals.
If one map to a second ring is finite and every pair of maximal ideals occurs
as the contractions, along two fixed maps, of one prime ideal upstairs, then
the maximal spectrum is finite.  An integral map from a local ring makes the
contractions of any two maximal ideals equal, so it suffices to have this orbit
condition only over common contractions.

As an application, a finite flat algebra of constant fibre rank satisfying the
integral local orbit criterion is free of that rank.  The finite-orbit theorem
also handles an empty maximal spectrum. The local corollaries use exactly
mathlib's `IsLocalRing` assumption (which visibly includes `Nontrivial`) and
require no domain or Noetherian hypothesis.
-/

public section

universe uR uA uB

open scoped TensorProduct

/-- For an integral algebra over a local ring, the extension of the maximal
ideal is contained in the Jacobson radical. -/
lemma Ideal.map_maximalIdeal_le_jacobson_of_isIntegral
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] [IsLocalRing R]
    [Algebra R A] [Algebra.IsIntegral R A] :
    Ideal.map (algebraMap R A) (IsLocalRing.maximalIdeal R) ≤
      Ideal.jacobson (⊥ : Ideal A) := by
  rw [Ideal.jacobson]
  refine le_sInf fun P hP ↦ ?_
  obtain ⟨_, hPmax⟩ := hP
  rw [Ideal.map_le_iff_le_comap]
  have hcomap : (P.comap (algebraMap R A)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
      (algebraMap R A) (algebraMap_isIntegral_iff.mpr inferInstance) P
  exact (IsLocalRing.eq_maximalIdeal hcomap).ge

namespace MaximalSpectrum

/-- Suppose one of two maps `A →+* B` is finite. If every pair of maximal
ideals of `A` is obtained by contracting one prime ideal of `B` along the two
maps, then `A` has only finitely many maximal ideals. -/
lemma finite_of_finite_orbit
    {A : Type uA} {B : Type uB} [CommRing A] [CommRing B]
    (s t : A →+* B) (hs : s.Finite)
    (horbit : ∀ P Q : MaximalSpectrum A,
      ∃ W : PrimeSpectrum B,
        PrimeSpectrum.comap s W = P.toPrimeSpectrum ∧
        PrimeSpectrum.comap t W = Q.toPrimeSpectrum) :
    Finite (MaximalSpectrum A) := by
  classical
  let _ : Algebra A B := s.toAlgebra
  let _ : Module.Finite A B := hs
  have hs_alg : algebraMap A B = s := rfl
  cases isEmpty_or_nonempty (MaximalSpectrum A) with
  | inl h => exact Finite.of_subsingleton
  | inr h =>
      let P₀ : MaximalSpectrum A := Classical.arbitrary (MaximalSpectrum A)
      let F : Set (PrimeSpectrum B) :=
        PrimeSpectrum.comap s ⁻¹' {P₀.toPrimeSpectrum}
      have hF : F.Finite := by
        dsimp only [F]
        rw [← hs_alg]
        exact Algebra.QuasiFinite.finite_comap_preimage_singleton P₀.toPrimeSpectrum
      let T : Set (PrimeSpectrum A) := PrimeSpectrum.comap t '' F
      have hT : T.Finite := hF.image (PrimeSpectrum.comap t)
      have hmax : Set.range MaximalSpectrum.toPrimeSpectrum ⊆ T := by
        rintro Q ⟨Q', rfl⟩
        obtain ⟨W, hWs, hWt⟩ := horbit P₀ Q'
        exact ⟨W, hWs, hWt⟩
      have hrange : (Set.range MaximalSpectrum.toPrimeSpectrum).Finite :=
        hT.subset hmax
      let _ := hrange.to_subtype
      exact Finite.of_injective_finite_range MaximalSpectrum.toPrimeSpectrum_injective

/-- Let `R` be local and let `A` be integral over `R`. Suppose one of two maps
`A →+* B` is finite and any two maximal ideals of `A` with the same contraction
to `R` are joined by a prime of `B`. Then `A` has only finitely many maximal
ideals. -/
lemma finite_of_isIntegral_of_isLocalRing
    {R : Type uR} {A : Type uA} {B : Type uB}
    [CommRing R] [CommRing A] [CommRing B] [IsLocalRing R]
    (i : R →+* A) (hi : i.IsIntegral)
    (s t : A →+* B) (hs : s.Finite)
    (horbit : ∀ P Q : MaximalSpectrum A,
      P.asIdeal.comap i = Q.asIdeal.comap i →
        ∃ W : PrimeSpectrum B,
          PrimeSpectrum.comap s W = P.toPrimeSpectrum ∧
          PrimeSpectrum.comap t W = Q.toPrimeSpectrum) :
    Finite (MaximalSpectrum A) := by
  apply finite_of_finite_orbit s t hs
  intro P Q
  apply horbit P Q
  have hP : (P.asIdeal.comap i).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal i hi P.asIdeal
  have hQ : (Q.asIdeal.comap i).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal i hi Q.asIdeal
  exact (IsLocalRing.eq_maximalIdeal hP).trans
    (IsLocalRing.eq_maximalIdeal hQ).symm

end MaximalSpectrum

/-- A finite flat algebra of constant fibre rank is free of that rank when its
base is integral over a local ring and the two supplied maps satisfy the common
contraction orbit criterion. -/
lemma Module.nonempty_basis_of_finrank_eq_of_integral_local_orbit
    {R : Type uR} {A : Type uA} {B : Type uB}
    [CommRing R] [CommRing A] [CommRing B] [IsLocalRing R]
    [Algebra A B] [Module.Finite A B] [Module.Flat A B]
    (i : R →+* A) (hi : i.IsIntegral)
    (s t : A →+* B) (hs : algebraMap A B = s)
    (horbit : ∀ P Q : MaximalSpectrum A,
      P.asIdeal.comap i = Q.asIdeal.comap i →
        ∃ W : PrimeSpectrum B,
          PrimeSpectrum.comap s W = P.toPrimeSpectrum ∧
          PrimeSpectrum.comap t W = Q.toPrimeSpectrum)
    (n : ℕ)
    (hrank : ∀ P : MaximalSpectrum A,
        Module.finrank (A ⧸ P.asIdeal)
          ((A ⧸ P.asIdeal) ⊗[A] B) = n) :
    Nonempty (Module.Basis (Fin n) A B) := by
  have hfinite : s.Finite := by
    rw [← hs, RingHom.finite_algebraMap]
    infer_instance
  let _ : Finite (MaximalSpectrum A) :=
    MaximalSpectrum.finite_of_isIntegral_of_isLocalRing i hi s t hfinite horbit
  exact Module.nonempty_basis_of_flat_of_finrank_eq A B n hrank
