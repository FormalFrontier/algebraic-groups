/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.RingTheory.Unramified.Field

/-!
# Reducedness of smooth algebras over domains

This file proves that étale, standard smooth, and smooth algebras over an integral domain are
reduced.

## Main results

- `Algebra.Etale.isReduced_of_isDomain`
- `Algebra.IsStandardSmooth.isReduced_of_isDomain`
- `Algebra.Smooth.isReduced_of_isDomain`
-/

public section

open scoped TensorProduct

namespace Algebra

universe u v

/-- An étale algebra over an integral domain is reduced. -/
theorem Etale.isReduced_of_isDomain
    (R : Type u) (S : Type v) [CommRing R] [IsDomain R]
    [CommRing S] [Algebra R S] [Etale R S] : IsReduced S := by
  let K := FractionRing R
  have : Etale K (K ⊗[R] S) := inferInstance
  have : IsReduced (K ⊗[R] S) :=
    FormallyUnramified.isReduced_of_field K (K ⊗[R] S)
  exact isReduced_of_injective
    (TensorProduct.includeRight : S →ₐ[R] K ⊗[R] S)
    (TensorProduct.includeRight_injective (IsFractionRing.injective R K))

/-- A standard smooth algebra over an integral domain is reduced. -/
theorem IsStandardSmooth.isReduced_of_isDomain
    (R : Type u) (S : Type v) [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]
    [IsStandardSmooth R S] : IsReduced S := by
  have hs : (algebraMap R S).IsStandardSmooth :=
    (RingHom.isStandardSmooth_algebraMap (R := R) (S := S)).mpr inferInstance
  obtain ⟨n, g, -, hg⟩ := hs.exists_etale_mvPolynomial
  let : Algebra (MvPolynomial (Fin n) R) S := g.toAlgebra
  have : Etale (MvPolynomial (Fin n) R) S := hg.toAlgebra
  exact Etale.isReduced_of_isDomain (MvPolynomial (Fin n) R) S

/-- A smooth algebra over an integral domain is reduced. -/
theorem Smooth.isReduced_of_isDomain
    (R : Type u) (S : Type v) [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]
    [Smooth R S] : IsReduced S := by
  obtain ⟨s, hs, hstd⟩ := Smooth.exists_span_eq_top_isStandardSmooth R S
  apply isReduced_ofLocalizationMaximal S
  intro p hp
  have hnsub : ¬s ⊆ p := by
    intro h
    have htop : (⊤ : Ideal S) ≤ p := by
      rw [← hs]
      exact Ideal.span_le.mpr h
    exact hp.ne_top (top_unique htop)
  obtain ⟨f, hfs, hfp⟩ := Set.not_subset.mp hnsub
  let Sf := Localization.Away f
  have : IsStandardSmooth R Sf := hstd f hfs
  have : IsReduced Sf := IsStandardSmooth.isReduced_of_isDomain R Sf
  have hle : Submonoid.powers f ≤ p.primeCompl := by
    rintro _ ⟨n, rfl⟩
    exact p.primeCompl.pow_mem hfp n
  let : Algebra Sf (Localization.AtPrime p) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe Sf (Localization.AtPrime p)
      (Submonoid.powers f) p.primeCompl hle
  have : IsScalarTower S Sf (Localization.AtPrime p) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le Sf (Localization.AtPrime p)
      (Submonoid.powers f) p.primeCompl hle
  have : IsLocalization (p.primeCompl.map (algebraMap S Sf))
      (Localization.AtPrime p) :=
    IsLocalization.isLocalization_of_submonoid_le Sf (Localization.AtPrime p)
      (Submonoid.powers f) p.primeCompl hle
  exact isReduced_localizationPreserves
    (p.primeCompl.map (algebraMap S Sf)) (Localization.AtPrime p) inferInstance

end Algebra
