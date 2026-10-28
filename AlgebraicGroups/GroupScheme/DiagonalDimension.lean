/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Scheme
public import TauCeti.Algebra.MonoidAlgebra.Localization
public import TauCeti.RingTheory.KrullDimension.FiniteType

/-!
# Polynomial localization and dimension of the split torus

The canonical character group algebra is the polynomial algebra with all
variables inverted. Inverting the monomial with every exponent one suffices.
This presentation works over every commutative ring, including the zero ring
and an empty index type. Over a field its Krull dimension is the number of
indices; the affine spectrum has the same topological dimension.

## References

* J. S. Milne, *Algebraic Groups* (2017), item 2.9 (diagonal matrices over a field).
* Tau Ceti contributors, monoid-algebra localization and polynomial Krull dimension.
* Mathlib contributors, finitely supported functions and localization equivalences.
-/

public section

noncomputable section

universe u

namespace TauCeti.SplitTorus

section CommRing

variable (K : Type u) [CommRing K] (ι : Type u) [Finite ι]

/-- The monomial obtained by multiplying each polynomial variable once. -/
def polynomialDenominator : MvPolynomial ι K :=
  MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm (fun _ : ι => 1)) 1

private def exponentCast : Multiplicative (ι →₀ ℕ) →* Multiplicative (ι →₀ ℤ) :=
  (Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℤ)).toMultiplicative

omit [Finite ι] in
private theorem exponentCast_injective : Function.Injective (exponentCast ι) := by
  intro x y h
  apply Multiplicative.toAdd.injective
  apply Finsupp.mapRange_injective (fun n : ℕ => (n : ℤ)) (by simp) Nat.cast_injective
  exact congrArg Multiplicative.toAdd h

private theorem exponentCast_clears_denominators (y : Multiplicative (ι →₀ ℤ)) :
    ∃ n : ℕ, y * exponentCast ι
        (.ofAdd (Finsupp.equivFunOnFinite.symm (fun _ : ι => 1))) ^ n ∈
      Set.range (exponentCast ι) := by
  classical
  let := Fintype.ofFinite ι
  let n := Finset.univ.sup (fun i : ι => (-(Multiplicative.toAdd y i)).toNat)
  have hnonneg (i : ι) : 0 ≤ Multiplicative.toAdd y i + (n : ℤ) := by
    have hbound : (-(Multiplicative.toAdd y i)).toNat ≤ n :=
      Finset.le_sup (f := fun j : ι => (-(Multiplicative.toAdd y j)).toNat)
        (Finset.mem_univ i)
    omega
  refine ⟨n, .ofAdd (Finsupp.equivFunOnFinite.symm
    (fun i : ι => (Multiplicative.toAdd y i + (n : ℤ)).toNat)), ?_⟩
  apply Multiplicative.toAdd.injective
  ext i
  simp [exponentCast, Int.toNat_of_nonneg (hnonneg i)]

private theorem monoidAlgebra_localization :
    letI := (MonoidAlgebra.mapDomainRingHom K (exponentCast ι)).toAlgebra
    IsLocalization.Away
      (MonoidAlgebra.single
        (Multiplicative.ofAdd (Finsupp.equivFunOnFinite.symm (fun _ : ι => 1))) (1 : K))
      (MonoidAlgebra K (Multiplicative (ι →₀ ℤ))) := by
  apply TauCeti.MonoidAlgebra.isLocalization_away_mapDomainRingHom
    K (exponentCast ι) (exponentCast_injective ι)
  · exact IsUnit.of_mul_eq_one _ (mul_inv_cancel _)
  · exact exponentCast_clears_denominators ι

/-- The canonical split-torus coordinate ring is a polynomial localization. -/
def polynomialLocalizationEquiv :
    MonoidAlgebra K (Multiplicative (ι →₀ ℤ)) ≃ₐ[K]
      Localization.Away (polynomialDenominator K ι) := by
  let e : MvPolynomial ι K ≃ₐ[K] MonoidAlgebra K (Multiplicative (ι →₀ ℕ)) :=
    AddMonoidAlgebra.toMultiplicativeAlgEquiv K K (ι →₀ ℕ)
  let f := MonoidAlgebra.mapDomainAlgHom K K (exponentCast ι)
  letI := (MonoidAlgebra.mapDomainRingHom K (exponentCast ι)).toAlgebra
  letI : IsScalarTower K (MonoidAlgebra K (Multiplicative (ι →₀ ℕ)))
      (MonoidAlgebra K (Multiplicative (ι →₀ ℤ))) :=
    IsScalarTower.of_algebraMap_eq (fun r => (f.commutes r).symm)
  haveI : IsLocalization.Away
      (MonoidAlgebra.single
        (Multiplicative.ofAdd (Finsupp.equivFunOnFinite.symm (fun _ : ι => 1))) (1 : K))
      (MonoidAlgebra K (Multiplicative (ι →₀ ℤ))) := monoidAlgebra_localization K ι
  have hp : e (polynomialDenominator K ι) = MonoidAlgebra.single
      (Multiplicative.ofAdd (Finsupp.equivFunOnFinite.symm (fun _ : ι => 1))) (1 : K) := by
    exact AddMonoidAlgebra.toMultiplicativeAlgEquiv_single
      (R := K) (A := K) (M := ι →₀ ℕ) _ _
  refine IsLocalization.algEquivOfAlgEquiv
    (M := Submonoid.powers (MonoidAlgebra.single
      (Multiplicative.ofAdd (Finsupp.equivFunOnFinite.symm (fun _ : ι => 1))) (1 : K)))
    (T := Submonoid.powers (polynomialDenominator K ι))
    (MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))
    (Localization.Away (polynomialDenominator K ι)) e.symm ?_
  rw [Submonoid.map_powers]
  congr 1
  exact e.symm_apply_eq.mpr hp.symm

/-- Every standard polynomial variable evaluates to the corresponding torus character. -/
theorem polynomialLocalizationEquiv_symm_variable (i : ι) :
    (polynomialLocalizationEquiv K ι).symm
      (algebraMap (MvPolynomial ι K) (Localization.Away (polynomialDenominator K ι))
        (MvPolynomial.X i)) =
      MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single i (1 : ℤ))) (1 : K) := by
  classical
  let f := MonoidAlgebra.mapDomainAlgHom K K (exponentCast ι)
  let := (MonoidAlgebra.mapDomainRingHom K (exponentCast ι)).toAlgebra
  let : IsScalarTower K (MonoidAlgebra K (Multiplicative (ι →₀ ℕ)))
      (MonoidAlgebra K (Multiplicative (ι →₀ ℤ))) :=
    IsScalarTower.of_algebraMap_eq (fun r => (f.commutes r).symm)
  have : IsLocalization.Away
      (MonoidAlgebra.single
        (Multiplicative.ofAdd (Finsupp.equivFunOnFinite.symm (fun _ : ι => 1))) (1 : K))
      (MonoidAlgebra K (Multiplicative (ι →₀ ℤ))) := monoidAlgebra_localization K ι
  unfold polynomialLocalizationEquiv
  erw [IsLocalization.algEquivOfAlgEquiv_symm, IsLocalization.algEquivOfAlgEquiv_eq]
  simp only [RingHom.algebraMap_toAlgebra, MonoidAlgebra.mapDomainRingHom_apply,
    MvPolynomial.X]
  rw [show MvPolynomial.monomial (Finsupp.single i 1) (1 : K) =
    AddMonoidAlgebra.single (Finsupp.single i 1) (1 : K) from rfl,
    AlgEquiv.symm_symm, AddMonoidAlgebra.toMultiplicativeAlgEquiv_single,
    MonoidAlgebra.mapDomain_single]
  congr 1
  simp [exponentCast]

/-- The localization presentation sends each basic torus character to its polynomial variable. -/
theorem polynomialLocalizationEquiv_variable (i : ι) :
    polynomialLocalizationEquiv K ι
      (MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single i (1 : ℤ))) (1 : K)) =
      algebraMap (MvPolynomial ι K) (Localization.Away (polynomialDenominator K ι))
        (MvPolynomial.X i) := by
  rw [← polynomialLocalizationEquiv_symm_variable K ι i, AlgEquiv.apply_symm_apply]

end CommRing

variable (K : Type u) [Field K] (ι : Type u) [Finite ι]

/-- Inverting the all-variable monomial does not lower polynomial dimension over a field. -/
theorem ringKrullDim_coordinateRing :
    ringKrullDim (MonoidAlgebra K (Multiplicative (ι →₀ ℤ))) =
      (Nat.card ι : WithBot ℕ∞) := by
  rw [ringKrullDim_eq_of_ringEquiv (polynomialLocalizationEquiv K ι).toRingEquiv]
  have hp : polynomialDenominator K ι ≠ 0 := by
    simp [polynomialDenominator]
  rw [TauCeti.ringKrullDim_localization_away K hp,
    MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
    ringKrullDim_eq_zero_of_field, zero_add]

/-- The canonical split torus has its rank as topological Krull dimension. -/
theorem topologicalKrullDim_groupScheme :
    topologicalKrullDim (groupScheme K ι).X.left = (Nat.card ι : WithBot ℕ∞) := by
  change topologicalKrullDim (PrimeSpectrum (MonoidAlgebra K (Multiplicative (ι →₀ ℤ)))) = _
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ringKrullDim_coordinateRing]

end TauCeti.SplitTorus
