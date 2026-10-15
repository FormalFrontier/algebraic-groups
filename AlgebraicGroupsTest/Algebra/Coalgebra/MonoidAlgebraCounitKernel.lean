/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra

/-!
# Basis differences in canonical counit kernels

The canonical counit on a monoid algebra has kernel spanned by differences of
standard basis vectors from the identity vector. The split-kernel and
basis-image theorems also give the anchored total-coefficient kernel for
finitely supported functions over an arbitrary, possibly noncommutative ring.

The examples below use the infinite group `Multiplicative ℤ`. Integer
coefficients exhibit a nonzero basis difference, while coefficients in `ZMod 6`
exhibit a nonzero torsion element. All supports are finite without imposing
finiteness on the group. These proofs use Mathlib's split linear map and
basis-image range formulas.
-/

noncomputable section

namespace MonoidAlgebraCounitKernel

universe u v

private lemma monoidAlgebra_counit_ker {R : Type u} [CommRing R]
    {M : Type v} [Monoid M] :
    LinearMap.ker (Coalgebra.counit (R := R) (A := MonoidAlgebra R M)) =
      Submodule.span R (Set.range (fun m : M =>
        MonoidAlgebra.of R M m - MonoidAlgebra.of R M 1)) := by
  let ε := Coalgebra.counit (R := R) (A := MonoidAlgebra R M)
  let σ := Algebra.linearMap R (MonoidAlgebra R M)
  have hsplit : ε ∘ₗ σ = LinearMap.id := by
    apply LinearMap.ext
    intro r
    exact Bialgebra.counit_algebraMap (R := R) (A := MonoidAlgebra R M) r
  let q := LinearMap.id - σ ∘ₗ ε
  have hq (m : M) : q (MonoidAlgebra.basis M R m) =
      MonoidAlgebra.of R M m - MonoidAlgebra.of R M 1 := by
    simp [q, ε, σ, MonoidAlgebra.of_apply]
  calc
    LinearMap.ker ε = LinearMap.range q :=
      LinearMap.ker_eq_range_of_comp_eq_id hsplit
    _ = LinearMap.range ((MonoidAlgebra.basis M R).constr R
        (fun m => q (MonoidAlgebra.basis M R m))) := by
      rw [Module.Basis.constr_self]
    _ = Submodule.span R
        (Set.range (fun m => q (MonoidAlgebra.basis M R m))) :=
      (MonoidAlgebra.basis M R).constr_range R
    _ = Submodule.span R (Set.range (fun m : M =>
        MonoidAlgebra.of R M m - MonoidAlgebra.of R M 1)) := by
      simp only [hq]

private lemma finsupp_linearCombination_ker {R : Type u} [Ring R]
    {X : Type v} (a : X) :
    LinearMap.ker (Finsupp.linearCombination R (fun _ : X => (1 : R))) =
      Submodule.span R (Set.range (fun x : X =>
        Finsupp.single x (1 : R) - Finsupp.single a (1 : R))) := by
  let ε := Finsupp.linearCombination R (fun _ : X => (1 : R))
  let σ : R →ₗ[R] X →₀ R := Finsupp.lsingle a
  have hsplit : ε ∘ₗ σ = LinearMap.id := by
    apply LinearMap.ext
    intro r
    simp [ε, σ]
  let q := LinearMap.id - σ ∘ₗ ε
  let b : Module.Basis X R (X →₀ R) := Finsupp.basisSingleOne
  have hq (x : X) : q (b x) =
      Finsupp.single x (1 : R) - Finsupp.single a (1 : R) := by
    simp [q, b, ε, σ, Finsupp.coe_basisSingleOne]
  calc
    LinearMap.ker ε = LinearMap.range q :=
      LinearMap.ker_eq_range_of_comp_eq_id hsplit
    _ = LinearMap.range (b.constr ℕ (fun x => q (b x))) := by
      rw [Module.Basis.constr_self]
    _ = Submodule.span R (Set.range (fun x => q (b x))) :=
      b.constr_range ℕ
    _ = Submodule.span R (Set.range (fun x : X =>
        Finsupp.single x (1 : R) - Finsupp.single a (1 : R))) := by
      simp only [hq]


private abbrev BoundaryGroup := Multiplicative ℤ

private def boundaryPoint : BoundaryGroup := Multiplicative.ofAdd (1 : ℤ)

private theorem boundaryPoint_ne_one : boundaryPoint ≠ (1 : BoundaryGroup) := by
  change (1 : ℤ) ≠ 0
  decide

private theorem boundaryGroup_infinite : Infinite BoundaryGroup := inferInstance

private theorem boundaryGroup_no_fintype : ¬ Nonempty (Fintype BoundaryGroup) := by
  intro h
  rcases h with ⟨h⟩
  let : Fintype BoundaryGroup := h
  exact not_finite BoundaryGroup

private def integerBoundaryVector : MonoidAlgebra ℤ BoundaryGroup :=
  MonoidAlgebra.of ℤ BoundaryGroup boundaryPoint -
    MonoidAlgebra.of ℤ BoundaryGroup (1 : BoundaryGroup)

/-- A nonzero augmentation-kernel vector with exactly two coefficients
in a group algebra whose index group is infinite. -/
private theorem integer_boundary_data :
    Infinite BoundaryGroup ∧
    (¬ Nonempty (Fintype BoundaryGroup)) ∧
    boundaryPoint ≠ (1 : BoundaryGroup) ∧
    Coalgebra.counit (R := ℤ) integerBoundaryVector = 0 ∧
    integerBoundaryVector ∈ LinearMap.ker
      (Coalgebra.counit (R := ℤ) (A := MonoidAlgebra ℤ BoundaryGroup)) ∧
    integerBoundaryVector ∈ Submodule.span ℤ
      (Set.range (fun g : BoundaryGroup =>
        MonoidAlgebra.of ℤ BoundaryGroup g -
          MonoidAlgebra.of ℤ BoundaryGroup (1 : BoundaryGroup))) ∧
    integerBoundaryVector.coeff boundaryPoint = 1 ∧
    integerBoundaryVector.coeff (1 : BoundaryGroup) = -1 ∧
    (∀ g : BoundaryGroup, g ≠ boundaryPoint → g ≠ 1 →
      integerBoundaryVector.coeff g = 0) ∧
    integerBoundaryVector.coeff.support = {boundaryPoint, 1} ∧
    integerBoundaryVector ≠ 0 := by
  have h1 : (1 : ℤ) ≠ 0 := by decide
  classical
  have ht := boundaryPoint_ne_one
  have heps : Coalgebra.counit (R := ℤ) integerBoundaryVector = 0 := by
    simp only [integerBoundaryVector, MonoidAlgebra.of_apply, map_sub,
      MonoidAlgebra.counit_single, CommSemiring.counit_apply, sub_self]
  have hker : integerBoundaryVector ∈ LinearMap.ker
      (Coalgebra.counit (R := ℤ) (A := MonoidAlgebra ℤ BoundaryGroup)) :=
    LinearMap.mem_ker.mpr heps
  have hspan : integerBoundaryVector ∈ Submodule.span ℤ
      (Set.range (fun g : BoundaryGroup =>
        MonoidAlgebra.of ℤ BoundaryGroup g -
          MonoidAlgebra.of ℤ BoundaryGroup (1 : BoundaryGroup))) := by
    rw [← monoidAlgebra_counit_ker (R := ℤ) (M := Multiplicative ℤ)]
    exact hker
  have hcoeff (g : BoundaryGroup) :
      integerBoundaryVector.coeff g =
        (if boundaryPoint = g then (1 : ℤ) else 0) -
          (if (1 : BoundaryGroup) = g then (1 : ℤ) else 0) := by
    simp only [integerBoundaryVector, MonoidAlgebra.of_apply,
      MonoidAlgebra.coeff_sub, MonoidAlgebra.coeff_single,
      Finsupp.sub_apply, Finsupp.single_apply]
  have hct : integerBoundaryVector.coeff boundaryPoint = 1 := by
    simp [hcoeff, Ne.symm ht]
  have hc1 : integerBoundaryVector.coeff (1 : BoundaryGroup) = -1 := by
    simp [hcoeff, ht]
  have hother (g : BoundaryGroup) (hgt : g ≠ boundaryPoint) (hg1 : g ≠ 1) :
      integerBoundaryVector.coeff g = 0 := by
    simp [hcoeff, Ne.symm hgt, Ne.symm hg1]
  have hsupport : integerBoundaryVector.coeff.support = {boundaryPoint, 1} := by
    apply Finset.ext
    intro g
    by_cases hgt : g = boundaryPoint
    · subst g
      simp [Finsupp.mem_support_iff, hct]
    · by_cases hg1 : g = (1 : BoundaryGroup)
      · subst g
        simp [Finsupp.mem_support_iff, hc1]
      · simp [Finsupp.mem_support_iff, hother g hgt hg1, hgt, hg1]
  have hne : integerBoundaryVector ≠ 0 := by
    intro hx
    have hc : integerBoundaryVector.coeff boundaryPoint = 0 := by
      rw [hx]
      rfl
    exact h1 (hct.symm.trans hc)
  exact ⟨boundaryGroup_infinite, boundaryGroup_no_fintype, ht, heps, hker,
    hspan, hct, hc1, hother, hsupport, hne⟩

private def zmodSixBoundaryVector : MonoidAlgebra (ZMod 6) BoundaryGroup :=
  (2 : ZMod 6) •
    (MonoidAlgebra.of (ZMod 6) BoundaryGroup boundaryPoint -
      MonoidAlgebra.of (ZMod 6) BoundaryGroup (1 : BoundaryGroup))

/-- A nonzero augmentation-kernel vector over `ZMod 6`, with exact support and
an explicit nonzero scalar annihilator. -/
private theorem zmod_six_boundary_data :
    Infinite BoundaryGroup ∧
    (¬ Nonempty (Fintype BoundaryGroup)) ∧
    boundaryPoint ≠ (1 : BoundaryGroup) ∧
    (1 : ZMod 6) ≠ 0 ∧ (2 : ZMod 6) ≠ 0 ∧
    (3 : ZMod 6) ≠ 0 ∧ (4 : ZMod 6) ≠ 0 ∧
    (3 : ZMod 6) * (2 : ZMod 6) = 0 ∧
    Coalgebra.counit (R := ZMod 6) zmodSixBoundaryVector = 0 ∧
    zmodSixBoundaryVector ∈ LinearMap.ker
      (Coalgebra.counit (R := ZMod 6)
        (A := MonoidAlgebra (ZMod 6) BoundaryGroup)) ∧
    zmodSixBoundaryVector ∈ Submodule.span (ZMod 6)
      (Set.range (fun g : BoundaryGroup =>
        MonoidAlgebra.of (ZMod 6) BoundaryGroup g -
          MonoidAlgebra.of (ZMod 6) BoundaryGroup (1 : BoundaryGroup))) ∧
    zmodSixBoundaryVector.coeff boundaryPoint = (2 : ZMod 6) ∧
    zmodSixBoundaryVector.coeff boundaryPoint ≠ 0 ∧
    zmodSixBoundaryVector.coeff (1 : BoundaryGroup) = (4 : ZMod 6) ∧
    zmodSixBoundaryVector.coeff (1 : BoundaryGroup) ≠ 0 ∧
    (∀ g : BoundaryGroup, g ≠ boundaryPoint → g ≠ 1 →
      zmodSixBoundaryVector.coeff g = 0) ∧
    zmodSixBoundaryVector.coeff.support = {boundaryPoint, 1} ∧
    zmodSixBoundaryVector ≠ 0 ∧
    (3 : ZMod 6) • zmodSixBoundaryVector = 0 := by
  have ht := boundaryPoint_ne_one
  have h1 : (1 : ZMod 6) ≠ 0 := by decide
  have h2 : (2 : ZMod 6) ≠ 0 := by decide
  have h3 : (3 : ZMod 6) ≠ 0 := by decide
  have h4 : (4 : ZMod 6) ≠ 0 := by decide
  have h32 : (3 : ZMod 6) * (2 : ZMod 6) = 0 := by decide
  have hneg2 : -(2 : ZMod 6) = (4 : ZMod 6) := by decide
  classical
  have heps : Coalgebra.counit (R := ZMod 6) zmodSixBoundaryVector = 0 := by
    simp only [zmodSixBoundaryVector, MonoidAlgebra.of_apply, map_smul,
      map_sub, MonoidAlgebra.counit_single, CommSemiring.counit_apply,
      sub_self, smul_zero]
  have hker : zmodSixBoundaryVector ∈ LinearMap.ker
      (Coalgebra.counit (R := ZMod 6)
        (A := MonoidAlgebra (ZMod 6) BoundaryGroup)) :=
    LinearMap.mem_ker.mpr heps
  have hspan : zmodSixBoundaryVector ∈ Submodule.span (ZMod 6)
      (Set.range (fun g : BoundaryGroup =>
        MonoidAlgebra.of (ZMod 6) BoundaryGroup g -
          MonoidAlgebra.of (ZMod 6) BoundaryGroup (1 : BoundaryGroup))) := by
    rw [← monoidAlgebra_counit_ker (R := ZMod 6) (M := Multiplicative ℤ)]
    exact hker
  have hcoeff (g : BoundaryGroup) :
      zmodSixBoundaryVector.coeff g =
        (2 : ZMod 6) *
          ((if boundaryPoint = g then (1 : ZMod 6) else 0) -
            (if (1 : BoundaryGroup) = g then (1 : ZMod 6) else 0)) := by
    simp only [zmodSixBoundaryVector, MonoidAlgebra.of_apply,
      MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_sub,
      MonoidAlgebra.coeff_single, Finsupp.sub_apply, Finsupp.single_apply,
      smul_eq_mul]
  have hct : zmodSixBoundaryVector.coeff boundaryPoint = (2 : ZMod 6) := by
    simp [hcoeff, Ne.symm ht]
  have hc1 : zmodSixBoundaryVector.coeff (1 : BoundaryGroup) = (4 : ZMod 6) := by
    calc
      zmodSixBoundaryVector.coeff (1 : BoundaryGroup) = -(2 : ZMod 6) := by
        simp [hcoeff, ht]
      _ = (4 : ZMod 6) := hneg2
  have hct_ne : zmodSixBoundaryVector.coeff boundaryPoint ≠ 0 := by
    simpa only [hct] using h2
  have hc1_ne : zmodSixBoundaryVector.coeff (1 : BoundaryGroup) ≠ 0 := by
    simpa only [hc1] using h4
  have hother (g : BoundaryGroup) (hgt : g ≠ boundaryPoint) (hg1 : g ≠ 1) :
      zmodSixBoundaryVector.coeff g = 0 := by
    simp [hcoeff, Ne.symm hgt, Ne.symm hg1]
  have hsupport : zmodSixBoundaryVector.coeff.support = {boundaryPoint, 1} := by
    apply Finset.ext
    intro g
    by_cases hgt : g = boundaryPoint
    · subst g
      simp [Finsupp.mem_support_iff, hct, h2]
    · by_cases hg1 : g = (1 : BoundaryGroup)
      · subst g
        simp [Finsupp.mem_support_iff, hc1, h4]
      · simp [Finsupp.mem_support_iff, hother g hgt hg1, hgt, hg1]
  have hne : zmodSixBoundaryVector ≠ 0 := by
    intro hz
    have hc : zmodSixBoundaryVector.coeff boundaryPoint = 0 := by
      rw [hz]
      rfl
    exact h2 (hct.symm.trans hc)
  have hann : (3 : ZMod 6) • zmodSixBoundaryVector = 0 := by
    rw [zmodSixBoundaryVector, smul_smul, h32, zero_smul]
  exact ⟨boundaryGroup_infinite, boundaryGroup_no_fintype, ht, h1, h2, h3,
    h4, h32, heps, hker, hspan, hct, hct_ne, hc1, hc1_ne, hother, hsupport,
    hne, hann⟩

end MonoidAlgebraCounitKernel
