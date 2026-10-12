/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.TensorProduct.Split
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Data.Finsupp.Fintype
public import Mathlib.Data.Finsupp.ToDFinsupp
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.RingTheory.Ideal.Span

/-!
# Split tensor coordinates over semirings and nonfree modules

The free example has infinitely many indices over `ℕ`. The ideal `(3)` in
`ZMod 6` has a concrete split presentation indexed by `Unit`, but is not free:
the nonzero scalar `4` annihilates it. Its tensor coordinate at the generator is
`3`, not `1`, illustrating why these coordinates need not be biorthogonal.
The countable direct sum of this ideal is projective, nonfree and not finitely
generated. Mathlib's `Module.Projective.out` supplies its canonical section.
An empty-index presentation gives a zero right factor. Finally, zero maps over
`ℕ` show why the splitting identity is necessary.

## References

* Mathlib's projective-module split and direct-sum formalizations, Finsupp
  coordinates, and finite-scalar-ring criterion for module finiteness.
* Formal Frontier's earlier coefficient-coalgebra formalizations, for the
  idempotent-ideal and countable-direct-sum examples.
-/

@[expose] public section

open scoped TensorProduct

namespace TensorProduct.SplitExamples

open Classical in
/-- If the section is a basis representation, the split-presentation coordinates
agree with Mathlib's original coordinates on the presented module. -/
theorem basis_coordinates_agree {R C M ι : Type*}
    [CommSemiring R] [AddCommMonoid C] [Module R C]
    [AddCommMonoid M] [Module R M] (b : Module.Basis ι R C) (t : M ⊗[R] C) :
    equivFinsuppOfBasisRight (Finsupp.basisSingleOne : Module.Basis ι R (ι →₀ R))
        (b.repr.toLinearMap.lTensor M t) = equivFinsuppOfBasisRight b t := by
  ext i
  rw [equivFinsuppOfBasisRight_lTensor_apply, equivFinsuppOfBasisRight_apply]
  rfl

open Classical in
/-- The canonical tensor coordinates on the countably generated free `ℕ`-module
send `2 ⊗ single 7 3` to `single 7 6`. -/
theorem natural_tensor_coordinates :
    equivFinsuppOfBasisRight (Finsupp.basisSingleOne :
      Module.Basis ℕ ℕ (ℕ →₀ ℕ)) ((2 : ℕ) ⊗ₜ[ℕ] Finsupp.single 7 3) =
        Finsupp.single 7 6 := by
  ext i
  rw [equivFinsuppOfBasisRight_apply_tmul_apply]
  by_cases hi : i = 7
  · subst i
    simp
  · simp [Ne.symm hi]

open Classical in
/-- The split identity presentation reconstructs a tensor with a nonzero
coefficient on an infinite index type, over a semiring rather than a ring. -/
theorem natural_tensor_reconstruction :
    (∑ i ∈ (Finsupp.single 7 6 : ℕ →₀ ℕ).support,
      (Finsupp.single 7 6 : ℕ →₀ ℕ) i ⊗ₜ[ℕ] (Finsupp.single i 1 : ℕ →₀ ℕ)) =
        (2 : ℕ) ⊗ₜ[ℕ] Finsupp.single 7 3 := by
  obtain ⟨a, ha, hcoord⟩ := exists_tensor_coefficients_of_split
    (LinearMap.id : (ℕ →₀ ℕ) →ₗ[ℕ] (ℕ →₀ ℕ)) LinearMap.id (by simp)
    ((2 : ℕ) ⊗ₜ[ℕ] Finsupp.single 7 3)
  have haeq : a = Finsupp.single 7 6 := by
    apply Finsupp.ext
    intro i
    rw [hcoord]
    by_cases hi : i = 7
    · subst i
      simp
    · simp [Ne.symm hi]
  rw [haeq] at ha
  simpa only [LinearMap.id_apply] using ha

open Classical in
/-- The empty-index identity presentation is a valid split presentation of the
zero module; its tensor support reconstructs every tensor as zero. -/
theorem empty_index_tensor_eq_zero (t : ℕ ⊗[ℕ] (Empty →₀ ℕ)) : t = 0 := by
  have h := sum_tmul_eq_of_split
    (LinearMap.id : (Empty →₀ ℕ) →ₗ[ℕ] (Empty →₀ ℕ)) LinearMap.id (by simp) t
  simpa only [Finset.eq_empty_of_isEmpty, Finset.sum_empty] using h.symm

private abbrev K := ZMod 6
private abbrev D := Ideal.span ({(3 : K)} : Set K)

private theorem three_idempotent : (3 : K) * 3 = 3 := by decide
private theorem three_ne_zero : (3 : K) ≠ 0 := by decide
private theorem four_ne_zero : (4 : K) ≠ 0 := by decide
private theorem four_mul_three : (4 : K) * 3 = 0 := by decide

private def generator : D := ⟨3, Ideal.subset_span (Set.mem_singleton 3)⟩

private theorem generator_ne_zero : generator ≠ 0 := by
  intro h
  exact three_ne_zero (congrArg (fun d : D ↦ (d : K)) h)

private instance : Nontrivial D := ⟨⟨generator, 0, generator_ne_zero⟩⟩

private noncomputable def retract : K →ₗ[K] D :=
  (LinearMap.toSpanSingleton K K (3 : K)).codRestrict D fun r ↦
    Ideal.mem_span_singleton'.mpr ⟨r, rfl⟩

private theorem retract_comp_subtype : retract.comp D.subtype = LinearMap.id := by
  ext d
  change (d : K) * 3 = (d : K)
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp d.property
  rw [← hr, mul_assoc, three_idempotent]

private noncomputable instance : Module.Projective K D :=
  Module.Projective.of_split D.subtype retract retract_comp_subtype

private theorem four_smul_D (d : D) : (4 : K) • d = 0 := by
  apply Subtype.ext
  change (4 : K) * (d : K) = 0
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp d.property
  rw [← hr, mul_left_comm (4 : K) r 3, four_mul_three, mul_zero]

private theorem not_free_D : ¬ Module.Free K D := by
  intro h
  let := h
  have hz : (4 : K) = 0 := eq_of_smul_eq_smul (α := D) fun d ↦ by
    rw [four_smul_D, zero_smul]
  exact four_ne_zero hz

private noncomputable def idealPresentation : (Unit →₀ K) →ₗ[K] D :=
  retract.comp (Finsupp.lapply ())

private noncomputable def idealSection : D →ₗ[K] (Unit →₀ K) :=
  (Finsupp.lsingle ()).comp D.subtype

private theorem idealSection_split : idealPresentation.comp idealSection = LinearMap.id := by
  ext d
  simpa [idealPresentation, idealSection] using LinearMap.congr_fun retract_comp_subtype d

open Classical in
/-- The nonfree ideal `(3)` has a split free presentation whose tensor coordinate
at its generator is `3`. No biorthogonality to the presented generator is assumed. -/
theorem idempotent_ideal_coordinate :
    let D := Ideal.span ({(3 : ZMod 6)} : Set (ZMod 6))
    let σ : D →ₗ[ZMod 6] (Unit →₀ ZMod 6) := (Finsupp.lsingle ()).comp D.subtype
    ¬ Module.Free (ZMod 6) D ∧
      equivFinsuppOfBasisRight
        (Finsupp.basisSingleOne : Module.Basis Unit (ZMod 6) (Unit →₀ ZMod 6))
        (σ.lTensor (ZMod 6)
          ((1 : ZMod 6) ⊗ₜ[ZMod 6] (⟨3, Ideal.subset_span (Set.mem_singleton 3)⟩ : D)))
          () = 3 := by
  change ¬ Module.Free K D ∧
    equivFinsuppOfBasisRight (Finsupp.basisSingleOne : Module.Basis Unit K (Unit →₀ K))
      (idealSection.lTensor K ((1 : K) ⊗ₜ[K] generator)) () = 3
  refine ⟨not_free_D, ?_⟩
  rw [LinearMap.lTensor_tmul, equivFinsuppOfBasisRight_apply_tmul_apply]
  simp [idealSection, generator]

open Classical in
/-- The canonical coordinates reconstruct a tensor through the concrete split
presentation of the nonfree ideal `(3)` in `ZMod 6`. -/
theorem idempotent_ideal_reconstruction
    (t : ZMod 6 ⊗[ZMod 6] Ideal.span ({(3 : ZMod 6)} : Set (ZMod 6))) :
    let D := Ideal.span ({(3 : ZMod 6)} : Set (ZMod 6))
    let σ : D →ₗ[ZMod 6] (Unit →₀ ZMod 6) := (Finsupp.lsingle ()).comp D.subtype
    let a := equivFinsuppOfBasisRight
      (Finsupp.basisSingleOne : Module.Basis Unit (ZMod 6) (Unit →₀ ZMod 6))
        (σ.lTensor (ZMod 6) t)
    (∑ i ∈ a.support,
      a i ⊗ₜ[ZMod 6] (⟨3, Ideal.subset_span (Set.mem_singleton 3)⟩ : D)) = t := by
  change
    let a := equivFinsuppOfBasisRight
      (Finsupp.basisSingleOne : Module.Basis Unit K (Unit →₀ K)) (idealSection.lTensor K t)
    (∑ i ∈ a.support, a i ⊗ₜ[K] generator) = t
  obtain ⟨a, ha, hcoord⟩ := exists_tensor_coefficients_of_split
    idealPresentation idealSection idealSection_split t
  have haeq : a = equivFinsuppOfBasisRight
      (Finsupp.basisSingleOne : Module.Basis Unit K (Unit →₀ K))
        (idealSection.lTensor K t) := by
    apply Finsupp.ext
    intro i
    rw [hcoord, equivFinsuppOfBasisRight_apply]
    change TensorProduct.rid K K (((Finsupp.lapply i).comp idealSection).lTensor K t) =
      TensorProduct.rid K K ((Finsupp.lapply i).lTensor K (idealSection.lTensor K t))
    rw [LinearMap.lTensor_comp_apply]
  have hgen (i : Unit) : idealPresentation (Finsupp.single i 1) = generator := by
    cases i
    apply Subtype.ext
    change (Finsupp.single () (1 : K)) () * 3 = 3
    simp
  rw [haeq] at ha
  simpa only [hgen] using ha

private abbrev CountableIdeal := ℕ →₀ D

private noncomputable instance : Module.Projective K CountableIdeal :=
  Module.Projective.of_equiv' (finsuppLequivDFinsupp K).symm

private theorem four_smul_countable (x : CountableIdeal) : (4 : K) • x = 0 := by
  ext n
  simp [four_smul_D]

private theorem not_free_countable : ¬ Module.Free K CountableIdeal := by
  intro h
  let := h
  have hz : (4 : K) = 0 := eq_of_smul_eq_smul (α := CountableIdeal) fun x ↦ by
    rw [four_smul_countable, zero_smul]
  exact four_ne_zero hz

private theorem not_finite_countable : ¬ Module.Finite K CountableIdeal := by
  intro h
  let := h
  let : Finite CountableIdeal := Module.finite_of_finite K
  exact (Finite.not_infinite (inferInstance : Finite CountableIdeal))
    (inferInstance : Infinite CountableIdeal)

open Classical in
/-- Every tensor with the countable direct sum of `(3)` in `ZMod 6` has finite
coordinates from a global section of its canonical free presentation, although
that right factor is neither free nor finitely generated. -/
theorem countable_ideal_tensor_coordinates
    (t : ZMod 6 ⊗[ZMod 6] (ℕ →₀ Ideal.span ({(3 : ZMod 6)} : Set (ZMod 6)))) :
    let C := ℕ →₀ Ideal.span ({(3 : ZMod 6)} : Set (ZMod 6))
    ¬ Module.Free (ZMod 6) C ∧ ¬ Module.Finite (ZMod 6) C ∧
      ∃ σ : C →ₗ[ZMod 6] (C →₀ ZMod 6),
        Function.LeftInverse (Finsupp.linearCombination (ZMod 6) id) σ ∧
        ∃ a : C →₀ ZMod 6,
          (∑ i ∈ a.support, a i ⊗ₜ[ZMod 6] i) = t ∧
          ∀ i, a i = TensorProduct.rid (ZMod 6) (ZMod 6)
            (((Finsupp.lapply i).comp σ).lTensor (ZMod 6) t) := by
  refine ⟨not_free_countable, not_finite_countable, ?_⟩
  obtain ⟨σ, hσ⟩ := Module.Projective.out (R := K) (P := CountableIdeal)
  have hcomp : (Finsupp.linearCombination K id).comp σ = LinearMap.id := by
    apply LinearMap.ext
    intro c
    exact hσ c
  obtain ⟨a, ha, hcoord⟩ := exists_tensor_coefficients_of_split
    (Finsupp.linearCombination K id) σ hcomp t
  exact ⟨σ, hσ, a, by simpa using ha, hcoord⟩

open Classical in
/-- Without the splitting identity, zero presentation and section maps cannot
reconstruct the nonzero tensor `1 ⊗ 1` over `ℕ`. -/
theorem zero_maps_do_not_reconstruct :
    ¬ ∃ a : Unit →₀ ℕ,
      (∑ i ∈ a.support, a i ⊗ₜ[ℕ] (0 : ℕ)) = (1 : ℕ) ⊗ₜ[ℕ] (1 : ℕ) ∧
      ∀ i, a i = TensorProduct.rid ℕ ℕ
        (((Finsupp.lapply i).comp (0 : ℕ →ₗ[ℕ] (Unit →₀ ℕ))).lTensor ℕ
          ((1 : ℕ) ⊗ₜ[ℕ] (1 : ℕ))) := by
  rintro ⟨a, ha, hcoord⟩
  have haz : a = 0 := by
    apply Finsupp.ext
    intro i
    simpa using hcoord i
  rw [haz] at ha
  have h := congrArg (TensorProduct.rid ℕ ℕ) ha
  simp at h

end TensorProduct.SplitExamples
