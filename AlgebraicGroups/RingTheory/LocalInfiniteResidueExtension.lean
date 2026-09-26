/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.LocalRing.ResidueField.Polynomial

@[expose] public section

/-!
# A local faithfully flat extension with infinite residue field

For a local ring `R`, localize `R[X]` at the extension of the maximal ideal of
`R`.  The resulting ring is a faithfully flat local `R`-algebra whose residue
field is the rational function field over the residue field of `R`, and is
therefore infinite.

This construction is useful for arguments that may be checked after faithfully
flat local base change and need an infinite residue field.
-/

noncomputable section

namespace LocalInfiniteResidueExtension

universe u

open scoped Polynomial

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- The extension of the maximal ideal of a local ring to its polynomial ring. -/
abbrev genericPrime : Ideal R[X] :=
  (IsLocalRing.maximalIdeal R).map Polynomial.C

/-- The local ring at the generic point of the closed fibre of `R[X]`. -/
abbrev GenericLocalExtension := Localization.AtPrime (genericPrime R)

lemma genericPrime_liesOver :
    (genericPrime R).LiesOver (IsLocalRing.maximalIdeal R) := by
  constructor
  ext x
  change x ∈ IsLocalRing.maximalIdeal R ↔
    Polynomial.C x ∈ (IsLocalRing.maximalIdeal R).map Polynomial.C
  rw [Ideal.mem_map_C_iff]
  constructor
  · intro hx n
    by_cases hn : n = 0
    · subst n
      simpa using hx
    · simp [Polynomial.coeff_C, hn]
  · intro h
    simpa using h 0

lemma isLocalHom_algebraMap :
    IsLocalHom (algebraMap R (GenericLocalExtension R)) := by
  apply ((IsLocalRing.local_hom_TFAE
    (algebraMap R (GenericLocalExtension R))).out 5 1).mp
  ext x
  change algebraMap R[X] (GenericLocalExtension R) (Polynomial.C x) ∈
      IsLocalRing.maximalIdeal (GenericLocalExtension R) ↔
    x ∈ IsLocalRing.maximalIdeal R
  rw [IsLocalization.AtPrime.to_map_mem_maximal_iff
    (S := GenericLocalExtension R) (I := genericPrime R)]
  rw [Ideal.mem_map_C_iff]
  simp only [IsLocalRing.mem_maximalIdeal]
  constructor
  · intro h
    simpa using h 0
  · intro hx n
    by_cases hn : n = 0
    · subst n
      simpa using hx
    · simp [Polynomial.coeff_C, hn]

lemma faithfullyFlat : Module.FaithfullyFlat R (GenericLocalExtension R) := by
  let _ := isLocalHom_algebraMap R
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- The residue field of the generic local extension is the rational function
field over the residue field of the original local ring. -/
noncomputable def residueFieldEquivRatFunc :
    IsLocalRing.ResidueField (GenericLocalExtension R) ≃+*
      RatFunc (IsLocalRing.maximalIdeal R).ResidueField := by
  let _ := genericPrime_liesOver R
  letI := Localization.AtPrime.algebraOfLiesOver
    (IsLocalRing.maximalIdeal R) (genericPrime R)
  exact (Polynomial.residueFieldMapCAlgEquiv
    (IsLocalRing.maximalIdeal R) (genericPrime R) rfl).toRingEquiv

/-- The generic local extension has infinite residue field. -/
lemma infinite_residueField :
    Infinite (IsLocalRing.ResidueField (GenericLocalExtension R)) := by
  let _ : Infinite (RatFunc (IsLocalRing.maximalIdeal R).ResidueField) :=
    Infinite.of_injective
      (algebraMap (IsLocalRing.maximalIdeal R).ResidueField[X]
        (RatFunc (IsLocalRing.maximalIdeal R).ResidueField))
      (FaithfulSMul.algebraMap_injective
        (IsLocalRing.maximalIdeal R).ResidueField[X]
        (RatFunc (IsLocalRing.maximalIdeal R).ResidueField))
  exact (residueFieldEquivRatFunc R).toEquiv.infinite_iff.mpr inferInstance

end LocalInfiniteResidueExtension
