/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.UnitriangularStageCoordinateRing
public import Mathlib.Algebra.MvPolynomial.Rename

/-!
# Polynomial coordinates for the unitriangular stage

The actual quotient by forbidden strict-upper entries is freely generated, as a
commutative algebra, by the entries whose index gap is at least the stage.
This holds over every commutative base ring, including the zero ring.

Milne's polynomial presentation is for the full unitriangular group over a
field; the stage presentation here uses the actual quotient algebra.

## References

* J. S. Milne, *Algebraic Groups* (2017), item 2.9 (polynomial
  presentation of the full unitriangular group) and §6.49 (field-case
  filtration by individual upper entries).
* Mathlib contributors, `Mathlib.Algebra.MvPolynomial.Rename`
  (`MvPolynomial.killCompl` and `rename`) and the algebra-quotient
  lifting and extensionality API.
* The existing `UnitriangularCoordinateRing.freeEquiv` supplies the full
  group's free strict-upper coordinates.
-/

@[expose] public section

noncomputable section

namespace UnitriangularStageCoordinateRing

variable (K : Type) [CommRing K] (n r : ℕ)

/-- Strict-upper indices surviving the stage ideal. -/
abbrev SurvivingPair (n r : ℕ) :=
  {p : UnitriangularCoordinateRing.StrictUpperPair (Fin n) //
    p.1.1.val + r ≤ p.1.2.val}

/-- Include a surviving index among all strict-upper indices. -/
def survivingInclusion : SurvivingPair n r →
    UnitriangularCoordinateRing.StrictUpperPair (Fin n) := Subtype.val

theorem survivingInclusion_injective : Function.Injective (survivingInclusion n r) :=
  Subtype.val_injective

theorem mem_range_survivingInclusion
    (p : UnitriangularCoordinateRing.StrictUpperPair (Fin n)) :
    p ∈ Set.range (survivingInclusion n r) ↔ p.1.1.val + r ≤ p.1.2.val := by
  constructor
  · rintro ⟨s, rfl⟩
    exact s.2
  · intro hp
    exact ⟨⟨p, hp⟩, rfl⟩

/-- Projection of all free entries onto the surviving variables. -/
def killForbidden :
    MvPolynomial (UnitriangularCoordinateRing.StrictUpperPair (Fin n)) K →ₐ[K]
      MvPolynomial (SurvivingPair n r) K :=
  MvPolynomial.killCompl (survivingInclusion_injective n r)

@[simp] theorem killForbidden_X
    (p : UnitriangularCoordinateRing.StrictUpperPair (Fin n)) :
    killForbidden K n r (MvPolynomial.X p) =
      if hp : p.1.1.val + r ≤ p.1.2.val then MvPolynomial.X ⟨p, hp⟩ else 0 := by
  classical
  by_cases hp : p.1.1.val + r ≤ p.1.2.val
  · have hr : p ∈ Set.range (survivingInclusion n r) :=
      (mem_range_survivingInclusion n r p).mpr hp
    have heq :
        (Equiv.ofInjective (survivingInclusion n r)
          (survivingInclusion_injective n r)).symm ⟨p, hr⟩ = ⟨p, hp⟩ := by
      apply (Equiv.ofInjective (survivingInclusion n r)
        (survivingInclusion_injective n r)).injective
      rw [Equiv.apply_symm_apply]
      apply Subtype.ext
      rfl
    simp only [killForbidden, MvPolynomial.killCompl, MvPolynomial.aeval_X,
      dif_pos hr, dif_pos hp, heq]
  · have hr : p ∉ Set.range (survivingInclusion n r) :=
      fun hm => hp ((mem_range_survivingInclusion n r p).mp hm)
    simp only [killForbidden, MvPolynomial.killCompl, MvPolynomial.aeval_X,
      dif_neg hr, dif_neg hp]

/-- Evaluate the ambient algebra in the surviving polynomial variables. -/
def toPolynomial : Ambient K n →ₐ[K] MvPolynomial (SurvivingPair n r) K :=
  (killForbidden K n r).comp
    (UnitriangularCoordinateRing.freeEquiv K (Fin n)).symm.toAlgHom

@[simp] theorem toPolynomial_entry
    (p : UnitriangularCoordinateRing.StrictUpperPair (Fin n)) :
    toPolynomial K n r (entry K n p.1.1 p.1.2) =
      if hp : p.1.1.val + r ≤ p.1.2.val then MvPolynomial.X ⟨p, hp⟩ else 0 := by
  change toPolynomial K n r
    (UnitriangularCoordinateRing.quotient K (Fin n)
      (GeneralLinearCoordinateRing.matrix K (Fin n) p.1.1 p.1.2)) = _
  rw [← UnitriangularCoordinateRing.freeEquiv_variable K (Fin n) p]
  simp only [toPolynomial, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
    AlgEquiv.symm_apply_apply, killForbidden_X]

theorem toPolynomial_ideal_le_ker :
    ideal K n r ≤ RingHom.ker (toPolynomial K n r).toRingHom := by
  apply Ideal.span_le.mpr
  rintro _ ⟨i, j, hij, hgap, rfl⟩
  apply RingHom.mem_ker.mpr
  change toPolynomial K n r (entry K n i j) = 0
  simpa [toPolynomial_entry, Nat.not_le.mpr hgap] using
    (toPolynomial_entry K n r ⟨(i, j), hij⟩)

/-- The direct evaluation through the actual stage quotient. -/
def toPolynomialQuotient :
    CoordinateRing K n r →ₐ[K] MvPolynomial (SurvivingPair n r) K :=
  Ideal.Quotient.liftₐ (ideal K n r) (toPolynomial K n r)
    (fun x hx => RingHom.mem_ker.mp (toPolynomial_ideal_le_ker K n r hx))

@[simp] theorem toPolynomialQuotient_quotient (x : Ambient K n) :
    toPolynomialQuotient K n r (quotient K n r x) = toPolynomial K n r x := by
  exact AlgHom.congr_fun
    (Ideal.Quotient.liftₐ_comp (ideal K n r) (toPolynomial K n r)
      (fun y hy => RingHom.mem_ker.mp (toPolynomial_ideal_le_ker K n r hy))) x

/-- Rename surviving variables and map into the actual stage quotient. -/
def fromPolynomial :
    MvPolynomial (SurvivingPair n r) K →ₐ[K] CoordinateRing K n r :=
  ((quotient K n r).comp
    (UnitriangularCoordinateRing.freeEquiv K (Fin n)).toAlgHom).comp
      (MvPolynomial.rename (survivingInclusion n r))

@[simp] theorem fromPolynomial_X (s : SurvivingPair n r) :
    fromPolynomial K n r (MvPolynomial.X s) =
      quotient K n r (entry K n s.1.1.1 s.1.1.2) := by
  change (quotient K n r)
    ((UnitriangularCoordinateRing.freeEquiv K (Fin n))
      (MvPolynomial.rename (survivingInclusion n r) (MvPolynomial.X s))) = _
  rw [MvPolynomial.rename_X, UnitriangularCoordinateRing.freeEquiv_variable]
  rfl

theorem toPolynomialQuotient_comp_fromPolynomial :
    (toPolynomialQuotient K n r).comp (fromPolynomial K n r) =
      AlgHom.id K (MvPolynomial (SurvivingPair n r) K) := by
  apply MvPolynomial.algHom_ext
  intro s
  rcases s with ⟨p, hp⟩
  simp [fromPolynomial_X, toPolynomialQuotient_quotient,
    toPolynomial_entry, hp]

theorem fromPolynomial_comp_toPolynomialQuotient :
    (fromPolynomial K n r).comp (toPolynomialQuotient K n r) =
      AlgHom.id K (CoordinateRing K n r) := by
  have hgen :
      ((fromPolynomial K n r).comp (toPolynomial K n r)).comp
          (UnitriangularCoordinateRing.freeEquiv K (Fin n)).toAlgHom =
        (quotient K n r).comp
          (UnitriangularCoordinateRing.freeEquiv K (Fin n)).toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro p
    simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply]
    rw [UnitriangularCoordinateRing.freeEquiv_variable]
    change fromPolynomial K n r
      (toPolynomial K n r (entry K n p.1.1 p.1.2)) =
        quotient K n r (entry K n p.1.1 p.1.2)
    rw [toPolynomial_entry]
    by_cases hp : p.1.1.val + r ≤ p.1.2.val
    · simp [hp, fromPolynomial_X]
    · have hgap : p.1.2.val < p.1.1.val + r := Nat.lt_of_not_ge hp
      simp [hp, quotient_entry K n r p.1.1 p.1.2 p.2 hgap]
  apply Ideal.Quotient.algHom_ext K
  apply AlgHom.ext
  intro x
  obtain ⟨p, rfl⟩ := (UnitriangularCoordinateRing.freeEquiv K (Fin n)).surjective x
  change fromPolynomial K n r
      (toPolynomialQuotient K n r
        (quotient K n r ((UnitriangularCoordinateRing.freeEquiv K (Fin n)) p))) =
    quotient K n r ((UnitriangularCoordinateRing.freeEquiv K (Fin n)) p)
  rw [toPolynomialQuotient_quotient]
  simpa only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply] using AlgHom.congr_fun hgen p

/-- The stage quotient is a polynomial algebra on its surviving entries.
Milne, *Algebraic Groups* (2017), item 2.9 gives the full unitriangular
field-case antecedent; this equivalence also removes entire superdiagonals
over arbitrary commutative rings. It preserves ring addition as an algebra
equivalence but does not identify additive group schemes or Hopf structures. -/
def polynomialEquiv :
    CoordinateRing K n r ≃ₐ[K] MvPolynomial (SurvivingPair n r) K :=
  AlgEquiv.ofAlgHom (toPolynomialQuotient K n r) (fromPolynomial K n r)
    (toPolynomialQuotient_comp_fromPolynomial K n r)
    (fromPolynomial_comp_toPolynomialQuotient K n r)

@[simp] theorem polynomialEquiv_entry
    (p : UnitriangularCoordinateRing.StrictUpperPair (Fin n)) :
    polynomialEquiv K n r (quotient K n r (entry K n p.1.1 p.1.2)) =
      if hp : p.1.1.val + r ≤ p.1.2.val then MvPolynomial.X ⟨p, hp⟩ else 0 := by
  change toPolynomialQuotient K n r (quotient K n r (entry K n p.1.1 p.1.2)) = _
  rw [toPolynomialQuotient_quotient]
  exact toPolynomial_entry K n r p

@[simp] theorem polynomialEquiv_surviving (s : SurvivingPair n r) :
    polynomialEquiv K n r
      (quotient K n r (entry K n s.1.1.1 s.1.1.2)) = MvPolynomial.X s := by
  rcases s with ⟨p, hp⟩
  simpa [hp] using polynomialEquiv_entry K n r p

@[simp] theorem polynomialEquiv_forbidden
    (p : UnitriangularCoordinateRing.StrictUpperPair (Fin n))
    (hgap : p.1.2.val < p.1.1.val + r) :
    polynomialEquiv K n r (quotient K n r (entry K n p.1.1 p.1.2)) = 0 := by
  rw [polynomialEquiv_entry]
  simp [Nat.not_le.mpr hgap]

@[simp] theorem polynomialEquiv_symm_X (s : SurvivingPair n r) :
    (polynomialEquiv K n r).symm (MvPolynomial.X s) =
      quotient K n r (entry K n s.1.1.1 s.1.1.2) :=
  fromPolynomial_X K n r s

@[simp] theorem polynomialEquiv_C (k : K) :
    polynomialEquiv K n r
      (@algebraMap K (CoordinateRing K n r) _
        (inferInstance : Semiring (CoordinateRing K n r)) _ k) =
      (MvPolynomial.C k : MvPolynomial (SurvivingPair n r) K) :=
  (polynomialEquiv K n r).commutes k

@[simp] theorem polynomialEquiv_symm_C (k : K) :
    (polynomialEquiv K n r).symm
      (MvPolynomial.C k : MvPolynomial (SurvivingPair n r) K) =
      @algebraMap K (CoordinateRing K n r) _
        (inferInstance : Semiring (CoordinateRing K n r)) _ k :=
  (polynomialEquiv K n r).symm.commutes k

end UnitriangularStageCoordinateRing
