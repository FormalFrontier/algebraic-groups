/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.FieldTheory.RatFunc.IntermediateField
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.RingTheory.DualNumber
public import AlgebraicGroups.Scheme.GeometricallyReduced

/-!
# A Frobenius-twisted additive line

Let `K` be a field of prime characteristic `p` and let `t : K`. This file studies the affine
group scheme cut out in the additive plane by

`Y ^ p - t * X ^ p = 0`.

Its coordinate ring is finite type and carries the additive Hopf-algebra structure. If `t` is not
a `p`-th power in `K`, the defining polynomial is irreducible, so the coordinate ring is a domain
and hence reduced. After scalar extension to any field containing `α` with `α ^ p = t`, the class
of `Y - α * X` is a nonzero nilpotent. Thus this gives a reusable example of a reduced affine
finite-type group scheme that is not geometrically reduced.

## Main definitions

- `FrobeniusTwistedLine.CoordinateRing`
- `FrobeniusTwistedLine.groupScheme`
- `FrobeniusTwistedLine.nilpotentWitness`

## Main results

- `FrobeniusTwistedLine.equation_irreducible`
- `FrobeniusTwistedLine.coordinateRing_isDomain`
- `FrobeniusTwistedLine.nilpotentWitness_ne_zero`
- `FrobeniusTwistedLine.nilpotentWitness_pow`
- `FrobeniusTwistedLine.isReduced_and_not_isGeometricallyReduced`
- `FrobeniusTwistedLine.scheme_isReduced`
- `FrobeniusTwistedLine.scheme_not_geometricallyReduced`
-/

@[expose] public section

open Polynomial

namespace RatFunc

variable {K : Type*} [Field K]

lemma pow_ne_C_of_pow_ne {p : ℕ} {t : K} (ht : ∀ x : K, x ^ p ≠ t) (z : K⟮X⟯) :
    z ^ p ≠ C t := by
  intro hz
  by_cases hp : p = 0
  · subst p
    apply ht 1
    apply C_injective
    simpa only [pow_zero, map_one] using hz
  have hzalg : IsAlgebraic K z := by
    refine ⟨Polynomial.X ^ p - Polynomial.C t, ?_, ?_⟩
    · exact Polynomial.X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero hp) t
    · simp only [map_sub, map_pow, aeval_X, aeval_C, RatFunc.algebraMap_eq_C, hz, sub_self]
  obtain ⟨c, rfl⟩ : ∃ c : K, z = C c := by
    by_contra h
    exact (z.transcendental_of_ne_C h) hzalg
  apply ht c
  exact C_injective (by simpa only [map_pow] using hz)

end RatFunc

namespace RatFunc

variable {K : Type*} [Field K]

lemma pow_ne_C_mul_X_pow_of_pow_ne {p : ℕ} {t : K} (ht : ∀ x : K, x ^ p ≠ t)
    (z : K⟮X⟯) : z ^ p ≠ C t * X ^ p := by
  intro hz
  apply pow_ne_C_of_pow_ne ht (z / X)
  rw [div_pow, hz]
  exact mul_div_cancel_right₀ _ (pow_ne_zero _ X_ne_zero)

end RatFunc

namespace Polynomial

variable {K : Type*} [Field K]

lemma irreducible_X_pow_sub_C_C_mul_X_pow {p : ℕ} (hp : p.Prime) {t : K}
    (ht : ∀ x : K, x ^ p ≠ t) :
    Irreducible ((X : K[X][X]) ^ p - C (C t * X ^ p)) := by
  rw [(monic_X_pow_sub_C (C t * X ^ p) hp.ne_zero).irreducible_iff_irreducible_map_fraction_map
    (K := RatFunc K)]
  convert X_pow_sub_C_irreducible_of_prime hp
    (RatFunc.pow_ne_C_mul_X_pow_of_pow_ne ht) using 1
  all_goals simp [RatFunc.algebraMap_X]

end Polynomial

namespace MvPolynomial

variable {K : Type*} [Field K]

lemma irreducible_X_pow_sub_C_mul_X_pow {p : ℕ} (hp : p.Prime) {t : K}
    (ht : ∀ x : K, x ^ p ≠ t) :
    Irreducible (X 0 ^ p - C t * X 1 ^ p : MvPolynomial (Fin 2) K) := by
  let e : MvPolynomial (Fin 2) K ≃ₐ[K] K[X][X] :=
    (finSuccEquiv K 1).trans (Polynomial.mapAlgEquiv (uniqueAlgEquiv K (Fin 1)))
  have eX0 : e (X 0) = Polynomial.X := by
    simp only [e, AlgEquiv.trans_apply, finSuccEquiv_X_zero,
      Polynomial.coe_mapAlgEquiv, Polynomial.map_X]
  have hu : (uniqueAlgEquiv K (Fin 1)) (X (0 : Fin 1)) = Polynomial.X := by
    change eval₂ Polynomial.C (fun _ => Polynomial.X) (X (0 : Fin 1)) = Polynomial.X
    rw [eval₂_X]
  have eX1 : e (X 1) = Polynomial.C Polynomial.X := by
    rw [show (1 : Fin 2) = (0 : Fin 1).succ from rfl]
    simp only [e, AlgEquiv.trans_apply, finSuccEquiv_X_succ,
      Polynomial.coe_mapAlgEquiv, Polynomial.map_C]
    congr 1
  have eC : e (C t) = Polynomial.C (Polynomial.C t) := e.commutes t
  apply (MulEquiv.irreducible_iff (x :=
    (X 0 ^ p - C t * X 1 ^ p : MvPolynomial (Fin 2) K)) e.toMulEquiv).mp
  change Irreducible (e (X 0 ^ p - C t * X 1 ^ p))
  rw [map_sub, map_mul, map_pow, map_pow, eX0, eX1, eC]
  simpa using
    Polynomial.irreducible_X_pow_sub_C_C_mul_X_pow hp ht

end MvPolynomial

namespace FrobeniusTwistedLine

open scoped TensorProduct

noncomputable section

variable (K : Type*) [Field K]

/-- The equation `Y ^ p - t * X ^ p` in two variables. -/
def equation (p : ℕ) (t : K) : MvPolynomial (Fin 2) K :=
  MvPolynomial.X 0 ^ p - MvPolynomial.C t * MvPolynomial.X 1 ^ p

/-- The coordinate ring cut out by `Y ^ p - t * X ^ p`. -/
abbrev CoordinateRing (p : ℕ) (t : K) :=
  MvPolynomial (Fin 2) K ⧸ Ideal.span {equation K p t}

/-- The `X` coordinate in `CoordinateRing`. -/
def x (p : ℕ) (t : K) : CoordinateRing K p t :=
  Ideal.Quotient.mk _ (MvPolynomial.X 1)

/-- The `Y` coordinate in `CoordinateRing`. -/
def y (p : ℕ) (t : K) : CoordinateRing K p t :=
  Ideal.Quotient.mk _ (MvPolynomial.X 0)

theorem y_pow_eq (p : ℕ) (t : K) :
    y K p t ^ p = algebraMap K (CoordinateRing K p t) t * x K p t ^ p := by
  rw [← sub_eq_zero]
  change Ideal.Quotient.mk _ (equation K p t) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_singleton _)

theorem equation_irreducible {p : ℕ} (hp : p.Prime) {t : K}
    (ht : ∀ z : K, z ^ p ≠ t) : Irreducible (equation K p t) :=
  MvPolynomial.irreducible_X_pow_sub_C_mul_X_pow hp ht

theorem coordinateRing_isDomain {p : ℕ} (hp : p.Prime) {t : K}
    (ht : ∀ z : K, z ^ p ≠ t) : IsDomain (CoordinateRing K p t) := by
  rw [Ideal.Quotient.isDomain_iff_prime]
  exact Ideal.isPrime_span_singleton_of_prime (equation_irreducible K hp ht).prime

instance coordinateRing_finiteType (p : ℕ) (t : K) :
    Algebra.FiniteType K (CoordinateRing K p t) := inferInstance

theorem coordinateRing_isReduced {p : ℕ} (hp : p.Prime) {t : K}
    (ht : ∀ z : K, z ^ p ≠ t) : IsReduced (CoordinateRing K p t) := by
  let _ : IsDomain (CoordinateRing K p t) := coordinateRing_isDomain K hp ht
  infer_instance

/-- A pair of elements satisfying the equation defining `CoordinateRing`. -/
def SatisfiesEquation {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (p : ℕ) (t : R) (x y : A) : Prop :=
  y ^ p - algebraMap R A t * x ^ p = 0

/-- Evaluation of the two variables at `Y = y'` and `X = x'`. -/
def eval {A : Type*} [CommRing A] [Algebra K A] (x' y' : A) :
    MvPolynomial (Fin 2) K →ₐ[K] A :=
  MvPolynomial.aeval fun i => Fin.cases y' (fun _ => x') i

theorem span_equation_le_ker_eval {A : Type*} [CommRing A] [Algebra K A]
    (p : ℕ) (t : K) (x' y' : A)
    (h : SatisfiesEquation (R := K) (A := A) p t x' y') :
    Ideal.span {equation K p t} ≤ RingHom.ker (eval K x' y').toRingHom := by
  apply Ideal.span_le.mpr
  rw [Set.singleton_subset_iff]
  apply RingHom.mem_ker.mpr
  change eval K x' y' (equation K p t) = 0
  simp only [eval, equation, map_sub, map_pow, MvPolynomial.aeval_X, map_mul,
    MvPolynomial.aeval_C, Fin.cases_zero]
  have hx1 : Fin.cases y' (fun _ : Fin 1 => x') (1 : Fin 2) = x' := rfl
  rw [hx1]
  exact h

/-- The universal map from `CoordinateRing` to a pair satisfying its equation. -/
def lift {A : Type*} [CommRing A] [Algebra K A] (p : ℕ) (t : K) (x' y' : A)
    (h : SatisfiesEquation (R := K) (A := A) p t x' y') :
    CoordinateRing K p t →ₐ[K] A :=
  Ideal.Quotient.liftₐ _ (eval K x' y') fun _f hf =>
    RingHom.mem_ker.mp (span_equation_le_ker_eval K p t x' y' h hf)

theorem lift_comp_mk {A : Type*} [CommRing A] [Algebra K A]
    (p : ℕ) (t : K) (x' y' : A)
    (h : SatisfiesEquation (R := K) (A := A) p t x' y') :
    (lift K p t x' y' h).comp
      (Ideal.Quotient.mkₐ K (Ideal.span {equation K p t})) = eval K x' y' := by
  apply Ideal.Quotient.liftₐ_comp

@[simp]
theorem lift_x {A : Type*} [CommRing A] [Algebra K A]
    (p : ℕ) (t : K) (x' y' : A)
    (h : SatisfiesEquation (R := K) (A := A) p t x' y') :
    lift K p t x' y' h (x K p t) = x' := by
  change ((lift K p t x' y' h).comp
    (Ideal.Quotient.mkₐ K (Ideal.span {equation K p t}))) (MvPolynomial.X 1) = x'
  rw [lift_comp_mk]
  simp only [eval, MvPolynomial.aeval_X]
  rfl

@[simp]
theorem lift_y {A : Type*} [CommRing A] [Algebra K A]
    (p : ℕ) (t : K) (x' y' : A)
    (h : SatisfiesEquation (R := K) (A := A) p t x' y') :
    lift K p t x' y' h (y K p t) = y' := by
  change ((lift K p t x' y' h).comp
    (Ideal.Quotient.mkₐ K (Ideal.span {equation K p t}))) (MvPolynomial.X 0) = y'
  rw [lift_comp_mk]
  simp only [eval, MvPolynomial.aeval_X, Fin.cases_zero]

@[ext]
theorem hom_ext {A : Type*} [Semiring A] [Algebra K A]
    {p : ℕ} {t : K} {f g : CoordinateRing K p t →ₐ[K] A}
    (hx : f (x K p t) = g (x K p t)) (hy : f (y K p t) = g (y K p t)) : f = g := by
  rw [← AlgHom.cancel_right (Ideal.Quotient.mkₐ_surjective K _)]
  apply MvPolynomial.algHom_ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa [y] using hy
  · have : j = 0 := Subsingleton.elim _ _
    subst j
    simpa [x] using hx

/-- Evaluation of `Y` at the dual-number infinitesimal and `X` at zero. -/
def dualNumberEval (L : Type*) [Field L] [Algebra K L] :
    MvPolynomial (Fin 2) K →ₐ[K] DualNumber L :=
  MvPolynomial.aeval fun i => Fin.cases (DualNumber.eps : DualNumber L) (fun _ => 0) i

/-- The map from `CoordinateRing` to dual numbers that sends `Y` to the nonzero
infinitesimal and `X` to zero. -/
def toDualNumber (L : Type*) [Field L] [Algebra K L]
    {p : ℕ} (hp : p.Prime) (t : K) : CoordinateRing K p t →ₐ[K] DualNumber L := by
  refine Ideal.Quotient.liftₐ _ (dualNumberEval K L) fun f hf => ?_
  rw [← RingHom.mem_ker]
  apply (Ideal.span_le.mpr ?_) hf
  rw [Set.singleton_subset_iff]
  change dualNumberEval K L (equation K p t) = 0
  simp only [equation, dualNumberEval, map_sub, map_pow, MvPolynomial.aeval_X,
    map_mul, MvPolynomial.aeval_C, Fin.cases_zero]
  rw [pow_eq_zero_of_le hp.two_le DualNumber.eps_pow_two]
  rw [zero_sub, neg_eq_zero]
  change algebraMap K (DualNumber L) t * (0 : DualNumber L) ^ p = 0
  rw [zero_pow hp.ne_zero, mul_zero]

@[simp]
theorem toDualNumber_x (L : Type*) [Field L] [Algebra K L]
    {p : ℕ} (hp : p.Prime) (t : K) : toDualNumber K L hp t (x K p t) = 0 := by
  change ((toDualNumber K L hp t).comp
    (Ideal.Quotient.mkₐ K (Ideal.span {equation K p t}))) (MvPolynomial.X 1) = 0
  rw [show (toDualNumber K L hp t).comp
    (Ideal.Quotient.mkₐ K (Ideal.span {equation K p t})) = dualNumberEval K L from by
      apply Ideal.Quotient.liftₐ_comp]
  simp only [dualNumberEval, MvPolynomial.aeval_X]
  rfl

@[simp]
theorem toDualNumber_y (L : Type*) [Field L] [Algebra K L]
    {p : ℕ} (hp : p.Prime) (t : K) :
    toDualNumber K L hp t (y K p t) = (DualNumber.eps : DualNumber L) := by
  change ((toDualNumber K L hp t).comp
    (Ideal.Quotient.mkₐ K (Ideal.span {equation K p t}))) (MvPolynomial.X 0) = _
  rw [show (toDualNumber K L hp t).comp
    (Ideal.Quotient.mkₐ K (Ideal.span {equation K p t})) = dualNumberEval K L from by
      apply Ideal.Quotient.liftₐ_comp]
  simp only [dualNumberEval, MvPolynomial.aeval_X, Fin.cases_zero]

/-- The element `1 ⊗ Y - α ⊗ X` after scalar extension. -/
def nilpotentWitness (L : Type*) [Field L] [Algebra K L]
    (p : ℕ) (t : K) (α : L) : L ⊗[K] CoordinateRing K p t :=
  (1 : L) ⊗ₜ[K] y K p t - α ⊗ₜ[K] x K p t

/-- Evaluation of the scalar extension in dual numbers. -/
def baseChangeToDualNumber (L : Type*) [Field L] [Algebra K L]
    {p : ℕ} (hp : p.Prime) (t : K) :
    L ⊗[K] CoordinateRing K p t →ₐ[L] DualNumber L :=
  (toDualNumber K L hp t).liftEquiv K L (CoordinateRing K p t) (DualNumber L)

@[simp]
theorem baseChangeToDualNumber_witness (L : Type*) [Field L] [Algebra K L]
    {p : ℕ} (hp : p.Prime) (t : K) (α : L) :
    baseChangeToDualNumber K L hp t (nilpotentWitness K L p t α) =
      (DualNumber.eps : DualNumber L) := by
  simp [baseChangeToDualNumber, nilpotentWitness, toDualNumber_x, toDualNumber_y]

theorem nilpotentWitness_ne_zero (L : Type*) [Field L] [Algebra K L]
    {p : ℕ} (hp : p.Prime) (t : K) (α : L) : nilpotentWitness K L p t α ≠ 0 := by
  intro h
  have := congrArg (baseChangeToDualNumber K L hp t) h
  rw [baseChangeToDualNumber_witness, map_zero] at this
  exact one_ne_zero (congrArg TrivSqZeroExt.snd this)

theorem nilpotentWitness_pow (L : Type*) [Field L] [Algebra K L]
    {p : ℕ} (hp : p.Prime) [CharP K p] (t : K) (α : L)
    (hα : α ^ p = algebraMap K L t) : nilpotentWitness K L p t α ^ p = 0 := by
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : CharP L p := CharP.of_ringHom_of_ne_zero (algebraMap K L) p hp.ne_zero
  let _ : Nontrivial (L ⊗[K] CoordinateRing K p t) :=
    (baseChangeToDualNumber K L hp t).domain_nontrivial
  let _ : CharP (L ⊗[K] CoordinateRing K p t) p :=
    CharP.of_ringHom_of_ne_zero (algebraMap L _) p hp.ne_zero
  rw [nilpotentWitness,
    sub_pow_char ((1 : L) ⊗ₜ[K] y K p t) (α ⊗ₜ[K] x K p t),
    Algebra.TensorProduct.tmul_pow,
    Algebra.TensorProduct.tmul_pow, one_pow, y_pow_eq, hα]
  rw [show algebraMap K (CoordinateRing K p t) t * x K p t ^ p =
      t • x K p t ^ p from (Algebra.smul_def t _).symm]
  rw [← TensorProduct.smul_tmul]
  simp [Algebra.smul_def]

theorem nilpotentWitness_isNilpotent (L : Type*) [Field L] [Algebra K L]
    {p : ℕ} (hp : p.Prime) [CharP K p] (t : K) (α : L)
    (hα : α ^ p = algebraMap K L t) :
    IsNilpotent (nilpotentWitness K L p t α) :=
  ⟨p, nilpotentWitness_pow K L hp t α hα⟩

theorem baseChange_not_isReduced (L : Type*) [Field L] [Algebra K L]
    {p : ℕ} (hp : p.Prime) [CharP K p] (t : K) (α : L)
    (hα : α ^ p = algebraMap K L t) :
    ¬IsReduced (L ⊗[K] CoordinateRing K p t) := by
  intro h
  let _ : IsReduced (L ⊗[K] CoordinateRing K p t) := h
  exact nilpotentWitness_ne_zero K L hp t α
    (IsReduced.eq_zero _ (nilpotentWitness_isNilpotent K L hp t α hα))

theorem not_isGeometricallyReduced {p : ℕ} (hp : p.Prime) [CharP K p] (t : K) :
    ¬Algebra.IsGeometricallyReduced K (CoordinateRing K p t) := by
  intro h
  let α : AlgebraicClosure K := Classical.choose
    (IsAlgClosed.exists_pow_nat_eq (algebraMap K (AlgebraicClosure K) t) hp.pos)
  have hα : α ^ p = algebraMap K (AlgebraicClosure K) t := Classical.choose_spec
    (IsAlgClosed.exists_pow_nat_eq (algebraMap K (AlgebraicClosure K) t) hp.pos)
  exact baseChange_not_isReduced K (AlgebraicClosure K) hp t α hα
    ((Algebra.isGeometricallyReduced_field_iff K (CoordinateRing K p t)).mp h)

theorem isReduced_and_not_isGeometricallyReduced {p : ℕ} (hp : p.Prime)
    [CharP K p] {t : K} (ht : ∀ z : K, z ^ p ≠ t) :
    IsReduced (CoordinateRing K p t) ∧
      ¬Algebra.IsGeometricallyReduced K (CoordinateRing K p t) :=
  ⟨coordinateRing_isReduced K hp ht, not_isGeometricallyReduced K hp t⟩

variable {K}

theorem satisfiesEquation_zero {A : Type*} [CommRing A] [Algebra K A]
    {p : ℕ} (hp : p ≠ 0) (t : K) : SatisfiesEquation p t (0 : A) 0 := by
  simp [SatisfiesEquation, hp]

theorem SatisfiesEquation.map {A B : Type*} [Ring A] [Ring B]
    [Algebra K A] [Algebra K B] {p : ℕ} {t : K} {x y : A}
    (h : SatisfiesEquation p t x y) (f : A →ₐ[K] B) :
    SatisfiesEquation p t (f x) (f y) := by
  rw [SatisfiesEquation] at h ⊢
  rw [← map_pow, ← map_pow, ← f.commutes t, ← map_mul, ← map_sub, h, map_zero]

theorem SatisfiesEquation.add {A : Type*} [CommRing A] [Algebra K A]
    {p : ℕ} [Fact p.Prime] [CharP A p] {t : K} {x₁ y₁ x₂ y₂ : A}
    (h₁ : SatisfiesEquation p t x₁ y₁) (h₂ : SatisfiesEquation p t x₂ y₂) :
    SatisfiesEquation p t (x₁ + x₂) (y₁ + y₂) := by
  rw [SatisfiesEquation, add_pow_char, add_pow_char, sub_eq_zero]
  rw [SatisfiesEquation, sub_eq_zero] at h₁ h₂
  exact (congrArg₂ (· + ·) h₁ h₂).trans (mul_add _ _ _).symm

theorem SatisfiesEquation.neg {A : Type*} [CommRing A] [Algebra K A]
    {p : ℕ} [Fact p.Prime] [CharP A p] {t : K} {x y : A} (h : SatisfiesEquation p t x y) :
    SatisfiesEquation p t (-x) (-y) := by
  rw [SatisfiesEquation] at h
  rw [SatisfiesEquation]
  rw [show -x = 0 - x by simp, show -y = 0 - y by simp, sub_pow_char, sub_pow_char]
  simp only [zero_pow (Fact.out : p.Prime).ne_zero, zero_sub]
  calc
    -y ^ p - algebraMap K A t * -x ^ p =
        -(y ^ p - algebraMap K A t * x ^ p) := by ring
    _ = 0 := by rw [h, neg_zero]

variable (K)

theorem coordinate_satisfiesEquation (p : ℕ) (t : K) :
    SatisfiesEquation p t (x K p t) (y K p t) := by
  rw [SatisfiesEquation, sub_eq_zero]
  exact y_pow_eq K p t

/-- Evaluation at the origin. -/
def origin {p : ℕ} [Fact p.Prime] (t : K) : CoordinateRing K p t →ₐ[K] K :=
  lift K p t 0 0 (satisfiesEquation_zero (Fact.out : p.Prime).ne_zero t)

instance coordinateRing_nontrivial {p : ℕ} [Fact p.Prime] (t : K) :
    Nontrivial (CoordinateRing K p t) := (origin K t).domain_nontrivial

instance coordinateRing_charP {p : ℕ} [Fact p.Prime] [CharP K p] (t : K) :
    CharP (CoordinateRing K p t) p :=
  CharP.of_ringHom_of_ne_zero (algebraMap K _) p (Fact.out : p.Prime).ne_zero

def comulX (p : ℕ) (t : K) :
    CoordinateRing K p t ⊗[K] CoordinateRing K p t :=
  Algebra.TensorProduct.includeLeft (R := K) (S := K)
      (A := CoordinateRing K p t) (B := CoordinateRing K p t) (x K p t) +
    Algebra.TensorProduct.includeRight (R := K)
      (A := CoordinateRing K p t) (B := CoordinateRing K p t) (x K p t)

def comulY (p : ℕ) (t : K) :
    CoordinateRing K p t ⊗[K] CoordinateRing K p t :=
  Algebra.TensorProduct.includeLeft (R := K) (S := K)
      (A := CoordinateRing K p t) (B := CoordinateRing K p t) (y K p t) +
    Algebra.TensorProduct.includeRight (R := K)
      (A := CoordinateRing K p t) (B := CoordinateRing K p t) (y K p t)

theorem comul_satisfiesEquation {p : ℕ} [Fact p.Prime] [CharP K p] (t : K) :
    SatisfiesEquation p t (comulX K p t) (comulY K p t) := by
  let _ : Nontrivial (CoordinateRing K p t ⊗[K] CoordinateRing K p t) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left K
      (CoordinateRing K p t) (CoordinateRing K p t) (algebraMap K _).injective
  let _ : CharP (CoordinateRing K p t ⊗[K] CoordinateRing K p t) p :=
    CharP.of_ringHom_of_ne_zero (algebraMap K _) p (Fact.out : p.Prime).ne_zero
  rw [SatisfiesEquation, comulX, comulY,
    add_pow_char (Algebra.TensorProduct.includeLeft (y K p t))
      (Algebra.TensorProduct.includeRight (y K p t)),
    add_pow_char (Algebra.TensorProduct.includeLeft (x K p t))
      (Algebra.TensorProduct.includeRight (x K p t)), mul_add]
  simp only [Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_pow, one_pow,
    y_pow_eq]
  simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [sub_eq_zero]
  rw [show algebraMap K (CoordinateRing K p t) t * x K p t ^ p =
      t • x K p t ^ p from (Algebra.smul_def t _).symm]
  rw [show algebraMap K (CoordinateRing K p t) t =
      t • (1 : CoordinateRing K p t) from by
        simpa only [mul_one] using
          (Algebra.smul_def t (1 : CoordinateRing K p t)).symm]
  exact (TensorProduct.smul_tmul t (1 : CoordinateRing K p t) (x K p t ^ p)).symm

/-- Comultiplication corresponding to coordinatewise addition. -/
def comul {p : ℕ} [Fact p.Prime] [CharP K p] (t : K) :
    CoordinateRing K p t →ₐ[K]
      CoordinateRing K p t ⊗[K] CoordinateRing K p t :=
  lift K p t (comulX K p t) (comulY K p t) (comul_satisfiesEquation K t)

@[simp]
theorem comul_x {p : ℕ} [Fact p.Prime] [CharP K p] (t : K) :
    comul K t (x K p t) = comulX K p t := lift_x K _ _ _ _ _

@[simp]
theorem comul_y {p : ℕ} [Fact p.Prime] [CharP K p] (t : K) :
    comul K t (y K p t) = comulY K p t := lift_y K _ _ _ _ _

/-- Counit corresponding to the origin. -/
def counit {p : ℕ} [Fact p.Prime] (t : K) : CoordinateRing K p t →ₐ[K] K :=
  origin K t

@[simp]
theorem counit_x {p : ℕ} [Fact p.Prime] (t : K) : counit K t (x K p t) = 0 :=
  by simp [counit, origin]

@[simp]
theorem counit_y {p : ℕ} [Fact p.Prime] (t : K) : counit K t (y K p t) = 0 :=
  by simp [counit, origin]

/-- Antipode corresponding to coordinatewise negation. -/
def antipode {p : ℕ} [Fact p.Prime] [CharP K p] (t : K) :
    CoordinateRing K p t →ₐ[K] CoordinateRing K p t :=
  lift K p t (-x K p t) (-y K p t) (coordinate_satisfiesEquation K p t).neg

@[simp]
theorem antipode_x {p : ℕ} [Fact p.Prime] [CharP K p] (t : K) :
    antipode K t (x K p t) = -x K p t := lift_x K _ _ _ _ _

@[simp]
theorem antipode_y {p : ℕ} [Fact p.Prime] [CharP K p] (t : K) :
    antipode K t (y K p t) = -y K p t := lift_y K _ _ _ _ _

noncomputable instance coordinateRing_bialgebra {p : ℕ} [Fact p.Prime]
    [CharP K p] (t : K) : Bialgebra K (CoordinateRing K p t) :=
  Bialgebra.ofAlgHom (comul K t) (counit K t)
    (by
      apply hom_ext
      · simp [comulX, Algebra.TensorProduct.includeLeft_apply,
          Algebra.TensorProduct.includeRight_apply, TensorProduct.add_tmul,
          TensorProduct.tmul_add, Algebra.TensorProduct.one_def, add_assoc]
      · simp [comulY, Algebra.TensorProduct.includeLeft_apply,
          Algebra.TensorProduct.includeRight_apply, TensorProduct.add_tmul,
          TensorProduct.tmul_add, Algebra.TensorProduct.one_def, add_assoc])
    (by
      apply hom_ext <;>
        simp [comulX, comulY, Algebra.TensorProduct.includeLeft_apply,
          Algebra.TensorProduct.includeRight_apply])
    (by
      apply hom_ext <;>
        simp [comulX, comulY, Algebra.TensorProduct.includeLeft_apply,
          Algebra.TensorProduct.includeRight_apply])

noncomputable instance coordinateRing_hopfAlgebra {p : ℕ} [Fact p.Prime]
    [CharP K p] (t : K) : HopfAlgebra K (CoordinateRing K p t) :=
  HopfAlgebra.ofAlgHom (antipode K t)
    (by
      apply hom_ext
      · change (Algebra.TensorProduct.lift (antipode K t)
          (AlgHom.id K (CoordinateRing K p t)) (fun _ _ => Commute.all _ _))
            (comul K t (x K p t)) = algebraMap K _ (counit K t (x K p t))
        simp [comulX]
      · change (Algebra.TensorProduct.lift (antipode K t)
          (AlgHom.id K (CoordinateRing K p t)) (fun _ _ => Commute.all _ _))
            (comul K t (y K p t)) = algebraMap K _ (counit K t (y K p t))
        simp [comulY])
    (by
      apply hom_ext
      · change (Algebra.TensorProduct.lift (AlgHom.id K (CoordinateRing K p t))
          (antipode K t) (fun _ _ => Commute.all _ _))
            (comul K t (x K p t)) = algebraMap K _ (counit K t (x K p t))
        simp [comulX]
      · change (Algebra.TensorProduct.lift (AlgHom.id K (CoordinateRing K p t))
          (antipode K t) (fun _ _ => Commute.all _ _))
            (comul K t (y K p t)) = algebraMap K _ (counit K t (y K p t))
        simp [comulY])

open CategoryTheory
open AlgebraicGeometry

/-- The affine scheme over `K` represented by `CoordinateRing`. -/
abbrev scheme (p : ℕ) (t : K) : Over (Spec (.of K)) :=
  (Spec (.of (CoordinateRing K p t))).asOver (Spec (.of K))

instance scheme_locallyOfFiniteType (p : ℕ) (t : K) :
    LocallyOfFiniteType (scheme K p t).hom := by
  let _ : Algebra.FiniteType K (CoordinateRing K p t) :=
    coordinateRing_finiteType K p t
  change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
    (algebraMap K (CoordinateRing K p t))))
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  simpa [RingHom.finiteType_algebraMap]

instance scheme_quasiCompact (p : ℕ) (t : K) : QuasiCompact (scheme K p t).hom := by
  change QuasiCompact (Spec.map (CommRingCat.ofHom
    (algebraMap K (CoordinateRing K p t))))
  infer_instance

/-- The affine group scheme whose group law is coordinatewise addition. -/
abbrev groupScheme {p : ℕ} [Fact p.Prime] [CharP K p] (t : K) :
    Grp (Over (Spec (.of K))) :=
  ⟨scheme K p t⟩

theorem scheme_isReduced {p : ℕ} (hp : p.Prime) {t : K}
    (ht : ∀ z : K, z ^ p ≠ t) : AlgebraicGeometry.IsReduced (scheme K p t).left := by
  change AlgebraicGeometry.IsReduced (Spec (.of (CoordinateRing K p t)))
  rw [AlgebraicGeometry.affine_isReduced_iff]
  exact coordinateRing_isReduced K hp ht

theorem scheme_not_geometricallyReduced {p : ℕ} (hp : p.Prime) [CharP K p] (t : K) :
    ¬GeometricallyReduced (scheme K p t).hom := by
  intro h
  let _ : GeometricallyReduced (Spec.map (CommRingCat.ofHom
      (algebraMap K (CoordinateRing K p t)))) := h
  exact not_isGeometricallyReduced K hp t
    (AlgebraicGeometry.Algebra.isGeometricallyReduced_of_geometricallyReduced_spec
      K (CoordinateRing K p t))

end

end FrobeniusTwistedLine
