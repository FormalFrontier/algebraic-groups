/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.RingTheory.AdjoinRoot

/-!
# The quotient by the square of the indeterminate

For every commutative ring `K`, the algebra `K[X]/(X²)` is the algebra of
dual numbers over `K`. Its two coefficient maps give unique representatives
`C a + C b * X`. The equivalence uses the universal properties of the ideal
quotient and `DualNumber`; no nontriviality assumption is needed.

The quotient carries its canonical algebra structures over `K[X]` and `K`.
The equivalence and coordinates below are over `K`.
-/

@[expose] public section

noncomputable section

namespace Polynomial

universe u

open TrivSqZeroExt

variable (K : Type u) [CommRing K]

/-- The quotient of `K[X]` by `(X²)` is the algebra of dual numbers over `K`. -/
def quotientXsqEquivDualNumber :
    (K[X] ⧸ Ideal.span {(X ^ 2 : K[X])}) ≃ₐ[K] DualNumber K := by
  let I : Ideal K[X] := Ideal.span {(X ^ 2 : K[X])}
  let q : K[X] →ₐ[K] K[X] ⧸ I := Ideal.Quotient.mkₐ K I
  have hI : ∀ p : K[X], p ∈ I → aeval (DualNumber.eps : DualNumber K) p = 0 := by
    intro p hp
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp hp
    simp only [map_mul, map_pow, aeval_X, DualNumber.eps_pow_two, zero_mul]
  let f : (K[X] ⧸ I) →ₐ[K] DualNumber K :=
    Ideal.Quotient.liftₐ I (aeval DualNumber.eps) hI
  have hf (p : K[X]) : f (q p) = aeval (DualNumber.eps : DualNumber K) p :=
    DFunLike.congr_fun (Ideal.Quotient.liftₐ_comp I (aeval DualNumber.eps) hI) p
  have hX : q X * q X = 0 := by
    rw [← map_mul, ← pow_two]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  let g : DualNumber K →ₐ[K] K[X] ⧸ I :=
    DualNumber.lift ⟨(Algebra.ofId K _, q X), ⟨hX, fun _ => Commute.all _ _⟩⟩
  have hg : g DualNumber.eps = q X := by
    simp only [g, DualNumber.lift_apply_apply, DualNumber.fst_eps, DualNumber.snd_eps,
      map_zero, map_one, zero_add, one_mul]
  refine AlgEquiv.ofAlgHom f g ?_ ?_
  · apply DualNumber.algHom_ext
    change f (g DualNumber.eps) = DualNumber.eps
    rw [hg, hf, aeval_X]
  · apply Ideal.Quotient.algHom_ext
    apply Polynomial.algHom_ext
    change g (f (q X)) = q X
    rw [hf, aeval_X, hg]

/-- A polynomial class maps to its constant and linear coefficients. -/
@[simp]
theorem quotientXsqEquivDualNumber_mk (p : K[X]) :
    quotientXsqEquivDualNumber K (Ideal.Quotient.mk (Ideal.span {(X ^ 2 : K[X])}) p) =
      inl (p.coeff 0) + inr (p.coeff 1) := by
  have hp : Ideal.Quotient.mk (Ideal.span {(X ^ 2 : K[X])}) p =
      Ideal.Quotient.mk (Ideal.span {(X ^ 2 : K[X])})
        (C (p.coeff 0) + C (p.coeff 1) * X) := by
    apply Ideal.Quotient.eq.mpr
    apply Ideal.mem_span_singleton.mpr
    rw [X_pow_dvd_iff]
    intro n hn
    rcases n with _ | (_ | n) <;> simp_all
  rw [hp]
  change aeval (DualNumber.eps : DualNumber K)
    (C (p.coeff 0) + C (p.coeff 1) * X) = _
  simp only [map_add, map_mul, aeval_C, aeval_X, TrivSqZeroExt.algebraMap_eq_inl,
    DualNumber.eps, inl_mul_inr, smul_eq_mul, mul_one]

/-- A dual number maps to the class of its affine polynomial. -/
@[simp]
theorem quotientXsqEquivDualNumber_symm_apply (x : DualNumber K) :
    (quotientXsqEquivDualNumber K).symm x =
      Ideal.Quotient.mk (Ideal.span {(X ^ 2 : K[X])}) (C x.fst + C x.snd * X) := by
  change algebraMap K (K[X] ⧸ Ideal.span {(X ^ 2 : K[X])}) x.fst +
    algebraMap K (K[X] ⧸ Ideal.span {(X ^ 2 : K[X])}) x.snd *
      Ideal.Quotient.mk (Ideal.span {(X ^ 2 : K[X])}) X = _
  rw [← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap,
    Polynomial.algebraMap_eq, map_add, map_mul]

/-- The constant coordinate of a class modulo `X²`. -/
def quotientXsqCoeffZero : (K[X] ⧸ Ideal.span {(X ^ 2 : K[X])}) →ₗ[K] K :=
  (fstHom K K K).toLinearMap.comp (quotientXsqEquivDualNumber K).toLinearMap

/-- The linear coordinate of a class modulo `X²`. -/
def quotientXsqCoeffOne : (K[X] ⧸ Ideal.span {(X ^ 2 : K[X])}) →ₗ[K] K :=
  (sndHom K K).comp (quotientXsqEquivDualNumber K).toLinearMap

theorem quotientXsqCoeffZero_apply (t : K[X] ⧸ Ideal.span {(X ^ 2 : K[X])}) :
    quotientXsqCoeffZero K t = (quotientXsqEquivDualNumber K t).fst := rfl

theorem quotientXsqCoeffOne_apply (t : K[X] ⧸ Ideal.span {(X ^ 2 : K[X])}) :
    quotientXsqCoeffOne K t = (quotientXsqEquivDualNumber K t).snd := rfl

@[simp]
theorem quotientXsqCoeffZero_mk (p : K[X]) :
    quotientXsqCoeffZero K (Ideal.Quotient.mk (Ideal.span {(X ^ 2 : K[X])}) p) =
      p.coeff 0 := by
  simp [quotientXsqCoeffZero_apply]

@[simp]
theorem quotientXsqCoeffOne_mk (p : K[X]) :
    quotientXsqCoeffOne K (Ideal.Quotient.mk (Ideal.span {(X ^ 2 : K[X])}) p) =
      p.coeff 1 := by
  simp [quotientXsqCoeffOne_apply]

/-- The two coordinates reconstruct the dual number of a quotient class. -/
theorem quotientXsqEquivDualNumber_apply (t : K[X] ⧸ Ideal.span {(X ^ 2 : K[X])}) :
    quotientXsqEquivDualNumber K t =
      inl (quotientXsqCoeffZero K t) + inr (quotientXsqCoeffOne K t) :=
  (quotientXsqEquivDualNumber K t).inl_fst_add_inr_snd_eq.symm

/-- Every class modulo `X²` is represented by its constant and linear terms. -/
theorem quotientXsq_mk_coeffs (t : K[X] ⧸ Ideal.span {(X ^ 2 : K[X])}) :
    Ideal.Quotient.mk (Ideal.span {(X ^ 2 : K[X])})
      (C (quotientXsqCoeffZero K t) + C (quotientXsqCoeffOne K t) * X) = t := by
  change Ideal.Quotient.mk (Ideal.span {(X ^ 2 : K[X])})
    (C ((quotientXsqEquivDualNumber K t).fst) +
      C ((quotientXsqEquivDualNumber K t).snd) * X) = t
  rw [← quotientXsqEquivDualNumber_symm_apply]
  exact (quotientXsqEquivDualNumber K).symm_apply_apply t

/-- Two classes modulo `X²` agree if both of their coordinates agree. -/
@[ext (iff := false)]
theorem quotientXsq_ext {s t : K[X] ⧸ Ideal.span {(X ^ 2 : K[X])}}
    (h₀ : quotientXsqCoeffZero K s = quotientXsqCoeffZero K t)
    (h₁ : quotientXsqCoeffOne K s = quotientXsqCoeffOne K t) : s = t := by
  apply (quotientXsqEquivDualNumber K).injective
  exact TrivSqZeroExt.ext h₀ h₁

/-- Two classes modulo `X²` agree exactly when both coordinates agree. -/
theorem quotientXsq_ext_iff {s t : K[X] ⧸ Ideal.span {(X ^ 2 : K[X])}} :
    s = t ↔ quotientXsqCoeffZero K s = quotientXsqCoeffZero K t ∧
      quotientXsqCoeffOne K s = quotientXsqCoeffOne K t := by
  constructor
  · intro h
    exact ⟨congrArg (quotientXsqCoeffZero K) h, congrArg (quotientXsqCoeffOne K) h⟩
  · rintro ⟨h₀, h₁⟩
    exact quotientXsq_ext K h₀ h₁

/-- The affine representative of a class has unique coefficients. -/
theorem quotientXsq_mk_coeffs_eq_iff (a b : K) (t : K[X] ⧸ Ideal.span {(X ^ 2 : K[X])}) :
    Ideal.Quotient.mk (Ideal.span {(X ^ 2 : K[X])}) (C a + C b * X) = t ↔
      a = quotientXsqCoeffZero K t ∧ b = quotientXsqCoeffOne K t := by
  rw [quotientXsq_ext_iff K]
  simp only [quotientXsqCoeffZero_mk, quotientXsqCoeffOne_mk, coeff_add, coeff_C_zero,
    coeff_C_succ, coeff_C_mul, coeff_X_zero, coeff_X_one, mul_zero, mul_one, add_zero,
    zero_add]

theorem quotientXsqCoeffZero_algebraMap (a : K) :
    quotientXsqCoeffZero K (algebraMap K (K[X] ⧸ Ideal.span {(X ^ 2 : K[X])}) a) = a := by
  rw [← Ideal.Quotient.mk_algebraMap, Polynomial.algebraMap_eq]
  simpa only [coeff_C_zero] using (quotientXsqCoeffZero_mk K (C a))

theorem quotientXsqCoeffOne_algebraMap (a : K) :
    quotientXsqCoeffOne K (algebraMap K (K[X] ⧸ Ideal.span {(X ^ 2 : K[X])}) a) = 0 := by
  rw [← Ideal.Quotient.mk_algebraMap, Polynomial.algebraMap_eq]
  simpa only [coeff_C_succ] using (quotientXsqCoeffOne_mk K (C a))

/-- The constant coordinate of the class of a constant polynomial. -/
theorem quotientXsqCoeffZero_of (a : K) :
    quotientXsqCoeffZero K (Ideal.Quotient.mk (Ideal.span {(X ^ 2 : K[X])}) (C a)) = a := by
  simpa only [coeff_C_zero] using (quotientXsqCoeffZero_mk K (C a))

/-- The linear coordinate of the class of a constant polynomial. -/
theorem quotientXsqCoeffOne_of (a : K) :
    quotientXsqCoeffOne K (Ideal.Quotient.mk (Ideal.span {(X ^ 2 : K[X])}) (C a)) = 0 := by
  simpa only [coeff_C_succ] using (quotientXsqCoeffOne_mk K (C a))

/-- The constant coordinate of the class of `X`. -/
theorem quotientXsqCoeffZero_root :
    quotientXsqCoeffZero K (Ideal.Quotient.mk (Ideal.span {(X ^ 2 : K[X])}) X) = 0 := by
  simpa only [coeff_X_zero] using (quotientXsqCoeffZero_mk K X)

/-- The linear coordinate of the class of `X`. -/
theorem quotientXsqCoeffOne_root :
    quotientXsqCoeffOne K (Ideal.Quotient.mk (Ideal.span {(X ^ 2 : K[X])}) X) = 1 := by
  simpa only [coeff_X_one] using (quotientXsqCoeffOne_mk K X)

@[simp]
theorem quotientXsqCoeffZero_one :
    quotientXsqCoeffZero K (1 : K[X] ⧸ Ideal.span {(X ^ 2 : K[X])}) = 1 := by
  simpa only [map_one] using (quotientXsqCoeffZero_of K 1)

@[simp]
theorem quotientXsqCoeffOne_one :
    quotientXsqCoeffOne K (1 : K[X] ⧸ Ideal.span {(X ^ 2 : K[X])}) = 0 := by
  simpa only [map_one] using (quotientXsqCoeffOne_of K 1)

/-- The class of a constant polynomial maps to the corresponding scalar dual number. -/
theorem quotientXsqEquivDualNumber_of (a : K) :
    quotientXsqEquivDualNumber K (Ideal.Quotient.mk (Ideal.span {(X ^ 2 : K[X])}) (C a)) =
      inl a := by
  simpa only [coeff_C_zero, coeff_C_succ, inr_zero, add_zero] using
    (quotientXsqEquivDualNumber_mk K (C a))

/-- The class of `X` maps to the dual-number generator. -/
theorem quotientXsqEquivDualNumber_root :
    quotientXsqEquivDualNumber K (Ideal.Quotient.mk (Ideal.span {(X ^ 2 : K[X])}) X) =
      DualNumber.eps := by
  simpa only [coeff_X_zero, coeff_X_one, inl_zero, zero_add, DualNumber.eps] using
    (quotientXsqEquivDualNumber_mk K X)

end Polynomial
