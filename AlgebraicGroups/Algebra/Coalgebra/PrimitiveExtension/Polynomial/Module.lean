/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.PrimitiveExtension
public import AlgebraicGroups.Algebra.Polynomial.QuotientXsq
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.LinearAlgebra.Dimension.Torsion.Basic
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# The polynomial primitive extension as a module

For any commutative ring `K`, put `R = K[X]` and `T = R/(X²)`. The stock
primitive `R`-coalgebra `TrivSqZeroExt R T` has underlying module `R ⊕ T`.
It is finitely presented and has cardinal module rank one, using Mathlib's
rank convention even when `K` is the zero ring. Its second summand is
annihilated by the regular scalar `X²`. If `K` is nontrivial, this gives a
nonzero torsion element and proves
that the extension is not flat.

## References

*Finite generation and group-like elements*, §3, supplies the rational
construction `ℚ[X] ⊕ ℚ[X]/(X²)`, its finite presentation, rank and torsion
calculation. The commutative-ring generality and nonflatness result here
extend that rational example.
-/

@[expose] public section

universe u

namespace TrivSqZeroExt

open Polynomial

variable (K : Type u) [CommRing K]

/-- The polynomial primitive extension is finitely presented over `K[X]`. -/
theorem polynomial_finitePresentation :
    Module.FinitePresentation (Polynomial K)
      (TrivSqZeroExt (Polynomial K)
        (Polynomial K ⧸ Ideal.span {(X : Polynomial K) ^ 2})) := by
  let I : Ideal (Polynomial K) := Ideal.span {(X : Polynomial K) ^ 2}
  let : Module.FinitePresentation (Polynomial K) (Polynomial K ⧸ I) :=
    Module.finitePresentation_of_surjective I.mkQ I.mkQ_surjective
      (by simpa only [Submodule.ker_mkQ] using
        (Submodule.fg_span_singleton (R := Polynomial K) ((X : Polynomial K) ^ 2)))
  exact inferInstanceAs
    (Module.FinitePresentation (Polynomial K) (Polynomial K × (Polynomial K ⧸ I)))

/-- The defining scalar `X²` annihilates the polynomial quotient. -/
@[simp] theorem X_sq_smul_quotientXsq
    (t : Polynomial K ⧸ Ideal.span {(X : Polynomial K) ^ 2}) :
    (X : Polynomial K) ^ 2 • t = 0 := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective t
  rw [← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk_smul,
    Submodule.Quotient.mk_eq_zero]
  exact Ideal.mul_mem_right p _ (Ideal.mem_span_singleton_self _)

/-- The scalar annihilating the quotient is nonzero over a nontrivial ring. -/
theorem polynomial_X_sq_ne_zero [Nontrivial K] : (X : Polynomial K) ^ 2 ≠ 0 :=
  (monic_X_pow 2).ne_zero

/-- The image of `1` in the second summand of the polynomial primitive extension. -/
noncomputable def polynomialTorsionElement :
    TrivSqZeroExt (Polynomial K)
      (Polynomial K ⧸ Ideal.span {(X : Polynomial K) ^ 2}) :=
  inr (Ideal.Quotient.mk (Ideal.span {(X : Polynomial K) ^ 2}) 1)

@[simp] theorem fst_polynomialTorsionElement :
    (polynomialTorsionElement K).fst = 0 := rfl

@[simp] theorem snd_polynomialTorsionElement :
    (polynomialTorsionElement K).snd =
      Ideal.Quotient.mk (Ideal.span {(X : Polynomial K) ^ 2}) 1 := rfl

theorem quotientXsqCoeffZero_polynomialTorsionElement :
    quotientXsqCoeffZero K (polynomialTorsionElement K).snd = 1 := by
  rw [snd_polynomialTorsionElement, quotientXsqCoeffZero_mk]
  simp

/-- The constant quotient class in the second summand is nonzero. -/
theorem polynomialTorsionElement_ne_zero [Nontrivial K] :
    polynomialTorsionElement K ≠ 0 := by
  intro h
  have hK := congrArg
    (fun x : TrivSqZeroExt (Polynomial K)
      (Polynomial K ⧸ Ideal.span {(X : Polynomial K) ^ 2}) =>
        quotientXsqCoeffZero K x.snd) h
  simp at hK

/-- The defining scalar annihilates the distinguished torsion element. -/
@[simp] theorem X_sq_smul_polynomialTorsionElement :
    (X : Polynomial K) ^ 2 • polynomialTorsionElement K = 0 := by
  apply TrivSqZeroExt.ext
  · simp
  · simpa only [snd_smul, snd_zero] using
      X_sq_smul_quotientXsq K (polynomialTorsionElement K).snd

/-- The distinguished element belongs to the torsion submodule. -/
theorem polynomialTorsionElement_mem_torsion :
    polynomialTorsionElement K ∈ Submodule.torsion (Polynomial K)
      (TrivSqZeroExt (Polynomial K)
        (Polynomial K ⧸ Ideal.span {(X : Polynomial K) ^ 2})) := by
  apply (Submodule.mem_torsion_iff _).2
  exact ⟨⟨(X : Polynomial K) ^ 2, (monic_X_pow 2).mem_nonZeroDivisors⟩,
    X_sq_smul_polynomialTorsionElement K⟩

/-- The polynomial primitive extension has rank one over every commutative ring. -/
theorem polynomial_rank :
    Module.rank (Polynomial K)
      (TrivSqZeroExt (Polynomial K)
        (Polynomial K ⧸ Ideal.span {(X : Polynomial K) ^ 2})) = 1 := by
  let π : TrivSqZeroExt (Polynomial K)
      (Polynomial K ⧸ Ideal.span {(X : Polynomial K) ^ 2}) →ₗ[Polynomial K] Polynomial K :=
    LinearMap.fst _ _ _
  have hπ : Function.Surjective π := fst_surjective
  have hker : LinearMap.ker π ≤ Submodule.torsion (Polynomial K)
      (TrivSqZeroExt (Polynomial K)
        (Polynomial K ⧸ Ideal.span {(X : Polynomial K) ^ 2})) := by
    intro x hx
    have hx0 : x.fst = 0 := LinearMap.mem_ker.mp hx
    apply (Submodule.mem_torsion_iff x).2
    refine ⟨⟨(X : Polynomial K) ^ 2, (monic_X_pow 2).mem_nonZeroDivisors⟩, ?_⟩
    change (X : Polynomial K) ^ 2 • x = 0
    apply TrivSqZeroExt.ext
    · simp only [fst_smul, hx0, smul_zero, fst_zero]
    · simpa only [snd_smul, snd_zero] using X_sq_smul_quotientXsq K x.snd
  calc
    _ = Module.rank (Polynomial K)
        (TrivSqZeroExt (Polynomial K)
          (Polynomial K ⧸ Ideal.span {(X : Polynomial K) ^ 2}) ⧸ LinearMap.ker π) :=
      (rank_quotient_eq_of_le_torsion hker).symm
    _ = Module.rank (Polynomial K) (Polynomial K) :=
      (π.quotKerEquivOfSurjective hπ).rank_eq
    _ = 1 := CommSemiring.rank_self _

/-- The polynomial primitive extension is not flat over a nontrivial coefficient ring. -/
theorem polynomial_not_flat [Nontrivial K] :
    ¬ Module.Flat (Polynomial K)
      (TrivSqZeroExt (Polynomial K)
        (Polynomial K ⧸ Ideal.span {(X : Polynomial K) ^ 2})) := by
  intro h
  let := h
  have hinj : IsSMulRegular
      (TrivSqZeroExt (Polynomial K)
        (Polynomial K ⧸ Ideal.span {(X : Polynomial K) ^ 2}))
      ((X : Polynomial K) ^ 2) :=
    Module.Flat.isSMulRegular_of_isRegular (monic_X_pow 2).isRegular
  exact polynomialTorsionElement_ne_zero K
    (hinj (by simpa only [smul_zero] using X_sq_smul_polynomialTorsionElement K))

end TrivSqZeroExt
