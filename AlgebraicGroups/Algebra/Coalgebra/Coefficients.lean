/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Coalgebra.Basic
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Coefficients of finite coalgebra coordinates

Suppose `u : ι → C` is a finite family in a coalgebra over a commutative semiring,
with comultiplications `Δ(u j) = ∑ i, u i ⊗ a i j`. Ambient linear functionals
biorthogonal to `u` extract these coefficients. Coassociativity then gives
`Δ(a i j) = ∑ k, a i k ⊗ a k j`, so their span is finitely generated and has
comultiplication in the image of its tensor square.

The left counit puts the span of `u` inside the coefficient span; this containment
does not require coordinate functionals or linear independence. The right counit
instead determines the counits of the coefficients. No injectivity of tensor
inclusions is used, and the index type may be empty.

## Implementation notes

The coordinate functionals are supplied as linear maps on the ambient module.
Constructing them from a linearly independent family over a field is a separate
linear-algebra step. No compatibility of these maps with comultiplication is
assumed. The conclusion is tensor-image closure of a submodule, not a construction
of a restricted coalgebra structure.

## References

* M. E. Sweedler, *Hopf Algebras*, W. A. Benjamin, 1969: bibliographic credit for
  the classical coefficient-coalgebra method.
* Mathlib's coalgebra, tensor-product and module-finiteness formalizations.
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Coalgebra

variable {R : Type u} {C : Type v} {ι : Type w}
variable [CommSemiring R] [AddCommMonoid C] [Module R C]

/-- The span of a finite coefficient family is finitely generated, even when its
members are dependent or the index type is empty. -/
theorem fg_span_coefficients [Finite ι] (a : ι → ι → C) :
    (Submodule.span R (Set.range (Function.uncurry a))).FG :=
  Submodule.fg_span (Set.finite_range (Function.uncurry a))

variable [Coalgebra R C] [Fintype ι]

/-- Applying the left counit to a finite comultiplication expression expresses
its argument as a linear combination of the second factors. -/
theorem eq_sum_counit_smul_of_comul_eq {x : C} {p q : ι → C}
    (hΔ : comul (R := R) x = ∑ i, p i ⊗ₜ[R] q i) :
    x = ∑ i, counit (R := R) (p i) • q i := by
  let repr : Repr R x ι :=
    { index := Finset.univ, left := p, right := q, eq := hΔ.symm }
  simpa [repr] using (sum_counit_smul repr).symm

/-- The original coordinate span lies in the coefficient span by the left
counit. This requires neither linear independence nor coordinate functionals. -/
theorem span_le_span_coefficients {u : ι → C} {a : ι → ι → C}
    (hΔ : ∀ j, comul (R := R) (u j) = ∑ i, u i ⊗ₜ[R] a i j) :
    Submodule.span R (Set.range u) ≤
      Submodule.span R (Set.range (Function.uncurry a)) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  rw [eq_sum_counit_smul_of_comul_eq (hΔ j)]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, j), rfl⟩)

variable [DecidableEq ι]

/-- A biorthogonal ambient coordinate functional extracts a coefficient by
contracting the first tensor factor. -/
theorem coefficient_eq_contraction {u : ι → C} {a : ι → ι → C}
    {f : ι → (C →ₗ[R] R)}
    (hΔ : ∀ j, comul (R := R) (u j) = ∑ k, u k ⊗ₜ[R] a k j)
    (hf : ∀ i j, f i (u j) = if i = j then 1 else 0) (i j : ι) :
    a i j = ((TensorProduct.lid R C).toLinearMap ∘ₗ (f i).rTensor C)
      (comul (R := R) (u j)) := by
  have h := congrArg
    ((TensorProduct.lid R C).toLinearMap ∘ₗ (f i).rTensor C) (hΔ j)
  simpa [map_sum, hf, ite_smul] using h.symm

-- Expand both sides in right-associated tensors before contracting the first
-- factor. The order of the coefficients is `a i k`, `a k j`.
omit [DecidableEq ι] in
private theorem coassoc_coefficients {u : ι → C} {a : ι → ι → C}
    (hΔ : ∀ j, comul (R := R) (u j) = ∑ i, u i ⊗ₜ[R] a i j) (j : ι) :
    (∑ k, ∑ i, u i ⊗ₜ[R] (a i k ⊗ₜ[R] a k j)) =
      ∑ i, u i ⊗ₜ[R] comul (R := R) (a i j) := by
  simpa only [hΔ, map_sum, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
    TensorProduct.sum_tmul, TensorProduct.assoc_tmul]
    using coassoc_apply (R := R) (u j)

/-- The coefficients of finite biorthogonal coalgebra coordinates satisfy the
coefficient-comultiplication identity of the classical coefficient method. -/
theorem comul_coefficient {u : ι → C} {a : ι → ι → C}
    {f : ι → (C →ₗ[R] R)}
    (hΔ : ∀ j, comul (R := R) (u j) = ∑ k, u k ⊗ₜ[R] a k j)
    (hf : ∀ i j, f i (u j) = if i = j then 1 else 0) (i j : ι) :
    comul (R := R) (a i j) = ∑ k, a i k ⊗ₜ[R] a k j := by
  have h := congrArg
    ((TensorProduct.lid R (C ⊗[R] C)).toLinearMap ∘ₗ
      (f i).rTensor (C ⊗[R] C)) (coassoc_coefficients hΔ j)
  simpa [map_sum, hf, ite_smul] using h.symm

/-- The right counit determines the counit of each coefficient. This is a
consequence of biorthogonality, not an additional coefficient hypothesis. -/
theorem counit_coefficient {u : ι → C} {a : ι → ι → C}
    {f : ι → (C →ₗ[R] R)}
    (hΔ : ∀ j, comul (R := R) (u j) = ∑ k, u k ⊗ₜ[R] a k j)
    (hf : ∀ i j, f i (u j) = if i = j then 1 else 0) (i j : ι) :
    counit (R := R) (a i j) = if i = j then 1 else 0 := by
  have h := congrArg (fun t : C ⊗[R] R => f i (TensorProduct.rid R C t))
    (lTensor_counit_comul (R := R) (u j))
  rw [hΔ j] at h
  simpa [map_sum, hf, smul_ite, smul_eq_mul] using h

/-- The coefficient span of finite biorthogonal coalgebra coordinates has
comultiplication in the image of its tensor square, for every member of the span.
The pure-tensor preimages use both coefficient factors. -/
theorem comul_mem_range_mapIncl_span_coefficients {u : ι → C} {a : ι → ι → C}
    {f : ι → (C →ₗ[R] R)}
    (hΔ : ∀ j, comul (R := R) (u j) = ∑ k, u k ⊗ₜ[R] a k j)
    (hf : ∀ i j, f i (u j) = if i = j then 1 else 0)
    {x : C} (hx : x ∈ Submodule.span R (Set.range (Function.uncurry a))) :
    comul (R := R) x ∈ LinearMap.range (TensorProduct.mapIncl
      (Submodule.span R (Set.range (Function.uncurry a)))
      (Submodule.span R (Set.range (Function.uncurry a)))) := by
  let D := Submodule.span R (Set.range (Function.uncurry a))
  have hD : D ≤ (LinearMap.range (TensorProduct.mapIncl D D)).comap
      (comul (R := R)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨i, j⟩, rfl⟩
    change comul (R := R) (a i j) ∈ LinearMap.range (TensorProduct.mapIncl D D)
    rw [comul_coefficient hΔ hf i j]
    apply Submodule.sum_mem
    intro k _
    exact ⟨(⟨a i k, Submodule.subset_span ⟨(i, k), rfl⟩⟩ : D) ⊗ₜ[R]
      (⟨a k j, Submodule.subset_span ⟨(k, j), rfl⟩⟩ : D), rfl⟩
  exact hD hx

end Coalgebra
