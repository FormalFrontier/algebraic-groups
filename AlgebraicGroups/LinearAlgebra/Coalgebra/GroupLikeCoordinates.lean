/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Coalgebra.GroupLike
public import Mathlib.RingTheory.Idempotents

/-!
# Coordinates in a basis of group-like elements

For a basis of group-like elements over a commutative semiring, an element is group-like
if and only if distinct coordinates have product zero and the finite-support sum of its
coordinates is one. Coordinate idempotence follows from these two conditions; it is not
an additional hypothesis. The index type need not be finite.

The counit and comultiplication coordinate lemmas only require coalgebra structure maps,
with their respective values on the basis. In particular, the comultiplication-only
criterion includes idempotence but does not impose counit normalization.

## References

The proofs use Mathlib's basis coordinate maps and tensor-product basis formula. The
redundancy of idempotence uses Mathlib's
`CompleteOrthogonalIdempotents.iff_ortho_complete` on the finite support of the coordinates.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

variable {R : Type u} {C : Type v} {I : Type w}
variable [CommSemiring R] [AddCommMonoid C] [Module R C]

namespace Module.Basis

section Maps

variable [CoalgebraStruct R C]

/-- If the counit is one on each basis vector, it is the finite-support sum of the
coordinates. -/
theorem counit_eq_sum_repr (b : Module.Basis I R C)
    (hcounit : ∀ i, Coalgebra.counit (R := R) (b i) = 1) (x : C) :
    Coalgebra.counit (R := R) x = (b.repr x).sum (fun _ r ↦ r) := by
  have h : Coalgebra.counit (R := R) = b.sumCoords := by
    apply b.ext
    intro i
    simpa using hcounit i
  calc
    Coalgebra.counit (R := R) x = b.sumCoords x := LinearMap.congr_fun h x
    _ = (b.repr x).sum (fun _ => id) := congrFun b.coe_sumCoords x
    _ = (b.repr x).sum (fun _ r ↦ r) :=
      Finsupp.sum_congr (fun i _ ↦ id_eq (b.repr x i))

/-- A diagonal comultiplication has diagonal tensor-basis coordinates. The basis
coordinate on the right expresses the Kronecker delta without a decidable equality
assumption on the index type. -/
theorem tensorProduct_repr_comul_apply (b : Module.Basis I R C)
    (hcomul : ∀ i, Coalgebra.comul (R := R) (b i) = b i ⊗ₜ[R] b i)
    (x : C) (i j : I) :
    (b.tensorProduct b).repr (Coalgebra.comul (R := R) x) (i, j) =
      b.repr x i * b.repr (b i) j := by
  classical
  have h : ((b.tensorProduct b).coord (i, j)).comp (Coalgebra.comul (R := R)) =
      b.repr (b i) j • b.coord i := by
    apply b.ext
    intro k
    simp only [LinearMap.comp_apply, Module.Basis.coord_apply, hcomul,
      tensorProduct_repr_tmul_apply, LinearMap.smul_apply, smul_eq_mul]
    by_cases hk : k = i
    · subst k
      rfl
    · have hki : b.repr (b k) i = 0 := by
        simp [hk]
      simp only [hki, mul_zero]
  simpa only [LinearMap.comp_apply, Module.Basis.coord_apply, LinearMap.smul_apply,
    smul_eq_mul, mul_comm] using LinearMap.congr_fun h x

/-- For a diagonal comultiplication, an element equals its own tensor square under
comultiplication if and only if its coordinates form an orthogonal family of idempotents.
This criterion does not require counit normalization. -/
theorem comul_eq_tmul_self_iff_orthogonalIdempotents_repr (b : Module.Basis I R C)
    (hcomul : ∀ i, Coalgebra.comul (R := R) (b i) = b i ⊗ₜ[R] b i)
    (x : C) :
    Coalgebra.comul (R := R) x = x ⊗ₜ[R] x ↔
      OrthogonalIdempotents (fun i ↦ b.repr x i) := by
  classical
  constructor
  · intro hx
    have hcoord (i j : I) :
        b.repr x i * b.repr x j = b.repr x i * b.repr (b i) j := by
      have hij := congrArg (fun t ↦ (b.tensorProduct b).repr t (i, j)) hx
      rw [b.tensorProduct_repr_comul_apply hcomul, tensorProduct_repr_tmul_apply,
        smul_eq_mul] at hij
      simpa only [mul_comm] using hij.symm
    refine ⟨?_, ?_⟩
    · intro i
      change b.repr x i * b.repr x i = b.repr x i
      simpa using hcoord i i
    · intro i j hij
      simpa [b.repr_self_apply, hij] using hcoord i j
  · intro hx
    apply (b.tensorProduct b).repr.injective
    apply Finsupp.ext
    rintro ⟨i, j⟩
    rw [b.tensorProduct_repr_comul_apply hcomul, tensorProduct_repr_tmul_apply,
      smul_eq_mul]
    by_cases hij : i = j
    · subst j
      simpa using (hx.idem i).eq.symm
    · rw [b.repr_self_apply, ite_eq_right hij, mul_zero]
      exact (hx.ortho (Ne.symm hij)).symm

end Maps

section GroupLike

variable [Coalgebra R C]

/-- In a basis of group-like elements over a commutative semiring, an element is
group-like exactly when distinct coordinates multiply to zero and the finite-support
sum of its coordinates is one. Idempotence of the coordinates follows by applying
`CompleteOrthogonalIdempotents.iff_ortho_complete` to their support. -/
theorem isGroupLikeElem_iff_pairwise_mul_eq_zero_and_sum_eq_one
    (b : Module.Basis I R C) (hb : ∀ i, IsGroupLikeElem R (b i)) (x : C) :
    IsGroupLikeElem R x ↔
      Pairwise (fun i j ↦ b.repr x i * b.repr x j = 0) ∧
        (b.repr x).sum (fun _ r ↦ r) = 1 := by
  have hcounit := b.counit_eq_sum_repr (fun i ↦ (hb i).counit_eq_one) x
  have hcomul := b.comul_eq_tmul_self_iff_orthogonalIdempotents_repr
    (fun i ↦ (hb i).comul_eq_tmul_self) x
  constructor
  · intro hx
    exact ⟨(hcomul.mp hx.comul_eq_tmul_self).ortho, hcounit.symm.trans hx.counit_eq_one⟩
  · rintro ⟨hortho, hsum⟩
    refine ⟨hcounit.trans hsum, hcomul.mpr ?_⟩
    classical
    have hcomplete : CompleteOrthogonalIdempotents
        (fun i : (b.repr x).support ↦ b.repr x i) := by
      apply CompleteOrthogonalIdempotents.iff_ortho_complete.mpr
      refine ⟨?_, ?_⟩
      · intro i j hij
        exact hortho (fun h ↦ hij (Subtype.ext h))
      · simpa only [Finset.sum_coe_sort, Finsupp.sum] using hsum
    refine ⟨?_, hortho⟩
    intro i
    by_cases hi : i ∈ (b.repr x).support
    · exact hcomplete.idem ⟨i, hi⟩
    · have hzero : b.repr x i = 0 := Finsupp.notMem_support_iff.mp hi
      simp only [hzero, isIdempotentElem_iff, zero_mul]

end GroupLike

end Module.Basis

/-- Every coordinate of a group-like element in a basis of group-like elements is
idempotent, without a finiteness assumption on the index type. -/
theorem IsGroupLikeElem.isIdempotentElem_repr [Coalgebra R C]
    (b : Module.Basis I R C) (hb : ∀ i, IsGroupLikeElem R (b i))
    {x : C} (hx : IsGroupLikeElem R x) (i : I) :
    IsIdempotentElem (b.repr x i) :=
  ((b.comul_eq_tmul_self_iff_orthogonalIdempotents_repr
    (fun j ↦ (hb j).comul_eq_tmul_self) x).mp hx.comul_eq_tmul_self).idem i
