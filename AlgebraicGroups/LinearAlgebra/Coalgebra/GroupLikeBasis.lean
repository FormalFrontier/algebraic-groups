/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.LinearAlgebra.Coalgebra.GroupLikeCoordinates
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.Coalgebra.GroupLike
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Connected.Basic

/-!
# Group-like bases over connected scalars

A given group-like basis over a nontrivial commutative semiring with preconnected
prime spectrum exhausts the group-like elements, with a unique basis index for
each element. The scalar, coalgebra and index types have independent universes;
the index type need not be finite or inhabited.

## Implementation notes

The predicate `IsGroupLikeElem` uses a full `Coalgebra` in Mathlib's interface.
No multiplication on the coalgebra is required. A supplied basis is part of the
hypotheses, rather than a conclusion about independence in arbitrary coalgebras.

## References

The basis and group-like interfaces are from Mathlib's
`Mathlib.LinearAlgebra.Basis.Defs` and `Mathlib.RingTheory.Coalgebra.GroupLike`.
The connectedness hypothesis uses the topology of
`Mathlib.RingTheory.Spectrum.Prime.Topology`.
-/

@[expose] public section

open scoped BigOperators

universe u v w

/-- A complemented scalar is zero or one when the prime spectrum is preconnected. -/
private theorem eq_zero_or_one_of_mul_add_of_preconnected_spectrum
    {R : Type u} [CommSemiring R] [PreconnectedSpace (PrimeSpectrum R)]
    (a b : R) (hab : a * b = 0) (hs : a + b = 1) : a = 0 ∨ a = 1 := by
  let e : {p : R × R // p.1 * p.2 = 0 ∧ p.1 + p.2 = 1} := ⟨(a, b), hab, hs⟩
  let E := PrimeSpectrum.mulZeroAddOneEquivClopens (R := R)
  rcases isClopen_iff.mp (E e).isClopen with h | h
  · left
    have he : E e = ⊥ := TopologicalSpace.Clopens.ext h
    have hp : e = ⊥ := E.injective (he.trans E.map_bot.symm)
    exact congrArg (Prod.fst ∘ Subtype.val) hp
  · right
    have he : E e = ⊤ := TopologicalSpace.Clopens.ext h
    have hp : e = ⊤ := E.injective (he.trans E.map_top.symm)
    exact congrArg (Prod.fst ∘ Subtype.val) hp

/-- Every coefficient of a normalized orthogonal family has a complement. -/
private theorem exists_mul_eq_zero_add_eq_one
    {R : Type u} {I : Type w} [Semiring R]
    (a : I →₀ R) (hp : Pairwise (fun i j : I => a i * a j = 0))
    (hs : a.sum (fun _ r => r) = 1) (i : I) :
    ∃ c : R, a i * c = 0 ∧ a i + c = 1 := by
  classical
  change (∑ j ∈ a.support, a j) = 1 at hs
  refine ⟨∑ j ∈ a.support.erase i, a j, ?_, ?_⟩
  · rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun j hj =>
      hp (Ne.symm (Finset.ne_of_mem_erase hj))
  · by_cases hi : i ∈ a.support
    · exact (Finset.add_sum_erase a.support (fun j => a j) hi).trans hs
    · rw [Finsupp.notMem_support_iff.mp hi, zero_add,
        Finset.erase_eq_of_notMem hi]
      exact hs

/-- A normalized family over a nontrivial semiring has a nonzero coefficient. -/
private theorem exists_apply_ne_zero_of_sum_eq_one
    {R : Type u} {I : Type w} [Semiring R] [Nontrivial R]
    (a : I →₀ R) (hs : a.sum (fun _ r => r) = 1) :
    ∃ i : I, a i ≠ 0 := by
  have hsum : (∑ j ∈ a.support, a j) ≠ 0 := by
    change a.sum (fun _ r => r) ≠ 0
    rw [hs]
    exact one_ne_zero
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  exact ⟨i, hi⟩

/-- An orthogonal family with a coefficient equal to one is the corresponding single. -/
private theorem eq_single_of_apply_eq_one
    {R : Type u} {I : Type w} [MulZeroOneClass R]
    (a : I →₀ R) (hp : Pairwise (fun i j : I => a i * a j = 0))
    {i : I} (hi : a i = 1) : a = Finsupp.single i 1 := by
  classical
  apply Finsupp.eq_single_iff.mpr
  refine ⟨?_, hi⟩
  intro j hj
  apply Finset.mem_singleton.mpr
  by_contra hji
  have hz : a j = 0 := by
    simpa only [hi, mul_one] using (hp hji : a j * a i = 0)
  exact (Finsupp.mem_support_iff.mp hj) hz

/-- A normalized orthogonal family over connected scalars is a unique single-one vector. -/
private theorem existsUnique_eq_single_of_preconnected_spectrum
    {R : Type u} {I : Type w} [CommSemiring R] [Nontrivial R]
    [PreconnectedSpace (PrimeSpectrum R)]
    (a : I →₀ R) (hp : Pairwise (fun i j : I => a i * a j = 0))
    (hs : a.sum (fun _ r => r) = 1) :
    ∃! i : I, a = Finsupp.single i 1 := by
  obtain ⟨i, hi⟩ := exists_apply_ne_zero_of_sum_eq_one a hs
  obtain ⟨c, hmul, hadd⟩ := exists_mul_eq_zero_add_eq_one a hp hs i
  have hi_one : a i = 1 :=
    (eq_zero_or_one_of_mul_add_of_preconnected_spectrum (a i) c hmul hadd).resolve_left hi
  have hsingle : a = Finsupp.single i 1 := eq_single_of_apply_eq_one a hp hi_one
  refine ⟨i, hsingle, ?_⟩
  intro j hj
  exact Finsupp.single_left_injective (one_ne_zero : (1 : R) ≠ 0)
    (hj.symm.trans hsingle)

namespace Module.Basis

/-- Over a nontrivial commutative semiring with preconnected prime spectrum,
every group-like element equals the vector at a unique index of a given
group-like basis. Nontriviality excludes coincident basis values over the zero
semiring; no finiteness or inhabitedness of the index type is required. -/
theorem existsUnique_eq_of_isGroupLikeElem
    {R : Type u} {C : Type v} {I : Type w}
    [CommSemiring R] [Nontrivial R] [PreconnectedSpace (PrimeSpectrum R)]
    [AddCommMonoid C] [Module R C] [Coalgebra R C]
    (b : Module.Basis I R C) (hb : ∀ i : I, IsGroupLikeElem R (b i))
    (x : C) (hx : IsGroupLikeElem R x) :
    ∃! i : I, x = b i := by
  obtain ⟨hp, hs⟩ :=
    (b.isGroupLikeElem_iff_pairwise_mul_eq_zero_and_sum_eq_one hb x).mp hx
  obtain ⟨i, hi, huniq⟩ :=
    existsUnique_eq_single_of_preconnected_spectrum (b.repr x) hp hs
  refine ⟨i, b.repr.injective (hi.trans (b.repr_self i).symm), ?_⟩
  intro j hj
  exact huniq j ((congrArg b.repr hj).trans (b.repr_self j))

end Module.Basis
