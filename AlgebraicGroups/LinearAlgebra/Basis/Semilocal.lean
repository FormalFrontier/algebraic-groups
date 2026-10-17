/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Submodule.Union
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.RingTheory.Ideal.Nonunits
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Spectrum.Maximal.Basic

/-!
# Basis selection over semilocal algebras

A spanning subspace over an infinite field contains a basis of a finite free
module over a semilocal algebra. For a local base ring with infinite residue
field, the same selection works when the extended maximal ideal lies in the
Jacobson radical. The finite index set may be empty.

The selection first avoids finitely many proper kernels over a field, then
finds unit coordinates modulo each maximal ideal. A unit coordinate permits
a basis update, even for an infinite basis: linear independence follows from
Mathlib's replacement lemma, and spanning follows by separating the pivot
from the finitely supported coordinates and multiplying by its unit inverse.

## References

* The Stacks Project, Lemma 10.78.8
  ([tag 03C1](https://stacks.math.columbia.edu/tag/03C1)), proves the
  local-ring version by reducing to the infinite residue field and selecting
  a basis over a semilocal algebra. The field version below uses the same
  finite-avoidance idea.
* Mathlib, `Mathlib.Algebra.Module.Submodule.Union`
  (`Submodule.exists_forall_notMem_of_forall_ne_top`),
  `Mathlib.RingTheory.Ideal.Nonunits`, `Mathlib.RingTheory.Jacobson.Ideal`,
  and `Mathlib.LinearAlgebra.LinearIndependent.Lemmas`
  (`LinearIndependent.update`) provide the avoidance, unit, Jacobson, and
  independence ingredients. `Finsupp.single_add_erase` and the linear-combination
  API provide the finite-support spanning argument for arbitrary-index updates.
  The update-coordinate proofs use Mathlib's `Basis.ext` on coordinate linear
  maps, following the inverse-unit coordinate approach of `Basis.coord_unitsSMul`.
-/

@[expose] public section

open Function

namespace LinearMap

variable {ι K M : Type*} [Field K] [Infinite K]
  [AddCommGroup M] [Module K M]
  {N : ι → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module K (N i)]

/-- A finite family of nonzero linear maps over an infinite field is
simultaneously nonzero at some vector. -/
lemma exists_forall_map_ne_zero [Finite ι] (f : (i : ι) → M →ₗ[K] N i)
    (hf : ∀ i, f i ≠ 0) : ∃ x, ∀ i, f i x ≠ 0 := by
  have hker : ∀ i, LinearMap.ker (f i) ≠ ⊤ := fun i h ↦ hf i (LinearMap.ker_eq_top.mp h)
  obtain ⟨x, hx⟩ :=
    Submodule.exists_forall_notMem_of_forall_ne_top (fun i ↦ LinearMap.ker (f i)) hker
  exact ⟨x, fun i hi ↦ hx i (LinearMap.mem_ker.mpr hi)⟩

variable {A : Type*} [CommRing A] [Algebra K A]
  [Module A M] [IsScalarTower K A M]
  {P : ι → Type*} [∀ i, AddCommGroup (P i)]
  [∀ i, Module A (P i)] [∀ i, Module K (P i)]
  [∀ i, IsScalarTower K A (P i)]

/-- If a `K`-subspace spans an `A`-module, a finite family of nonzero
`A`-linear maps is simultaneously nonzero on some element of that subspace. -/
lemma exists_mem_forall_map_ne_zero [Finite ι] (W : Submodule K M)
    (hW : Submodule.span A (W : Set M) = ⊤) (f : (i : ι) → M →ₗ[A] P i)
    (hf : ∀ i, f i ≠ 0) : ∃ x ∈ W, ∀ i, f i x ≠ 0 := by
  let g (i : ι) : W →ₗ[K] P i := (f i).restrictScalars K ∘ₗ W.subtype
  have hg : ∀ i, g i ≠ 0 := by
    intro i hgi
    apply hf i
    apply LinearMap.ker_eq_top.mp
    rw [← top_le_iff, ← hW]
    refine Submodule.span_le.mpr fun x hx ↦ LinearMap.mem_ker.mpr ?_
    have := LinearMap.congr_fun hgi ⟨x, hx⟩
    simpa [g] using this
  obtain ⟨x, hx⟩ := exists_forall_map_ne_zero g hg
  exact ⟨x, x.property, fun i ↦ hx i⟩

/-- Over a semilocal algebra of an infinite field, a base subspace that spans
an `A`-module contains an element on which any surjective `A`-linear
functional takes a unit value. -/
lemma exists_mem_isUnit_apply [Finite (MaximalSpectrum A)] (W : Submodule K M)
    (hW : Submodule.span A (W : Set M) = ⊤) (f : M →ₗ[A] A)
    (hf : Function.Surjective f) : ∃ x ∈ W, IsUnit (f x) := by
  let g (P : MaximalSpectrum A) : M →ₗ[A] A ⧸ P.asIdeal := P.asIdeal.mkQ.comp f
  have hg : ∀ P, g P ≠ 0 := by
    intro P hP
    obtain ⟨x, hx⟩ := hf 1
    have := LinearMap.congr_fun hP x
    simp [g, hx] at this
  obtain ⟨x, hxW, hx⟩ := exists_mem_forall_map_ne_zero W hW g hg
  refine ⟨x, hxW, ?_⟩
  by_contra hunit
  obtain ⟨I, hI, hxI⟩ := exists_max_ideal_of_mem_nonunits hunit
  exact hx ⟨I, hI⟩ (Ideal.Quotient.eq_zero_iff_mem.mpr hxI)

variable {R : Type*} [CommRing R] [IsLocalRing R]
  [Infinite (IsLocalRing.ResidueField R)]
  {B : Type*} [CommRing B] [Algebra R B]
  {L : Type*} [AddCommGroup L] [Module B L] [Module R L]
  [IsScalarTower R B L]

/-- Local-base version of `exists_mem_isUnit_apply`: a generating base
submodule contains a vector on which a surjective functional takes a unit
value, provided the extended maximal ideal lies in the Jacobson radical. -/
lemma exists_mem_isUnit_apply_of_le_jacobson [Finite (MaximalSpectrum B)]
    (W : Submodule R L) (hW : Submodule.span B (W : Set L) = ⊤)
    (hJ : Ideal.map (algebraMap R B) (IsLocalRing.maximalIdeal R) ≤
      (Ideal.jacobson (⊥ : Ideal B)))
    (f : L →ₗ[B] B) (hf : Function.Surjective f) : ∃ x ∈ W, IsUnit (f x) := by
  classical
  let _ := Fintype.ofFinite (MaximalSpectrum B)
  let g (P : MaximalSpectrum B) : L →ₗ[B] B ⧸ P.asIdeal := P.asIdeal.mkQ.comp f
  have hg : ∀ P, g P ≠ 0 := by
    intro P hP
    obtain ⟨x, hx⟩ := hf 1
    have := LinearMap.congr_fun hP x
    simp [g, hx] at this
  have hpoint : ∀ P, ∃ x ∈ W, g P x ≠ 0 := by
    intro P
    by_contra! h
    apply hg P
    apply LinearMap.ker_eq_top.mp
    rw [← top_le_iff, ← hW]
    refine Submodule.span_le.mpr fun x hx ↦ LinearMap.mem_ker.mpr ?_
    exact h x hx
  choose x hxW hx using hpoint
  let q (P : MaximalSpectrum B) : B →+* B ⧸ P.asIdeal := Ideal.Quotient.mk P.asIdeal
  have hmax (P : MaximalSpectrum B) :
      Ideal.map (algebraMap R B) (IsLocalRing.maximalIdeal R) ≤ P.asIdeal :=
    hJ.trans (sInf_le ⟨bot_le, P.isMaximal⟩)
  have hker (P : MaximalSpectrum B) : ∀ r ∈ IsLocalRing.maximalIdeal R,
      (q P).comp (algebraMap R B) r = 0 := by
    intro r hr
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact hmax P (Ideal.mem_map_of_mem (algebraMap R B) hr)
  let σ (P : MaximalSpectrum B) : IsLocalRing.ResidueField R →+* B ⧸ P.asIdeal :=
    Ideal.Quotient.lift (IsLocalRing.maximalIdeal R)
      ((q P).comp (algebraMap R B)) (hker P)
  have hσ (P : MaximalSpectrum B) (r : R) :
      σ P (IsLocalRing.residue R r) =
        Ideal.Quotient.mk P.asIdeal (algebraMap R B r) := by
    set_option backward.isDefEq.respectTransparency false in
      rfl
  let _ (P : MaximalSpectrum B) : Algebra (IsLocalRing.ResidueField R) (B ⧸ P.asIdeal) :=
    (σ P).toAlgebra
  let ℓ (P : MaximalSpectrum B) :
      (MaximalSpectrum B → IsLocalRing.ResidueField R) →ₗ[IsLocalRing.ResidueField R]
        B ⧸ P.asIdeal :=
    { toFun := fun c ↦ ∑ Q, algebraMap (IsLocalRing.ResidueField R) (B ⧸ P.asIdeal) (c Q) * g P (x Q)
      map_add' := by
        intro c d
        simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro a c
        change (∑ Q, algebraMap (IsLocalRing.ResidueField R) (B ⧸ P.asIdeal)
            (a * c Q) * g P (x Q)) =
          algebraMap (IsLocalRing.ResidueField R) (B ⧸ P.asIdeal) a *
            ∑ Q, algebraMap (IsLocalRing.ResidueField R) (B ⧸ P.asIdeal)
              (c Q) * g P (x Q)
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro Q _
        rw [map_mul, mul_assoc] }
  have hℓ : ∀ P, ℓ P ≠ 0 := by
    intro P hP
    have := LinearMap.congr_fun hP
      (Pi.single (M := fun _ : MaximalSpectrum B ↦ IsLocalRing.ResidueField R)
        P (1 : IsLocalRing.ResidueField R))
    have heval :
        ℓ P (Pi.single (M := fun _ : MaximalSpectrum B ↦ IsLocalRing.ResidueField R)
          P (1 : IsLocalRing.ResidueField R)) = g P (x P) := by
      change (∑ Q, algebraMap (IsLocalRing.ResidueField R) (B ⧸ P.asIdeal)
          (Pi.single (M := fun _ : MaximalSpectrum B ↦ IsLocalRing.ResidueField R)
            P (1 : IsLocalRing.ResidueField R) Q) * g P (x Q)) =
        g P (x P)
      rw [Finset.sum_eq_single P]
      · simp
      · intro Q _ hQP
        simp [hQP]
      · intro hP'
        exact (hP' (Finset.mem_univ P)).elim
    rw [heval] at this
    exact hx P this
  obtain ⟨c, hc⟩ := exists_forall_map_ne_zero ℓ hℓ
  choose r hr using fun P ↦ IsLocalRing.residue_surjective (c P)
  let y : L := ∑ P, r P • x P
  have hyW : y ∈ W := by
    apply Submodule.sum_mem
    intro P _
    exact W.smul_mem (r P) (hxW P)
  refine ⟨y, hyW, ?_⟩
  by_contra hy
  obtain ⟨I, hI, hyI⟩ := exists_max_ideal_of_mem_nonunits hy
  let P : MaximalSpectrum B := ⟨I, hI⟩
  apply hc P
  rw [show ℓ P c = g P y by
    simp only [ℓ, y, g, map_sum]
    apply Finset.sum_congr rfl
    intro Q _
    rw [← hr Q]
    change algebraMap (IsLocalRing.ResidueField R) (B ⧸ P.asIdeal)
        (IsLocalRing.residue R (r Q)) *
          Ideal.Quotient.mk P.asIdeal (f (x Q)) =
      Ideal.Quotient.mk P.asIdeal (f (r Q • x Q))
    rw [RingHom.algebraMap_toAlgebra, hσ]
    rw [← map_mul, ← Algebra.smul_def, f.map_smul_of_tower]]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hyI

end LinearMap

namespace Module.Basis

variable {ι A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

/-- Replacing one vector of a basis by a vector having a unit coefficient
at that position remains linearly independent and spanning. -/
lemma isBasis_update [DecidableEq ι] (b : Basis ι A M) (i : ι) (x : M)
    (hx : IsUnit (b.repr x i)) :
    LinearIndependent A (Function.update b i x) ∧
      Submodule.span A (Set.range (Function.update b i x)) = ⊤ := by
  refine ⟨b.linearIndependent.update i x ?_, ?_⟩
  · refine ⟨1, one_mem _, b.repr x, hx.mem_nonZeroDivisors, ?_⟩
    simpa only [one_smul] using (b.linearCombination_repr x).symm
  · let S := Submodule.span A (Set.range (Function.update b i x))
    have hxS : x ∈ S := by
      apply Submodule.subset_span
      exact ⟨i, by simp⟩
    have hbS (j : ι) (hji : j ≠ i) : b j ∈ S := by
      apply Submodule.subset_span
      exact ⟨j, by simp only [Function.update_of_ne hji]⟩
    have hy : Finsupp.linearCombination A b ((b.repr x).erase i) ∈ S := by
      rw [Finsupp.linearCombination_apply, Finsupp.sum]
      apply S.sum_smul_mem
      intro j hj
      apply hbS j
      exact Finset.ne_of_mem_erase (by simpa only [Finsupp.support_erase] using hj)
    have hdecomp : (b.repr x i) • b i +
        Finsupp.linearCombination A b ((b.repr x).erase i) = x := by
      simpa only [map_add, Finsupp.linearCombination_single, b.linearCombination_repr] using
        congrArg (Finsupp.linearCombination A b) (Finsupp.single_add_erase i (b.repr x))
    have hmul : (b.repr x i) • b i ∈ S := by
      rw [eq_sub_iff_add_eq.mpr hdecomp]
      exact S.sub_mem hxS hy
    have hbi : b i ∈ S := (S.smul_mem_iff_of_isUnit hx).mp hmul
    exact (Submodule.eq_top_iff_forall_basis_mem b).2 fun j ↦ by
      by_cases hji : j = i
      · simpa only [hji] using hbi
      · exact hbS j hji

/-- The basis obtained by replacing one basis vector by a vector having a unit
coefficient at that position. -/
noncomputable def update [DecidableEq ι] (b : Basis ι A M) (i : ι) (x : M)
    (hx : IsUnit (b.repr x i)) : Basis ι A M :=
  Basis.mk (isBasis_update b i x hx).1 (isBasis_update b i x hx).2.ge

@[simp]
lemma update_apply [DecidableEq ι] (b : Basis ι A M) (i : ι) (x : M)
    (hx : IsUnit (b.repr x i)) (j : ι) :
    update b i x hx j = Function.update b i x j := by
  apply Basis.mk_apply

@[simp]
lemma update_same [DecidableEq ι] (b : Basis ι A M) (i : ι) (x : M)
    (hx : IsUnit (b.repr x i)) : update b i x hx i = x := by
  simp

/-- The pivot coordinate after a unit-pivot basis update is multiplied by the
inverse of the pivot unit. No finiteness of the index type is needed. -/
lemma repr_update_same [DecidableEq ι] (b : Basis ι A M) (i : ι) (x y : M)
    (hx : IsUnit (b.repr x i)) :
    (b.update i x hx).repr y i = (↑(hx.unit⁻¹) : A) * b.repr y i := by
  have hmul : (↑(hx.unit⁻¹) : A) * b.repr x i = 1 := by
    simpa only [hx.unit_spec] using (Units.inv_mul hx.unit)
  have hcoord : (b.update i x hx).coord i = (↑(hx.unit⁻¹) : A) • b.coord i := by
    apply (b.update i x hx).ext
    intro k
    simp only [coord_apply, LinearMap.smul_apply, smul_eq_mul, repr_self]
    by_cases hki : k = i
    · subst k
      simpa only [update_same, Finsupp.single_eq_same] using hmul.symm
    · simp only [update_apply, Function.update_of_ne hki, repr_self,
        Finsupp.single_apply, if_neg hki, mul_zero]
  simpa only [coord_apply, LinearMap.smul_apply, smul_eq_mul] using
    congrArg (fun f : M →ₗ[A] A ↦ f y) hcoord

/-- Away from the pivot, the new coordinate subtracts the old pivot coordinate
multiplied by the inverse pivot unit and the replacement vector's coordinate. -/
lemma repr_update_of_ne [DecidableEq ι] (b : Basis ι A M) (i : ι) (x y : M)
    (hx : IsUnit (b.repr x i)) (j : ι) (hji : j ≠ i) :
    (b.update i x hx).repr y j =
      b.repr y j - b.repr y i * (↑(hx.unit⁻¹) : A) * b.repr x j := by
  have hmul : (↑(hx.unit⁻¹) : A) * b.repr x i = 1 := by
    simpa only [hx.unit_spec] using (Units.inv_mul hx.unit)
  have hcoord : (b.update i x hx).coord j =
      b.coord j - ((↑(hx.unit⁻¹) : A) * b.repr x j) • b.coord i := by
    apply (b.update i x hx).ext
    intro k
    simp only [coord_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul, repr_self]
    by_cases hki : k = i
    · subst k
      simp only [update_same, Finsupp.single_apply, if_neg (Ne.symm hji)]
      rw [mul_right_comm _ (b.repr x j), hmul, one_mul, sub_self]
    · simp only [update_apply, Function.update_of_ne hki, repr_self,
        Finsupp.single_apply, if_neg hki, mul_zero, sub_zero]
  calc
    (b.update i x hx).repr y j =
        b.repr y j - ((↑(hx.unit⁻¹) : A) * b.repr x j) * b.repr y i := by
      simpa only [coord_apply, LinearMap.sub_apply, LinearMap.smul_apply,
        smul_eq_mul] using congrArg (fun f : M →ₗ[A] A ↦ f y) hcoord
    _ = b.repr y j - b.repr y i * (↑(hx.unit⁻¹) : A) * b.repr x j := by
      rw [mul_comm _ (b.repr y i), ← mul_assoc]

private lemma exists_basis_subset_finset_aux (b : Basis ι A M) (S : Set M)
    (hselect : ∀ f : M →ₗ[A] A, Function.Surjective f → ∃ x ∈ S, IsUnit (f x))
    (s : Finset ι) :
    ∃ b' : Basis ι A M, (∀ i ∈ s, b' i ∈ S) ∧ ∀ i ∉ s, b' i = b i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨b, by simp, fun _ _ ↦ rfl⟩
  | @insert i s _ ih =>
      obtain ⟨c, hcS, hcb⟩ := ih
      obtain ⟨x, hxS, hx⟩ := hselect (c.coord i) (by
        intro a
        refine ⟨a • c i, ?_⟩
        simp [Basis.coord_apply])
      have hx' : IsUnit (c.repr x i) := by
        simpa [Basis.coord_apply] using hx
      refine ⟨c.update i x hx', ?_, ?_⟩
      · intro j hj
        by_cases hji : j = i
        · subst j
          simpa only [update_same] using hxS
        · rw [update_apply, Function.update_of_ne hji]
          exact hcS j ((Finset.mem_insert.mp hj).resolve_left hji)
      · intro j hj
        have hji : j ≠ i := fun hji ↦ hj (Finset.mem_insert.mpr (Or.inl hji))
        have hjs : j ∉ s := fun hjs ↦ hj (Finset.mem_insert_of_mem hjs)
        rw [update_apply, Function.update_of_ne hji]
        exact hcb j hjs

variable {K : Type*} [Field K] [Infinite K] [Algebra K A]
  [Module K M] [IsScalarTower K A M] [Finite (MaximalSpectrum A)]

/-- Over a semilocal algebra of an infinite field, a spanning base subspace
contains the entries on any finite set of indices of a new basis that agrees
with the given basis at every other index. -/
lemma exists_basis_subset_finset (b : Basis ι A M) (W : Submodule K M)
    (hW : Submodule.span A (W : Set M) = ⊤) (s : Finset ι) :
    ∃ b' : Basis ι A M, (∀ i ∈ s, b' i ∈ W) ∧ ∀ i ∉ s, b' i = b i := by
  exact exists_basis_subset_finset_aux b (W : Set M)
    (fun f hf ↦ LinearMap.exists_mem_isUnit_apply W hW f hf) s

/-- A base-field subspace spanning a finite free module over a semilocal
algebra contains a basis. This is a field-base analogue of Stacks Project,
Lemma 10.78.8 (tag 03C1). -/
lemma exists_basis_subset [Finite ι] (b : Basis ι A M) (W : Submodule K M)
    (hW : Submodule.span A (W : Set M) = ⊤) :
    ∃ b' : Basis ι A M, ∀ i, b' i ∈ W := by
  classical
  let _ := Fintype.ofFinite ι
  obtain ⟨b', hb', _⟩ := exists_basis_subset_finset b W hW Finset.univ
  exact ⟨b', fun i ↦ hb' i (Finset.mem_univ i)⟩

variable {R B L : Type*} [CommRing R] [IsLocalRing R]
  [Infinite (IsLocalRing.ResidueField R)] [CommRing B] [Algebra R B]
  [AddCommGroup L] [Module B L] [Module R L] [IsScalarTower R B L]
  [Finite (MaximalSpectrum B)]

/-- Over a semilocal algebra of a local ring with infinite residue field, a
generating base submodule contains the entries on any finite set of indices of
a new basis agreeing with the given basis elsewhere, provided the extended
maximal ideal lies in the Jacobson radical. -/
lemma exists_basis_subset_finset_of_le_jacobson (b : Basis ι B L) (W : Submodule R L)
    (hW : Submodule.span B (W : Set L) = ⊤)
    (hJ : Ideal.map (algebraMap R B) (IsLocalRing.maximalIdeal R) ≤
      (Ideal.jacobson (⊥ : Ideal B))) (s : Finset ι) :
    ∃ b' : Basis ι B L, (∀ i ∈ s, b' i ∈ W) ∧ ∀ i ∉ s, b' i = b i := by
  exact exists_basis_subset_finset_aux b (W : Set L)
    (fun f hf ↦ LinearMap.exists_mem_isUnit_apply_of_le_jacobson W hW hJ f hf) s

/-- Local-base version of `exists_basis_subset`: a generating base submodule
contains a basis if the extended maximal ideal lies in the Jacobson radical.
This is the basis-selection conclusion of Stacks Project, Lemma 10.78.8
(tag 03C1). -/
lemma exists_basis_subset_of_le_jacobson [Finite ι] (b : Basis ι B L) (W : Submodule R L)
    (hW : Submodule.span B (W : Set L) = ⊤)
    (hJ : Ideal.map (algebraMap R B) (IsLocalRing.maximalIdeal R) ≤
      (Ideal.jacobson (⊥ : Ideal B))) :
    ∃ b' : Basis ι B L, ∀ i, b' i ∈ W := by
  classical
  let _ := Fintype.ofFinite ι
  obtain ⟨b', hb', _⟩ := exists_basis_subset_finset_of_le_jacobson b W hW hJ Finset.univ
  exact ⟨b', fun i ↦ hb' i (Finset.mem_univ i)⟩

end Module.Basis
