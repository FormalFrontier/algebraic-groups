/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Submodule.Union
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.RingTheory.Ideal.Nonunits
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Spectrum.Maximal.Basic

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
  [Fintype ι] [DecidableEq ι]

/-- Replacing one vector of a finite basis by a vector having a unit coefficient
at that position remains linearly independent and spanning. -/
lemma isBasis_update (b : Basis ι A M) (i : ι) (x : M)
    (hx : IsUnit (b.repr x i)) :
    LinearIndependent A (Function.update b i x) ∧
      Submodule.span A (Set.range (Function.update b i x)) = ⊤ := by
  rw [is_basis_iff_det b, Basis.det_apply, b.toMatrix_update, b.toMatrix_self,
    ← Matrix.cramer_apply, Matrix.cramer_one]
  simpa using hx

/-- The basis obtained by replacing one basis vector by a vector having a unit
coefficient at that position. -/
noncomputable def update (b : Basis ι A M) (i : ι) (x : M)
    (hx : IsUnit (b.repr x i)) : Basis ι A M :=
  Basis.mk (isBasis_update b i x hx).1 (isBasis_update b i x hx).2.ge

@[simp]
lemma update_apply (b : Basis ι A M) (i : ι) (x : M)
    (hx : IsUnit (b.repr x i)) (j : ι) :
    update b i x hx j = Function.update b i x j := by
  apply Basis.mk_apply

@[simp]
lemma update_same (b : Basis ι A M) (i : ι) (x : M)
    (hx : IsUnit (b.repr x i)) : update b i x hx i = x := by
  simp

variable {K : Type*} [Field K] [Infinite K] [Algebra K A]
  [Module K M] [IsScalarTower K A M] [Finite (MaximalSpectrum A)]

/-- A base-field subspace spanning a finite free module over a semilocal
algebra contains a basis. -/
lemma exists_basis_subset (b : Basis ι A M) (W : Submodule K M)
    (hW : Submodule.span A (W : Set M) = ⊤) :
    ∃ b' : Basis ι A M, ∀ i, b' i ∈ W := by
  classical
  suffices h : ∀ s : Finset ι, ∃ b' : Basis ι A M, ∀ i ∈ s, b' i ∈ W by
    obtain ⟨b', hb'⟩ := h Finset.univ
    exact ⟨b', fun i ↦ hb' i (Finset.mem_univ i)⟩
  intro s
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨b, by simp⟩
  | @insert i s hi ih =>
      obtain ⟨b', hb'⟩ := ih
      obtain ⟨x, hxW, hx⟩ := LinearMap.exists_mem_isUnit_apply W hW (b'.coord i) (by
        intro a
        refine ⟨a • b' i, ?_⟩
        simp [Basis.coord_apply])
      have hx' : IsUnit (b'.repr x i) := by
        simpa [Basis.coord_apply] using hx
      refine ⟨b'.update i x hx', ?_⟩
      intro j hj
      by_cases hji : j = i
      · subst j
        simpa using hxW
      · rw [update_apply, update_of_ne hji]
        exact hb' j ((Finset.mem_insert.mp hj).resolve_left hji)

variable {R B L : Type*} [CommRing R] [IsLocalRing R]
  [Infinite (IsLocalRing.ResidueField R)] [CommRing B] [Algebra R B]
  [AddCommGroup L] [Module B L] [Module R L] [IsScalarTower R B L]
  [Finite (MaximalSpectrum B)]

/-- Local-base version of `exists_basis_subset`: a generating base submodule
contains a basis if the extended maximal ideal lies in the Jacobson radical. -/
lemma exists_basis_subset_of_le_jacobson (b : Basis ι B L) (W : Submodule R L)
    (hW : Submodule.span B (W : Set L) = ⊤)
    (hJ : Ideal.map (algebraMap R B) (IsLocalRing.maximalIdeal R) ≤
      (Ideal.jacobson (⊥ : Ideal B))) :
    ∃ b' : Basis ι B L, ∀ i, b' i ∈ W := by
  classical
  suffices h : ∀ s : Finset ι, ∃ b' : Basis ι B L, ∀ i ∈ s, b' i ∈ W by
    obtain ⟨b', hb'⟩ := h Finset.univ
    exact ⟨b', fun i ↦ hb' i (Finset.mem_univ i)⟩
  intro s
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨b, by simp⟩
  | @insert i s hi ih =>
      obtain ⟨b', hb'⟩ := ih
      obtain ⟨x, hxW, hx⟩ := LinearMap.exists_mem_isUnit_apply_of_le_jacobson
        W hW hJ (b'.coord i) (by
          intro a
          refine ⟨a • b' i, ?_⟩
          simp [Basis.coord_apply])
      have hx' : IsUnit (b'.repr x i) := by
        simpa [Basis.coord_apply] using hx
      refine ⟨b'.update i x hx', ?_⟩
      intro j hj
      by_cases hji : j = i
      · subst j
        simpa using hxW
      · rw [update_apply, update_of_ne hji]
        exact hb' j ((Finset.mem_insert.mp hj).resolve_left hji)

end Module.Basis
