/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.FieldTheory.TranscendentalSeparable
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import Mathlib.RingTheory.Smooth.Field

/-!
# Geometrically reduced field extensions

This file relates geometric reducedness to separable generation and formal smoothness for field
extensions of finite type. It also records that geometric reducedness over a field is preserved by
localization.

## Main results

- `Algebra.IsGeometricallyReduced.of_isLocalization`
- `Algebra.IsGeometricallyReduced.linearIndepOn_pow`
- `Algebra.IsSeparablyGenerated.of_isGeometricallyReduced`
- `Algebra.FormallySmooth.of_isGeometricallyReduced`
- `IsSepClosed.instInfinite`: a separably closed field is infinite
-/

public section

open scoped TensorProduct

noncomputable section

universe u v

namespace Algebra.IsGeometricallyReduced

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

/-- Geometric reducedness over a field is preserved by localization. -/
theorem of_isLocalization {A B : Type v} [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    (M : Submonoid A) [IsLocalization M B] [Algebra.IsGeometricallyReduced k A] :
    Algebra.IsGeometricallyReduced k B := by
  rw [Algebra.isGeometricallyReduced_field_iff]
  let E := AlgebraicClosure k
  let _ : Algebra (E ⊗[k] A) (E ⊗[k] B) :=
    (Algebra.TensorProduct.map (AlgHom.id k E) (IsScalarTower.toAlgHom k A B)).toAlgebra
  have _ : IsScalarTower E (E ⊗[k] A) (E ⊗[k] B) :=
    .of_algebraMap_eq <| by intro; simp [RingHom.algebraMap_toAlgebra]
  have _ : IsLocalization
      (M.map (Algebra.TensorProduct.includeRight (R := k) (A := E))) (E ⊗[k] B) :=
    IsLocalization.tensorProduct_tensorProduct_right k E M B
      (by ext; simp [RingHom.algebraMap_toAlgebra])
  exact isReduced_localizationPreserves
    (M.map (Algebra.TensorProduct.includeRight (R := k) (A := E))) (E ⊗[k] B) inferInstance

/-- A linearly independent family in a geometrically reduced field extension remains linearly
independent after taking `p`th powers in positive characteristic. -/
theorem linearIndepOn_pow (p : ℕ) [hp : Fact p.Prime] [CharP k p]
    [Algebra.IsGeometricallyReduced k K]
    {s : Set K} (hs : LinearIndepOn k _root_.id s) :
    LinearIndepOn k (fun x : K ↦ x ^ p) s := by
  let E := AlgebraicClosure k
  let _ : CharP K p :=
    CharP.of_ringHom_of_ne_zero (algebraMap k K) p hp.out.ne_zero
  have _ : IsReduced (E ⊗[k] K) :=
    (Algebra.isGeometricallyReduced_field_iff k K).mp inferInstance
  have _ : Nontrivial (E ⊗[k] K) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left k E K
      (algebraMap k K).injective
  have _ : ExpChar (E ⊗[k] K) p :=
    expChar_of_injective_algebraMap (algebraMap E (E ⊗[k] K)).injective p
  have hsE : LinearIndepOn E (fun x : K ↦ (1 : E) ⊗ₜ[k] x) s := by
    change LinearIndependent E (fun x : ↥s ↦ (1 : E) ⊗ₜ[k] (x : K))
    let b := Module.Basis.extend hs
    let f : ↥s → ↥(hs.extend (Set.subset_univ _)) :=
      fun x ↦ ⟨x, hs.subset_extend _ x.property⟩
    have hf : Function.Injective f := fun _ _ h ↦ Subtype.ext congr($h.1)
    have hb := (b.baseChange E).linearIndependent.comp f hf
    convert hb using 1
    funext x
    simp [b, f, Module.Basis.baseChange_apply]
  have tmul_pow_aux (n : ℕ) (a : E) (x : K) :
      (a ⊗ₜ[k] x : E ⊗[k] K) ^ n = (a ^ n) ⊗ₜ[k] (x ^ n) := by
    induction n with
    | zero => rw [pow_zero, pow_zero, pow_zero, Algebra.TensorProduct.one_def]
    | succ n ih =>
        rw [pow_succ, ih, pow_succ, pow_succ, Algebra.TensorProduct.tmul_mul_tmul]
  have tmul_pow (a : E) (x : K) :
      (a ⊗ₜ[k] x : E ⊗[k] K) ^ p = (a ^ p) ⊗ₜ[k] (x ^ p) :=
    tmul_pow_aux p a x
  have algebraMap_tmul (a : k) (x : K) :
      (algebraMap k E a) ⊗ₜ[k] x = (1 : E) ⊗ₜ[k] (a • x) := by
    conv_lhs => rw [← mul_one (algebraMap k E a), ← Algebra.smul_def]
    rw [TensorProduct.smul_tmul]
  rw [linearIndepOn_iff]
  intro l hl hrel
  rw [Finsupp.linearCombination_apply] at hrel
  let root : k → E := fun a ↦ Classical.choose
    (IsAlgClosed.exists_pow_nat_eq (algebraMap k E a) hp.out.pos)
  have root_pow (a : k) : root a ^ p = algebraMap k E a :=
    Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (algebraMap k E a) hp.out.pos)
  have root_zero : root 0 = 0 := by
    apply eq_zero_of_pow_eq_zero (n := p)
    rw [root_pow, map_zero]
  let lE : K →₀ E := l.mapRange root root_zero
  have hlE : lE ∈ Finsupp.supported E E s := by
    rw [Finsupp.mem_supported] at hl ⊢
    intro x hx
    apply hl
    have hx' : x ∈ lE.support := hx
    have : x ∈ l.support :=
      Finsupp.support_mapRange (f := root) (hf := root_zero) (g := l) hx'
    simpa using this
  have hrel' : (∑ a ∈ l.support, l a • a ^ p) = 0 := by
    simpa only [Finsupp.sum] using hrel
  have hcombE :
      Finsupp.linearCombination E (fun x : K ↦ (1 : E) ⊗ₜ[k] x) lE = 0 := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index]
    · apply eq_zero_of_pow_eq_zero (n := p)
      rw [Finsupp.sum, sum_pow_char p]
      simp_rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, tmul_pow, root_pow,
        algebraMap_tmul]
      rw [← TensorProduct.tmul_sum, hrel']
      simp
    · intro
      simp
  have hlE_zero : lE = 0 := (linearIndepOn_iff.mp hsE) lE hlE hcombE
  ext x
  change l x = 0
  apply (algebraMap k E).injective
  rw [map_zero, ← root_pow]
  have : root (l x) = 0 := by
    have := DFunLike.congr_fun hlE_zero x
    simpa [lE] using this
  simp [this, hp.out.ne_zero]

end Algebra.IsGeometricallyReduced

namespace Algebra

variable (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]

/-- A geometrically reduced field extension of finite type is separably generated. -/
instance (priority := low) IsSeparablyGenerated.of_isGeometricallyReduced
    [Algebra.IsGeometricallyReduced k K] [Algebra.EssFiniteType k K] :
    Algebra.IsSeparablyGenerated k K := by
  obtain _ | ⟨p, hprime, _⟩ := CharP.exists' k
  · obtain ⟨s, hs, hsep⟩ :=
      exists_isTranscendenceBasis_and_isSeparable_of_perfectField k K
    exact ⟨s, hs, hsep⟩
  · let _ : ExpChar k p := .prime hprime.out
    let _ : CharP K p :=
      CharP.of_ringHom_of_ne_zero (algebraMap k K) p hprime.out.ne_zero
    obtain ⟨s, hs, hsep⟩ :=
      exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteType
        p hprime.out fun _ hs ↦
          Algebra.IsGeometricallyReduced.linearIndepOn_pow (k := k) (K := K) p hs
    exact ⟨s, hs, hsep⟩

/-- A geometrically reduced field extension of finite type is formally smooth. -/
instance (priority := low) FormallySmooth.of_isGeometricallyReduced
    [Algebra.IsGeometricallyReduced k K] [Algebra.EssFiniteType k K] :
    Algebra.FormallySmooth k K := by
  obtain ⟨s, hs, hsep⟩ := IsSeparablyGenerated.isSeparable (k := k) (K := K)
  let _ : Algebra.IsSeparable
      (IntermediateField.adjoin k (Set.range ((↑) : s → K))) K := by
    convert hsep <;> simp
  exact .of_algebraicIndependent_of_isSeparable hs.1

end Algebra

namespace IsSepClosed

/-- A separably closed field is infinite. -/
instance (priority := 510) instInfinite {K : Type*} [Field K] [IsSepClosed K] : Infinite K := by
  apply Infinite.of_not_fintype
  intro hfin
  set n := Fintype.card K
  set f := (Polynomial.X : Polynomial K) ^ (n + 1) - 1
  have hfsep : f.Separable :=
    Polynomial.separable_X_pow_sub_C 1 (by simp [n]) one_ne_zero
  apply Nat.not_succ_le_self (Fintype.card K)
  have hroot : n.succ = Fintype.card (f.rootSet K) := by
    rw [Polynomial.card_rootSet_eq_natDegree hfsep (IsSepClosed.splits_domain f hfsep)]
    unfold f
    rw [← Polynomial.C_1, Polynomial.natDegree_X_pow_sub_C]
  rw [hroot]
  exact Fintype.card_le_of_injective _ Subtype.coe_injective

end IsSepClosed
