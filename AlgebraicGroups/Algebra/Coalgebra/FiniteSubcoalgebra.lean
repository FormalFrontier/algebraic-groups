/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.Coefficients
public import AlgebraicGroups.Algebra.TensorProduct.Split
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Coalgebra.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Finite-dimensional subcoalgebra containment

The fundamental theorem of coalgebras over a field says that every finite subset
of a coalgebra is contained in a finite-dimensional subcoalgebra. We express
containment using a submodule `D` and the image of the tensor inclusion
`D ⊗ D → C ⊗ C`. Finiteness is module finite generation (`Submodule.FG`),
not finite generation of an algebra. No multiplication on `C` is required.

The finite right-coideal step works more generally over a commutative semiring
when the ambient coalgebra module is projective, with only an additive commutative
monoid structure. A global section of its canonical free presentation replaces
an ambient basis; no finite-generation assumption on the ambient module is needed.
Comultiplication lies in the image of the first-factor tensor inclusion for every
member of the resulting finitely generated submodule.
Over a field, the coefficients of a finite basis then produce two-factor
closure. The automatic basis and ambient coordinate extensions in this later
step are field-only. A right coideal alone need not have two-factor closure,
and finite tensor support alone does not give either closure. The counit takes
values in the scalar semiring, so it needs no additional closure condition.

## References

* M. E. Sweedler, *Hopf Algebras*, W. A. Benjamin, 1969, for the classical
  theorem and coefficient-coalgebra method (bibliographic credit).
* Mathlib's projective-module, coalgebra and tensor-product formalizations.
* Formal Frontier's projective-coalgebra formalization, for the global-splitting
  version of the coefficient argument.
-/

@[expose] public section

universe u v

namespace Coalgebra

variable {K : Type u} {C : Type v}

open scoped TensorProduct

section CommSemiring

variable [CommSemiring K] [AddCommMonoid C] [Module K C]

-- Contract the second factor. Mathlib's `lTensor` acts on that factor.
private noncomputable def contractRight {M : Type*} [AddCommMonoid M] [Module K M]
    (f : C →ₗ[K] K) : M ⊗[K] C →ₗ[K] M :=
  (TensorProduct.rid K M).toLinearMap ∘ₗ f.lTensor M

private lemma contractRight_tmul {M : Type*} [AddCommMonoid M] [Module K M]
    (f : C →ₗ[K] K) (m : M) (c : C) :
    contractRight f (m ⊗ₜ[K] c) = f c • m := by
  simp [contractRight]

variable [Coalgebra K C]

private lemma contractRight_counit_comul (x : C) :
    contractRight (counit (R := K)) (comul x) = x := by
  simp [contractRight]

-- Third-factor contraction of coassociativity. Both comparison identities are
-- equalities of linear maps, checked on pure tensors (and pure triples).
private lemma comul_contractRight (f : C →ₗ[K] K) (x : C) :
    comul (contractRight f (comul x)) =
      TensorProduct.map (LinearMap.id : C →ₗ[K] C) (contractRight f)
        ((comul (R := K)).lTensor C (comul x)) := by
  have h₁ : (comul (R := K) (A := C)) ∘ₗ contractRight (M := C) f =
      contractRight (M := C ⊗[K] C) f ∘ₗ (comul (R := K) (A := C)).rTensor C := by
    ext c d
    simp [contractRight_tmul]
  have h₂ : contractRight f ∘ₗ (TensorProduct.assoc K C C C).symm.toLinearMap =
      TensorProduct.map (LinearMap.id : C →ₗ[K] C) (contractRight f) := by
    ext c d e
    simp [contractRight_tmul, TensorProduct.tmul_smul]
  calc
    comul (contractRight f (comul x)) =
        contractRight f ((comul (R := K)).rTensor C (comul x)) :=
      LinearMap.congr_fun h₁ (comul x)
    _ = contractRight f ((TensorProduct.assoc K C C C).symm
        ((comul (R := K)).lTensor C (comul x))) := by
      rw [coassoc_symm_apply]
    _ = _ := LinearMap.congr_fun h₂ _

variable [Module.Projective K C]

private theorem exists_fg_right_coideal_single (x : C) :
    ∃ U : Submodule K C, x ∈ U ∧ U.FG ∧
      ∀ y ∈ U, comul (R := K) y ∈ LinearMap.range (U.subtype.rTensor C) := by
  classical
  obtain ⟨σ, hσ⟩ := (inferInstance : Module.Projective K C).out
  have hsplit : (Finsupp.linearCombination K id).comp σ = LinearMap.id := by
    ext c
    exact hσ c
  obtain ⟨a, hrepr, hcoef⟩ := TensorProduct.exists_tensor_coefficients_of_split
    (Finsupp.linearCombination K id) σ hsplit (comul x)
  have hrepr' : (∑ i ∈ a.support, a i ⊗ₜ[K] i) = comul x := by
    simpa using hrepr
  have hcoef' (i : C) : a i = contractRight ((Finsupp.lapply i).comp σ) (comul x) :=
    hcoef i
  let t := a.support.image a
  let U : Submodule K C := Submodule.span K (t : Set C)
  have ha (i : C) (hi : i ∈ a.support) : a i ∈ U :=
    Submodule.subset_span (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  have hx : (∑ i ∈ a.support, counit (R := K) i • a i) = x := by
    simpa only [map_sum, contractRight_tmul, contractRight_counit_comul]
      using congrArg (contractRight (counit (R := K))) hrepr'
  have hclosed : U ≤ (LinearMap.range (U.subtype.rTensor C)).comap (comul (R := K)) := by
    apply Submodule.span_le.mpr
    rintro y hy
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hy
    have hcomul : comul (R := K) (a i) = ∑ j ∈ a.support,
        a j ⊗ₜ[K] contractRight ((Finsupp.lapply i).comp σ) (comul j) := by
      have h := comul_contractRight ((Finsupp.lapply i).comp σ) x
      rw [← hcoef' i] at h
      conv_rhs at h => rw [← hrepr']
      simpa only [map_sum, LinearMap.lTensor_tmul, TensorProduct.map_tmul,
        LinearMap.id_apply] using h
    change comul (R := K) (a i) ∈ LinearMap.range (U.subtype.rTensor C)
    rw [hcomul]
    apply Submodule.sum_mem
    intro j hj
    refine ⟨(⟨a j, ha j hj⟩ : U) ⊗ₜ[K]
      contractRight ((Finsupp.lapply i).comp σ) (comul j), ?_⟩
    simp only [LinearMap.rTensor_tmul, Submodule.subtype_apply]
  refine ⟨U, ?_, Submodule.fg_span t.finite_toSet, fun y hy ↦ hclosed hy⟩
  rw [← hx]
  exact U.sum_mem fun i hi ↦ U.smul_mem _ (ha i hi)

/-- Every finite subset of a coalgebra over a commutative semiring with projective
underlying module is contained in a module-finitely-generated right coideal.
Projectivity replaces freeness via a global section of the canonical free
presentation; no finite-generation assumption on the ambient module is required.
The right-coideal condition holds for every member of the submodule and uses
the image of `U ⊗ C → C ⊗ C`; it does not assert closure in `U ⊗ U` or
injectivity of the tensor inclusion. This generalizes the first step of the
classical field coefficient-coalgebra method, credited bibliographically to
Sweedler's *Hopf Algebras*. -/
theorem exists_fg_submodule_comul_right_closed_of_finite
    {s : Set C} (hs : s.Finite) :
    ∃ U : Submodule K C,
      s ⊆ (U : Set C) ∧ U.FG ∧
      ∀ x ∈ U, comul (R := K) x ∈ LinearMap.range (U.subtype.rTensor C) := by
  classical
  induction s, hs using Set.Finite.induction_on with
  | empty =>
    refine ⟨⊥, Set.empty_subset _, Submodule.fg_bot, ?_⟩
    intro x hx
    have hx0 : x = 0 := (Submodule.mem_bot K).mp hx
    simp [hx0]
  | @insert x s hxs hs ih =>
    obtain ⟨U, hx, hUfg, hU⟩ := exists_fg_right_coideal_single (K := K) x
    obtain ⟨V, hsV, hVfg, hV⟩ := ih
    have hu_range : LinearMap.range (U.subtype.rTensor C) ≤
        LinearMap.range ((U ⊔ V).subtype.rTensor C) := by
      simpa only [LinearMap.rTensor_def] using
        TensorProduct.range_map_mono (a := U.subtype) (b := (U ⊔ V).subtype)
          (c := (LinearMap.id : C →ₗ[K] C)) (d := (LinearMap.id : C →ₗ[K] C))
          (by simpa only [Submodule.range_subtype] using (le_sup_left : U ≤ U ⊔ V)) le_rfl
    have hv_range : LinearMap.range (V.subtype.rTensor C) ≤
        LinearMap.range ((U ⊔ V).subtype.rTensor C) := by
      simpa only [LinearMap.rTensor_def] using
        TensorProduct.range_map_mono (a := V.subtype) (b := (U ⊔ V).subtype)
          (c := (LinearMap.id : C →ₗ[K] C)) (d := (LinearMap.id : C →ₗ[K] C))
          (by simpa only [Submodule.range_subtype] using (le_sup_right : V ≤ U ⊔ V)) le_rfl
    have hu : U ≤ (LinearMap.range ((U ⊔ V).subtype.rTensor C)).comap (comul (R := K)) :=
      fun y hy ↦ hu_range (hU y hy)
    have hv : V ≤ (LinearMap.range ((U ⊔ V).subtype.rTensor C)).comap (comul (R := K)) :=
      fun y hy ↦ hv_range (hV y hy)
    refine ⟨U ⊔ V, ?_, hUfg.sup hVfg, fun y hy ↦ (sup_le hu hv) hy⟩
    rintro y (rfl | hy)
    · exact (le_sup_left : U ≤ U ⊔ V) hx
    · exact (le_sup_right : V ≤ U ⊔ V) (hsV hy)

end CommSemiring

section Field

variable [Field K] [AddCommGroup C] [Module K C] [Coalgebra K C]

/-- A finitely generated right coideal has a finite basis whose ambient images
admit a matrix presentation of comultiplication. Its coordinate functionals
extend to the ambient coalgebra and are biorthogonal to these basis images.
This is the coordinate-presentation step of the coefficient-coalgebra method. -/
theorem exists_basis_comul_coefficients (U : Submodule K C) (hfg : U.FG)
    (hclosed : ∀ x ∈ U, comul (R := K) x ∈ LinearMap.range (U.subtype.rTensor C)) :
    ∃ (b : Module.Basis (Fin (Module.finrank K U)) K U)
      (f : Fin (Module.finrank K U) → C →ₗ[K] K)
      (a : Fin (Module.finrank K U) → Fin (Module.finrank K U) → C),
      (∀ i, (f i).comp U.subtype = b.coord i) ∧
      (∀ i j, f i (b j : C) = if i = j then 1 else 0) ∧
      (∀ j, comul (R := K) (b j : C) = ∑ i, (b i : C) ⊗ₜ[K] a i j) ∧
      Submodule.span K (Set.range fun i ↦ (b i : C)) = U := by
  classical
  let : Module.Finite K U := Module.Finite.iff_fg.mpr hfg
  let b := Module.finBasis K U
  choose f hf using fun i : Fin (Module.finrank K U) ↦
    LinearMap.exists_extend (b.coord i)
  have hw (j : Fin (Module.finrank K U)) :
      ∃ z : U ⊗[K] C, U.subtype.rTensor C z = comul (R := K) (b j : C) :=
    hclosed (b j : C) (b j).property
  choose z hz using hw
  let a (i j : Fin (Module.finrank K U)) :=
    TensorProduct.equivFinsuppOfBasisLeft b (z j) i
  have hrepr (j : Fin (Module.finrank K U)) :
      (∑ i, b i ⊗ₜ[K] a i j) = z j := by
    have h := (TensorProduct.equivFinsuppOfBasisLeft b).symm_apply_apply (z j)
    rw [TensorProduct.equivFinsuppOfBasisLeft_symm_apply,
      Finsupp.sum_fintype _ _ (fun _ ↦ by simp)] at h
    exact h
  refine ⟨b, f, a, hf, ?_, ?_, ?_⟩
  · intro i j
    simpa only [LinearMap.comp_apply, Submodule.subtype_apply,
      Module.Basis.coord_apply, Module.Basis.repr_self_apply, eq_comm]
      using LinearMap.congr_fun (hf i) (b j)
  · intro j
    calc
      comul (R := K) (b j : C) = U.subtype.rTensor C (z j) := (hz j).symm
      _ = ∑ i, (b i : C) ⊗ₜ[K] a i j := by
        rw [← hrepr j]
        simp only [map_sum, LinearMap.rTensor_tmul, Submodule.subtype_apply]
  · change Submodule.span K (Set.range (U.subtype ∘ b)) = U
    rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_subtype_top]

/-- The fundamental theorem of coalgebras over a field, in finite-subset form:
every finite subset is contained in a module-finitely-generated submodule whose
comultiplication lies in the image of its tensor square. This is the classical
coefficient-coalgebra theorem, credited bibliographically to Sweedler's
*Hopf Algebras*. -/
theorem exists_fg_submodule_comul_closed_of_finite
    {s : Set C} (hs : s.Finite) :
    ∃ D : Submodule K C,
      s ⊆ (D : Set C) ∧ D.FG ∧
      ∀ x ∈ D, Coalgebra.comul (R := K) x ∈
        LinearMap.range (TensorProduct.mapIncl D D) := by
  obtain ⟨U, hsU, hUfg, hUclosed⟩ :=
    exists_fg_submodule_comul_right_closed_of_finite (K := K) hs
  obtain ⟨b, f, a, _hfcomp, hf, hΔ, hspan⟩ :=
    exists_basis_comul_coefficients U hUfg hUclosed
  let D := Submodule.span K (Set.range (Function.uncurry a))
  have hUD : U ≤ D := by
    rw [← hspan]
    exact span_le_span_coefficients hΔ
  refine ⟨D, fun x hx ↦ hUD (hsU hx), fg_span_coefficients a, ?_⟩
  intro x hx
  exact comul_mem_range_mapIncl_span_coefficients (f := f) hΔ hf hx

end Field

end Coalgebra
