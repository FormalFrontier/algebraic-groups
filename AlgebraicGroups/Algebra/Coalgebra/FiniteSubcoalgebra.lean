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
public import Mathlib.RingTheory.FiniteType
public import Mathlib.Data.Matrix.Basic

/-!
# Finite right-coaction and coalgebra containment

Over a commutative semiring `K`, let `C` be a coalgebra and `M` a module, both
with additive commutative monoid structures and with independent universes.
For a linear right coaction `ρ : M →ₗ[K] M ⊗[K] C` satisfying coassociativity
and right counitality, projectivity of `C` gives finite containment:
`exists_fg_submodule_coaction_right_closed_of_finite` places every finite subset
of `M` in a submodule `U` with `U.FG` and
`ρ x ∈ LinearMap.range (U.subtype.rTensor C)` for every `x ∈ U`.
Neither projectivity of `M`, finite generation of either module, nor surjectivity
of the counit is required.

The coefficient argument uses a global section of the canonical free presentation
of `C`, rather than a basis of `M` or `C`. Contracting the right counit recovers
each element from its coefficients; contracting coassociativity gives image
stability for every member of their span. This module supplies the image-stable
submodule. `AlgebraicGroups.Algebra.Coalgebra.RightComodule` equips it with a
subtype coaction and colinear inclusion using flatness of `C`.

The regular case `M = C`, `ρ = comul` is
`exists_fg_submodule_comul_right_closed_of_finite`: every finite subset lies in
a finitely generated right coideal with image closure under `U ⊗ C → C ⊗ C`.
It is a specialization of the same coefficient argument.

The fundamental theorem of coalgebras over a field has a distinct two-factor
step: the coefficients of a finite basis produce a submodule `D` with
comultiplication in the image of `D ⊗ D → C ⊗ C` for every member.
The automatic basis and ambient coordinate extensions in this later step are
field-only. These statements use module finite generation (`Submodule.FG`),
not algebra finite generation, and do not construct a coalgebra structure on
the subtype. No multiplication on `C` is required. A right coideal alone need
not have two-factor closure, and finite tensor support alone does not give
either closure. The counit takes values in the scalar semiring, so it needs
no additional closure condition.

## References

* M. E. Sweedler, *Hopf Algebras*, W. A. Benjamin, 1969, for classical
  comodules, the field coalgebra theorem and coefficient method (bibliographic credit).
* Mathlib's projective-module, coalgebra and tensor-product formalizations.
* Formal Frontier's projective-coalgebra formalization, for the global-splitting
  version of the coefficient argument.
-/

@[expose] public section

universe u v w

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

variable {M : Type w} [AddCommMonoid M] [Module K M]

private lemma contractRight_counit_coaction (ρ : M →ₗ[K] M ⊗[K] C)
    (hcounit : (counit (R := K) (A := C)).lTensor M ∘ₗ ρ =
      (TensorProduct.rid K M).symm.toLinearMap) (x : M) :
    contractRight (counit (R := K)) (ρ x) = x := by
  change TensorProduct.rid K M ((counit (R := K)).lTensor M (ρ x)) = x
  rw [show (counit (R := K)).lTensor M (ρ x) = (TensorProduct.rid K M).symm x
    from LinearMap.congr_fun hcounit x]
  exact (TensorProduct.rid K M).apply_symm_apply x

-- Third-factor contraction of coassociativity. Both comparison identities are
-- equalities of linear maps, checked on pure tensors (and pure triples).
private lemma coaction_contractRight (ρ : M →ₗ[K] M ⊗[K] C)
    (hcoassoc : TensorProduct.assoc K M C C ∘ₗ ρ.rTensor C ∘ₗ ρ =
      (comul (R := K) (A := C)).lTensor M ∘ₗ ρ)
    (f : C →ₗ[K] K) (x : M) :
    ρ (contractRight f (ρ x)) =
      TensorProduct.map (LinearMap.id : M →ₗ[K] M) (contractRight (M := C) f)
        ((comul (R := K)).lTensor M (ρ x)) := by
  have h₁ : ρ ∘ₗ contractRight (M := M) f =
      contractRight (M := M ⊗[K] C) f ∘ₗ ρ.rTensor C := by
    ext m c
    simp [contractRight_tmul]
  have h₂ : contractRight f ∘ₗ (TensorProduct.assoc K M C C).symm.toLinearMap =
      TensorProduct.map (LinearMap.id : M →ₗ[K] M) (contractRight (M := C) f) := by
    ext m c d
    simp [contractRight_tmul, TensorProduct.tmul_smul]
  have hρ : (TensorProduct.assoc K M C C).symm
      ((comul (R := K)).lTensor M (ρ x)) = ρ.rTensor C (ρ x) := by
    rw [(TensorProduct.assoc K M C C).symm_apply_eq]
    exact (LinearMap.congr_fun hcoassoc x).symm
  calc
    ρ (contractRight f (ρ x)) = contractRight f (ρ.rTensor C (ρ x)) :=
      LinearMap.congr_fun h₁ (ρ x)
    _ = contractRight f ((TensorProduct.assoc K M C C).symm
        ((comul (R := K)).lTensor M (ρ x))) := by rw [hρ]
    _ = _ := LinearMap.congr_fun h₂ _

variable [Module.Projective K C]

private theorem exists_fg_coaction_stable_single (ρ : M →ₗ[K] M ⊗[K] C)
    (hcoassoc : TensorProduct.assoc K M C C ∘ₗ ρ.rTensor C ∘ₗ ρ =
      (comul (R := K) (A := C)).lTensor M ∘ₗ ρ)
    (hcounit : (counit (R := K) (A := C)).lTensor M ∘ₗ ρ =
      (TensorProduct.rid K M).symm.toLinearMap) (x : M) :
    ∃ U : Submodule K M, x ∈ U ∧ U.FG ∧
      ∀ y ∈ U, ρ y ∈ LinearMap.range (U.subtype.rTensor C) := by
  classical
  obtain ⟨σ, hσ⟩ := (inferInstance : Module.Projective K C).out
  have hsplit : (Finsupp.linearCombination K id).comp σ = LinearMap.id := by
    ext c
    exact hσ c
  obtain ⟨a, hrepr, hcoef⟩ := TensorProduct.exists_tensor_coefficients_of_split
    (Finsupp.linearCombination K id) σ hsplit (ρ x)
  have hrepr' : (∑ i ∈ a.support, a i ⊗ₜ[K] i) = ρ x := by
    simpa using hrepr
  have hcoef' (i : C) : a i = contractRight ((Finsupp.lapply i).comp σ) (ρ x) :=
    hcoef i
  let t := a.support.image a
  let U : Submodule K M := Submodule.span K (t : Set M)
  have ha (i : C) (hi : i ∈ a.support) : a i ∈ U :=
    Submodule.subset_span (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  have hx : (∑ i ∈ a.support, counit (R := K) i • a i) = x := by
    have hx_counit := contractRight_counit_coaction ρ hcounit x
    simpa only [map_sum, contractRight_tmul, hx_counit]
      using congrArg (contractRight (counit (R := K))) hrepr'
  have hclosed : U ≤ (LinearMap.range (U.subtype.rTensor C)).comap ρ := by
    apply Submodule.span_le.mpr
    rintro y hy
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hy
    have hcoaction : ρ (a i) = ∑ j ∈ a.support,
        a j ⊗ₜ[K] contractRight ((Finsupp.lapply i).comp σ) (comul j) := by
      have h := coaction_contractRight ρ hcoassoc ((Finsupp.lapply i).comp σ) x
      rw [← hcoef' i] at h
      conv_rhs at h => rw [← hrepr']
      simpa only [map_sum, LinearMap.lTensor_tmul, TensorProduct.map_tmul,
        LinearMap.id_apply] using h
    change ρ (a i) ∈ LinearMap.range (U.subtype.rTensor C)
    rw [hcoaction]
    apply Submodule.sum_mem
    intro j hj
    refine ⟨(⟨a j, ha j hj⟩ : U) ⊗ₜ[K]
      contractRight ((Finsupp.lapply i).comp σ) (comul j), ?_⟩
    simp only [LinearMap.rTensor_tmul, Submodule.subtype_apply]
  refine ⟨U, ?_, Submodule.fg_span t.finite_toSet, fun y hy ↦ hclosed hy⟩
  rw [← hx]
  exact U.sum_mem fun i hi ↦ U.smul_mem _ (ha i hi)

/-- Every finite subset of a module with a right coaction of a projective
coalgebra is contained in a finitely generated image-stable submodule.
The hypotheses are the coassociativity and right counitality equations for the
linear coaction. Neither projectivity nor finite generation of the coacted-on
module is required. Image stability holds for every member of the submodule.
This is the split-coordinate form of the classical coefficient method for
comodules, credited bibliographically to Sweedler's *Hopf Algebras*. -/
theorem exists_fg_submodule_coaction_right_closed_of_finite
    (ρ : M →ₗ[K] M ⊗[K] C)
    (hcoassoc : TensorProduct.assoc K M C C ∘ₗ ρ.rTensor C ∘ₗ ρ =
      (comul (R := K) (A := C)).lTensor M ∘ₗ ρ)
    (hcounit : (counit (R := K) (A := C)).lTensor M ∘ₗ ρ =
      (TensorProduct.rid K M).symm.toLinearMap)
    {s : Set M} (hs : s.Finite) :
    ∃ U : Submodule K M,
      s ⊆ (U : Set M) ∧ U.FG ∧
      ∀ x ∈ U, ρ x ∈ LinearMap.range (U.subtype.rTensor C) := by
  classical
  induction s, hs using Set.Finite.induction_on with
  | empty =>
    refine ⟨⊥, Set.empty_subset _, Submodule.fg_bot, ?_⟩
    intro x hx
    have hx0 : x = 0 := (Submodule.mem_bot K).mp hx
    simp [hx0]
  | @insert x s hxs hs ih =>
    obtain ⟨U, hx, hUfg, hU⟩ := exists_fg_coaction_stable_single ρ hcoassoc hcounit x
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
    have hu : U ≤ (LinearMap.range ((U ⊔ V).subtype.rTensor C)).comap ρ :=
      fun y hy ↦ hu_range (hU y hy)
    have hv : V ≤ (LinearMap.range ((U ⊔ V).subtype.rTensor C)).comap ρ :=
      fun y hy ↦ hv_range (hV y hy)
    refine ⟨U ⊔ V, ?_, hUfg.sup hVfg, fun y hy ↦ (sup_le hu hv) hy⟩
    rintro y (rfl | hy)
    · exact (le_sup_left : U ≤ U ⊔ V) hx
    · exact (le_sup_right : V ≤ U ⊔ V) (hsV hy)

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
  exact exists_fg_submodule_coaction_right_closed_of_finite (comul (R := K))
    Coalgebra.coassoc Coalgebra.lTensor_counit_comp_comul hs

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

namespace Coalgebra

open scoped TensorProduct

section FiniteType

variable {K : Type u} {A : Type v}
variable [Field K] [Semiring A] [Algebra K A] [Coalgebra K A]
variable [Algebra.FiniteType K A]

/-- A finite-type algebra carrying a coalgebra structure over a field admits a
finite coefficient matrix whose entries generate the algebra. Comultiplication
satisfies the coefficient-matrix identity, and the counits form the identity
matrix over the field. The algebra need not be commutative or finite-dimensional,
and the matrix size may be zero. The coefficient method for finite right coideals
is credited to Sweedler's *Hopf Algebras*. -/
theorem exists_coefficientMatrix_adjoin_eq_top :
    ∃ (n : ℕ) (a : Matrix (Fin n) (Fin n) A),
      (∀ i j, Coalgebra.comul (R := K) (a i j) = ∑ k, a i k ⊗ₜ[K] a k j) ∧
      (∀ i j, Coalgebra.counit (R := K) (a i j) = if i = j then 1 else 0) ∧
      Algebra.adjoin K (Set.range (Function.uncurry a)) = ⊤ := by
  classical
  let : AddCommGroup A := Module.addCommMonoidToAddCommGroup K
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType K A).out
  obtain ⟨U, hsU, hUfg, hUclosed⟩ :=
    exists_fg_submodule_comul_right_closed_of_finite (K := K) s.finite_toSet
  obtain ⟨b, f, a, _hfcomp, hf, hΔ, hspan⟩ :=
    exists_basis_comul_coefficients U hUfg hUclosed
  have hUcoeff : U ≤ Submodule.span K (Set.range (Function.uncurry a)) :=
    hspan.ge.trans (span_le_span_coefficients hΔ)
  refine ⟨Module.finrank K U, a, fun i j ↦ comul_coefficient hΔ hf i j,
    fun i j ↦ counit_coefficient hΔ hf i j, ?_⟩
  apply top_unique
  rw [← hs]
  exact Algebra.adjoin_le fun x hx ↦
    Algebra.span_le_adjoin K _ (hUcoeff (hsU hx))

end FiniteType

end Coalgebra
