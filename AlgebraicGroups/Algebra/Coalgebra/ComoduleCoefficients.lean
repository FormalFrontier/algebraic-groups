/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.RightComodule
public import AlgebraicGroups.Algebra.Coalgebra.Subcoalgebra.Hom

/-!
# Coefficient coalgebras of right comodules

For a specified right coaction `X` of a coalgebra `C` on a module `M`, a
coefficient is obtained by evaluating a linear functional on the first tensor
factor of `X.coaction m`. The coefficient span uses all linear functionals on
`M` and all elements of `M`; no basis or finite-generation hypothesis is part
of its definition. Coefficients and their span are defined over a commutative
semiring.

Over a field, `coefficientSubcoalgebra` has exactly this coefficient span as its
underlying submodule. Corestriction of the coacting coalgebra uses the tensor
inclusion `M ⊗ D → M ⊗ C`, rather than a comodule morphism with a fixed coacting
coalgebra. The inclusion equation characterizes the corestricted coaction.
The coefficient span is contained in the underlying submodule of `D` exactly
when the coaction factors through this tensor inclusion.

The field constructions use the ambient coalgebra's given additive-group
structure, matching the `Subcoalgebra` interface. Additive inverses in a module
over a field are determined by scalar multiplication by `-1`, so this interface
imposes no additional mathematical assumption. The coacted-on module retains
only its additive commutative monoid and module structures.

## References

* M. E. Sweedler, *Hopf Algebras*, W. A. Benjamin, 1969, for the classical
  coefficient-coalgebra construction (bibliographic credit).
* Mathlib's tensor-product, linear-map, and module-finiteness formalizations.
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Coalgebra.RightComodule

section CommSemiring

variable {K : Type u} {C : Type v} {M : Type w}
variable [CommSemiring K] [AddCommMonoid C] [Module K C] [Coalgebra K C]
variable [AddCommMonoid M] [Module K M]

/-- A coefficient of a right coaction, obtained by evaluating its first tensor factor. -/
def coefficient (X : RightComodule K C M) (ell : M →ₗ[K] K) (m : M) : C :=
  TensorProduct.lid K C (ell.rTensor C (X.coaction m))

/-- The defining all-dual evaluation formula for a coefficient. -/
theorem coefficient_eq (X : RightComodule K C M) (ell : M →ₗ[K] K) (m : M) :
    X.coefficient ell m = TensorProduct.lid K C (ell.rTensor C (X.coaction m)) :=
  rfl

/-- The submodule spanned by all coefficients of a specified right coaction. -/
def coefficientSpan (X : RightComodule K C M) : Submodule K C :=
  Submodule.span K (Set.range (Function.uncurry X.coefficient))

/-- The coefficient span is the span of the exact range of all-dual evaluation. -/
theorem coefficientSpan_eq_span (X : RightComodule K C M) :
    X.coefficientSpan = Submodule.span K (Set.range (Function.uncurry X.coefficient)) :=
  rfl

/-- Every coefficient belongs to the coefficient span. -/
theorem coefficient_mem_coefficientSpan (X : RightComodule K C M)
    (ell : M →ₗ[K] K) (m : M) : X.coefficient ell m ∈ X.coefficientSpan :=
  Submodule.subset_span ⟨(ell, m), rfl⟩

/-- Containment of the coefficient span is equivalent to containment of all coefficients. -/
theorem coefficientSpan_le_iff (X : RightComodule K C M) (S : Submodule K C) :
    X.coefficientSpan ≤ S ↔ ∀ (ell : M →ₗ[K] K) (m : M), X.coefficient ell m ∈ S := by
  constructor
  · intro h ell m
    exact h (X.coefficient_mem_coefficientSpan ell m)
  · intro h
    apply Submodule.span_le.mpr
    rintro c ⟨⟨ell, m⟩, rfl⟩
    exact h ell m

private theorem coefficient_eq_sum_basis {ι : Type*} [Fintype ι]
    (X : RightComodule K C M) (b : Module.Basis ι K M)
    (ell : M →ₗ[K] K) (m : M) :
    X.coefficient ell m = ∑ j, b.equivFun m j • X.coefficient ell (b j) := by
  let f : M →ₗ[K] C :=
    (TensorProduct.lid K C).toLinearMap ∘ₗ ell.rTensor C ∘ₗ X.coaction
  have h := b.constr_apply_fintype K (fun j ↦ f (b j)) m
  rw [b.constr_self K f] at h
  simpa only [f, LinearMap.comp_apply, coefficient_eq, LinearEquiv.coe_coe] using h

private theorem coefficientSpan_eq_span_basis {ι : Type*} [Finite ι]
    (X : RightComodule K C M) (b : Module.Basis ι K M) :
    X.coefficientSpan = Submodule.span K
      (Set.range (Function.uncurry (fun i j : ι ↦ X.coefficient (b.coord i) (b j)))) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  apply le_antisymm
  · apply (X.coefficientSpan_le_iff _).mpr
    intro ell m
    have hrepr := (TensorProduct.equivFinsuppOfBasisLeft b).symm_apply_apply (X.coaction m)
    rw [TensorProduct.equivFinsuppOfBasisLeft_symm_apply,
      Finsupp.sum_fintype _ _ (fun _ ↦ by simp)] at hrepr
    have hcoaction :
        X.coaction m = ∑ i, b i ⊗ₜ[K] X.coefficient (b.coord i) m := by
      simpa only [TensorProduct.equivFinsuppOfBasisLeft_apply, coefficient_eq]
        using hrepr.symm
    rw [coefficient_eq, hcoaction]
    simp only [map_sum, LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
    refine Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ ?_
    rw [coefficient_eq_sum_basis X b (b.coord i) m]
    exact Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _
      (Submodule.subset_span ⟨(i, j), rfl⟩)
  · apply Submodule.span_le.mpr
    rintro c ⟨⟨i, j⟩, rfl⟩
    exact X.coefficient_mem_coefficientSpan (b.coord i) (b j)

end CommSemiring

/-- All first-factor dual evaluations detect a tensor's membership in the
range of a second-factor submodule inclusion. -/
private theorem tensor_mem_range_lTensor_iff {K : Type u} {N : Type v} {M : Type w}
    [Field K] [AddCommMonoid N] [Module K N] [AddCommMonoid M] [Module K M]
    (S : Submodule K N) (z : M ⊗[K] N) :
    z ∈ LinearMap.range (S.subtype.lTensor M) ↔
      ∀ ell : M →ₗ[K] K, TensorProduct.lid K N (ell.rTensor N z) ∈ S := by
  constructor
  · rintro ⟨y, rfl⟩ ell
    induction y with
    | tmul m n =>
      simpa only [LinearMap.lTensor_tmul, Submodule.subtype_apply,
        LinearMap.rTensor_tmul, TensorProduct.lid_tmul] using
        S.smul_mem (ell m) n.property
    | add y₁ y₂ hy₁ hy₂ =>
      simpa only [map_add] using S.add_mem hy₁ hy₂
  · intro hz
    classical
    let : AddCommGroup M := Module.addCommMonoidToAddCommGroup K (M := M)
    let b := Module.Basis.ofVectorSpace K M
    let c := TensorProduct.equivFinsuppOfBasisLeft (N := N) b z
    have hc (i : Module.Basis.ofVectorSpaceIndex K M) : c i ∈ S := by
      dsimp only [c]
      rw [TensorProduct.equivFinsuppOfBasisLeft_apply]
      exact hz (b.coord i)
    have hrepr : c.sum (fun i n ↦ b i ⊗ₜ[K] n) = z := by
      simpa only [TensorProduct.equivFinsuppOfBasisLeft_symm_apply] using
        (TensorProduct.equivFinsuppOfBasisLeft b).symm_apply_apply z
    rw [← hrepr]
    refine Submodule.finsuppSum_mem K (LinearMap.range (S.subtype.lTensor M)) c
      (fun i n ↦ b i ⊗ₜ[K] n) ?_
    intro i _
    refine ⟨b i ⊗ₜ[K] (⟨c i, hc i⟩ : S), ?_⟩
    simp only [LinearMap.lTensor_tmul, Submodule.subtype_apply]

private theorem coefficientSpan_fg
    {K : Type u} {C : Type v} {M : Type w}
    [Field K] [AddCommMonoid C] [Module K C] [Coalgebra K C]
    [AddCommMonoid M] [Module K M] [Module.Finite K M] (X : RightComodule K C M) :
    X.coefficientSpan.FG := by
  classical
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup K (M := M)
  let b := Module.finBasis K M
  rw [coefficientSpan_eq_span_basis X b]
  exact Coalgebra.fg_span_coefficients (fun i j ↦ X.coefficient (b.coord i) (b j))

section Field

variable {K : Type u} {C : Type v} {M : Type w}
variable [Field K] [AddCommGroup C] [Module K C] [Coalgebra K C]
variable [AddCommMonoid M] [Module K M]

-- Contract the first factor of right-coaction coassociativity. The two
-- comparison maps are checked on pure tensors, keeping the coalgebra factors
-- in their original order.
private theorem comul_coefficient_eq_rTensor (X : RightComodule K C M)
    (ell : M →ₗ[K] K) (m : M) :
    comul (R := K) (X.coefficient ell m) =
      (((TensorProduct.lid K C).toLinearMap ∘ₗ ell.rTensor C) ∘ₗ
        X.coaction).rTensor C (X.coaction m) := by
  let q : M ⊗[K] C →ₗ[K] C :=
    (TensorProduct.lid K C).toLinearMap ∘ₗ ell.rTensor C
  let q₂ : M ⊗[K] (C ⊗[K] C) →ₗ[K] C ⊗[K] C :=
    (TensorProduct.lid K (C ⊗[K] C)).toLinearMap ∘ₗ ell.rTensor (C ⊗[K] C)
  have hΔ : comul (R := K) ∘ₗ q = q₂ ∘ₗ (comul (R := K)).lTensor M := by
    refine TensorProduct.ext' fun x c => ?_
    simp [q, q₂]
  have ha : q₂ ∘ₗ (TensorProduct.assoc K M C C).toLinearMap = q.rTensor C := by
    refine TensorProduct.ext (TensorProduct.ext ?_)
    ext x c d
    simp [q, q₂, TensorProduct.smul_tmul']
  calc
    comul (R := K) (X.coefficient ell m) =
        q₂ ((comul (R := K)).lTensor M (X.coaction m)) :=
      LinearMap.congr_fun hΔ (X.coaction m)
    _ = q₂ (TensorProduct.assoc K M C C (X.coaction.rTensor C (X.coaction m))) := by
      rw [X.coassoc_apply]
    _ = q.rTensor C (X.coaction.rTensor C (X.coaction m)) :=
      LinearMap.congr_fun ha _
    _ = (q ∘ₗ X.coaction).rTensor C (X.coaction m) :=
      (LinearMap.rTensor_comp_apply (M := C) (g := q) (f := X.coaction)
        (X.coaction m)).symm

private theorem coefficientSpan_comul_mem (X : RightComodule K C M)
    {c : C} (hc : c ∈ X.coefficientSpan) :
    comul (R := K) c ∈ LinearMap.range
      (TensorProduct.mapIncl X.coefficientSpan X.coefficientSpan) := by
  classical
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup K (M := M)
  have hS : X.coefficientSpan ≤
      (LinearMap.range (TensorProduct.mapIncl X.coefficientSpan X.coefficientSpan)).comap
        (comul (R := K)) := by
    apply (X.coefficientSpan_le_iff _).mpr
    intro ell m
    change comul (R := K) (X.coefficient ell m) ∈ LinearMap.range
      (TensorProduct.mapIncl X.coefficientSpan X.coefficientSpan)
    let b := Module.Basis.ofVectorSpace K M
    let f := TensorProduct.equivFinsuppOfBasisLeft b (X.coaction m)
    have hf (i : Module.Basis.ofVectorSpaceIndex K M) :
        f i = X.coefficient (b.coord i) m :=
      TensorProduct.equivFinsuppOfBasisLeft_apply b (X.coaction m) i
    have hρ : f.sum (fun i c => b i ⊗ₜ[K] c) = X.coaction m := by
      simpa only [TensorProduct.equivFinsuppOfBasisLeft_symm_apply] using
        (TensorProduct.equivFinsuppOfBasisLeft b).symm_apply_apply (X.coaction m)
    let T := (((TensorProduct.lid K C).toLinearMap ∘ₗ ell.rTensor C) ∘ₗ
      X.coaction).rTensor C
    have hΔ : comul (R := K) (X.coefficient ell m) =
        ∑ i ∈ f.support, X.coefficient ell (b i) ⊗ₜ[K] f i := by
      calc
        comul (R := K) (X.coefficient ell m) = T (X.coaction m) :=
          comul_coefficient_eq_rTensor X ell m
        _ = T (f.sum (fun i c => b i ⊗ₜ[K] c)) := congrArg T hρ.symm
        _ = ∑ i ∈ f.support, X.coefficient ell (b i) ⊗ₜ[K] f i := by
          simp [T, Finsupp.sum, map_sum, coefficient_eq]
    rw [hΔ]
    apply Submodule.sum_mem
    intro i hi
    exact ⟨(⟨X.coefficient ell (b i), X.coefficient_mem_coefficientSpan ell (b i)⟩ :
        X.coefficientSpan) ⊗ₜ[K]
      (⟨f i, by rw [hf i]; exact X.coefficient_mem_coefficientSpan (b.coord i) m⟩ :
        X.coefficientSpan), rfl⟩
  exact hS hc

/-- The coefficient subcoalgebra, with underlying submodule the all-dual coefficient span. -/
def coefficientSubcoalgebra (X : RightComodule K C M) : _root_.Subcoalgebra K C :=
  _root_.Subcoalgebra.mk' X.coefficientSpan (by
    intro c hc
    exact coefficientSpan_comul_mem X hc)

/-- The carrier of the coefficient subcoalgebra is exactly the coefficient span. -/
@[simp] theorem coefficientSubcoalgebra_toSubmodule (X : RightComodule K C M) :
    X.coefficientSubcoalgebra.toSubmodule = X.coefficientSpan :=
  rfl

/-- The underlying submodule is the span of the exact range of coefficient evaluation. -/
theorem coefficientSubcoalgebra_toSubmodule_eq_span_range (X : RightComodule K C M) :
    X.coefficientSubcoalgebra.toSubmodule =
      Submodule.span K (Set.range (Function.uncurry X.coefficient)) :=
  rfl

/-- Membership in the coefficient subcoalgebra is membership in the coefficient span. -/
@[simp] theorem mem_coefficientSubcoalgebra (X : RightComodule K C M) (c : C) :
    c ∈ X.coefficientSubcoalgebra ↔ c ∈ X.coefficientSpan :=
  Iff.rfl

/-- Every coefficient belongs to the coefficient subcoalgebra. -/
theorem coefficient_mem_coefficientSubcoalgebra (X : RightComodule K C M)
    (ell : M →ₗ[K] K) (m : M) : X.coefficient ell m ∈ X.coefficientSubcoalgebra :=
  X.coefficient_mem_coefficientSpan ell m

/-- A coaction takes values in `M ⊗ D` exactly when its coefficient span is
contained in the underlying submodule of `D`. -/
theorem coaction_mem_range_iff_coefficientSpan_le (X : RightComodule K C M)
    (D : _root_.Subcoalgebra K C) :
    (∀ m : M, X.coaction m ∈ LinearMap.range (D.subtype.toLinearMap.lTensor M)) ↔
      X.coefficientSpan ≤ D.toSubmodule := by
  constructor
  · intro h
    apply (X.coefficientSpan_le_iff D.toSubmodule).mpr
    intro ell m
    exact (tensor_mem_range_lTensor_iff D.toSubmodule (X.coaction m)).mp (h m) ell
  · intro h m
    apply (tensor_mem_range_lTensor_iff D.toSubmodule (X.coaction m)).mpr
    intro ell
    exact (X.coefficientSpan_le_iff D.toSubmodule).mp h ell m

/-- The linear corestriction of a coaction through the tensor inclusion of a subcoalgebra. -/
noncomputable def coactionCodRestrict (X : RightComodule K C M)
    (D : _root_.Subcoalgebra K C)
    (h : ∀ m : M, X.coaction m ∈ LinearMap.range (D.subtype.toLinearMap.lTensor M)) :
    M →ₗ[K] M ⊗[K] D :=
  X.coaction.codLift (D.subtype.toLinearMap.lTensor M)
    (by
      let : AddCommGroup M := Module.addCommMonoidToAddCommGroup K (M := M)
      exact Module.Flat.lTensor_preserves_injective_linearMap
        (R := K) (M := M) D.subtype.toLinearMap D.subtype_injective) h

/-- Tensor inclusion after linear corestriction recovers the original coaction. -/
theorem subtype_lTensor_comp_coactionCodRestrict (X : RightComodule K C M)
    (D : _root_.Subcoalgebra K C)
    (h : ∀ m : M, X.coaction m ∈ LinearMap.range (D.subtype.toLinearMap.lTensor M)) :
    D.subtype.toLinearMap.lTensor M ∘ₗ X.coactionCodRestrict D h = X.coaction :=
  LinearMap.comp_codLift _ _ _ _

/-- The corestricted linear coaction satisfies the inclusion equation at each element. -/
@[simp] theorem subtype_lTensor_coactionCodRestrict (X : RightComodule K C M)
    (D : _root_.Subcoalgebra K C)
    (h : ∀ m : M, X.coaction m ∈ LinearMap.range (D.subtype.toLinearMap.lTensor M))
    (m : M) :
    D.subtype.toLinearMap.lTensor M (X.coactionCodRestrict D h m) = X.coaction m :=
  LinearMap.congr_fun (X.subtype_lTensor_comp_coactionCodRestrict D h) m

private theorem coactionCodRestrict_coassoc (X : RightComodule K C M)
    (D : _root_.Subcoalgebra K C)
    (h : ∀ m : M, X.coaction m ∈ LinearMap.range (D.subtype.toLinearMap.lTensor M)) :
    TensorProduct.assoc K M D D ∘ₗ (X.coactionCodRestrict D h).rTensor D ∘ₗ
        X.coactionCodRestrict D h =
      (comul (R := K) (A := D)).lTensor M ∘ₗ X.coactionCodRestrict D h := by
  let ρ : M →ₗ[K] M ⊗[K] D := X.coactionCodRestrict D h
  have hρ : D.subtype.toLinearMap.lTensor M ∘ₗ ρ = X.coaction :=
    X.subtype_lTensor_comp_coactionCodRestrict D h
  have hρ_apply (m : M) : D.subtype.toLinearMap.lTensor M (ρ m) = X.coaction m :=
    LinearMap.congr_fun hρ m
  have hρ_tensor :
      TensorProduct.map (D.subtype.toLinearMap.lTensor M) D.subtype.toLinearMap ∘ₗ
          ρ.rTensor D =
        X.coaction.rTensor C ∘ₗ D.subtype.toLinearMap.lTensor M := by
    rw [LinearMap.map_comp_rTensor, hρ, LinearMap.rTensor_comp_lTensor]
  have hcomul :
      (TensorProduct.map D.subtype.toLinearMap D.subtype.toLinearMap).lTensor M ∘ₗ
          (comul (R := K) (A := D)).lTensor M =
        (comul (R := K) (A := C)).lTensor M ∘ₗ D.subtype.toLinearMap.lTensor M := by
    rw [← LinearMap.lTensor_comp, D.subtype.map_comp_comul, LinearMap.lTensor_comp]
  -- Only the cancellation step needs the field's canonical additive inverses on M.
  have hinj : Function.Injective
      ((TensorProduct.map D.subtype.toLinearMap D.subtype.toLinearMap).lTensor M) := by
    let : AddCommGroup M := Module.addCommMonoidToAddCommGroup K (M := M)
    exact Module.Flat.lTensor_preserves_injective_linearMap (M := M)
      (TensorProduct.mapIncl D.toSubmodule D.toSubmodule)
      (Module.Flat.tensorProduct_mapIncl_injective_of_right D.toSubmodule D.toSubmodule)
  apply LinearMap.ext
  intro m
  apply hinj
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  calc
    (TensorProduct.map D.subtype.toLinearMap D.subtype.toLinearMap).lTensor M
        (TensorProduct.assoc K M D D (ρ.rTensor D (ρ m))) =
        TensorProduct.assoc K M C C
          (TensorProduct.map (D.subtype.toLinearMap.lTensor M) D.subtype.toLinearMap
            (ρ.rTensor D (ρ m))) :=
      TensorProduct.map_map_assoc (LinearMap.id : M →ₗ[K] M)
        D.subtype.toLinearMap D.subtype.toLinearMap _
    _ = TensorProduct.assoc K M C C
        (X.coaction.rTensor C (D.subtype.toLinearMap.lTensor M (ρ m))) :=
      congrArg (TensorProduct.assoc K M C C) (LinearMap.congr_fun hρ_tensor (ρ m))
    _ = TensorProduct.assoc K M C C (X.coaction.rTensor C (X.coaction m)) := by
      rw [hρ_apply]
    _ = (comul (R := K) (A := C)).lTensor M (X.coaction m) := X.coassoc_apply m
    _ = (comul (R := K) (A := C)).lTensor M
        (D.subtype.toLinearMap.lTensor M (ρ m)) := by rw [hρ_apply]
    _ = (TensorProduct.map D.subtype.toLinearMap D.subtype.toLinearMap).lTensor M
        ((comul (R := K) (A := D)).lTensor M (ρ m)) :=
      (LinearMap.congr_fun hcomul (ρ m)).symm

private theorem coactionCodRestrict_counit_comp (X : RightComodule K C M)
    (D : _root_.Subcoalgebra K C)
    (h : ∀ m : M, X.coaction m ∈ LinearMap.range (D.subtype.toLinearMap.lTensor M)) :
    (counit (R := K) (A := D)).lTensor M ∘ₗ X.coactionCodRestrict D h =
      (TensorProduct.rid K M).symm.toLinearMap := by
  rw [← D.subtype.counit_comp, LinearMap.lTensor_comp, LinearMap.comp_assoc,
    X.subtype_lTensor_comp_coactionCodRestrict D h]
  exact X.counit_comp

/-- The right comodule on the same module with coacting coalgebra corestricted to `D`. -/
noncomputable def restrictCoalgebra (X : RightComodule K C M)
    (D : _root_.Subcoalgebra K C)
    (h : ∀ m : M, X.coaction m ∈ LinearMap.range (D.subtype.toLinearMap.lTensor M)) :
    RightComodule K D M where
  coaction := X.coactionCodRestrict D h
  coassoc := by exact coactionCodRestrict_coassoc X D h
  counit_comp := by exact coactionCodRestrict_counit_comp X D h

/-- The coaction of the corestricted comodule is the specified linear lift. -/
@[simp] theorem restrictCoalgebra_coaction (X : RightComodule K C M)
    (D : _root_.Subcoalgebra K C)
    (h : ∀ m : M, X.coaction m ∈ LinearMap.range (D.subtype.toLinearMap.lTensor M)) :
    (X.restrictCoalgebra D h).coaction = X.coactionCodRestrict D h :=
  rfl

/-- The coaction of the corestricted comodule maps to the original coaction under inclusion. -/
theorem subtype_lTensor_comp_restrictCoalgebra_coaction (X : RightComodule K C M)
    (D : _root_.Subcoalgebra K C)
    (h : ∀ m : M, X.coaction m ∈ LinearMap.range (D.subtype.toLinearMap.lTensor M)) :
    D.subtype.toLinearMap.lTensor M ∘ₗ (X.restrictCoalgebra D h).coaction = X.coaction :=
  X.subtype_lTensor_comp_coactionCodRestrict D h

/-- The coacting coalgebra has a unique corestriction to `D` precisely when the
coefficient span is contained in its underlying submodule, as in the classical
coefficient-coalgebra construction from Sweedler's *Hopf Algebras*. -/
theorem existsUnique_restrictCoalgebra_iff (X : RightComodule K C M)
    (D : _root_.Subcoalgebra K C) :
    (∃! Y : RightComodule K D M, D.subtype.toLinearMap.lTensor M ∘ₗ Y.coaction =
      X.coaction) ↔ X.coefficientSpan ≤ D.toSubmodule := by
  constructor
  · rintro ⟨Y, hY, _⟩
    apply (X.coaction_mem_range_iff_coefficientSpan_le D).mp
    intro m
    exact ⟨Y.coaction m, LinearMap.congr_fun hY m⟩
  · intro h
    have hρ := (X.coaction_mem_range_iff_coefficientSpan_le D).mpr h
    refine ⟨X.restrictCoalgebra D hρ,
      X.subtype_lTensor_comp_restrictCoalgebra_coaction D hρ, ?_⟩
    intro Y hY
    apply Coalgebra.RightComodule.ext
    apply LinearMap.ext
    intro m
    have hinj : Function.Injective (D.subtype.toLinearMap.lTensor M) := by
      let : AddCommGroup M := Module.addCommMonoidToAddCommGroup K (M := M)
      exact Module.Flat.lTensor_preserves_injective_linearMap
        (R := K) (M := M) D.subtype.toLinearMap D.subtype_injective
    apply hinj
    exact (LinearMap.congr_fun hY m).trans
      (X.subtype_lTensor_coactionCodRestrict D hρ m).symm

/-- The original module as a right comodule over its coefficient subcoalgebra. -/
noncomputable def coefficientComodule (X : RightComodule K C M) :
    RightComodule K X.coefficientSubcoalgebra M :=
  X.restrictCoalgebra X.coefficientSubcoalgebra
    ((X.coaction_mem_range_iff_coefficientSpan_le X.coefficientSubcoalgebra).mpr le_rfl)

/-- Inclusion of the coefficient subcoalgebra intertwines the two coactions. -/
theorem subtype_lTensor_comp_coefficientComodule_coaction (X : RightComodule K C M) :
    X.coefficientSubcoalgebra.subtype.toLinearMap.lTensor M ∘ₗ
        X.coefficientComodule.coaction = X.coaction :=
  X.subtype_lTensor_comp_restrictCoalgebra_coaction X.coefficientSubcoalgebra _

/-- The coefficient-comodule inclusion equation evaluated at an element. -/
@[simp] theorem subtype_lTensor_coefficientComodule_coaction
    (X : RightComodule K C M) (m : M) :
    X.coefficientSubcoalgebra.subtype.toLinearMap.lTensor M
      (X.coefficientComodule.coaction m) = X.coaction m :=
  LinearMap.congr_fun X.subtype_lTensor_comp_coefficientComodule_coaction m

/-- A module-finite right comodule has a finitely generated coefficient subcoalgebra.
This is the finite-comodule coefficient theorem from Sweedler's *Hopf Algebras*. -/
theorem coefficientSubcoalgebra_fg [Module.Finite K M] (X : RightComodule K C M) :
    X.coefficientSubcoalgebra.toSubmodule.FG := by
  simpa only [coefficientSubcoalgebra_toSubmodule] using coefficientSpan_fg X

example (X : RightComodule K C M) :
    ∃ Y : RightComodule K X.coefficientSubcoalgebra M,
      X.coefficientSubcoalgebra.subtype.toLinearMap.lTensor M ∘ₗ Y.coaction = X.coaction :=
  ⟨X.coefficientComodule, X.subtype_lTensor_comp_coefficientComodule_coaction⟩

end Field

end Coalgebra.RightComodule
