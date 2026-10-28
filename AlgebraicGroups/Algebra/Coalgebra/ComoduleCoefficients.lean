/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.RightComodule
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Adjoin
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Finite
public import AlgebraicGroups.Algebra.Coalgebra.Subcoalgebra.Hom
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Coefficient coalgebras of right comodules

For a specified right coact `X` of a coalgebra `C` on a module `M`, a
coefficient is obtained by evaluating a linear functional on the first tensor
factor of `X.coact m`. The coefficient span uses all linear functionals on
`M` and all elements of `M`; no basis or finite-generation hypothesis is part
of its definition. Coefficients and their span are defined over a commutative
semiring. Under a right-comodule morphism, coefficients pull back along the
underlying linear map. Surjections decrease coefficient spans, bijections
preserve them, and over a field injections increase them, since linear
functionals extend from subspaces. The corresponding statements hold for the
underlying submodules of coefficient subcoalgebras.

Over a field, `coefficientSubcoalgebra` has exactly this coefficient span as its
underlying submodule. Corestriction of the coacting coalgebra uses the tensor
inclusion `M ⊗ D → M ⊗ C`, rather than a comodule morphism with a fixed coacting
coalgebra. The inclusion equation characterizes the corestricted coact.
Changing this corestricted coacting coalgebra back along its inclusion recovers
the original specified comodule.
The coefficient span is contained in the underlying submodule of `D` exactly
when the coact factors through this tensor inclusion.

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

open TauCeti
open Coalgebra


universe u v w

open scoped TensorProduct

namespace TauCeti.Comodule.Hom

section CommSemiring

variable {K : Type u} {C : Type v} {M : Type w} {N : Type*}
variable [CommSemiring K] [AddCommMonoid C] [Module K C] [Coalgebra K C]
variable [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
variable {X : Comodule K C M} {Y : Comodule K C N}

/-- A bijective comodule morphism preserves the coefficient span; its inverse
linear map pulls every source functional back to the target. -/
theorem coefficientSpan_eq_of_bijective (f : (@Hom K C M N _ _ _ _ _ _ X _ _ Y))
    (hf : Function.Bijective f) : (@matrixCoefficientSubmodule K C M _ _ _ _ _ _ X) =
      (@matrixCoefficientSubmodule K C N _ _ _ _ _ _ Y) := by
  classical
  let e : M ≃ₗ[K] N := LinearEquiv.ofBijective f.toLinearMap hf
  apply le_antisymm
  · apply (@matrixCoefficientSubmodule_le_iff K C M _ _ _ _ _ _ X _).mpr
    intro ell m
    have hcomp : (ell.comp e.symm.toLinearMap).comp f.toLinearMap = ell := by
      ext x
      exact congrArg ell (e.symm_apply_apply x)
    have h := (@matrixCoefficient_mem_submodule K C N _ _ _ _ _ _ Y) (ell.comp
      e.symm.toLinearMap) (f m)
    rw [matrixCoefficient_map f, hcomp] at h
    exact h
  · exact matrixCoefficientSubmodule_le_of_surjective f hf.surjective

end CommSemiring

section FieldCore

variable {K : Type u} {C : Type v} {M : Type w} {N : Type*}
variable [Field K] [AddCommMonoid C] [Module K C] [Coalgebra K C]
variable [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
variable {X : Comodule K C M} {Y : Comodule K C N}

/-- An injective comodule morphism over a field increases the coefficient span.
Injectivity lets each source functional extend to the target; coefficients on
vectors in a kernel need not survive a noninjective map. -/
theorem coefficientSpan_le_of_injective (f : (@Hom K C M N _ _ _ _ _ _ X _ _ Y))
    (hf : Function.Injective f) : (@matrixCoefficientSubmodule K C M _ _ _ _ _ _ X) ≤
      (@matrixCoefficientSubmodule K C N _ _ _ _ _ _ Y) := by
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup K
  let : AddCommGroup N := Module.addCommMonoidToAddCommGroup K
  apply (@matrixCoefficientSubmodule_le_iff K C M _ _ _ _ _ _ X _).mpr
  intro ell m
  obtain ⟨eta, heta⟩ :=
    LinearMap.dualMap_surjective_of_injective (f := f.toLinearMap) hf ell
  have hcomp : eta.comp f.toLinearMap = ell := by
    simpa only [LinearMap.dualMap_apply'] using heta
  have h := (@matrixCoefficient_mem_submodule K C N _ _ _ _ _ _ Y) eta (f m)
  rw [matrixCoefficient_map f, hcomp] at h
  exact h

end FieldCore

end TauCeti.Comodule.Hom

namespace TauCeti.Comodule

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


section Field

variable {K : Type u} {C : Type v} {M : Type w}
variable [Field K] [AddCommGroup C] [Module K C] [Coalgebra K C]
variable [AddCommMonoid M] [Module K M]

-- Contract the first factor of right-coact coassociativity. The two
-- comparison maps are checked on pure tensors, keeping the coalgebra factors
-- in their original order.
private theorem comul_coefficient_eq_rTensor (X : Comodule K C M)
    (ell : M →ₗ[K] K) (m : M) :
    comul (R := K) ((@matrixCoefficient K C M _ _ _ _ _ _ X) ell m) =
      (((TensorProduct.lid K C).toLinearMap ∘ₗ ell.rTensor C) ∘ₗ
        X.coact).rTensor C (X.coact m) := by
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
    comul (R := K) ((@matrixCoefficient K C M _ _ _ _ _ _ X) ell m) =
        q₂ ((comul (R := K)).lTensor M (X.coact m)) :=
      LinearMap.congr_fun hΔ (X.coact m)
    _ = q₂ (TensorProduct.assoc K M C C (X.coact.rTensor C (X.coact m))) := by
      rw [(@Comodule.coassoc_apply K C M _ _ _ _ _ _ X)]
    _ = q.rTensor C (X.coact.rTensor C (X.coact m)) :=
      LinearMap.congr_fun ha _
    _ = (q ∘ₗ X.coact).rTensor C (X.coact m) :=
      (LinearMap.rTensor_comp_apply (M := C) (g := q) (f := X.coact)
        (X.coact m)).symm

private theorem coefficientSpan_comul_mem (X : Comodule K C M)
    {c : C} (hc : c ∈ (@matrixCoefficientSubmodule K C M _ _ _ _ _ _ X)) :
    comul (R := K) c ∈ LinearMap.range
      (TensorProduct.mapIncl (@matrixCoefficientSubmodule K C M _ _ _ _ _ _ X)
        (@matrixCoefficientSubmodule K C M _ _ _ _ _ _ X)) := by
  classical
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup K (M := M)
  have hS : (@matrixCoefficientSubmodule K C M _ _ _ _ _ _ X) ≤
      (LinearMap.range (TensorProduct.mapIncl (@matrixCoefficientSubmodule K C M _ _ _ _ _ _ X)
        (@matrixCoefficientSubmodule K C M _ _ _ _ _ _ X))).comap
        (comul (R := K)) := by
    apply (@matrixCoefficientSubmodule_le_iff K C M _ _ _ _ _ _ X _).mpr
    intro ell m
    change comul (R := K) ((@matrixCoefficient K C M _ _ _ _ _ _ X) ell m) ∈ LinearMap.range
      (TensorProduct.mapIncl (@matrixCoefficientSubmodule K C M _ _ _ _ _ _ X)
        (@matrixCoefficientSubmodule K C M _ _ _ _ _ _ X))
    let b := Module.Basis.ofVectorSpace K M
    let f := TensorProduct.equivFinsuppOfBasisLeft b (X.coact m)
    have hf (i : Module.Basis.ofVectorSpaceIndex K M) :
        f i = (@matrixCoefficient K C M _ _ _ _ _ _ X) (b.coord i) m :=
      TensorProduct.equivFinsuppOfBasisLeft_apply b (X.coact m) i
    have hρ : f.sum (fun i c => b i ⊗ₜ[K] c) = X.coact m := by
      simpa only [TensorProduct.equivFinsuppOfBasisLeft_symm_apply] using
        (TensorProduct.equivFinsuppOfBasisLeft b).symm_apply_apply (X.coact m)
    let T := (((TensorProduct.lid K C).toLinearMap ∘ₗ ell.rTensor C) ∘ₗ
      X.coact).rTensor C
    have hΔ : comul (R := K) ((@matrixCoefficient K C M _ _ _ _ _ _ X) ell m) =
        ∑ i ∈ f.support, (@matrixCoefficient K C M _ _ _ _ _ _ X) ell (b i) ⊗ₜ[K] f i := by
      calc
        comul (R := K) ((@matrixCoefficient K C M _ _ _ _ _ _ X) ell m) = T (X.coact m) :=
          comul_coefficient_eq_rTensor X ell m
        _ = T (f.sum (fun i c => b i ⊗ₜ[K] c)) := congrArg T hρ.symm
        _ = ∑ i ∈ f.support, (@matrixCoefficient K C M _ _ _ _ _ _ X) ell (b i) ⊗ₜ[K] f i := by
          simp [T, Finsupp.sum, map_sum, matrixCoefficient_def, LinearMap.rTensor_def]
    rw [hΔ]
    apply Submodule.sum_mem
    intro i hi
    exact ⟨(⟨(@matrixCoefficient K C M _ _ _ _ _ _ X) ell (b i),
      (@matrixCoefficient_mem_submodule K C M _ _ _ _ _ _ X) ell (b i)⟩ :
        (@matrixCoefficientSubmodule K C M _ _ _ _ _ _ X)) ⊗ₜ[K]
      (⟨f i, by
        rw [hf i]
        exact (@matrixCoefficient_mem_submodule K C M _ _ _ _ _ _ X) (b.coord i) m⟩ :
        (@matrixCoefficientSubmodule K C M _ _ _ _ _ _ X)), rfl⟩
  exact hS hc

/-- The coefficient subcoalgebra, with underlying submodule the all-dual coefficient span. -/
def coefficientSubcoalgebra (X : Comodule K C M) : TauCeti.Subcoalgebra K C :=
  TauCeti.Subcoalgebra.ofSubmodule (@matrixCoefficientSubmodule K C M _ _ _ _ _ _ X) (by
    intro c hc
    exact coefficientSpan_comul_mem X hc)

/-- The carrier of the coefficient subcoalgebra is exactly the coefficient span. -/
@[simp] theorem coefficientSubcoalgebra_toSubmodule (X : Comodule K C M) :
    X.coefficientSubcoalgebra.toSubmodule = (@matrixCoefficientSubmodule K C M _ _ _ _ _ _ X) :=
  rfl

/-- The underlying submodule is the span of the exact range of coefficient evaluation. -/
theorem coefficientSubcoalgebra_toSubmodule_eq_span_range (X : Comodule K C M) :
    X.coefficientSubcoalgebra.toSubmodule =
      Submodule.span K (Set.range (Function.uncurry (@matrixCoefficient K C M _ _ _ _ _ _ X))) :=
  rfl

/-- Membership in the coefficient subcoalgebra is membership in the coefficient span. -/
@[simp] theorem mem_coefficientSubcoalgebra (X : Comodule K C M) (c : C) :
    c ∈ X.coefficientSubcoalgebra ↔ c ∈ (@matrixCoefficientSubmodule K C M _ _ _ _ _ _ X) :=
  Iff.rfl

/-- Every coefficient belongs to the coefficient subcoalgebra. -/
theorem coefficient_mem_coefficientSubcoalgebra (X : Comodule K C M)
    (ell : M →ₗ[K] K) (m : M) : (@matrixCoefficient K C M _ _ _ _ _ _ X) ell m ∈
      X.coefficientSubcoalgebra :=
  (@matrixCoefficient_mem_submodule K C M _ _ _ _ _ _ X) ell m

/-- A coact takes values in `M ⊗ D` exactly when its coefficient span is
contained in the underlying submodule of `D`. -/
theorem coact_mem_range_iff_coefficientSpan_le (X : Comodule K C M)
    (D : TauCeti.Subcoalgebra K C) :
    (∀ m : M, X.coact m ∈ LinearMap.range (D.subtype.toLinearMap.lTensor M)) ↔
      (@matrixCoefficientSubmodule K C M _ _ _ _ _ _ X) ≤ D.toSubmodule := by
  constructor
  · intro h
    apply (@matrixCoefficientSubmodule_le_iff K C M _ _ _ _ _ _ X D.toSubmodule).mpr
    intro ell m
    exact (tensor_mem_range_lTensor_iff D.toSubmodule (X.coact m)).mp (h m) ell
  · intro h m
    apply (tensor_mem_range_lTensor_iff D.toSubmodule (X.coact m)).mpr
    intro ell
    exact (@matrixCoefficientSubmodule_le_iff K C M _ _ _ _ _ _ X D.toSubmodule).mp h ell m

/-- The linear corestriction of a coact through the tensor inclusion of a subcoalgebra. -/
noncomputable def coactCodRestrict (X : Comodule K C M)
    (D : TauCeti.Subcoalgebra K C)
    (h : ∀ m : M, X.coact m ∈ LinearMap.range (D.subtype.toLinearMap.lTensor M)) :
    M →ₗ[K] M ⊗[K] D.toSubmodule :=
  X.coact.codLift (D.subtype.toLinearMap.lTensor M)
    (by
      let : AddCommGroup M := Module.addCommMonoidToAddCommGroup K (M := M)
      exact Module.Flat.lTensor_preserves_injective_linearMap
        (R := K) (M := M) D.subtype.toLinearMap D.subtype_injective) h

/-- Tensor inclusion after linear corestriction recovers the original coact. -/
theorem subtype_lTensor_comp_coactCodRestrict (X : Comodule K C M)
    (D : TauCeti.Subcoalgebra K C)
    (h : ∀ m : M, X.coact m ∈ LinearMap.range (D.subtype.toLinearMap.lTensor M)) :
    D.subtype.toLinearMap.lTensor M ∘ₗ X.coactCodRestrict D h = X.coact :=
  LinearMap.comp_codLift _ _ _ _

/-- The corestricted linear coact satisfies the inclusion equation at each element. -/
@[simp] theorem subtype_lTensor_coactCodRestrict (X : Comodule K C M)
    (D : TauCeti.Subcoalgebra K C)
    (h : ∀ m : M, X.coact m ∈ LinearMap.range (D.subtype.toLinearMap.lTensor M))
    (m : M) :
    DFunLike.coe (F := M ⊗[K] D.toSubmodule →ₗ[K] M ⊗[K] C)
      (α := M ⊗[K] D.toSubmodule) (β := fun _ => M ⊗[K] C)
      (D.toSubmodule.subtype.lTensor (N := D.toSubmodule) M) (X.coactCodRestrict D h m) = X.coact
        m :=
  LinearMap.congr_fun (X.subtype_lTensor_comp_coactCodRestrict D h) m

private theorem coactCodRestrict_coassoc (X : Comodule K C M)
    (D : TauCeti.Subcoalgebra K C)
    (h : ∀ m : M, X.coact m ∈ LinearMap.range (D.subtype.toLinearMap.lTensor M)) :
    TensorProduct.assoc K M D.toSubmodule D.toSubmodule ∘ₗ (X.coactCodRestrict D h).rTensor
      D.toSubmodule ∘ₗ
        X.coactCodRestrict D h =
      (comul (R := K) (A := D.toSubmodule)).lTensor M ∘ₗ X.coactCodRestrict D h := by
  let ρ : M →ₗ[K] M ⊗[K] D.toSubmodule := X.coactCodRestrict D h
  have hρ : D.subtype.toLinearMap.lTensor M ∘ₗ ρ = X.coact :=
    X.subtype_lTensor_comp_coactCodRestrict D h
  have hρ_apply (m : M) : D.subtype.toLinearMap.lTensor M (ρ m) = X.coact m :=
    LinearMap.congr_fun hρ m
  have hρ_tensor :
      TensorProduct.map (D.subtype.toLinearMap.lTensor M) D.subtype.toLinearMap ∘ₗ
          ρ.rTensor D.toSubmodule =
        X.coact.rTensor C ∘ₗ D.subtype.toLinearMap.lTensor M := by
    rw [LinearMap.map_comp_rTensor, hρ, LinearMap.rTensor_comp_lTensor]
  have hcomul :
      (TensorProduct.map D.subtype.toLinearMap D.subtype.toLinearMap).lTensor M ∘ₗ
          (comul (R := K) (A := D.toSubmodule)).lTensor M =
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
        (TensorProduct.assoc K M D.toSubmodule D.toSubmodule (ρ.rTensor D.toSubmodule (ρ m))) =
        TensorProduct.assoc K M C C
          (TensorProduct.map (D.subtype.toLinearMap.lTensor M) D.subtype.toLinearMap
            (ρ.rTensor D.toSubmodule (ρ m))) :=
      TensorProduct.map_map_assoc (LinearMap.id : M →ₗ[K] M)
        D.subtype.toLinearMap D.subtype.toLinearMap _
    _ = TensorProduct.assoc K M C C
        (X.coact.rTensor C (D.subtype.toLinearMap.lTensor M (ρ m))) :=
      congrArg (TensorProduct.assoc K M C C) (LinearMap.congr_fun hρ_tensor (ρ m))
    _ = TensorProduct.assoc K M C C (X.coact.rTensor C (X.coact m)) := by
      rw [hρ_apply]
    _ = (comul (R := K) (A := C)).lTensor M (X.coact m) := (@Comodule.coassoc_apply K C M _ _ _ _
      _ _ X) m
    _ = (comul (R := K) (A := C)).lTensor M
        (D.subtype.toLinearMap.lTensor M (ρ m)) := by rw [hρ_apply]
    _ = (TensorProduct.map D.subtype.toLinearMap D.subtype.toLinearMap).lTensor M
        ((comul (R := K) (A := D.toSubmodule)).lTensor M (ρ m)) :=
      (LinearMap.congr_fun hcomul (ρ m)).symm

private theorem coactCodRestrict_counit_comp (X : Comodule K C M)
    (D : TauCeti.Subcoalgebra K C)
    (h : ∀ m : M, X.coact m ∈ LinearMap.range (D.subtype.toLinearMap.lTensor M)) :
    (counit (R := K) (A := D.toSubmodule)).lTensor M ∘ₗ X.coactCodRestrict D h =
      (TensorProduct.rid K M).symm.toLinearMap := by
  rw [← D.subtype.counit_comp, LinearMap.lTensor_comp, LinearMap.comp_assoc,
    X.subtype_lTensor_comp_coactCodRestrict D h]
  exact X.lTensor_counit_comp_coact

/-- The right comodule on the same module with coacting coalgebra corestricted to `D`. -/
@[instance_reducible] noncomputable def restrictCoalgebra (X : Comodule K C M)
    (D : TauCeti.Subcoalgebra K C)
    (h : ∀ m : M, X.coact m ∈ LinearMap.range (D.subtype.toLinearMap.lTensor M)) :
    Comodule K D.toSubmodule M where
  coact := X.coactCodRestrict D h
  coassoc := by exact coactCodRestrict_coassoc X D h
  lTensor_counit_comp_coact := by exact coactCodRestrict_counit_comp X D h

/-- The coact of the corestricted comodule is the specified linear lift. -/
@[simp] theorem restrictCoalgebra_coact (X : Comodule K C M)
    (D : TauCeti.Subcoalgebra K C)
    (h : ∀ m : M, X.coact m ∈ LinearMap.range (D.subtype.toLinearMap.lTensor M)) :
    (X.restrictCoalgebra D h).coact = X.coactCodRestrict D h :=
  rfl

/-- The coact of the corestricted comodule maps to the original coact under inclusion. -/
theorem subtype_lTensor_comp_restrictCoalgebra_coact (X : Comodule K C M)
    (D : TauCeti.Subcoalgebra K C)
    (h : ∀ m : M, X.coact m ∈ LinearMap.range (D.subtype.toLinearMap.lTensor M)) :
    D.subtype.toLinearMap.lTensor M ∘ₗ (X.restrictCoalgebra D h).coact = X.coact :=
  X.subtype_lTensor_comp_coactCodRestrict D h

/-- The coacting coalgebra has a unique corestriction to `D` precisely when the
coefficient span is contained in its underlying submodule, as in the classical
coefficient-coalgebra construction from Sweedler's *Hopf Algebras*. -/
theorem existsUnique_restrictCoalgebra_iff (X : Comodule K C M)
    (D : TauCeti.Subcoalgebra K C) :
    (∃! Y : Comodule K D.toSubmodule M, D.subtype.toLinearMap.lTensor M ∘ₗ Y.coact =
      X.coact) ↔ (@matrixCoefficientSubmodule K C M _ _ _ _ _ _ X) ≤ D.toSubmodule := by
  constructor
  · rintro ⟨Y, hY, _⟩
    apply (X.coact_mem_range_iff_coefficientSpan_le D).mp
    intro m
    exact ⟨Y.coact m, LinearMap.congr_fun hY m⟩
  · intro h
    have hρ := (X.coact_mem_range_iff_coefficientSpan_le D).mpr h
    refine ⟨X.restrictCoalgebra D hρ,
      X.subtype_lTensor_comp_restrictCoalgebra_coact D hρ, ?_⟩
    intro Y hY
    apply TauCeti.Comodule.ext
    apply LinearMap.ext
    intro m
    have hinj : Function.Injective (D.subtype.toLinearMap.lTensor M) := by
      let : AddCommGroup M := Module.addCommMonoidToAddCommGroup K (M := M)
      exact Module.Flat.lTensor_preserves_injective_linearMap
        (R := K) (M := M) D.subtype.toLinearMap D.subtype_injective
    apply hinj
    exact (LinearMap.congr_fun hY m).trans
      (X.subtype_lTensor_coactCodRestrict D hρ m).symm

/-- The original module as a right comodule over its coefficient subcoalgebra. -/
@[instance_reducible] noncomputable def coefficientComodule (X : Comodule K C M) :
    Comodule K X.coefficientSubcoalgebra.toSubmodule M :=
  X.restrictCoalgebra X.coefficientSubcoalgebra
    ((X.coact_mem_range_iff_coefficientSpan_le X.coefficientSubcoalgebra).mpr le_rfl)

/-- Inclusion of the coefficient subcoalgebra intertwines the two coacts. -/
theorem subtype_lTensor_comp_coefficientComodule_coact (X : Comodule K C M) :
    X.coefficientSubcoalgebra.subtype.toLinearMap.lTensor M ∘ₗ
        X.coefficientComodule.coact = X.coact :=
  X.subtype_lTensor_comp_restrictCoalgebra_coact X.coefficientSubcoalgebra _

/-- The coefficient-comodule inclusion equation evaluated at an element. -/
theorem subtype_lTensor_coefficientComodule_coact
    (X : Comodule K C M) (m : M) :
    DFunLike.coe (F := M ⊗[K] (@matrixCoefficientSubmodule K C M _ _ _ _ _ _ X) →ₗ[K] M ⊗[K] C)
      (α := M ⊗[K] (@matrixCoefficientSubmodule K C M _ _ _ _ _ _ X)) (β := fun _ => M ⊗[K] C)
      ((@matrixCoefficientSubmodule K C M _ _ _ _ _ _ X).subtype.lTensor (N :=
        (@matrixCoefficientSubmodule K C M _ _ _ _ _ _ X)) M)
      (X.coefficientComodule.coact m) = X.coact m :=
  LinearMap.congr_fun X.subtype_lTensor_comp_coefficientComodule_coact m

/-- A module-finite right comodule has a finitely generated coefficient subcoalgebra.
This is the finite-comodule coefficient theorem from Sweedler's *Hopf Algebras*. -/
theorem coefficientSubcoalgebra_fg [Module.Finite K M] (X : Comodule K C M) :
    X.coefficientSubcoalgebra.toSubmodule.FG := by
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup K (M := M)
  let := X
  rw [coefficientSubcoalgebra_toSubmodule]
  exact Module.Finite.iff_fg.mp inferInstance

example (X : Comodule K C M) :
    ∃ Y : Comodule K X.coefficientSubcoalgebra.toSubmodule M,
      X.coefficientSubcoalgebra.subtype.toLinearMap.lTensor M ∘ₗ Y.coact = X.coact :=
  ⟨X.coefficientComodule, X.subtype_lTensor_comp_coefficientComodule_coact⟩

/-- Changing the corestricted coacting coalgebra along its inclusion recovers the original
comodule. -/
@[simp] theorem mapCoalgebra_restrictCoalgebra (X : Comodule K C M)
    (D : TauCeti.Subcoalgebra K C)
    (h : ∀ m : M, X.coact m ∈ LinearMap.range (D.subtype.toLinearMap.lTensor M)) :
    (letI := X.restrictCoalgebra D h; Corestrict (M := M) D.subtype) = X := by
  apply TauCeti.Comodule.ext
  change D.subtype.toLinearMap.lTensor M ∘ₗ (X.restrictCoalgebra D h).coact = X.coact
  exact X.subtype_lTensor_comp_restrictCoalgebra_coact D h

end Field

end TauCeti.Comodule

namespace TauCeti.Comodule.Hom

section FieldCarrier

variable {K : Type u} {C : Type v} {M : Type w} {N : Type*}
variable [Field K] [AddCommGroup C] [Module K C] [Coalgebra K C]
variable [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
variable {X : Comodule K C M} {Y : Comodule K C N}

/-- A surjective comodule morphism decreases the underlying submodule of the
coefficient subcoalgebra, since every target vector has a source lift. -/
theorem coefficientSubcoalgebra_toSubmodule_le_of_surjective
    (f : (@Hom K C M N _ _ _ _ _ _ X _ _ Y)) (hf : Function.Surjective f) :
    Y.coefficientSubcoalgebra.toSubmodule ≤ X.coefficientSubcoalgebra.toSubmodule := by
  simpa only [Comodule.coefficientSubcoalgebra_toSubmodule] using
    matrixCoefficientSubmodule_le_of_surjective f hf

/-- A bijective comodule morphism preserves the coefficient subcoalgebra. -/
theorem coefficientSubcoalgebra_eq_of_bijective
    (f : (@Hom K C M N _ _ _ _ _ _ X _ _ Y)) (hf : Function.Bijective f) :
    X.coefficientSubcoalgebra = Y.coefficientSubcoalgebra := by
  apply TauCeti.Subcoalgebra.toSubmodule_injective
  simpa only [Comodule.coefficientSubcoalgebra_toSubmodule] using
    f.coefficientSpan_eq_of_bijective hf

/-- An injective comodule morphism over a field increases the underlying
submodule of the coefficient subcoalgebra, by extension of linear functionals. -/
theorem coefficientSubcoalgebra_toSubmodule_le_of_injective
    (f : (@Hom K C M N _ _ _ _ _ _ X _ _ Y)) (hf : Function.Injective f) :
    X.coefficientSubcoalgebra.toSubmodule ≤ Y.coefficientSubcoalgebra.toSubmodule := by
  simpa only [Comodule.coefficientSubcoalgebra_toSubmodule] using
    f.coefficientSpan_le_of_injective hf

end FieldCarrier

end TauCeti.Comodule.Hom
