/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.Components
public import Mathlib.Algebra.DirectSum.Module

/-!
# Weight decomposition along a group-like basis

For a given group-like basis of a coalgebra, the weight spaces of any specified
right comodule form an internal direct sum. The decomposition is the inverse of
the canonical summation map, and its coordinates are the finitely supported
vector components of the coaction.

The proof uses the component expansion and recovery theorems, together with
Mathlib's dependent finitely supported functions and canonical direct-sum maps.
Only the coalgebra has a given basis; no basis or flatness of the comodule is
required. The summands are indexed by this basis, not by all group-like elements.
-/

@[expose] public section

universe uR uC uV uI

open scoped BigOperators DirectSum

namespace Coalgebra.RightComodule

variable {R : Type uR} {C : Type uC} {V : Type uV} {I : Type uI}
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid V] [Module R V]
variable (X : Coalgebra.RightComodule R C V) (b : Module.Basis I R C)

attribute [local instance] Classical.propDecidable

private noncomputable def weightComponents
    (hb : ∀ i : I, IsGroupLikeElem R (b i)) (v : V) :
    ⨁ i, X.weightSpace (b i) :=
  DFinsupp.mk (X.components b v).support fun i =>
    ⟨X.components b v i.1, X.components_mem_weightSpace b hb v i.1⟩

private theorem weightComponents_apply
    (hb : ∀ i : I, IsGroupLikeElem R (b i)) (v : V) (i : I) :
    ((weightComponents X b hb v i : X.weightSpace (b i)) : V) =
      X.components b v i := by
  classical
  by_cases hi : i ∈ (X.components b v).support
  · simp only [weightComponents, DFinsupp.mk_of_mem hi]
  · simpa only [weightComponents, DFinsupp.mk_of_notMem hi, ZeroMemClass.coe_zero]
      using (Finsupp.notMem_support_iff.mp hi).symm

private noncomputable def weightComponentsLinear
    (hb : ∀ i : I, IsGroupLikeElem R (b i)) :
    V →ₗ[R] ⨁ i, X.weightSpace (b i) where
  toFun := weightComponents X b hb
  map_add' v w := by
    apply DirectSum.ext
    intro i
    apply Subtype.ext
    simpa only [DirectSum.add_apply, Submodule.coe_add, weightComponents_apply,
      Finsupp.add_apply] using
      congrArg (fun f : I →₀ V => f i) ((X.components b).map_add v w)
  map_smul' r v := by
    apply DirectSum.ext
    intro i
    apply Subtype.ext
    simpa only [DirectSum.smul_apply, Submodule.coe_smul, weightComponents_apply,
      Finsupp.smul_apply, RingHom.id_apply] using
      congrArg (fun f : I →₀ V => f i) ((X.components b).map_smul r v)

private theorem weightComponentsLinear_apply
    (hb : ∀ i : I, IsGroupLikeElem R (b i)) (v : V) :
    weightComponentsLinear X b hb v = weightComponents X b hb v := rfl

private theorem coeLinearMap_weightComponents
    (hb : ∀ i : I, IsGroupLikeElem R (b i)) (v : V) :
    DirectSum.coeLinearMap (fun i => X.weightSpace (b i))
      (weightComponents X b hb v) = v := by
  classical
  calc
    DirectSum.coeLinearMap (fun i => X.weightSpace (b i))
        (weightComponents X b hb v) =
        DFinsupp.sum (weightComponents X b hb v) (fun _ w => (w : V)) :=
      DirectSum.coeLinearMap_eq_dfinsuppSum _ _
    _ = ∑ i ∈ (X.components b v).support,
        ((weightComponents X b hb v i : X.weightSpace (b i)) : V) :=
      DFinsupp.sum_of_support_subset DFinsupp.support_mk_subset (fun _ _ => rfl)
    _ = (X.components b v).sum (fun _ w => w) := by
      simp only [Finsupp.sum, weightComponents_apply]
    _ = v := X.sum_components b hb v

private theorem weightComponents_coe
    (hb : ∀ i : I, IsGroupLikeElem R (b i)) (i : I) (w : X.weightSpace (b i)) :
    weightComponents X b hb (w : V) =
      DirectSum.lof R I (fun j => X.weightSpace (b j)) i w := by
  apply DirectSum.ext
  intro j
  apply Subtype.ext
  rw [weightComponents_apply]
  by_cases hij : i = j
  · subst j
    rw [X.components_apply_of_mem_weightSpace b w.property, DirectSum.lof_apply]
  · rw [X.components_apply_of_mem_weightSpace_ne b w.property hij,
      DirectSum.lof_eq_of,
      DirectSum.of_eq_of_ne (β := fun k => ↥(X.weightSpace (b k))) i j w
        (fun hji => hij (Eq.symm hji))]
    rfl

private theorem weightComponentsLinear_comp_coeLinearMap
    (hb : ∀ i : I, IsGroupLikeElem R (b i)) :
    (weightComponentsLinear X b hb).comp
        (DirectSum.coeLinearMap (fun i => X.weightSpace (b i))) =
      LinearMap.id := by
  apply DirectSum.linearMap_ext
  intro i
  apply LinearMap.ext
  intro w
  simpa only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof,
    weightComponentsLinear_apply, LinearMap.id_apply] using
    weightComponents_coe X b hb i w

/-- The weight spaces indexed by a given group-like basis form an internal
sum in any specified right comodule. -/
theorem isInternal_weightSpace (hb : ∀ i : I, IsGroupLikeElem R (b i)) :
    DirectSum.IsInternal (fun i => X.weightSpace (b i)) := by
  have hleft : Function.LeftInverse (weightComponents X b hb)
      (DirectSum.coeLinearMap (fun i => X.weightSpace (b i))) := by
    intro u
    simpa only [LinearMap.comp_apply, weightComponentsLinear_apply,
      LinearMap.id_apply] using
      DFunLike.congr_fun (weightComponentsLinear_comp_coeLinearMap X b hb) u
  have hright : Function.RightInverse (weightComponents X b hb)
      (DirectSum.coeLinearMap (fun i => X.weightSpace (b i))) :=
    coeLinearMap_weightComponents X b hb
  exact ⟨hleft.injective, hright.surjective⟩

/-- The canonical weight decomposition associated to a given group-like basis.
Its inverse is the canonical sum of the weight-space inclusions. -/
noncomputable def weightDecomposition (hb : ∀ i : I, IsGroupLikeElem R (b i)) :
    V ≃ₗ[R] ⨁ i, X.weightSpace (b i) :=
  (LinearEquiv.ofBijective (DirectSum.coeLinearMap (fun i => X.weightSpace (b i)))
    (X.isInternal_weightSpace b hb)).symm

/-- The inverse weight decomposition is the canonical summation linear map. -/
@[simp]
theorem weightDecomposition_symm (hb : ∀ i : I, IsGroupLikeElem R (b i)) :
    (X.weightDecomposition b hb).symm.toLinearMap =
      DirectSum.coeLinearMap (fun i => X.weightSpace (b i)) := rfl

/-- The inverse decomposition sums the inclusions of its weight coordinates. -/
theorem weightDecomposition_symm_apply (hb : ∀ i : I, IsGroupLikeElem R (b i))
    (u : ⨁ i, X.weightSpace (b i)) :
    (X.weightDecomposition b hb).symm u =
      DirectSum.coeLinearMap (fun i => X.weightSpace (b i)) u := rfl

/-- The ambient value of each decomposition coordinate is the corresponding
finite coaction component. -/
theorem weightDecomposition_apply (hb : ∀ i : I, IsGroupLikeElem R (b i))
    (v : V) (i : I) :
    ((X.weightDecomposition b hb v i : X.weightSpace (b i)) : V) =
      X.components b v i := by
  have heq : X.weightDecomposition b hb v = weightComponents X b hb v := by
    apply (X.weightDecomposition b hb).symm.injective
    rw [LinearEquiv.symm_apply_apply, weightDecomposition_symm_apply,
      coeLinearMap_weightComponents]
  rw [heq, weightComponents_apply]

/-- The inverse decomposition on a summand is its subtype inclusion. -/
@[simp]
theorem weightDecomposition_symm_lof (hb : ∀ i : I, IsGroupLikeElem R (b i))
    (i : I) (w : X.weightSpace (b i)) :
    (X.weightDecomposition b hb).symm
      (DirectSum.lof R I (fun j => X.weightSpace (b j)) i w) = (w : V) := by
  rw [weightDecomposition_symm_apply, DirectSum.coeLinearMap_lof]

/-- A vector in a basis weight space is its own coordinate at that weight. -/
theorem weightDecomposition_apply_of_mem_weightSpace
    (hb : ∀ i : I, IsGroupLikeElem R (b i)) {i : I} {v : V}
    (hv : v ∈ X.weightSpace (b i)) :
    X.weightDecomposition b hb v i = ⟨v, hv⟩ :=
  (X.isInternal_weightSpace b hb).ofBijective_coeLinearMap_of_mem hv

/-- A vector in one basis weight space has zero coordinates at other weights. -/
theorem weightDecomposition_apply_of_mem_weightSpace_ne
    (hb : ∀ i : I, IsGroupLikeElem R (b i)) {i j : I} {v : V}
    (hv : v ∈ X.weightSpace (b i)) (hij : i ≠ j) :
    X.weightDecomposition b hb v j = 0 :=
  (X.isInternal_weightSpace b hb).ofBijective_coeLinearMap_of_mem_ne hij hv

end Coalgebra.RightComodule
