/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.RightComodule
public import Mathlib.Algebra.Module.Submodule.EqLocus
public import Mathlib.Order.SupIndep
public import Mathlib.RingTheory.Coalgebra.GroupLike

/-!
# Weight spaces of specified right comodules

For a specified right comodule `X` and any coalgebra element `c`, the weight
space consists of the vectors whose coaction is `v ↦ v ⊗ c`. The definition
does not require `c` to be group-like or assert that its weight space is nonzero.

The construction uses Mathlib's equalizer submodule and the existing
`Coalgebra.RightComodule` formalization. The regular weight-space inverse
relations and independence statement use Mathlib's bundled `GroupLike` elements.
The weight-space and regular-occurrence viewpoints are motivated by Milne's treatment
in §§4.22–4.26. Here the coalgebra and coaction are specified directly; an
algebraic-group or character dictionary is not part of the construction.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§4.22–4.26.
-/

@[expose] public section

universe u v w z

open scoped TensorProduct

namespace Coalgebra.RightComodule

section CommSemiring

variable {R : Type u} {C : Type v} {V : Type w}
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid V] [Module R V]

/-- The vectors with coaction `v ↦ v ⊗ c`, for a specified coalgebra element `c`. -/
def weightSpace (X : RightComodule R C V) (c : C) : Submodule R V :=
  LinearMap.eqLocus X.coaction ((TensorProduct.mk R V C).flip c)

/-- Membership in a weight space is the corresponding coaction equation. -/
@[simp] theorem mem_weightSpace (X : RightComodule R C V) (c : C) {v : V} :
    v ∈ X.weightSpace c ↔ X.coaction v = v ⊗ₜ[R] c :=
  Iff.rfl

/-- The coaction equation for an element of a weight space. -/
theorem coaction_weightSpace (X : RightComodule R C V) (c : C) (v : X.weightSpace c) :
    X.coaction (v : V) = (v : V) ⊗ₜ[R] c :=
  (mem_weightSpace X c).mp v.property

/-- The counit and scalar multiplication satisfy the inverse relations on a regular weight space.

For the motivating regular-weight viewpoint, see Milne, *Algebraic Groups* (2017), §§4.22–4.26.
The equations here concern a specified coalgebra coaction. -/
theorem regular_weightSpace_inverse (g : GroupLike R C) :
    (∀ r : R, counit (R := R) (r • g.val) = r) ∧
      (∀ v : (regular R C).weightSpace g.val,
        (counit (R := R) (v : C)) • g.val = (v : C)) := by
  constructor
  · intro r
    rw [map_smul, g.isGroupLikeElem_val.counit_eq_one, smul_eq_mul, mul_one]
  · intro v
    have hv : comul (R := R) (v : C) = (v : C) ⊗ₜ[R] g.val :=
      coaction_weightSpace (regular R C) g.val v
    have h := congrArg
      (fun t : C ⊗[R] C ↦
        TensorProduct.lid R C ((counit (R := R) (A := C)).rTensor C t)) hv
    simpa only [Coalgebra.rTensor_counit_comul, LinearMap.rTensor_tmul,
      TensorProduct.lid_tmul, one_smul] using h.symm

end CommSemiring

section Field

variable {k : Type u} {C : Type v} {V : Type w}
variable [Field k] [AddCommMonoid C] [Module k C] [Coalgebra k C]
variable [AddCommMonoid V] [Module k V]

/-- The weight submodules indexed by group-like elements are independent over a field.

For the motivating weight-space independence, see Milne, *Algebraic Groups* (2017), §§4.22–4.26.
The statement here concerns a specified coalgebra coaction. -/
theorem iSupIndep_weightSpace (X : RightComodule k C V) :
    iSupIndep (fun g : GroupLike k C ↦ X.weightSpace g.val) := by
  classical
  let : AddCommGroup C := Module.addCommMonoidToAddCommGroup k
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup k
  let L : (GroupLike k C →₀ k) →ₗ[k] C :=
    Finsupp.linearCombination k (fun g : GroupLike k C ↦ g.val)
  have hL : Function.Injective L := linearIndep_groupLikeVal
  have hT : Function.Injective (L.lTensor V) :=
    Module.Flat.lTensor_preserves_injective_linearMap L hL
  apply (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).2
  intro s f hf hsum g hg
  have hco : (∑ i ∈ s, f i ⊗ₜ[k] i.val) = 0 := by
    calc
      (∑ i ∈ s, f i ⊗ₜ[k] i.val) = ∑ i ∈ s, X.coaction (f i) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact ((mem_weightSpace X i.val).mp (hf i hi)).symm
      _ = X.coaction (∑ i ∈ s, f i) := (map_sum X.coaction f s).symm
      _ = 0 := by rw [hsum, map_zero]
  have ht : (∑ i ∈ s, f i ⊗ₜ[k] Finsupp.single i (1 : k)) = 0 := by
    apply hT
    simpa only [map_sum, LinearMap.lTensor_tmul, L,
      Finsupp.linearCombination_single, one_smul, map_zero] using hco
  have he := congrArg
    (fun t ↦ TensorProduct.finsuppScalarRight k k V (GroupLike k C) t g) ht
  simpa [map_sum, Finsupp.finsetSum_apply, Finsupp.single_apply, ite_smul, hg] using he

end Field

end Coalgebra.RightComodule

namespace Coalgebra.RightComoduleHom

open Coalgebra.RightComodule

variable {R : Type u} {C : Type v} {V : Type w}
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid V] [Module R V]

/-- A right-comodule morphism preserves each specified weight space. -/
theorem map_mem_weightSpace {W : Type z} [AddCommMonoid W] [Module R W]
    {X : RightComodule R C V} {Y : RightComodule R C W}
    (f : RightComoduleHom X Y) (c : C) {v : V} (hv : v ∈ X.weightSpace c) :
    f v ∈ Y.weightSpace c := by
  rw [mem_weightSpace] at hv ⊢
  simpa only [hv, LinearMap.rTensor_tmul, RightComoduleHom.toLinearMap_apply] using
    f.colinear_apply v

end Coalgebra.RightComoduleHom
