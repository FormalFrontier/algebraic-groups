/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.RightComodule
public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.WeightSpace
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Coalgebra.GroupLike

/-!
# Components of a right comodule along a coalgebra basis

A basis of the coalgebra gives finitely supported vector-valued components of a
specified right coaction. Projection contracts the coalgebra factor on the right;
the inverse basis expansion reconstructs the coaction. When every basis vector is
group-like, each component has that vector as its coaction weight, and the finite
sum of the components recovers the original vector.

The component projections act as the identity on their own weight space and
vanish on the other basis weight spaces; hence they are idempotent and pairwise
orthogonal.

## References

The construction and characteristic formulas use Mathlib's
`TensorProduct.equivFinsuppOfBasisRight`, developed in the tensor-product basis
formalization by Jakob von Raumer. The group-like specialization is motivated by
comodule weight decompositions as in J. S. Milne, *Algebraic Groups* (2017),
§§4.22–4.26; here the group-like basis is given, over a commutative semiring.
-/

@[expose] public section

universe uR uC uV uI

open scoped TensorProduct

namespace Coalgebra.RightComodule

variable {R : Type uR} {C : Type uC} {V : Type uV} {I : Type uI}
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid V] [Module R V]
variable (X : Coalgebra.RightComodule R C V) (b : Module.Basis I R C)

/-- The finitely supported vector components of a right coaction along a basis
of its coalgebra, obtained by expanding the right tensor factor. -/
noncomputable def components : V →ₗ[R] (I →₀ V) :=
  letI : DecidableEq I := Classical.decEq I
  (TensorProduct.equivFinsuppOfBasisRight (M := V) b).toLinearMap ∘ₗ X.coaction

/-- A component is the contraction of the right coalgebra factor by its basis
coordinate, followed by the right unitor. -/
@[simp]
theorem components_apply (v : V) (i : I) :
    X.components b v i =
      TensorProduct.rid R V ((b.coord i).lTensor V (X.coaction v)) := by
  classical
  exact TensorProduct.equivFinsuppOfBasisRight_apply b (X.coaction v) i

/-- The finite basis expansion of the coaction in terms of its vector components. -/
theorem coaction_eq_sum_components_tmul (v : V) :
    X.coaction v = (X.components b v).sum (fun i w => w ⊗ₜ[R] b i) := by
  classical
  change X.coaction v =
    ((TensorProduct.equivFinsuppOfBasisRight (M := V) b) (X.coaction v)).sum _
  simpa only [TensorProduct.equivFinsuppOfBasisRight_symm_apply] using
    ((TensorProduct.equivFinsuppOfBasisRight (M := V) b).symm_apply_apply
      (X.coaction v)).symm

/-- Along a group-like basis, the coaction of a component is its tensor with the
corresponding basis vector. This is the raw component identity underlying comodule
weight decompositions (cf. Milne, *Algebraic Groups*, §§4.22–4.26). -/
theorem coaction_components (hb : ∀ i : I, IsGroupLikeElem R (b i)) (v : V) (i : I) :
    X.coaction (X.components b v i) = (X.components b v i) ⊗ₜ[R] b i := by
  classical
  let project : V ⊗[R] C →ₗ[R] V :=
    (TensorProduct.rid R V).toLinearMap ∘ₗ (b.coord i).lTensor V
  let contract : (V ⊗[R] C) ⊗[R] C →ₗ[R] V ⊗[R] C :=
    (TensorProduct.rid R (V ⊗[R] C)).toLinearMap ∘ₗ
      (b.coord i).lTensor (V ⊗[R] C)
  let weight : V →ₗ[R] V ⊗[R] C := (TensorProduct.mk R V C).flip (b i)
  have hproject : project (X.coaction v) = X.components b v i :=
    (X.components_apply b v i).symm
  -- Contracting the last factor commutes with the coaction on the first factor.
  have hnatural : contract ∘ₗ X.coaction.rTensor C = X.coaction ∘ₗ project := by
    ext w c
    simp [project, contract]
  -- On basis vectors, group-likeness makes the last-factor contraction diagonal.
  have hdiagonal :
      contract ∘ₗ (TensorProduct.assoc R V C C).symm.toLinearMap ∘ₗ
          (comul (R := R) (A := C)).lTensor V = weight ∘ₗ project := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro w
    apply b.ext
    intro j
    change contract ((TensorProduct.assoc R V C C).symm
      (w ⊗ₜ[R] comul (R := R) (b j))) = weight (project (w ⊗ₜ[R] b j))
    by_cases hji : j = i
    · subst j
      simp [contract, project, weight, (hb i).comul_eq_tmul_self]
    · simp [contract, project, weight, (hb j).comul_eq_tmul_self, hji]
  calc
    X.coaction (X.components b v i) = X.coaction (project (X.coaction v)) :=
      congrArg X.coaction hproject.symm
    _ = contract (X.coaction.rTensor C (X.coaction v)) :=
      (LinearMap.congr_fun hnatural (X.coaction v)).symm
    _ = contract ((TensorProduct.assoc R V C C).symm
        ((comul (R := R) (A := C)).lTensor V (X.coaction v))) :=
      congrArg contract (X.coassoc_symm_apply v).symm
    _ = weight (project (X.coaction v)) :=
      LinearMap.congr_fun hdiagonal (X.coaction v)
    _ = (X.components b v i) ⊗ₜ[R] b i := by rw [hproject]; rfl

/-- Along a group-like basis, the finite sum of the vector components is the
original vector, by the counit identity for a right comodule. -/
theorem sum_components (hb : ∀ i : I, IsGroupLikeElem R (b i)) (v : V) :
    (X.components b v).sum (fun _ w => w) = v := by
  classical
  let recover : V ⊗[R] C →ₗ[R] V :=
    (TensorProduct.rid R V).toLinearMap ∘ₗ (counit (R := R) (A := C)).lTensor V
  have recover_tmul (i : I) (w : V) : recover (w ⊗ₜ[R] b i) = w := by
    change TensorProduct.rid R V (w ⊗ₜ[R] counit (R := R) (b i)) = w
    rw [(hb i).counit_eq_one, TensorProduct.rid_tmul, one_smul]
  calc
    (X.components b v).sum (fun _ w => w) =
        recover ((X.components b v).sum (fun i w => w ⊗ₜ[R] b i)) := by
      rw [map_finsuppSum recover]
      simp only [recover_tmul]
    _ = recover (X.coaction v) :=
      congrArg recover (X.coaction_eq_sum_components_tmul b v).symm
    _ = v := X.rid_counit_coaction v

/-- Each component belongs to the weight space of its group-like basis vector. -/
theorem components_mem_weightSpace (hb : ∀ i : I, IsGroupLikeElem R (b i))
    (v : V) (i : I) : X.components b v i ∈ X.weightSpace (b i) :=
  (X.mem_weightSpace (b i)).mpr (X.coaction_components b hb v i)

private theorem components_apply_eq_smul_of_mem_weightSpace {i : I} {v : V}
    (hv : v ∈ X.weightSpace (b i)) (j : I) :
    X.components b v j = b.repr (b i) j • v := by
  classical
  change (TensorProduct.equivFinsuppOfBasisRight (M := V) b) (X.coaction v) j = _
  rw [(X.mem_weightSpace (b i)).mp hv,
    TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]

/-- A basis component acts as the identity on its own weight space. -/
theorem components_apply_of_mem_weightSpace {i : I} {v : V}
    (hv : v ∈ X.weightSpace (b i)) : X.components b v i = v := by
  classical
  simpa using X.components_apply_eq_smul_of_mem_weightSpace b hv i

/-- A basis component vanishes on a weight space at a different basis index. -/
theorem components_apply_of_mem_weightSpace_ne {i j : I} {v : V}
    (hv : v ∈ X.weightSpace (b i)) (hij : i ≠ j) : X.components b v j = 0 := by
  classical
  simpa [hij] using X.components_apply_eq_smul_of_mem_weightSpace b hv j

/-- Every component projection is idempotent. -/
theorem components_components (hb : ∀ i : I, IsGroupLikeElem R (b i))
    (v : V) (i : I) :
    X.components b (X.components b v i) i = X.components b v i :=
  X.components_apply_of_mem_weightSpace b (X.components_mem_weightSpace b hb v i)

/-- Component projections at distinct basis indices are orthogonal. -/
theorem components_components_of_ne (hb : ∀ i : I, IsGroupLikeElem R (b i))
    (v : V) {i j : I} (hij : i ≠ j) :
    X.components b (X.components b v i) j = 0 :=
  X.components_apply_of_mem_weightSpace_ne b (X.components_mem_weightSpace b hb v i) hij

end Coalgebra.RightComodule
