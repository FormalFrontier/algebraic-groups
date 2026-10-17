/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Bialgebra.GroupLikeTensorProduct
public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra

/-!
# Tensor equivalences on normalized group-like elements

The monoid algebra `ℕ[ℕ]`, with the usual multiplication on its indexing monoid,
has the nonidentity group-like elements `single 2 1` and `single 3 1`. Their inverse
image under the tensor equivalence is also nonidentity, by preservation of the unit
under the multiplicative equivalence. Over subsingleton scalars, normalization
instead allows a zero group-like element. The final example specializes coalgebra
naturality to arbitrary bialgebra morphisms.

The monoid-algebra and group-like structures use Mathlib's formalizations by
Amelia Livingston, Yaël Dillies and Michał Mrugała. The tensor coalgebra and
bialgebra infrastructure is due to Amelia Livingston and Andrew Yang; transport
and the scalar-source correspondence use the project's group-like morphism API.
-/

@[expose] public section

open scoped TensorProduct

universe uR uC uD uC' uD'

private theorem natMonoidAlgebra_delta_two_three_contract :
    let A := MonoidAlgebra ℕ ℕ
    let δ₂ : GroupLike ℕ A :=
      ⟨MonoidAlgebra.single 2 1,
        MonoidAlgebra.isGroupLikeElem_single_one (R := ℕ) (A := ℕ) 2⟩
    let δ₃ : GroupLike ℕ A :=
      ⟨MonoidAlgebra.single 3 1,
        MonoidAlgebra.isGroupLikeElem_single_one (R := ℕ) (A := ℕ) 3⟩
    δ₂ ≠ 1 ∧ δ₃ ≠ 1 ∧
      ∃ x : @GroupLike ℕ (A ⊗[ℕ] A) _ _ _
        (TensorProduct.instCoalgebra (R := ℕ) (S := ℕ) (A := A) (B := A)),
        x.val = δ₂.val ⊗ₜ[ℕ] δ₃.val ∧
        GroupLike.tensorEquiv ℕ A A x = (δ₂, δ₃) ∧ x ≠ 1 := by
  let A := MonoidAlgebra ℕ ℕ
  let δ₂ : GroupLike ℕ A :=
    ⟨MonoidAlgebra.single 2 1,
      MonoidAlgebra.isGroupLikeElem_single_one (R := ℕ) (A := ℕ) 2⟩
  let δ₃ : GroupLike ℕ A :=
    ⟨MonoidAlgebra.single 3 1,
      MonoidAlgebra.isGroupLikeElem_single_one (R := ℕ) (A := ℕ) 3⟩
  change δ₂ ≠ 1 ∧ δ₃ ≠ 1 ∧
    ∃ x : @GroupLike ℕ (A ⊗[ℕ] A) _ _ _
      (TensorProduct.instCoalgebra (R := ℕ) (S := ℕ) (A := A) (B := A)),
      x.val = δ₂.val ⊗ₜ[ℕ] δ₃.val ∧
      GroupLike.tensorEquiv ℕ A A x = (δ₂, δ₃) ∧ x ≠ 1
  have h₂ : δ₂ ≠ 1 := by
    intro h
    have hv := congrArg (fun y : GroupLike ℕ A => y.val) h
    change MonoidAlgebra.single 2 (1 : ℕ) = (1 : A) at hv
    rw [MonoidAlgebra.one_def] at hv
    have hi : (2 : ℕ) = 1 :=
      MonoidAlgebra.single_left_injective (R := ℕ) (by simp : (1 : ℕ) ≠ 0) hv
    exact (by simp : (2 : ℕ) ≠ 1) hi
  have h₃ : δ₃ ≠ 1 := by
    intro h
    have hv := congrArg (fun y : GroupLike ℕ A => y.val) h
    change MonoidAlgebra.single 3 (1 : ℕ) = (1 : A) at hv
    rw [MonoidAlgebra.one_def] at hv
    have hi : (3 : ℕ) = 1 :=
      MonoidAlgebra.single_left_injective (R := ℕ) (by simp : (1 : ℕ) ≠ 0) hv
    exact (by simp : (3 : ℕ) ≠ 1) hi
  let x := (GroupLike.tensorEquiv ℕ A A).symm (δ₂, δ₃)
  have hx : GroupLike.tensorEquiv ℕ A A x = (δ₂, δ₃) :=
    (GroupLike.tensorEquiv ℕ A A).apply_symm_apply _
  refine ⟨h₂, h₃, x, GroupLike.tensorEquiv_symm_val (δ₂, δ₃), hx, ?_⟩
  intro h
  apply h₂
  have hunit : GroupLike.tensorMulEquiv ℕ A A x = (1, 1) := by
    rw [h, map_one, Prod.one_eq_mk]
  change GroupLike.tensorEquiv ℕ A A x = (1, 1) at hunit
  exact congrArg Prod.fst (hx.symm.trans hunit)

private theorem tensorEquiv_subsingleton_scalar_contract
    {R : Type uR} {C : Type uC} {D : Type uD}
    [CommSemiring R]
    [AddCommMonoid C] [Module R C] [Coalgebra R C]
    [AddCommMonoid D] [Module R D] [Coalgebra R D]
    [Subsingleton R] :
    ∃ x : GroupLike R (C ⊗[R] D),
      x.val = 0 ∧
      (GroupLike.tensorEquiv R C D x).1.val = 0 ∧
      (GroupLike.tensorEquiv R C D x).2.val = 0 := by
  let x : GroupLike R (C ⊗[R] D) := ⟨0, {
    counit_eq_one := by simpa only [map_zero] using (Subsingleton.elim (0 : R) 1)
    comul_eq_tmul_self := by simp }⟩
  refine ⟨x, rfl, ?_, ?_⟩
  · exact Module.eq_zero_of_zero_eq_one _ (Subsingleton.elim (0 : R) 1)
  · exact Module.eq_zero_of_zero_eq_one _ (Subsingleton.elim (0 : R) 1)

private theorem tensorMulEquiv_bialgebra_naturality
    {R : Type uR} {C : Type uC} {D : Type uD}
    {C' : Type uC'} {D' : Type uD'}
    [CommSemiring R]
    [Semiring C] [Bialgebra R C] [Semiring D] [Bialgebra R D]
    [Semiring C'] [Bialgebra R C'] [Semiring D'] [Bialgebra R D']
    (f : C →ₐc[R] C') (g : D →ₐc[R] D')
    (x : GroupLike R (C ⊗[R] D)) :
    GroupLike.tensorMulEquiv R C' D'
        ((Bialgebra.TensorProduct.map f g).groupLikeMap x) =
      (f.groupLikeMap ((GroupLike.tensorMulEquiv R C D x).1),
       g.groupLikeMap ((GroupLike.tensorMulEquiv R C D x).2)) := by
  change GroupLike.tensorEquiv R C' D'
      (GroupLike.map (Bialgebra.TensorProduct.map f g).toCoalgHom x) =
    (GroupLike.map f.toCoalgHom ((GroupLike.tensorEquiv R C D x).1),
     GroupLike.map g.toCoalgHom ((GroupLike.tensorEquiv R C D x).2))
  have hmap :
      (Bialgebra.TensorProduct.map f g).toCoalgHom =
        Coalgebra.TensorProduct.map f.toCoalgHom g.toCoalgHom := by
    apply CoalgHom.coe_linearMap_injective
    apply TensorProduct.ext'
    intro c d
    simp only [CoalgHom.coe_toLinearMap, BialgHom.toCoalgHom_apply,
      Bialgebra.TensorProduct.map_tmul, Coalgebra.TensorProduct.map_tmul]
  rw [hmap]
  exact GroupLike.tensorEquiv_mapCoalgHoms f.toCoalgHom g.toCoalgHom x
