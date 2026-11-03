/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AlgebraicGroups.Algebra.HopfAlgebra.TensorQuotient
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Tensor–quotient coordinates after extension of scalars

The tensor–quotient algebra equivalence can be extended to any compatible
commutative coefficient algebra. The coefficient algebra need not be a Hopf
algebra. Both finite-comultiplication formulas follow from the linear
computation API and tensor base-change cancellation.
-/

noncomputable section

universe uR uA0 uA uB uι

open scoped BigOperators TensorProduct
open TensorProduct

variable (R : Type uR) (A0 : Type uA0) (A : Type uA) (B : Type uB)
variable [CommRing R] [CommRing A0] [Bialgebra R A0]
variable [CommRing A] [HopfAlgebra R A]
variable [CommRing B] [Algebra R B]
variable [Algebra A0 A] [IsScalarTower R A0 A]
variable [Algebra A B] [IsScalarTower R A B]
variable [Algebra A0 B] [IsScalarTower A0 A B]
variable
  (counit_comp :
    (Bialgebra.counitAlgHom R A).comp (IsScalarTower.toAlgHom R A0 A) =
      Bialgebra.counitAlgHom R A0)
  (map_comp_comul :
    (Algebra.TensorProduct.map
      (IsScalarTower.toAlgHom R A0 A)
      (IsScalarTower.toAlgHom R A0 A)).comp (Bialgebra.comulAlgHom R A0) =
        (Bialgebra.comulAlgHom R A).comp (IsScalarTower.toAlgHom R A0 A))

local notation "J" =>
  Ideal.map (algebraMap A0 A) (RingHom.ker (Bialgebra.counitAlgHom R A0 : A0 →+* R))
local notation "Q" => A ⧸ J

example {ι : Type uι} (b : B) (a : A) (r : Coalgebra.Repr R a ι) :
    let C : (B ⊗[A0] A) ≃ₐ[B] (B ⊗[R] Q) :=
      (Algebra.TensorProduct.cancelBaseChange A0 A B B A).symm.trans
        ((Algebra.TensorProduct.congr
          (AlgEquiv.refl : B ≃ₐ[B] B)
          (HopfAlgebra.tensorQuotientAlgEquiv R A0 A counit_comp map_comp_comul)).trans
            (Algebra.TensorProduct.cancelBaseChange R A B B Q))
    C (b ⊗ₜ[A0] a) =
        ∑ k ∈ r.index,
          (b * algebraMap A B (r.left k)) ⊗ₜ[R]
            (Submodule.Quotient.mk (r.right k) : Q) ∧
      C.symm (b ⊗ₜ[R] (Submodule.Quotient.mk a : Q)) =
        ∑ k ∈ r.index,
          (b * algebraMap A B (HopfAlgebra.antipode R (r.left k))) ⊗ₜ[A0] r.right k := by
  classical
  have hforget :=
    HopfAlgebra.tensorQuotientAlgEquiv_toLinearEquiv R A0 A counit_comp map_comp_comul
  -- Identify only the stock quotient/tensor parents at default transparency.
  have hforward :
      HopfAlgebra.tensorQuotientAlgEquiv R A0 A counit_comp map_comp_comul
          ((1 : A) ⊗ₜ[A0] a) =
        ∑ k ∈ r.index, r.left k ⊗ₜ[R] (Submodule.Quotient.mk (r.right k) : Q) := by
    change (HopfAlgebra.tensorQuotientAlgEquiv R A0 A
      counit_comp map_comp_comul).toLinearEquiv ((1 : A) ⊗ₜ[A0] a) = _
    rw [hforget]
    erw [HopfAlgebra.tensorQuotientEquiv_tmul R A0 A
      counit_comp map_comp_comul (1 : A) a r]
    change (∑ k ∈ r.index,
      ((1 : A) * r.left k) ⊗ₜ[R] (Submodule.Quotient.mk (r.right k) : Q)) = _
    simp only [one_mul]
  have hinverse :
      (HopfAlgebra.tensorQuotientAlgEquiv R A0 A counit_comp map_comp_comul).symm
          ((1 : A) ⊗ₜ[R] (Submodule.Quotient.mk a : Q)) =
        ∑ k ∈ r.index, HopfAlgebra.antipode R (r.left k) ⊗ₜ[A0] r.right k := by
    change (HopfAlgebra.tensorQuotientAlgEquiv R A0 A
      counit_comp map_comp_comul).toLinearEquiv.symm
        ((1 : A) ⊗ₜ[R] (Submodule.Quotient.mk a : Q)) = _
    rw [hforget]
    erw [HopfAlgebra.tensorQuotientEquiv_symm_tmul R A0 A
      counit_comp map_comp_comul (1 : A) a r]
    simp only [one_mul]
  have hsmul (x : A) : (x • b : B) = b * algebraMap A B x := by
    rw [Algebra.smul_def, mul_comm]
  dsimp only
  constructor
  · rw [AlgEquiv.trans_apply (R := B)]
    change Algebra.TensorProduct.cancelBaseChange R A B B Q
      (Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[B] B)
        (HopfAlgebra.tensorQuotientAlgEquiv R A0 A counit_comp map_comp_comul)
        ((Algebra.TensorProduct.cancelBaseChange A0 A B B A).symm
          (b ⊗ₜ[A0] a))) = _
    rw [Algebra.TensorProduct.cancelBaseChange_symm_tmul A0 A B B A,
      Algebra.TensorProduct.congr_apply (R := A) (S := B),
      Algebra.TensorProduct.map_tmul (R := A) (S := B)]
    change Algebra.TensorProduct.cancelBaseChange R A B B Q
      (b ⊗ₜ[A] (HopfAlgebra.tensorQuotientAlgEquiv R A0 A
        counit_comp map_comp_comul ((1 : A) ⊗ₜ[A0] a))) = _
    rw [hforward, TensorProduct.tmul_sum, map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Algebra.TensorProduct.cancelBaseChange_tmul R A B B Q, hsmul]
  · rw [AlgEquiv.symm_trans_apply (R := B)]
    change Algebra.TensorProduct.cancelBaseChange A0 A B B A
      ((Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[B] B)
        (HopfAlgebra.tensorQuotientAlgEquiv R A0 A counit_comp map_comp_comul)).symm
        ((Algebra.TensorProduct.cancelBaseChange R A B B Q).symm
          (b ⊗ₜ[R] (Submodule.Quotient.mk a : Q)))) = _
    rw [Algebra.TensorProduct.cancelBaseChange_symm_tmul R A B B Q]
    change Algebra.TensorProduct.cancelBaseChange A0 A B B A
      (Algebra.TensorProduct.map (R := A) (S := B)
        ((AlgEquiv.refl : B ≃ₐ[B] B).symm : B →ₐ[B] B)
        (HopfAlgebra.tensorQuotientAlgEquiv R A0 A
          counit_comp map_comp_comul).symm.toAlgHom
        (b ⊗ₜ[A] ((1 : A) ⊗ₜ[R] (Submodule.Quotient.mk a : Q)))) = _
    rw [Algebra.TensorProduct.map_tmul (R := A) (S := B)]
    change Algebra.TensorProduct.cancelBaseChange A0 A B B A
      (b ⊗ₜ[A] ((HopfAlgebra.tensorQuotientAlgEquiv R A0 A
        counit_comp map_comp_comul).symm
          ((1 : A) ⊗ₜ[R] (Submodule.Quotient.mk a : Q)))) = _
    rw [hinverse, TensorProduct.tmul_sum, map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Algebra.TensorProduct.cancelBaseChange_tmul A0 A B B A, hsmul]
