/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AlgebraicGroups.Algebra.Coalgebra.RightComodule.TensorProduct
import Mathlib.RingTheory.Coalgebra.MonoidAlgebra

/-!
# Regular and bottom-subcomodule external tensor products

The regular comodules on `A = MonoidAlgebra ℕ ℕ` give the regular comodule of
the tensor coalgebra on `A ⊗[ℕ] A`. The monomials at indices `2` and `3`, with
coefficient `1`, have a nonzero tensor whose coaction is its tensor square.
The tensor of the two counits detects this input without a field or basis.

The bottom subcomodule of the same regular comodule gives a zero-carrier
boundary. Its subtype and tensor domain are inhabited subsingletons, and the
specified external tensor coaction is zero.

## References

The specified right comodules and raw external coaction are AlgebraicGroups
constructions by Formal Frontier Agents. Mathlib supplies the tensor maps and
permutations by Kenny Lau and Mario Carneiro, tensor coalgebras by Amelia
Livingston and Andrew Yang, scalar-tower tensor APIs by Kim Morrison, Johan
Commelin and Eric Wieser, and monoid-algebra coalgebras by Amelia Livingston.
Classical comodules are credited bibliographically to M. E. Sweedler,
*Hopf Algebras*, W. A. Benjamin, 1969.
-/

@[expose] public section

open scoped TensorProduct

open Coalgebra.RightComodule (externalTensor regular)

noncomputable section

namespace CoalgebraExternalTensorExamples

private abbrev regularMonoidAlgebra :=
  @regular ℕ (MonoidAlgebra ℕ ℕ) _ _ _ (MonoidAlgebra.instCoalgebra ℕ ℕ ℕ)

private abbrev externalRegular :=
  externalTensor regularMonoidAlgebra regularMonoidAlgebra

private abbrev regularTensor :=
  @regular ℕ ((MonoidAlgebra ℕ ℕ) ⊗[ℕ] (MonoidAlgebra ℕ ℕ)) _ _ _
    (TensorProduct.instCoalgebra (R := ℕ) (S := ℕ)
      (A := MonoidAlgebra ℕ ℕ) (B := MonoidAlgebra ℕ ℕ))

private abbrev monomialLeft : MonoidAlgebra ℕ ℕ := MonoidAlgebra.single (2 : ℕ) 1

private abbrev monomialRight : MonoidAlgebra ℕ ℕ := MonoidAlgebra.single (3 : ℕ) 1

private abbrev tensorMonomial := monomialLeft ⊗ₜ[ℕ] monomialRight

/-- A closed regular model: recovery on the tensor coalgebra, a counit-detected
nonzero input, and its diagonal, nonzero coaction. -/
private theorem regular_semiring_contract :
    externalRegular = regularTensor ∧
    externalRegular.coaction =
      ((TensorProduct.instCoalgebra (R := ℕ) (S := ℕ)
        (A := MonoidAlgebra ℕ ℕ) (B := MonoidAlgebra ℕ ℕ)).toCoalgebraStruct).comul ∧
    tensorMonomial ≠ 0 ∧
    externalRegular.coaction tensorMonomial = tensorMonomial ⊗ₜ[ℕ] tensorMonomial ∧
    externalRegular.coaction tensorMonomial ≠ 0 := by
  have ha : Coalgebra.counit (R := ℕ) monomialLeft = 1 := by
    exact (MonoidAlgebra.counit_single (R := ℕ) (2 : ℕ) (1 : ℕ)).trans
      (CommSemiring.counit_apply ℕ 1)
  have hb : Coalgebra.counit (R := ℕ) monomialRight = 1 := by
    exact (MonoidAlgebra.counit_single (R := ℕ) (3 : ℕ) (1 : ℕ)).trans
      (CommSemiring.counit_apply ℕ 1)
  let detector := (TensorProduct.rid ℕ ℕ).toLinearMap ∘ₗ
    TensorProduct.map (Coalgebra.counit (R := ℕ) (A := MonoidAlgebra ℕ ℕ))
      (Coalgebra.counit (R := ℕ) (A := MonoidAlgebra ℕ ℕ))
  have hdetect : detector tensorMonomial = 1 := by
    simp only [detector, tensorMonomial, LinearMap.comp_apply, TensorProduct.map_tmul,
      ha, hb, LinearEquiv.coe_coe, TensorProduct.rid_tmul, one_smul]
  have hinput : tensorMonomial ≠ 0 := by
    intro h
    have hone : (1 : ℕ) = 0 :=
      hdetect.symm.trans ((congrArg detector h).trans (map_zero detector))
    exact Nat.one_ne_zero hone
  have hleft : regularMonoidAlgebra.coaction monomialLeft =
      monomialLeft ⊗ₜ[ℕ] monomialLeft := by
    rw [Coalgebra.RightComodule.regular_coaction]
    simp only [monomialLeft, MonoidAlgebra.comul_single, CommSemiring.comul_apply,
      TensorProduct.map_tmul, MonoidAlgebra.lsingle_apply]
  have hright : regularMonoidAlgebra.coaction monomialRight =
      monomialRight ⊗ₜ[ℕ] monomialRight := by
    rw [Coalgebra.RightComodule.regular_coaction]
    simp only [monomialRight, MonoidAlgebra.comul_single, CommSemiring.comul_apply,
      TensorProduct.map_tmul, MonoidAlgebra.lsingle_apply]
  have hvalue : externalRegular.coaction tensorMonomial =
      tensorMonomial ⊗ₜ[ℕ] tensorMonomial := by
    calc
      _ = TensorProduct.tensorTensorTensorComm ℕ (MonoidAlgebra ℕ ℕ)
          (MonoidAlgebra ℕ ℕ) (MonoidAlgebra ℕ ℕ) (MonoidAlgebra ℕ ℕ)
          (regularMonoidAlgebra.coaction monomialLeft ⊗ₜ[ℕ]
            regularMonoidAlgebra.coaction monomialRight) :=
        Coalgebra.RightComodule.externalTensor_coaction_tmul _ _ _ _
      _ = _ := by
        rw [hleft, hright]
        exact TensorProduct.tensorTensorTensorComm_tmul (R := ℕ)
          monomialLeft monomialLeft monomialRight monomialRight
  refine ⟨Coalgebra.RightComodule.externalTensor_regular, ?_, hinput, hvalue, ?_⟩
  · rw [Coalgebra.RightComodule.externalTensor_coaction]
    exact Coalgebra.RightComodule.externalTensorCoaction_regular
  · intro h
    apply hinput
    exact externalRegular.coaction_injective
      (h.trans (map_zero externalRegular.coaction).symm)

private abbrev regularBottom :=
  Coalgebra.RightComodule.Subcomodule.bot regularMonoidAlgebra

private abbrev bottomExternal := externalTensor regularBottom.comodule regularMonoidAlgebra

/-- Tensoring the bottom subtype comodule gives a zero coaction on an inhabited
subsingleton carrier, with the same ordinary tensor coalgebra. -/
private theorem bottom_regular_contract :
    Subsingleton regularBottom.toSubmodule ∧
    regularBottom.comodule.coaction = 0 ∧
    Subsingleton (regularBottom.toSubmodule ⊗[ℕ] MonoidAlgebra ℕ ℕ) ∧
    bottomExternal.coaction = 0 ∧
    ∀ t : regularBottom.toSubmodule ⊗[ℕ] MonoidAlgebra ℕ ℕ,
      bottomExternal.coaction t = 0 := by
  have hbot : Subsingleton regularBottom.toSubmodule := by
    change Subsingleton (⊥ : Submodule ℕ (MonoidAlgebra ℕ ℕ))
    infer_instance
  have htensor : Subsingleton (regularBottom.toSubmodule ⊗[ℕ] MonoidAlgebra ℕ ℕ) := by
    change Subsingleton ((⊥ : Submodule ℕ (MonoidAlgebra ℕ ℕ)) ⊗[ℕ] MonoidAlgebra ℕ ℕ)
    infer_instance
  have hzero : bottomExternal.coaction = 0 :=
    bottomExternal.coaction_eq_zero_iff.mpr htensor
  refine ⟨hbot, ?_, htensor, hzero, ?_⟩
  · rfl
  · intro t
    exact (LinearMap.congr_fun hzero t).trans (LinearMap.zero_apply t)

end CoalgebraExternalTensorExamples

end
