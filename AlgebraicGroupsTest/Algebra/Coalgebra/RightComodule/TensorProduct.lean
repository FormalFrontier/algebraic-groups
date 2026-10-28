/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.ComoduleCoefficients
public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.TensorProduct
public import Mathlib.RingTheory.Coalgebra.MonoidAlgebra

/-!
# Regular and bottom-subcomodule external tensor products

The regular comodules on `A = MonoidAlgebra ℕ ℕ` give the regular comodule of
the tensor coalgebra on `A ⊗[ℕ] A`. The monomials at indices `2` and `3`, with
coefficient `1`, have a nonzero tensor whose coact is its tensor square.
The tensor of the two counits detects this input without a field or basis.

For the distinct coalgebras `MonoidAlgebra ℕ Bool` and `MonoidAlgebra ℕ (Fin 3)`,
coordinate extraction on a tensor of two sums selects the tensor of the monomials
at `false` and `0`. The product coordinate detects a nonzero value, and the product
counit distinguishes that value from the input. Neither coordinate is a counit.

The bottom subcomodule of the regular comodule on `A` gives a zero-carrier
boundary. Its subtype and tensor domain are inhabited subsingletons, and the
specified external tensor coact is zero.

For the scalar coalgebra `ℕ`, tensoring twice the identity with three times the
identity sends `1 ⊗ₜ 1` to `2 ⊗ₜ 3`. The left unitor sends the latter to `6`,
not `1`, so this morphism is not the identity. The identity and composition
laws are also exercised on these regular comodules.

## References

The specified right comodules and raw external coact are AlgebraicGroups
constructions by Formal Frontier Agents. Mathlib supplies the tensor maps and
permutations by Kenny Lau and Mario Carneiro, tensor coalgebras by Amelia
Livingston and Andrew Yang, scalar-tower tensor APIs by Kim Morrison, Johan
Commelin and Eric Wieser, and monoid-algebra coalgebras by Amelia Livingston.
The coordinate maps follow AlgebraicGroups' finite-coalgebra coefficient examples
and Mathlib's monoid-algebra and Finsupp formalizations by Johannes Hölzl,
Yury Kudryashov and Kim Morrison.
Classical comodules are credited bibliographically to M. E. Sweedler,
*Hopf Algebras*, W. A. Benjamin, 1969.
-/

@[expose] public section

open scoped TensorProduct

open TauCeti.Comodule (externalTensor instSelf)
open TauCeti

noncomputable section

namespace CoalgebraExternalTensorExamples

private abbrev regularMonoidAlgebra :=
  @instSelf ℕ (MonoidAlgebra ℕ ℕ) _ _ _ (MonoidAlgebra.instCoalgebra ℕ ℕ ℕ)

private abbrev externalRegular :=
  externalTensor regularMonoidAlgebra regularMonoidAlgebra

private abbrev regularTensor :=
  @instSelf ℕ ((MonoidAlgebra ℕ ℕ) ⊗[ℕ] (MonoidAlgebra ℕ ℕ)) _ _ _
    (TensorProduct.instCoalgebra (R := ℕ) (S := ℕ)
      (A := MonoidAlgebra ℕ ℕ) (B := MonoidAlgebra ℕ ℕ))

private abbrev monomialLeft : MonoidAlgebra ℕ ℕ := MonoidAlgebra.single (2 : ℕ) 1

private abbrev monomialRight : MonoidAlgebra ℕ ℕ := MonoidAlgebra.single (3 : ℕ) 1

private abbrev tensorMonomial := monomialLeft ⊗ₜ[ℕ] monomialRight

/-- A closed regular model: recovery on the tensor coalgebra, a counit-detected
nonzero input, and its diagonal, nonzero coact. -/
private theorem regular_semiring_contract :
    externalRegular = regularTensor ∧
    externalRegular.coact =
      ((TensorProduct.instCoalgebra (R := ℕ) (S := ℕ)
        (A := MonoidAlgebra ℕ ℕ) (B := MonoidAlgebra ℕ ℕ)).toCoalgebraStruct).comul ∧
    tensorMonomial ≠ 0 ∧
    externalRegular.coact tensorMonomial = tensorMonomial ⊗ₜ[ℕ] tensorMonomial ∧
    externalRegular.coact tensorMonomial ≠ 0 := by
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
  have hleft : regularMonoidAlgebra.coact monomialLeft =
      monomialLeft ⊗ₜ[ℕ] monomialLeft := by
    rw [TauCeti.Comodule.instSelf_coact]
    simp only [monomialLeft, MonoidAlgebra.comul_single, CommSemiring.comul_apply,
      TensorProduct.map_tmul, MonoidAlgebra.lsingle_apply]
  have hright : regularMonoidAlgebra.coact monomialRight =
      monomialRight ⊗ₜ[ℕ] monomialRight := by
    rw [TauCeti.Comodule.instSelf_coact]
    simp only [monomialRight, MonoidAlgebra.comul_single, CommSemiring.comul_apply,
      TensorProduct.map_tmul, MonoidAlgebra.lsingle_apply]
  have hvalue : externalRegular.coact tensorMonomial =
      tensorMonomial ⊗ₜ[ℕ] tensorMonomial := by
    calc
      _ = TensorProduct.tensorTensorTensorComm ℕ (MonoidAlgebra ℕ ℕ)
          (MonoidAlgebra ℕ ℕ) (MonoidAlgebra ℕ ℕ) (MonoidAlgebra ℕ ℕ)
          (regularMonoidAlgebra.coact monomialLeft ⊗ₜ[ℕ]
            regularMonoidAlgebra.coact monomialRight) :=
        TauCeti.Comodule.externalTensor_coact_tmul _ _ _ _
      _ = _ := by
        rw [hleft, hright]
        exact TensorProduct.tensorTensorTensorComm_tmul (R := ℕ)
          monomialLeft monomialLeft monomialRight monomialRight
  refine ⟨TauCeti.Comodule.externalTensor_regular, ?_, hinput, hvalue, ?_⟩
  · rw [TauCeti.Comodule.externalTensor_coact]
    exact TauCeti.Comodule.externalTensorCoaction_regular
  · intro h
    apply hinput
    exact externalRegular.coact_injective
      (h.trans (map_zero externalRegular.coact).symm)

private abbrev regularBool :=
  @instSelf ℕ (MonoidAlgebra ℕ Bool) _ _ _ (MonoidAlgebra.instCoalgebra ℕ ℕ Bool)

private abbrev regularFinThree :=
  @instSelf ℕ (MonoidAlgebra ℕ (Fin 3)) _ _ _ (MonoidAlgebra.instCoalgebra ℕ ℕ (Fin 3))

private abbrev falseMonomial : MonoidAlgebra ℕ Bool := MonoidAlgebra.single false 1

private abbrev trueMonomial : MonoidAlgebra ℕ Bool := MonoidAlgebra.single true 1

private abbrev zeroMonomial : MonoidAlgebra ℕ (Fin 3) := MonoidAlgebra.single 0 1

private abbrev oneMonomial : MonoidAlgebra ℕ (Fin 3) := MonoidAlgebra.single 1 1

private abbrev boolPair := falseMonomial + trueMonomial

private abbrev finThreePair := zeroMonomial + oneMonomial

private def falseCoordinate : MonoidAlgebra ℕ Bool →ₗ[ℕ] ℕ :=
  (Finsupp.lapply false).comp (MonoidAlgebra.coeffLinearEquiv ℕ).toLinearMap

private def zeroCoordinate : MonoidAlgebra ℕ (Fin 3) →ₗ[ℕ] ℕ :=
  (Finsupp.lapply (0 : Fin 3)).comp (MonoidAlgebra.coeffLinearEquiv ℕ).toLinearMap

private abbrev coordinateProduct :=
  (TensorProduct.lid ℕ ℕ).toLinearMap ∘ₗ TensorProduct.map falseCoordinate zeroCoordinate

private abbrev counitProduct :=
  (TensorProduct.lid ℕ ℕ).toLinearMap ∘ₗ
    TensorProduct.map (Coalgebra.counit (R := ℕ) (A := MonoidAlgebra ℕ Bool))
      (Coalgebra.counit (R := ℕ) (A := MonoidAlgebra ℕ (Fin 3)))

private abbrev tensorPair := boolPair ⊗ₜ[ℕ] finThreePair

private abbrev selectedTensor := falseMonomial ⊗ₜ[ℕ] zeroMonomial

/-- Product coordinates on two distinct regular coalgebras select one monomial tensor
from a tensor of two sums. -/
private theorem external_coordinate_coefficient :
    (@Comodule.matrixCoefficient ℕ ((MonoidAlgebra ℕ Bool) ⊗[ℕ] (MonoidAlgebra ℕ (Fin 3)))
        ((MonoidAlgebra ℕ Bool) ⊗[ℕ] (MonoidAlgebra ℕ (Fin 3))) _ _ _ _ _ _
        (regularBool.externalTensor regularFinThree)) coordinateProduct tensorPair =
      selectedTensor := by
  have hleft : (@Comodule.matrixCoefficient ℕ (MonoidAlgebra ℕ Bool) (MonoidAlgebra ℕ Bool) _ _
      _ _ _ _ regularBool) falseCoordinate boolPair = falseMonomial := by
    rw [TauCeti.Comodule.matrixCoefficient_def, ← LinearMap.rTensor_def,
      TauCeti.Comodule.instSelf_coact]
    simp [boolPair, falseMonomial, trueMonomial, falseCoordinate,
      MonoidAlgebra.comul_single, TensorProduct.map_tmul, MonoidAlgebra.lsingle_apply,
      LinearMap.rTensor_tmul]
  have hright : (@Comodule.matrixCoefficient ℕ (MonoidAlgebra ℕ (Fin 3)) (MonoidAlgebra ℕ (Fin
      3)) _ _ _ _ _ _ regularFinThree) zeroCoordinate finThreePair = zeroMonomial := by
    rw [TauCeti.Comodule.matrixCoefficient_def, ← LinearMap.rTensor_def,
      TauCeti.Comodule.instSelf_coact]
    simp [finThreePair, zeroMonomial, oneMonomial, zeroCoordinate,
      MonoidAlgebra.comul_single, TensorProduct.map_tmul, MonoidAlgebra.lsingle_apply,
      LinearMap.rTensor_tmul]
  calc
    _ = (@Comodule.matrixCoefficient ℕ (MonoidAlgebra ℕ Bool) (MonoidAlgebra ℕ Bool) _ _ _ _ _ _
        regularBool) falseCoordinate boolPair ⊗ₜ[ℕ]
        (@Comodule.matrixCoefficient ℕ (MonoidAlgebra ℕ (Fin 3)) (MonoidAlgebra ℕ (Fin 3)) _ _ _
            _ _ _ regularFinThree) zeroCoordinate finThreePair :=
      TauCeti.Comodule.externalTensor_coefficient_tmul
        regularBool regularFinThree falseCoordinate zeroCoordinate boolPair finThreePair
    _ = selectedTensor := by rw [hleft, hright]

/-- The selected coefficient is nonzero and differs from the input, as detected by
product coordinates and counits. The rejected monomials separate each coordinate
from its coalgebra's counit. -/
private theorem coordinate_coefficient_contract :
    coordinateProduct selectedTensor = 1 ∧
    selectedTensor ≠ 0 ∧
    counitProduct tensorPair = 4 ∧
    counitProduct selectedTensor = 1 ∧
    selectedTensor ≠ tensorPair ∧
    falseCoordinate trueMonomial = 0 ∧
    Coalgebra.counit (R := ℕ) trueMonomial = 1 ∧
    zeroCoordinate oneMonomial = 0 ∧
    Coalgebra.counit (R := ℕ) oneMonomial = 1 := by
  have hselected : coordinateProduct selectedTensor = 1 := by
    simp [coordinateProduct, selectedTensor, falseCoordinate, zeroCoordinate,
      falseMonomial, zeroMonomial]
  have hraw : counitProduct tensorPair = 4 := by
    simp [counitProduct, tensorPair, boolPair, finThreePair, falseMonomial,
      trueMonomial, zeroMonomial, oneMonomial, smul_eq_mul]
  have hsmall : counitProduct selectedTensor = 1 := by
    simp [counitProduct, selectedTensor, falseMonomial, zeroMonomial]
  have hleftCounit : Coalgebra.counit (R := ℕ) trueMonomial = 1 := by
    exact (MonoidAlgebra.counit_single (R := ℕ) true (1 : ℕ)).trans
      (CommSemiring.counit_apply ℕ 1)
  have hrightCounit : Coalgebra.counit (R := ℕ) oneMonomial = 1 := by
    exact (MonoidAlgebra.counit_single (R := ℕ) (1 : Fin 3) (1 : ℕ)).trans
      (CommSemiring.counit_apply ℕ 1)
  refine ⟨hselected, ?_, hraw, hsmall, ?_, ?_, hleftCounit, ?_, hrightCounit⟩
  · intro h
    have hone : (1 : ℕ) = 0 :=
      hselected.symm.trans ((congrArg coordinateProduct h).trans (map_zero coordinateProduct))
    exact Nat.one_ne_zero hone
  · intro h
    have hone : (1 : ℕ) = 4 :=
      hsmall.symm.trans ((congrArg counitProduct h).trans hraw)
    exact (by decide : (1 : ℕ) ≠ 4) hone
  · simp [falseCoordinate, trueMonomial]
  · simp [zeroCoordinate, oneMonomial]

private abbrev regularBottom :=
  (⊥ : Subcomodule ℕ (MonoidAlgebra ℕ ℕ) (MonoidAlgebra ℕ ℕ))

private abbrev bottomExternal := externalTensor (Subcomodule.instComodule (R := ℕ) (C :=
    MonoidAlgebra ℕ ℕ) regularBottom) regularMonoidAlgebra

/-- Tensoring the bottom subtype comodule gives a zero coact on an inhabited
subsingleton carrier, with the same ordinary tensor coalgebra. -/
private theorem bottom_regular_contract :
    Subsingleton regularBottom ∧
    (Subcomodule.instComodule (R := ℕ) (C := MonoidAlgebra ℕ ℕ) regularBottom).coact = 0 ∧
    Subsingleton (regularBottom ⊗[ℕ] MonoidAlgebra ℕ ℕ) ∧
    bottomExternal.coact = 0 ∧
    ∀ t : regularBottom ⊗[ℕ] MonoidAlgebra ℕ ℕ,
      bottomExternal.coact t = 0 := by
  have hbot : Subsingleton regularBottom := by
    change Subsingleton (⊥ : Submodule ℕ (MonoidAlgebra ℕ ℕ))
    infer_instance
  have htensor : Subsingleton (regularBottom ⊗[ℕ] MonoidAlgebra ℕ ℕ) := by
    change Subsingleton ((⊥ : Submodule ℕ (MonoidAlgebra ℕ ℕ)) ⊗[ℕ] MonoidAlgebra ℕ ℕ)
    infer_instance
  have hzero : bottomExternal.coact = 0 :=
    bottomExternal.coact_eq_zero_iff.mpr htensor
  refine ⟨hbot, ?_, htensor, hzero, ?_⟩
  · ext m; exact Subsingleton.elim _ _
  · intro t
    exact (LinearMap.congr_fun hzero t).trans (LinearMap.zero_apply t)

end CoalgebraExternalTensorExamples

end


namespace CoalgebraExternalTensorHomExamples

open TauCeti
open TauCeti.Comodule (externalTensor instSelf)

/-- The standard tensor coalgebra specialized to the two scalar natural-number coalgebras. -/
noncomputable local instance natTensorCoalgebra : Coalgebra ℕ (ℕ ⊗[ℕ] ℕ) :=
  TensorProduct.instCoalgebra (R := ℕ) (S := ℕ) (A := ℕ) (B := ℕ)

/-- The external tensor of the two regular natural-number coactions in this fixture. -/
local instance natTensorComodule : TauCeti.Comodule ℕ (ℕ ⊗[ℕ] ℕ) (ℕ ⊗[ℕ] ℕ) :=
  TauCeti.Comodule.externalTensor (TauCeti.Comodule.instSelf ℕ ℕ)
    (TauCeti.Comodule.instSelf ℕ ℕ)

open TauCeti.Comodule.Hom

example :
    (((2 : ℕ) • Comodule.Hom.id ℕ ℕ ℕ).externalTensor
      ((3 : ℕ) • Comodule.Hom.id ℕ ℕ ℕ)) ((1 : ℕ) ⊗ₜ[ℕ] (1 : ℕ)) =
        (2 : ℕ) ⊗ₜ[ℕ] (3 : ℕ) := by
  rw [Comodule.Hom.externalTensor_tmul]
  rfl

example :
    TensorProduct.lid ℕ ℕ
        ((((2 : ℕ) • Comodule.Hom.id ℕ ℕ ℕ).externalTensor
          ((3 : ℕ) • Comodule.Hom.id ℕ ℕ ℕ)) ((1 : ℕ) ⊗ₜ[ℕ] (1 : ℕ))) = 6 ∧
      ((2 : ℕ) • Comodule.Hom.id ℕ ℕ ℕ).externalTensor
          ((3 : ℕ) • Comodule.Hom.id ℕ ℕ ℕ) ≠
        Comodule.Hom.id ℕ (ℕ ⊗[ℕ] ℕ) (ℕ ⊗[ℕ] ℕ) := by
  constructor
  · rw [Comodule.Hom.externalTensor_tmul, TensorProduct.lid_tmul]
    rfl
  · intro h
    have hvalue := congrArg
      (fun k : Comodule.Hom ℕ (ℕ ⊗[ℕ] ℕ) (ℕ ⊗[ℕ] ℕ) (ℕ ⊗[ℕ] ℕ) ↦
        TensorProduct.lid ℕ ℕ (k ((1 : ℕ) ⊗ₜ[ℕ] (1 : ℕ)))) h
    apply (by decide : (6 : ℕ) ≠ 1)
    simp only [
      Comodule.Hom.id_apply, TensorProduct.lid_tmul, Nat.nsmul_eq_mul] at hvalue
    exact hvalue

example (t : ℕ ⊗[ℕ] ℕ) :
    ((Comodule.Hom.id ℕ ℕ ℕ).externalTensor
      (Comodule.Hom.id ℕ ℕ ℕ)) t = t := by
  rw [Comodule.Hom.externalTensor_id, Comodule.Hom.id_apply]

example :
    ((((2 : ℕ) • Comodule.Hom.id ℕ ℕ ℕ).comp
        ((2 : ℕ) • Comodule.Hom.id ℕ ℕ ℕ)).externalTensor
      (((3 : ℕ) • Comodule.Hom.id ℕ ℕ ℕ).comp
        ((3 : ℕ) • Comodule.Hom.id ℕ ℕ ℕ))) ((1 : ℕ) ⊗ₜ[ℕ] (1 : ℕ)) =
        (4 : ℕ) ⊗ₜ[ℕ] (9 : ℕ) := by
  rw [Comodule.Hom.externalTensor_comp, Comodule.Hom.comp_apply,
    Comodule.Hom.externalTensor_tmul, Comodule.Hom.externalTensor_tmul]
  rfl

example :
    ((0 : Comodule.Hom ℕ ℕ ℕ ℕ).externalTensor
      ((3 : ℕ) • Comodule.Hom.id ℕ ℕ ℕ)) ((1 : ℕ) ⊗ₜ[ℕ] (1 : ℕ)) = 0 := by
  simp only [Comodule.Hom.externalTensor_tmul, Comodule.Hom.zero_apply,
    TensorProduct.zero_tmul]

end CoalgebraExternalTensorHomExamples
