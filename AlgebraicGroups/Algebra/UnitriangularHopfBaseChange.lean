/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.UnitriangularBaseChange
public import Mathlib.RingTheory.HopfAlgebra.TensorProduct
public import AlgebraicGroups.Algebra.HopfAlgebra.Hom

/-!
# Hopf compatibility of unitriangular coordinate base change

The canonical scalar extension of the canonical unitriangular Hopf
algebra is equivalent to the corresponding quotient over the new base. Both
bialgebra structures are their independently defined tensor-product and quotient
structures, not structures transported along the algebra equivalence.

Milne's `GL_n` coordinate coproduct over a field and polynomial presentation
of `U_n` give the matrix-coordinate antecedents. The scalar-extension map is
built from Christian Merten's Mathlib polynomial equivalence, currently
implemented using Yaël Dillies's monoid-algebra equivalence; Antoine
Chambert-Loir contributed a related earlier scalar-extension equivalence.
Mathlib's tensor-product Hopf structure, bialgebra equivalence and convolution
API supply the compatibility and antipode arguments. The comparison also
applies over arbitrary commutative base rings.

## References

* James S. Milne, *Algebraic Groups* (2017), items 2.8 (matrix-entry
  coproduct) and 2.9 (the `U_n` coordinate presentation).
* Antoine Chambert-Loir, Mathlib, `Mathlib.RingTheory.TensorProduct.MvPolynomial`
  (the related earlier `MvPolynomial.scalarRTensorAlgEquiv`).
* Christian Merten, Mathlib, `Mathlib.RingTheory.TensorProduct.MvPolynomial`
  (`MvPolynomial.algebraTensorAlgEquiv` used by the algebra comparison).
* Yaël Dillies, Mathlib, `Mathlib.RingTheory.TensorProduct.MonoidAlgebra`
  (`AddMonoidAlgebra.scalarTensorEquiv` implementing the polynomial equivalence).
* Amelia Livingston and Andrew Yang, Mathlib,
  `Mathlib.RingTheory.Bialgebra.TensorProduct` and
  `Mathlib.RingTheory.HopfAlgebra.TensorProduct` (canonical tensor structures).
* Yaël Dillies, Mathlib, `Mathlib.RingTheory.Bialgebra.Equiv`
  (`BialgEquiv.ofAlgEquiv`).
* Yaël Dillies, Mathlib, `Mathlib.RingTheory.Coalgebra.Convolution`
  (linear-map convolution) and
  `Mathlib.RingTheory.HopfAlgebra.Convolution` (the antipode inverse identities).
  Michał Mrugała and Yunzhou Xie contributed to the wider Hopf-algebra
  convolution formalization.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

open TauCeti.UpperUnitriangular

universe u

namespace UnitriangularCoordinateRing

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (ι : Type u) [Fintype ι] [LinearOrder ι]

/-- The counit of the canonical scalar-extension bialgebra commutes with
base change of the canonical unitriangular Hopf algebra. -/
theorem baseChange_counit :
    (Bialgebra.counitAlgHom S (coordinateHopfAlgebra S ι)).comp
      (baseChange R S ι).toAlgHom =
    Bialgebra.counitAlgHom S (S ⊗[R] coordinateHopfAlgebra R ι) := by
  apply tensor_algHom_ext_entries R S ι
  intro p
  change (Bialgebra.counitAlgHom S (coordinateHopfAlgebra S ι))
      (baseChange R S ι (1 ⊗ₜ[R] (coordinateHopfAlgebraAlgEquiv R ι (genericMatrix R ι p.1.1
        p.1.2)))) =
      (Bialgebra.counitAlgHom S (S ⊗[R] coordinateHopfAlgebra R ι))
        (1 ⊗ₜ[R] (coordinateHopfAlgebraAlgEquiv R ι (genericMatrix R ι p.1.1 p.1.2)))
  rw [baseChange_tmul_entry, map_mul]
  simp only [map_one, one_mul]
  change Coalgebra.counit (R := S)
      ((coordinateHopfAlgebraAlgEquiv S ι (genericMatrix S ι p.1.1 p.1.2))) =
    Coalgebra.counit (R := S)
      ((1 : S) ⊗ₜ[R] (coordinateHopfAlgebraAlgEquiv R ι (genericMatrix R ι p.1.1 p.1.2)))
  rw [TensorProduct.counit_tmul, coordinateHopfAlgebra_counit_genericMatrix_apply S ι,
    coordinateHopfAlgebra_counit_genericMatrix_apply R ι, CommSemiring.counit_apply]
  simp [ne_of_lt p.2]

/-- The comultiplication of the canonical tensor-product bialgebra commutes
with base change of the canonical unitriangular Hopf algebra. -/
theorem baseChange_comul :
    (Algebra.TensorProduct.map (baseChange R S ι).toAlgHom
      (baseChange R S ι).toAlgHom).comp
        (Bialgebra.comulAlgHom S (S ⊗[R] coordinateHopfAlgebra R ι)) =
    (Bialgebra.comulAlgHom S (coordinateHopfAlgebra S ι)).comp
      (baseChange R S ι).toAlgHom := by
  apply tensor_algHom_ext_entries R S ι
    (coordinateHopfAlgebra S ι ⊗[S] coordinateHopfAlgebra S ι)
  intro p
  change (Algebra.TensorProduct.map (baseChange R S ι).toAlgHom
      (baseChange R S ι).toAlgHom)
      (Coalgebra.comul (R := S) ((1 : S) ⊗ₜ[R] (coordinateHopfAlgebraAlgEquiv R ι
        (genericMatrix R ι p.1.1 p.1.2)))) =
    Coalgebra.comul (R := S)
      (baseChange R S ι ((1 : S) ⊗ₜ[R] (coordinateHopfAlgebraAlgEquiv R ι (genericMatrix R ι
        p.1.1 p.1.2))))
  rw [baseChange_tmul_entry, Bialgebra.comul_mul]
  simp only [map_one, one_mul, Bialgebra.comul_one]
  rw [coordinateHopfAlgebra_comul_genericMatrix_apply S ι p.1.1 p.1.2]
  rw [TensorProduct.comul_tmul, CommSemiring.comul_apply,
    coordinateHopfAlgebra_comul_genericMatrix_apply R ι p.1.1 p.1.2]
  simp only [TensorProduct.tmul_sum, map_sum, Algebra.TensorProduct.map_tmul,
    TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul]
  apply Finset.sum_congr rfl
  intro k _
  change baseChange R S ι
        ((1 : S) ⊗ₜ[R] (coordinateHopfAlgebraAlgEquiv R ι (genericMatrix R ι p.1.1 k))) ⊗ₜ[S]
      baseChange R S ι
        ((1 : S) ⊗ₜ[R] (coordinateHopfAlgebraAlgEquiv R ι (genericMatrix R ι k p.1.2))) =
    (coordinateHopfAlgebraAlgEquiv S ι (genericMatrix S ι p.1.1 k)) ⊗ₜ[S]
      (coordinateHopfAlgebraAlgEquiv S ι (genericMatrix S ι k p.1.2))
  rw [baseChange_tmul_entry, baseChange_tmul_entry]
  simp only [map_one, one_mul]

/-- The scalar-extension algebra equivalence built from Christian Merten's
Mathlib `MvPolynomial.algebraTensorAlgEquiv` respects the two independently
given bialgebra structures, using Yaël Dillies's `BialgEquiv.ofAlgEquiv`. -/
def baseChangeBialgEquiv :
    S ⊗[R] coordinateHopfAlgebra R ι ≃ₐc[S] coordinateHopfAlgebra S ι := by
  let sourceBialgebra : Bialgebra S (S ⊗[R] coordinateHopfAlgebra R ι) := inferInstance
  let targetBialgebra : Bialgebra S (coordinateHopfAlgebra S ι) := inferInstance
  let algebraTypes :
      (S ⊗[R] coordinateHopfAlgebra R ι ≃ₐ[S] coordinateHopfAlgebra S ι) =
        @AlgEquiv S (S ⊗[R] coordinateHopfAlgebra R ι) (coordinateHopfAlgebra S ι) (inferInstance)
          (inferInstance) (inferInstance) sourceBialgebra.toAlgebra
          targetBialgebra.toAlgebra := rfl
  let bialgebraTypes :
      (S ⊗[R] coordinateHopfAlgebra R ι ≃ₐc[S] coordinateHopfAlgebra S ι) =
        @BialgEquiv S (inferInstance) (S ⊗[R] coordinateHopfAlgebra R ι) (coordinateHopfAlgebra S ι)
          (inferInstance) (inferInstance) sourceBialgebra.toAlgebra
          targetBialgebra.toAlgebra sourceBialgebra.toCoalgebra.toCoalgebraStruct
          targetBialgebra.toCoalgebra.toCoalgebraStruct := rfl
  let algebraEquiv := algebraTypes.mp (baseChange R S ι)
  have algebraEquiv_eq : algebraEquiv = baseChange R S ι := by
    dsimp [algebraEquiv, algebraTypes]
  apply bialgebraTypes.mpr
  exact BialgEquiv.ofAlgEquiv algebraEquiv
    (by rw [algebraEquiv_eq]; exact baseChange_counit R S ι)
    (by rw [algebraEquiv_eq]; exact baseChange_comul R S ι)

@[simp] theorem baseChangeBialgEquiv_apply (x : S ⊗[R] coordinateHopfAlgebra R ι) :
    baseChangeBialgEquiv R S ι x = baseChange R S ι x := rfl

/-- The antipodes of the existing scalar-extension and quotient Hopf algebras
intertwine under the algebra base-change map, by `BialgHomClass.map_antipode`. -/
theorem baseChange_antipode (x : S ⊗[R] coordinateHopfAlgebra R ι) :
    baseChange R S ι
        ((@HopfAlgebraStruct.antipode S (S ⊗[R] coordinateHopfAlgebra R ι)
          inferInstance inferInstance (inferInstance : HopfAlgebraStruct S
            (S ⊗[R] coordinateHopfAlgebra R ι))) x) =
      (@HopfAlgebraStruct.antipode S (coordinateHopfAlgebra S ι)
        inferInstance inferInstance (inferInstance : HopfAlgebraStruct S
          (coordinateHopfAlgebra S ι))) (baseChange R S ι x) := by
  have hpoint (y : S ⊗[R] coordinateHopfAlgebra R ι) :
      (baseChangeBialgEquiv R S ι).toBialgHom y = baseChange R S ι y :=
    baseChangeBialgEquiv_apply R S ι y
  have h := BialgHomClass.map_antipode (baseChangeBialgEquiv R S ι).toBialgHom x
  simpa only [hpoint] using h

end UnitriangularCoordinateRing
