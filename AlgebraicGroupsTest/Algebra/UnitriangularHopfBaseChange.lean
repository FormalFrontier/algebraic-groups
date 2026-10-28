/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.UnitriangularHopfBaseChange
public import Mathlib.Data.ZMod.Basic

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u

namespace UnitriangularCoordinateRing

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (ι : Type u) [Fintype ι] [LinearOrder ι]

example :
    (Bialgebra.counitAlgHom S (TauCeti.UpperUnitriangular.coordinateHopfAlgebra S ι)).comp
      (baseChange R S ι).toAlgHom =
    Bialgebra.counitAlgHom S (S ⊗[R] TauCeti.UpperUnitriangular.coordinateHopfAlgebra R ι) :=
  baseChange_counit R S ι

example :
    (Algebra.TensorProduct.map (baseChange R S ι).toAlgHom
      (baseChange R S ι).toAlgHom).comp
        (Bialgebra.comulAlgHom S (S ⊗[R] TauCeti.UpperUnitriangular.coordinateHopfAlgebra R ι)) =
    (Bialgebra.comulAlgHom S (TauCeti.UpperUnitriangular.coordinateHopfAlgebra S ι)).comp
      (baseChange R S ι).toAlgHom :=
  baseChange_comul R S ι

example (element : S ⊗[R] TauCeti.UpperUnitriangular.coordinateHopfAlgebra R ι) :
    baseChangeBialgEquiv R S ι element = baseChange R S ι element :=
  baseChangeBialgEquiv_apply R S ι element

example (element : S ⊗[R] TauCeti.UpperUnitriangular.coordinateHopfAlgebra R ι) :
    baseChange R S ι
        ((@HopfAlgebraStruct.antipode S (S ⊗[R]
          TauCeti.UpperUnitriangular.coordinateHopfAlgebra R ι)
          inferInstance inferInstance (inferInstance : HopfAlgebraStruct S
            (S ⊗[R] TauCeti.UpperUnitriangular.coordinateHopfAlgebra R ι))) element) =
      (@HopfAlgebraStruct.antipode S (TauCeti.UpperUnitriangular.coordinateHopfAlgebra S ι)
        inferInstance inferInstance (inferInstance : HopfAlgebraStruct S
          (TauCeti.UpperUnitriangular.coordinateHopfAlgebra S ι))) (baseChange R S ι element) :=
  baseChange_antipode R S ι element

private abbrev finThreeEntry (K : Type) [CommRing K] (row col : Fin 3) :
    TauCeti.UpperUnitriangular.coordinateHopfAlgebra K (Fin 3) :=
  (TauCeti.UpperUnitriangular.coordinateHopfAlgebraAlgEquiv K (Fin 3)
    (TauCeti.UpperUnitriangular.genericMatrix K (Fin 3) row col))

section FinThree

variable (K L : Type) [CommRing K] [CommRing L] [Algebra K L]

example :
    ((Algebra.TensorProduct.map (baseChange K L (Fin 3)).toAlgHom
      (baseChange K L (Fin 3)).toAlgHom).comp
        (Bialgebra.comulAlgHom L (L ⊗[K] TauCeti.UpperUnitriangular.coordinateHopfAlgebra K
          (Fin 3))))
        (1 ⊗ₜ[K] finThreeEntry K 0 2) =
      (1 ⊗ₜ[L] finThreeEntry L 0 2) +
        (finThreeEntry L 0 1 ⊗ₜ[L] finThreeEntry L 1 2) +
        (finThreeEntry L 0 2 ⊗ₜ[L] 1) := by
  have correspondence := AlgHom.congr_fun (baseChange_comul K L (Fin 3))
    (1 ⊗ₜ[K] finThreeEntry K 0 2)
  change _ = Coalgebra.comul (R := L)
      ((baseChange K L (Fin 3)) (1 ⊗ₜ[K] finThreeEntry K 0 2)) at correspondence
  rw [baseChange_tmul_entry, map_one, one_mul,
    TauCeti.UpperUnitriangular.coordinateHopfAlgebra_comul_genericMatrix_apply,
    Fin.sum_univ_three] at correspondence
  simpa only [finThreeEntry,
    TauCeti.UpperUnitriangular.genericMatrix_apply_diag, map_one] using correspondence

end FinThree

example :
    (Bialgebra.counitAlgHom (ZMod 1) (TauCeti.UpperUnitriangular.coordinateHopfAlgebra (ZMod
      1) (Fin 0))).comp
      (baseChange (ZMod 1) (ZMod 1) (Fin 0)).toAlgHom =
    Bialgebra.counitAlgHom (ZMod 1)
      (ZMod 1 ⊗[ZMod 1] TauCeti.UpperUnitriangular.coordinateHopfAlgebra (ZMod 1) (Fin 0)) :=
  baseChange_counit (ZMod 1) (ZMod 1) (Fin 0)

example :
    (Algebra.TensorProduct.map (baseChange (ZMod 1) (ZMod 1) (Fin 0)).toAlgHom
      (baseChange (ZMod 1) (ZMod 1) (Fin 0)).toAlgHom).comp
        (Bialgebra.comulAlgHom (ZMod 1)
          (ZMod 1 ⊗[ZMod 1] TauCeti.UpperUnitriangular.coordinateHopfAlgebra (ZMod 1) (Fin 0))) =
    (Bialgebra.comulAlgHom (ZMod 1) (TauCeti.UpperUnitriangular.coordinateHopfAlgebra (ZMod 1)
      (Fin 0))).comp
      (baseChange (ZMod 1) (ZMod 1) (Fin 0)).toAlgHom :=
  baseChange_comul (ZMod 1) (ZMod 1) (Fin 0)

example :
    (Algebra.TensorProduct.map (baseChange (ZMod 1) (ZMod 1) (Fin 1)).toAlgHom
      (baseChange (ZMod 1) (ZMod 1) (Fin 1)).toAlgHom).comp
        (Bialgebra.comulAlgHom (ZMod 1)
          (ZMod 1 ⊗[ZMod 1] TauCeti.UpperUnitriangular.coordinateHopfAlgebra (ZMod 1) (Fin 1))) =
    (Bialgebra.comulAlgHom (ZMod 1) (TauCeti.UpperUnitriangular.coordinateHopfAlgebra (ZMod 1)
      (Fin 1))).comp
      (baseChange (ZMod 1) (ZMod 1) (Fin 1)).toAlgHom :=
  baseChange_comul (ZMod 1) (ZMod 1) (Fin 1)

example :
    (Algebra.TensorProduct.map (baseChange ℚ ℚ (Fin 1)).toAlgHom
      (baseChange ℚ ℚ (Fin 1)).toAlgHom).comp
        (Bialgebra.comulAlgHom ℚ (ℚ ⊗[ℚ] TauCeti.UpperUnitriangular.coordinateHopfAlgebra ℚ
          (Fin 1))) =
    (Bialgebra.comulAlgHom ℚ (TauCeti.UpperUnitriangular.coordinateHopfAlgebra ℚ (Fin 1))).comp
      (baseChange ℚ ℚ (Fin 1)).toAlgHom :=
  baseChange_comul ℚ ℚ (Fin 1)

end UnitriangularCoordinateRing
