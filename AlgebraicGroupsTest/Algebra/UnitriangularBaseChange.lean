/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents, Lattice
-/
module

public import AlgebraicGroups.Algebra.UnitriangularBaseChange
public import Mathlib.Data.ZMod.Basic

/-! Ordinary clients of the actual-(TauCeti.UpperUnitriangular.coordinateHopfAlgebraAlgEquiv
  scalar  )-extension comparison. -/

@[expose] public section

noncomputable section


open UnitriangularCoordinateRing
open scoped TensorProduct

variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]

example (ι : Type) [Fintype ι] [LinearOrder ι] :
    S ⊗[R] (TauCeti.UpperUnitriangular.coordinateHopfAlgebra R ι) ≃ₐ[S]
      (TauCeti.UpperUnitriangular.coordinateHopfAlgebra S ι) :=
  baseChange R S ι

example (s : S) :
    baseChange R S (Fin 3)
        (s ⊗ₜ[R] (TauCeti.UpperUnitriangular.coordinateHopfAlgebraAlgEquiv R (Fin 3)
          (TauCeti.UpperUnitriangular.genericMatrix R (Fin 3) 0 2))) =
      algebraMap S _ s *
        (TauCeti.UpperUnitriangular.coordinateHopfAlgebraAlgEquiv S (Fin 3)
          (TauCeti.UpperUnitriangular.genericMatrix S (Fin 3) 0 2)) :=
  baseChange_tmul_entry R S (Fin 3) s 0 2

example :
    (baseChange R S (Fin 3)).symm
        ((TauCeti.UpperUnitriangular.coordinateHopfAlgebraAlgEquiv S (Fin 3)
          (TauCeti.UpperUnitriangular.genericMatrix S (Fin 3) 2 0))) =
      1 ⊗ₜ[R] (TauCeti.UpperUnitriangular.coordinateHopfAlgebraAlgEquiv R (Fin 3)
        (TauCeti.UpperUnitriangular.genericMatrix R (Fin 3) 2 0)) :=
  baseChange_symm_entry R S (Fin 3) 2 0

example (s : S) :
    baseChange R S (Fin 1)
        (s ⊗ₜ[R] (TauCeti.UpperUnitriangular.coordinateHopfAlgebraAlgEquiv R (Fin 1)
          (TauCeti.UpperUnitriangular.genericMatrix R (Fin 1) 0 0))) =
      algebraMap S _ s := by
  simpa only [TauCeti.UpperUnitriangular.genericMatrix_apply_diag, map_one, mul_one] using
    baseChange_tmul_entry R S (Fin 1) s 0 0

example :
    S ⊗[R] (TauCeti.UpperUnitriangular.coordinateHopfAlgebra R (Fin 0)) ≃ₐ[S]
      (TauCeti.UpperUnitriangular.coordinateHopfAlgebra S (Fin 0)) :=
  baseChange R S (Fin 0)

-- Infer the concrete tensor structures from the public comparison itself.
example := baseChange ℤ (ZMod 1) (Fin 0)

example (s : S) : (baseChange R S (Fin 1)).symm
    (algebraMap S (TauCeti.UpperUnitriangular.coordinateHopfAlgebra S (Fin 1)) s) =
    s ⊗ₜ[R] (1 : TauCeti.UpperUnitriangular.coordinateHopfAlgebra R (Fin 1)) := by
  simp

example : (baseChange ℤ (ZMod 1) (Fin 1)).symm
    (algebraMap (ZMod 1) (TauCeti.UpperUnitriangular.coordinateHopfAlgebra (ZMod 1) (Fin 1))
      (0 : ZMod 1)) = 0 := by
  simp

example (p : TauCeti.UpperUnitriangular.CoordinateRing R (Fin 3)) (s : S) :
    baseChange R S (Fin 3) (s ⊗ₜ[R] TauCeti.UpperUnitriangular.coordinateHopfAlgebraAlgEquiv R
      (Fin 3) p) =
      TauCeti.UpperUnitriangular.coordinateHopfAlgebraAlgEquiv S (Fin 3) (s • MvPolynomial.map
        (algebraMap R S) p) :=
  baseChange_tmul_freeEquiv R S (Fin 3) s p
