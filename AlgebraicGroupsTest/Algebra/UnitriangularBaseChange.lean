/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents, Lattice
-/
module

public import AlgebraicGroups.Algebra.UnitriangularBaseChange
public import Mathlib.Data.ZMod.Basic

/-! Ordinary clients of the actual-quotient scalar-extension comparison. -/

@[expose] public section

noncomputable section

open UnitriangularCoordinateRing
open scoped TensorProduct

variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]

example (ι : Type) [Fintype ι] [LinearOrder ι] :
    S ⊗[R] UnitriangularCoordinateRing.CoordinateRing R ι ≃ₐ[S]
      UnitriangularCoordinateRing.CoordinateRing S ι :=
  baseChange R S ι

example (s : S) :
    baseChange R S (Fin 3)
        (s ⊗ₜ[R] quotient R (Fin 3) (GeneralLinearCoordinateRing.matrix R (Fin 3) 0 2)) =
      algebraMap S _ s *
        quotient S (Fin 3) (GeneralLinearCoordinateRing.matrix S (Fin 3) 0 2) :=
  baseChange_tmul_entry R S (Fin 3) s 0 2

example :
    (baseChange R S (Fin 3)).symm
        (quotient S (Fin 3) (GeneralLinearCoordinateRing.matrix S (Fin 3) 2 0)) =
      1 ⊗ₜ[R] quotient R (Fin 3) (GeneralLinearCoordinateRing.matrix R (Fin 3) 2 0) :=
  baseChange_symm_entry R S (Fin 3) 2 0

example (s : S) :
    baseChange R S (Fin 1)
        (s ⊗ₜ[R] quotient R (Fin 1) (GeneralLinearCoordinateRing.matrix R (Fin 1) 0 0)) =
      algebraMap S _ s := by
  simpa only [quotient_diag, mul_one] using
    baseChange_tmul_entry R S (Fin 1) s 0 0

example :
    S ⊗[R] UnitriangularCoordinateRing.CoordinateRing R (Fin 0) ≃ₐ[S]
      UnitriangularCoordinateRing.CoordinateRing S (Fin 0) :=
  baseChange R S (Fin 0)

-- Infer the concrete tensor structures from the public comparison itself.
example := baseChange ℤ (ZMod 1) (Fin 0)

example := baseChange_symm_algebraMap ℤ (ZMod 1) (Fin 1) (0 : ZMod 1)

example (p : FreeCoordinateRing R (Fin 3)) (s : S) :
    baseChange R S (Fin 3) (s ⊗ₜ[R] freeEquiv R (Fin 3) p) =
      freeEquiv S (Fin 3) (s • MvPolynomial.map (algebraMap R S) p) :=
  baseChange_tmul_freeEquiv R S (Fin 3) s p
