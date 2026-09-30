module

public import AlgebraicGroups.Algebra.UnitriangularBaseChangeCoherence
public import Mathlib.Data.ZMod.Basic

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u

namespace UnitriangularCoordinateRing

variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
  (ι : Type u) [Fintype ι] [LinearOrder ι]

example : baseChange R R ι =
    Algebra.TensorProduct.lid R (CoordinateRing R ι) :=
  baseChange_self R ι

example :
    (Algebra.TensorProduct.cancelBaseChange R S T T (CoordinateRing R ι)).trans
        (baseChange R T ι) =
      (Algebra.TensorProduct.congr
          (AlgEquiv.refl : T ≃ₐ[T] T)
          (baseChange R S ι)).trans
        (baseChange S T ι) :=
  baseChange_tower R S T ι

example : baseChange (ZMod 1) (ZMod 1) (Fin 0) =
    Algebra.TensorProduct.lid (ZMod 1)
      (CoordinateRing (ZMod 1) (Fin 0)) :=
  baseChange_self (ZMod 1) (Fin 0)

example : baseChange ℤ ℤ (Fin 1) =
    Algebra.TensorProduct.lid ℤ (CoordinateRing ℤ (Fin 1)) :=
  baseChange_self ℤ (Fin 1)

example :
    (Algebra.TensorProduct.cancelBaseChange ℤ (ZMod 1) (ZMod 1)
      (ZMod 1) (CoordinateRing ℤ (Fin 1))).trans
        (baseChange ℤ (ZMod 1) (Fin 1)) =
      (Algebra.TensorProduct.congr
          (AlgEquiv.refl : ZMod 1 ≃ₐ[ZMod 1] ZMod 1)
          (baseChange ℤ (ZMod 1) (Fin 1))).trans
        (baseChange (ZMod 1) (ZMod 1) (Fin 1)) :=
  baseChange_tower ℤ (ZMod 1) (ZMod 1) (Fin 1)

example :
    (Algebra.TensorProduct.cancelBaseChange ℤ ℚ ℚ ℚ
      (CoordinateRing ℤ (Fin 2))).trans
        (baseChange ℤ ℚ (Fin 2)) =
      (Algebra.TensorProduct.congr
          (AlgEquiv.refl : ℚ ≃ₐ[ℚ] ℚ)
          (baseChange ℤ ℚ (Fin 2))).trans
        (baseChange ℚ ℚ (Fin 2)) :=
  baseChange_tower ℤ ℚ ℚ (Fin 2)

end UnitriangularCoordinateRing
