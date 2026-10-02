/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.UnitriangularStagePolynomial
public import Mathlib.Data.ZMod.Basic

@[expose] public section

noncomputable section

namespace UnitriangularStageCoordinateRing

variable (K : Type) [CommRing K] (n r : ℕ)

example : CoordinateRing K n r ≃ₐ[K] MvPolynomial (SurvivingPair n r) K :=
  polynomialEquiv K n r

example (s : SurvivingPair n r) :
    polynomialEquiv K n r
      (quotient K n r (entry K n s.1.1.1 s.1.1.2)) = MvPolynomial.X s :=
  polynomialEquiv_surviving K n r s

example (s : SurvivingPair n r) :
    (polynomialEquiv K n r).symm (MvPolynomial.X s) =
      quotient K n r (entry K n s.1.1.1 s.1.1.2) :=
  polynomialEquiv_symm_X K n r s

example (p : UnitriangularCoordinateRing.StrictUpperPair (Fin n))
    (hgap : p.1.2.val < p.1.1.val + r) :
    polynomialEquiv K n r
      (quotient K n r (entry K n p.1.1 p.1.2)) = 0 :=
  polynomialEquiv_forbidden K n r p hgap

example (k : K) :
    polynomialEquiv K n r
      (@algebraMap K (CoordinateRing K n r) _
        (inferInstance : Semiring (CoordinateRing K n r)) _ k) =
      (MvPolynomial.C k : MvPolynomial (SurvivingPair n r) K) :=
  polynomialEquiv_C K n r k

example (k : K) :
    (polynomialEquiv K n r).symm
      (MvPolynomial.C k : MvPolynomial (SurvivingPair n r) K) =
      @algebraMap K (CoordinateRing K n r) _
        (inferInstance : Semiring (CoordinateRing K n r)) _ k :=
  polynomialEquiv_symm_C K n r k

example : CoordinateRing ℤ 0 0 ≃ₐ[ℤ] MvPolynomial (SurvivingPair 0 0) ℤ :=
  polynomialEquiv ℤ 0 0

example : CoordinateRing ℤ 1 1 ≃ₐ[ℤ] MvPolynomial (SurvivingPair 1 1) ℤ :=
  polynomialEquiv ℤ 1 1

example : CoordinateRing ℤ 3 0 ≃ₐ[ℤ] MvPolynomial (SurvivingPair 3 0) ℤ :=
  polynomialEquiv ℤ 3 0

example : CoordinateRing ℤ 3 1 ≃ₐ[ℤ] MvPolynomial (SurvivingPair 3 1) ℤ :=
  polynomialEquiv ℤ 3 1

example : CoordinateRing ℤ 3 2 ≃ₐ[ℤ] MvPolynomial (SurvivingPair 3 2) ℤ :=
  polynomialEquiv ℤ 3 2

example : CoordinateRing ℤ 3 3 ≃ₐ[ℤ] MvPolynomial (SurvivingPair 3 3) ℤ :=
  polynomialEquiv ℤ 3 3

example : CoordinateRing ℤ 3 4 ≃ₐ[ℤ] MvPolynomial (SurvivingPair 3 4) ℤ :=
  polynomialEquiv ℤ 3 4

example : CoordinateRing (ZMod 1) 0 4 ≃ₐ[ZMod 1]
    MvPolynomial (SurvivingPair 0 4) (ZMod 1) :=
  polynomialEquiv (ZMod 1) 0 4

example : CoordinateRing (ZMod 1) 1 2 ≃ₐ[ZMod 1]
    MvPolynomial (SurvivingPair 1 2) (ZMod 1) :=
  polynomialEquiv (ZMod 1) 1 2

example : CoordinateRing (ZMod 1) 3 0 ≃ₐ[ZMod 1]
    MvPolynomial (SurvivingPair 3 0) (ZMod 1) :=
  polynomialEquiv (ZMod 1) 3 0

example : CoordinateRing (ZMod 1) 3 1 ≃ₐ[ZMod 1]
    MvPolynomial (SurvivingPair 3 1) (ZMod 1) :=
  polynomialEquiv (ZMod 1) 3 1

example : CoordinateRing (ZMod 1) 3 2 ≃ₐ[ZMod 1]
    MvPolynomial (SurvivingPair 3 2) (ZMod 1) :=
  polynomialEquiv (ZMod 1) 3 2

example : CoordinateRing (ZMod 1) 3 3 ≃ₐ[ZMod 1]
    MvPolynomial (SurvivingPair 3 3) (ZMod 1) :=
  polynomialEquiv (ZMod 1) 3 3

example : CoordinateRing (ZMod 1) 3 4 ≃ₐ[ZMod 1]
    MvPolynomial (SurvivingPair 3 4) (ZMod 1) :=
  polynomialEquiv (ZMod 1) 3 4

example :
    polynomialEquiv ℤ 3 2
      (quotient ℤ 3 2 (entry ℤ 3 (0 : Fin 3) (2 : Fin 3))) =
        MvPolynomial.X (⟨⟨(0, 2), by decide⟩, by decide⟩ : SurvivingPair 3 2) := by
  simpa using polynomialEquiv_surviving ℤ 3 2
    (⟨⟨(0, 2), by decide⟩, by decide⟩ : SurvivingPair 3 2)

example :
    polynomialEquiv (ZMod 1) 3 2
      (quotient (ZMod 1) 3 2 (entry (ZMod 1) 3 (0 : Fin 3) (1 : Fin 3))) = 0 :=
  polynomialEquiv_forbidden (ZMod 1) 3 2 ⟨((0 : Fin 3), (1 : Fin 3)), by decide⟩
    (by decide)

end UnitriangularStageCoordinateRing
