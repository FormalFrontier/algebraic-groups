/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.UnitriangularBaseChange
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Identity and tower laws for unitriangular coordinate base change

These equations identify the published base-change equivalence of the actual
determinant-localized quotient with the tensor unit and scalar-tower cancellation.
They use the strict-upper-coordinate presentation (Milne's field case) and
Mathlib's polynomial scalar extension and tensor-algebra coherence maps; the
arbitrary-commutative-base coherence equations are established here.

## References

* James S. Milne, *Algebraic Groups* (2017), item 2.9 (the underlying
  strict-upper-coordinate presentation over a field).
* Antoine Chambert-Loir, Mathlib, `Mathlib.RingTheory.TensorProduct.MvPolynomial`
  (the related earlier `MvPolynomial.scalarRTensorAlgEquiv`).
* Christian Merten, Mathlib, `Mathlib.RingTheory.TensorProduct.MvPolynomial`
  (`MvPolynomial.algebraTensorAlgEquiv` used by the algebra comparison), and
  `Mathlib.RingTheory.TensorProduct.Maps` (`Algebra.TensorProduct.cancelBaseChange`).
* Yaël Dillies, Mathlib, `Mathlib.RingTheory.TensorProduct.MonoidAlgebra`
  (`AddMonoidAlgebra.scalarTensorEquiv` implementing the polynomial equivalence).
* Kevin Buzzard, Mathlib4 port of `Algebra.TensorProduct.lid`, now in
  `Mathlib.RingTheory.TensorProduct.Maps`.
* Kim Morrison and Johan Commelin, Mathlib, contributors to the wider
  `Mathlib.RingTheory.TensorProduct.Maps` module.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u

namespace UnitriangularCoordinateRing

/-- Base change along the identity agrees with the algebra tensor unit
`Algebra.TensorProduct.lid` from Mathlib's `RingTheory.TensorProduct.Maps`. -/
theorem baseChange_self (R : Type u) [CommRing R]
    (ι : Type u) [Fintype ι] [LinearOrder ι] :
    baseChange R R ι =
      Algebra.TensorProduct.lid R (CoordinateRing R ι) := by
  apply AlgEquiv.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
      let p := (freeEquiv R ι).symm a
      have ha : freeEquiv R ι p = a := (freeEquiv R ι).apply_symm_apply a
      rw [← ha, baseChange_tmul_freeEquiv, Algebra.TensorProduct.lid_tmul]
      simp only [Algebra.algebraMap_self, MvPolynomial.map_id, map_smul]
  | add x y hx hy =>
      simp only [map_add, hx, hy]

private theorem baseChange_tower_polynomial (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T]
    (ι : Type u) [Fintype ι] [LinearOrder ι]
    (s : S) (p : FreeCoordinateRing R ι) :
    MvPolynomial.map (algebraMap S T)
        (s • MvPolynomial.map (algebraMap R S) p) =
      (algebraMap S T s) • MvPolynomial.map (algebraMap R T) p := by
  simp only [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C,
    MvPolynomial.map_map, ← IsScalarTower.algebraMap_eq R S T]

/-- Successive base changes agree with Mathlib's
`Algebra.TensorProduct.cancelBaseChange` as algebra equivalences. -/
theorem baseChange_tower (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T]
    (ι : Type u) [Fintype ι] [LinearOrder ι] :
    (Algebra.TensorProduct.cancelBaseChange R S T T (CoordinateRing R ι)).trans
        (baseChange R T ι) =
      (Algebra.TensorProduct.congr
          (AlgEquiv.refl : T ≃ₐ[T] T)
          (baseChange R S ι)).trans
        (baseChange S T ι) := by
  apply AlgEquiv.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul t y =>
      induction y using TensorProduct.inductionOn with
      | tmul s a =>
          let p := (freeEquiv R ι).symm a
          have ha : freeEquiv R ι p = a := (freeEquiv R ι).apply_symm_apply a
          rw [← ha, AlgEquiv.trans_apply, AlgEquiv.trans_apply,
            Algebra.TensorProduct.cancelBaseChange_tmul,
            Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
            baseChange_tmul_freeEquiv R T ι]
          change (freeEquiv T ι) ((s • t) • MvPolynomial.map (algebraMap R T) p) =
            baseChange S T ι
              (t ⊗ₜ[S] (baseChange R S ι (s ⊗ₜ[R] freeEquiv R ι p)))
          rw [baseChange_tmul_freeEquiv R S ι,
            baseChange_tmul_freeEquiv S T ι]
          rw [baseChange_tower_polynomial R S T ι]
          simp only [Algebra.smul_def, mul_comm (algebraMap S T s) t,
            map_mul, mul_assoc]
      | add y z hy hz =>
          simp only [TensorProduct.tmul_add, map_add, AlgEquiv.trans_apply] at *
          rw [hy, hz]
  | add x y hx hy =>
      simp only [map_add, hx, hy]

end UnitriangularCoordinateRing
