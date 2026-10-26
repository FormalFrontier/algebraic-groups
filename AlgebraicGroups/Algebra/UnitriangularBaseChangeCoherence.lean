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
  have hmaps : (baseChange R R ι).toAlgHom =
      (Algebra.TensorProduct.lid R (CoordinateRing R ι)).toAlgHom := by
    apply tensor_algHom_ext_entries R R ι (CoordinateRing R ι)
    intro p
    change baseChange R R ι
        (1 ⊗ₜ[R] quotient R ι
          (GeneralLinearCoordinateRing.matrix R ι p.1.1 p.1.2)) =
      Algebra.TensorProduct.lid R (CoordinateRing R ι)
        (1 ⊗ₜ[R] quotient R ι
          (GeneralLinearCoordinateRing.matrix R ι p.1.1 p.1.2))
    rw [baseChange_tmul_entry, Algebra.TensorProduct.lid_tmul]
    simp only [map_one, one_mul, one_smul]
  exact AlgEquiv.ext (fun x => congrArg (fun φ => φ x) hmaps)

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
  let : Algebra S (CoordinateRing T ι) :=
    Algebra.compHom (CoordinateRing T ι) (algebraMap S T)
  let : IsScalarTower S T (CoordinateRing T ι) :=
    inferInstance
  -- Restricting algebra homomorphisms uses the algebra-induced scalar actions.
  let := IsScalarTower.of_algebraMap_eq
    (R := S) (S := T) (A := CoordinateRing T ι) (fun _ => rfl)
  have hmaps :
      ((Algebra.TensorProduct.cancelBaseChange R S T T (CoordinateRing R ι)).trans
        (baseChange R T ι)).toAlgHom =
      ((Algebra.TensorProduct.congr
        (AlgEquiv.refl : T ≃ₐ[T] T) (baseChange R S ι)).trans
          (baseChange S T ι)).toAlgHom := by
    apply Algebra.TensorProduct.ext_ring
    apply tensor_algHom_ext_entries R S ι (CoordinateRing T ι)
    intro p
    change baseChange R T ι
        (Algebra.TensorProduct.cancelBaseChange R S T T (CoordinateRing R ι)
          (1 ⊗ₜ[S] (1 ⊗ₜ[R] quotient R ι
            (GeneralLinearCoordinateRing.matrix R ι p.1.1 p.1.2)))) =
      baseChange S T ι
        (Algebra.TensorProduct.congr
          (AlgEquiv.refl : T ≃ₐ[T] T) (baseChange R S ι)
          (1 ⊗ₜ[S] (1 ⊗ₜ[R] quotient R ι
            (GeneralLinearCoordinateRing.matrix R ι p.1.1 p.1.2))))
    rw [Algebra.TensorProduct.cancelBaseChange_tmul,
      Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
    change baseChange R T ι
        (((1 : S) • (1 : T)) ⊗ₜ[R] quotient R ι
          (GeneralLinearCoordinateRing.matrix R ι p.1.1 p.1.2)) =
      baseChange S T ι
        ((1 : T) ⊗ₜ[S] baseChange R S ι
          ((1 : S) ⊗ₜ[R] quotient R ι
            (GeneralLinearCoordinateRing.matrix R ι p.1.1 p.1.2)))
    simp only [one_smul, baseChange_tmul_entry, map_one, one_mul]
  exact AlgEquiv.ext (fun x => congrArg (fun φ => φ x) hmaps)

end UnitriangularCoordinateRing
