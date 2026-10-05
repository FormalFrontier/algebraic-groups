/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents, Lattice
-/
module

public import AlgebraicGroups.Algebra.UnitriangularCoordinateRing
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Base change of the native unitriangular coordinate algebra

The actual determinant-localized GL quotient commutes with extension of an
arbitrary commutative base ring. The equivalence is transported through its
published free strict-upper-coordinate presentation. Its entry laws include
lower and diagonal entries, and require neither nontrivial rings nor nonempty
indices. This is an algebra comparison, not a Hopf or scheme base-change claim.

Milne's presentation of `U_n` over a field supplies the strict-upper-coordinate
antecedent; the arbitrary-commutative-base comparison uses Christian Merten's
Mathlib `MvPolynomial.algebraTensorAlgEquiv`, whose implementation uses Yaël
Dillies's `AddMonoidAlgebra.scalarTensorEquiv`. Antoine Chambert-Loir's earlier
`MvPolynomial.scalarRTensorAlgEquiv` is a related scalar-extension formalization,
not a base-change theorem stated by Milne.

## References

* James S. Milne, *Algebraic Groups* (2017), item 2.9 (the polynomial
  presentation of `U_n` over a field).
* Antoine Chambert-Loir, Mathlib,
  `Mathlib.RingTheory.TensorProduct.MvPolynomial` (the related earlier
  `MvPolynomial.scalarRTensorAlgEquiv`).
* Christian Merten, Mathlib, `Mathlib.RingTheory.TensorProduct.MvPolynomial`
  (`MvPolynomial.algebraTensorAlgEquiv` and its entry lemmas).
* Yaël Dillies, Mathlib, `Mathlib.RingTheory.TensorProduct.MonoidAlgebra`
  (`AddMonoidAlgebra.scalarTensorEquiv`, used in the polynomial equivalence).
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u

namespace UnitriangularCoordinateRing

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (ι : Type u) [Fintype ι] [LinearOrder ι]

/-- Extension of scalars for the actual determinant-localized unitriangular
coordinate quotient, with its natural `S`-algebra structure. The strict-upper
presentation specializes to Milne, *Algebraic Groups*, item 2.9 over a field;
the scalar-extension step uses Christian Merten's Mathlib
`MvPolynomial.algebraTensorAlgEquiv`, now implemented using Yaël Dillies's
`AddMonoidAlgebra.scalarTensorEquiv`. Antoine Chambert-Loir's
`MvPolynomial.scalarRTensorAlgEquiv` is a related earlier equivalence. -/
def baseChange : S ⊗[R] CoordinateRing R ι ≃ₐ[S] CoordinateRing S ι :=
  ((Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) (freeEquiv R ι).symm).trans
    (MvPolynomial.algebraTensorAlgEquiv R S)).trans (freeEquiv S ι)

/-- The comparison respects the entire strict-upper polynomial presentation. -/
theorem baseChange_presentation (x : S ⊗[R] FreeCoordinateRing R ι) :
    baseChange R S ι
        (Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) (freeEquiv R ι) x) =
      freeEquiv S ι (MvPolynomial.algebraTensorAlgEquiv R S x) := by
  change freeEquiv S ι (MvPolynomial.algebraTensorAlgEquiv R S
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) (freeEquiv R ι)).symm
      (Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) (freeEquiv R ι) x))) = _
  rw [AlgEquiv.symm_apply_apply]

/-- On polynomial representatives, coefficients are extended by the given
`R`-algebra structure and the tensor coefficient acts by `S`-scalar multiplication. -/
@[simp] theorem baseChange_tmul_freeEquiv (s : S) (p : FreeCoordinateRing R ι) :
    baseChange R S ι (s ⊗ₜ[R] freeEquiv R ι p) =
      freeEquiv S ι (s • MvPolynomial.map (algebraMap R S) p) := by
  simp [baseChange]

/-- Coefficients from the new base ring are preserved. -/
@[simp] theorem baseChange_tmul_one (s : S) :
    baseChange R S ι (s ⊗ₜ[R] (1 : CoordinateRing R ι)) =
      algebraMap S (CoordinateRing S ι) s := by
  simpa using (baseChange R S ι).commutes s

/-- The forward law for every matrix entry in the actual quotient, not just
the freely varying strictly upper entries. -/
@[simp] theorem baseChange_tmul_entry (s : S) (i j : ι) :
    baseChange R S ι
        (s ⊗ₜ[R] quotient R ι (GeneralLinearCoordinateRing.matrix R ι i j)) =
      algebraMap S (CoordinateRing S ι) s *
        quotient S ι (GeneralLinearCoordinateRing.matrix S ι i j) := by
  rcases lt_trichotomy i j with hij | hij | hji
  · simpa only [MvPolynomial.map_X, Algebra.smul_def, map_mul, AlgEquiv.commutes,
      freeEquiv_variable] using
      baseChange_tmul_freeEquiv R S ι s (MvPolynomial.X ⟨(i, j), hij⟩)
  · subst j
    simp only [quotient_diag, baseChange_tmul_one, mul_one]
  · simp only [quotient_lower R ι i j hji, quotient_lower S ι i j hji,
      TensorProduct.tmul_zero, map_zero, mul_zero]

/-- The inverse comparison sends each actual quotient entry to its scalar
extension with tensor coefficient one. -/
@[simp] theorem baseChange_symm_entry (i j : ι) :
    (baseChange R S ι).symm
        (quotient S ι (GeneralLinearCoordinateRing.matrix S ι i j)) =
      1 ⊗ₜ[R] quotient R ι (GeneralLinearCoordinateRing.matrix R ι i j) := by
  apply (baseChange R S ι).injective
  simp only [AlgEquiv.apply_symm_apply, baseChange_tmul_entry, map_one, one_mul]

/-- The inverse coefficient law is valid also over the zero ring. -/
@[simp] theorem baseChange_symm_algebraMap (s : S) :
    (baseChange R S ι).symm (algebraMap S (CoordinateRing S ι) s) =
      s ⊗ₜ[R] (1 : CoordinateRing R ι) := by
  apply (baseChange R S ι).injective
  simp only [AlgEquiv.apply_symm_apply, baseChange_tmul_one]

end UnitriangularCoordinateRing
