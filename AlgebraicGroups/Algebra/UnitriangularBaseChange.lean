/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents, Lattice
-/
module

public import TauCeti.Algebra.AlgebraicGroup.UpperUnitriangular.Scheme
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Base change of the native unitriangular coordinate algebra

The canonical strict-upper polynomial coordinate Hopf algebra commutes with extension of an
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

open TauCeti.UpperUnitriangular

universe u

namespace UnitriangularCoordinateRing

section

universe v w

variable (R : Type u) [CommRing R] (S : Type v) [CommSemiring S] [Algebra R S]
  (ι : Type u) [Fintype ι] [LinearOrder ι] (B : Type w) [Semiring B] [Algebra S B]

/-- Algebra homomorphisms from the scalar extension of the unitriangular coordinate
Hopf algebra are determined by the strictly upper entries with tensor coefficient
one. Mathlib's `Algebra.TensorProduct.ext_ring` reduces this to
`algHom_ext_entries`. -/
theorem tensor_algHom_ext_entries
    (f g : S ⊗[R] coordinateHopfAlgebra R ι →ₐ[S] B)
    (h : ∀ p : Index ι,
      f (1 ⊗ₜ[R] (coordinateHopfAlgebraAlgEquiv R ι (genericMatrix R ι p.1.1 p.1.2))) =
        g (1 ⊗ₜ[R] (coordinateHopfAlgebraAlgEquiv R ι (genericMatrix R ι p.1.1 p.1.2)))) : f =
          g := by
  let : Algebra R B := Algebra.compHom B (algebraMap R S)
  let : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  apply Algebra.TensorProduct.ext_ring
  apply coordinateHopfAlgebra_algHom_ext R ι
  intro p
  have hp := h p
  rw [genericMatrix_apply_of_lt R ι p.2] at hp
  exact hp

end

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (ι : Type u) [Fintype ι] [LinearOrder ι]

/-- Extension of scalars for the actual canonical unitriangular
coordinate Hopf algebra, with its natural `S`-algebra structure. The strict-upper
presentation specializes to Milne, *Algebraic Groups*, item 2.9 over a field;
the scalar-extension step uses Christian Merten's Mathlib
`MvPolynomial.algebraTensorAlgEquiv`, now implemented using Yaël Dillies's
`AddMonoidAlgebra.scalarTensorEquiv`. Antoine Chambert-Loir's
`MvPolynomial.scalarRTensorAlgEquiv` is a related earlier equivalence. -/
def baseChange : S ⊗[R] coordinateHopfAlgebra R ι ≃ₐ[S] coordinateHopfAlgebra S ι :=
  ((Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) (coordinateHopfAlgebraAlgEquiv R
    ι).symm).trans
    (MvPolynomial.algebraTensorAlgEquiv R S)).trans (coordinateHopfAlgebraAlgEquiv S ι)

/-- The comparison respects the entire strict-upper polynomial presentation. -/
theorem baseChange_presentation (x : S ⊗[R] CoordinateRing R ι) :
    baseChange R S ι
        (Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S)
          (coordinateHopfAlgebraAlgEquiv R ι) x) =
      coordinateHopfAlgebraAlgEquiv S ι (MvPolynomial.algebraTensorAlgEquiv R S x) := by
  change coordinateHopfAlgebraAlgEquiv S ι (MvPolynomial.algebraTensorAlgEquiv R S
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) (coordinateHopfAlgebraAlgEquiv R
      ι)).symm
      (Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) (coordinateHopfAlgebraAlgEquiv
        R ι) x))) = _
  rw [AlgEquiv.symm_apply_apply]

/-- On polynomial representatives, coefficients are extended by the given
`R`-algebra structure and the tensor coefficient acts by `S`-scalar multiplication. -/
@[simp] theorem baseChange_tmul_freeEquiv (s : S) (p : CoordinateRing R ι) :
    baseChange R S ι (s ⊗ₜ[R] coordinateHopfAlgebraAlgEquiv R ι p) =
      coordinateHopfAlgebraAlgEquiv S ι (s • MvPolynomial.map (algebraMap R S) p) := by
  simp [baseChange]

/-- Coefficients from the new base ring are preserved. -/
@[simp] theorem baseChange_tmul_one (s : S) :
    baseChange R S ι (s ⊗ₜ[R] (1 : coordinateHopfAlgebra R ι)) =
      algebraMap S (coordinateHopfAlgebra S ι) s := by
  simpa using (baseChange R S ι).commutes s

/-- The forward law for every matrix entry in the canonical coordinate algebra, not just
the freely varying strictly upper entries. -/
theorem baseChange_tmul_entry (s : S) (i j : ι) :
    baseChange R S ι
        (s ⊗ₜ[R] (coordinateHopfAlgebraAlgEquiv R ι (genericMatrix R ι i j))) =
      algebraMap S (coordinateHopfAlgebra S ι) s *
        (coordinateHopfAlgebraAlgEquiv S ι (genericMatrix S ι i j)) := by
  rcases lt_trichotomy i j with hij | hij | hji
  · rw [genericMatrix_apply_of_lt R ι hij, genericMatrix_apply_of_lt S ι hij]
    simpa only [MvPolynomial.map_X, Algebra.smul_def, map_mul, AlgEquiv.commutes] using
      baseChange_tmul_freeEquiv R S ι s (MvPolynomial.X ⟨(i, j), hij⟩)
  · subst j
    simp only [genericMatrix_apply_diag, map_one, baseChange_tmul_one, mul_one]
  · simp only [genericMatrix_apply_eq_zero_of_gt R ι hji,
      genericMatrix_apply_eq_zero_of_gt S ι hji, map_zero,
      TensorProduct.tmul_zero, mul_zero]

/-- The inverse comparison sends each canonical coordinate algebra entry to its scalar
extension with tensor coefficient one. -/
@[simp] theorem baseChange_symm_entry (i j : ι) :
    (baseChange R S ι).symm
        ((coordinateHopfAlgebraAlgEquiv S ι (genericMatrix S ι i j))) =
      1 ⊗ₜ[R] (coordinateHopfAlgebraAlgEquiv R ι (genericMatrix R ι i j)) := by
  apply (baseChange R S ι).injective
  simp only [AlgEquiv.apply_symm_apply, baseChange_tmul_entry, map_one, one_mul]

/- The inverse coefficient law, valid also over the zero ring, is the standard
`AlgEquiv.commutes` formula together with the tensor-product algebra map. -/

end UnitriangularCoordinateRing
