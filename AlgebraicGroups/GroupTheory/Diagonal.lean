/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Diagonal subgroups of matrix general linear groups

Milne's diagonal subgroup `D_n` of `GL_n` is defined on algebras over a field.
Here the index may be any finite decidable type and the coefficient ring any commutative ring.
The identification with tuples of units uses Mathlib's diagonal ring map and unit-product
equivalence; no ordering or nonempty index is required.

## References

* J. S. Milne, *Algebraic Groups* (2017), §2.9 (p. 42), for `D_n`, and §12.d
  (p. 234, after Definition 12.11), for its product-of-multiplicative-groups description.
* Mathlib, `Mathlib.Data.Matrix.Basic` (`Matrix.diagonalRingHom`),
  `Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs`,
  `Mathlib.LinearAlgebra.Matrix.Determinant.Basic` (`Matrix.det_diagonal`),
  `Mathlib.LinearAlgebra.Matrix.NonsingularInverse` (`Matrix.isUnits_det_units`), and
  `Mathlib.Algebra.Group.Pi.Units` (`MulEquiv.piUnits`).
-/

@[expose] public section

noncomputable section

universe u

namespace Matrix

variable (ι : Type u) [Fintype ι] [DecidableEq ι] (R : Type u) [CommRing R]

/-- Invertible matrices whose off-diagonal entries vanish, generalizing Milne's
`D_n` over a field (*Algebraic Groups*, §2.9) to commutative rings. -/
def diagonalSubgroup : Subgroup (GeneralLinearGroup ι R) where
  carrier := {g | ∀ i j, i ≠ j → g i j = 0}
  one_mem' := by
    intro i j hij
    simp [hij]
  mul_mem' := by
    intro a b ha hb i j hij
    change ((a : Matrix ι ι R) * (b : Matrix ι ι R)) i j = 0
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hik : i = k
    · subst k
      rw [hb i j hij, mul_zero]
    · rw [ha i k hik, zero_mul]
  inv_mem' := by
    intro g hg
    have hmatrix : (g : Matrix ι ι R) = diagonal (fun i => g i i) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp
      · simp [hg i j hij, diagonal_apply_ne _ hij]
    have hdet : IsUnit (∏ i, g i i) := by
      rw [← det_diagonal, ← hmatrix]
      exact isUnits_det_units g
    let d : ι → Rˣ := fun i => ((IsUnit.prod_univ_iff.mp hdet) i).unit
    have heq : TauCeti.diagGL (ι := ι) (k := R) d = g := by
      apply Units.ext
      ext i j
      by_cases hij : i = j
      · subst j
        simp [TauCeti.diagGL_apply, d]
      · simpa [TauCeti.diagGL_apply, hij] using (hg i j hij).symm
    rw [← heq]
    intro i j hij
    have hinv : (TauCeti.diagGL (ι := ι) (k := R) d)⁻¹ = TauCeti.diagGL (ι := ι) (k := R) (d⁻¹) :=
      by
      exact (map_inv (TauCeti.diagGL (ι := ι) (k := R)) d).symm
    rw [hinv, TauCeti.diagGL_apply, ite_eq_right hij]

/-- The native diagonal general linear group, including empty indices and zero rings. -/
abbrev DiagonalGroup := diagonalSubgroup ι R

namespace DiagonalGroup

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {R S : Type u} [CommRing R] [CommRing S]

/-- Inclusion into the native matrix general linear group. -/
def inclusion : DiagonalGroup ι R →* GeneralLinearGroup ι R :=
  (diagonalSubgroup ι R).subtype

@[ext] theorem ext {g h : DiagonalGroup ι R}
    (heq : ∀ i, g.1 i i = h.1 i i) : g = h := by
  apply Subtype.ext
  apply GeneralLinearGroup.ext
  intro i j
  by_cases hij : i = j
  · subst j
    exact heq i
  · exact (g.2 i j hij).trans (h.2 i j hij).symm

/-- The diagonal entry of a native invertible diagonal matrix is a unit. -/
theorem isUnit_entry (g : DiagonalGroup ι R) (i : ι) : IsUnit (g.1 i i) := by
  exact TauCeti.isUnit_apply_of_isDiag g.2 i

/-- The diagonal subgroup is multiplicatively equivalent to tuples of scalar units;
compare Milne, *Algebraic Groups* (2017), §12.d (p. 234). -/
def unitsEquiv : DiagonalGroup ι R ≃* (ι → Rˣ) where
  toFun g i := (isUnit_entry g i).unit
  invFun d := ⟨TauCeti.diagGL (ι := ι) (k := R) d, by
    intro i j hij
    simp [TauCeti.diagGL_apply, hij]⟩
  left_inv g := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    by_cases hij : i = j
    · subst j
      simp [TauCeti.diagGL_apply]
    · simpa [TauCeti.diagGL_apply, hij] using (g.2 i j hij).symm
  right_inv d := by
    funext i
    apply Units.ext
    simp [TauCeti.diagGL_apply]
  map_mul' g h := by
    funext i
    apply Units.ext
    change ((isUnit_entry (g * h) i).unit : R) =
      ((isUnit_entry g i).unit : R) * ((isUnit_entry h i).unit : R)
    rw [IsUnit.unit_spec, IsUnit.unit_spec, IsUnit.unit_spec]
    change ((g.1 : Matrix ι ι R) * (h.1 : Matrix ι ι R)) i i = _
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · intro j _ hji
      rw [g.2 i j hji.symm, zero_mul]
    · simp

@[simp] theorem unitsEquiv_apply_val (g : DiagonalGroup ι R) (i : ι) :
    ((unitsEquiv g i : Rˣ) : R) = g.1 i i := (isUnit_entry g i).unit_spec

@[simp] theorem unitsEquiv_symm_apply (d : ι → Rˣ) (i j : ι) :
    ((unitsEquiv (R := R)).symm d).1 i j = if i = j then (d i : R) else 0 :=
  TauCeti.diagGL_apply d i j

/-- Entrywise coefficient change of native diagonal matrix units. -/
def map (f : R →+* S) : DiagonalGroup ι R →* DiagonalGroup ι S where
  toFun g := ⟨GeneralLinearGroup.map f g.1, by
    intro i j hij
    rw [GeneralLinearGroup.map_apply, g.2 i j hij, map_zero]⟩
  map_one' := by
    apply Subtype.ext
    exact (GeneralLinearGroup.map f).map_one
  map_mul' g h := by
    apply Subtype.ext
    exact (GeneralLinearGroup.map f).map_mul g.1 h.1

@[simp] theorem map_apply (f : R →+* S) (g : DiagonalGroup ι R) (i j : ι) :
    (map f g).1 i j = f (g.1 i j) := GeneralLinearGroup.map_apply f i j g.1

theorem inclusion_map (f : R →+* S) (g : DiagonalGroup ι R) :
    inclusion (map f g) = GeneralLinearGroup.map f (inclusion g) := rfl

theorem unitsEquiv_map (f : R →+* S) (g : DiagonalGroup ι R) :
    unitsEquiv (map f g) = fun i => Units.map f.toMonoidHom (unitsEquiv g i) := by
  funext i
  apply Units.ext
  simp

end DiagonalGroup

end Matrix
