/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupTheory.UnitriangularCentralFiltration
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Successive superdiagonal quotients of unitriangular point groups

The quotient of the `r`-th stage by the next stage is the additive group of
its `r`-th superdiagonal coordinates, for `1 ≤ r` over any commutative ring.
The construction is natural under arbitrary unital coefficient maps.
-/

public section

namespace Matrix.UnitriangularGroup

variable (n : ℕ) (R : Type) [CommRing R]

/-- Positions on the `r`-th superdiagonal of an `n` by `n` matrix. -/
abbrev superdiagonalIndex (n r : ℕ) : Type :=
  {ij : Fin n × Fin n // ij.2.val = ij.1.val + r}

private theorem coordinate_one (r : ℕ) (hr : 1 ≤ r)
    (ij : superdiagonalIndex n r) :
    (1 : Matrix (Fin n) (Fin n) R) ij.1.1 ij.1.2 = 0 := by
  have hne : ij.1.1 ≠ ij.1.2 := by
    intro heq
    have := ij.2
    rw [heq] at this
    omega
  simp [hne]

private theorem coordinate_mul (r : ℕ) (hr : 1 ≤ r)
    (x y : superdiagonalSubgroup n R r) (ij : superdiagonalIndex n r) :
    (((x * y).1.1 : Matrix (Fin n) (Fin n) R) ij.1.1 ij.1.2) =
      (x.1.1 : Matrix (Fin n) (Fin n) R) ij.1.1 ij.1.2 +
        (y.1.1 : Matrix (Fin n) (Fin n) R) ij.1.1 ij.1.2 := by
  let X : Matrix (Fin n) (Fin n) R := x.1.1
  let Y : Matrix (Fin n) (Fin n) R := y.1.1
  have hproduct : ((X - 1) * (Y - 1)) ij.1.1 ij.1.2 = 0 := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hik : k.val < ij.1.1.val + r
    · simp [(mem_superdiagonalSubgroup n R x.1).1 x.2 ij.1.1 k hik, X]
    · have hkj : ij.1.2.val < k.val + r := by omega
      simp [(mem_superdiagonalSubgroup n R y.1).1 y.2 k ij.1.2 hkj, Y]
  have hone := coordinate_one n R r hr ij
  have hformula : X * Y = (X - 1) * (Y - 1) + X + Y - 1 := by
    noncomm_ring
  have hmul : (((x * y).1.1 : Matrix (Fin n) (Fin n) R)) = X * Y :=
    Matrix.GeneralLinearGroup.coe_mul x.1.1 y.1.1
  rw [hmul, hformula]
  simp only [Matrix.add_apply, Matrix.sub_apply, hproduct, hone]
  ring

/-- The actual `r`-stage maps to additive coordinates on its `r`-th superdiagonal. -/
def superdiagonalCoordinateHom (r : ℕ) (hr : 1 ≤ r) :
    superdiagonalSubgroup n R r →*
      Multiplicative (superdiagonalIndex n r → R) where
  toFun x := Multiplicative.ofAdd (fun ij =>
    (x.1.1 : Matrix (Fin n) (Fin n) R) ij.1.1 ij.1.2)
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext ij
    exact coordinate_one n R r hr ij
  map_mul' := by
    intro x y
    apply Multiplicative.toAdd.injective
    funext ij
    exact coordinate_mul n R r hr x y ij

/-- Evaluation of the stage-coordinate homomorphism is a matrix entry. -/
@[simp] theorem superdiagonalCoordinateHom_apply (r : ℕ) (hr : 1 ≤ r)
    (x : superdiagonalSubgroup n R r) (ij : superdiagonalIndex n r) :
    Multiplicative.toAdd (superdiagonalCoordinateHom n R r hr x) ij =
      (x.1.1 : Matrix (Fin n) (Fin n) R) ij.1.1 ij.1.2 := by
  simp [superdiagonalCoordinateHom]

/-- The kernel inside the `r`-th stage is precisely its next stage. -/
theorem superdiagonalCoordinateHom_ker (r : ℕ) (hr : 1 ≤ r) :
    (superdiagonalCoordinateHom n R r hr).ker =
      (superdiagonalSubgroup n R (r + 1)).subgroupOf
        (superdiagonalSubgroup n R r) := by
  apply Subgroup.ext
  intro x
  change superdiagonalCoordinateHom n R r hr x = 1 ↔
    x.1 ∈ superdiagonalSubgroup n R (r + 1)
  constructor
  · intro hx
    apply (mem_superdiagonalSubgroup n R x.1).2
    intro i j hij
    by_cases hlt : j.val < i.val + r
    · exact (mem_superdiagonalSubgroup n R x.1).1 x.2 i j hlt
    · have heq : j.val = i.val + r := by omega
      let ij : superdiagonalIndex n r := ⟨(i, j), heq⟩
      have hentry : (x.1.1 : Matrix (Fin n) (Fin n) R) i j = 0 := by
        have heval := congrArg (fun a : Multiplicative (superdiagonalIndex n r → R) =>
          Multiplicative.toAdd a ij) hx
        simpa [superdiagonalCoordinateHom_apply] using heval
      have hone : (1 : Matrix (Fin n) (Fin n) R) i j = 0 :=
        coordinate_one n R r hr ij
      simpa [Matrix.sub_apply, hone] using hentry
  · intro hx
    apply Multiplicative.toAdd.injective
    funext ij
    rw [superdiagonalCoordinateHom_apply]
    have hentry := (mem_superdiagonalSubgroup n R x.1).1 hx
      ij.1.1 ij.1.2 (by omega : ij.1.2.val < ij.1.1.val + (r + 1))
    simpa [Matrix.sub_apply, coordinate_one n R r hr ij] using hentry

private def coordinateMatrix (r : ℕ) (a : superdiagonalIndex n r → R) :
    Matrix (Fin n) (Fin n) R := fun i j =>
  if h : j.val = i.val + r then a ⟨(i, j), h⟩ else 0

private theorem coordinateMatrix_upper (r : ℕ) (hr : 1 ≤ r)
    (a : superdiagonalIndex n r → R) :
    (coordinateMatrix n R r a).IsUpperTriangular := by
  intro i j hji
  simp only [id_eq] at hji
  have hne : j.val ≠ i.val + r := by omega
  simp only [coordinateMatrix, dite_eq_right hne]

private theorem coordinateMatrix_diag (r : ℕ) (hr : 1 ≤ r)
    (a : superdiagonalIndex n r → R) (i : Fin n) :
    coordinateMatrix n R r a i i = 0 := by
  have hne : i.val ≠ i.val + r := by omega
  simp only [coordinateMatrix, dite_eq_right hne]

/-- Every coordinate family is attained by an element of the actual stage. -/
theorem superdiagonalCoordinateHom_surjective (r : ℕ) (hr : 1 ≤ r) :
    Function.Surjective (superdiagonalCoordinateHom n R r hr) := by
  classical
  intro a
  let A := coordinateMatrix n R r (Multiplicative.toAdd a)
  have hupper : (1 + A).IsUpperTriangular :=
    Matrix.blockTriangular_one.add (coordinateMatrix_upper n R r hr _)
  have hdiag (i : Fin n) : (1 + A) i i = 1 := by
    simp [Matrix.add_apply, A, coordinateMatrix_diag n R r hr]
  have hdet : IsUnit (1 + A).det := by
    rw [Matrix.det_of_isUpperTriangular hupper]
    simp [hdiag]
  let g : Matrix.UnitriangularGroup (Fin n) R :=
    ⟨Matrix.GeneralLinearGroup.mk'' (1 + A) hdet, by
      constructor
      · change (1 + A).IsUpperTriangular
        exact hupper
      · intro i
        change (1 + A) i i = 1
        exact hdiag i⟩
  have hmatrix : (g.1 : Matrix (Fin n) (Fin n) R) = 1 + A := by
    simp [g]
  have hstage : g ∈ superdiagonalSubgroup n R r := by
    apply (mem_superdiagonalSubgroup n R g).2
    intro i j hij
    have hne : j.val ≠ i.val + r := by omega
    have hzero : A i j = 0 := by simp [A, coordinateMatrix, hne]
    rw [hmatrix]
    simp [Matrix.add_apply, Matrix.sub_apply, hzero]
  refine ⟨⟨g, hstage⟩, ?_⟩
  apply Multiplicative.toAdd.injective
  funext ij
  rw [superdiagonalCoordinateHom_apply, hmatrix]
  simp [Matrix.add_apply, coordinate_one n R r hr ij, A, coordinateMatrix, ij.2]

/-- The successive whole-stage quotient is the additive coordinate group. -/
noncomputable def superdiagonalQuotientEquiv (r : ℕ) (hr : 1 ≤ r) :
    (superdiagonalSubgroup n R r ⧸
      (superdiagonalSubgroup n R (r + 1)).subgroupOf
        (superdiagonalSubgroup n R r)) ≃*
      Multiplicative (superdiagonalIndex n r → R) :=
  QuotientGroup.liftEquiv _ (superdiagonalCoordinateHom_surjective n R r hr)
    (superdiagonalCoordinateHom_ker n R r hr).symm

/-- Evaluating the quotient equivalence at the coset of a stage element. -/
@[simp] theorem superdiagonalQuotientEquiv_mk (r : ℕ) (hr : 1 ≤ r)
    (x : superdiagonalSubgroup n R r) (ij : superdiagonalIndex n r) :
    Multiplicative.toAdd
        (superdiagonalQuotientEquiv n R r hr
          (x : superdiagonalSubgroup n R r ⧸
            (superdiagonalSubgroup n R (r + 1)).subgroupOf
              (superdiagonalSubgroup n R r))) ij =
      (x.1.1 : Matrix (Fin n) (Fin n) R) ij.1.1 ij.1.2 := by
  simp [superdiagonalQuotientEquiv]

/-- Apply any unital coefficient homomorphism to an entire stage. -/
def superdiagonalStageMap {S : Type} [CommRing S] (f : R →+* S) (r : ℕ) :
    superdiagonalSubgroup n R r →* superdiagonalSubgroup n S r where
  toFun x := ⟨Matrix.UnitriangularGroup.map f x.1,
    map_mem_superdiagonalSubgroup n R f x.2⟩
  map_one' := Subtype.ext (map_one (Matrix.UnitriangularGroup.map f))
  map_mul' x y := Subtype.ext (map_mul (Matrix.UnitriangularGroup.map f) x.1 y.1)

/-- Apply any unital coefficient map pointwise to additive superdiagonal coordinates. -/
def superdiagonalCoordinateMap {S : Type} [CommRing S] (f : R →+* S) (r : ℕ) :
    Multiplicative (superdiagonalIndex n r → R) →*
      Multiplicative (superdiagonalIndex n r → S) where
  toFun a := Multiplicative.ofAdd (fun ij => f (Multiplicative.toAdd a ij))
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext ij
    exact map_zero f
  map_mul' := by
    intro a b
    apply Multiplicative.toAdd.injective
    funext ij
    exact map_add f _ _

/-- Stage coordinates commute with arbitrary unital coefficient change. -/
theorem superdiagonalCoordinateHom_natural {S : Type} [CommRing S]
    (f : R →+* S) (r : ℕ) (hr : 1 ≤ r)
    (x : superdiagonalSubgroup n R r) :
    superdiagonalCoordinateHom n S r hr (superdiagonalStageMap n R f r x) =
      superdiagonalCoordinateMap n R f r
        (superdiagonalCoordinateHom n R r hr x) := by
  apply Multiplicative.toAdd.injective
  funext ij
  simp [superdiagonalCoordinateMap, superdiagonalStageMap,
    Matrix.UnitriangularGroup.map_apply]

/-- Coefficient maps descend to the quotients by their actual next stages. -/
def superdiagonalQuotientMap {S : Type} [CommRing S] (f : R →+* S) (r : ℕ) :
    (superdiagonalSubgroup n R r ⧸
      (superdiagonalSubgroup n R (r + 1)).subgroupOf
        (superdiagonalSubgroup n R r)) →*
    (superdiagonalSubgroup n S r ⧸
      (superdiagonalSubgroup n S (r + 1)).subgroupOf
        (superdiagonalSubgroup n S r)) :=
  QuotientGroup.map _ _ (superdiagonalStageMap n R f r) (by
    intro x hx
    change (superdiagonalStageMap n R f r x).1 ∈ superdiagonalSubgroup n S (r + 1)
    exact map_mem_superdiagonalSubgroup n R f hx)

/-- The quotient-to-coordinate equivalences are natural for all coefficient maps. -/
theorem superdiagonalQuotientEquiv_natural {S : Type} [CommRing S]
    (f : R →+* S) (r : ℕ) (hr : 1 ≤ r)
    (x : superdiagonalSubgroup n R r ⧸
      (superdiagonalSubgroup n R (r + 1)).subgroupOf
        (superdiagonalSubgroup n R r)) :
    superdiagonalQuotientEquiv n S r hr (superdiagonalQuotientMap n R f r x) =
      superdiagonalCoordinateMap n R f r
        (superdiagonalQuotientEquiv n R r hr x) := by
  refine Quotient.inductionOn x ?_
  intro y
  exact superdiagonalCoordinateHom_natural n R f r hr y

end Matrix.UnitriangularGroup
