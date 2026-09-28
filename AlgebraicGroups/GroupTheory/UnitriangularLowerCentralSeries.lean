/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupTheory.UnitriangularSuperdiagonalQuotients
public import AlgebraicGroups.GroupTheory.UnitriangularNilpotencyClass

/-!
# Lower central series of finite unitriangular groups

Over any commutative ring, the actual lower central series is the superdiagonal
filtration, with the lower central series indexed from zero.
-/

@[expose] public section

open scoped commutatorElement

namespace Matrix.UnitriangularGroup

variable (n : ℕ) (R : Type) [CommRing R]

/-- An elementary root of distance `d + 1` belongs to the `d`-th lower central term. -/
theorem elementary_mem_lowerCentralSeries_of_distance
    (i j : Fin n) (hij : i < j) (a : R) (d : ℕ)
    (hd : j.val = i.val + d + 1) :
    elementary n R i j hij a ∈
      (⊤ : Subgroup (Matrix.UnitriangularGroup (Fin n) R)).lowerCentralSeries d := by
  induction d generalizing j with
  | zero =>
      simp only [Subgroup.lowerCentralSeries_zero]
      exact Subgroup.mem_top _
  | succ d ih =>
      let k : Fin n := ⟨i.val + d + 1, by omega⟩
      have hik : i < k := Fin.lt_def.mpr (by dsimp [k]; omega)
      have hkj : k < j := Fin.lt_def.mpr (by dsimp [k]; omega)
      have hfirst : elementary n R i k hik a ∈
          (⊤ : Subgroup (Matrix.UnitriangularGroup (Fin n) R)).lowerCentralSeries d :=
        ih k hik (by dsimp [k])
      have hcomm := Subgroup.commutator_mem_commutator hfirst
        (Subgroup.mem_top (elementary n R k j hkj (1 : R)))
      have hroot := elementary_commutator n R i k j hik hkj a (1 : R)
      simpa only [Subgroup.lowerCentralSeries_succ, hroot, mul_one] using hcomm

/-- An elementary root belongs to every superdiagonal stage below its distance. -/
theorem elementary_mem_superdiagonalSubgroup
    (i j : Fin n) (hij : i < j) (a : R) (r : ℕ)
    (hr : i.val + r ≤ j.val) :
    elementary n R i j hij a ∈ superdiagonalSubgroup n R r := by
  apply (mem_superdiagonalSubgroup n R _).2
  intro u v huv
  rw [elementary_coe]
  by_cases hi : i = u <;> by_cases hj : j = v
  · subst u; subst v
    omega
  · simp [Matrix.add_apply, Matrix.sub_apply, hi, hj]
  · simp [Matrix.add_apply, Matrix.sub_apply, hi, hj]
  · simp [Matrix.add_apply, Matrix.sub_apply, hi, hj]

private theorem lowerCentralSeries_le_superdiagonalSubgroup (t : ℕ) :
    (⊤ : Subgroup (Matrix.UnitriangularGroup (Fin n) R)).lowerCentralSeries t ≤
      superdiagonalSubgroup n R (t + 1) := by
  induction t with
  | zero => simpa only [Subgroup.lowerCentralSeries_zero, zero_add,
      superdiagonalSubgroup_one] using (le_refl
        (⊤ : Subgroup (Matrix.UnitriangularGroup (Fin n) R)))
  | succ t ih =>
      simpa only [Subgroup.lowerCentralSeries_succ, Nat.succ_eq_add_one] using
        (Subgroup.commutator_mono ih
          (show (⊤ : Subgroup (Matrix.UnitriangularGroup (Fin n) R)) ≤
            superdiagonalSubgroup n R 1 from (superdiagonalSubgroup_one n R).symm.le)).trans
          (by simpa only [show (t + 1) + 1 = t + 1 + 1 by omega] using
            superdiagonalSubgroup_commutator n R (t + 1) 1)

private def coordinateElementary (r : ℕ) (hr : 1 ≤ r)
    (x : superdiagonalSubgroup n R r) (ij : superdiagonalIndex n r) :
    superdiagonalSubgroup n R r :=
  ⟨elementary n R ij.1.1 ij.1.2
      (Fin.lt_def.mpr (by have := ij.2; omega))
      ((x.1.1 : Matrix (Fin n) (Fin n) R) ij.1.1 ij.1.2),
    elementary_mem_superdiagonalSubgroup n R _ _ _ _ r (by exact le_of_eq ij.2.symm)⟩

private theorem coordinateElementary_mem_lowerCentralSeries
    (r : ℕ) (hr : 1 ≤ r) (x : superdiagonalSubgroup n R r)
    (ij : superdiagonalIndex n r) :
    (coordinateElementary n R r hr x ij).1 ∈
      (⊤ : Subgroup (Matrix.UnitriangularGroup (Fin n) R)).lowerCentralSeries
        (r - 1) := by
  have hij : ij.1.1 < ij.1.2 := Fin.lt_def.mpr (by have := ij.2; omega)
  change elementary n R ij.1.1 ij.1.2 hij
    ((x.1.1 : Matrix (Fin n) (Fin n) R) ij.1.1 ij.1.2) ∈
      (⊤ : Subgroup (Matrix.UnitriangularGroup (Fin n) R)).lowerCentralSeries (r - 1)
  exact elementary_mem_lowerCentralSeries_of_distance n R _ _ hij _ (r - 1)
    (by have := ij.2; omega)

private theorem coordinateElementary_apply (r : ℕ) (hr : 1 ≤ r)
    (x : superdiagonalSubgroup n R r) (ij kl : superdiagonalIndex n r) :
    Multiplicative.toAdd
        (superdiagonalCoordinateHom n R r hr (coordinateElementary n R r hr x ij)) kl =
      if ij = kl then (x.1.1 : Matrix (Fin n) (Fin n) R) kl.1.1 kl.1.2 else 0 := by
  rw [superdiagonalCoordinateHom_apply]
  have hij : ij.1.1 < ij.1.2 := Fin.lt_def.mpr (by have := ij.2; omega)
  change ((elementary n R ij.1.1 ij.1.2 hij
    ((x.1.1 : Matrix (Fin n) (Fin n) R) ij.1.1 ij.1.2)).1 :
      Matrix (Fin n) (Fin n) R) kl.1.1 kl.1.2 = _
  rw [elementary_coe]
  have hdiag : kl.1.1 ≠ kl.1.2 := by
    intro heq
    have := kl.2
    rw [heq] at this
    omega
  by_cases heq : ij = kl
  · subst kl
    simp [Matrix.add_apply, hdiag]
  · have hpositions : ij.1.1 ≠ kl.1.1 ∨ ij.1.2 ≠ kl.1.2 := by
      by_contra h
      push Not at h
      exact heq (Subtype.ext (Prod.ext h.1 h.2))
    rcases hpositions with hfirst | hsecond
    · simp [Matrix.add_apply, hdiag, heq, hfirst]
    · simp [Matrix.add_apply, hdiag, heq, hsecond]

private noncomputable def coordinateProduct (r : ℕ) (hr : 1 ≤ r)
    (x : superdiagonalSubgroup n R r) : superdiagonalSubgroup n R r :=
  (((Finset.univ : Finset (superdiagonalIndex n r)).toList).map
    (coordinateElementary n R r hr x)).prod

private theorem coordinateProduct_mem_lowerCentralSeries (r : ℕ) (hr : 1 ≤ r)
    (x : superdiagonalSubgroup n R r) :
    (coordinateProduct n R r hr x).1 ∈
      (⊤ : Subgroup (Matrix.UnitriangularGroup (Fin n) R)).lowerCentralSeries
        (r - 1) := by
  have hlist (l : List (superdiagonalIndex n r)) :
      ((l.map (coordinateElementary n R r hr x)).prod).1 ∈
        (⊤ : Subgroup (Matrix.UnitriangularGroup (Fin n) R)).lowerCentralSeries
          (r - 1) := by
    induction l with
    | nil => exact Subgroup.one_mem _
    | cons ij l ih =>
        simpa only [List.map_cons, List.prod_cons, Subgroup.coe_mul] using
          (Subgroup.mul_mem _ (coordinateElementary_mem_lowerCentralSeries n R r hr x ij) ih)
  exact hlist _

private theorem coordinateProduct_apply (r : ℕ) (hr : 1 ≤ r)
    (x : superdiagonalSubgroup n R r) (kl : superdiagonalIndex n r) :
    Multiplicative.toAdd (superdiagonalCoordinateHom n R r hr
      (coordinateProduct n R r hr x)) kl =
      (x.1.1 : Matrix (Fin n) (Fin n) R) kl.1.1 kl.1.2 := by
  let coeff : superdiagonalIndex n r → R := fun ij =>
    if ij = kl then (x.1.1 : Matrix (Fin n) (Fin n) R) kl.1.1 kl.1.2 else 0
  have hlist (l : List (superdiagonalIndex n r)) :
      Multiplicative.toAdd (superdiagonalCoordinateHom n R r hr
        (l.map (coordinateElementary n R r hr x)).prod) kl =
        (l.map coeff).sum := by
    induction l with
    | nil => simp
    | cons ij l ih =>
        simp only [List.map_cons, List.prod_cons, map_mul, List.sum_cons]
        change Multiplicative.toAdd
            (superdiagonalCoordinateHom n R r hr (coordinateElementary n R r hr x ij)) kl +
          Multiplicative.toAdd (superdiagonalCoordinateHom n R r hr
            (l.map (coordinateElementary n R r hr x)).prod) kl = _
        rw [coordinateElementary_apply, ih]
  have hsum : (((Finset.univ : Finset (superdiagonalIndex n r)).toList).map coeff).sum =
      (x.1.1 : Matrix (Fin n) (Fin n) R) kl.1.1 kl.1.2 := by
    rw [← List.sum_toFinset coeff (Finset.nodup_toList _)]
    simp [coeff]
  exact (hlist _).trans hsum

/-- The actual lower central series is exactly the superdiagonal filtration. -/
theorem lowerCentralSeries_eq_superdiagonalSubgroup (t : ℕ) :
    (⊤ : Subgroup (Matrix.UnitriangularGroup (Fin n) R)).lowerCentralSeries t =
      superdiagonalSubgroup n R (t + 1) := by
  apply le_antisymm (lowerCentralSeries_le_superdiagonalSubgroup n R t)
  have hdown (r : ℕ) (hrn : r ≤ n) :
      superdiagonalSubgroup n R r ≤
        (⊤ : Subgroup (Matrix.UnitriangularGroup (Fin n) R)).lowerCentralSeries
          (r - 1) := by
    apply Nat.decreasingInduction (n := n)
      (motive := fun r _ => superdiagonalSubgroup n R r ≤
        (⊤ : Subgroup (Matrix.UnitriangularGroup (Fin n) R)).lowerCentralSeries
          (r - 1))
    · intro r hr ih
      by_cases hr0 : r = 0
      · subst r
        rw [superdiagonalSubgroup_zero]
        exact le_top
      · have hpos : 1 ≤ r := by omega
        have hnext : superdiagonalSubgroup n R (r + 1) ≤
            (⊤ : Subgroup (Matrix.UnitriangularGroup (Fin n) R)).lowerCentralSeries r := by
          simpa only [show r + 1 - 1 = r by omega] using ih
        intro g hg
        let x : superdiagonalSubgroup n R r := ⟨g, hg⟩
        let p := coordinateProduct n R r hpos x
        have hphi : superdiagonalCoordinateHom n R r hpos p =
            superdiagonalCoordinateHom n R r hpos x := by
          apply Multiplicative.toAdd.injective
          funext ij
          simpa only [superdiagonalCoordinateHom_apply] using
            coordinateProduct_apply n R r hpos x ij
        have hker : p⁻¹ * x ∈ (superdiagonalCoordinateHom n R r hpos).ker := by
          change superdiagonalCoordinateHom n R r hpos (p⁻¹ * x) = 1
          rw [map_mul, map_inv, hphi, inv_mul_cancel]
        have hq : (p⁻¹ * x).1 ∈ superdiagonalSubgroup n R (r + 1) := by
          rw [superdiagonalCoordinateHom_ker n R r hpos] at hker
          exact hker
        have hq' : (p⁻¹ * x).1 ∈
            (⊤ : Subgroup (Matrix.UnitriangularGroup (Fin n) R)).lowerCentralSeries
              (r - 1) :=
          (Subgroup.lowerCentralSeries_antitone
            (⊤ : Subgroup (Matrix.UnitriangularGroup (Fin n) R))
            (by omega : r - 1 ≤ r))
            (hnext hq)
        have hp := coordinateProduct_mem_lowerCentralSeries n R r hpos x
        have hrecover : p.1 * (p⁻¹ * x).1 = g := by
          change p.1 * (p.1⁻¹ * g) = g
          group
        rw [← hrecover]
        exact Subgroup.mul_mem _ hp hq'
    · rw [superdiagonalSubgroup_end]
      exact bot_le
    · exact hrn
  by_cases ht : t + 1 ≤ n
  · simpa only [show t + 1 - 1 = t by omega] using hdown (t + 1) ht
  · have hn : n ≤ t + 1 := by omega
    exact (superdiagonalSubgroup_antitone n R hn).trans
      (by rw [superdiagonalSubgroup_end]; exact bot_le)

end Matrix.UnitriangularGroup
