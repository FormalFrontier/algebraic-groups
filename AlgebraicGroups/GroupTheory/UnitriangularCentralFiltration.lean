/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.Unitriangular
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Order

/-!
# The superdiagonal central filtration of a unitriangular group

For a commutative ring `R`, the group `Matrix.UnitriangularGroup (Fin n) R` has a
descending normal filtration by the vanishing of its first superdiagonals.
Products of matrices supported above superdiagonals `r` and `s` are supported
above superdiagonal `r + s`; this gives a central series and a nilpotency-class
bound even for the zero ring and empty index type.
-/

public section

open scoped commutatorElement

namespace Matrix.UnitriangularGroup

variable (n : ℕ) (R : Type) [CommRing R]

private def hasSupport (r : ℕ) (A : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ i j : Fin n, j.val < i.val + r → A i j = 0

private theorem hasSupport_zero (r : ℕ) :
    hasSupport n R r (0 : Matrix (Fin n) (Fin n) R) := by
  intro i j _
  rfl

private theorem hasSupport_add (r : ℕ) {A B : Matrix (Fin n) (Fin n) R}
    (hA : hasSupport n R r A) (hB : hasSupport n R r B) :
    hasSupport n R r (A + B) := by
  intro i j h
  simp [hA i j h, hB i j h]

private theorem hasSupport_neg (r : ℕ) {A : Matrix (Fin n) (Fin n) R}
    (hA : hasSupport n R r A) : hasSupport n R r (-A) := by
  intro i j h
  simp [hA i j h]

private theorem hasSupport_mono {r s : ℕ} {A : Matrix (Fin n) (Fin n) R}
    (h : r ≤ s) (hA : hasSupport n R s A) : hasSupport n R r A := by
  intro i j hij
  exact hA i j (by omega)

private theorem hasSupport_mul (r s : ℕ) {A B : Matrix (Fin n) (Fin n) R}
    (hA : hasSupport n R r A) (hB : hasSupport n R s B) :
    hasSupport n R (r + s) (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hik : k.val < i.val + r
  · simp [hA i k hik]
  · simp [hB k j (by omega)]

private theorem matrix_mul (g h : Matrix.UnitriangularGroup (Fin n) R) :
    ((g * h : Matrix.UnitriangularGroup (Fin n) R).1 : Matrix (Fin n) (Fin n) R) =
      (g.1 : Matrix (Fin n) (Fin n) R) * (h.1 : Matrix (Fin n) (Fin n) R) := by
  exact Matrix.GeneralLinearGroup.coe_mul g.1 h.1

private theorem matrix_one :
    ((1 : Matrix.UnitriangularGroup (Fin n) R).1 : Matrix (Fin n) (Fin n) R) = 1 := by
  exact Matrix.GeneralLinearGroup.coe_one

private theorem matrix_mul_inv (g : Matrix.UnitriangularGroup (Fin n) R) :
    (g.1 : Matrix (Fin n) (Fin n) R) *
      ((g⁻¹ : Matrix.UnitriangularGroup (Fin n) R).1 : Matrix (Fin n) (Fin n) R) = 1 := by
  have h := congrArg (fun x : Matrix.UnitriangularGroup (Fin n) R =>
    (x.1 : Matrix (Fin n) (Fin n) R)) (mul_inv_cancel g)
  simpa only [matrix_mul, matrix_one] using h

private theorem matrix_inv_mul (g : Matrix.UnitriangularGroup (Fin n) R) :
    ((g⁻¹ : Matrix.UnitriangularGroup (Fin n) R).1 : Matrix (Fin n) (Fin n) R) *
      (g.1 : Matrix (Fin n) (Fin n) R) = 1 := by
  have h := congrArg (fun x : Matrix.UnitriangularGroup (Fin n) R =>
    (x.1 : Matrix (Fin n) (Fin n) R)) (inv_mul_cancel g)
  simpa only [matrix_mul, matrix_one] using h

private theorem hasSupport_sub_one (g : Matrix.UnitriangularGroup (Fin n) R) :
    hasSupport n R 1 ((g.1 : Matrix (Fin n) (Fin n) R) - 1) := by
  intro i j hij
  by_cases h : i = j
  · subst j
    simp [g.2.2 i]
  · have hji : j < i := Fin.lt_def.mpr (by omega)
    simp [Matrix.sub_apply, g.2.1 hji, h]

private theorem hasSupport_mul_group_right (r : ℕ)
    {A : Matrix (Fin n) (Fin n) R} (hA : hasSupport n R r A)
    (g : Matrix.UnitriangularGroup (Fin n) R) :
    hasSupport n R r (A * (g.1 : Matrix (Fin n) (Fin n) R)) := by
  have hprod := hasSupport_mul n R r 1 hA (hasSupport_sub_one n R g)
  have hsum := hasSupport_add n R r hA
    (hasSupport_mono n R (Nat.le_add_right r 1) hprod)
  convert hsum using 1
  noncomm_ring

private theorem hasSupport_mul_group_left (r : ℕ)
    {A : Matrix (Fin n) (Fin n) R} (hA : hasSupport n R r A)
    (g : Matrix.UnitriangularGroup (Fin n) R) :
    hasSupport n R r ((g.1 : Matrix (Fin n) (Fin n) R) * A) := by
  have hprod := hasSupport_mul n R 1 r (hasSupport_sub_one n R g) hA
  have hsum := hasSupport_add n R r hA
    (hasSupport_mono n R (by omega : r ≤ 1 + r) hprod)
  convert hsum using 1
  noncomm_ring

/-- The subgroup whose entries below the `r`-th superdiagonal equal the identity. -/
def superdiagonalSubgroup (r : ℕ) : Subgroup (Matrix.UnitriangularGroup (Fin n) R) where
  carrier := {g | hasSupport n R r ((g.1 : Matrix (Fin n) (Fin n) R) - 1)}
  one_mem' := by
    simpa [matrix_one] using hasSupport_zero n R r
  mul_mem' := by
    intro g h hg hh
    have hsum := hasSupport_add n R r
      (hasSupport_mul_group_right n R r hg h) hh
    change hasSupport n R r (((g * h).1 : Matrix (Fin n) (Fin n) R) - 1)
    rw [matrix_mul]
    convert hsum using 1; noncomm_ring
  inv_mem' := by
    intro g hg
    have hneg := hasSupport_neg n R r (hasSupport_mul_group_right n R r hg g⁻¹)
    change hasSupport n R r (((g⁻¹).1 : Matrix (Fin n) (Fin n) R) - 1)
    have hinv := matrix_mul_inv n R g
    have heq : ((g⁻¹).1 : Matrix (Fin n) (Fin n) R) - 1 =
        -(((g.1 : Matrix (Fin n) (Fin n) R) - 1) *
          ((g⁻¹).1 : Matrix (Fin n) (Fin n) R)) := by
      calc
        _ = ((g⁻¹).1 : Matrix (Fin n) (Fin n) R) -
            (g.1 : Matrix (Fin n) (Fin n) R) *
              ((g⁻¹).1 : Matrix (Fin n) (Fin n) R) := by rw [hinv]
        _ = _ := by noncomm_ring
    rw [heq]
    exact hneg

/-- Membership is an entrywise condition on the difference from the identity. -/
theorem mem_superdiagonalSubgroup {r : ℕ}
    (g : Matrix.UnitriangularGroup (Fin n) R) :
    g ∈ superdiagonalSubgroup n R r ↔
      ∀ i j : Fin n, j.val < i.val + r →
        ((g.1 : Matrix (Fin n) (Fin n) R) - 1) i j = 0 :=
  Iff.rfl

/-- The first stage is the whole unitriangular group. -/
theorem superdiagonalSubgroup_one : superdiagonalSubgroup n R 1 = ⊤ := by
  apply le_antisymm le_top
  intro g _
  exact hasSupport_sub_one n R g

/-- The stage numbered zero is also the whole group. -/
theorem superdiagonalSubgroup_zero : superdiagonalSubgroup n R 0 = ⊤ := by
  apply le_antisymm le_top
  intro g _
  exact hasSupport_mono n R (by omega : 0 ≤ 1) (hasSupport_sub_one n R g)

/-- Later superdiagonal stages are smaller. -/
theorem superdiagonalSubgroup_antitone {r s : ℕ} (h : r ≤ s) :
    superdiagonalSubgroup n R s ≤ superdiagonalSubgroup n R r := by
  intro g hg
  exact hasSupport_mono n R h hg

/-- Erasing one more superdiagonal gives a descending filtration. -/
theorem superdiagonalSubgroup_succ_le (r : ℕ) :
    superdiagonalSubgroup n R (r + 1) ≤ superdiagonalSubgroup n R r :=
  superdiagonalSubgroup_antitone n R (Nat.le_add_right r 1)

/-- At the dimension, every matrix entry is forced to equal the identity. -/
theorem superdiagonalSubgroup_end : superdiagonalSubgroup n R n = ⊥ := by
  apply le_antisymm _ bot_le
  intro g hg
  have hmat : (g.1 : Matrix (Fin n) (Fin n) R) = 1 := by
    ext i j
    have hij : j.val < i.val + n := by have := j.isLt; omega
    have hz := hg i j hij
    exact sub_eq_zero.mp (by simpa only [Matrix.sub_apply] using hz)
  have hunit : g = 1 := by
    apply Subtype.ext
    apply Units.ext
    simpa only [matrix_one] using hmat
  exact Subgroup.mem_bot.mpr hunit

/-- Each superdiagonal subgroup is normal in the existing native point group. -/
instance superdiagonalSubgroup_normal (r : ℕ) : (superdiagonalSubgroup n R r).Normal where
  conj_mem := by
    intro g hg u
    have hs := hasSupport_mul_group_right n R r
      (hasSupport_mul_group_left n R r hg u) u⁻¹
    change hasSupport n R r (((u * g * u⁻¹).1 : Matrix (Fin n) (Fin n) R) - 1)
    have hu := matrix_mul_inv n R u
    have heq : ((u * g * u⁻¹).1 : Matrix (Fin n) (Fin n) R) - 1 =
        (u.1 : Matrix (Fin n) (Fin n) R) *
          (((g.1 : Matrix (Fin n) (Fin n) R) - 1) *
            ((u⁻¹).1 : Matrix (Fin n) (Fin n) R)) := by
      calc
        _ = ((u.1 : Matrix (Fin n) (Fin n) R) * (g.1 : Matrix (Fin n) (Fin n) R)) *
            ((u⁻¹).1 : Matrix (Fin n) (Fin n) R) -
            (u.1 : Matrix (Fin n) (Fin n) R) *
              ((u⁻¹).1 : Matrix (Fin n) (Fin n) R) := by
          simp only [matrix_mul, hu]
        _ = _ := by noncomm_ring
    rw [heq]
    simpa only [mul_assoc] using hs

/-- The commutator of stages `r` and `s` lies in stage `r + s`. -/
theorem superdiagonalSubgroup_commutator (r s : ℕ) :
    ⁅superdiagonalSubgroup n R r, superdiagonalSubgroup n R s⁆ ≤
      superdiagonalSubgroup n R (r + s) := by
  apply Subgroup.commutator_le.mpr
  intro x hx y hy
  have hAB := hasSupport_mul n R r s hx hy
  have hBA := hasSupport_mul n R s r hy hx
  have hdiff : hasSupport n R (r + s)
      ((x.1 : Matrix (Fin n) (Fin n) R) * (y.1 : Matrix (Fin n) (Fin n) R) -
       (y.1 : Matrix (Fin n) (Fin n) R) * (x.1 : Matrix (Fin n) (Fin n) R)) := by
    have hsum := hasSupport_add n R (r + s) hAB
      (hasSupport_neg n R (r + s) (by simpa only [Nat.add_comm] using hBA))
    convert hsum using 1; noncomm_ring
  have hs := hasSupport_mul_group_right n R (r + s)
    (hasSupport_mul_group_right n R (r + s) hdiff x⁻¹) y⁻¹
  change hasSupport n R (r + s)
    (((⁅x, y⁆ : Matrix.UnitriangularGroup (Fin n) R).1 : Matrix (Fin n) (Fin n) R) - 1)
  have hxinv := matrix_mul_inv n R x
  have hyinv := matrix_mul_inv n R y
  have hcancel :
      (((y.1 : Matrix (Fin n) (Fin n) R) * (x.1 : Matrix (Fin n) (Fin n) R)) *
        ((x⁻¹).1 : Matrix (Fin n) (Fin n) R)) *
        ((y⁻¹).1 : Matrix (Fin n) (Fin n) R) = 1 := by
    calc
      _ = (y.1 : Matrix (Fin n) (Fin n) R) *
            ((x.1 : Matrix (Fin n) (Fin n) R) *
              ((x⁻¹).1 : Matrix (Fin n) (Fin n) R)) *
            ((y⁻¹).1 : Matrix (Fin n) (Fin n) R) := by noncomm_ring
      _ = (y.1 : Matrix (Fin n) (Fin n) R) *
            ((y⁻¹).1 : Matrix (Fin n) (Fin n) R) := by rw [hxinv]; simp
      _ = 1 := hyinv
  have heq : (((⁅x, y⁆ : Matrix.UnitriangularGroup (Fin n) R).1 :
      Matrix (Fin n) (Fin n) R) - 1) =
      (((x.1 : Matrix (Fin n) (Fin n) R) * (y.1 : Matrix (Fin n) (Fin n) R) -
        (y.1 : Matrix (Fin n) (Fin n) R) * (x.1 : Matrix (Fin n) (Fin n) R)) *
        ((x⁻¹).1 : Matrix (Fin n) (Fin n) R)) *
        ((y⁻¹).1 : Matrix (Fin n) (Fin n) R) := by
    calc
      _ = (((x.1 : Matrix (Fin n) (Fin n) R) * (y.1 : Matrix (Fin n) (Fin n) R)) *
            ((x⁻¹).1 : Matrix (Fin n) (Fin n) R)) *
            ((y⁻¹).1 : Matrix (Fin n) (Fin n) R) - 1 := by
          simp only [commutatorElement_def, matrix_mul]
      _ = (((x.1 : Matrix (Fin n) (Fin n) R) * (y.1 : Matrix (Fin n) (Fin n) R)) *
            ((x⁻¹).1 : Matrix (Fin n) (Fin n) R)) *
            ((y⁻¹).1 : Matrix (Fin n) (Fin n) R) -
          (((y.1 : Matrix (Fin n) (Fin n) R) * (x.1 : Matrix (Fin n) (Fin n) R)) *
            ((x⁻¹).1 : Matrix (Fin n) (Fin n) R)) *
            ((y⁻¹).1 : Matrix (Fin n) (Fin n) R) := by rw [hcancel]
      _ = _ := by noncomm_ring
  rw [heq]
  exact hs

/-- The infinite descending central series, starting at the entire point group. -/
def descendingSeries (t : ℕ) : Subgroup (Matrix.UnitriangularGroup (Fin n) R) :=
  superdiagonalSubgroup n R (t + 1)

/-- The full infinite family satisfies the native descending-central-series predicate. -/
theorem descendingSeries_isDescendingCentralSeries :
    Subgroup.IsDescendingCentralSeries (descendingSeries n R) := by
  constructor
  · exact superdiagonalSubgroup_one n R
  · intro x t hx g
    change x ∈ superdiagonalSubgroup n R (t + 1) at hx
    change ⁅x, g⁆ ∈ superdiagonalSubgroup n R ((t + 1) + 1)
    have hg : g ∈ superdiagonalSubgroup n R 1 := by
      rw [superdiagonalSubgroup_one]
      trivial
    exact (Subgroup.commutator_le.mp
      (superdiagonalSubgroup_commutator n R (t + 1) 1)) x hx g hg

/-- The central series reaches the identity by index `n - 1`, including `n = 0`. -/
theorem descendingSeries_end : descendingSeries n R (n - 1) = ⊥ := by
  by_cases hn : n = 0
  · subst n
    have htriv : (⊤ : Subgroup (Matrix.UnitriangularGroup (Fin 0) R)) = ⊥ :=
      (superdiagonalSubgroup_zero 0 R).symm.trans (superdiagonalSubgroup_end 0 R)
    simpa [descendingSeries, superdiagonalSubgroup_one] using htriv
  · have hindex : n - 1 + 1 = n := by omega
    simpa only [descendingSeries, hindex] using superdiagonalSubgroup_end n R

/-- The native unitriangular point group is nilpotent over every commutative ring. -/
instance instIsNilpotent : Group.IsNilpotent (Matrix.UnitriangularGroup (Fin n) R) :=
  (Subgroup.nilpotent_iff_finite_descending_central_series _).2
    ⟨n - 1, descendingSeries n R, descendingSeries_isDescendingCentralSeries n R,
      descendingSeries_end n R⟩

/-- The nilpotency class is at most the dimension minus one, also for `Fin 0`. -/
theorem nilpotencyClass_le :
    Group.nilpotencyClass (Matrix.UnitriangularGroup (Fin n) R) ≤ n - 1 := by
  apply (Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le).mp
  apply le_antisymm _ bot_le
  calc
    Subgroup.lowerCentralSeries
        (⊤ : Subgroup (Matrix.UnitriangularGroup (Fin n) R)) (n - 1) ≤
        descendingSeries n R (n - 1) :=
      Subgroup.descending_central_series_ge_lower (descendingSeries n R)
        (descendingSeries_isDescendingCentralSeries n R) (n - 1)
    _ = ⊥ := descendingSeries_end n R

/-- Coefficient homomorphisms preserve every superdiagonal stage pointwise. -/
theorem map_mem_superdiagonalSubgroup {S : Type} [CommRing S]
    (f : R →+* S) {r : ℕ} {g : Matrix.UnitriangularGroup (Fin n) R}
    (hg : g ∈ superdiagonalSubgroup n R r) :
    Matrix.UnitriangularGroup.map f g ∈ superdiagonalSubgroup n S r := by
  apply (mem_superdiagonalSubgroup n S _).2
  intro i j hij
  have hz := (mem_superdiagonalSubgroup n R g).1 hg i j hij
  simpa [Matrix.sub_apply, Matrix.one_apply, Matrix.UnitriangularGroup.map_apply]
    using congrArg f hz

/-- The native coefficient-map group homomorphism maps each stage into its counterpart. -/
theorem superdiagonalSubgroup_map {S : Type} [CommRing S]
    (f : R →+* S) (r : ℕ) :
    (superdiagonalSubgroup n R r).map (Matrix.UnitriangularGroup.map f) ≤
      superdiagonalSubgroup n S r := by
  rintro g ⟨x, hx, rfl⟩
  exact map_mem_superdiagonalSubgroup n R f hx

end Matrix.UnitriangularGroup
