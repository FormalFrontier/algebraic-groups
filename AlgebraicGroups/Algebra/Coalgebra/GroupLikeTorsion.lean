/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.GroupLikeBaseChange
public import AlgebraicGroups.Algebra.Coalgebra.GroupLikeCardinality
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Dimension.Localization

/-!
# Group-like elements and torsion fibers

For a coalgebra over a commutative domain, scalar extension to the fraction field
sends group-like elements to group-like elements. Two elements with the same image
differ by an element of the canonical torsion submodule. Consequently the number
of group-like elements is at most the module rank times the cardinality of that
submodule. No torsion-freeness or finite generation of the coalgebra is assumed.

The finite-rank consequences assume that the torsion submodule is finite as a
**type**, not merely finitely generated as a module. They establish finiteness of
the group-like carrier before passing to `Nat.card`. The final two results express
the bound in terms of a finite cardinal dimension after extension to the fraction
field, using the canonical base-change rank and finrank equalities.
-/

@[expose] public section

universe u v

open scoped Cardinal TensorProduct

namespace GroupLike

variable (R : Type u) (C : Type v)
variable [CommRing R] [IsDomain R] [AddCommGroup C] [Module R C] [Coalgebra R C]

/-- Group-like elements are bounded by the rank times the size of the canonical
torsion submodule. The two universes of the ring and the coalgebra are independent. -/
theorem cardinalMk_le_rank_mul_torsion :
    Cardinal.lift.{u} #(GroupLike R C) ≤
      Cardinal.lift.{u} (Module.rank R C) *
        Cardinal.lift.{u} #(Submodule.torsion R C) := by
  classical
  let K := FractionRing R
  let D := K ⊗[R] C
  let f : C →ₗ[R] D := TensorProduct.mk R K C 1
  have bc : IsBaseChange K f := TensorProduct.isBaseChange R C K
  have hker : LinearMap.ker f = Submodule.torsion R C := by
    ext c
    exact (IsLocalizedModule.eq_zero_iff (nonZeroDivisors R) f).trans
      (Submodule.mem_torsion_iff c).symm
  let fG : GroupLike R C → GroupLike K D := fun g =>
    ⟨(1 : K) ⊗ₜ[R] g.val, g.isGroupLikeElem_val.baseChange K⟩
  have hfG (g : GroupLike R C) : (fG g).val = f g.val :=
    (TensorProduct.mk_apply (R := R) (1 : K) g.val).symm
  let I : Set (GroupLike K D) := Set.range fG
  let p : GroupLike R C → I := fun g => ⟨fG g, ⟨g, rfl⟩⟩
  have hfiber : ∀ y : I,
      Cardinal.lift.{max u v} #(p ⁻¹' {y}) ≤
        Cardinal.lift.{max u v} #(Submodule.torsion R C) := by
    intro y
    obtain ⟨a, ha⟩ := y.property
    let e : (p ⁻¹' {y}) ↪ Submodule.torsion R C :=
      { toFun := fun x => ⟨x.val.val - a.val, by
          rw [← hker]
          change f (x.val.val - a.val) = 0
          rw [map_sub]
          have hx : p x.val = y := Set.mem_singleton_iff.mp x.property
          have hx' : fG x.val = y.val := congrArg Subtype.val hx
          exact sub_eq_zero.mpr <| (hfG x.val).symm.trans
            ((congrArg GroupLike.val (hx'.trans ha.symm)).trans (hfG a))⟩
        inj' := by
          intro x z h
          apply Subtype.ext
          apply GroupLike.val_injective
          have hv := congrArg (fun t : Submodule.torsion R C => (t : C)) h
          have hc := congrArg (fun c : C => c + a.val) hv
          simpa only [sub_add_cancel] using hc }
    exact Cardinal.lift_le.mpr (Cardinal.mk_le_of_injective e.injective)
  have hcount : Cardinal.lift.{max u v} #(GroupLike R C) ≤
      Cardinal.lift.{v} #I * Cardinal.lift.{max u v} #(Submodule.torsion R C) :=
    Cardinal.lift_mk_le_lift_mk_mul_of_lift_mk_preimage_le p hfiber
  have himage : #I ≤ #(GroupLike K D) :=
    Cardinal.mk_le_of_injective
      (Subtype.val_injective : Function.Injective (fun y : I => y.val))
  have hi : Cardinal.lift.{v} #I ≤ Cardinal.lift.{v} (Module.rank K D) :=
    Cardinal.lift_le.mpr (himage.trans (cardinalMk_le_rank K D))
  have h := hcount.trans (mul_le_mul_left hi _)
  rw [bc.lift_rank_eq] at h
  rw [← Cardinal.lift_mul] at h
  rw [← Cardinal.lift_mul]
  exact Cardinal.lift_le.mpr (Cardinal.lift_le.mp h)

omit [IsDomain R] [Coalgebra R C] in
private theorem rank_mul_torsion_lt_aleph0 [Finite (Submodule.torsion R C)]
    (hrank : Module.rank R C < ℵ₀) :
    Cardinal.lift.{u} (Module.rank R C) *
      Cardinal.lift.{u} #(Submodule.torsion R C) < ℵ₀ := by
  have ht : #(Submodule.torsion R C) < ℵ₀ :=
    Cardinal.lt_aleph0_iff_finite.mpr inferInstance
  exact Cardinal.mul_lt_aleph0 (Cardinal.lift_lt_aleph0.mpr hrank)
    (Cardinal.lift_lt_aleph0.mpr ht)

/-- Finite cardinal rank and finite underlying torsion imply a genuinely finite
carrier of group-like elements, without a finite-generation assumption. -/
theorem finite_of_rank_lt_aleph0_of_finite_torsion [Finite (Submodule.torsion R C)]
    (hrank : Module.rank R C < ℵ₀) : Finite (GroupLike R C) := by
  apply Cardinal.lt_aleph0_iff_finite.mp
  exact Cardinal.lift_lt_aleph0.mp <|
    (cardinalMk_le_rank_mul_torsion R C).trans_lt
      (rank_mul_torsion_lt_aleph0 R C hrank)

/-- The finite-rank numerical bound, with the torsion factor retained. Finiteness
of the group-like carrier is established before applying the cardinal-to-natural bridge. -/
theorem nat_card_le_finrank_mul_torsion_of_rank_lt_aleph0
    [Finite (Submodule.torsion R C)] (hrank : Module.rank R C < ℵ₀) :
    Nat.card (GroupLike R C) ≤ Module.finrank R C * Nat.card (Submodule.torsion R C) := by
  let : Finite (GroupLike R C) :=
    finite_of_rank_lt_aleph0_of_finite_torsion R C hrank
  have h := Cardinal.toNat_le_toNat (cardinalMk_le_rank_mul_torsion R C)
    (rank_mul_torsion_lt_aleph0 R C hrank)
  simpa only [Cardinal.toNat_mul, Cardinal.toNat_lift, Nat.card, Module.finrank] using h

omit [Coalgebra R C] in
private theorem rank_lt_aleph0_of_fractionRing_rank_eq_nat (n : ℕ)
    (hdim : Module.rank (FractionRing R) ((FractionRing R) ⊗[R] C) = n) :
    Module.rank R C < ℵ₀ := by
  have bc := TensorProduct.isBaseChange R C (FractionRing R)
  have h : Cardinal.lift.{max u v} (Module.rank R C) < ℵ₀ := by
    rw [← bc.lift_rank_eq, hdim]
    exact Cardinal.lift_lt_aleph0.mpr (Cardinal.natCast_lt_aleph0 (n := n))
  exact Cardinal.lift_lt_aleph0.mp h

/-- A coalgebra with finite underlying torsion and finite cardinal dimension over
the fraction field has finitely many group-like elements. This includes dimension zero. -/
theorem finite_of_fractionRing_rank_eq_nat [Finite (Submodule.torsion R C)] (n : ℕ)
    (hdim : Module.rank (FractionRing R) ((FractionRing R) ⊗[R] C) = n) :
    Finite (GroupLike R C) :=
  finite_of_rank_lt_aleph0_of_finite_torsion R C
    (rank_lt_aleph0_of_fractionRing_rank_eq_nat R C n hdim)

/-- If the fraction-field scalar extension has cardinal dimension `n`, the number
of group-like elements is at most `n` times the number of torsion elements.
The canonical base-change finrank equality supplies the numerical dimension. -/
theorem nat_card_le_mul_torsion_of_fractionRing_rank_eq_nat
    [Finite (Submodule.torsion R C)] (n : ℕ)
    (hdim : Module.rank (FractionRing R) ((FractionRing R) ⊗[R] C) = n) :
    Nat.card (GroupLike R C) ≤ n * Nat.card (Submodule.torsion R C) := by
  let : Finite (GroupLike R C) := finite_of_fractionRing_rank_eq_nat R C n hdim
  have bc := TensorProduct.isBaseChange R C (FractionRing R)
  have hfinrank : Module.finrank R C = n := by
    rw [← bc.finrank_eq]
    change Cardinal.toNat (Module.rank (FractionRing R) ((FractionRing R) ⊗[R] C)) = n
    rw [hdim]
    exact Cardinal.toNat_natCast n
  simpa only [hfinrank] using
    nat_card_le_finrank_mul_torsion_of_rank_lt_aleph0 R C
      (rank_lt_aleph0_of_fractionRing_rank_eq_nat R C n hdim)

end GroupLike
