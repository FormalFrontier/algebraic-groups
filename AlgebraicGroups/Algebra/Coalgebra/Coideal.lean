/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.Quotient
public import Mathlib.Order.GaloisConnection.Basic

/-!
# Coideals and the coideal core of a submodule

`Coideal R C` bundles a submodule with Mathlib's `Submodule.IsCoideal` predicate.
Its order is inclusion of the underlying submodules. Only `CoalgebraStruct` is
needed: neither coalgebra laws nor flatness assumptions enter the definition.

`Coideal.core S` is the ambient submodule join of all coideals contained in `S`.
The coideality of this join follows from `Submodule.IsCoideal.iSup` before it is
bundled. Its characteristic property says that inclusion is left adjoint to core.

The Galois coinsertion `Coideal.gi` induces a complete lattice. Joins have the
ambient submodule carriers, including the bottom submodule. Meets and top are
cores of ambient meets and top, not necessarily those ambient submodules themselves.

## References

The proof-only bundle and carrier API follow Mathlib's `HomogeneousSubmodule`
and this library's `Subcoalgebra`. The order-theoretic interface uses Mathlib's
`GaloisConnection` and the coinsertion pattern of `TopologicalSpace.Opens`.
-/

@[expose] public section



universe u v z

/-- A submodule on which the counit vanishes and comultiplication descends to the
module quotient. The extra field is a proof of `Submodule.IsCoideal`. -/
structure Coideal (R : Type u) (C : Type v)
    [CommRing R] [AddCommGroup C] [Module R C] [CoalgebraStruct R C] : Type v
    extends Submodule R C where
  /-- The underlying submodule is a coideal. -/
  isCoideal' : toSubmodule.IsCoideal

/-- The underlying submodule of a coideal. -/
add_decl_doc Coideal.toSubmodule

namespace Coideal

variable {R : Type u} {C : Type v}
variable [CommRing R] [AddCommGroup C] [Module R C] [CoalgebraStruct R C]

instance : SetLike (Coideal R C) C where
  coe I := I.toSubmodule
  coe_injective I J h := by
    cases I
    cases J
    congr
    exact SetLike.coe_injective h

instance : PartialOrder (Coideal R C) := .ofSetLike (Coideal R C)

instance : CoeOut (Coideal R C) (Submodule R C) := ⟨toSubmodule⟩

instance : AddSubgroupClass (Coideal R C) C where
  zero_mem I := I.toSubmodule.zero_mem
  add_mem {I} := I.toSubmodule.add_mem
  neg_mem {I} := I.toSubmodule.neg_mem

instance : SMulMemClass (Coideal R C) R C where
  smul_mem {I} r _ hx := I.toSubmodule.smul_mem r hx

/-- The coideal predicate on the underlying submodule. -/
theorem isCoideal (I : Coideal R C) : I.toSubmodule.IsCoideal :=
  I.isCoideal'

@[simp]
theorem mem_toSubmodule {I : Coideal R C} {x : C} :
    x ∈ I.toSubmodule ↔ x ∈ I :=
  Iff.rfl

/-- Membership in a coideal is membership in its underlying submodule. -/
theorem mem_iff (I : Coideal R C) {x : C} : x ∈ I ↔ x ∈ I.toSubmodule :=
  Iff.rfl

@[simp]
theorem coe_toSubmodule (I : Coideal R C) : (I.toSubmodule : Set C) = I :=
  rfl

/-- Coideals with the same members are equal. -/
@[ext]
theorem ext {I J : Coideal R C} (h : ∀ x : C, x ∈ I ↔ x ∈ J) : I = J :=
  SetLike.ext h

/-- The underlying submodule determines a coideal. -/
theorem toSubmodule_injective :
    Function.Injective (toSubmodule : Coideal R C → Submodule R C) :=
  fun _ _ h => SetLike.coe_injective (congrArg (fun S : Submodule R C => (S : Set C)) h)

@[simp]
theorem toSubmodule_inj {I J : Coideal R C} :
    I.toSubmodule = J.toSubmodule ↔ I = J :=
  toSubmodule_injective.eq_iff

/-- Forgetting the coideal proof preserves and reflects inclusion. -/
@[simp]
theorem toSubmodule_le_toSubmodule {I J : Coideal R C} :
    I.toSubmodule ≤ J.toSubmodule ↔ I ≤ J :=
  Iff.rfl

/-- Bundle a submodule together with a proof that it is a coideal. -/
def ofSubmodule (S : Submodule R C) (hS : S.IsCoideal) : Coideal R C where
  toSubmodule := S
  isCoideal' := hS

@[simp]
theorem toSubmodule_ofSubmodule (S : Submodule R C) (hS : S.IsCoideal) :
    (ofSubmodule S hS).toSubmodule = S :=
  rfl

@[simp]
theorem mem_ofSubmodule (S : Submodule R C) (hS : S.IsCoideal) {x : C} :
    x ∈ ofSubmodule S hS ↔ x ∈ S :=
  Iff.rfl

@[simp]
theorem ofSubmodule_toSubmodule (I : Coideal R C) :
    ofSubmodule I.toSubmodule I.isCoideal = I :=
  toSubmodule_injective rfl

/-- The coideal core of a submodule: the join of all coideals contained in it. -/
def core (S : Submodule R C) : Coideal R C := by
  have h : (⨆ J : {J : Submodule R C // J.IsCoideal ∧ J ≤ S}, J.val).IsCoideal :=
    Submodule.IsCoideal.iSup _ (fun J => J.property.1)
  exact ofSubmodule _ h

/-- The carrier of core is an indexed join in the ambient submodule lattice. -/
theorem toSubmodule_core (S : Submodule R C) :
    (core S).toSubmodule = ⨆ J : {J : Submodule R C // J.IsCoideal ∧ J ≤ S}, J.val :=
  rfl

/-- The coideal core is contained in the supplied submodule. -/
theorem core_le (S : Submodule R C) : (core S).toSubmodule ≤ S := by
  rw [toSubmodule_core]
  exact iSup_le fun J => J.property.2

/-- Every coideal contained in a submodule is contained in its coideal core. -/
theorem le_core {I : Coideal R C} {S : Submodule R C} (h : I.toSubmodule ≤ S) :
    I ≤ core S := by
  apply toSubmodule_le_toSubmodule.mp
  rw [toSubmodule_core]
  exact le_iSup (fun J : {J : Submodule R C // J.IsCoideal ∧ J ≤ S} => J.val)
    ⟨I.toSubmodule, I.isCoideal, h⟩

/-- Core is characterized by maximal containment of coideals. -/
theorem le_core_iff {I : Coideal R C} {S : Submodule R C} :
    I ≤ core S ↔ I.toSubmodule ≤ S :=
  ⟨fun h _ hx => core_le S (h hx), le_core⟩

/-- A coideal is fixed by core after forgetting its proof. -/
@[simp]
theorem core_coe (I : Coideal R C) : core I.toSubmodule = I := by
  apply le_antisymm
  · exact core_le I.toSubmodule
  · exact le_core le_rfl

/-- Inclusion of coideals into submodules is left adjoint to coideal core. -/
theorem gc : GaloisConnection (toSubmodule : Coideal R C → Submodule R C) core :=
  fun _ _ => le_core_iff.symm

/-- Coideal core is monotone in the ambient submodule. -/
theorem core_mono : Monotone (core : Submodule R C → Coideal R C) :=
  gc.monotone_u

/-- The Galois coinsertion of coideals into submodules, with core as right adjoint.
Its choice repackages a fixed submodule without changing its carrier. -/
def gi : GaloisCoinsertion (toSubmodule : Coideal R C → Submodule R C) core where
  choice S h := ofSubmodule S (by
    have hfix : (core S).toSubmodule = S := le_antisymm (core_le S) h
    exact hfix ▸ (core S).isCoideal)
  gc := gc
  u_l_le I := (core_coe I).le
  choice_eq S h := toSubmodule_injective (le_antisymm h (core_le S))

instance : CompleteLattice (Coideal R C) := gi.liftCompleteLattice

/-- The carrier of a binary coideal join is the ambient submodule join. -/
@[simp]
theorem toSubmodule_sup (I J : Coideal R C) :
    (I ⊔ J).toSubmodule = I.toSubmodule ⊔ J.toSubmodule :=
  gc.l_sup

/-- The carrier of an arbitrary coideal join is the ambient submodule join. -/
@[simp]
theorem toSubmodule_sSup (A : Set (Coideal R C)) :
    (sSup A).toSubmodule = sSup (toSubmodule '' A) :=
  gc.l_sSup_eq_sSup_image

/-- The carrier of an indexed coideal join is the ambient indexed submodule join. -/
@[simp]
theorem toSubmodule_iSup {ι : Sort z} (F : ι → Coideal R C) :
    (⨆ i, F i).toSubmodule = ⨆ i, (F i).toSubmodule :=
  gc.l_iSup

/-- A binary coideal meet is the core of the ambient submodule meet. -/
theorem inf_eq_core (I J : Coideal R C) :
    I ⊓ J = core (I.toSubmodule ⊓ J.toSubmodule) :=
  rfl

/-- An arbitrary coideal meet is the core of the ambient submodule meet. -/
theorem sInf_eq_core (A : Set (Coideal R C)) :
    sInf A = core (sInf (toSubmodule '' A)) :=
  rfl

/-- The greatest coideal is the core of the ambient top submodule. -/
theorem top_eq_core : (⊤ : Coideal R C) = core (⊤ : Submodule R C) :=
  rfl

/-- The least coideal has the zero submodule as carrier. -/
@[simp]
theorem toSubmodule_bot : (⊥ : Coideal R C).toSubmodule = ⊥ :=
  gc.l_bot

@[simp]
theorem mem_bot {x : C} : x ∈ (⊥ : Coideal R C) ↔ x = 0 := by
  rw [mem_iff, toSubmodule_bot, Submodule.mem_bot]

end Coideal
