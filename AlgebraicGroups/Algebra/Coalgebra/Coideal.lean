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

`Coideal.map f` is the ordinary linear image under a coalgebra-structure-preserving
map, while `Coideal.coreComap f` takes the coideal core of the ordinary submodule
preimage. These operations form a Galois connection: image preserves arbitrary
joins and core-preimage preserves arbitrary meets, including empty families.
They respect identity and composition without requiring coalgebra laws.

## References

The proof-only bundle and carrier API follow Mathlib's `HomogeneousSubmodule`
and this library's `Subcoalgebra`. The order-theoretic interface uses Mathlib's
`GaloisConnection` and the coinsertion pattern of `TopologicalSpace.Opens`.
Transport uses Mathlib's submodule map/comap adjunction and the coideal-image
theorem from `AlgebraicGroups.Algebra.Coalgebra.Quotient`.
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

instance : PartialOrder (Coideal R C) := .ofSetLike (Coideal R C) C

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

namespace Coideal

universe uR uC uD uE uF uι

variable {R : Type uR} [CommRing R]
variable {C : Type uC} [AddCommGroup C] [Module R C] [CoalgebraStruct R C]
variable {D : Type uD} [AddCommGroup D] [Module R D] [CoalgebraStruct R D]

section Map

variable {F : Type uF} [FunLike F C D] [CoalgHomClass F R C D]

/-- The ordinary linear image of a coideal under a coalgebra-structure-preserving map. -/
def map (f : F) (I : Coideal R C) : Coideal R D where
  toSubmodule := I.toSubmodule.map (f : C →ₗ[R] D)
  isCoideal' := I.isCoideal.map f

/-- The greatest coideal contained in the ordinary submodule preimage. -/
def coreComap (f : F) (J : Coideal R D) : Coideal R C :=
  core (J.toSubmodule.comap (f : C →ₗ[R] D))

/-- The carrier of coideal image is the ordinary submodule image. -/
@[simp]
theorem toSubmodule_map (f : F) (I : Coideal R C) :
    (map f I).toSubmodule = I.toSubmodule.map (f : C →ₗ[R] D) :=
  rfl

/-- Membership in coideal image is witnessed by a member of the source coideal. -/
theorem mem_map (f : F) (I : Coideal R C) {y : D} :
    y ∈ map f I ↔ ∃ x, x ∈ I ∧ f x = y :=
  Submodule.mem_map

/-- Core-preimage is the coideal core of the ordinary submodule preimage. -/
theorem coreComap_eq_core (f : F) (J : Coideal R D) :
    coreComap f J = core (J.toSubmodule.comap (f : C →ₗ[R] D)) :=
  rfl

/-- A member of core-preimage maps into the target coideal. -/
theorem apply_mem_of_mem_coreComap (f : F) (J : Coideal R D) {x : C}
    (hx : x ∈ coreComap f J) : f x ∈ J :=
  core_le (J.toSubmodule.comap (f : C →ₗ[R] D)) hx

/-- A source coideal lies in core-preimage exactly when its carrier lies in preimage. -/
theorem le_coreComap_iff (f : F) {I : Coideal R C} {J : Coideal R D} :
    I ≤ coreComap f J ↔ I.toSubmodule ≤ J.toSubmodule.comap (f : C →ₗ[R] D) :=
  le_core_iff

/-- Coideal direct image is left adjoint to coideal core-preimage. -/
theorem gc_map_coreComap (f : F) :
    GaloisConnection (map f : Coideal R C → Coideal R D) (coreComap f) := by
  intro I J
  calc
    map f I ≤ J ↔ (map f I).toSubmodule ≤ J.toSubmodule :=
      toSubmodule_le_toSubmodule.symm
    _ ↔ I.toSubmodule ≤ J.toSubmodule.comap (f : C →ₗ[R] D) := by
      rw [toSubmodule_map, Submodule.map_le_iff_le_comap]
    _ ↔ I ≤ coreComap f J := (le_coreComap_iff f).symm

/-- Image lies in a coideal exactly when the source lies in its core-preimage. -/
theorem map_le_iff_le_coreComap (f : F) {I : Coideal R C} {J : Coideal R D} :
    map f I ≤ J ↔ I ≤ coreComap f J :=
  gc_map_coreComap f I J

/-- Coideal image is monotone. -/
theorem map_mono (f : F) : Monotone (map f : Coideal R C → Coideal R D) :=
  (gc_map_coreComap f).monotone_l

/-- Coideal core-preimage is monotone. -/
theorem coreComap_mono (f : F) : Monotone (coreComap f : Coideal R D → Coideal R C) :=
  (gc_map_coreComap f).monotone_u

/-- Direct image preserves arbitrary indexed coideal joins, including empty joins. -/
@[simp]
theorem map_iSup (f : F) {ι : Sort uι} (I : ι → Coideal R C) :
    map f (⨆ i, I i) = ⨆ i, map f (I i) :=
  (gc_map_coreComap f).l_iSup

/-- Core-preimage preserves arbitrary indexed coideal meets, including empty meets. -/
@[simp]
theorem coreComap_iInf (f : F) {ι : Sort uι} (J : ι → Coideal R D) :
    coreComap f (⨅ i, J i) = ⨅ i, coreComap f (J i) :=
  (gc_map_coreComap f).u_iInf

/-- Direct image preserves joins of sets of coideals. -/
theorem map_sSup (f : F) (S : Set (Coideal R C)) :
    map f (sSup S) = sSup (map f '' S) :=
  (gc_map_coreComap f).l_sSup_eq_sSup_image

/-- Core-preimage preserves meets of sets of coideals. -/
theorem coreComap_sInf (f : F) (S : Set (Coideal R D)) :
    coreComap f (sInf S) = sInf (coreComap f '' S) :=
  (gc_map_coreComap f).u_sInf_eq_sInf_image

/-- The image of the least coideal is the least coideal. -/
@[simp]
theorem map_bot (f : F) : map f (⊥ : Coideal R C) = ⊥ :=
  (gc_map_coreComap f).l_bot

/-- The core-preimage of the greatest coideal is the greatest coideal. -/
@[simp]
theorem coreComap_top (f : F) : coreComap f (⊤ : Coideal R D) = ⊤ :=
  (gc_map_coreComap f).u_top

end Map

/-- Image under the identity coalgebra morphism fixes every coideal. -/
@[simp]
theorem map_id (I : Coideal R C) : map (CoalgHom.id R C) I = I := by
  apply toSubmodule_injective
  rw [toSubmodule_map, CoalgHom.id_toLinearMap, Submodule.map_id]

/-- Core-preimage under the identity coalgebra morphism fixes every coideal. -/
@[simp]
theorem coreComap_id (I : Coideal R C) : coreComap (CoalgHom.id R C) I = I :=
  (gc_map_coreComap (CoalgHom.id R C)).u_unique GaloisConnection.id (fun J => map_id J)

variable {E : Type uE} [AddCommGroup E] [Module R E] [CoalgebraStruct R E]

/-- Coideal image respects composition of coalgebra morphisms. -/
theorem map_comp (f : C →ₗc[R] D) (g : D →ₗc[R] E) (I : Coideal R C) :
    map (g.comp f) I = map g (map f I) := by
  apply toSubmodule_injective
  simp only [toSubmodule_map, CoalgHom.comp_toLinearMap, Submodule.map_comp]

/-- Coideal core-preimage reverses composition of coalgebra morphisms. -/
theorem coreComap_comp (f : C →ₗc[R] D) (g : D →ₗc[R] E) (K : Coideal R E) :
    coreComap (g.comp f) K = coreComap f (coreComap g K) :=
  (gc_map_coreComap (g.comp f)).u_unique
    ((gc_map_coreComap f).compose (gc_map_coreComap g)) (fun I => map_comp f g I)

end Coideal
