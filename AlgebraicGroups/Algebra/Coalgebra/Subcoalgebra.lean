/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.RingTheory.Coalgebra.Basic

/-!
# Subcoalgebras over a field

A subcoalgebra is a subspace whose comultiplication lies in the image of the tensor square
of that subspace. Over a field the tensor inclusion is injective, so this closure condition
determines a unique restriction of the ambient comultiplication. The counit takes values in
the scalar field and requires no additional closure condition.

The set and type coercions use the underlying submodule. In particular, the additive and
module structures on a subcoalgebra are those on the existing submodule subtype.

## References

The carrier and tensor inclusion use Mathlib's `Submodule` and `TensorProduct.mapIncl`.
The ambient coalgebra follows `Mathlib.RingTheory.Coalgebra.Basic`; the submodule and tensor
maps follow `Mathlib.Algebra.Module.Submodule.LinearMap` and
`Mathlib.LinearAlgebra.TensorProduct.Map`. The carrier API follows Mathlib's `Submodule`
and `Subalgebra` conventions.
-/

@[expose] public section

universe u v

/-- A subspace of a coalgebra over a field closed under comultiplication into the image of
its tensor square. -/
structure Subcoalgebra (K : Type u) (C : Type v)
    [Field K] [AddCommGroup C] [Module K C] [Coalgebra K C] : Type v
    extends Submodule K C where
  /-- Comultiplication of every member lies in the image of the tensor square of the subspace. -/
  comul_mem' : ∀ ⦃x : C⦄, x ∈ toSubmodule →
    Coalgebra.comul (R := K) x ∈
      LinearMap.range (TensorProduct.mapIncl toSubmodule toSubmodule)

/-- The underlying submodule of a subcoalgebra. -/
add_decl_doc Subcoalgebra.toSubmodule

namespace Subcoalgebra

variable {K : Type u} {C : Type v}
variable [Field K] [AddCommGroup C] [Module K C] [Coalgebra K C]

instance : SetLike (Subcoalgebra K C) C where
  coe D := D.toSubmodule
  coe_injective D E h := by
    cases D
    cases E
    congr
    exact SetLike.coe_injective h

@[simp]
theorem mem_toSubmodule {D : Subcoalgebra K C} {x : C} :
    x ∈ D.toSubmodule ↔ x ∈ D :=
  Iff.rfl

@[simp]
theorem coe_toSubmodule (D : Subcoalgebra K C) : (D.toSubmodule : Set C) = D :=
  rfl

@[simp]
theorem carrier_eq_coe (D : Subcoalgebra K C) : D.carrier = (D : Set C) :=
  rfl

theorem mem_carrier {D : Subcoalgebra K C} {x : C} : x ∈ D.carrier ↔ x ∈ D :=
  Iff.rfl

/-- Membership in a subcoalgebra is membership in its underlying submodule. -/
theorem mem_iff (D : Subcoalgebra K C) {x : C} : x ∈ D ↔ x ∈ D.toSubmodule :=
  Iff.rfl

/-- Subcoalgebras are equal if they have the same members. -/
@[ext]
theorem ext {D E : Subcoalgebra K C} (h : ∀ x : C, x ∈ D ↔ x ∈ E) : D = E :=
  SetLike.ext h

/-- Subcoalgebras are equal if their underlying sets are equal. -/
theorem ext' {D E : Subcoalgebra K C} (h : (D : Set C) = E) : D = E :=
  SetLike.coe_injective h

theorem toSubmodule_injective :
    Function.Injective (toSubmodule : Subcoalgebra K C → Submodule K C) :=
  fun _ _ h => SetLike.coe_injective (congrArg (fun S : Submodule K C => (S : Set C)) h)

@[simp]
theorem toSubmodule_inj {D E : Subcoalgebra K C} :
    D.toSubmodule = E.toSubmodule ↔ D = E :=
  toSubmodule_injective.eq_iff

instance : AddSubgroupClass (Subcoalgebra K C) C where
  zero_mem D := D.toSubmodule.zero_mem
  add_mem {D} := D.toSubmodule.add_mem
  neg_mem {D} := D.toSubmodule.neg_mem

instance : SMulMemClass (Subcoalgebra K C) K C where
  smul_mem {D} r _ hx := D.toSubmodule.smul_mem r hx

/-- Comultiplication of a member lies in the image of the tensor square of the subcoalgebra. -/
theorem comul_mem (D : Subcoalgebra K C) {x : C} (hx : x ∈ D) :
    Coalgebra.comul (R := K) x ∈
      LinearMap.range (TensorProduct.mapIncl D.toSubmodule D.toSubmodule) :=
  D.comul_mem' hx

@[simp]
theorem toSubmodule_mk (S : Submodule K C) (hS) :
    (Subcoalgebra.mk S hS).toSubmodule = S :=
  rfl

@[simp]
theorem coe_set_mk (S : Submodule K C) (hS) : (Subcoalgebra.mk S hS : Set C) = S :=
  rfl

@[simp]
theorem mem_mk (S : Submodule K C) (hS) (x : C) :
    x ∈ Subcoalgebra.mk S hS ↔ x ∈ S :=
  Iff.rfl

/-- Construct a subcoalgebra from a submodule whose members have comultiplication in the
image of its tensor square. -/
def mk' (S : Submodule K C)
    (hS : ∀ ⦃x : C⦄, x ∈ S → Coalgebra.comul (R := K) x ∈
      LinearMap.range (TensorProduct.mapIncl S S)) : Subcoalgebra K C :=
  Subcoalgebra.mk S hS

@[simp]
theorem toSubmodule_mk' (S : Submodule K C) (hS) : (mk' S hS).toSubmodule = S :=
  rfl

@[simp]
theorem coe_mk' (S : Submodule K C) (hS) : (mk' S hS : Set C) = S :=
  rfl

@[simp]
theorem mem_mk' (S : Submodule K C) (hS) (x : C) : x ∈ mk' S hS ↔ x ∈ S :=
  Iff.rfl

/-- The subcoalgebra subtype is the subtype of its underlying submodule. -/
@[simp]
theorem coe_sort_toSubmodule (D : Subcoalgebra K C) : (D.toSubmodule : Type v) = D :=
  rfl

instance addCommGroup (D : Subcoalgebra K C) : AddCommGroup D :=
  D.toSubmodule.addCommGroup

instance module (D : Subcoalgebra K C) : Module K D :=
  D.toSubmodule.module

instance inhabited (D : Subcoalgebra K C) : Inhabited D :=
  ⟨0⟩

variable (D : Subcoalgebra K C)

protected theorem zero_mem : (0 : C) ∈ D :=
  D.toSubmodule.zero_mem

protected theorem add_mem {x y : C} (hx : x ∈ D) (hy : y ∈ D) : x + y ∈ D :=
  D.toSubmodule.add_mem hx hy

protected theorem neg_mem {x : C} (hx : x ∈ D) : -x ∈ D :=
  D.toSubmodule.neg_mem hx

protected theorem sub_mem {x y : C} (hx : x ∈ D) (hy : y ∈ D) : x - y ∈ D :=
  D.toSubmodule.sub_mem hx hy

theorem smul_mem (r : K) {x : C} (hx : x ∈ D) : r • x ∈ D :=
  D.toSubmodule.smul_mem r hx

variable {D}

/-- The coercion from a subcoalgebra to the ambient coalgebra is injective. -/
theorem coe_injective : Function.Injective ((↑) : D → C) :=
  Subtype.coe_injective

theorem coe_mem (x : D) : (x : C) ∈ D :=
  x.property

@[norm_cast]
theorem coe_mk (x : C) (hx : x ∈ D) : ((⟨x, hx⟩ : D) : C) = x :=
  rfl

@[simp, norm_cast]
theorem coe_zero : ((0 : D) : C) = 0 :=
  rfl

@[simp, norm_cast]
theorem coe_add (x y : D) : ((x + y : D) : C) = (x : C) + (y : C) :=
  rfl

@[simp, norm_cast]
theorem coe_neg (x : D) : ((-x : D) : C) = -(x : C) :=
  rfl

@[simp, norm_cast]
theorem coe_sub (x y : D) : ((x - y : D) : C) = (x : C) - (y : C) :=
  rfl

@[simp, norm_cast]
theorem coe_smul (r : K) (x : D) : ((r • x : D) : C) = r • (x : C) :=
  rfl

end Subcoalgebra
