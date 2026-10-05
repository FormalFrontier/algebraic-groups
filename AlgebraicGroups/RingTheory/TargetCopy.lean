/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# A disjoint copy of a ring

This file provides a copy of a type which does not inherit any of its module
or algebra instances.  It is useful when two incompatible scalar actions on
the same underlying ring must coexist in one expression.

The copy has a canonical ring equivalence with its source; homomorphisms into
the source can be transported to give separately chosen scalar actions on the
copy, including in mixed tensor products.

## References

* Mathlib's `Function.Injective.commRing`, `RingEquiv.symm.toRingHom`, and
  `RingHom.toAlgebra` provide the structure and homomorphism transport used
  here; `Mathlib.RingTheory.TensorProduct.Basic` supplies the tensor-product
  algebra setting. The disjoint wrapper isolates the resulting scalar actions.
-/

public section

noncomputable section

universe u uC uA uB

/-- A distinct copy of a type which does not inherit the original type's
module and algebra instances. -/
structure TargetCopy (S : Type u) where
  /-- The element of the original type represented by this copy. -/
  down : S

namespace TargetCopy

variable {S : Type u}

instance [Zero S] : Zero (TargetCopy S) := ⟨⟨0⟩⟩
instance [One S] : One (TargetCopy S) := ⟨⟨1⟩⟩
instance [Add S] : Add (TargetCopy S) := ⟨fun x y ↦ ⟨x.down + y.down⟩⟩
instance [Mul S] : Mul (TargetCopy S) := ⟨fun x y ↦ ⟨x.down * y.down⟩⟩
instance [Neg S] : Neg (TargetCopy S) := ⟨fun x ↦ ⟨-x.down⟩⟩
instance [Sub S] : Sub (TargetCopy S) := ⟨fun x y ↦ ⟨x.down - y.down⟩⟩
instance [SMul ℕ S] : SMul ℕ (TargetCopy S) := ⟨fun n x ↦ ⟨n • x.down⟩⟩
instance [SMul ℤ S] : SMul ℤ (TargetCopy S) := ⟨fun n x ↦ ⟨n • x.down⟩⟩
instance [Pow S ℕ] : Pow (TargetCopy S) ℕ := ⟨fun x n ↦ ⟨x.down ^ n⟩⟩
instance [NatCast S] : NatCast (TargetCopy S) := ⟨fun n ↦ ⟨n⟩⟩
instance [IntCast S] : IntCast (TargetCopy S) := ⟨fun n ↦ ⟨n⟩⟩

instance [CommRing S] : CommRing (TargetCopy S) :=
  Function.Injective.commRing down (by
    intro x y h
    cases x
    cases y
    cases h
    rfl)
    rfl rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ ↦ rfl) (fun _ ↦ rfl)

/-- The canonical ring equivalence from the distinct copy back to its source. -/
@[expose]
def ringEquiv [CommRing S] : TargetCopy S ≃+* S where
  toFun := down
  invFun := TargetCopy.mk
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

/-- Transport a ring homomorphism to a genuinely distinct target copy. -/
@[expose]
def map {R : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    R →+* TargetCopy S :=
  ringEquiv.symm.toRingHom.comp f

end TargetCopy

variable {C : Type uC} {A : Type uA} {B : Type uB}
  [CommRing C] [CommRing A] [CommRing B]
  [Algebra C A] [Algebra C B]

/-- The scalar action on a target copy induced by a ring homomorphism. -/
@[expose]
def targetCopyMap (t : A →+* B) : A →+* TargetCopy B :=
  TargetCopy.map t

/-- The transported `A`-action on the target copy extends its inherited
`C`-action when `t : A →ₐ[C] B`. -/
lemma targetCopy_isScalarTower (t : A →ₐ[C] B) :
    letI : Algebra C (TargetCopy B) :=
      (targetCopyMap (algebraMap C B)).toAlgebra
    letI : Algebra A (TargetCopy B) :=
      (targetCopyMap t.toRingHom).toAlgebra
    IsScalarTower C A (TargetCopy B) := by
  let _ : Algebra C (TargetCopy B) :=
    (targetCopyMap (algebraMap C B)).toAlgebra
  let _ : Algebra A (TargetCopy B) :=
    (targetCopyMap t.toRingHom).toAlgebra
  exact IsScalarTower.of_algebraMap_eq'
    (R := C) (S := A) (A := TargetCopy B) <| by
      ext x
      exact congr_arg TargetCopy.mk (t.commutes x).symm
