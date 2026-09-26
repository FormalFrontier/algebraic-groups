/-
Authors: Formal Frontier Agents
SPDX-License-Identifier: Apache-2.0
-/
module

import AlgebraicGroups.RingTheory.TargetCopy

/-!
# Ordinary-import regression clients for the distinct target copy

These persistent clients check the public reduction and scalar-transport API.
They are deliberately private: this test module adds no downstream mathematical
interface and must not re-export its implementation checks.
-/

set_option warningAsError true

noncomputable section

namespace AlgebraicGroupsTest.TargetCopy

universe u v w

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

private theorem forward (x : TargetCopy S) :
    TargetCopy.ringEquiv x = x.down := rfl

private theorem inverse (x : S) :
    TargetCopy.ringEquiv.symm x = TargetCopy.mk x := rfl

private theorem transportedMap (f : R →+* S) (x : R) :
    TargetCopy.map f x = TargetCopy.mk (f x) := rfl

private theorem scalarMap (f : R →+* S) (x : R) :
    targetCopyMap f x = TargetCopy.mk (f x) := rfl

private theorem mapDownRewrite (f : R →+* S) (x : R) :
    (targetCopyMap f x).down = f x := by
  rw [scalarMap]

private theorem mapDownSimp (f : R →+* S) (x : R) :
    (TargetCopy.map f x).down = f x := by
  simp only [transportedMap]

variable {C : Type w} [CommRing C] [Algebra C R] [Algebra C S]

private theorem commutes (x : C) :
    letI : Algebra C (TargetCopy S) :=
      (targetCopyMap (algebraMap C S)).toAlgebra
    TargetCopy.ringEquiv.symm (algebraMap C S x) = algebraMap C (TargetCopy S) x := rfl

private def transportedAlgebraEquiv :
    letI : Algebra C (TargetCopy S) :=
      (targetCopyMap (algebraMap C S)).toAlgebra
    S ≃ₐ[C] TargetCopy S := by
  letI : Algebra C (TargetCopy S) :=
    (targetCopyMap (algebraMap C S)).toAlgebra
  exact AlgEquiv.ofRingEquiv (f := TargetCopy.ringEquiv.symm) (fun _ ↦ rfl)

private theorem scalarTower (f : R →ₐ[C] S) :
    letI : Algebra C (TargetCopy S) :=
      (targetCopyMap (algebraMap C S)).toAlgebra
    letI : Algebra R (TargetCopy S) :=
      (targetCopyMap f.toRingHom).toAlgebra
    IsScalarTower C R (TargetCopy S) := targetCopy_isScalarTower f

end AlgebraicGroupsTest.TargetCopy
