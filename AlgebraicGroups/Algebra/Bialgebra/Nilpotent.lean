/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Bialgebra.Derivation
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import SmoothRegularity.Algebra.Derivation
public import SmoothRegularity.Algebra.PointDerivation

/-!
# Nilpotent elements and the augmentation ideal

For a commutative bialgebra over a field of characteristic zero, every nilpotent
element belongs to the square of the kernel of the counit.

Point derivations extend to left-invariant derivations, which preserve nilpotent
elements. Their counit values therefore vanish. Linear functionals on the
augmentation cotangent represent the point derivations and separate its elements,
so the cotangent class of a nilpotent element is zero.

This is an augmentation-square containment, not a reducedness assertion. No
antipode or finite-generation hypothesis is used.

## References

The proof uses Mathlib's ideal cotangent and dual separation APIs, the cotangent
representation of point derivations in `SmoothRegularity.Algebra.PointDerivation`,
and preservation of nilpotent elements by derivations in
`SmoothRegularity.Algebra.Derivation`.
-/

@[expose] public section

universe u v

namespace Bialgebra

variable (K : Type u) (H : Type v)
variable [Field K] [CharZero K] [CommRing H] [Bialgebra K H]

/-- In a commutative bialgebra over a characteristic-zero field, every nilpotent
element lies in the square of the augmentation ideal. -/
theorem nilradical_le_ker_counit_sq :
    nilradical H ≤ (RingHom.ker ((Bialgebra.counitAlgHom K H).toRingHom)) ^ 2 := by
  let ε : H →ₐ[K] K := Bialgebra.counitAlgHom K H
  let I : Ideal H := RingHom.ker ε.toRingHom
  let htf : IsAddTorsionFree H := IsAddTorsionFree.of_isTorsionFree K H
  intro a ha
  have ha_nil : IsNilpotent a := mem_nilradical.mp ha
  have haI : a ∈ I := by
    change ε a = 0
    exact (ha_nil.map ε).eq_zero
  change a ∈ I ^ 2
  apply (I.toCotangent_eq_zero ⟨a, haI⟩).mp
  apply (Module.forall_dual_apply_eq_zero_iff K (I.toCotangent ⟨a, haI⟩)).mp
  intro f
  let δ : @Derivation K H K _ _ _ _ (Module.compHom K ε.toRingHom) _ :=
    ε.cotangentEquivPointDerivation (M := K) f
  have hD : IsNilpotent (Derivation.leftInvariant δ a) :=
    @Derivation.isNilpotent_apply K H _ _ _ htf (Derivation.leftInvariant δ) a ha_nil
  calc
    f (I.toCotangent ⟨a, haI⟩) = δ a :=
      (ε.cotangentEquivPointDerivation_apply_coe f ⟨a, haI⟩).symm
    _ = Coalgebra.counit (R := K) (Derivation.leftInvariant δ a) :=
      (Derivation.counit_leftInvariant_apply δ a).symm
    _ = 0 := (hD.map ε).eq_zero

end Bialgebra
