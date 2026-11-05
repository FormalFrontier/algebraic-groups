/-
Copyright (c) 2026 Formal Frontier Agents. All rights reserved.
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.RingTheory.FaithfullyFlat

/-!
# Faithful flatness through an algebra range

The range criterion applies over a commutative semiring base, using the
canonical ring structure on the range of the underlying ring homomorphism.
-/

@[expose] public section

universe uA uB

example {A : Type uA} {B : Type uB} [CommRing A] [CommRing B]
    [Algebra ℕ A] [Algebra ℕ B] (f : A →ₐ[ℕ] B) :
    f.toRingHom.FaithfullyFlat ↔
      (Function.Injective f ∧
        (show f.toRingHom.range →+* B from f.range.val.toRingHom).FaithfullyFlat) := by
  exact AlgHom.faithfullyFlat_iff_injective_and_range_val f
