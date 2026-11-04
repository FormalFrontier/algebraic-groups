/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.HopfAlgebra.Subalgebra.Hom
public import AlgebraicGroups.Algebra.HopfAlgebra.Subalgebra.Pure

/-!
# Hopf structures on stable subalgebras

Over a field, a subalgebra stable under comultiplication and the antipode inherits a
Hopf algebra structure on its given algebra and module. Its inclusion is a bialgebra
homomorphism, and bialgebra homomorphisms with values in the subalgebra lift uniquely
through this inclusion. The counit is restricted without an additional closure condition.
Finite-dimensional Hopf subalgebras have injective tensor units, as do finite-type Hopf
subalgebras with nil augmentation kernel.
-/
