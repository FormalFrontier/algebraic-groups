/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AlgebraicGroups.GroupObject.FunctorLimits
import Mathlib.CategoryTheory.Monoidal.Types.Basic

/-!
# Group-object transport for the identity functor

The identity functor on types commutes with forgetting internal groups to internal monoids,
and its induced functor on internal groups preserves binary products.
-/

open CategoryTheory

universe u

example :
    (𝟭 (Type u)).mapGrp ⋙ Grp.forget₂Mon (Type u) =
      Grp.forget₂Mon (Type u) ⋙ (𝟭 (Type u)).mapMon :=
  Functor.mapGrp_comp_forget₂Mon (𝟭 (Type u))

example :
    Limits.PreservesLimitsOfShape (Discrete Limits.WalkingPair) (𝟭 (Type u)).mapGrp :=
  inferInstance
