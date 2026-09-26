/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Filtered

/-!
# Filtered colimits of groups

This file supplies the same-universe filtered-colimit existence instance for
`GrpCat`, using Mathlib's explicit filtered-colimit cocone and its universal
property.
-/

public section

noncomputable section

open CategoryTheory Limits

universe u

/-- The category of groups has filtered colimits indexed in its own universe. -/
noncomputable instance GrpCat.hasFilteredColimits : HasFilteredColimits (GrpCat.{u}) where
  HasColimitsOfShape _ _ _ :=
    { has_colimit F :=
        ⟨GrpCat.FilteredColimits.colimitCocone F,
          GrpCat.FilteredColimits.colimitCoconeIsColimit F⟩ }
