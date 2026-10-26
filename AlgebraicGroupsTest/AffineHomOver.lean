/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.AffineHomOver
public import Mathlib.Data.ZMod.Basic

/-!
# Affine identity and pullback on global sections

For the standard integer algebra `ZMod 2`, the affine identity gives the
canonical inverse spectrum global-sections map under the affine-target adjunction.
-/

public section

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

/-- For the standard Int-algebra ZMod 2, the affine identity is read back as
    the canonical inverse Gamma-Spec ring map, using only the bare API. -/
theorem affineSpecHomOverEquiv_int_zmod2_identity_toRingHom :
    CommRingCat.ofHom
      (affineSpecHomOverEquiv Int
        ((Spec (.of (ZMod 2))).asOver (Spec (.of Int)))
        (ZMod 2)
        (𝟙 ((Spec (.of (ZMod 2))).asOver (Spec (.of Int))) ≫
          (affineSpecHomOverTargetIso Int (ZMod 2)).inv)).toRingHom =
      (Scheme.ΓSpecIso (.of (ZMod 2))).inv := by
  rw [affineSpecHomOverEquiv_apply_toRingHom]
  change (Scheme.ΓSpecIso (.of (ZMod 2))).inv ≫ 𝟙 _ =
    (Scheme.ΓSpecIso (.of (ZMod 2))).inv
  exact Category.comp_id _

end AlgebraicGeometry
