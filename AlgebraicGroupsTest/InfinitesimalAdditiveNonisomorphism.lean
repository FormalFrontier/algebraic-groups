/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.InfinitesimalAdditiveNonisomorphism
public import Mathlib.Algebra.Field.ZMod

public section

set_option warningAsError true

open CategoryTheory AlgebraicGeometry

universe u

theorem infinitesimalAdditive_not_iso_abstract
    (K : Type u) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (m : ℕ) (hm : 0 < m) :
    ¬ Nonempty (infinitesimalAdditiveGroupScheme K p m ≅
      rootsOfUnityGroupScheme K (p ^ m)) :=
  infinitesimalAdditiveGroupScheme_not_iso_rootsOfUnity K p m hm

theorem infinitesimalAdditive_not_iso_reverse
    (K : Type u) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (m : ℕ) (hm : 0 < m) :
    ¬ Nonempty (rootsOfUnityGroupScheme K (p ^ m) ≅
      infinitesimalAdditiveGroupScheme K p m) := by
  rintro ⟨iso⟩
  exact infinitesimalAdditiveGroupScheme_not_iso_rootsOfUnity K p m hm ⟨iso.symm⟩

theorem infinitesimalAdditive_not_iso_zmod2 :
    ¬ Nonempty (infinitesimalAdditiveGroupScheme (ZMod 2) 2 1 ≅
      rootsOfUnityGroupScheme (ZMod 2) (2 ^ 1)) :=
  infinitesimalAdditiveGroupScheme_not_iso_rootsOfUnity (ZMod 2) 2 1 (by decide)

theorem infinitesimalAdditive_not_iso_zmod3 :
    ¬ Nonempty (infinitesimalAdditiveGroupScheme (ZMod 3) 3 1 ≅
      rootsOfUnityGroupScheme (ZMod 3) (3 ^ 1)) :=
  infinitesimalAdditiveGroupScheme_not_iso_rootsOfUnity (ZMod 3) 3 1 (by decide)

/-- The infinitesimal native presentation elaborates in group objects over the base scheme. -/
noncomputable def infinitesimalAdditiveNativeGroupObject
    (K : Type u) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (m : ℕ) : Grp (Over (Spec (.of K))) :=
  infinitesimalAdditiveGroupScheme K p m

theorem infinitesimalAdditive_coordinate_zero_exponent
    (K : Type u) [Field K] (p : ℕ) :
    infinitesimalAdditiveCoordinate K p 0 = 0 := by
  simpa using infinitesimalAdditiveCoordinate_pow K p 0

#print axioms infinitesimalAdditive_not_iso_abstract
#print axioms infinitesimalAdditive_not_iso_reverse
#print axioms infinitesimalAdditive_not_iso_zmod2
#print axioms infinitesimalAdditive_not_iso_zmod3
#print axioms infinitesimalAdditiveNativeGroupObject
#print axioms infinitesimalAdditive_coordinate_zero_exponent

#lint
