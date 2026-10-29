/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AlgebraicGroups.GroupScheme.RootsOfUnityThree
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Cube-root coordinates over the three smallest relevant prime fields

Over F₇ the root 2 orders the split factors as 1, 2, 4, not as diagonal
scalars. Over F₂ the quadratic is irreducible and separable, although 2 is zero.
Over F₃ all field-extension points are the identity, but the coordinate algebra
has a nonzero nilpotent and the square-zero algebra has a nonidentity point.
The component-map check uses the scheme decomposition rather than a ring-only
replacement. All coordinate readbacks use the public laws.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Polynomial
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.RootsOfUnityThree

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private lemma sevenRoot_primitive : IsPrimitiveRoot (2 : ZMod 7) 3 := by
  refine (IsPrimitiveRoot.iff (by decide : 0 < 3)).2 ⟨by decide, ?_⟩
  intro l hl hlt
  interval_cases l <;> decide

-- The generator and scalars distinguish ordered evaluation from a diagonal map.
example : coordinateSplitAlgEquiv (ZMod 7) 2 sevenRoot_primitive
    (rootsOfUnityCoordinateGenerator (ZMod 7) 3) = (1, (2, 4)) := by
  simpa only [show (2 : ZMod 7) ^ 2 = 4 by decide] using
    coordinateSplitAlgEquiv_generator (ZMod 7) 2 sevenRoot_primitive

example (a : ZMod 7) : coordinateSplitAlgEquiv (ZMod 7) 2 sevenRoot_primitive
    (algebraMap (ZMod 7) (rootsOfUnityCoordinateRing (ZMod 7) 3) a) = (a, (a, a)) :=
  coordinateSplitAlgEquiv_algebraMap (ZMod 7) 2 sevenRoot_primitive a

-- On polynomial classes the second projection is evaluation at the chosen root.
example (p : (ZMod 7)[X]) :
    (coordinateSplitAlgEquiv (ZMod 7) 2 sevenRoot_primitive
      ((rootsOfUnityCoordinateAlgEquiv (ZMod 7) 3).symm (AdjoinRoot.mk _ p))).2.1 =
        p.eval 2 := by
  rw [coordinateSplitAlgEquiv_mk]

example :
    let h3 := primitiveRoot_three_isUnit (ZMod 7) 2 sevenRoot_primitive
    let hq := primitiveRoot_quadratic_eval (ZMod 7) 2 sevenRoot_primitive
    (coprod.inl ≫ coprod.inr ≫
      (splitSchemeIsoOfQuadraticRoot (ZMod 7) h3 2 hq).inv).left =
        Spec.map (CommRingCat.ofHom (splitComponentOne (ZMod 7) h3 2 hq).toRingHom) :=
  (splitSchemeIsoOfQuadraticRoot_components (ZMod 7)
    (primitiveRoot_three_isUnit (ZMod 7) 2 sevenRoot_primitive) 2
    (primitiveRoot_quadratic_eval (ZMod 7) 2 sevenRoot_primitive)).2.1

private lemma two_no_primitive : ¬ ∃ a : ZMod 2, IsPrimitiveRoot a 3 := by
  rintro ⟨a, ha⟩
  have hp := ha.pow_eq_one
  have hn := ha.ne_one (by decide : 1 < 3)
  fin_cases a
  · exact (by decide : (0 : ZMod 2) ^ 3 ≠ 1) hp
  · exact hn rfl

private lemma two_three_unit : IsUnit (3 : ZMod 2) := by
  rw [show (3 : ZMod 2) = 1 by decide]
  exact isUnit_one

example : Irreducible (X ^ 2 + X + 1 : (ZMod 2)[X]) ∧
    (X ^ 2 + X + 1 : (ZMod 2)[X]).Separable :=
  ⟨quadratic_irreducible (by decide) two_no_primitive,
    quadratic_separable two_three_unit⟩

example : coordinateTwoFactorAlgEquiv (ZMod 2) two_three_unit
    (rootsOfUnityCoordinateGenerator (ZMod 2) 3) =
      (1, AdjoinRoot.root (X ^ 2 + X + 1 : (ZMod 2)[X])) :=
  coordinateTwoFactorAlgEquiv_generator (ZMod 2) two_three_unit

example : rootsOfUnityCoordinateGenerator (ZMod 3) 3 - 1 ≠ 0 ∧
    (rootsOfUnityCoordinateGenerator (ZMod 3) 3 - 1) ^ 3 = 0 :=
  ⟨coordinate_sub_one_ne_zero (ZMod 3), coordinate_sub_one_cube (ZMod 3)⟩

example (F : Type) [Field F] [Algebra (ZMod 3) F]
    (x : (Spec (.of F)).asOver (Spec (.of (ZMod 3))) ⟶ rootsOfUnityScheme (ZMod 3) 3) :
    x = 1 :=
  fieldExtension_point_eq_one (ZMod 3) F x

example : squareZeroPoint (ZMod 3) ≠ 1 := squareZeroPoint_ne_one (ZMod 3)

example (p : (ZMod 3)[X]) :
    (rootsOfUnityMulEquivAlgHom (ZMod 3) (TrivSqZeroExt (ZMod 3) (ZMod 3)) 3
      (squareZeroRoot (ZMod 3))).ofConv
      ((rootsOfUnityCoordinateAlgEquiv (ZMod 3) 3).symm (AdjoinRoot.mk _ p)) =
      aeval (1 + TrivSqZeroExt.inr (1 : ZMod 3) : TrivSqZeroExt (ZMod 3) (ZMod 3)) p :=
  squareZeroPoint_eval (ZMod 3) p

end AlgebraicGeometry.RootsOfUnityThree
