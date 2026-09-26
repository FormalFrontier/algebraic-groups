/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Morphisms of group objects

This file records basic results about morphisms into group objects in a cartesian monoidal
category.
-/

public section

open CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CategoryTheory

open MonObj CartesianMonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable {M G : C} [MonObj M] [GrpObj G]

/-- A morphism from a monoid object to a group object that preserves multiplication is a monoid
morphism. -/
@[to_additive]
lemma isMonHom_of_mul_hom (f : M ⟶ G)
    (mul_hom : μ[M] ≫ f = (f ⊗ₘ f) ≫ μ[G]) : IsMonHom f where
  mul_hom := mul_hom
  one_hom := by
    have h : η[M] ≫ f = (η[M] ≫ f) * (η[M] ≫ f) := by
      calc
        η[M] ≫ f = (lift η[M] η[M] ≫ μ[M]) ≫ f := by
          simp [mul_eq_mul, comp_mul, one_eq_one]
        _ = lift η[M] η[M] ≫ (μ[M] ≫ f) := Category.assoc _ _ _
        _ = lift η[M] η[M] ≫ ((f ⊗ₘ f) ≫ μ[G]) := by rw [mul_hom]
        _ = (η[M] ≫ f) * (η[M] ≫ f) := by simp [mul_eq_mul, comp_mul]
    have h' : (η[M] ≫ f : 𝟙_ C ⟶ G) = 1 := by
      apply mul_right_cancel (b := (η[M] ≫ f : 𝟙_ C ⟶ G))
      simpa only [_root_.one_mul] using h.symm
    simpa only [one_eq_one] using h'

end CategoryTheory
