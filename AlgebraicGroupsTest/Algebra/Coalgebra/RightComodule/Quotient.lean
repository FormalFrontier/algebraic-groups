/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.Quotient
public import Mathlib.Algebra.Field.Rat
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Prod

/-!
# A nonzero proper right-comodule quotient

The scalar right comodule on `ℚ × ℚ`, quotiented by the kernel of the second
projection, has a nonzero proper kernel and a quotient linearly equivalent to `ℚ`.
The coaction used here is the descended coaction, not an independently chosen
scalar coaction on the quotient. The projection factors through the canonical
comodule quotient, and its induced linear equivalence and inverse are colinear.
The final two examples check the bottom and top boundaries on the same comodule.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace Coalgebra.RightComodule.QuotientTest

abbrev M := ℚ × ℚ

abbrev X : RightComodule ℚ ℚ M := scalar ℚ M

abbrev p : M →ₗ[ℚ] ℚ := LinearMap.snd ℚ ℚ ℚ

abbrev U : Submodule ℚ M := LinearMap.ker p

theorem stable : X.IsStable U := scalar_isStable U

abbrev q : M →ₗ[ℚ] M ⧸ U := U.mkQ

/-- The quotient comodule supplied by the quotient construction. -/
def descended : RightComodule ℚ ℚ (M ⧸ U) := X.quotient U stable

/-- The ordinary first-isomorphism-theorem equivalence for the projection. -/
def e : (M ⧸ U) ≃ₗ[ℚ] ℚ :=
  LinearMap.quotKerEquivOfSurjective p LinearMap.snd_surjective

theorem first_axis_nonzero : ∃ m : M, m ∈ U ∧ m ≠ 0 := by
  refine ⟨(1, 0), rfl, ?_⟩
  intro h
  exact one_ne_zero (congrArg Prod.fst h)

theorem second_axis_not_mem : ((0, 1) : M) ∉ U := by
  intro h
  change (1 : ℚ) = 0 at h
  exact one_ne_zero h

@[simp] theorem e_apply (a b : ℚ) : e (q (a, b)) = b := rfl

@[simp] theorem e_symm_apply (b : ℚ) : e.symm b = q (0, b) := by
  change (p.quotKerEquivOfSurjective LinearMap.snd_surjective).symm (p (0, b)) =
    Submodule.Quotient.mk (0, b)
  exact p.quotKerEquivOfSurjective_symm_apply LinearMap.snd_surjective (0, b)

example : e (q (0, 1)) = 1 := e_apply 0 1

theorem quotient_nonzero : q (0, 1) ≠ 0 := by
  intro h
  have h' : (1 : ℚ) = 0 := by
    simpa only [e_apply, map_zero] using congrArg e h
  exact one_ne_zero h'

@[simp] theorem descended_coaction (a b : ℚ) :
    descended.coaction (q (a, b)) = q (a, b) ⊗ₜ[ℚ] (1 : ℚ) := by
  change (X.quotient U stable).coaction (Submodule.Quotient.mk (a, b)) = _
  rw [quotient_coaction_mkQ, scalar_coaction, LinearMap.rTensor_tmul]

example : (X.mkQ U stable).toLinearMap = q := mkQ_toLinearMap X U stable

example (m : M) : X.mkQ U stable m = q m := mkQ_apply X U stable m

example : Function.Surjective (X.mkQ U stable) := mkQ_surjective X U stable

example (m : M) :
    descended.coaction (X.mkQ U stable m) =
      (X.mkQ U stable).toLinearMap.rTensor ℚ (X.coaction m) :=
  (X.mkQ U stable).colinear_apply m

example (ρ : (M ⧸ U) →ₗ[ℚ] (M ⧸ U) ⊗[ℚ] ℚ)
    (hρ : ρ ∘ₗ q = q.rTensor ℚ ∘ₗ X.coaction) : ρ = descended.coaction :=
  quotient_coaction_unique X U stable ρ hρ

/-- The second projection, packaged only for this scalar-comodule model. -/
def projection : RightComoduleHom X (scalar ℚ ℚ) where
  toLinearMap := p
  colinear := by
    apply LinearMap.ext
    intro m
    simp only [LinearMap.comp_apply, scalar_coaction, LinearMap.rTensor_tmul]

/-- The factor obtained from the comodule quotient universal property. -/
def factor : RightComoduleHom descended (scalar ℚ ℚ) :=
  projection.liftQ U stable (le_refl _)

@[simp] theorem factor_apply (a b : ℚ) : factor (q (a, b)) = b :=
  projection.liftQ_mkQ U stable (le_refl _) (a, b)

theorem factor_toLinearMap : factor.toLinearMap = e.toLinearMap := by
  apply Submodule.linearMap_qext U
  apply LinearMap.ext
  rintro ⟨a, b⟩
  change factor (q (a, b)) = e (q (a, b))
  rw [factor_apply, e_apply]

example : factor.comp (X.mkQ U stable) = projection :=
  projection.liftQ_comp_mkQ U stable (le_refl _)

example (g : RightComoduleHom descended (scalar ℚ ℚ))
    (hg : g.comp (X.mkQ U stable) = projection) : g = factor :=
  projection.liftQ_unique U stable (le_refl _) g hg

example : ∃! g : RightComoduleHom descended (scalar ℚ ℚ),
    g.comp (X.mkQ U stable) = projection :=
  projection.existsUnique_liftQ U stable (le_refl _)

theorem e_colinear :
    (scalar ℚ ℚ).coaction ∘ₗ e.toLinearMap =
      e.toLinearMap.rTensor ℚ ∘ₗ descended.coaction := by
  rw [← factor_toLinearMap]
  exact factor.colinear

example : descended.coaction ∘ₗ e.symm.toLinearMap =
    e.symm.toLinearMap.rTensor ℚ ∘ₗ (scalar ℚ ℚ).coaction :=
  RightComoduleHom.colinear_symm e e_colinear

example : Function.Injective (X.mkQ ⊥ (scalar_isStable (⊥ : Submodule ℚ M))) := by
  intro m n h
  change (Submodule.Quotient.mk m : M ⧸ (⊥ : Submodule ℚ M)) =
    Submodule.Quotient.mk n at h
  have h' : m - n ∈ (⊥ : Submodule ℚ M) := (Submodule.Quotient.eq ⊥).mp h
  exact sub_eq_zero.mp (show m - n = 0 from h')

example (z : M ⧸ (⊤ : Submodule ℚ M)) :
    (X.quotient ⊤ (scalar_isStable (⊤ : Submodule ℚ M))).coaction z = 0 := by
  have hz : z = 0 := by
    obtain ⟨m, rfl⟩ := (⊤ : Submodule ℚ M).mkQ_surjective z
    exact (Submodule.Quotient.mk_eq_zero ⊤).2 (by trivial)
  rw [hz, map_zero]

end Coalgebra.RightComodule.QuotientTest
