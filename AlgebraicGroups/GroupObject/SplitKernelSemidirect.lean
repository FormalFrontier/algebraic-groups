/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupObject.SplitKernelProduct
import Mathlib.Tactic.Group

public section

/-!
# Conjugation and the section-first multiplication of a split group-object kernel

The restricted conjugation is defined by the kernel pullback, without a group structure
on the kernel or a multiplicative section. When the kernel and section are group-object
homomorphisms, the underlying product trivialization has a twisted, not a direct-product,
multiplication law.
-/

set_option warningAsError true

open CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {N G Q : C} [GrpObj G] [GrpObj Q]
  (i : N ⟶ G) (q : G ⟶ Q) [IsMonHom q] (e : Q ⟶ G)
  (hN : IsPullback i (toUnit N) q η[Q]) (he : e ≫ q = 𝟙 Q)

include hN he

private theorem splitKernelConj_kernel :
    ((e ⊗ₘ i) ≫ GrpObj.conj G) ≫ q = toUnit (Q ⊗ N) ≫ η[Q] := by
  simp [GrpObj.conj, MonObj.mul_comp, MonObj.comp_mul, GrpObj.inv_comp,
    GrpObj.comp_inv, tensorHom_fst, tensorHom_snd, Category.assoc,
    he, hN.w, MonObj.one_eq_one]

/-- The canonical restriction of conjugation by a section to a genuine kernel. -/
noncomputable def splitKernelConj : Q ⊗ N ⟶ N :=
  hN.lift ((e ⊗ₘ i) ≫ GrpObj.conj G) (toUnit (Q ⊗ N))
    (splitKernelConj_kernel i q e hN he)

@[simp] theorem splitKernelConj_comp_i :
    splitKernelConj i q e hN he ≫ i = (e ⊗ₘ i) ≫ GrpObj.conj G := by
  simp [splitKernelConj]

@[simp] theorem splitKernelConj_comp_toUnit :
    splitKernelConj i q e hN he ≫ toUnit N = toUnit (Q ⊗ N) := by
  simp [splitKernelConj]

/-- The inclusion readback is natural in every test object, without any group structure on `N`. -/
theorem splitKernelConj_lift_comp_i {T : C} (a : T ⟶ Q) (n : T ⟶ N) :
    (lift a n ≫ splitKernelConj i q e hN he) ≫ i =
      (a ≫ e) * (n ≫ i) * (a ≫ e)⁻¹ := by
  simp [Category.assoc, GrpObj.lift_conj_eq_mul_mul_inv]

variable [GrpObj N] [IsMonHom i]

/-- Conjugation by a fixed section value preserves multiplication in the kernel.
This does not require the section to preserve multiplication. -/
theorem splitKernelConj_map_mul {T : C} (a : T ⟶ Q) (n n' : T ⟶ N) :
    lift a (n * n') ≫ splitKernelConj i q e hN he =
      (lift a n ≫ splitKernelConj i q e hN he) *
        (lift a n' ≫ splitKernelConj i q e hN he) := by
  apply hN.hom_ext
  · simp only [MonObj.mul_comp, splitKernelConj_lift_comp_i]
    group
  · simp

/-- Conjugation by a fixed section value preserves inverses without assuming `IsMonHom e`. -/
theorem splitKernelConj_map_inv {T : C} (a : T ⟶ Q) (n : T ⟶ N) :
    lift a n⁻¹ ≫ splitKernelConj i q e hN he =
      (lift a n ≫ splitKernelConj i q e hN he)⁻¹ := by
  apply hN.hom_ext
  · simp only [GrpObj.inv_comp, splitKernelConj_lift_comp_i]
    group
  · simp

variable [IsMonHom e]

omit [GrpObj N] [IsMonHom i] in
/-- The unit of `Q` acts identically on the kernel. -/
theorem splitKernelConj_one {T : C} (n : T ⟶ N) :
    lift (toUnit T ≫ η[Q]) n ≫ splitKernelConj i q e hN he = n := by
  apply hN.hom_ext
  · simp [Category.assoc, MonObj.one_eq_one]
  · simp

omit [GrpObj N] [IsMonHom i] in
/-- The restriction of conjugation is an internal left action on the kernel. -/
theorem splitKernelConj_mul {T : C} (a a' : T ⟶ Q) (n : T ⟶ N) :
    lift (a * a') n ≫ splitKernelConj i q e hN he =
      lift a (lift a' n ≫ splitKernelConj i q e hN he) ≫
        splitKernelConj i q e hN he := by
  apply hN.hom_ext
  · simp only [splitKernelConj_lift_comp_i, MonObj.mul_comp]
    group
  · simp

/-- The section-first product law on arbitrary test-object coordinates. -/
theorem splitKernelProductIso_mul_lift {T : C} (n n' : T ⟶ N) (a a' : T ⟶ Q) :
    lift ((lift (a'⁻¹) n ≫ splitKernelConj i q e hN he) * n') (a * a') ≫
        (splitKernelProductIso i q e hN he).hom =
      (lift n a ≫ (splitKernelProductIso i q e hN he).hom) *
        (lift n' a' ≫ (splitKernelProductIso i q e hN he).hom) := by
  simp [splitKernelProductIso_hom, MonObj.comp_mul,
    MonObj.mul_comp, GrpObj.inv_comp]
  group

/-- The twisted multiplication on the underlying `N ⊗ Q`, in section-first coordinates.
This is *not* the canonical direct-product multiplication on the tensor. -/
noncomputable def splitKernelTwistedMul : (N ⊗ Q) ⊗ (N ⊗ Q) ⟶ N ⊗ Q :=
  let first := fst (N ⊗ Q) (N ⊗ Q)
  let second := snd (N ⊗ Q) (N ⊗ Q)
  let n := first ≫ fst N Q
  let a := first ≫ snd N Q
  let n' := second ≫ fst N Q
  let a' := second ≫ snd N Q
  lift ((lift (a'⁻¹) n ≫ splitKernelConj i q e hN he) * n') (a * a')

/-- The morphism-level section-first twisted product diagram. -/
theorem splitKernelTwistedMul_comp_hom :
    splitKernelTwistedMul i q e hN he ≫
        (splitKernelProductIso i q e hN he).hom =
      ((splitKernelProductIso i q e hN he).hom ⊗ₘ
        (splitKernelProductIso i q e hN he).hom) ≫ μ[G] := by
  let first := fst (N ⊗ Q) (N ⊗ Q)
  let second := snd (N ⊗ Q) (N ⊗ Q)
  let n := first ≫ fst N Q
  let a := first ≫ snd N Q
  let n' := second ≫ fst N Q
  let a' := second ≫ snd N Q
  change lift ((lift (a'⁻¹) n ≫ splitKernelConj i q e hN he) * n')
      (a * a') ≫ (splitKernelProductIso i q e hN he).hom = _
  rw [splitKernelProductIso_mul_lift i q e hN he n n' a a']
  simp [n, n', a, a', first, second, Hom.mul_def, tensorHom_def]

end CategoryTheory
