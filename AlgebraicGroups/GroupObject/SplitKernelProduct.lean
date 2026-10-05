/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

public section

/-!
# Splitting the underlying object of a group-object kernel

A section of a group-object morphism trivializes its kernel pullback as an underlying
cartesian product. The section need not be multiplicative; this is not a group-object
isomorphism.

## References

* J. S. Milne, *Algebraic Groups* (2017), Definition 1.61, for kernels and
  exact sequences of algebraic groups. The section-first underlying-object
  construction here applies more generally and does not require a group
  structure on the kernel or a multiplicative section.
* Mathlib, `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp` for group laws on
  Hom sets and `Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs`
  for the kernel-pullback lift and its universal property.
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

include he

private theorem normalization_comp {T : C} (f : T ⟶ G) :
    ((f ≫ q ≫ e)⁻¹ * f) ≫ q = toUnit T ≫ η[Q] := by
  rw [MonObj.mul_comp, GrpObj.inv_comp]
  simp [Category.assoc, he, MonObj.one_eq_one]

/-- The unique kernel component of the section-normalized element. -/
noncomputable def splitKernelRemainder : G ⟶ N :=
  hN.lift ((q ≫ e)⁻¹ * 𝟙 G) (toUnit G)
    (by simpa using normalization_comp q e he (𝟙 G))

@[simp] theorem splitKernelRemainder_comp_i :
    splitKernelRemainder i q e hN he ≫ i = (q ≫ e)⁻¹ * 𝟙 G := by
  simp [splitKernelRemainder]

@[simp] theorem splitKernelRemainder_comp_toUnit :
    splitKernelRemainder i q e hN he ≫ toUnit N = toUnit G := by
  simp [splitKernelRemainder]

include hN

private theorem splitKernelForward_comp_q :
    ((snd N Q ≫ e) * (fst N Q ≫ i)) ≫ q = snd N Q := by
  simp [MonObj.mul_comp, Category.assoc, he, hN.w, MonObj.one_eq_one]

/-- The section-first multiplication gives an isomorphism of underlying objects.
Compare the exact-sequence context of Milne, *Algebraic Groups* (2017),
Definition 1.61; the section here need not be multiplicative, and the conclusion
is not an isomorphism of group objects. -/
noncomputable def splitKernelProductIso : N ⊗ Q ≅ G where
  hom := (snd N Q ≫ e) * (fst N Q ≫ i)
  inv := lift (splitKernelRemainder i q e hN he) q
  hom_inv_id := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst]
      apply hN.hom_ext
      · rw [Category.assoc, splitKernelRemainder_comp_i, MonObj.comp_mul,
          GrpObj.comp_inv]
        rw [← Category.assoc, splitKernelForward_comp_q i q e hN he]
        simp
      · simp
    · simpa [Category.assoc] using splitKernelForward_comp_q i q e hN he
  inv_hom_id := by
    simp [MonObj.comp_mul, splitKernelRemainder_comp_i]

/-- The forward map multiplies the section on the left of the kernel inclusion. -/
theorem splitKernelProductIso_hom :
    (splitKernelProductIso i q e hN he).hom =
      (snd N Q ≫ e) * (fst N Q ≫ i) := by
  simp [splitKernelProductIso]

@[simp] theorem splitKernelProductIso_hom_comp_q :
    (splitKernelProductIso i q e hN he).hom ≫ q = snd N Q := by
  exact splitKernelForward_comp_q i q e hN he

@[simp] theorem splitKernelProductIso_inv_comp_fst :
    (splitKernelProductIso i q e hN he).inv ≫ fst N Q =
      splitKernelRemainder i q e hN he := by
  simp [splitKernelProductIso]

@[simp] theorem splitKernelProductIso_inv_comp_snd :
    (splitKernelProductIso i q e hN he).inv ≫ snd N Q = q := by
  simp [splitKernelProductIso]

end CategoryTheory
