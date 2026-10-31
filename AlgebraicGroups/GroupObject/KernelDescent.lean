/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupObject.KernelTorsor
public import Mathlib.CategoryTheory.EffectiveEpi.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Descent through a monoid homomorphism from a group object

A monoid homomorphism from a group object that is trivial on a given kernel square descends
uniquely along an effective epimorphism, provided its tensor square is an epimorphism. The
codomain of the epimorphism and the target of the descended morphism need only be monoid
objects. The kernel object requires no algebraic structure.

The underlying descended arrow is Mathlib's `EffectiveEpi.desc`; its monoid-homomorphism
certificate allows it to be bundled with `Mon.ofHom`. Compatibility is obtained from
`GrpObj.isPullback_kernel_mul`, by lifting arbitrary pairs of morphisms with equal composites.
The proofs use Mathlib's generalized-element monoid operations and its effective-epimorphism
factorization and uniqueness API.

## References

* J. S. Milne, *Algebraic Groups* (2017), (5.13), motivates the factorization theorem.
  The formulation here generalizes to Cartesian monoidal categories and arbitrary monoid
  targets; it does not construct a quotient.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj

open scoped CategoryTheory.MonObj

namespace CategoryTheory

private lemma isMonHom_of_comp_eq
    {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]
    {G H X : C} [MonObj G] [MonObj H] [MonObj X]
    (q : G ⟶ H) [IsMonHom q] [Epi (q ⊗ₘ q)]
    (f : H ⟶ X) (φ : G ⟶ X) [IsMonHom φ] (hf : q ≫ f = φ) :
    IsMonHom f := by
  constructor
  · calc
      η[H] ≫ f = (η[G] ≫ q) ≫ f := by rw [IsMonHom.one_hom q]
      _ = η[G] ≫ φ := by rw [Category.assoc, hf]
      _ = η[X] := IsMonHom.one_hom φ
  · apply (cancel_epi (q ⊗ₘ q)).1
    calc
      (q ⊗ₘ q) ≫ (μ[H] ≫ f) = μ[G] ≫ φ := by
        rw [← Category.assoc, ← IsMonHom.mul_hom q, Category.assoc, hf]
      _ = (φ ⊗ₘ φ) ≫ μ[X] := IsMonHom.mul_hom φ
      _ = (q ⊗ₘ q) ≫ ((f ⊗ₘ f) ≫ μ[X]) := by
        rw [← hf, ← MonoidalCategory.tensorHom_comp_tensorHom, Category.assoc]

namespace GrpObj

/-- A monoid homomorphism trivial on the given kernel identifies every pair of morphisms
identified by the given homomorphism. The test object carries no algebraic structure. -/
lemma comp_eq_of_trivial_kernel
    {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    {N G H X : C} [GrpObj G] [MonObj H] [MonObj X]
    (q : G ⟶ H) [IsMonHom q] (φ : G ⟶ X) [IsMonHom φ]
    (i : N ⟶ G) (hN : IsPullback i (toUnit N) q η[H])
    (hφ : i ≫ φ = toUnit N ≫ η[X])
    {T : C} (a b : T ⟶ G) (hab : a ≫ q = b ≫ q) :
    a ≫ φ = b ≫ φ := by
  have hk : ((i ⊗ₘ 𝟙 G) ≫ μ[G]) ≫ φ = snd N G ≫ φ := by
    rw [mul_eq_mul, comp_mul, tensorHom_fst, tensorHom_snd, Category.comp_id,
      mul_comp, Category.assoc, hφ, ← Category.assoc, comp_toUnit, ← Hom.one_def,
      _root_.one_mul]
  let hK := isPullback_kernel_mul i q hN
  calc
    a ≫ φ = hK.lift a b hab ≫ ((i ⊗ₘ 𝟙 G) ≫ μ[G]) ≫ φ := by
      rw [← Category.assoc, hK.lift_fst]
    _ = hK.lift a b hab ≫ snd N G ≫ φ := by rw [hk]
    _ = b ≫ φ := by rw [← Category.assoc, hK.lift_snd]

/-- The arrow chosen by `EffectiveEpi.desc` for a monoid homomorphism trivial on the given
kernel is a monoid homomorphism. Its underlying factorization and uniqueness are given by
`EffectiveEpi.fac` and `EffectiveEpi.uniq`. -/
theorem isMonHom_desc_of_trivial_kernel
    {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    {N G H X : C} [GrpObj G] [MonObj H] [MonObj X]
    (q : G ⟶ H) [IsMonHom q] [EffectiveEpi q] [Epi (q ⊗ₘ q)]
    (φ : G ⟶ X) [IsMonHom φ]
    (i : N ⟶ G) (hN : IsPullback i (toUnit N) q η[H])
    (hφ : i ≫ φ = toUnit N ≫ η[X]) :
    IsMonHom (EffectiveEpi.desc q φ (comp_eq_of_trivial_kernel q φ i hN hφ)) := by
  exact isMonHom_of_comp_eq q _ φ
    (EffectiveEpi.fac q φ (comp_eq_of_trivial_kernel q φ i hN hφ))

/-- A monoid homomorphism trivial on the given kernel factors uniquely through the given
effective epimorphism. This generalizes the factorization in Milne, *Algebraic Groups* (2017),
(5.13), to Cartesian monoidal categories and monoid targets: only the source needs inversion. -/
theorem existsUnique_monoidHom_of_trivial_kernel
    {C : Type u} [Category.{v} C] [c : CartesianMonoidalCategory C]
    {N G H X : C} [GrpObj G] [MonObj H] [MonObj X]
    (q : G ⟶ H) [IsMonHom q] [EffectiveEpi q] [Epi (q ⊗ₘ q)]
    (φ : G ⟶ X) [IsMonHom φ]
    (i : N ⟶ G) (hN : IsPullback i (toUnit N) q η[H])
    (hφ : i ≫ φ = toUnit N ≫ η[X]) :
    ∃! ψ : Mon.mk H ⟶ Mon.mk X, q ≫ ψ.hom = φ := by
  let h : ∀ {T : C} (a b : T ⟶ G), a ≫ q = b ≫ q → a ≫ φ = b ≫ φ :=
    comp_eq_of_trivial_kernel q φ i hN hφ
  let : IsMonHom (EffectiveEpi.desc q φ h) :=
    isMonHom_desc_of_trivial_kernel q φ i hN hφ
  refine ⟨Mon.ofHom (EffectiveEpi.desc q φ h), EffectiveEpi.fac q φ h, ?_⟩
  intro ψ hψ
  exact Mon.Hom.ext' (EffectiveEpi.uniq q φ h ψ.hom hψ)

/-- Triviality on the given kernel is equivalent to existence of a monoid-homomorphism factor
through the given effective epimorphism. -/
theorem trivial_kernel_iff_exists_monoidHom
    {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    {N G H X : C} [GrpObj G] [MonObj H] [MonObj X]
    (q : G ⟶ H) [IsMonHom q] [EffectiveEpi q] [Epi (q ⊗ₘ q)]
    (φ : G ⟶ X) [IsMonHom φ]
    (i : N ⟶ G) (hN : IsPullback i (toUnit N) q η[H]) :
    (i ≫ φ = toUnit N ≫ η[X]) ↔
      ∃ ψ : Mon.mk H ⟶ Mon.mk X, q ≫ ψ.hom = φ := by
  constructor
  · intro hφ
    obtain ⟨ψ, hψ, _⟩ := existsUnique_monoidHom_of_trivial_kernel q φ i hN hφ
    exact ⟨ψ, hψ⟩
  · rintro ⟨ψ, hψ⟩
    calc
      i ≫ φ = (i ≫ q) ≫ ψ.hom := by rw [Category.assoc, hψ]
      _ = (toUnit N ≫ η[H]) ≫ ψ.hom := by rw [hN.w]
      _ = toUnit N ≫ η[X] := by rw [Category.assoc, IsMonHom.one_hom ψ.hom]

end GrpObj

end CategoryTheory
