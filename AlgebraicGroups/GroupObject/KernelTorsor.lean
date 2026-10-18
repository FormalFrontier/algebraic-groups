/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupObject.Hom
public import AlgebraicGroups.GroupObject.Translation
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Kernel fibres and torsors for group-object morphisms

This file relates monomorphisms from group objects to monoid objects to their fibres over
the unit, and begins the categorical core of smooth descent for extensions of group schemes.
The monomorphism criterion uses all ordinary test objects through their Hom groups. The
fibre object needs no group structure, and the target need only be a monoid object.

The source-group hypothesis is essential: addition `ℕ × ℕ → ℕ` has trivial zero fibre
but is not injective. For schemes, the fibre must be the scheme-theoretic pullback:
in characteristic `p`, Frobenius on `Gₐ` has kernel `αₚ`, which geometric points do not detect.

This file begins the categorical core of smooth descent for extensions of group schemes.
A chosen lift of a point of the target identifies the kernel with the fibre over that
point by right translation. This does not assert that a fibre without a supplied lift
already has a point.

## References

* J. S. Milne, *Algebraic Groups* (2017), Definition 1.61 and the proof of
  Proposition 1.62(a), for exact sequences and the fibre-translation argument
  in smooth extension descent. The kernel-pair theorem here is a generic
  pullback statement, not the smoothness implication.
* J. S. Milne, *Abelian Varieties*, version 2.0 (March 16, 2008), Chapter I,
  proof of Proposition 7.1, for the chosen-lift fibre-translation step.
  Scalar extension and the existence of a lift are separate from this step;
  the full proposition is not asserted here.
* Mathlib, `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`, for group laws on
  Hom sets, and the `IsPullback` cone and universal-property API;
  `Mathlib.Algebra.Group.Subgroup.Ker`, for the trivial-kernel injectivity criterion.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Category

universe v u

namespace CategoryTheory.GrpObj

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- A morphism from a group object to a monoid object is a monomorphism exactly when
the canonical map from the tensor unit to its fibre over the unit is an isomorphism. -/
theorem mono_iff_isIso_lift_one {N G Q : C} [GrpObj G] [MonObj Q]
    (i : N ⟶ G) (q : G ⟶ Q) [IsMonHom q]
    (hN : IsPullback i (toUnit N) q η[Q]) :
    Mono q ↔ IsIso (hN.lift η[G] (𝟙 (𝟙_ C))
      (by simpa only [Category.id_comp] using IsMonHom.one_hom q)) := by
  constructor
  · intro hq
    let : Mono q := hq
    have hunit : IsPullback η[G] (𝟙 (𝟙_ C)) q η[Q] :=
      IsPullback.of_vert_isIso_mono
        ⟨by simpa only [Category.id_comp] using IsMonHom.one_hom q⟩
    exact (IsLimit.nonempty_isLimit_iff_isIso_lift hN.isLimit).mp hunit.isLimit'
  · intro he
    let e := hN.lift η[G] (𝟙 (𝟙_ C))
      (by simpa only [Category.id_comp] using IsMonHom.one_hom q)
    let : IsIso e := he
    let hterminal : IsTerminal N := isTerminalTensorUnit.ofIso (asIso e)
    refine ⟨fun {T} a b hab ↦ ?_⟩
    have hinjective : Function.Injective (IsMonHom.monoidHom q T) := by
      apply (MonoidHom.ker_eq_bot_iff _).mp
      apply bot_unique
      intro f hf
      apply Subgroup.mem_bot.mpr
      have hfq : f ≫ q = toUnit T ≫ η[Q] := hf
      calc
        f = hN.lift f (toUnit T) hfq ≫ i := (hN.lift_fst _ _ _).symm
        _ = (toUnit T ≫ e) ≫ i :=
          congrArg (fun k : T ⟶ N ↦ k ≫ i) (hterminal.hom_ext _ _)
        _ = 1 := by simp only [Category.assoc, e, hN.lift_fst, Hom.one_def]
    exact hinjective hab

variable {N G Q : C} [GrpObj G] [GrpObj Q]

/-- If `N` is the kernel of a morphism of group objects `q : G ⟶ Q`, then multiplying
an element of `G` by an element of `N` exhibits `N × G` as `G ×_Q G`.
Compare the fibre-translation argument in Milne, *Algebraic Groups* (2017), proof of
Proposition 1.62(a); the conclusion here is only the categorical pullback. -/
theorem isPullback_kernel_mul (i : N ⟶ G) (q : G ⟶ Q) [IsMonHom q]
    (hN : IsPullback i (toUnit N) q η[Q]) :
    IsPullback ((i ⊗ₘ 𝟙 G) ≫ μ[G]) (snd N G) q q := by
  have hmul : (i ⊗ₘ 𝟙 G) ≫ μ[G] = (fst N G ≫ i) * snd N G := by
    rw [Hom.mul_def, ← lift_fst_comp_snd_comp]
    simp
  have hdiff (s : PullbackCone q q) : (s.fst * s.snd⁻¹) ≫ q = (toUnit s.pt) ≫ η[Q] := by
    change (s.fst * s.snd⁻¹) ≫ q = 1
    rw [MonObj.mul_comp, GrpObj.inv_comp, s.condition]
    exact mul_inv_cancel _
  let kernelLift (s : PullbackCone q q) : s.pt ⟶ N :=
    hN.lift (s.fst * s.snd⁻¹) (toUnit s.pt) (hdiff s)
  have kernelLift_i (s : PullbackCone q q) : kernelLift s ≫ i = s.fst * s.snd⁻¹ := by
    simp [kernelLift]
  have kernelLift_toUnit (s : PullbackCone q q) : kernelLift s ≫ toUnit N = toUnit s.pt := by
    simp [kernelLift]
  refine
    { w := ?_
      isLimit' := ⟨PullbackCone.IsLimit.mk _
        (fun s ↦ lift (kernelLift s) s.snd)
        ?_ ?_ ?_⟩ }
  · rw [hmul]
    rw [MonObj.mul_comp, Category.assoc, hN.w]
    simp [← Hom.one_def]
  · intro s
    rw [hmul]
    simp [MonObj.comp_mul, kernelLift_i]
  · intro s
    simp
  · intro s m hm₁ hm₂
    apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst]
      apply hN.hom_ext
      · rw [kernelLift_i]
        rw [hmul] at hm₁
        have hm₁' : (m ≫ fst N G ≫ i) * (m ≫ snd N G) = s.fst := by
          simpa [MonObj.comp_mul, Category.assoc] using hm₁
        rw [hm₂] at hm₁'
        simpa only [Category.assoc] using (eq_mul_inv_iff_mul_eq).2 hm₁'
      · rw [kernelLift_toUnit]
        simp
    · rw [lift_snd]
      exact hm₂

/-- A chosen lift `g` identifies the kernel of `q` with the fibre over `g ≫ q`
by right translation. The point `g` need not be a group-object homomorphism.
This is the chosen-lift translation step in Milne, *Abelian Varieties*, version 2.0
(March 16, 2008), Chapter I, proof of Proposition 7.1; it does not assert that fibres
without a supplied lift already have points, nor supply the scalar-extension or
existence arguments of that proposition. -/
theorem isPullback_kernel_mulRight (i : N ⟶ G) (q : G ⟶ Q) [IsMonHom q]
    (hN : IsPullback i (toUnit N) q η[Q]) (g : 𝟙_ C ⟶ G) :
    IsPullback (i ≫ (GrpObj.mulRight g).hom) (toUnit N) q (g ≫ q) := by
  have htranslation :
      IsPullback (GrpObj.mulRight g).hom q q (GrpObj.mulRight (g ≫ q)).hom := by
    apply IsPullback.of_horiz_isIso
    refine ⟨?_⟩
    rw [← Category.id_comp (GrpObj.mulRight g).hom, comp_mulRight_hom,
      MonObj.mul_comp, comp_mulRight_hom]
    simp only [Category.id_comp, Category.assoc]
  have hunit : η[Q] ≫ (GrpObj.mulRight (g ≫ q)).hom = g ≫ q := by
    rw [comp_mulRight_hom]
    simp [MonObj.one_eq_one]
  simpa only [hunit] using hN.paste_horiz htranslation

end CategoryTheory.GrpObj
