/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupObject.FamilyTranslation
public import AlgebraicGroups.GroupObject.KernelTorsor

/-!
# Kernel pairs and first-fixed multiplication

For a homomorphism from a group object to a monoid object, multiplication identifies the
product of the group with its given canonical-unit fibre with a self-pullback. The first
coordinate is fixed: the two maps are `(x, n) ↦ x` and `(x, n) ↦ x * i(n)`.

The canonical comparison with any supplied self-pullback is the existing
`IsPullback.isoIsPullback`. Its inverse kernel coordinate is characterized through `i` by
`p₁⁻¹ * p₂`. This is an isomorphism in the underlying category, not in general an
isomorphism of coordinatewise group objects. Neither the fibre nor the self-pullback needs
a group-object structure.

The proof uses the family-translation and kernel-torsor API of Formal Frontier, together
with Mathlib's groups of generalized elements and pullback universal properties.

## References

* J. S. Milne, *Algebraic Groups* (2017), (5.8), for motivation.
-/

@[expose] public section

universe u v

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [c : CartesianMonoidalCategory C]

private lemma MonObj.tensorHom_id_comp_mul {N M : C} [MonObj M] (i : N ⟶ M) :
    (𝟙 M ⊗ₘ i) ≫ μ[M] = fst M N * (snd M N ≫ i) := by
  rw [MonObj.mul_eq_mul, MonObj.comp_mul, tensorHom_fst, tensorHom_snd,
    Category.comp_id]

namespace GrpObj

variable {N G Q : C} [GrpObj G] [MonObj Q]

/-- Multiplication on the right by the canonical-unit fibre gives a self-pullback with
first coordinate fixed. The target needs only a monoid structure: the inverse relation
is used in the source group and transported by the homomorphism. -/
theorem isPullback_mul_kernel (i : N ⟶ G) (q : G ⟶ Q) [IsMonHom q]
    (hN : IsPullback i (toUnit N) q η[Q]) :
    IsPullback (fst G N) ((𝟙 G ⊗ₘ i) ≫ μ[G]) q q := by
  have hi : i ≫ q = (1 : N ⟶ Q) := by
    simpa only [Hom.one_def] using hN.w
  have hw : fst G N ≫ q = ((𝟙 G ⊗ₘ i) ≫ μ[G]) ≫ q := by
    rw [MonObj.tensorHom_id_comp_mul, MonObj.mul_comp, Category.assoc, hi,
      MonObj.comp_one, mul_one]
  let d (s : PullbackCone q q) : s.pt ⟶ G :=
    lift s.fst s.snd ≫ (mulLeftFamily (𝟙 G)).inv ≫ snd G G
  have hd (s : PullbackCone q q) : d s = s.fst⁻¹ * s.snd := by
    dsimp only [d]
    simp only [mulLeftFamily_inv_snd, Category.comp_id, MonObj.comp_mul,
      GrpObj.comp_inv, lift_fst, lift_snd]
  have hdq (s : PullbackCone q q) : d s ≫ q = toUnit s.pt ≫ η[Q] := by
    rw [hd, MonObj.mul_comp, ← s.condition, ← MonObj.mul_comp,
      inv_mul_cancel, MonObj.one_comp, Hom.one_def]
  let k (s : PullbackCone q q) : s.pt ⟶ N :=
    hN.lift (d s) (toUnit s.pt) (hdq s)
  have hk (s : PullbackCone q q) : k s ≫ i = s.fst⁻¹ * s.snd := by
    dsimp only [k]
    rw [hN.lift_fst, hd]
  exact IsPullback.of_isLimit (PullbackCone.IsLimit.mk hw
    (fun s ↦ lift s.fst (k s))
    (fun s ↦ lift_fst _ _)
    (fun s ↦ by
      rw [MonObj.tensorHom_id_comp_mul, MonObj.comp_mul, lift_fst,
        ← Category.assoc, lift_snd, hk]
      simp only [← mul_assoc, mul_inv_cancel, one_mul])
    (fun s m hm₁ hm₂ ↦ by
      apply CartesianMonoidalCategory.hom_ext
      · simpa only [lift_fst] using hm₁
      · rw [lift_snd]
        apply hN.hom_ext
        · rw [hk]
          have hm₂' : s.fst * ((m ≫ snd G N) ≫ i) = s.snd := by
            simpa only [MonObj.tensorHom_id_comp_mul, MonObj.comp_mul,
              ← Category.assoc, hm₁] using hm₂
          calc
            (m ≫ snd G N) ≫ i =
                s.fst⁻¹ * (s.fst * ((m ≫ snd G N) ≫ i)) := by
              simp only [← mul_assoc, inv_mul_cancel, one_mul]
            _ = s.fst⁻¹ * s.snd := by rw [hm₂']
        · exact toUnit_unique _ _))

/-- In the canonical comparison with any given self-pullback, the inverse kernel
coordinate has image `p₁⁻¹ * p₂` in the original group object. -/
theorem isPullback_mul_kernel_isoIsPullback_inv_snd_comp
    (i : N ⟶ G) (q : G ⟶ Q) [IsMonHom q]
    (hN : IsPullback i (toUnit N) q η[Q])
    {P : C} {p₁ p₂ : P ⟶ G} (hP : IsPullback p₁ p₂ q q) :
    ((isPullback_mul_kernel i q hN).isoIsPullback G G hP).inv ≫ snd G N ≫ i =
      p₁⁻¹ * p₂ := by
  let e := (isPullback_mul_kernel i q hN).isoIsPullback G G hP
  have he₁ : e.inv ≫ fst G N = p₁ :=
    IsPullback.isoIsPullback_inv_fst G G (isPullback_mul_kernel i q hN) hP
  have he₂ : e.inv ≫ ((𝟙 G ⊗ₘ i) ≫ μ[G]) = p₂ :=
    IsPullback.isoIsPullback_inv_snd G G (isPullback_mul_kernel i q hN) hP
  rw [MonObj.tensorHom_id_comp_mul, MonObj.comp_mul, he₁] at he₂
  change e.inv ≫ snd G N ≫ i = p₁⁻¹ * p₂
  calc
    e.inv ≫ snd G N ≫ i = p₁⁻¹ * (p₁ * (e.inv ≫ snd G N ≫ i)) := by
      simp only [← mul_assoc, inv_mul_cancel, one_mul]
    _ = p₁⁻¹ * p₂ := by rw [he₂]

/-- The canonical comparisons with supplied self-pullbacks commute with a group
homomorphism, a compatible map of canonical-unit fibres, and a map of the two pullback
cones. No map of the target monoid objects is required once the two component equations
are supplied. -/
theorem isPullback_mul_kernel_isoIsPullback_hom_naturality
    (i : N ⟶ G) (q : G ⟶ Q) [IsMonHom q]
    (hN : IsPullback i (toUnit N) q η[Q])
    {N' G' Q' P P' : C} [GrpObj G'] [MonObj Q']
    (i' : N' ⟶ G') (q' : G' ⟶ Q') [IsMonHom q']
    (hN' : IsPullback i' (toUnit N') q' η[Q'])
    {p₁ p₂ : P ⟶ G} {p₁' p₂' : P' ⟶ G'}
    (hP : IsPullback p₁ p₂ q q) (hP' : IsPullback p₁' p₂' q' q')
    (a : G ⟶ G') [IsMonHom a] (n : N ⟶ N') (t : P ⟶ P')
    (hi : n ≫ i' = i ≫ a)
    (hp₁ : t ≫ p₁' = p₁ ≫ a) (hp₂ : t ≫ p₂' = p₂ ≫ a) :
    (a ⊗ₘ n) ≫ ((isPullback_mul_kernel i' q' hN').isoIsPullback G' G' hP').hom =
      ((isPullback_mul_kernel i q hN).isoIsPullback G G hP).hom ≫ t := by
  let e := (isPullback_mul_kernel i q hN).isoIsPullback G G hP
  let e' := (isPullback_mul_kernel i' q' hN').isoIsPullback G' G' hP'
  have he₁ : e.hom ≫ p₁ = fst G N :=
    IsPullback.isoIsPullback_hom_fst G G (isPullback_mul_kernel i q hN) hP
  have he₂ : e.hom ≫ p₂ = (𝟙 G ⊗ₘ i) ≫ μ[G] :=
    IsPullback.isoIsPullback_hom_snd G G (isPullback_mul_kernel i q hN) hP
  have he₁' : e'.hom ≫ p₁' = fst G' N' :=
    IsPullback.isoIsPullback_hom_fst G' G' (isPullback_mul_kernel i' q' hN') hP'
  have he₂' : e'.hom ≫ p₂' = (𝟙 G' ⊗ₘ i') ≫ μ[G'] :=
    IsPullback.isoIsPullback_hom_snd G' G' (isPullback_mul_kernel i' q' hN') hP'
  have hm : (a ⊗ₘ n) ≫ ((𝟙 G' ⊗ₘ i') ≫ μ[G']) =
      ((𝟙 G ⊗ₘ i) ≫ μ[G]) ≫ a := by
    simp only [MonObj.tensorHom_id_comp_mul, MonObj.comp_mul, MonObj.mul_comp]
    apply congrArg₂ (· * ·)
    · exact tensorHom_fst a n
    · simp only [← Category.assoc, tensorHom_snd]
      simpa only [Category.assoc] using
        congrArg (fun f : N ⟶ G' ↦ snd G N ≫ f) hi
  change (a ⊗ₘ n) ≫ e'.hom = e.hom ≫ t
  apply hP'.hom_ext
  · calc
      ((a ⊗ₘ n) ≫ e'.hom) ≫ p₁' = (a ⊗ₘ n) ≫ fst G' N' := by
        rw [Category.assoc, he₁']
      _ = fst G N ≫ a := tensorHom_fst a n
      _ = (e.hom ≫ p₁) ≫ a := by rw [he₁]
      _ = (e.hom ≫ t) ≫ p₁' := by simp only [Category.assoc, hp₁]
  · calc
      ((a ⊗ₘ n) ≫ e'.hom) ≫ p₂' =
          (a ⊗ₘ n) ≫ ((𝟙 G' ⊗ₘ i') ≫ μ[G']) := by
        rw [Category.assoc, he₂']
      _ = ((𝟙 G ⊗ₘ i) ≫ μ[G]) ≫ a := hm
      _ = (e.hom ≫ p₂) ≫ a := by rw [he₂]
      _ = (e.hom ≫ t) ≫ p₂' := by simp only [Category.assoc, hp₂]

end GrpObj

end CategoryTheory
