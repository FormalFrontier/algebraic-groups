/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupObject.Hom

/-!
# Kernel torsors for morphisms of group objects

This file begins the categorical core of smooth descent for extensions of group schemes.

## References

* J. S. Milne, *Algebraic Groups* (2017), Definition 1.61 and the proof of
  Proposition 1.62(a), for exact sequences and the fibre-translation argument
  in smooth extension descent. The theorem here is a generic kernel-pair
  pullback statement, not the smoothness implication.
* Mathlib, `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`, for group laws on
  Hom sets, and the `IsPullback` cone and universal-property API.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Category

universe v u

namespace CategoryTheory.GrpObj

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
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

end CategoryTheory.GrpObj
