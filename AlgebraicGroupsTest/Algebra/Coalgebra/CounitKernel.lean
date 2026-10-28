/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.Hom
public import AlgebraicGroups.Algebra.Coalgebra.IdempotentIdeal
public import AlgebraicGroupsTest.Algebra.Coalgebra.FiniteSubcoalgebra
public import AlgebraicGroupsTest.Algebra.Coalgebra.GroupLikeHom
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Counit kernels and injectivity on concrete coalgebra morphisms

The rational two-point diagonal counit has a proper nonzero kernel and is not
injective. The natural two-point diagonal counit instead has zero kernel, but
still has collisions. Thus zero kernel does not characterize injectivity for
modules whose addition is only a commutative monoid.

An identity with the same selected zero-comultiplication data on its source and
target exercises the structure-only hypotheses. These selected data fail the
left counit law on every nontrivial module; this makes no assertion about other
coalgebra structures on that carrier. The identity on the idempotent ideal `(3)`
in `ZMod 6` gives a lawful nonfield example with injective, nonsurjective counit.
Finally, scalar-source maps to a diagonal natural coalgebra are injective even
though the target counit is not.

## References

The scalar and diagonal coalgebras, their counit readbacks, and bundled identity
and counit morphisms are supplied by Mathlib. The ideal and scalar-source map
examples reuse the public idempotent-ideal and group-like equivalence APIs.
-/

@[expose] public section



open scoped TensorProduct

universe u v

namespace CoalgebraTest.CounitKernel

private theorem scalar_counit_injective (R : Type u) [CommSemiring R] :
    Function.Injective (Coalgebra.counit (R := R) (A := R) : R → R) := by
  intro x y h
  simpa only [CommSemiring.counit_apply] using h

/-- The two-point rational counit has a specified nonzero kernel vector, a
vector outside its kernel, and a collision of distinct coordinate vectors. -/
theorem rational_two_point_counit :
    let f := Coalgebra.counitCoalgHom ℚ (Fin 2 →₀ ℚ)
    let ε := Coalgebra.counit (R := ℚ) (A := Fin 2 →₀ ℚ)
    let e₀ := Finsupp.single (0 : Fin 2) (1 : ℚ)
    let e₁ := Finsupp.single (1 : Fin 2) (1 : ℚ)
    let k := e₀ - e₁
    LinearMap.ker f.toLinearMap = LinearMap.ker ε ∧
      (Function.Injective f ↔ Function.Injective ε) ∧
      ε e₀ = 1 ∧ ε e₁ = 1 ∧ e₀ ≠ e₁ ∧ f e₀ = f e₁ ∧
      k ≠ 0 ∧ k ∈ LinearMap.ker ε ∧ k ∈ LinearMap.ker f.toLinearMap ∧
      e₀ ∉ LinearMap.ker ε ∧ LinearMap.ker ε ≠ ⊥ ∧ LinearMap.ker ε ≠ ⊤ ∧
      ¬ Function.Injective f ∧ ¬ Function.Injective ε := by
  let f := Coalgebra.counitCoalgHom ℚ (Fin 2 →₀ ℚ)
  let ε := Coalgebra.counit (R := ℚ) (A := Fin 2 →₀ ℚ)
  let e₀ := Finsupp.single (0 : Fin 2) (1 : ℚ)
  let e₁ := Finsupp.single (1 : Fin 2) (1 : ℚ)
  let k := e₀ - e₁
  have hker : LinearMap.ker f.toLinearMap = LinearMap.ker ε :=
    CoalgHomClass.ker_eq_ker_counit (R := ℚ) f (scalar_counit_injective ℚ)
  have hiff : Function.Injective f ↔ Function.Injective ε :=
    CoalgHomClass.injective_iff_counit_injective (R := ℚ) f
      (scalar_counit_injective ℚ)
  have h₀ : ε e₀ = 1 := by
    simp only [ε, e₀, Finsupp.counit_single, CommSemiring.counit_apply]
  have h₁ : ε e₁ = 1 := by
    simp only [ε, e₁, Finsupp.counit_single, CommSemiring.counit_apply]
  have hne : e₀ ≠ e₁ := by
    intro h
    have hc := congrArg (fun x : Fin 2 →₀ ℚ => x 0) h
    simp [e₀, e₁] at hc
  have hsame : f e₀ = f e₁ := by
    simpa only [f, Coalgebra.counitCoalgHom_apply] using h₀.trans h₁.symm
  have hk : k ≠ 0 := by
    intro h
    have hc := congrArg (fun x : Fin 2 →₀ ℚ => x 0) h
    simp [k, e₀, e₁] at hc
  have hkε : k ∈ LinearMap.ker ε := by
    rw [LinearMap.mem_ker, show k = e₀ - e₁ from rfl, map_sub, h₀, h₁, sub_self]
  have hkf : k ∈ LinearMap.ker f.toLinearMap := by
    rw [hker]
    exact hkε
  have hout : e₀ ∉ LinearMap.ker ε := by
    simpa only [LinearMap.mem_ker, h₀] using (one_ne_zero : (1 : ℚ) ≠ 0)
  have hbot : LinearMap.ker ε ≠ ⊥ := by
    intro h
    exact hk ((Submodule.mem_bot ℚ).mp (h ▸ hkε))
  have htop : LinearMap.ker ε ≠ ⊤ := by
    intro h
    apply hout
    rw [h]
    exact Submodule.mem_top
  exact ⟨hker, hiff, h₀, h₁, hne, hsame, hk, hkε, hkf, hout, hbot, htop,
    fun hi => hne (hi hsame), fun hi => hne (hi (h₀.trans h₁.symm))⟩

/-- The natural diagonal counit is the sum of the two coefficients, as follows
from its values on singles and the finite single-vector decomposition. -/
theorem natural_two_point_counit_apply (x : Fin 2 →₀ ℕ) :
    Coalgebra.counit (R := ℕ) x = ∑ i : Fin 2, x i := by
  calc
    Coalgebra.counit (R := ℕ) x =
        Coalgebra.counit (R := ℕ) (∑ i : Fin 2, Finsupp.single i (x i)) :=
      congrArg (Coalgebra.counit (R := ℕ) (A := Fin 2 →₀ ℕ))
        (Finsupp.univ_sum_single x).symm
    _ = ∑ i : Fin 2, x i := by
      simp only [map_sum, Finsupp.counit_single, CommSemiring.counit_apply]

/-- The natural two-point counit has zero kernel but is not injective. Both
kernel equality and the injectivity equivalence apply to its bundled counit map. -/
theorem natural_two_point_counit :
    let f := Coalgebra.counitCoalgHom ℕ (Fin 2 →₀ ℕ)
    let ε := Coalgebra.counit (R := ℕ) (A := Fin 2 →₀ ℕ)
    let e₀ := Finsupp.single (0 : Fin 2) (1 : ℕ)
    let e₁ := Finsupp.single (1 : Fin 2) (1 : ℕ)
    LinearMap.ker f.toLinearMap = LinearMap.ker ε ∧
      LinearMap.ker ε = ⊥ ∧ LinearMap.ker f.toLinearMap = ⊥ ∧
      (Function.Injective f ↔ Function.Injective ε) ∧
      e₀ ≠ e₁ ∧ ε e₀ = 1 ∧ ε e₁ = 1 ∧ f e₀ = f e₁ ∧
      ¬ Function.Injective f ∧ ¬ Function.Injective ε := by
  let f := Coalgebra.counitCoalgHom ℕ (Fin 2 →₀ ℕ)
  let ε := Coalgebra.counit (R := ℕ) (A := Fin 2 →₀ ℕ)
  let e₀ := Finsupp.single (0 : Fin 2) (1 : ℕ)
  let e₁ := Finsupp.single (1 : Fin 2) (1 : ℕ)
  have hker : LinearMap.ker f.toLinearMap = LinearMap.ker ε :=
    CoalgHomClass.ker_eq_ker_counit (R := ℕ) f (scalar_counit_injective ℕ)
  have hiff : Function.Injective f ↔ Function.Injective ε :=
    CoalgHomClass.injective_iff_counit_injective (R := ℕ) f
      (scalar_counit_injective ℕ)
  have hbot : LinearMap.ker ε = ⊥ := by
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    have hsum : ∑ i : Fin 2, x i = 0 := by
      simpa only [ε, natural_two_point_counit_apply] using hx
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Nat.zero_le (x i))).mp hsum
    ext i
    exact hz i (Finset.mem_univ i)
  have h₀ : ε e₀ = 1 := by
    simp only [ε, e₀, Finsupp.counit_single, CommSemiring.counit_apply]
  have h₁ : ε e₁ = 1 := by
    simp only [ε, e₁, Finsupp.counit_single, CommSemiring.counit_apply]
  have hne : e₀ ≠ e₁ := by
    intro h
    have hc := congrArg (fun x : Fin 2 →₀ ℕ => x 0) h
    simp [e₀, e₁] at hc
  have hsame : f e₀ = f e₁ := by
    simpa only [f, Coalgebra.counitCoalgHom_apply] using h₀.trans h₁.symm
  exact ⟨hker, hbot, hker.trans hbot, hiff, hne, h₀, h₁, hsame,
    fun hi => hne (hi hsame), fun hi => hne (hi (h₀.trans h₁.symm))⟩

section ZeroComultiplication

variable {R : Type u} {B : Type v}
variable [CommSemiring R] [AddCommMonoid B] [Module R B]

/-- The identity for the same chosen zero-comultiplication data on both sides
has kernel equal to the kernel of the specified injective counit. No coalgebra
laws on either side are assumed. -/
theorem zero_comul_identity (e : B →ₗ[R] R) (he : Function.Injective e) :
    let c : CoalgebraStruct R B := { comul := 0, counit := e }
    let g := @CoalgHom.id R B _ _ _ c
    LinearMap.ker g.toLinearMap = LinearMap.ker e ∧
      LinearMap.ker e = ⊥ ∧ Function.Injective g ∧
      (Function.Injective g ↔ Function.Injective e) := by
  let : CoalgebraStruct R B := { comul := 0, counit := e }
  let g := CoalgHom.id R B
  have hε : Function.Injective (Coalgebra.counit (R := R) (A := B) : B → R) := he
  have hker : LinearMap.ker g.toLinearMap = LinearMap.ker e :=
    CoalgHomClass.ker_eq_ker_counit (R := R) g hε
  have hiff : Function.Injective g ↔ Function.Injective e :=
    CoalgHomClass.injective_iff_counit_injective (R := R) g hε
  have hg : Function.Injective g :=
    CoalgHomClass.injective_of_counit_injective (R := R) g hε
  have hbot : LinearMap.ker e = ⊥ := by
    rw [← hker]
    simp only [g, CoalgHom.toLinearMap_eq_ofClass, CoalgHom.id_toLinearMap, LinearMap.ker_id]
  exact ⟨hker, hbot, hg, hiff⟩

/-- The chosen zero-comultiplication data fail the left counit law on a
nontrivial module. The left tensor unitor detects the nonzero pure tensor. -/
theorem zero_comul_left_counit_law_failure [Nontrivial B] (e : B →ₗ[R] R) :
    let c : CoalgebraStruct R B := { comul := 0, counit := e }
    c.counit.rTensor B ∘ₗ c.comul ≠ TensorProduct.mk R R B 1 := by
  dsimp only
  obtain ⟨b, hb⟩ := exists_ne (0 : B)
  intro h
  have ht : (0 : R ⊗[R] B) = (1 : R) ⊗ₜ[R] b := by
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply, map_zero,
      TensorProduct.mk_apply] using LinearMap.congr_fun h b
  have hc := congrArg (TensorProduct.lid R B) ht
  exact hb (by simpa only [map_zero, TensorProduct.lid_tmul, one_smul] using hc.symm)

end ZeroComultiplication

section IdempotentIdeal

attribute [local instance] CoalgebraExamples.zmodSixIdealCoalgebra

/-- The identity on the projective, nonfree idempotent ideal `(3)` in `ZMod 6`
is injective. Its counit is injective with zero kernel but has proper image. -/
theorem span_three_identity :
    let I := Ideal.span ({(3 : ZMod 6)} : Set (ZMod 6))
    let f := CoalgHom.id (ZMod 6) I
    let ε := Coalgebra.counit (R := ZMod 6) (A := I)
    Function.Injective ε ∧ LinearMap.ker f.toLinearMap = LinearMap.ker ε ∧
      LinearMap.ker ε = ⊥ ∧ Function.Injective f ∧
      (Function.Injective f ↔ Function.Injective ε) ∧
      LinearMap.range ε ≠ ⊤ ∧ Module.Projective (ZMod 6) I ∧
      ¬ Module.Free (ZMod 6) I := by
  let I := Ideal.span ({(3 : ZMod 6)} : Set (ZMod 6))
  let f := CoalgHom.id (ZMod 6) I
  let ε := Coalgebra.counit (R := ZMod 6) (A := I)
  have hε : Function.Injective ε := by
    rw [show ε = I.subtype from
      CoalgebraExamples.zmod_six_three_idempotent.coalgebraSpan_counit]
    exact Subtype.val_injective
  have hker : LinearMap.ker f.toLinearMap = LinearMap.ker ε :=
    CoalgHomClass.ker_eq_ker_counit (R := ZMod 6) f hε
  have hiff : Function.Injective f ↔ Function.Injective ε :=
    CoalgHomClass.injective_iff_counit_injective (R := ZMod 6) f hε
  have hf : Function.Injective f :=
    CoalgHomClass.injective_of_counit_injective (R := ZMod 6) f hε
  exact ⟨hε, hker, LinearMap.ker_eq_bot_of_injective hε, hf, hiff,
    CoalgebraExamples.zmod_six_ideal_counit_range_ne_top,
    CoalgebraExamples.zmod_six_ideal_projective_not_free⟩

end IdempotentIdeal

/-- Two distinct scalar-source maps to a diagonal natural coalgebra are
injective by source-counit injectivity, although the target counit has a
collision between their distinct values at one. Lifted labels allow an
independent target universe. -/
theorem exists_injective_scalar_maps_noninjective_target_counit :
    ∃ f₀ f₁ : ℕ →ₗc[ℕ] (ULift.{v} (Fin 2) →₀ ℕ),
      Function.Injective f₀ ∧ Function.Injective f₁ ∧ f₀ ≠ f₁ ∧
      f₀ 1 ≠ f₁ 1 ∧
      Coalgebra.counit (R := ℕ) (f₀ 1) = Coalgebra.counit (R := ℕ) (f₁ 1) ∧
      ¬ Function.Injective
        (Coalgebra.counit (R := ℕ) (A := ULift.{v} (Fin 2) →₀ ℕ) :
          (ULift.{v} (Fin 2) →₀ ℕ) → ℕ) := by
  obtain ⟨g₀, g₁, h₀, h₁, hne, _⟩ :=
    Finsupp.exists_distinct_coalgHomEquiv_nat_ulift_fin_two.{v}
  have hi₀ : Function.Injective (GroupLike.coalgHomEquiv g₀) :=
    CoalgHomClass.injective_of_counit_injective (R := ℕ)
      (GroupLike.coalgHomEquiv g₀) (scalar_counit_injective ℕ)
  have hi₁ : Function.Injective (GroupLike.coalgHomEquiv g₁) :=
    CoalgHomClass.injective_of_counit_injective (R := ℕ)
      (GroupLike.coalgHomEquiv g₁) (scalar_counit_injective ℕ)
  have hpoints : GroupLike.coalgHomEquiv g₀ 1 ≠ GroupLike.coalgHomEquiv g₁ 1 := by
    rw [h₀, h₁]
    intro h
    have hc := congrArg
      (fun x : ULift.{v} (Fin 2) →₀ ℕ => x (ULift.up (0 : Fin 2))) h
    simp at hc
  have hcounit : Coalgebra.counit (R := ℕ) (GroupLike.coalgHomEquiv g₀ 1) =
      Coalgebra.counit (R := ℕ) (GroupLike.coalgHomEquiv g₁ 1) := by
    rw [h₀, h₁]
    simp only [Finsupp.counit_single, CommSemiring.counit_apply]
  exact ⟨GroupLike.coalgHomEquiv g₀, GroupLike.coalgHomEquiv g₁,
    hi₀, hi₁, hne, hpoints, hcounit, fun hi => hpoints (hi hcounit)⟩

end CoalgebraTest.CounitKernel
