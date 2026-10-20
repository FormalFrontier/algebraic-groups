/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.RightComodule
public import Mathlib.RingTheory.Coalgebra.MonoidAlgebra
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Stable and nonstable spans in a regular monoid-algebra comodule

For the regular right comodule on `MonoidAlgebra ℕ (Multiplicative ℤ)`, the
span of `e₀` is stable, while the span of `e₀ + e₁` is not. Both spans are
nonzero and proper. First-factor coefficient slices obstruct the original
right-order stability image directly. Second-factor slices obstruct identity
evaluation in the scalar-extension image at `1 ⊗ (e₀ + e₁)`.

The examples apply both evaluation criteria, the identity one-tensor law and
the independently universe-polymorphic forward preservation theorem. The zero
and whole submodules give the boundary cases. No subtype coaction is chosen.

## References

* M. E. Sweedler, *Hopf Algebras*, W. A. Benjamin, 1969, for comodules.
* Mathlib's monoid-algebra coalgebra, coefficient linear equivalence,
  scalar-extension image and tensor-product APIs.
-/

@[expose] public section

universe uA

open scoped TensorProduct

noncomputable section

namespace Coalgebra.RightComodule

namespace NatMonoidAlgebraExamples

private abbrev C := MonoidAlgebra ℕ (Multiplicative ℤ)

private def regularComodule : Coalgebra.RightComodule ℕ C C :=
  Coalgebra.RightComodule.regular ℕ C

private def e (i : ℤ) : C :=
  MonoidAlgebra.single (Multiplicative.ofAdd i) 1

private def q (i : ℤ) : C →ₗ[ℕ] ℕ :=
  (Finsupp.lapply (Multiplicative.ofAdd i)).comp
    (MonoidAlgebra.coeffLinearEquiv ℕ).toLinearMap

private def U : Submodule ℕ C := Submodule.span ℕ {e 0}
private def V : Submodule ℕ C := Submodule.span ℕ {e 0 + e 1}

private theorem q_e (i j : ℤ) : q i (e j) = if i = j then 1 else 0 := by
  change (Finsupp.single (Multiplicative.ofAdd j) (1 : ℕ))
    (Multiplicative.ofAdd i) = if i = j then 1 else 0
  by_cases h : i = j
  · subst j
    simp
  · have hji : Multiplicative.ofAdd j ≠ Multiplicative.ofAdd i := by
      intro hij
      exact h (congrArg Multiplicative.toAdd hij).symm
    simp [Finsupp.single_apply, h, hji]

private theorem coaction_e (i : ℤ) :
    regularComodule.coaction (e i) = e i ⊗ₜ[ℕ] e i := by
  change Coalgebra.comul (R := ℕ) (e i) = e i ⊗ₜ[ℕ] e i
  simp [e, MonoidAlgebra.comul_single, CommSemiring.comul_apply,
    TensorProduct.map_tmul, MonoidAlgebra.lsingle_apply]

private theorem e_zero_mem_U : e 0 ∈ U :=
  Submodule.mem_span_singleton_self _

private theorem sum_mem_V : e 0 + e 1 ∈ V :=
  Submodule.mem_span_singleton_self _

private theorem e_zero_ne_zero : e 0 ≠ 0 := by
  intro h
  have hq := congrArg (q 0) h
  simpa [q_e] using hq

private theorem sum_ne_zero : e 0 + e 1 ≠ 0 := by
  intro h
  have hq := congrArg (q 0) h
  simpa [map_add, q_e] using hq

private theorem e_zero_ne_one : e 0 ≠ e 1 := by
  intro h
  have hq := congrArg (q 0) h
  simpa [q_e] using hq

private theorem q_one_zero_on_U {x : C} (hx : x ∈ U) : q 1 x = 0 := by
  obtain ⟨n, rfl⟩ := Submodule.mem_span_singleton.mp hx
  rw [(q 1).map_smul]
  simp [q_e]

private theorem q_zero_eq_one_on_V {x : C} (hx : x ∈ V) :
    q 0 x = q 1 x := by
  obtain ⟨n, rfl⟩ := Submodule.mem_span_singleton.mp hx
  rw [(q 0).map_smul, (q 1).map_smul]
  simp [map_add, q_e]

private theorem q_restrict_V : (q 0).comp V.subtype = (q 1).comp V.subtype := by
  ext x
  exact q_zero_eq_one_on_V x.property

private theorem U_ne_bot : U ≠ ⊥ := by
  intro h
  have hx : e 0 ∈ (⊥ : Submodule ℕ C) := h ▸ e_zero_mem_U
  exact e_zero_ne_zero (by simpa using hx)

private theorem U_ne_top : U ≠ ⊤ := by
  intro h
  have hx : e 1 ∈ U := h.symm ▸ (Submodule.mem_top : e 1 ∈ (⊤ : Submodule ℕ C))
  have hq := q_one_zero_on_U hx
  simpa [q_e] using hq

private theorem e_zero_not_mem_V : e 0 ∉ V := by
  intro hx
  have hq := q_zero_eq_one_on_V hx
  simpa [q_e] using hq

private theorem V_ne_bot : V ≠ ⊥ := by
  intro h
  have hx : e 0 + e 1 ∈ (⊥ : Submodule ℕ C) := h ▸ sum_mem_V
  exact sum_ne_zero (by simpa using hx)

private theorem V_ne_top : V ≠ ⊤ := by
  intro h
  exact e_zero_not_mem_V
    (h.symm ▸ (Submodule.mem_top : e 0 ∈ (⊤ : Submodule ℕ C)))

/-- Direct image witness for the original right-order coaction. -/
private theorem U_isStable : regularComodule.IsStable U := by
  intro x hx
  obtain ⟨n, rfl⟩ := Submodule.mem_span_singleton.mp hx
  refine ⟨n • ((⟨e 0, e_zero_mem_U⟩ : U) ⊗ₜ[ℕ] e 0), ?_⟩
  rw [(U.subtype.rTensor C).map_smul, regularComodule.coaction.map_smul]
  exact congrArg (fun t : C ⊗[ℕ] C => n • t) (coaction_e 0).symm

/-- First-factor slice of the original right-order coaction. -/
private def firstSlice (i : ℤ) : C ⊗[ℕ] C →ₗ[ℕ] C :=
  (TensorProduct.lid ℕ C).toLinearMap.comp ((q i).rTensor C)

private theorem firstSlice_tmul (i : ℤ) (x y : C) :
    firstSlice i (x ⊗ₜ[ℕ] y) = q i x • y := rfl

private theorem first_slices_equal_on_V_image (t : V ⊗[ℕ] C) :
    firstSlice 0 (V.subtype.rTensor C t) =
      firstSlice 1 (V.subtype.rTensor C t) := by
  induction t using TensorProduct.inductionOn with
  | tmul v c =>
      simp only [LinearMap.rTensor_tmul, firstSlice_tmul]
      exact congrArg (fun n : ℕ => n • c)
        (LinearMap.congr_fun q_restrict_V v)
  | add x y hx hy =>
      simpa only [map_add] using congrArg₂ (fun a b : C => a + b) hx hy

private theorem firstSlice_zero_coaction_sum :
    firstSlice 0 (regularComodule.coaction (e 0 + e 1)) = e 0 := by
  simp only [map_add, coaction_e, firstSlice_tmul]
  simp [q_e]

private theorem firstSlice_one_coaction_sum :
    firstSlice 1 (regularComodule.coaction (e 0 + e 1)) = e 1 := by
  simp only [map_add, coaction_e, firstSlice_tmul]
  simp [q_e]

/-- First-factor coefficient slices separate the coaction from the inclusion image. -/
private theorem V_not_isStable : ¬ regularComodule.IsStable V := by
  intro h
  obtain ⟨t, ht⟩ := h.coaction_mem_range (e 0 + e 1) sum_mem_V
  have hs := first_slices_equal_on_V_image t
  rw [ht] at hs
  apply e_zero_ne_one
  calc
    e 0 = firstSlice 0 (regularComodule.coaction (e 0 + e 1)) :=
      firstSlice_zero_coaction_sum.symm
    _ = firstSlice 1 (regularComodule.coaction (e 0 + e 1)) := hs
    _ = e 1 := firstSlice_one_coaction_sum

/-- Second-factor slice in the scalar-extension order. -/
private def secondSlice (i : ℤ) : C ⊗[ℕ] C →ₗ[ℕ] C :=
  (TensorProduct.rid ℕ C).toLinearMap.comp ((q i).lTensor C)

private theorem secondSlice_tmul (i : ℤ) (x y : C) :
    secondSlice i (x ⊗ₜ[ℕ] y) = q i y • x := rfl

private theorem second_slices_equal_on_V_baseChange {z : C ⊗[ℕ] C}
    (hz : z ∈ V.baseChange C) : secondSlice 0 z = secondSlice 1 z := by
  obtain ⟨t, rfl⟩ := hz
  induction t using TensorProduct.inductionOn with
  | tmul c v =>
      simp only [LinearMap.baseChange_tmul, secondSlice_tmul]
      exact congrArg (fun n : ℕ => n • c)
        (LinearMap.congr_fun q_restrict_V v)
  | add x y hx hy =>
      simpa only [map_add] using congrArg₂ (fun a b : C => a + b) hx hy

private theorem diagonal_not_mem_V_baseChange :
    e 0 ⊗ₜ[ℕ] e 0 + e 1 ⊗ₜ[ℕ] e 1 ∉ V.baseChange C := by
  intro hz
  have hs := second_slices_equal_on_V_baseChange hz
  apply e_zero_ne_one
  simpa [map_add, secondSlice_tmul, q_e] using hs

private theorem id_evaluation_sum :
    LinearMap.liftBaseChange C
      ((TensorProduct.map (AlgHom.toLinearMap (AlgHom.id ℕ C))
          (LinearMap.id : C →ₗ[ℕ] C)).comp
        ((TensorProduct.comm ℕ C C).toLinearMap.comp regularComodule.coaction))
      ((1 : C) ⊗ₜ[ℕ] (e 0 + e 1)) =
        e 0 ⊗ₜ[ℕ] e 0 + e 1 ⊗ₜ[ℕ] e 1 := by
  rw [regularComodule.id_evaluation_one_tmul]
  simp [map_add, coaction_e, TensorProduct.comm_tmul]

/-- Identity evaluation leaves the scalar-extension image at a specified member. -/
private theorem V_id_counterexample :
    ∃ z ∈ V.baseChange C,
      LinearMap.liftBaseChange C
        ((TensorProduct.map (AlgHom.toLinearMap (AlgHom.id ℕ C))
            (LinearMap.id : C →ₗ[ℕ] C)).comp
          ((TensorProduct.comm ℕ C C).toLinearMap.comp regularComodule.coaction)) z
        ∉ V.baseChange C := by
  refine ⟨(1 : C) ⊗ₜ[ℕ] (e 0 + e 1),
    Submodule.tmul_mem_baseChange_of_mem 1 sum_mem_V, ?_⟩
  rw [id_evaluation_sum]
  exact diagonal_not_mem_V_baseChange

/-- The two spans are nonzero and proper, with opposite stability behavior. -/
private theorem stable_and_nonstable_spans : U ≠ ⊥ ∧ U ≠ ⊤ ∧ regularComodule.IsStable U ∧
    V ≠ ⊥ ∧ V ≠ ⊤ ∧ ¬ regularComodule.IsStable V :=
  ⟨U_ne_bot, U_ne_top, U_isStable, V_ne_bot, V_ne_top, V_not_isStable⟩

/-- The original stock image-preservation predicate, with only the target algebra
varying. The anonymous expression is elaborated over an abstract scalar first;
its source algebra, full coalgebra, module and comodule are then fixed to the
original model, before any specialization of the target to `C`. -/
private def originalTargetPredicate (W : Submodule ℕ C)
    (A : Type uA) [CommSemiring A] (β : Algebra ℕ A) : Prop :=
  (fun (R₀ C₀ M₀ : Type) [instR₀ : CommSemiring R₀] [instC₀ : CommSemiring C₀]
      [sourceAlgebra : Algebra R₀ C₀] [sourceCoalgebra : Coalgebra R₀ C₀]
      [instM₀ : AddCommMonoid M₀] [sourceModule : Module R₀ M₀]
      (X : Coalgebra.RightComodule R₀ C₀ M₀) (W₀ : Submodule R₀ M₀)
      (B : Type uA) [instB : CommSemiring B] [targetAlgebra : Algebra R₀ B] =>
    ∀ (α : C₀ →ₐ[R₀] B), ∀ z ∈ W₀.baseChange B,
      LinearMap.liftBaseChange B
        ((TensorProduct.map (AlgHom.toLinearMap α)
            (LinearMap.id : M₀ →ₗ[R₀] M₀)).comp
          ((TensorProduct.comm R₀ M₀ C₀).toLinearMap.comp X.coaction)) z
        ∈ W₀.baseChange B)
    ℕ C C (instR₀ := inferInstance) (instC₀ := inferInstance)
      (sourceAlgebra := (MonoidAlgebra.algebra : Algebra ℕ C))
      (sourceCoalgebra := (inferInstance : Coalgebra ℕ C))
      (instM₀ := inferInstance) (sourceModule := (inferInstance : Module ℕ C))
      regularComodule W A (instB := inferInstance) (targetAlgebra := β)

/-- Unfolding the original predicate exposes precisely the stock range of the
base-changed subtype map and the stock lifted evaluation. In the abstract
expression every target tensor has the left module induced by `β`; its right
factor and the source coalgebra are independent of `β`. -/
private theorem originalTargetPredicate_apply (W : Submodule ℕ C)
    (A : Type uA) [CommSemiring A] (β : Algebra ℕ A) :
    originalTargetPredicate W A β =
    (fun (R₀ C₀ M₀ : Type) [instR₀ : CommSemiring R₀] [instC₀ : CommSemiring C₀]
        [sourceAlgebra : Algebra R₀ C₀] [sourceCoalgebra : Coalgebra R₀ C₀]
        [instM₀ : AddCommMonoid M₀] [sourceModule : Module R₀ M₀]
        (X : Coalgebra.RightComodule R₀ C₀ M₀) (W₀ : Submodule R₀ M₀)
        (B : Type uA) [instB : CommSemiring B] [targetAlgebra : Algebra R₀ B] =>
      ∀ (α : C₀ →ₐ[R₀] B), ∀ z ∈ LinearMap.range (W₀.subtype.baseChange B),
        LinearMap.liftBaseChange B
          ((TensorProduct.map (AlgHom.toLinearMap α)
              (LinearMap.id : M₀ →ₗ[R₀] M₀)).comp
            ((TensorProduct.comm R₀ M₀ C₀).toLinearMap.comp X.coaction)) z
          ∈ LinearMap.range (W₀.subtype.baseChange B))
      ℕ C C (instR₀ := inferInstance) (instC₀ := inferInstance)
        (sourceAlgebra := (MonoidAlgebra.algebra : Algebra ℕ C))
        (sourceCoalgebra := (inferInstance : Coalgebra ℕ C))
        (instM₀ := inferInstance) (sourceModule := (inferInstance : Module ℕ C))
        regularComodule W A (instB := inferInstance) (targetAlgebra := β) := by
  rfl

/-- At the canonical target dictionary this is exactly the displayed model
predicate, not an equality with an unelaborated old declaration's type. -/
private theorem originalTargetPredicate_canonical (W : Submodule ℕ C)
    (A : Type uA) [CommSemiring A] :
    originalTargetPredicate W A (Semiring.toNatAlgebra : Algebra ℕ A) ↔
      ∀ (α : C →ₐ[ℕ] A), ∀ z ∈ W.baseChange A,
        LinearMap.liftBaseChange A
          ((TensorProduct.map (AlgHom.toLinearMap α)
              (LinearMap.id : C →ₗ[ℕ] C)).comp
            ((TensorProduct.comm ℕ C C).toLinearMap.comp regularComodule.coaction)) z
          ∈ W.baseChange A := by
  rfl

/-- Stable image preservation for an independently sized target algebra. -/
private theorem U_evaluation_mem_baseChange
    {A : Type uA} [CommSemiring A]
    (α : C →ₐ[ℕ] A) (z : A ⊗[ℕ] C) (hz : z ∈ U.baseChange A) :
    LinearMap.liftBaseChange A
      ((TensorProduct.map (AlgHom.toLinearMap α)
          (LinearMap.id : C →ₗ[ℕ] C)).comp
        ((TensorProduct.comm ℕ C C).toLinearMap.comp regularComodule.coaction)) z
      ∈ U.baseChange A :=
  U_isStable.evaluation_mem_baseChange α z hz

-- Uses of both stability criteria on the regular monoid-algebra comodule.

private theorem U_forall_evaluation_mem_baseChange (A : Type uA) [CommSemiring A] (α : C →ₐ[ℕ] A) :
    ∀ z ∈ U.baseChange A,
      LinearMap.liftBaseChange A
        ((TensorProduct.map (AlgHom.toLinearMap α)
            (LinearMap.id : C →ₗ[ℕ] C)).comp
          ((TensorProduct.comm ℕ C C).toLinearMap.comp regularComodule.coaction)) z
        ∈ U.baseChange A := by
  exact ((Coalgebra.RightComodule.isStable_iff_forall_evaluation_mem_baseChange
    regularComodule U).mp U_isStable) A α

/-- Quantifying every original target dictionary is equivalent to the canonical
predicate in the same target universe. Equality substitutes the whole stock
predicate: homomorphisms, both tensor factors, subtype image and lifted map. -/
private theorem forall_originalTargetPredicate_iff (W : Submodule ℕ C) :
    (∀ (A : Type uA) [CommSemiring A] (β : Algebra ℕ A),
      originalTargetPredicate W A β) ↔
    (∀ (A : Type uA) [CommSemiring A] (α : C →ₐ[ℕ] A),
      ∀ z ∈ W.baseChange A,
        LinearMap.liftBaseChange A
          ((TensorProduct.map (AlgHom.toLinearMap α)
              (LinearMap.id : C →ₗ[ℕ] C)).comp
            ((TensorProduct.comm ℕ C C).toLinearMap.comp regularComodule.coaction)) z
          ∈ W.baseChange A) := by
  constructor
  · intro h A _
    exact (originalTargetPredicate_canonical W A).mp
      (h A (Semiring.toNatAlgebra : Algebra ℕ A))
  · intro h A _ β
    have hcanonical : originalTargetPredicate W A
        (Semiring.toNatAlgebra : Algebra ℕ A) :=
      (originalTargetPredicate_canonical W A).mpr (h A)
    exact Eq.mpr (congrArg (originalTargetPredicate W A)
      (Subsingleton.elim β (Semiring.toNatAlgebra : Algebra ℕ A))) hcanonical

/-- Preservation for every original target algebra, hence for all its original
homomorphisms, tensors and image-membership witnesses, without a coherence
hypothesis. The left module is induced by `β`; the right module is fixed. -/
private theorem U_original_evaluation_mem_baseChange
    (A : Type uA) [CommSemiring A] (β : Algebra ℕ A) :
    originalTargetPredicate U A β := by
  exact ((forall_originalTargetPredicate_iff U).mpr
    (fun B _ α => U_forall_evaluation_mem_baseChange B α)) A β

private theorem V_not_id_evaluation_mem_baseChange :
    ¬ (∀ z ∈ V.baseChange C,
      LinearMap.liftBaseChange C
        ((TensorProduct.map (AlgHom.toLinearMap (AlgHom.id ℕ C))
            (LinearMap.id : C →ₗ[ℕ] C)).comp
          ((TensorProduct.comm ℕ C C).toLinearMap.comp regularComodule.coaction)) z
        ∈ V.baseChange C) := by
  intro h
  exact V_not_isStable
    ((Coalgebra.RightComodule.isStable_iff_id_evaluation_mem_baseChange
      regularComodule V).mpr h)

/-- The same explicit C/id witness disproves the all-algebra test at level zero. -/
private theorem V_not_forall_evaluation_mem_baseChange :
    ¬ (∀ (A : Type) [CommSemiring A] (α : C →ₐ[ℕ] A),
      ∀ z ∈ V.baseChange A,
        LinearMap.liftBaseChange A
          ((TensorProduct.map (AlgHom.toLinearMap α)
              (LinearMap.id : C →ₗ[ℕ] C)).comp
            ((TensorProduct.comm ℕ C C).toLinearMap.comp regularComodule.coaction)) z
          ∈ V.baseChange A) := by
  intro h
  have hcanonical : originalTargetPredicate V C
      (Semiring.toNatAlgebra : Algebra ℕ C) :=
    (originalTargetPredicate_canonical V C).mpr (h C)
  have hold : originalTargetPredicate V C
      (MonoidAlgebra.algebra : Algebra ℕ C) :=
    Eq.mpr (congrArg (originalTargetPredicate V C)
      (Subsingleton.elim (MonoidAlgebra.algebra : Algebra ℕ C)
        (Semiring.toNatAlgebra : Algebra ℕ C))) hcanonical
  have horiginal :
      ∀ (α : C →ₐ[ℕ] C) (z : C ⊗[ℕ] C), z ∈ V.baseChange C →
        LinearMap.liftBaseChange C
          ((TensorProduct.map (AlgHom.toLinearMap α)
              (LinearMap.id : C →ₗ[ℕ] C)).comp
            ((TensorProduct.comm ℕ C C).toLinearMap.comp regularComodule.coaction)) z
          ∈ V.baseChange C := hold
  obtain ⟨z, hz, hn⟩ := V_id_counterexample
  exact hn (horiginal (AlgHom.id ℕ C) z hz)

-- Zero and whole submodule boundary cases.
private theorem bot_isStable : regularComodule.IsStable (⊥ : Submodule ℕ C) := by
  intro x hx
  have hx0 : x = 0 := by simpa using hx
  subst x
  exact ⟨0, by simp⟩

private theorem top_isStable : regularComodule.IsStable (⊤ : Submodule ℕ C) := by
  intro x _
  have hall : ∀ t : C ⊗[ℕ] C,
      t ∈ LinearMap.range ((⊤ : Submodule ℕ C).subtype.rTensor C) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul c d =>
        exact ⟨(⟨c, Submodule.mem_top⟩ : (⊤ : Submodule ℕ C)) ⊗ₜ[ℕ] d, rfl⟩
    | add a b ha hb => exact Submodule.add_mem _ ha hb
  exact hall (regularComodule.coaction x)

end NatMonoidAlgebraExamples

end Coalgebra.RightComodule
