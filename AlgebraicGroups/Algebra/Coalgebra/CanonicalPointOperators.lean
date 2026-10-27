/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.CoefficientOperators
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.RingTheory.Bialgebra.Convolution
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Canonical point tests for left coaction laws

For an `R`-bialgebra `C` over a commutative semiring `R` and a given linear map
`δ : M →ₗ[R] C ⊗[R] M`, its counit law is equivalent to
identity of the tensor-extended coefficient operator at the convolution unit,
for every commutative coefficient algebra in a fixed sufficiently large universe.
The unit point is the counit followed by the structure map of the coefficient
algebra, as in Mathlib's `AlgHom.convOne_def`.

The tester universe depends on the scalar and coordinate algebras, not on `M`.
The converse uses `ULift R` and its tensor congruence with `R ⊗[R] M`; no
injectivity or flatness assumption on scalar extension is needed. No coaction
laws are assumed on `δ`. The bialgebra `C` need not be commutative; the
commutative-coordinate criterion follows by specialization.

When `C` is commutative, coassociativity of the same given map is equivalent to
composition of all its algebra-point coefficient operators: the operator for `β` after that for `α`
is the operator at their convolution product `α ⋆ β`. Its converse uses the two
ordered inclusions into `C ⊗[R] C`, lifted to the same tester universe. Neither
criterion assumes the other coaction law. Their conjunction gives the combined
criterion for commutative `C`.

The operators are Mathlib's `TensorProduct.AlgebraTensorModule.lift` applied to
`LinearMap.toSpanSingleton`. The proof uses its tensor universal property and
Mathlib's convolution-unit and algebra-equivalence APIs.
-/

@[expose] public section

open scoped TensorProduct

namespace TensorProduct.AlgebraTensorModule

universe uR uC uM uA w

section Counit

variable {R : Type uR} {C : Type uC} {M : Type uM}
variable [CommSemiring R] [Semiring C] [Bialgebra R C]
variable [AddCommMonoid M] [Module R M]

private theorem map_one_eq_one_tmul_counit {A : Type uA}
    [CommSemiring A] [Algebra R A] (x : C ⊗[R] M) :
    TensorProduct.map
        (1 : WithConv (C →ₐ[R] A)).ofConv.toLinearMap
        (LinearMap.id : M →ₗ[R] M) x =
      (1 : A) ⊗ₜ[R] (TensorProduct.lid R M)
        (TensorProduct.map (Bialgebra.counitAlgHom R C).toLinearMap
          (LinearMap.id : M →ₗ[R] M) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul c m =>
      simp only [TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply,
        AlgHom.convOne_apply, Bialgebra.counitAlgHom_apply, TensorProduct.lid_tmul]
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  | add x y hx hy =>
      simp only [map_add, TensorProduct.tmul_add, hx, hy]

/-- A given linear map over a possibly noncommutative `R`-bialgebra satisfies the
counit law if and only if its tensor-extended coefficient operator at the convolution
unit is the identity for every commutative
coefficient algebra in `Type (max uR uC w)`. The carrier universe `uM` is independent
of the tester universe, and no coassociativity or counit law is assumed on `δ`. -/
theorem counit_iff_forall_lift_toSpanSingleton_one
    (δ : M →ₗ[R] C ⊗[R] M) :
    ((TensorProduct.lid R M).toLinearMap.comp
        ((TensorProduct.map (Bialgebra.counitAlgHom R C).toLinearMap
          (LinearMap.id : M →ₗ[R] M)).comp δ) =
      (LinearMap.id : M →ₗ[R] M)) ↔
    (∀ (A : Type (max uR uC w)) [CommSemiring A] [Algebra R A],
      TensorProduct.AlgebraTensorModule.lift
          (LinearMap.toSpanSingleton A (M →ₗ[R] A ⊗[R] M)
            ((TensorProduct.map
              (1 : WithConv (C →ₐ[R] A)).ofConv.toLinearMap
              (LinearMap.id : M →ₗ[R] M)).comp δ)) =
        (LinearMap.id : A ⊗[R] M →ₗ[A] A ⊗[R] M)) := by
  constructor
  · intro hδ A _ _
    apply ext
    intro a m
    have hm :
        (TensorProduct.lid R M)
          (TensorProduct.map (Bialgebra.counitAlgHom R C).toLinearMap
            (LinearMap.id : M →ₗ[R] M) (δ m)) = m :=
      LinearMap.congr_fun hδ m
    simp only [lift_tmul, LinearMap.toSpanSingleton_apply, LinearMap.smul_apply,
      LinearMap.comp_apply, LinearMap.id_apply]
    rw [map_one_eq_one_tmul_counit, hm]
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  · intro h
    -- Normalize the scalar-one action before specializing the coefficient algebra.
    have hseed (A : Type (max uR uC w)) [CommSemiring A] [Algebra R A] (m : M) :
        TensorProduct.map
            (1 : WithConv (C →ₐ[R] A)).ofConv.toLinearMap
            (LinearMap.id : M →ₗ[R] M) (δ m) =
          (1 : A) ⊗ₜ[R] m := by
      -- Coefficient change is R-linear, not linear over the two different algebras.
      have hR := congrArg (LinearMap.restrictScalars R) (h A)
      have hm := LinearMap.congr_fun hR ((1 : A) ⊗ₜ[R] m)
      simpa only [LinearMap.coe_restrictScalars, lift_tmul, LinearMap.toSpanSingleton_apply,
        LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.id_apply, one_smul] using hm
    let e : ULift.{max uC w} R ≃ₐ[R] R := ULift.algEquiv
    apply LinearMap.ext
    intro m
    have hm := hseed (ULift.{max uC w} R) m
    rw [map_one_eq_one_tmul_counit] at hm
    have hdown := congrArg
      (fun z => (TensorProduct.lid R M)
        (TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl R M) z)) hm
    simpa only [TensorProduct.congr_tmul, AlgEquiv.coe_toLinearEquiv,
      LinearEquiv.refl_apply, map_one, LinearEquiv.coe_toLinearMap,
      TensorProduct.lid_tmul, one_smul,
      LinearMap.comp_apply, LinearMap.id_apply] using hdown

end Counit

section Coassociativity

variable {R : Type uR} {C : Type uC} {M : Type uM}
variable [CommSemiring R] [CommSemiring C] [Bialgebra R C]
variable [AddCommMonoid M] [Module R M]

private theorem lift_toSpanSingleton_one_tmul
    {A : Type uA} [Semiring A] [Algebra R A]
    (F : M →ₗ[R] A ⊗[R] M) (m : M) :
    (lift (LinearMap.toSpanSingleton A (M →ₗ[R] A ⊗[R] M) F)).restrictScalars R
      ((1 : A) ⊗ₜ[R] m) = F m := by
  simpa only [LinearMap.coe_restrictScalars, lift_tmul,
    LinearMap.toSpanSingleton_apply, LinearMap.smul_apply] using (one_smul A (F m))

/-- Coassociativity of a given left linear coaction is equivalent to the
composition law for all algebra-point coefficient operators at one fixed
coefficient universe. The operator for `β` is applied after that for `α`.
No counit law on the given map is required. -/
theorem coassoc_iff_forall_lift_toSpanSingleton_comp_map
    (δ : M →ₗ[R] C ⊗[R] M) :
    ((TensorProduct.map (Bialgebra.comulAlgHom R C).toLinearMap
        (LinearMap.id : M →ₗ[R] M)).comp δ =
      (TensorProduct.assoc R C C M).symm.toLinearMap.comp
        ((TensorProduct.map (LinearMap.id : C →ₗ[R] C) δ).comp δ)) ↔
    (∀ (A : Type (max uR uC w)) [CommSemiring A] [Algebra R A]
        (α β : C →ₐ[R] A),
      (TensorProduct.AlgebraTensorModule.lift
        (LinearMap.toSpanSingleton A (M →ₗ[R] A ⊗[R] M)
          ((TensorProduct.map β.toLinearMap
            (LinearMap.id : M →ₗ[R] M)).comp δ))).comp
        (TensorProduct.AlgebraTensorModule.lift
          (LinearMap.toSpanSingleton A (M →ₗ[R] A ⊗[R] M)
            ((TensorProduct.map α.toLinearMap
              (LinearMap.id : M →ₗ[R] M)).comp δ))) =
      TensorProduct.AlgebraTensorModule.lift
        (LinearMap.toSpanSingleton A (M →ₗ[R] A ⊗[R] M)
          ((TensorProduct.map
            (WithConv.toConv α * WithConv.toConv β).ofConv.toLinearMap
            (LinearMap.id : M →ₗ[R] M)).comp δ))) := by
  constructor
  · intro hδ A _ _ α β
    have hCoefficient :
        (WithConv.toConv α * WithConv.toConv β).ofConv.toLinearMap =
          (LinearMap.mul' R A).comp
            ((TensorProduct.map α.toLinearMap β.toLinearMap).comp
              (Bialgebra.comulAlgHom R C).toLinearMap) :=
      congrArg WithConv.ofConv
        (AlgHom.toLinearMap_convMul (WithConv.toConv α) (WithConv.toConv β))
    have hComposition := lift_toSpanSingleton_comp_map_of_coassoc
      (Bialgebra.comulAlgHom R C).toLinearMap δ α.toLinearMap β.toLinearMap hδ
    rw [← hCoefficient] at hComposition
    exact hComposition
  · intro h
    let U := C ⊗[R] C
    let B := ULift.{max uR w} U
    let e : B ≃ₐ[R] U := ULift.algEquiv (R := R) (A := U)
    let E : B ⊗[R] M ≃ₗ[R] U ⊗[R] M :=
      TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl R M)
    let l : C →ₐ[R] U :=
      Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := C) (B := C)
    let r : C →ₐ[R] U :=
      Algebra.TensorProduct.includeRight (R := R) (A := C) (B := C)
    let α : C →ₐ[R] B := e.symm.toAlgHom.comp l
    let β : C →ₐ[R] B := e.symm.toAlgHom.comp r
    let p : C →ₐ[R] B := (WithConv.toConv α * WithConv.toConv β).ofConv
    let T (γ : C →ₐ[R] B) : B ⊗[R] M →ₗ[B] B ⊗[R] M :=
      lift (LinearMap.toSpanSingleton B (M →ₗ[R] B ⊗[R] M)
        ((TensorProduct.map γ.toLinearMap (LinearMap.id : M →ₗ[R] M)).comp δ))
    let S (γ : C →ₐ[R] U) : U ⊗[R] M →ₗ[U] U ⊗[R] M :=
      lift (LinearMap.toSpanSingleton U (M →ₗ[R] U ⊗[R] M)
        ((TensorProduct.map γ.toLinearMap (LinearMap.id : M →ₗ[R] M)).comp δ))
    have hα : e.toAlgHom.comp α = l := by
      ext c
      exact e.apply_symm_apply (l c)
    have hβ : e.toAlgHom.comp β = r := by
      ext c
      exact e.apply_symm_apply (r c)
    have hmul :
        (LinearMap.mul' R U).comp (TensorProduct.map l.toLinearMap r.toLinearMap) =
          (LinearMap.id : U →ₗ[R] U) := by
      apply TensorProduct.ext'
      intro c d
      change (c ⊗ₜ[R] (1 : C)) * ((1 : C) ⊗ₜ[R] d) = c ⊗ₜ[R] d
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    have hInclusions : (WithConv.toConv l * WithConv.toConv r).ofConv =
        Bialgebra.comulAlgHom R C := by
      apply AlgHom.toLinearMap_injective
      calc
        _ = (LinearMap.mul' R U).comp
            ((TensorProduct.map l.toLinearMap r.toLinearMap).comp
              (Bialgebra.comulAlgHom R C).toLinearMap) :=
          congrArg WithConv.ofConv
            (AlgHom.toLinearMap_convMul (WithConv.toConv l) (WithConv.toConv r))
        _ = _ := by rw [← LinearMap.comp_assoc, hmul, LinearMap.id_comp]
    have hp : e.toAlgHom.comp p = Bialgebra.comulAlgHom R C := by
      calc
        _ = (WithConv.toConv (e.toAlgHom.comp α) *
            WithConv.toConv (e.toAlgHom.comp β)).ofConv :=
          AlgHom.comp_convMul_distrib e.toAlgHom (WithConv.toConv α) (WithConv.toConv β)
        _ = _ := by rw [hα, hβ, hInclusions]
    -- Restrict scalars before comparing the two operators across coefficients.
    -- This square is only for the displayed tensor-square tester.
    have hdownCoefficient (γ : C →ₐ[R] B) (b : B) (z : C ⊗[R] M) :
        E (b • TensorProduct.map γ.toLinearMap (LinearMap.id : M →ₗ[R] M) z) =
          e b • TensorProduct.map (e.toAlgHom.comp γ).toLinearMap
            (LinearMap.id : M →ₗ[R] M) z := by
      induction z using TensorProduct.inductionOn with
      | tmul c m =>
          change E ((b * γ c) ⊗ₜ[R] m) = (e b * e (γ c)) ⊗ₜ[R] m
          simp only [E, TensorProduct.congr_tmul, AlgEquiv.coe_toLinearEquiv,
            LinearEquiv.refl_apply, map_mul]
      | add x y hx hy =>
          simp only [map_add, smul_add, hx, hy]
    have hdown (γ : C →ₐ[R] B) :
        E.toLinearMap.comp ((T γ).restrictScalars R) =
          ((S (e.toAlgHom.comp γ)).restrictScalars R).comp E.toLinearMap := by
      apply LinearMap.ext
      intro x
      change E (T γ x) = S (e.toAlgHom.comp γ) (E x)
      induction x using TensorProduct.inductionOn with
      | tmul b m =>
          change E (b • TensorProduct.map γ.toLinearMap
            (LinearMap.id : M →ₗ[R] M) (δ m)) =
              e b • TensorProduct.map (e.toAlgHom.comp γ).toLinearMap
                (LinearMap.id : M →ₗ[R] M) (δ m)
          exact hdownCoefficient γ b (δ m)
      | add x y hx hy =>
          simp only [map_add, hx, hy]
    have hdownApply (γ : C →ₐ[R] B) (x : B ⊗[R] M) :
        E (T γ x) = S (e.toAlgHom.comp γ) (E x) :=
      LinearMap.congr_fun (hdown γ) x
    have htest : (T β).comp (T α) = T p := h B α β
    have heval (m : M) :
        S r (S l ((1 : U) ⊗ₜ[R] m)) =
          S (Bialgebra.comulAlgHom R C) ((1 : U) ⊗ₜ[R] m) := by
      have hz := congrArg
        (fun f : B ⊗[R] M →ₗ[B] B ⊗[R] M => E (f ((1 : B) ⊗ₜ[R] m))) htest
      change E (T β (T α ((1 : B) ⊗ₜ[R] m))) = E (T p ((1 : B) ⊗ₜ[R] m)) at hz
      rw [hdownApply β, hdownApply α, hdownApply p, hα, hβ, hp] at hz
      simpa only [E, TensorProduct.congr_tmul, AlgEquiv.coe_toLinearEquiv,
        LinearEquiv.refl_apply, map_one] using hz
    have hCoefficient (c : C) (y : C ⊗[R] M) :
        (c ⊗ₜ[R] (1 : C)) •
            TensorProduct.map r.toLinearMap (LinearMap.id : M →ₗ[R] M) y =
          (TensorProduct.assoc R C C M).symm (c ⊗ₜ[R] y) := by
      induction y using TensorProduct.inductionOn with
      | tmul d n =>
          change ((c ⊗ₜ[R] (1 : C)) * ((1 : C) ⊗ₜ[R] d)) ⊗ₜ[R] n =
            (c ⊗ₜ[R] d) ⊗ₜ[R] n
          simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      | add x y hx hy =>
          simp only [map_add, TensorProduct.tmul_add, smul_add, hx, hy]
    have hIteration (x : C ⊗[R] M) :
        S r (TensorProduct.map l.toLinearMap (LinearMap.id : M →ₗ[R] M) x) =
          (TensorProduct.assoc R C C M).symm
            (TensorProduct.map (LinearMap.id : C →ₗ[R] C) δ x) := by
      induction x using TensorProduct.inductionOn with
      | tmul c m =>
          change (c ⊗ₜ[R] (1 : C)) •
              TensorProduct.map r.toLinearMap (LinearMap.id : M →ₗ[R] M) (δ m) =
            (TensorProduct.assoc R C C M).symm (c ⊗ₜ[R] δ m)
          exact hCoefficient c (δ m)
      | add x y hx hy =>
          simp only [map_add, hx, hy]
    apply LinearMap.ext
    intro m
    have hseed (γ : C →ₐ[R] U) :
        S γ ((1 : U) ⊗ₜ[R] m) =
          TensorProduct.map γ.toLinearMap (LinearMap.id : M →ₗ[R] M) (δ m) :=
      lift_toSpanSingleton_one_tmul
        ((TensorProduct.map γ.toLinearMap (LinearMap.id : M →ₗ[R] M)).comp δ) m
    have hm := heval m
    rw [hseed l, hseed (Bialgebra.comulAlgHom R C)] at hm
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] using
      hm.symm.trans (hIteration (δ m))

end Coassociativity

section Combined

/-- A given linear map satisfies the counit and coassociativity laws if and only if
its tensor-extended algebra-point coefficient operators send the convolution unit
to the identity and satisfy the composition law: the operator for `β` after that
for `α` is the operator at `α ⋆ β`. The fixed tester universe is independent of
the carrier universe. -/
theorem counit_and_coassoc_iff_forall_lift_toSpanSingleton_one_and_comp_map
    {R : Type uR} {C : Type uC} {M : Type uM}
    [CommSemiring R] [CommSemiring C] [Bialgebra R C]
    [AddCommMonoid M] [Module R M]
    (δ : M →ₗ[R] C ⊗[R] M) :
    (((TensorProduct.lid R M).toLinearMap.comp
          ((TensorProduct.map (Bialgebra.counitAlgHom R C).toLinearMap
            (LinearMap.id : M →ₗ[R] M)).comp δ) =
        (LinearMap.id : M →ₗ[R] M)) ∧
      ((TensorProduct.map (Bialgebra.comulAlgHom R C).toLinearMap
          (LinearMap.id : M →ₗ[R] M)).comp δ =
        (TensorProduct.assoc R C C M).symm.toLinearMap.comp
          ((TensorProduct.map (LinearMap.id : C →ₗ[R] C) δ).comp δ))) ↔
    (∀ (A : Type (max uR uC w)) [CommSemiring A] [Algebra R A],
      (TensorProduct.AlgebraTensorModule.lift
          (LinearMap.toSpanSingleton A (M →ₗ[R] A ⊗[R] M)
            ((TensorProduct.map
              (1 : WithConv (C →ₐ[R] A)).ofConv.toLinearMap
              (LinearMap.id : M →ₗ[R] M)).comp δ)) =
        (LinearMap.id : A ⊗[R] M →ₗ[A] A ⊗[R] M)) ∧
      (∀ (α β : C →ₐ[R] A),
        (TensorProduct.AlgebraTensorModule.lift
          (LinearMap.toSpanSingleton A (M →ₗ[R] A ⊗[R] M)
            ((TensorProduct.map β.toLinearMap
              (LinearMap.id : M →ₗ[R] M)).comp δ))).comp
          (TensorProduct.AlgebraTensorModule.lift
            (LinearMap.toSpanSingleton A (M →ₗ[R] A ⊗[R] M)
              ((TensorProduct.map α.toLinearMap
                (LinearMap.id : M →ₗ[R] M)).comp δ))) =
        TensorProduct.AlgebraTensorModule.lift
          (LinearMap.toSpanSingleton A (M →ₗ[R] A ⊗[R] M)
            ((TensorProduct.map
              (WithConv.toConv α * WithConv.toConv β).ofConv.toLinearMap
              (LinearMap.id : M →ₗ[R] M)).comp δ)))) := by
  constructor
  · intro h A _ _
    exact ⟨(counit_iff_forall_lift_toSpanSingleton_one.{uR, uC, uM, w} δ).mp h.1 A,
      (coassoc_iff_forall_lift_toSpanSingleton_comp_map.{uR, uC, uM, w} δ).mp h.2 A⟩
  · intro h
    exact ⟨(counit_iff_forall_lift_toSpanSingleton_one.{uR, uC, uM, w} δ).mpr
        (fun A _ _ => (h A).1),
      (coassoc_iff_forall_lift_toSpanSingleton_comp_map.{uR, uC, uM, w} δ).mpr
        (fun A _ _ => (h A).2)⟩
end Combined

end TensorProduct.AlgebraTensorModule
