/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.CoefficientOperators
public import AlgebraicGroups.LinearAlgebra.TensorProduct.Extension
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.RingTheory.Bialgebra.Convolution
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Canonical point tests for left coaction laws

For a semiring `R`-algebra `C`, an arbitrary linear map `Δ : C →ₗ[R] C ⊗[R] C`
and a given `δ : M →ₗ[R] C ⊗[R] M`, relative coassociativity is equivalent to
composition of the tensor-extended operators for the two ordered inclusions into
`C ⊗[R] C`. This tensor-square criterion requires neither commutativity of `C`
nor a coalgebra structure or law on `Δ`.

For an arbitrary linear counit candidate `ε : C →ₗ[R] R`, the counit law of
this same `δ` is equivalent to identity of every scalar coefficient operator.
Here `C` needs only module structure. The tester algebras may be noncommutative,
and lie in `Type (max uR uT)`, independently of the universes of `C` and `M`.

Relative coassociativity is also detected by all pairs of algebra maps into
semiring testers in `Type (max uC uT)`. Multiplication of their coefficients
remains linear when `Δ` is only linear; no commutativity of the testers is needed.

When `ε` or `Δ` is an algebra homomorphism, the coefficients are genuine algebra
points: respectively `(Algebra.ofId R A).comp ε` and
`(Algebra.TensorProduct.productMap α β).comp Δ`. The counit criterion permits
noncommutative `C`. The coassociativity criterion uses commutative `C` and
commutative testers, so that the same tensor-square tester remains available.
Neither criterion assumes a coalgebra structure or any law on `ε`, `Δ` or `δ`.

The converses raise the canonical testers `R` and `C ⊗[R] C` using `ULift` and
transport along algebra equivalences. No injectivity or flatness assumption on
scalar extension is needed. The existing bialgebra criteria are specializations
at the convolution unit and product; their conjunction tests both laws.

The operators are Mathlib's `TensorProduct.AlgebraTensorModule.lift` applied to
`LinearMap.toSpanSingleton`. The proof uses its tensor universal property and
Mathlib's convolution-unit and algebra-equivalence APIs.
-/

@[expose] public section

open scoped TensorProduct

namespace TensorProduct.AlgebraTensorModule

universe uR uC uM uA w uT

section Inclusions

variable {R : Type uR} {C : Type uC}
variable [CommSemiring R] [Semiring C] [Algebra R C]

private theorem mul'_comp_map_includeLeft_includeRight :
    (LinearMap.mul' R (C ⊗[R] C)).comp
        (TensorProduct.map
          (Algebra.TensorProduct.includeLeft : C →ₐ[R] C ⊗[R] C).toLinearMap
          (Algebra.TensorProduct.includeRight : C →ₐ[R] C ⊗[R] C).toLinearMap) =
      (LinearMap.id : C ⊗[R] C →ₗ[R] C ⊗[R] C) := by
  apply TensorProduct.ext'
  intro c d
  have h := congrArg (fun f : C ⊗[R] C →ₐ[R] C ⊗[R] C => f (c ⊗ₜ[R] d))
    (Algebra.TensorProduct.lift_includeLeft_includeRight
      (R := R) (S := R) (A := C) (B := C))
  change (c ⊗ₜ[R] (1 : C)) * ((1 : C) ⊗ₜ[R] d) = c ⊗ₜ[R] d at h ⊢
  exact h

variable {M : Type uM} [AddCommMonoid M] [Module R M]

private theorem lift_toSpanSingleton_comp_inclusions_one_tmul
    (δ : M →ₗ[R] C ⊗[R] M) (m : M) :
    (lift
      (LinearMap.toSpanSingleton (C ⊗[R] C) (M →ₗ[R] (C ⊗[R] C) ⊗[R] M)
        ((TensorProduct.map
          (Algebra.TensorProduct.includeRight : C →ₐ[R] C ⊗[R] C).toLinearMap
          (LinearMap.id : M →ₗ[R] M)).comp δ))).comp
      (lift
        (LinearMap.toSpanSingleton (C ⊗[R] C) (M →ₗ[R] (C ⊗[R] C) ⊗[R] M)
          ((TensorProduct.map
            (Algebra.TensorProduct.includeLeft : C →ₐ[R] C ⊗[R] C).toLinearMap
            (LinearMap.id : M →ₗ[R] M)).comp δ)))
        ((1 : C ⊗[R] C) ⊗ₜ[R] m) =
      (TensorProduct.assoc R C C M).symm.toLinearMap
        (((TensorProduct.map (LinearMap.id : C →ₗ[R] C) δ).comp δ) m) := by
  simp only [LinearMap.comp_apply, lift_tmul, LinearMap.toSpanSingleton_apply,
    one_smul, LinearEquiv.coe_toLinearMap]
  simpa only [mul'_comp_map_includeLeft_includeRight, TensorProduct.map_id,
    LinearMap.id_apply] using
    lift_toSpanSingleton_apply_map δ
      (Algebra.TensorProduct.includeLeft : C →ₐ[R] C ⊗[R] C).toLinearMap
      (Algebra.TensorProduct.includeRight : C →ₐ[R] C ⊗[R] C).toLinearMap (δ m)

/-- A given linear map satisfies relative coassociativity for `Δ` if and only if
its tensor-square coefficient operators compose in the order of the two
inclusions. No coalgebra structure or law on `Δ` is required. -/
theorem coassoc_iff_lift_toSpanSingleton_comp_map_inclusions
    (Δ : C →ₗ[R] C ⊗[R] C) (δ : M →ₗ[R] C ⊗[R] M) :
    ((TensorProduct.map Δ (LinearMap.id : M →ₗ[R] M)).comp δ =
      (TensorProduct.assoc R C C M).symm.toLinearMap.comp
        ((TensorProduct.map (LinearMap.id : C →ₗ[R] C) δ).comp δ)) ↔
    (lift
      (LinearMap.toSpanSingleton (C ⊗[R] C) (M →ₗ[R] (C ⊗[R] C) ⊗[R] M)
        ((TensorProduct.map
          (Algebra.TensorProduct.includeRight : C →ₐ[R] C ⊗[R] C).toLinearMap
          (LinearMap.id : M →ₗ[R] M)).comp δ))).comp
      (lift
        (LinearMap.toSpanSingleton (C ⊗[R] C) (M →ₗ[R] (C ⊗[R] C) ⊗[R] M)
          ((TensorProduct.map
            (Algebra.TensorProduct.includeLeft : C →ₐ[R] C ⊗[R] C).toLinearMap
            (LinearMap.id : M →ₗ[R] M)).comp δ))) =
      lift
        (LinearMap.toSpanSingleton (C ⊗[R] C) (M →ₗ[R] (C ⊗[R] C) ⊗[R] M)
          ((TensorProduct.map Δ (LinearMap.id : M →ₗ[R] M)).comp δ)) := by
  constructor
  · intro hδ
    have hComposition := lift_toSpanSingleton_comp_map_of_coassoc Δ δ
      (Algebra.TensorProduct.includeLeft : C →ₐ[R] C ⊗[R] C).toLinearMap
      (Algebra.TensorProduct.includeRight : C →ₐ[R] C ⊗[R] C).toLinearMap hδ
    rw [← LinearMap.comp_assoc, mul'_comp_map_includeLeft_includeRight, LinearMap.id_comp]
      at hComposition
    exact hComposition
  · intro h
    apply LinearMap.ext
    intro m
    have hm := congrArg
      (fun f : (C ⊗[R] C) ⊗[R] M →ₗ[C ⊗[R] C] (C ⊗[R] C) ⊗[R] M =>
        f ((1 : C ⊗[R] C) ⊗ₜ[R] m)) h
    rw [lift_toSpanSingleton_comp_inclusions_one_tmul] at hm
    simpa only [lift_tmul, LinearMap.toSpanSingleton_apply, LinearMap.smul_apply,
      LinearMap.comp_apply, one_smul, LinearEquiv.coe_toLinearMap] using hm.symm

end Inclusions

section LinearCounitCalculations

variable {R : Type uR} {C : Type uC} {M : Type uM}
variable [CommSemiring R] [AddCommMonoid C] [Module R C]
variable [AddCommMonoid M] [Module R M]

private theorem map_scalar_eq_one_tmul {A : Type uA}
    [Semiring A] [Algebra R A] (ε : C →ₗ[R] R) (x : C ⊗[R] M) :
    TensorProduct.map ((Algebra.linearMap R A).comp ε)
        (LinearMap.id : M →ₗ[R] M) x =
      (1 : A) ⊗ₜ[R] (TensorProduct.lid R M)
        (TensorProduct.map ε (LinearMap.id : M →ₗ[R] M) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul c m =>
      simp only [TensorProduct.map_tmul, LinearMap.comp_apply,
        Algebra.linearMap_apply, LinearMap.id_apply, TensorProduct.lid_tmul]
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  | add x y hx hy =>
      simp only [map_add, TensorProduct.tmul_add, hx, hy]

private theorem lift_toSpanSingleton_map_linear_eq_id_of_counit {A : Type uA}
    [Semiring A] [Algebra R A] (ε : C →ₗ[R] R) (δ : M →ₗ[R] C ⊗[R] M)
    (hδ : (TensorProduct.lid R M).toLinearMap.comp
        ((TensorProduct.map ε (LinearMap.id : M →ₗ[R] M)).comp δ) =
      (LinearMap.id : M →ₗ[R] M)) :
    lift (LinearMap.toSpanSingleton A (M →ₗ[R] A ⊗[R] M)
        ((TensorProduct.map ((Algebra.linearMap R A).comp ε)
          (LinearMap.id : M →ₗ[R] M)).comp δ)) =
      (LinearMap.id : A ⊗[R] M →ₗ[A] A ⊗[R] M) := by
  apply (lift_toSpanSingleton_eq_id_iff _).mpr
  apply LinearMap.ext
  intro m
  have hm : (TensorProduct.lid R M)
      (TensorProduct.map ε (LinearMap.id : M →ₗ[R] M) (δ m)) = m :=
    LinearMap.congr_fun hδ m
  simp only [LinearMap.comp_apply, TensorProduct.mk_apply, map_scalar_eq_one_tmul, hm]

private theorem counit_of_lift_toSpanSingleton_map_ulift
    (ε : C →ₗ[R] R) (δ : M →ₗ[R] C ⊗[R] M)
    (h : lift (LinearMap.toSpanSingleton (ULift.{uT} R)
        (M →ₗ[R] ULift.{uT} R ⊗[R] M)
        ((TensorProduct.map ((Algebra.linearMap R (ULift.{uT} R)).comp ε)
          (LinearMap.id : M →ₗ[R] M)).comp δ)) =
      (LinearMap.id : ULift.{uT} R ⊗[R] M →ₗ[ULift.{uT} R] ULift.{uT} R ⊗[R] M)) :
    (TensorProduct.lid R M).toLinearMap.comp
        ((TensorProduct.map ε (LinearMap.id : M →ₗ[R] M)).comp δ) =
      (LinearMap.id : M →ₗ[R] M) := by
  let e : ULift.{uT} R ≃ₐ[R] R := ULift.algEquiv
  have hseed := (lift_toSpanSingleton_eq_id_iff _).mp h
  apply LinearMap.ext
  intro m
  have hm := LinearMap.congr_fun hseed m
  simp only [LinearMap.comp_apply, TensorProduct.mk_apply] at hm
  rw [map_scalar_eq_one_tmul] at hm
  have hdown := congrArg
    (fun z => (TensorProduct.lid R M)
      (TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl R M) z)) hm
  simpa only [TensorProduct.congr_tmul, AlgEquiv.coe_toLinearEquiv,
    LinearEquiv.refl_apply, map_one, LinearEquiv.coe_toLinearMap,
    TensorProduct.lid_tmul, one_smul,
    LinearMap.comp_apply, LinearMap.id_apply] using hdown

end LinearCounitCalculations

section CoassociativityTransport

variable {R : Type uR} {C : Type uC} {M : Type uM} {A : Type uA}
variable [CommSemiring R] [Semiring C] [Algebra R C]
variable [AddCommMonoid M] [Module R M] [Semiring A] [Algebra R A]

private theorem coassoc_of_lift_toSpanSingleton_comp_map_equiv
    (Δ : C →ₗ[R] C ⊗[R] C) (δ : M →ₗ[R] C ⊗[R] M)
    (e : A ≃ₐ[R] C ⊗[R] C) (α β : C →ₐ[R] A)
    (hα : e.toAlgHom.comp α = Algebra.TensorProduct.includeLeft)
    (hβ : e.toAlgHom.comp β = Algebra.TensorProduct.includeRight)
    (h : (lift (LinearMap.toSpanSingleton A (M →ₗ[R] A ⊗[R] M)
        ((TensorProduct.map β.toLinearMap (LinearMap.id : M →ₗ[R] M)).comp δ))).comp
      (lift (LinearMap.toSpanSingleton A (M →ₗ[R] A ⊗[R] M)
        ((TensorProduct.map α.toLinearMap (LinearMap.id : M →ₗ[R] M)).comp δ))) =
      lift (LinearMap.toSpanSingleton A (M →ₗ[R] A ⊗[R] M)
        ((TensorProduct.map
          ((LinearMap.mul' R A).comp
            ((TensorProduct.map α.toLinearMap β.toLinearMap).comp Δ))
          (LinearMap.id : M →ₗ[R] M)).comp δ))) :
    (TensorProduct.map Δ (LinearMap.id : M →ₗ[R] M)).comp δ =
      (TensorProduct.assoc R C C M).symm.toLinearMap.comp
        ((TensorProduct.map (LinearMap.id : C →ₗ[R] C) δ).comp δ) := by
  let U := C ⊗[R] C
  let E : A ⊗[R] M ≃ₗ[R] U ⊗[R] M :=
    TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl R M)
  let l : C →ₐ[R] U := Algebra.TensorProduct.includeLeft
  let r : C →ₐ[R] U := Algebra.TensorProduct.includeRight
  let p := (LinearMap.mul' R A).comp
    ((TensorProduct.map α.toLinearMap β.toLinearMap).comp Δ)
  let T (γ : C →ₗ[R] A) := lift (LinearMap.toSpanSingleton A
    (M →ₗ[R] A ⊗[R] M)
    ((TensorProduct.map γ (LinearMap.id : M →ₗ[R] M)).comp δ))
  let S (γ : C →ₗ[R] U) := lift (LinearMap.toSpanSingleton U
    (M →ₗ[R] U ⊗[R] M)
    ((TensorProduct.map γ (LinearMap.id : M →ₗ[R] M)).comp δ))
  have hα' : e.toLinearMap.comp α.toLinearMap = l.toLinearMap :=
    congrArg AlgHom.toLinearMap hα
  have hβ' : e.toLinearMap.comp β.toLinearMap = r.toLinearMap :=
    congrArg AlgHom.toLinearMap hβ
  have hprod : e.toLinearMap.comp
      ((LinearMap.mul' R A).comp (TensorProduct.map α.toLinearMap β.toLinearMap)) =
      (LinearMap.id : U →ₗ[R] U) := by
    calc
      _ = (LinearMap.mul' R U).comp
          (TensorProduct.map l.toLinearMap r.toLinearMap) := by
        apply TensorProduct.ext'
        intro c d
        change e (α c * β d) = l c * r d
        rw [map_mul]
        exact congrArg₂ (· * ·) (AlgHom.congr_fun hα c) (AlgHom.congr_fun hβ d)
      _ = _ := mul'_comp_map_includeLeft_includeRight
  have hp : e.toLinearMap.comp p = Δ := by
    simpa only [p, LinearMap.comp_assoc, LinearMap.id_comp] using
      congrArg (fun f => f.comp Δ) hprod
  have hdown (γ : C →ₗ[R] A) (x : A ⊗[R] M) :
      E (T γ x) = S (e.toLinearMap.comp γ) (E x) := by
    have hseed : E.toLinearMap.comp
        ((TensorProduct.map γ (LinearMap.id : M →ₗ[R] M)).comp δ) =
        (TensorProduct.map (e.toLinearMap.comp γ)
          (LinearMap.id : M →ₗ[R] M)).comp δ := by
      simp only [E, TensorProduct.toLinearMap_congr, LinearEquiv.refl_toLinearMap,
        ← LinearMap.comp_assoc, ← TensorProduct.map_comp, LinearMap.id_comp]
    have hs := congr_comp_lift_toSpanSingleton e
      ((TensorProduct.map γ (LinearMap.id : M →ₗ[R] M)).comp δ)
    change E.toLinearMap.comp ((T γ).restrictScalars R) = _ at hs
    rw [hseed] at hs
    exact LinearMap.congr_fun hs x
  apply (coassoc_iff_lift_toSpanSingleton_comp_map_inclusions Δ δ).mpr
  change (S r.toLinearMap).comp (S l.toLinearMap) = S Δ
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := E.surjective x
  have hz := congrArg (fun f : A ⊗[R] M →ₗ[A] A ⊗[R] M => E (f y)) h
  change E (T β.toLinearMap (T α.toLinearMap y)) = E (T p y) at hz
  change S r.toLinearMap (S l.toLinearMap (E y)) = S Δ (E y)
  rw [hdown, hdown, hdown, hα', hβ', hp] at hz
  exact hz

end CoassociativityTransport

section LinearCounit
variable {R : Type uR} {C : Type uC} {M : Type uM}
variable [CommSemiring R] [AddCommMonoid C] [Module R C]
variable [AddCommMonoid M] [Module R M]

/-- The counit law for a given linear map is equivalent to identity of every
scalar coefficient operator. Only module structure on `C` is needed, and the
tester universe depends on `R`, not on `C` or `M`. -/
theorem counit_iff_forall_lift_toSpanSingleton_map_linear
    (ε : C →ₗ[R] R) (δ : M →ₗ[R] C ⊗[R] M) :
    ((TensorProduct.lid R M).toLinearMap.comp
        ((TensorProduct.map ε (LinearMap.id : M →ₗ[R] M)).comp δ) =
      (LinearMap.id : M →ₗ[R] M)) ↔
    (∀ (A : Type (max uR uT)) [Semiring A] [Algebra R A],
      lift
          (LinearMap.toSpanSingleton A (M →ₗ[R] A ⊗[R] M)
            ((TensorProduct.map ((Algebra.linearMap R A).comp ε)
              (LinearMap.id : M →ₗ[R] M)).comp δ)) =
        (LinearMap.id : A ⊗[R] M →ₗ[A] A ⊗[R] M)) := by
  constructor
  · intro hδ A _ _
    exact lift_toSpanSingleton_map_linear_eq_id_of_counit ε δ hδ
  · intro h
    exact counit_of_lift_toSpanSingleton_map_ulift ε δ (h (ULift.{uT} R))

end LinearCounit

section LinearCoassociativity
variable {R : Type uR} {C : Type uC} {M : Type uM}
variable [CommSemiring R] [Semiring C] [Algebra R C]
variable [AddCommMonoid M] [Module R M]

/-- Relative coassociativity of a given linear map is detected by its ordered
coefficient operators in all semiring algebras. The coefficient formed using
`Δ` is linear, and the tester universe depends only on `C`. -/
theorem coassoc_iff_forall_lift_toSpanSingleton_comp_map_linear
    (Δ : C →ₗ[R] C ⊗[R] C) (δ : M →ₗ[R] C ⊗[R] M) :
    ((TensorProduct.map Δ (LinearMap.id : M →ₗ[R] M)).comp δ =
      (TensorProduct.assoc R C C M).symm.toLinearMap.comp
        ((TensorProduct.map (LinearMap.id : C →ₗ[R] C) δ).comp δ)) ↔
    (∀ (A : Type (max uC uT)) [Semiring A] [Algebra R A]
        (α β : C →ₐ[R] A),
      (lift
        (LinearMap.toSpanSingleton A (M →ₗ[R] A ⊗[R] M)
          ((TensorProduct.map β.toLinearMap
            (LinearMap.id : M →ₗ[R] M)).comp δ))).comp
        (lift
          (LinearMap.toSpanSingleton A (M →ₗ[R] A ⊗[R] M)
            ((TensorProduct.map α.toLinearMap
              (LinearMap.id : M →ₗ[R] M)).comp δ))) =
      lift
        (LinearMap.toSpanSingleton A (M →ₗ[R] A ⊗[R] M)
          ((TensorProduct.map
            ((LinearMap.mul' R A).comp
              ((TensorProduct.map α.toLinearMap β.toLinearMap).comp Δ))
            (LinearMap.id : M →ₗ[R] M)).comp δ))) := by
  constructor
  · intro hδ A _ _ α β
    exact lift_toSpanSingleton_comp_map_of_coassoc Δ δ α.toLinearMap β.toLinearMap hδ
  · intro h
    let e : ULift.{uT} (C ⊗[R] C) ≃ₐ[R] C ⊗[R] C := ULift.algEquiv
    let α := e.symm.toAlgHom.comp
      (Algebra.TensorProduct.includeLeft : C →ₐ[R] C ⊗[R] C)
    let β := e.symm.toAlgHom.comp
      (Algebra.TensorProduct.includeRight : C →ₐ[R] C ⊗[R] C)
    apply coassoc_of_lift_toSpanSingleton_comp_map_equiv Δ δ e α β
    · ext c
      exact e.apply_symm_apply _
    · ext c
      exact e.apply_symm_apply _
    · exact h _ α β

end LinearCoassociativity

section PointCounit
variable {R : Type uR} {C : Type uC} {M : Type uM}
variable [CommSemiring R] [Semiring C] [Algebra R C]
variable [AddCommMonoid M] [Module R M]

/-- The counit law for the supplied `δ` is detected by all commutative-algebra
points obtained from the given algebra homomorphism `ε`. The coordinate algebra
`C` need not be commutative or carry a coalgebra structure. -/
theorem counit_iff_forall_lift_toSpanSingleton_map_algHom
    (ε : C →ₐ[R] R) (δ : M →ₗ[R] C ⊗[R] M) :
    ((TensorProduct.lid R M).toLinearMap.comp
        ((TensorProduct.map ε.toLinearMap
          (LinearMap.id : M →ₗ[R] M)).comp δ) =
      (LinearMap.id : M →ₗ[R] M)) ↔
    (∀ (A : Type (max uR uT)) [CommSemiring A] [Algebra R A],
      lift
          (LinearMap.toSpanSingleton A (M →ₗ[R] A ⊗[R] M)
            ((TensorProduct.map
              ((Algebra.ofId R A).comp ε).toLinearMap
              (LinearMap.id : M →ₗ[R] M)).comp δ)) =
        (LinearMap.id : A ⊗[R] M →ₗ[A] A ⊗[R] M)) := by
  constructor
  · intro hδ A _ _
    exact lift_toSpanSingleton_map_linear_eq_id_of_counit ε.toLinearMap δ hδ
  · intro h
    exact counit_of_lift_toSpanSingleton_map_ulift ε.toLinearMap δ (h (ULift.{uT} R))

end PointCounit

section PointCoassociativity
variable {R : Type uR} {C : Type uC} {M : Type uM}
variable [CommSemiring R] [CommSemiring C] [Algebra R C]
variable [AddCommMonoid M] [Module R M]

/-- Relative coassociativity for an algebra homomorphism `Δ` is equivalent to
composition of all algebra-point coefficient operators of the same `δ`. The
operator for `β` follows that for `α`; the coefficient is their stock product
point composed with `Δ`. No coalgebra law on `Δ` is assumed. -/
theorem coassoc_iff_forall_lift_toSpanSingleton_comp_map_algHom
    (Δ : C →ₐ[R] C ⊗[R] C) (δ : M →ₗ[R] C ⊗[R] M) :
    ((TensorProduct.map Δ.toLinearMap
        (LinearMap.id : M →ₗ[R] M)).comp δ =
      (TensorProduct.assoc R C C M).symm.toLinearMap.comp
        ((TensorProduct.map (LinearMap.id : C →ₗ[R] C) δ).comp δ)) ↔
    (∀ (A : Type (max uC uT)) [CommSemiring A] [Algebra R A]
        (α β : C →ₐ[R] A),
      (lift
        (LinearMap.toSpanSingleton A (M →ₗ[R] A ⊗[R] M)
          ((TensorProduct.map β.toLinearMap
            (LinearMap.id : M →ₗ[R] M)).comp δ))).comp
        (lift
          (LinearMap.toSpanSingleton A (M →ₗ[R] A ⊗[R] M)
            ((TensorProduct.map α.toLinearMap
              (LinearMap.id : M →ₗ[R] M)).comp δ))) =
      lift
        (LinearMap.toSpanSingleton A (M →ₗ[R] A ⊗[R] M)
          ((TensorProduct.map
            ((Algebra.TensorProduct.productMap α β).comp Δ).toLinearMap
            (LinearMap.id : M →ₗ[R] M)).comp δ))) := by
  constructor
  · intro hδ A _ _ α β
    simpa only [Algebra.TensorProduct.productMap_eq_comp_map, AlgHom.comp_toLinearMap,
      Algebra.TensorProduct.lmul'_toLinearMap, Algebra.TensorProduct.toLinearMap_map,
      map_eq, LinearMap.comp_assoc] using
      lift_toSpanSingleton_comp_map_of_coassoc Δ.toLinearMap δ
        α.toLinearMap β.toLinearMap hδ
  · intro h
    let e : ULift.{uT} (C ⊗[R] C) ≃ₐ[R] C ⊗[R] C := ULift.algEquiv
    let α := e.symm.toAlgHom.comp
      (Algebra.TensorProduct.includeLeft : C →ₐ[R] C ⊗[R] C)
    let β := e.symm.toAlgHom.comp
      (Algebra.TensorProduct.includeRight : C →ₐ[R] C ⊗[R] C)
    apply coassoc_of_lift_toSpanSingleton_comp_map_equiv Δ.toLinearMap δ e α β
    · ext c
      exact e.apply_symm_apply _
    · ext c
      exact e.apply_symm_apply _
    · simpa only [Algebra.TensorProduct.productMap_eq_comp_map, AlgHom.comp_toLinearMap,
        Algebra.TensorProduct.lmul'_toLinearMap, Algebra.TensorProduct.toLinearMap_map,
        map_eq, LinearMap.comp_assoc] using h _ α β

end PointCoassociativity

section Counit

variable {R : Type uR} {C : Type uC} {M : Type uM}
variable [CommSemiring R] [Semiring C] [Bialgebra R C]
variable [AddCommMonoid M] [Module R M]

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
  simpa only [AlgHom.convOne_def, WithConv.ofConv_toConv] using
    counit_iff_forall_lift_toSpanSingleton_map_algHom.{uR, uC, uM, max uC w}
      (Bialgebra.counitAlgHom R C) δ

end Counit

section Coassociativity

variable {R : Type uR} {C : Type uC} {M : Type uM}
variable [CommSemiring R] [CommSemiring C] [Bialgebra R C]
variable [AddCommMonoid M] [Module R M]

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
  simpa only [AlgHom.convMul_def, WithConv.ofConv_toConv,
    Algebra.TensorProduct.productMap_eq_comp_map, AlgHom.comp_assoc] using
    coassoc_iff_forall_lift_toSpanSingleton_comp_map_algHom.{uR, uC, uM, max uR w}
      (Bialgebra.comulAlgHom R C) δ

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
