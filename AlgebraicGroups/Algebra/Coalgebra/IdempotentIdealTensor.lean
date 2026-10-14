/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.IdempotentIdeal
public import Mathlib.RingTheory.Coalgebra.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Submodule
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.LinearAlgebra.LinearDisjoint

/-!
# Tensor products of idempotent principal-ideal coalgebras

Multiplication identifies the tensor product of the canonical coalgebras on
`Ideal.span {e}` and `Ideal.span {f}` with the canonical coalgebra on
`Ideal.span {e * f}`, for idempotents in a commutative semiring. The input
coalgebras are `he.coalgebraSpan` and `hf.coalgebraSpan`, the tensor coalgebra
is Mathlib's, and the output coalgebra is `(he.mul hf).coalgebraSpan`.

The inverse sends a target member `z` to its scalar value times the tensor
of the two specified generators. This does not require unique coefficients,
freeness, faithful scalar action, or a nonzero tensor product. The tensor
of the generators is diagonal and has counit `e * f`, which need not be one.

## References

The ideal coalgebras and their generator and scalar-recovery API are supplied
by `IdempotentIdeal`. Mathlib supplies `Submodule.mulMap`, the multiplication
equivalence `Submodule.LinearDisjoint.mulMap`, the principal-ideal product
identity, and the tensor coalgebra and `CoalgEquiv` APIs.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open scoped TensorProduct

namespace IsIdempotentElem

variable {R : Type u} [CommSemiring R] {e f : R}

private theorem span_singleton_linearDisjoint (e : R) (hf : IsIdempotentElem f) :
    (Ideal.span ({e} : Set R)).LinearDisjoint (Ideal.span ({f} : Set R)) := by
  let M := Ideal.span ({e} : Set R)
  let N := Ideal.span ({f} : Set R)
  let i : N →ₗ[R] R := N.subtype
  let p : R →ₗ[R] N :=
    LinearMap.toSpanSingleton R N (Ideal.spanSingletonGenerator f)
  -- The idempotent ideal is a retract of the scalars, so tensoring its inclusion
  -- preserves injectivity without any flatness assumption on the other factor.
  have hsplit :
      TensorProduct.map (LinearMap.id : M →ₗ[R] M) p ∘ₗ
        TensorProduct.map (LinearMap.id : M →ₗ[R] M) i = LinearMap.id := by
    apply TensorProduct.ext'
    intro x y
    change x ⊗ₜ[R] ((y : R) • Ideal.spanSingletonGenerator f) = x ⊗ₜ[R] y
    rw [hf.smul_spanSingletonGenerator y]
  have hi : Function.Injective
      (TensorProduct.map (LinearMap.id : M →ₗ[R] M) i) := by
    have hleft : Function.LeftInverse
        (TensorProduct.map (LinearMap.id : M →ₗ[R] M) p)
        (TensorProduct.map (LinearMap.id : M →ₗ[R] M) i) :=
      fun t => LinearMap.congr_fun hsplit t
    exact hleft.injective
  have hmul : Submodule.mulMap M N =
      M.subtype ∘ₗ (TensorProduct.rid R M).toLinearMap ∘ₗ
        TensorProduct.map (LinearMap.id : M →ₗ[R] M) i := by
    apply TensorProduct.ext'
    intro x y
    change (x : R) * (y : R) = (y : R) * (x : R)
    exact mul_comm _ _
  refine ⟨?_⟩
  rw [hmul]
  exact M.injective_subtype.comp ((TensorProduct.rid R M).injective.comp hi)

/-- Multiplication identifies the tensor product of the canonical coalgebras on
idempotent principal ideals with the canonical coalgebra on the product ideal.
The inverse multiplies the tensor of the specified generators by the scalar
value of the target member. -/
noncomputable def tensorCoalgebraSpanEquiv
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f) :
    @CoalgEquiv R _
      ((Ideal.span ({e} : Set R)) ⊗[R] (Ideal.span ({f} : Set R)))
      (Ideal.span ({e * f} : Set R))
      _ _ _ _
      (@TensorProduct.instCoalgebra R R
        (Ideal.span ({e} : Set R)) (Ideal.span ({f} : Set R))
        _ _ _ _ _ _ _ _ _
        hf.coalgebraSpan he.coalgebraSpan).toCoalgebraStruct
      (he.mul hf).coalgebraSpan.toCoalgebraStruct :=
  letI : Coalgebra R (Ideal.span ({e} : Set R)) := he.coalgebraSpan
  letI : Coalgebra R (Ideal.span ({f} : Set R)) := hf.coalgebraSpan
  letI : Coalgebra R (Ideal.span ({e * f} : Set R)) := (he.mul hf).coalgebraSpan
  have h :
      (Ideal.span ({e} : Set R)).LinearDisjoint (Ideal.span ({f} : Set R)) := by
    exact span_singleton_linearDisjoint e hf
  { h.mulMap ≪≫ₗ
      LinearEquiv.ofEq _ _ (Ideal.span_singleton_mul_span_singleton e f) with
    counit_comp := by
      apply TensorProduct.ext'
      intro x y
      change (x : R) * (y : R) = Coalgebra.counit (R := R) (x ⊗ₜ[R] y)
      rw [TensorProduct.counit_tmul]
      change (x : R) * (y : R) = (y : R) * (x : R)
      exact mul_comm _ _
    map_comp_comul := by
      apply TensorProduct.ext'
      intro x y
      simp only [LinearMap.comp_apply, TensorProduct.comul_tmul,
        he.coalgebraSpan_comul_apply, hf.coalgebraSpan_comul_apply,
        (he.mul hf).coalgebraSpan_comul_apply,
        TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
        TensorProduct.map_tmul]
      congr 1 }

/-- The scalar value of the image of a pure tensor is the product of the two
scalar values. -/
@[simp] theorem coe_tensorCoalgebraSpanEquiv_tmul
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (x : Ideal.span ({e} : Set R)) (y : Ideal.span ({f} : Set R)) :
    ((he.tensorCoalgebraSpanEquiv hf) (x ⊗ₜ[R] y) : R) =
      (x : R) * (y : R) := by
  change (((span_singleton_linearDisjoint e hf).mulMap ≪≫ₗ
      LinearEquiv.ofEq _ _ (Ideal.span_singleton_mul_span_singleton e f))
      (x ⊗ₜ[R] y) : R) = (x : R) * (y : R)
  simp only [LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply,
    Submodule.LinearDisjoint.val_mulMap_tmul]

/-- The tensor of the specified generators maps to the specified generator of
the product ideal. -/
@[simp] theorem tensorCoalgebraSpanEquiv_generator
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f) :
    (he.tensorCoalgebraSpanEquiv hf)
      (Ideal.spanSingletonGenerator e ⊗ₜ[R] Ideal.spanSingletonGenerator f) =
      Ideal.spanSingletonGenerator (e * f) := by
  apply Subtype.ext
  simpa only [Ideal.coe_spanSingletonGenerator] using
    coe_tensorCoalgebraSpanEquiv_tmul he hf
      (Ideal.spanSingletonGenerator e) (Ideal.spanSingletonGenerator f)

/-- The inverse uses the scalar value of the target member as a specified
coefficient, without asserting uniqueness of coefficients. -/
@[simp] theorem tensorCoalgebraSpanEquiv_symm_apply
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (z : Ideal.span ({e * f} : Set R)) :
    (@CoalgEquiv.symm R
      ((Ideal.span ({e} : Set R)) ⊗[R] (Ideal.span ({f} : Set R)))
      (Ideal.span ({e * f} : Set R)) _ _ _ _ _
      (@TensorProduct.instCoalgebra R R
        (Ideal.span ({e} : Set R)) (Ideal.span ({f} : Set R))
        _ _ _ _ _ _ _ _ _ hf.coalgebraSpan he.coalgebraSpan).toCoalgebraStruct
      (he.mul hf).coalgebraSpan.toCoalgebraStruct
      (he.tensorCoalgebraSpanEquiv hf)) z =
      (z : R) •
        (Ideal.spanSingletonGenerator e ⊗ₜ[R] Ideal.spanSingletonGenerator f) := by
  let : Coalgebra R (Ideal.span ({e} : Set R)) := he.coalgebraSpan
  let : Coalgebra R (Ideal.span ({f} : Set R)) := hf.coalgebraSpan
  let : Coalgebra R (Ideal.span ({e * f} : Set R)) := (he.mul hf).coalgebraSpan
  apply EquivLike.injective (he.tensorCoalgebraSpanEquiv hf)
  rw [CoalgEquiv.apply_symm_apply, map_smul, tensorCoalgebraSpanEquiv_generator]
  exact ((he.mul hf).smul_spanSingletonGenerator z).symm

/-- Forgetting ideal membership after the equivalence gives Mathlib's
multiplication map on the tensor product of the ideal submodules. -/
theorem tensorCoalgebraSpanEquiv_subtype_comp
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f) :
    (Ideal.span ({e * f} : Set R)).subtype ∘ₗ
        (@CoalgEquiv.toLinearEquiv R _
          ((Ideal.span ({e} : Set R)) ⊗[R] (Ideal.span ({f} : Set R)))
          (Ideal.span ({e * f} : Set R)) _ _ _ _
          (@TensorProduct.instCoalgebra R R
            (Ideal.span ({e} : Set R)) (Ideal.span ({f} : Set R))
            _ _ _ _ _ _ _ _ _ hf.coalgebraSpan he.coalgebraSpan).toCoalgebraStruct
          (he.mul hf).coalgebraSpan.toCoalgebraStruct
          (he.tensorCoalgebraSpanEquiv hf)).toLinearMap =
      Submodule.mulMap (Ideal.span ({e} : Set R)) (Ideal.span ({f} : Set R)) := by
  refine TensorProduct.ext' fun x y => ?_
  change ((he.tensorCoalgebraSpanEquiv hf) (x ⊗ₜ[R] y) : R) =
    (x : R) * (y : R)
  exact coe_tensorCoalgebraSpanEquiv_tmul he hf x y

/-- A tensor is recovered by multiplying the tensor of the generators by the
scalar value of its image. -/
theorem tensorCoalgebraSpanEquiv_coe_smul_generator
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (t : (Ideal.span ({e} : Set R)) ⊗[R] (Ideal.span ({f} : Set R))) :
    ((he.tensorCoalgebraSpanEquiv hf) t : R) •
        (Ideal.spanSingletonGenerator e ⊗ₜ[R] Ideal.spanSingletonGenerator f) = t := by
  let : Coalgebra R (Ideal.span ({e} : Set R)) := he.coalgebraSpan
  let : Coalgebra R (Ideal.span ({f} : Set R)) := hf.coalgebraSpan
  let : Coalgebra R (Ideal.span ({e * f} : Set R)) := (he.mul hf).coalgebraSpan
  calc
    ((he.tensorCoalgebraSpanEquiv hf) t : R) •
        (Ideal.spanSingletonGenerator e ⊗ₜ[R] Ideal.spanSingletonGenerator f) =
        (he.tensorCoalgebraSpanEquiv hf).symm ((he.tensorCoalgebraSpanEquiv hf) t) :=
      (tensorCoalgebraSpanEquiv_symm_apply he hf ((he.tensorCoalgebraSpanEquiv hf) t)).symm
    _ = t := CoalgEquiv.symm_apply_apply (he.tensorCoalgebraSpanEquiv hf) t

/-- Comultiplication in the canonical tensor coalgebra appends the tensor of
the two specified generators. -/
theorem tensorCoalgebraSpan_comul_apply
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (t : (Ideal.span ({e} : Set R)) ⊗[R] (Ideal.span ({f} : Set R))) :
    (@TensorProduct.instCoalgebra R R
      (Ideal.span ({e} : Set R)) (Ideal.span ({f} : Set R))
      _ _ _ _ _ _ _ _ _ hf.coalgebraSpan he.coalgebraSpan).comul t =
      t ⊗ₜ[R]
        (Ideal.spanSingletonGenerator e ⊗ₜ[R] Ideal.spanSingletonGenerator f) := by
  let : Coalgebra R (Ideal.span ({e} : Set R)) := he.coalgebraSpan
  let : Coalgebra R (Ideal.span ({f} : Set R)) := hf.coalgebraSpan
  change Coalgebra.comul (R := R) t =
    t ⊗ₜ[R] (Ideal.spanSingletonGenerator e ⊗ₜ[R] Ideal.spanSingletonGenerator f)
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
      rw [TensorProduct.comul_tmul]
      change TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R R R R
          (Ideal.span ({e} : Set R)) (Ideal.span ({e} : Set R))
          (Ideal.span ({f} : Set R)) (Ideal.span ({f} : Set R))
          (he.coalgebraSpan.comul x ⊗ₜ[R] hf.coalgebraSpan.comul y) =
        (x ⊗ₜ[R] y) ⊗ₜ[R]
          (Ideal.spanSingletonGenerator e ⊗ₜ[R] Ideal.spanSingletonGenerator f)
      rw [he.coalgebraSpan_comul_apply x, hf.coalgebraSpan_comul_apply y,
        TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul]
  | add t₁ t₂ h₁ h₂ =>
      rw [map_add, h₁, h₂, TensorProduct.add_tmul]

/-- The counit in the canonical tensor coalgebra is Mathlib's multiplication
map on the tensor product of the ideal submodules. -/
theorem tensorCoalgebraSpan_counit
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f) :
    (@TensorProduct.instCoalgebra R R
      (Ideal.span ({e} : Set R)) (Ideal.span ({f} : Set R))
      _ _ _ _ _ _ _ _ _ hf.coalgebraSpan he.coalgebraSpan).counit =
      Submodule.mulMap (Ideal.span ({e} : Set R)) (Ideal.span ({f} : Set R)) := by
  let : Coalgebra R (Ideal.span ({e} : Set R)) := he.coalgebraSpan
  let : Coalgebra R (Ideal.span ({f} : Set R)) := hf.coalgebraSpan
  refine TensorProduct.ext' fun x y => ?_
  change Coalgebra.counit (R := R) (x ⊗ₜ[R] y) = (x : R) * (y : R)
  rw [TensorProduct.counit_tmul]
  change hf.coalgebraSpan.counit y • he.coalgebraSpan.counit x = (x : R) * (y : R)
  rw [hf.coalgebraSpan_counit_apply y, he.coalgebraSpan_counit_apply x, smul_eq_mul]
  exact mul_comm _ _

end IsIdempotentElem
