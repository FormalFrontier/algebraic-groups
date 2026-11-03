/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Coalgebra.Convolution
public import Mathlib.RingTheory.Derivation.Basic

/-!
# Left-invariant derivations on a commutative bialgebra

A derivation at the counit extends to an ordinary derivation by contracting the
second factor of comultiplication. The underlying linear map is the convolution
of the linear identity with the algebra-map multiple of the point derivation.
The linear identity here is not the convolution unit, whose underlying map is
algebra-map composed with counit.

The extension is left-invariant, its counit is the original point derivation,
and these two properties characterize it uniquely. In particular the extension
loses no point derivations. `leftInvariantLinearMap` bundles its base-semiring
linearity. All tensor products retain the original base action of the given
bialgebra; the output has the natural coefficient action on itself.

## Implementation notes

The input coefficient action is explicitly `Module.compHom` along the counit.
The point module is passed directly to the derivation projection, rather than
installed as an ambient instance. No algebra structure in the reverse direction
is used. Neither additive cancellation nor an antipode nor cocommutativity is
needed.

## References

The construction uses Mathlib's `LinearMap.convMul`, balanced tensor maps and
unitors, and its `Derivation` structure and extensionality API. These interfaces
and the convolution comparison below follow the Mathlib contributors' work
(Apache-2.0).
-/

@[expose] public section

open scoped TensorProduct
open Coalgebra

namespace Derivation

universe u v

variable {R : Type u} {A : Type v} [CommSemiring R] [CommSemiring A] [Bialgebra R A]

variable (δ : @Derivation R A R _ _ _ _
  (Module.compHom R (Bialgebra.counitAlgHom R A).toRingHom) _)

private theorem leftInvariant_convolution_eq :
    (WithConv.toConv (LinearMap.id : A →ₗ[R] A) *
      WithConv.toConv ((Algebra.linearMap R A).comp (@Derivation.toLinearMap R A R
          (inferInstance : CommSemiring R) (inferInstance : CommSemiring A)
          (inferInstance : AddCommMonoid R) (inferInstance : Algebra R A)
          (Module.compHom R (Bialgebra.counitAlgHom R A).toRingHom)
          (inferInstance : Module R R) δ))).ofConv =
      ((TensorProduct.rid R A).toLinearMap.comp ((@Derivation.toLinearMap R A R
          (inferInstance : CommSemiring R) (inferInstance : CommSemiring A)
          (inferInstance : AddCommMonoid R) (inferInstance : Algebra R A)
          (Module.compHom R (Bialgebra.counitAlgHom R A).toRingHom)
          (inferInstance : Module R R) δ).lTensor A)).comp
        (comul : A →ₗ[R] A ⊗[R] A) := by
  change ((LinearMap.mul' R A).comp
      (TensorProduct.map LinearMap.id ((Algebra.linearMap R A).comp (@Derivation.toLinearMap R A R
          (inferInstance : CommSemiring R) (inferInstance : CommSemiring A)
          (inferInstance : AddCommMonoid R) (inferInstance : Algebra R A)
          (Module.compHom R (Bialgebra.counitAlgHom R A).toRingHom)
          (inferInstance : Module R R) δ)))).comp
        comul = _
  congr 1
  ext x y
  simp [Algebra.smul_def, mul_comm]

private theorem leftInvariant_contraction_leibniz (a b : A) :
    TensorProduct.rid R A ((@Derivation.toLinearMap R A R
        (inferInstance : CommSemiring R) (inferInstance : CommSemiring A)
        (inferInstance : AddCommMonoid R) (inferInstance : Algebra R A)
        (Module.compHom R (Bialgebra.counitAlgHom R A).toRingHom)
        (inferInstance : Module R R) δ).lTensor A (comul (a * b))) =
      a * TensorProduct.rid R A ((@Derivation.toLinearMap R A R
          (inferInstance : CommSemiring R) (inferInstance : CommSemiring A)
          (inferInstance : AddCommMonoid R) (inferInstance : Algebra R A)
          (Module.compHom R (Bialgebra.counitAlgHom R A).toRingHom)
          (inferInstance : Module R R) δ).lTensor A (comul b)) +
        b * TensorProduct.rid R A ((@Derivation.toLinearMap R A R
            (inferInstance : CommSemiring R) (inferInstance : CommSemiring A)
            (inferInstance : AddCommMonoid R) (inferInstance : Algebra R A)
            (Module.compHom R (Bialgebra.counitAlgHom R A).toRingHom)
            (inferInstance : Module R R) δ).lTensor A (comul a)) := by
  let f : A ⊗[R] A →ₗ[R] A :=
    (TensorProduct.rid R A).toLinearMap.comp ((@Derivation.toLinearMap R A R
        (inferInstance : CommSemiring R) (inferInstance : CommSemiring A)
        (inferInstance : AddCommMonoid R) (inferInstance : Algebra R A)
        (Module.compHom R (Bialgebra.counitAlgHom R A).toRingHom)
        (inferInstance : Module R R) δ).lTensor A)
  let e : A ⊗[R] A →ₗ[R] A :=
    (TensorProduct.rid R A).toLinearMap.comp ((counit : A →ₗ[R] R).lTensor A)
  -- Prove the product calculation on the existing balanced tensor product.
  have h (x y : A ⊗[R] A) : f (x * y) = e x * f y + e y * f x := by
    induction x using TensorProduct.inductionOn with
    | tmul x₁ x₂ =>
        induction y using TensorProduct.inductionOn with
        | tmul y₁ y₂ =>
            rw [Algebra.TensorProduct.tmul_mul_tmul]
            change δ (x₂ * y₂) • (x₁ * y₁) =
              (counit (R := R) x₂ • x₁) * (δ y₂ • y₁) +
                (counit (R := R) y₂ • y₁) * (δ x₂ • x₁)
            rw [@Derivation.leibniz R A R _ _ _ _
              (Module.compHom R (Bialgebra.counitAlgHom R A).toRingHom)
              (inferInstance : Module R R) δ x₂ y₂]
            change (counit (R := R) x₂ * δ y₂ + counit (R := R) y₂ * δ x₂) •
                (x₁ * y₁) = _
            simp only [Algebra.smul_def, map_add, map_mul, add_mul]
            ac_rfl
        | add y z hy hz =>
            simp only [mul_add, map_add, hy, hz, add_mul]
            ac_rfl
    | add x y hx hy =>
        simp only [add_mul, map_add, hx, hy, mul_add]
        ac_rfl
  simpa [f, e] using h (comul (R := R) a) (comul (R := R) b)

/-- Extend a derivation with the counit coefficient action to the left-invariant
ordinary derivation on the bialgebra. Its coefficient action is multiplication
on `A`, while its base action is the original action of the given bialgebra. -/
noncomputable def leftInvariant : Derivation R A A where
  toLinearMap :=
    (WithConv.toConv (LinearMap.id : A →ₗ[R] A) *
      WithConv.toConv ((Algebra.linearMap R A).comp (@Derivation.toLinearMap R A R
          (inferInstance : CommSemiring R) (inferInstance : CommSemiring A)
          (inferInstance : AddCommMonoid R) (inferInstance : Algebra R A)
          (Module.compHom R (Bialgebra.counitAlgHom R A).toRingHom)
          (inferInstance : Module R R) δ))).ofConv
  map_one_eq_zero' := by
    rw [(private_decl% leftInvariant_convolution_eq) δ]
    simp [Algebra.TensorProduct.one_def]
  leibniz' a b := by
    rw [(private_decl% leftInvariant_convolution_eq) δ]
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, smul_eq_mul] using
      (private_decl% leftInvariant_contraction_leibniz) δ a b

/-- The characteristic contraction formula for the left-invariant extension. -/
theorem leftInvariant_toLinearMap :
    (leftInvariant δ).toLinearMap =
      ((TensorProduct.rid R A).toLinearMap.comp ((@Derivation.toLinearMap R A R
          (inferInstance : CommSemiring R) (inferInstance : CommSemiring A)
          (inferInstance : AddCommMonoid R) (inferInstance : Algebra R A)
          (Module.compHom R (Bialgebra.counitAlgHom R A).toRingHom)
          (inferInstance : Module R R) δ).lTensor A)).comp
        (comul : A →ₗ[R] A ⊗[R] A) :=
  leftInvariant_convolution_eq δ

/-- Evaluate the left-invariant extension by contracting the second tensor factor. -/
theorem leftInvariant_apply (a : A) :
    leftInvariant δ a =
      TensorProduct.rid R A ((@Derivation.toLinearMap R A R
          (inferInstance : CommSemiring R) (inferInstance : CommSemiring A)
          (inferInstance : AddCommMonoid R) (inferInstance : Algebra R A)
          (Module.compHom R (Bialgebra.counitAlgHom R A).toRingHom)
          (inferInstance : Module R R) δ).lTensor A (comul a)) :=
  LinearMap.congr_fun (leftInvariant_toLinearMap δ) a

/-- The extension obeys the left-invariance convention
`Δ ∘ D = (id ⊗ D) ∘ Δ`, without assuming cocommutativity. -/
theorem comul_leftInvariant :
    (comul : A →ₗ[R] A ⊗[R] A).comp (leftInvariant δ).toLinearMap =
      ((leftInvariant δ).toLinearMap.lTensor A).comp comul := by
  let L : A →ₗ[R] A ⊗[R] A :=
    (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A).toLinearMap
  let J : A →ₗ[R] A ⊗[R] A :=
    (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toLinearMap
  let d : A →ₗ[R] A := (Algebra.linearMap R A).comp (@Derivation.toLinearMap R A R
      (inferInstance : CommSemiring R) (inferInstance : CommSemiring A)
      (inferInstance : AddCommMonoid R) (inferInstance : Algebra R A)
      (Module.compHom R (Bialgebra.counitAlgHom R A).toRingHom)
      (inferInstance : Module R R) δ)
  let l : WithConv (A →ₗ[R] A ⊗[R] A) := WithConv.toConv L
  let j : WithConv (A →ₗ[R] A ⊗[R] A) := WithConv.toConv J
  let t : WithConv (A →ₗ[R] A ⊗[R] A) := WithConv.toConv (J.comp d)
  have hmul : (LinearMap.mul' R (A ⊗[R] A)).comp (TensorProduct.map L J) =
      (LinearMap.id : A ⊗[R] A →ₗ[R] A ⊗[R] A) := by
    ext x y
    change (x ⊗ₜ[R] (1 : A)) * ((1 : A) ⊗ₜ[R] y) = x ⊗ₜ[R] y
    simp
  have hΔ : WithConv.toConv (comul : A →ₗ[R] A ⊗[R] A) = l * j := by
    apply WithConv.ext
    change comul = ((LinearMap.mul' R (A ⊗[R] A)).comp
      (TensorProduct.map L J)).comp comul
    rw [hmul, LinearMap.id_comp]
  have hd : (comul : A →ₗ[R] A ⊗[R] A).comp d = J.comp d := by
    ext a
    change comul (R := R) (algebraMap R A (δ a)) =
      (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A)
        (algebraMap R A (δ a))
    simp
  have hJ : WithConv.toConv (J.comp (leftInvariant δ).toLinearMap) = j * t := by
    apply WithConv.ext
    change J.comp (WithConv.toConv (LinearMap.id : A →ₗ[R] A) *
      WithConv.toConv d).ofConv = (j * t).ofConv
    simpa only [WithConv.ofConv_toConv, LinearMap.comp_id] using
      LinearMap.algHom_comp_convMul_distrib
        (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A)
        (WithConv.toConv (LinearMap.id : A →ₗ[R] A)) (WithConv.toConv d)
  -- Coassociativity is supplied by convolution associativity; no factors commute.
  calc
    _ = ((l * j) * t).ofConv := by
      change (Bialgebra.comulAlgHom R A).toLinearMap.comp
        (WithConv.toConv (LinearMap.id : A →ₗ[R] A) * WithConv.toConv d).ofConv = _
      rw [LinearMap.algHom_comp_convMul_distrib]
      simp only [Bialgebra.toLinearMap_comulAlgHom, LinearMap.comp_id]
      rw [hd]
      change (WithConv.toConv (comul : A →ₗ[R] A ⊗[R] A) * t).ofConv = _
      rw [hΔ]
    _ = (l * (j * t)).ofConv := by rw [mul_assoc]
    _ = (l * WithConv.toConv (J.comp (leftInvariant δ).toLinearMap)).ofConv := by
      rw [← hJ]
    _ = ((leftInvariant δ).toLinearMap.lTensor A).comp comul := by
      have ht : (LinearMap.mul' R (A ⊗[R] A)).comp
          (TensorProduct.map L (J.comp (leftInvariant δ).toLinearMap)) =
          (leftInvariant δ).toLinearMap.lTensor A := by
        ext x y
        change (x ⊗ₜ[R] (1 : A)) * ((1 : A) ⊗ₜ[R] leftInvariant δ y) =
          x ⊗ₜ[R] leftInvariant δ y
        simp
      change ((LinearMap.mul' R (A ⊗[R] A)).comp
        (TensorProduct.map L (J.comp (leftInvariant δ).toLinearMap))).comp comul = _
      rw [ht]

/-- Reading the left-invariant extension through the counit recovers the point
input. This is the convolution unit law after postcomposition with the counit. -/
theorem counit_leftInvariant :
    (Bialgebra.counitAlgHom R A).toLinearMap.comp (leftInvariant δ).toLinearMap =
      (@Derivation.toLinearMap R A R
          (inferInstance : CommSemiring R) (inferInstance : CommSemiring A)
          (inferInstance : AddCommMonoid R) (inferInstance : Algebra R A)
          (Module.compHom R (Bialgebra.counitAlgHom R A).toRingHom)
          (inferInstance : Module R R) δ) := by
  change (Bialgebra.counitAlgHom R A).toLinearMap.comp
    (WithConv.toConv (LinearMap.id : A →ₗ[R] A) *
      WithConv.toConv ((Algebra.linearMap R A).comp (@Derivation.toLinearMap R A R
          (inferInstance : CommSemiring R) (inferInstance : CommSemiring A)
          (inferInstance : AddCommMonoid R) (inferInstance : Algebra R A)
          (Module.compHom R (Bialgebra.counitAlgHom R A).toRingHom)
          (inferInstance : Module R R) δ))).ofConv = _
  rw [LinearMap.algHom_comp_convMul_distrib]
  have hη : (Bialgebra.counitAlgHom R A).toLinearMap.comp
      ((Algebra.linearMap R A).comp (@Derivation.toLinearMap R A R
          (inferInstance : CommSemiring R) (inferInstance : CommSemiring A)
          (inferInstance : AddCommMonoid R) (inferInstance : Algebra R A)
          (Module.compHom R (Bialgebra.counitAlgHom R A).toRingHom)
          (inferInstance : Module R R) δ)) = (@Derivation.toLinearMap R A R
          (inferInstance : CommSemiring R) (inferInstance : CommSemiring A)
          (inferInstance : AddCommMonoid R) (inferInstance : Algebra R A)
          (Module.compHom R (Bialgebra.counitAlgHom R A).toRingHom)
          (inferInstance : Module R R) δ) := by
    ext a
    simp
  have hε : WithConv.toConv ((Bialgebra.counitAlgHom R A).toLinearMap.comp
      (LinearMap.id : A →ₗ[R] A)) = (1 : WithConv (A →ₗ[R] R)) := by
    ext a
    simp
  rw [hη, hε, one_mul]

/-- Pointwise counit elimination for the left-invariant extension. -/
@[simp]
theorem counit_leftInvariant_apply (a : A) :
    counit (R := R) (leftInvariant δ a) = δ a :=
  LinearMap.congr_fun (counit_leftInvariant δ) a

/-- An ordinary derivation is determined by left-invariance and its counit value. -/
theorem leftInvariant_unique (D : Derivation R A A)
    (hΔ : (comul : A →ₗ[R] A ⊗[R] A).comp D.toLinearMap =
      (D.toLinearMap.lTensor A).comp comul)
    (hε : (Bialgebra.counitAlgHom R A).toLinearMap.comp D.toLinearMap =
      (@Derivation.toLinearMap R A R
        (inferInstance : CommSemiring R) (inferInstance : CommSemiring A)
        (inferInstance : AddCommMonoid R) (inferInstance : Algebra R A)
        (Module.compHom R (Bialgebra.counitAlgHom R A).toRingHom)
        (inferInstance : Module R R) δ)) :
    D = leftInvariant δ := by
  ext a
  have hΔa : comul (R := R) (D a) = D.toLinearMap.lTensor A (comul a) :=
    LinearMap.congr_fun hΔ a
  calc
    D a = TensorProduct.rid R A
        ((counit : A →ₗ[R] R).lTensor A (comul (D a))) := by simp
    _ = TensorProduct.rid R A
        ((counit : A →ₗ[R] R).lTensor A (D.toLinearMap.lTensor A (comul a))) := by
      rw [hΔa]
    _ = TensorProduct.rid R A ((@Derivation.toLinearMap R A R
        (inferInstance : CommSemiring R) (inferInstance : CommSemiring A)
        (inferInstance : AddCommMonoid R) (inferInstance : Algebra R A)
        (Module.compHom R (Bialgebra.counitAlgHom R A).toRingHom)
        (inferInstance : Module R R) δ).lTensor A (comul a)) := by
      rw [← LinearMap.lTensor_comp_apply]
      rw [show (counit : A →ₗ[R] R).comp D.toLinearMap =
        (@Derivation.toLinearMap R A R
          (inferInstance : CommSemiring R) (inferInstance : CommSemiring A)
          (inferInstance : AddCommMonoid R) (inferInstance : Algebra R A)
          (Module.compHom R (Bialgebra.counitAlgHom R A).toRingHom)
          (inferInstance : Module R R) δ) from hε]
    _ = leftInvariant δ a := (leftInvariant_apply δ a).symm

/-- A derivation is the extension of `δ` exactly when it is left-invariant and
its counit is `δ`. -/
theorem eq_leftInvariant_iff (D : Derivation R A A) :
    D = leftInvariant δ ↔
      (comul : A →ₗ[R] A ⊗[R] A).comp D.toLinearMap =
          (D.toLinearMap.lTensor A).comp comul ∧
        (Bialgebra.counitAlgHom R A).toLinearMap.comp D.toLinearMap =
          (@Derivation.toLinearMap R A R
            (inferInstance : CommSemiring R) (inferInstance : CommSemiring A)
            (inferInstance : AddCommMonoid R) (inferInstance : Algebra R A)
            (Module.compHom R (Bialgebra.counitAlgHom R A).toRingHom)
            (inferInstance : Module R R) δ) := by
  constructor
  · rintro rfl
    exact ⟨comul_leftInvariant δ, counit_leftInvariant δ⟩
  · rintro ⟨hΔ, hε⟩
    exact leftInvariant_unique δ D hΔ hε

/-- Distinct point derivations have distinct left-invariant extensions. -/
theorem leftInvariant_injective : Function.Injective (leftInvariant (R := R) (A := A)) := by
  intro δ₁ δ₂ h
  apply @Derivation.ext R A R _ _ _ _
    (Module.compHom R (Bialgebra.counitAlgHom R A).toRingHom)
    (inferInstance : Module R R) δ₁ δ₂
  intro a
  have ha := congrArg (fun D : Derivation R A A => counit (R := R) (D a)) h
  simpa only [counit_leftInvariant_apply] using ha

/-- Extending the zero point derivation gives the zero ordinary derivation. -/
@[simp]
theorem leftInvariant_zero : leftInvariant (R := R) (A := A) 0 = 0 := by
  ext a
  simp [leftInvariant_apply]

/-- The left-invariant extension preserves addition of point derivations. -/
@[simp]
theorem leftInvariant_add
    (δ₁ δ₂ : @Derivation R A R _ _ _ _
      (Module.compHom R (Bialgebra.counitAlgHom R A).toRingHom) _) :
    leftInvariant (δ₁ + δ₂) = leftInvariant δ₁ + leftInvariant δ₂ := by
  have h : (@Derivation.toLinearMap R A R
      (inferInstance : CommSemiring R) (inferInstance : CommSemiring A)
      (inferInstance : AddCommMonoid R) (inferInstance : Algebra R A)
      (Module.compHom R (Bialgebra.counitAlgHom R A).toRingHom)
      (inferInstance : Module R R) (δ₁ + δ₂)) = (@Derivation.toLinearMap R A R
      (inferInstance : CommSemiring R) (inferInstance : CommSemiring A)
      (inferInstance : AddCommMonoid R) (inferInstance : Algebra R A)
      (Module.compHom R (Bialgebra.counitAlgHom R A).toRingHom)
      (inferInstance : Module R R) δ₁) + (@Derivation.toLinearMap R A R
      (inferInstance : CommSemiring R) (inferInstance : CommSemiring A)
      (inferInstance : AddCommMonoid R) (inferInstance : Algebra R A)
      (Module.compHom R (Bialgebra.counitAlgHom R A).toRingHom)
      (inferInstance : Module R R) δ₂) := rfl
  ext a
  simp [leftInvariant_apply, h, Derivation.add_apply]

/-- The left-invariant extension as an `R`-linear map. The source module is
Mathlib's derivation module for the counit coefficient action, with scalar
commutation obtained by pulling back multiplication on `R`. Its addition and
scalar laws are available through `map_add` and `map_smul`. -/
noncomputable def leftInvariantLinearMap :
    @LinearMap R R _ _ (RingHom.id R)
      (@Derivation R A R _ _ _ _
        (Module.compHom R (Bialgebra.counitAlgHom R A).toRingHom) _)
      (Derivation R A A) _ _
      (@Derivation.instModule R A R _ _ _ _
        (Module.compHom R (Bialgebra.counitAlgHom R A).toRingHom)
        (inferInstance : Module R R) R _ (inferInstance : Module R R)
        (smulCommClass_self R R)
        (SMul.comp.smulCommClass' (α := R) (β := R) (M := R)
          (Bialgebra.counitAlgHom R A))) _ := by
  let : @SMulCommClass R A R _
      (Module.compHom R
        (Bialgebra.counitAlgHom R A).toRingHom).toDistribMulAction.toMulAction.toSMul :=
    SMul.comp.smulCommClass' (α := R) (β := R) (M := R) (Bialgebra.counitAlgHom R A)
  refine
    { toFun := leftInvariant
      map_add' := leftInvariant_add
      map_smul' := ?_ }
  intro r δ
  have h : (@Derivation.toLinearMap R A R
      (inferInstance : CommSemiring R) (inferInstance : CommSemiring A)
      (inferInstance : AddCommMonoid R) (inferInstance : Algebra R A)
      (Module.compHom R (Bialgebra.counitAlgHom R A).toRingHom)
      (inferInstance : Module R R) (r • δ)) = r • (@Derivation.toLinearMap R A R
      (inferInstance : CommSemiring R) (inferInstance : CommSemiring A)
      (inferInstance : AddCommMonoid R) (inferInstance : Algebra R A)
      (Module.compHom R (Bialgebra.counitAlgHom R A).toRingHom)
      (inferInstance : Module R R) δ) := rfl
  ext a
  simp [leftInvariant_apply, h, Derivation.smul_apply]

/-- The bundled linear extension evaluates to `leftInvariant`. -/
@[simp]
theorem leftInvariantLinearMap_apply :
    leftInvariantLinearMap (R := R) (A := A) δ = leftInvariant δ := rfl

end Derivation
