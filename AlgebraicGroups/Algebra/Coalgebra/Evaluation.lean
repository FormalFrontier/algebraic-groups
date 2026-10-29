/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.RightComodule

/-!
# Scalar-extension evaluation of a right coaction

`Coalgebra.RightComodule.evaluate` associates an `A`-linear endomorphism of
`A ⊗[K] V` to a specified right coaction on `V` and a linear map `C →ₗ[K] A`.
A coaction term `vᵢ ⊗ cᵢ` contributes `φ cᵢ ⊗ vᵢ` on a one-tensor.
The coalgebra need not be an algebra, and the input need not preserve products
or the unit. The counit gives the identity endomorphism.

Evaluation is natural in the scalar algebra and in colinear maps. It preserves
the scalar-extension image of every image-stable submodule, without flatness or
a coaction on the submodule subtype. For algebra-homomorphism inputs, the
identity and maximum-universe stability criteria reuse the evaluation criteria
for right comodules. No multiplication law on coefficient inputs or point action
is constructed here.

## References

* Mathlib's tensor-map and scalar-extension lift formalizations.
* The right-comodule evaluation and image-stability formalization in
  `AlgebraicGroups.Algebra.Coalgebra.RightComodule`.
* M. E. Sweedler, *Hopf Algebras*, W. A. Benjamin, 1969, for the right-coaction
  convention and image stability (bibliographic credit).
-/

@[expose] public section

universe u c v a b w

open scoped TensorProduct

namespace Coalgebra.RightComodule

variable {K : Type u} {C : Type c} {V : Type v}
variable [CommSemiring K] [AddCommMonoid C] [Module K C] [Coalgebra K C]
variable [AddCommMonoid V] [Module K V]
variable {A : Type a} [CommSemiring A] [Algebra K A]

/-- Evaluate a right coaction against a coefficient linear map, then extend
scalars. The coalgebra factor is commuted to the left before evaluation. -/
def evaluate (X : RightComodule K C V) (φ : C →ₗ[K] A) :
    Module.End A (A ⊗[K] V) :=
  LinearMap.liftBaseChange A
    ((TensorProduct.map φ (LinearMap.id : V →ₗ[K] V)).comp
      ((TensorProduct.comm K V C).toLinearMap.comp X.coaction))

/-- Evaluation on a pure tensor is the scalar multiple of the evaluated coaction. -/
@[simp] theorem evaluate_tmul (X : RightComodule K C V) (φ : C →ₗ[K] A)
    (a : A) (v : V) :
    X.evaluate φ (a ⊗ₜ[K] v) =
      a • TensorProduct.map φ (LinearMap.id : V →ₗ[K] V)
        (TensorProduct.comm K V C (X.coaction v)) := rfl

/-- On a one-tensor, evaluation applies the coefficient map to the commuted coaction. -/
theorem evaluate_one_tmul (X : RightComodule K C V) (φ : C →ₗ[K] A) (v : V) :
    X.evaluate φ (1 ⊗ₜ[K] v) =
      TensorProduct.map φ (LinearMap.id : V →ₗ[K] V)
        (TensorProduct.comm K V C (X.coaction v)) := by
  rw [evaluate_tmul, one_smul]

/-- Evaluation commutes with change of scalar algebra. The tensor transport is
only `K`-linear; neither scalar algebra is assumed to act on the other. -/
theorem evaluate_naturality (X : RightComodule K C V) (φ : C →ₗ[K] A)
    {B : Type b} [CommSemiring B] [Algebra K B] (q : A →ₐ[K] B) :
    (TensorProduct.map q.toLinearMap (LinearMap.id : V →ₗ[K] V)).comp
        ((X.evaluate φ).restrictScalars K) =
      ((X.evaluate (q.toLinearMap.comp φ)).restrictScalars K).comp
        (TensorProduct.map q.toLinearMap (LinearMap.id : V →ₗ[K] V)) := by
  have h (a : A) :
      (TensorProduct.map q.toLinearMap (LinearMap.id : V →ₗ[K] V)).comp
          (a • TensorProduct.map φ (LinearMap.id : V →ₗ[K] V)) =
        q a • TensorProduct.map (q.toLinearMap.comp φ) (LinearMap.id : V →ₗ[K] V) := by
    apply TensorProduct.ext'
    intro c v
    simp [TensorProduct.smul_tmul', smul_eq_mul]
  apply TensorProduct.ext'
  intro a v
  simpa only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    evaluate_tmul, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
    LinearMap.id_apply, LinearMap.smul_apply] using
      LinearMap.congr_fun (h a) (TensorProduct.comm K V C (X.coaction v))

/-- Elementwise scalar-algebra naturality, on an arbitrary tensor. -/
theorem evaluate_naturality_apply (X : RightComodule K C V) (φ : C →ₗ[K] A)
    {B : Type b} [CommSemiring B] [Algebra K B] (q : A →ₐ[K] B) (z : A ⊗[K] V) :
    TensorProduct.map q.toLinearMap (LinearMap.id : V →ₗ[K] V) (X.evaluate φ z) =
      X.evaluate (q.toLinearMap.comp φ)
        (TensorProduct.map q.toLinearMap (LinearMap.id : V →ₗ[K] V) z) :=
  LinearMap.congr_fun (X.evaluate_naturality φ q) z

/-- Evaluation against the counit followed by the scalar algebra map is the identity. -/
@[simp] theorem evaluate_counit (X : RightComodule K C V) :
    X.evaluate ((Algebra.linearMap K A).comp (counit (R := K) (A := C))) =
      LinearMap.id := by
  have h :
      (TensorProduct.map ((Algebra.linearMap K A).comp (counit (R := K) (A := C)))
        (LinearMap.id : V →ₗ[K] V)).comp (TensorProduct.comm K V C).toLinearMap =
      (TensorProduct.mk K A V 1).comp
        ((TensorProduct.rid K V).toLinearMap.comp
          ((counit (R := K) (A := C)).lTensor V)) := by
    apply TensorProduct.ext'
    intro v c
    change algebraMap K A (counit (R := K) (A := C) c) ⊗ₜ[K] v =
      (1 : A) ⊗ₜ[K] (counit (R := K) (A := C) c • v)
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  apply TensorProduct.AlgebraTensorModule.ext
  intro a v
  rw [evaluate_tmul]
  change a • ((TensorProduct.map
      ((Algebra.linearMap K A).comp (counit (R := K) (A := C)))
      (LinearMap.id : V →ₗ[K] V)).comp (TensorProduct.comm K V C).toLinearMap)
        (X.coaction v) = a ⊗ₜ[K] v
  rw [h]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.mk_apply]
  rw [X.rid_counit_coaction]
  simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

omit [Coalgebra K C] in
private theorem map_comm_mem_baseChange (U : Submodule K V) (φ : C →ₗ[K] A)
    {y : V ⊗[K] C} (hy : y ∈ LinearMap.range (U.subtype.rTensor C)) :
    TensorProduct.map φ (LinearMap.id : V →ₗ[K] V)
      (TensorProduct.comm K V C y) ∈ U.baseChange A := by
  obtain ⟨t, rfl⟩ := hy
  refine ⟨TensorProduct.map φ (LinearMap.id : U →ₗ[K] U)
    (TensorProduct.comm K U C t), ?_⟩
  change TensorProduct.map (LinearMap.id : A →ₗ[K] A) U.subtype
      (TensorProduct.map φ (LinearMap.id : U →ₗ[K] U)
        (TensorProduct.comm K U C t)) = _
  simp only [LinearMap.rTensor_def, TensorProduct.map_comm, TensorProduct.map_map,
    LinearMap.id_comp, LinearMap.comp_id]

/-- A stable submodule's scalar-extension image is preserved by every linear
coefficient evaluation. No injectivity of the tensor inclusion is needed. -/
theorem IsStable.evaluate_mem_baseChange {X : RightComodule K C V}
    {U : Submodule K V} (hU : X.IsStable U) (φ : C →ₗ[K] A)
    {z : A ⊗[K] V} (hz : z ∈ U.baseChange A) :
    X.evaluate φ z ∈ U.baseChange A := by
  have hle : U.baseChange A ≤ (U.baseChange A).comap (X.evaluate φ) := by
    calc
      U.baseChange A = Submodule.span A (U.map (TensorProduct.mk K A V 1)) :=
        Submodule.baseChange_eq_span A U
      _ ≤ (U.baseChange A).comap (X.evaluate φ) := by
        apply Submodule.span_le.mpr
        rintro _ ⟨v, hv, rfl⟩
        change X.evaluate φ (1 ⊗ₜ[K] v) ∈ U.baseChange A
        rw [evaluate_one_tmul]
        exact map_comm_mem_baseChange U φ (hU.coaction_mem_range v hv)
  exact hle hz

/-- On the scalar comodule, a linear input acts by multiplication by its value
at one. In particular, a nonunital input need not give the identity. -/
theorem scalar_evaluate (φ : K →ₗ[K] A) :
    (scalar K V).evaluate φ = φ 1 • (LinearMap.id : Module.End A (A ⊗[K] V)) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a v
  simp [evaluate_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_comm]

end Coalgebra.RightComodule

namespace Coalgebra.RightComoduleHom

variable {K : Type u} {C : Type c} {V : Type v} {W : Type w}
variable [CommSemiring K] [AddCommMonoid C] [Module K C] [Coalgebra K C]
variable [AddCommMonoid V] [Module K V] [AddCommMonoid W] [Module K W]
variable {A : Type a} [CommSemiring A] [Algebra K A]
variable {X : RightComodule K C V} {Y : RightComodule K C W}

/-- A colinear map commutes with the coaction in coefficient-first tensor order. -/
theorem comm_coaction_apply (l : RightComoduleHom X Y) (v : V) :
    TensorProduct.comm K W C (Y.coaction (l v)) =
      TensorProduct.map (LinearMap.id : C →ₗ[K] C) l.toLinearMap
        (TensorProduct.comm K V C (X.coaction v)) := by
  rw [l.colinear_apply]
  exact (TensorProduct.map_comm (LinearMap.id : C →ₗ[K] C) l.toLinearMap
    (X.coaction v)).symm

/-- The scalar extension of the underlying colinear map intertwines evaluations. -/
theorem baseChange_comp_evaluate (l : RightComoduleHom X Y) (φ : C →ₗ[K] A) :
    l.toLinearMap.baseChange A ∘ₗ X.evaluate φ =
      Y.evaluate φ ∘ₗ l.toLinearMap.baseChange A := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a v
  simp only [LinearMap.comp_apply, RightComodule.evaluate_tmul,
    LinearMap.baseChange_tmul, map_smul, toLinearMap_apply, l.comm_coaction_apply]
  congr 1
  change TensorProduct.map (LinearMap.id : A →ₗ[K] A) l.toLinearMap
    (TensorProduct.map φ (LinearMap.id : V →ₗ[K] V)
      (TensorProduct.comm K V C (X.coaction v))) = _
  simp only [TensorProduct.map_map, LinearMap.id_comp, LinearMap.comp_id]

/-- Elementwise intertwining on an arbitrary scalar-extended vector. -/
theorem baseChange_evaluate_apply (l : RightComoduleHom X Y) (φ : C →ₗ[K] A)
    (z : A ⊗[K] V) :
    l.toLinearMap.baseChange A (X.evaluate φ z) =
      Y.evaluate φ (l.toLinearMap.baseChange A z) :=
  LinearMap.congr_fun (l.baseChange_comp_evaluate φ) z

end Coalgebra.RightComoduleHom

namespace Coalgebra.RightComodule

variable {K : Type u} {C : Type c} {V : Type v}
variable [CommSemiring K] [CommSemiring C] [Algebra K C] [Coalgebra K C]
variable [AddCommMonoid V] [Module K V]
variable (X : RightComodule K C V)

/-- For an algebra-homomorphism input, evaluation is the scalar-extension
expression used in the algebra-valued evaluation criteria. -/
theorem evaluate_algHom {A : Type a} [CommSemiring A] [Algebra K A] (α : C →ₐ[K] A) :
    X.evaluate α.toLinearMap =
      LinearMap.liftBaseChange A
        ((TensorProduct.map α.toLinearMap (LinearMap.id : V →ₗ[K] V)).comp
          ((TensorProduct.comm K V C).toLinearMap.comp X.coaction)) := rfl

/-- Identity evaluation detects image stability for the same right coaction. -/
theorem isStable_iff_evaluate_id (U : Submodule K V) :
    X.IsStable U ↔ ∀ z ∈ U.baseChange C,
      X.evaluate (AlgHom.id K C).toLinearMap z ∈ U.baseChange C :=
  X.isStable_iff_id_evaluation_mem_baseChange U

/-- Algebra-homomorphism evaluations in a compatible maximum universe detect
image stability; the forward evaluation API itself has an independent universe. -/
theorem isStable_iff_forall_evaluate (U : Submodule K V) :
    X.IsStable U ↔
      ∀ (A : Type (max c a)) [CommSemiring A] [Algebra K A] (α : C →ₐ[K] A),
        ∀ z ∈ U.baseChange A, X.evaluate α.toLinearMap z ∈ U.baseChange A :=
  X.isStable_iff_forall_evaluation_mem_baseChange U

end Coalgebra.RightComodule
