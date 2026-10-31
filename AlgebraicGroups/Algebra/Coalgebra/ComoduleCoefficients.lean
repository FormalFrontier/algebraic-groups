/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.RightComodule
public import AlgebraicGroups.Algebra.Coalgebra.Subcoalgebra.Hom
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Coefficient coalgebras of right comodules

For a specified right coaction `X` of a coalgebra `C` on a module `M`, a
coefficient is obtained by evaluating a linear functional on the first tensor
factor of `X.coaction m`. The coefficient span uses all linear functionals on
`M` and all elements of `M`; no basis or finite-generation hypothesis is part
of its definition. Coefficients and their span are defined over a commutative
semiring. The span is the range of `coefficientTensor` on the tensor product
of the dual with the comodule. A finite tensor domain gives finite generation;
in particular it suffices that the comodule and its dual are both finite.
Over a Noetherian commutative ring, finiteness of the comodule alone suffices.
Every functional gives a morphism to the regular comodule, and composition
with the counit identifies these morphisms with the linear dual.
For a basis `b`, apply `TensorProduct.equivFinsuppOfBasisLeft b` directly to
`X.coaction m` to obtain the finitely supported coefficient column. Its stock
application and inverse formulas evaluate the coefficients and reconstruct the
original coaction; no finite-support assertion about a whole row is needed.
The matrix coefficients of any supplied basis span the all-dual coefficient
span, even for an infinite basis index. A supplied basis with finite index gives
finite generation over a commutative semiring. For a finite basis index, the
finite-column coproduct specializes to the usual matrix-coefficient sum.

Under a right-comodule morphism, coefficients pull back along the underlying
linear map. Surjections decrease coefficient spans, bijections preserve them,
and over a field injections increase them, since linear functionals extend
from subspaces. The corresponding statements hold for the underlying submodules
of coefficient subcoalgebras.

The regular right comodule has full coefficient span: evaluation
at the counit recovers every element of the coalgebra.

Over a field, `coefficientSubcoalgebra` has exactly this coefficient span as its
underlying submodule. Corestriction of the coacting coalgebra uses the tensor
inclusion `M ⊗ D → M ⊗ C`, rather than a comodule morphism with a fixed coacting
coalgebra. The inclusion equation characterizes the corestricted coaction.
Changing this corestricted coacting coalgebra back along its inclusion recovers
the original specified comodule.
The coefficient span is contained in the underlying submodule of `D` exactly
when the coaction factors through this tensor inclusion.

The field constructions use the ambient coalgebra's given additive-group
structure, matching the `Subcoalgebra` interface. Additive inverses in a module
over a field are determined by scalar multiplication by `-1`, so this interface
imposes no additional mathematical assumption. The coacted-on module retains
only its additive commutative monoid and module structures.

## References

* M. E. Sweedler, *Hopf Algebras*, W. A. Benjamin, 1969, for the classical
  coefficient-coalgebra construction (bibliographic credit).
* Mathlib's tensor-product, linear-map, and module-finiteness formalizations.
-/

@[expose] public section

universe u v w z

open scoped TensorProduct

namespace Coalgebra.RightComodule

section CommSemiring

variable {K : Type u} {C : Type v} {M : Type w}
variable [CommSemiring K] [AddCommMonoid C] [Module K C] [Coalgebra K C]
variable [AddCommMonoid M] [Module K M]

/-- A coefficient of a right coaction, obtained by evaluating its first tensor factor. -/
def coefficient (X : RightComodule K C M) (ell : M →ₗ[K] K) (m : M) : C :=
  _root_.TensorProduct.lid K C (ell.rTensor C (X.coaction m))

/-- The defining all-dual evaluation formula for a coefficient. -/
theorem coefficient_eq (X : RightComodule K C M) (ell : M →ₗ[K] K) (m : M) :
    X.coefficient ell m = _root_.TensorProduct.lid K C (ell.rTensor C (X.coaction m)) :=
  rfl

/-- The linear map on the dual tensor the comodule that evaluates coefficients. -/
def coefficientTensor (X : RightComodule K C M) :
    (Module.Dual K M) ⊗[K] M →ₗ[K] C :=
  TensorProduct.lift
    (LinearMap.llcomp K M (K ⊗[K] C) C (_root_.TensorProduct.lid K C).toLinearMap ∘ₗ
      (LinearMap.llcomp K M (M ⊗[K] C) (K ⊗[K] C)).flip X.coaction ∘ₗ
      LinearMap.rTensorHom C)

/-- On a pure tensor the coefficient map is the all-dual coefficient evaluation. -/
@[simp] theorem coefficientTensor_apply_tmul (X : RightComodule K C M)
    (ell : Module.Dual K M) (m : M) :
    X.coefficientTensor (ell ⊗ₜ[K] m) = X.coefficient ell m :=
  rfl

/-- Contracting the first factor of coassociativity makes every coefficient map
right-colinear with the regular coaction. -/
theorem comul_coefficient_eq_rTensor (X : RightComodule K C M)
    (ell : M →ₗ[K] K) (m : M) :
    comul (R := K) (X.coefficient ell m) =
      (((_root_.TensorProduct.lid K C).toLinearMap ∘ₗ ell.rTensor C) ∘ₗ
        X.coaction).rTensor C (X.coaction m) := by
  let q : M ⊗[K] C →ₗ[K] C :=
    (_root_.TensorProduct.lid K C).toLinearMap ∘ₗ ell.rTensor C
  let q₂ : M ⊗[K] (C ⊗[K] C) →ₗ[K] C ⊗[K] C :=
    (_root_.TensorProduct.lid K (C ⊗[K] C)).toLinearMap ∘ₗ ell.rTensor (C ⊗[K] C)
  have hΔ : comul (R := K) ∘ₗ q = q₂ ∘ₗ (comul (R := K)).lTensor M := by
    refine TensorProduct.ext' fun x c => ?_
    simp [q, q₂]
  have ha : q₂ ∘ₗ (_root_.TensorProduct.assoc K M C C).toLinearMap = q.rTensor C := by
    refine TensorProduct.ext (TensorProduct.ext ?_)
    ext x c d
    simp [q, q₂, TensorProduct.smul_tmul']
  calc
    comul (R := K) (X.coefficient ell m) =
        q₂ ((comul (R := K)).lTensor M (X.coaction m)) :=
      LinearMap.congr_fun hΔ (X.coaction m)
    _ = q₂ (_root_.TensorProduct.assoc K M C C (X.coaction.rTensor C (X.coaction m))) := by
      rw [X.coassoc_apply]
    _ = q.rTensor C (X.coaction.rTensor C (X.coaction m)) :=
      LinearMap.congr_fun ha _
    _ = (q ∘ₗ X.coaction).rTensor C (X.coaction m) :=
      (LinearMap.rTensor_comp_apply (M := C) (g := q) (f := X.coaction)
        (X.coaction m)).symm

/-- Applying the counit to a coefficient recovers the original functional. -/
@[simp] theorem counit_coefficient (X : RightComodule K C M)
    (ell : M →ₗ[K] K) (m : M) :
    counit (R := K) (X.coefficient ell m) = ell m := by
  have h : counit (R := K) ∘ₗ (_root_.TensorProduct.lid K C).toLinearMap ∘ₗ
        ell.rTensor C =
      ell ∘ₗ (_root_.TensorProduct.rid K M).toLinearMap ∘ₗ
        (counit (R := K)).lTensor M := by
    refine TensorProduct.ext' fun x c ↦ ?_
    simp [mul_comm]
  calc
    counit (R := K) (X.coefficient ell m) =
        ell (_root_.TensorProduct.rid K M ((counit (R := K)).lTensor M (X.coaction m))) :=
      LinearMap.congr_fun h (X.coaction m)
    _ = ell m := congrArg ell (X.rid_counit_coaction m)

/-- A functional on a right comodule determines a morphism to the regular comodule. -/
def coefficientHom (X : RightComodule K C M) (ell : M →ₗ[K] K) :
    RightComoduleHom X (regular K C) where
  toLinearMap := (_root_.TensorProduct.lid K C).toLinearMap ∘ₗ ell.rTensor C ∘ₗ X.coaction
  colinear := by
    apply LinearMap.ext
    intro m
    exact X.comul_coefficient_eq_rTensor ell m

/-- Evaluation of a coefficient morphism is the existing coefficient construction. -/
@[simp] theorem coefficientHom_apply (X : RightComodule K C M)
    (ell : M →ₗ[K] K) (m : M) :
    X.coefficientHom ell m = X.coefficient ell m := by
  rfl

/-- The underlying linear map contracts the first factor of the specified coaction. -/
@[simp] theorem coefficientHom_toLinearMap (X : RightComodule K C M)
    (ell : M →ₗ[K] K) :
    (X.coefficientHom ell).toLinearMap =
      (_root_.TensorProduct.lid K C).toLinearMap ∘ₗ ell.rTensor C ∘ₗ X.coaction := by
  rfl

/-- The counit is a left inverse to the coefficient-morphism construction. -/
@[simp↓] theorem counit_comp_coefficientHom (X : RightComodule K C M)
    (ell : M →ₗ[K] K) :
    counit (R := K) ∘ₗ (X.coefficientHom ell).toLinearMap = ell := by
  apply LinearMap.ext
  intro m
  exact X.counit_coefficient ell m

/-- A morphism to the regular comodule is recovered from its counit composite. -/
@[simp] theorem coefficientHom_counit_comp (X : RightComodule K C M)
    (g : RightComoduleHom X (regular K C)) :
    X.coefficientHom (counit (R := K) ∘ₗ g.toLinearMap) = g := by
  apply RightComoduleHom.ext
  intro m
  change _root_.TensorProduct.lid K C
    ((counit (R := K) ∘ₗ g.toLinearMap).rTensor C (X.coaction m)) = g m
  rw [LinearMap.rTensor_comp_apply, ← g.colinear_apply]
  simp only [regular_coaction, Coalgebra.rTensor_counit_comul,
    _root_.TensorProduct.lid_tmul, one_smul]

/-- On the regular comodule the counit gives the identity coefficient morphism. -/
@[simp] theorem coefficientHom_regular_counit :
    (regular K C).coefficientHom (counit (R := K)) =
      RightComoduleHom.id (regular K C) := by
  apply RightComoduleHom.ext
  intro c
  change _root_.TensorProduct.lid K C ((counit (R := K)).rTensor C
    (comul (R := K) c)) = c
  simp only [Coalgebra.rTensor_counit_comul, _root_.TensorProduct.lid_tmul, one_smul]

/-- Morphisms to the regular comodule correspond to linear functionals by the counit.
The inverse sends a functional to its coefficient morphism. -/
def homRegularEquiv (X : RightComodule K C M) :
    RightComoduleHom X (regular K C) ≃ (M →ₗ[K] K) where
  toFun g := counit (R := K) ∘ₗ g.toLinearMap
  invFun ell := X.coefficientHom ell
  left_inv := by
    intro g
    exact X.coefficientHom_counit_comp g
  right_inv := by
    intro ell
    exact X.counit_comp_coefficientHom ell

/-- The regular-target correspondence takes the counit composite. -/
@[simp] theorem homRegularEquiv_apply (X : RightComodule K C M)
    (g : RightComoduleHom X (regular K C)) :
    X.homRegularEquiv g = counit (R := K) ∘ₗ g.toLinearMap := by
  rfl

/-- The inverse regular-target correspondence is the coefficient morphism. -/
@[simp] theorem homRegularEquiv_symm_apply (X : RightComodule K C M)
    (ell : M →ₗ[K] K) :
    X.homRegularEquiv.symm ell = X.coefficientHom ell := by
  rfl

/-- The correspondence reads a coefficient morphism back as its functional. -/
@[simp↓] theorem homRegularEquiv_coefficientHom (X : RightComodule K C M)
    (ell : M →ₗ[K] K) :
    X.homRegularEquiv (X.coefficientHom ell) = ell := by
  exact X.counit_comp_coefficientHom ell

/-- Regular-target morphisms are determined by their counit composites. -/
theorem hom_regular_ext (X : RightComodule K C M)
    {g h : RightComoduleHom X (regular K C)}
    (heq : counit (R := K) ∘ₗ g.toLinearMap = counit (R := K) ∘ₗ h.toLinearMap) :
    g = h := by
  exact X.homRegularEquiv.injective heq

/-- The identity of the regular comodule corresponds to its counit. -/
@[simp↓] theorem homRegularEquiv_regular_id :
    (regular K C).homRegularEquiv (RightComoduleHom.id (regular K C)) =
      counit (R := K) := by
  apply LinearMap.ext
  intro c
  rfl

section Naturality

variable {N : Type z} [AddCommMonoid N] [Module K N]
variable (X : RightComodule K C M) (Y : RightComodule K C N)

/-- Coefficient morphisms commute with precomposition by a comodule morphism. -/
theorem coefficientHom_comp (ell : N →ₗ[K] K) (f : RightComoduleHom X Y) :
    X.coefficientHom (ell ∘ₗ f.toLinearMap) = (Y.coefficientHom ell).comp f := by
  apply X.hom_regular_ext
  rw [X.counit_comp_coefficientHom]
  change ell ∘ₗ f.toLinearMap =
    counit (R := K) ∘ₗ ((Y.coefficientHom ell).toLinearMap ∘ₗ f.toLinearMap)
  rw [← LinearMap.comp_assoc, Y.counit_comp_coefficientHom]

/-- The regular-target correspondence is natural in the source comodule. -/
theorem homRegularEquiv_comp (g : RightComoduleHom Y (regular K C))
    (f : RightComoduleHom X Y) :
    X.homRegularEquiv (g.comp f) = Y.homRegularEquiv g ∘ₗ f.toLinearMap := by
  change counit (R := K) ∘ₗ (g.toLinearMap ∘ₗ f.toLinearMap) =
    (counit (R := K) ∘ₗ g.toLinearMap) ∘ₗ f.toLinearMap
  rw [LinearMap.comp_assoc]

/-- The inverse correspondence is natural in the source comodule. -/
theorem homRegularEquiv_symm_comp (ell : N →ₗ[K] K) (f : RightComoduleHom X Y) :
    X.homRegularEquiv.symm (ell ∘ₗ f.toLinearMap) =
      (Y.homRegularEquiv.symm ell).comp f := by
  exact coefficientHom_comp X Y ell f

end Naturality

/-- A value of the canonical finite coaction column is the corresponding coefficient. -/
theorem equivFinsuppOfBasisLeft_coaction_apply {ι : Type*} [DecidableEq ι]
    (X : RightComodule K C M) (b : Module.Basis ι K M) (m : M) (i : ι) :
    TensorProduct.equivFinsuppOfBasisLeft b (X.coaction m) i =
      X.coefficient (b.coord i) m :=
  TensorProduct.equivFinsuppOfBasisLeft_apply b (X.coaction m) i

/-- The canonical finite column reconstructs the same specified coaction.
The supplied basis index need not be finite. -/
theorem coaction_eq_sum_basis {ι : Type*} [DecidableEq ι]
    (X : RightComodule K C M) (b : Module.Basis ι K M) (m : M) :
    X.coaction m = (TensorProduct.equivFinsuppOfBasisLeft b (X.coaction m)).sum
      (fun i c ↦ b i ⊗ₜ[K] c) := by
  symm
  simpa only [TensorProduct.equivFinsuppOfBasisLeft_symm_apply] using
    (TensorProduct.equivFinsuppOfBasisLeft b).symm_apply_apply (X.coaction m)

/-- Applying the counit to a coaction-column entry recovers the original coordinate. -/
theorem counit_equivFinsuppOfBasisLeft_coaction_apply {ι : Type*} [DecidableEq ι]
    (X : RightComodule K C M) (b : Module.Basis ι K M) (m : M) (i : ι) :
    counit (R := K) (TensorProduct.equivFinsuppOfBasisLeft b (X.coaction m) i) =
      b.coord i m := by
  rw [X.equivFinsuppOfBasisLeft_coaction_apply, X.counit_coefficient]

/-- An arbitrary coefficient has a coproduct expansion over the finite support of
its original coaction column, without a finite-index hypothesis. -/
theorem comul_coefficient_eq_sum_coaction {ι : Type*} [DecidableEq ι]
    (X : RightComodule K C M) (b : Module.Basis ι K M)
    (ell : M →ₗ[K] K) (m : M) :
    comul (R := K) (X.coefficient ell m) =
      (TensorProduct.equivFinsuppOfBasisLeft b (X.coaction m)).sum
        (fun j c ↦ X.coefficient ell (b j) ⊗ₜ[K] c) := by
  let T := (((_root_.TensorProduct.lid K C).toLinearMap ∘ₗ ell.rTensor C) ∘ₗ
    X.coaction).rTensor C
  calc
    comul (R := K) (X.coefficient ell m) = T (X.coaction m) :=
      X.comul_coefficient_eq_rTensor ell m
    _ = T ((TensorProduct.equivFinsuppOfBasisLeft b (X.coaction m)).sum
        (fun j c ↦ b j ⊗ₜ[K] c)) := congrArg T (X.coaction_eq_sum_basis b m)
    _ = (TensorProduct.equivFinsuppOfBasisLeft b (X.coaction m)).sum
        (fun j c ↦ X.coefficient ell (b j) ⊗ₜ[K] c) := by
      simp [T, Finsupp.sum, map_sum, coefficient_eq]

/-- Basis coefficients have the original coaction's finite column expansion under
comultiplication; the fixed index occurs in the first tensor factor. -/
theorem comul_coefficient_coord {ι : Type*} [DecidableEq ι]
    (X : RightComodule K C M) (b : Module.Basis ι K M) (i : ι) (m : M) :
    comul (R := K) (X.coefficient (b.coord i) m) =
      (TensorProduct.equivFinsuppOfBasisLeft b (X.coaction m)).sum
        (fun j c ↦ X.coefficient (b.coord i) (b j) ⊗ₜ[K] c) :=
  X.comul_coefficient_eq_sum_coaction b (b.coord i) m

/-- The counit of a basis matrix coefficient is the Kronecker delta, with no
finiteness assumption on the basis index. -/
@[simp↓] theorem counit_coefficient_basis {ι : Type*} [DecidableEq ι]
    (X : RightComodule K C M) (b : Module.Basis ι K M) (i j : ι) :
    counit (R := K) (X.coefficient (b.coord i) (b j)) =
      if i = j then 1 else 0 := by
  rw [X.counit_coefficient]
  simp [Module.Basis.coord_apply, Finsupp.single_apply, eq_comm]

/-- For a finite basis, the column expansion becomes the usual matrix-coefficient
comultiplication formula. -/
theorem comul_coefficient_basis {ι : Type*} [Fintype ι]
    (X : RightComodule K C M) (b : Module.Basis ι K M) (i j : ι) :
    comul (R := K) (X.coefficient (b.coord i) (b j)) =
      ∑ k, X.coefficient (b.coord i) (b k) ⊗ₜ[K] X.coefficient (b.coord k) (b j) := by
  classical
  rw [X.comul_coefficient_coord b i (b j),
    Finsupp.sum_fintype _ _ (fun _ ↦ by simp)]
  simp only [equivFinsuppOfBasisLeft_coaction_apply]

/-- The submodule spanned by all coefficients of a specified right coaction. -/
def coefficientSpan (X : RightComodule K C M) : Submodule K C :=
  Submodule.span K (Set.range (Function.uncurry X.coefficient))

/-- The coefficient span is the span of the exact range of all-dual evaluation. -/
theorem coefficientSpan_eq_span (X : RightComodule K C M) :
    X.coefficientSpan = Submodule.span K (Set.range (Function.uncurry X.coefficient)) :=
  rfl

/-- The range of the tensor coefficient map is the all-dual coefficient span. -/
theorem range_coefficientTensor (X : RightComodule K C M) :
    LinearMap.range X.coefficientTensor = X.coefficientSpan := by
  rw [LinearMap.range_eq_map,
    ← TensorProduct.map₂_mk_top_top_eq_top K (Module.Dual K M) M,
    Submodule.map_map₂, Submodule.map₂_eq_span_image2, coefficientSpan_eq_span]
  congr 1
  ext c
  constructor
  · rintro ⟨ell, _, m, _, rfl⟩
    exact ⟨(ell, m), (X.coefficientTensor_apply_tmul ell m).symm⟩
  · rintro ⟨⟨ell, m⟩, rfl⟩
    exact ⟨ell, trivial, m, trivial, X.coefficientTensor_apply_tmul ell m⟩

/-- A finite dual-tensor domain gives a finitely generated coefficient span. -/
theorem coefficientSpan_fg_of_finite_tensor
    [Module.Finite K ((Module.Dual K M) ⊗[K] M)]
    (X : RightComodule K C M) : X.coefficientSpan.FG := by
  rw [← X.range_coefficientTensor]
  exact Submodule.fg_range X.coefficientTensor

/-- Finite generation of the comodule and its dual gives a finite coefficient span. -/
theorem coefficientSpan_fg_of_finite
    [Module.Finite K M] [Module.Finite K (Module.Dual K M)]
    (X : RightComodule K C M) : X.coefficientSpan.FG :=
  X.coefficientSpan_fg_of_finite_tensor

/-- Every coefficient belongs to the coefficient span. -/
theorem coefficient_mem_coefficientSpan (X : RightComodule K C M)
    (ell : M →ₗ[K] K) (m : M) : X.coefficient ell m ∈ X.coefficientSpan :=
  Submodule.subset_span ⟨(ell, m), rfl⟩

/-- The coefficients of the regular right comodule span the whole coalgebra. -/
@[simp] theorem coefficientSpan_regular :
    (regular K C).coefficientSpan = (⊤ : Submodule K C) := by
  apply Submodule.eq_top_iff'.mpr
  intro c
  simpa only [coefficient, regular_coaction, Coalgebra.rTensor_counit_comul,
    _root_.TensorProduct.lid_tmul, one_smul] using
    (regular K C).coefficient_mem_coefficientSpan (counit (R := K)) c

/-- Containment of the coefficient span is equivalent to containment of all coefficients. -/
theorem coefficientSpan_le_iff (X : RightComodule K C M) (S : Submodule K C) :
    X.coefficientSpan ≤ S ↔ ∀ (ell : M →ₗ[K] K) (m : M), X.coefficient ell m ∈ S := by
  constructor
  · intro h ell m
    exact h (X.coefficient_mem_coefficientSpan ell m)
  · intro h
    apply Submodule.span_le.mpr
    rintro c ⟨⟨ell, m⟩, rfl⟩
    exact h ell m

end CommSemiring

/-- Over a Noetherian commutative ring, a finite comodule has a finitely generated
coefficient span. No freeness or chosen basis is required. -/
theorem coefficientSpan_fg_of_isNoetherianRing
    {K : Type u} {C : Type v} {M : Type w}
    [CommRing K] [IsNoetherianRing K]
    [AddCommMonoid C] [Module K C] [Coalgebra K C]
    [AddCommMonoid M] [Module K M] [Module.Finite K M]
    (X : RightComodule K C M) : X.coefficientSpan.FG := by
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup K (M := M)
  let : IsNoetherian K (Module.Dual K M) := isNoetherian_linearMap K K M
  let : Module.Finite K (Module.Dual K M) :=
    Module.IsNoetherian.finite K (Module.Dual K M)
  exact X.coefficientSpan_fg_of_finite

end Coalgebra.RightComodule

namespace Coalgebra.RightComoduleHom

section CommSemiring

variable {K : Type u} {C : Type v} {M : Type w} {N : Type*}
variable [CommSemiring K] [AddCommMonoid C] [Module K C] [Coalgebra K C]
variable [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
variable {X : RightComodule K C M} {Y : RightComodule K C N}

/-- Coefficients pull back along the underlying linear map of a comodule morphism. -/
theorem coefficient_apply (f : RightComoduleHom X Y) (ell : N →ₗ[K] K) (m : M) :
    Y.coefficient ell (f m) = X.coefficient (ell.comp f.toLinearMap) m := by
  simp only [RightComodule.coefficient_eq, f.colinear_apply,
    LinearMap.rTensor_comp, LinearMap.comp_apply]

/-- A surjective comodule morphism decreases the coefficient span: surjectivity
allows every target vector to be lifted to a source vector. -/
theorem coefficientSpan_le_of_surjective (f : RightComoduleHom X Y)
    (hf : Function.Surjective f) : Y.coefficientSpan ≤ X.coefficientSpan := by
  apply (Y.coefficientSpan_le_iff _).mpr
  intro ell n
  obtain ⟨m, rfl⟩ := hf n
  rw [f.coefficient_apply]
  exact X.coefficient_mem_coefficientSpan (ell.comp f.toLinearMap) m

/-- A bijective comodule morphism preserves the coefficient span; its inverse
linear map pulls every source functional back to the target. -/
theorem coefficientSpan_eq_of_bijective (f : RightComoduleHom X Y)
    (hf : Function.Bijective f) : X.coefficientSpan = Y.coefficientSpan := by
  classical
  let e : M ≃ₗ[K] N := LinearEquiv.ofBijective f.toLinearMap hf
  apply le_antisymm
  · apply (X.coefficientSpan_le_iff _).mpr
    intro ell m
    have hcomp : (ell.comp e.symm.toLinearMap).comp f.toLinearMap = ell := by
      ext x
      exact congrArg ell (e.symm_apply_apply x)
    have h := Y.coefficient_mem_coefficientSpan (ell.comp e.symm.toLinearMap) (f m)
    rw [f.coefficient_apply, hcomp] at h
    exact h
  · exact f.coefficientSpan_le_of_surjective hf.surjective

end CommSemiring

section FieldCore

variable {K : Type u} {C : Type v} {M : Type w} {N : Type*}
variable [Field K] [AddCommMonoid C] [Module K C] [Coalgebra K C]
variable [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
variable {X : RightComodule K C M} {Y : RightComodule K C N}

/-- An injective comodule morphism over a field increases the coefficient span.
Injectivity lets each source functional extend to the target; coefficients on
vectors in a kernel need not survive a noninjective map. -/
theorem coefficientSpan_le_of_injective (f : RightComoduleHom X Y)
    (hf : Function.Injective f) : X.coefficientSpan ≤ Y.coefficientSpan := by
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup K
  let : AddCommGroup N := Module.addCommMonoidToAddCommGroup K
  apply (X.coefficientSpan_le_iff _).mpr
  intro ell m
  obtain ⟨eta, heta⟩ :=
    LinearMap.dualMap_surjective_of_injective (f := f.toLinearMap) hf ell
  have hcomp : eta.comp f.toLinearMap = ell := by
    simpa only [LinearMap.dualMap_apply'] using heta
  have h := Y.coefficient_mem_coefficientSpan eta (f m)
  rw [f.coefficient_apply, hcomp] at h
  exact h

end FieldCore

end Coalgebra.RightComoduleHom

namespace Coalgebra.RightComodule

section CommSemiring

variable {K : Type u} {C : Type v} {M : Type w}
variable [CommSemiring K] [AddCommMonoid C] [Module K C] [Coalgebra K C]
variable [AddCommMonoid M] [Module K M]

private theorem coefficient_eq_sum_basis {ι : Type*} [Fintype ι]
    (X : RightComodule K C M) (b : Module.Basis ι K M)
    (ell : M →ₗ[K] K) (m : M) :
    X.coefficient ell m = ∑ j, b.equivFun m j • X.coefficient ell (b j) := by
  let f : M →ₗ[K] C :=
    (_root_.TensorProduct.lid K C).toLinearMap ∘ₗ ell.rTensor C ∘ₗ X.coaction
  have h := b.constr_apply_fintype K (fun j ↦ f (b j)) m
  rw [b.constr_self K f] at h
  simpa only [f, LinearMap.comp_apply, coefficient_eq, LinearEquiv.coe_coe] using h

/-- The coefficients of a supplied basis span the all-dual coefficient span.
Neither the basis index nor the support of a functional on the whole basis need be finite. -/
theorem coefficientSpan_eq_span_basis {ι : Type z}
    (X : RightComodule K C M) (b : Module.Basis ι K M) :
    X.coefficientSpan = Submodule.span K
      (Set.range (Function.uncurry (fun i j : ι ↦ X.coefficient (b.coord i) (b j)))) := by
  classical
  apply le_antisymm
  · apply (X.coefficientSpan_le_iff _).mpr
    intro ell m
    rw [coefficient_eq, X.coaction_eq_sum_basis b m, Finsupp.sum]
    simp only [map_sum, LinearMap.rTensor_tmul, _root_.TensorProduct.lid_tmul]
    refine Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ ?_
    rw [X.equivFinsuppOfBasisLeft_coaction_apply b m i]
    -- Only the support of this vector's coordinates is used.
    let f : M →ₗ[K] C :=
      (_root_.TensorProduct.lid K C).toLinearMap ∘ₗ (b.coord i).rTensor C ∘ₗ X.coaction
    have h := b.constr_apply K (fun j ↦ f (b j)) m
    rw [b.constr_self K f] at h
    have hcoord : X.coefficient (b.coord i) m =
        (b.repr m).sum (fun j a ↦ a • X.coefficient (b.coord i) (b j)) := by
      simpa only [f, LinearMap.comp_apply, coefficient_eq, LinearEquiv.coe_coe] using h
    rw [hcoord, Finsupp.sum]
    exact Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _
      (Submodule.subset_span ⟨(i, j), rfl⟩)
  · apply Submodule.span_le.mpr
    rintro c ⟨⟨i, j⟩, rfl⟩
    exact X.coefficient_mem_coefficientSpan (b.coord i) (b j)

end CommSemiring

/-- All first-factor dual evaluations detect a tensor's membership in the
range of a second-factor submodule inclusion. -/
private theorem tensor_mem_range_lTensor_iff {K : Type u} {N : Type v} {M : Type w}
    [Field K] [AddCommMonoid N] [Module K N] [AddCommMonoid M] [Module K M]
    (S : Submodule K N) (z : M ⊗[K] N) :
    z ∈ LinearMap.range (S.subtype.lTensor M) ↔
      ∀ ell : M →ₗ[K] K, _root_.TensorProduct.lid K N (ell.rTensor N z) ∈ S := by
  constructor
  · rintro ⟨y, rfl⟩ ell
    induction y with
    | tmul m n =>
      simpa only [LinearMap.lTensor_tmul, Submodule.subtype_apply,
        LinearMap.rTensor_tmul, _root_.TensorProduct.lid_tmul] using
        S.smul_mem (ell m) n.property
    | add y₁ y₂ hy₁ hy₂ =>
      simpa only [map_add] using S.add_mem hy₁ hy₂
  · intro hz
    classical
    let : AddCommGroup M := Module.addCommMonoidToAddCommGroup K (M := M)
    let b := Module.Basis.ofVectorSpace K M
    let c := TensorProduct.equivFinsuppOfBasisLeft (N := N) b z
    have hc (i : Module.Basis.ofVectorSpaceIndex K M) : c i ∈ S := by
      dsimp only [c]
      rw [TensorProduct.equivFinsuppOfBasisLeft_apply]
      exact hz (b.coord i)
    have hrepr : c.sum (fun i n ↦ b i ⊗ₜ[K] n) = z := by
      simpa only [TensorProduct.equivFinsuppOfBasisLeft_symm_apply] using
        (TensorProduct.equivFinsuppOfBasisLeft b).symm_apply_apply z
    rw [← hrepr]
    refine Submodule.finsuppSum_mem K (LinearMap.range (S.subtype.lTensor M)) c
      (fun i n ↦ b i ⊗ₜ[K] n) ?_
    intro i _
    refine ⟨b i ⊗ₜ[K] (⟨c i, hc i⟩ : S), ?_⟩
    simp only [LinearMap.lTensor_tmul, Submodule.subtype_apply]

/-- A supplied basis with finite index gives a finitely generated coefficient span. -/
theorem coefficientSpan_fg
    {K : Type u} {C : Type v} {M : Type w}
    [CommSemiring K] [AddCommMonoid C] [Module K C] [Coalgebra K C]
    [AddCommMonoid M] [Module K M] {ι : Type z} [Finite ι]
    (X : RightComodule K C M) (b : Module.Basis ι K M) :
    X.coefficientSpan.FG := by
  let : Module.Finite K M := Module.Finite.of_basis b
  let : Module.Free K M := Module.Free.of_basis b
  exact X.coefficientSpan_fg_of_finite

section Field

variable {K : Type u} {C : Type v} {M : Type w}
variable [Field K] [AddCommGroup C] [Module K C] [Coalgebra K C]
variable [AddCommMonoid M] [Module K M]

private theorem coefficientSpan_comul_mem (X : RightComodule K C M)
    {c : C} (hc : c ∈ X.coefficientSpan) :
    comul (R := K) c ∈ LinearMap.range
      (TensorProduct.mapIncl X.coefficientSpan X.coefficientSpan) := by
  classical
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup K (M := M)
  have hS : X.coefficientSpan ≤
      (LinearMap.range (TensorProduct.mapIncl X.coefficientSpan X.coefficientSpan)).comap
        (comul (R := K)) := by
    apply (X.coefficientSpan_le_iff _).mpr
    intro ell m
    change comul (R := K) (X.coefficient ell m) ∈ LinearMap.range
      (TensorProduct.mapIncl X.coefficientSpan X.coefficientSpan)
    let b := Module.Basis.ofVectorSpace K M
    let f := TensorProduct.equivFinsuppOfBasisLeft b (X.coaction m)
    have hf (i : Module.Basis.ofVectorSpaceIndex K M) :
        f i = X.coefficient (b.coord i) m :=
      X.equivFinsuppOfBasisLeft_coaction_apply b m i
    have hΔ : comul (R := K) (X.coefficient ell m) =
        ∑ i ∈ f.support, X.coefficient ell (b i) ⊗ₜ[K] f i := by
      simpa only [f, Finsupp.sum] using X.comul_coefficient_eq_sum_coaction b ell m
    rw [hΔ]
    apply Submodule.sum_mem
    intro i hi
    exact ⟨(⟨X.coefficient ell (b i), X.coefficient_mem_coefficientSpan ell (b i)⟩ :
        X.coefficientSpan) ⊗ₜ[K]
      (⟨f i, by rw [hf i]; exact X.coefficient_mem_coefficientSpan (b.coord i) m⟩ :
        X.coefficientSpan), rfl⟩
  exact hS hc

/-- The coefficient subcoalgebra, with underlying submodule the all-dual coefficient span. -/
def coefficientSubcoalgebra (X : RightComodule K C M) : _root_.Subcoalgebra K C :=
  _root_.Subcoalgebra.mk' X.coefficientSpan (by
    intro c hc
    exact coefficientSpan_comul_mem X hc)

/-- The carrier of the coefficient subcoalgebra is exactly the coefficient span. -/
@[simp] theorem coefficientSubcoalgebra_toSubmodule (X : RightComodule K C M) :
    X.coefficientSubcoalgebra.toSubmodule = X.coefficientSpan :=
  rfl

/-- The coefficient subcoalgebra of the regular right comodule has full underlying submodule. -/
theorem coefficientSubcoalgebra_regular_toSubmodule :
    (regular K C).coefficientSubcoalgebra.toSubmodule = (⊤ : Submodule K C) := by
  rw [coefficientSubcoalgebra_toSubmodule, coefficientSpan_regular]

/-- The underlying submodule is the span of the exact range of coefficient evaluation. -/
theorem coefficientSubcoalgebra_toSubmodule_eq_span_range (X : RightComodule K C M) :
    X.coefficientSubcoalgebra.toSubmodule =
      Submodule.span K (Set.range (Function.uncurry X.coefficient)) :=
  rfl

/-- Membership in the coefficient subcoalgebra is membership in the coefficient span. -/
@[simp] theorem mem_coefficientSubcoalgebra (X : RightComodule K C M) (c : C) :
    c ∈ X.coefficientSubcoalgebra ↔ c ∈ X.coefficientSpan :=
  Iff.rfl

/-- Every coefficient belongs to the coefficient subcoalgebra. -/
theorem coefficient_mem_coefficientSubcoalgebra (X : RightComodule K C M)
    (ell : M →ₗ[K] K) (m : M) : X.coefficient ell m ∈ X.coefficientSubcoalgebra :=
  X.coefficient_mem_coefficientSpan ell m

/-- A coaction takes values in `M ⊗ D` exactly when its coefficient span is
contained in the underlying submodule of `D`. -/
theorem coaction_mem_range_iff_coefficientSpan_le (X : RightComodule K C M)
    (D : _root_.Subcoalgebra K C) :
    (∀ m : M, X.coaction m ∈ LinearMap.range (D.subtype.toLinearMap.lTensor M)) ↔
      X.coefficientSpan ≤ D.toSubmodule := by
  constructor
  · intro h
    apply (X.coefficientSpan_le_iff D.toSubmodule).mpr
    intro ell m
    exact (tensor_mem_range_lTensor_iff D.toSubmodule (X.coaction m)).mp (h m) ell
  · intro h m
    apply (tensor_mem_range_lTensor_iff D.toSubmodule (X.coaction m)).mpr
    intro ell
    exact (X.coefficientSpan_le_iff D.toSubmodule).mp h ell m

/-- The linear corestriction of a coaction through the tensor inclusion of a subcoalgebra. -/
noncomputable def coactionCodRestrict (X : RightComodule K C M)
    (D : _root_.Subcoalgebra K C)
    (h : ∀ m : M, X.coaction m ∈ LinearMap.range (D.subtype.toLinearMap.lTensor M)) :
    M →ₗ[K] M ⊗[K] D :=
  X.coaction.codLift (D.subtype.toLinearMap.lTensor M)
    (by
      let : AddCommGroup M := Module.addCommMonoidToAddCommGroup K (M := M)
      exact Module.Flat.lTensor_preserves_injective_linearMap
        (R := K) (M := M) D.subtype.toLinearMap D.subtype_injective) h

/-- Tensor inclusion after linear corestriction recovers the original coaction. -/
theorem subtype_lTensor_comp_coactionCodRestrict (X : RightComodule K C M)
    (D : _root_.Subcoalgebra K C)
    (h : ∀ m : M, X.coaction m ∈ LinearMap.range (D.subtype.toLinearMap.lTensor M)) :
    D.subtype.toLinearMap.lTensor M ∘ₗ X.coactionCodRestrict D h = X.coaction :=
  LinearMap.comp_codLift _ _ _ _

/-- The corestricted linear coaction satisfies the inclusion equation at each element. -/
@[simp] theorem subtype_lTensor_coactionCodRestrict (X : RightComodule K C M)
    (D : _root_.Subcoalgebra K C)
    (h : ∀ m : M, X.coaction m ∈ LinearMap.range (D.subtype.toLinearMap.lTensor M))
    (m : M) :
    DFunLike.coe (F := M ⊗[K] D →ₗ[K] M ⊗[K] C)
      (α := M ⊗[K] D) (β := fun _ => M ⊗[K] C)
      (D.toSubmodule.subtype.lTensor (N := D) M) (X.coactionCodRestrict D h m) = X.coaction m :=
  LinearMap.congr_fun (X.subtype_lTensor_comp_coactionCodRestrict D h) m

private theorem coactionCodRestrict_coassoc (X : RightComodule K C M)
    (D : _root_.Subcoalgebra K C)
    (h : ∀ m : M, X.coaction m ∈ LinearMap.range (D.subtype.toLinearMap.lTensor M)) :
    _root_.TensorProduct.assoc K M D D ∘ₗ (X.coactionCodRestrict D h).rTensor D ∘ₗ
        X.coactionCodRestrict D h =
      (comul (R := K) (A := D)).lTensor M ∘ₗ X.coactionCodRestrict D h := by
  let ρ : M →ₗ[K] M ⊗[K] D := X.coactionCodRestrict D h
  have hρ : D.subtype.toLinearMap.lTensor M ∘ₗ ρ = X.coaction :=
    X.subtype_lTensor_comp_coactionCodRestrict D h
  have hρ_apply (m : M) : D.subtype.toLinearMap.lTensor M (ρ m) = X.coaction m :=
    LinearMap.congr_fun hρ m
  have hρ_tensor :
      _root_.TensorProduct.map (D.subtype.toLinearMap.lTensor M) D.subtype.toLinearMap ∘ₗ
          ρ.rTensor D =
        X.coaction.rTensor C ∘ₗ D.subtype.toLinearMap.lTensor M := by
    rw [LinearMap.map_comp_rTensor, hρ, LinearMap.rTensor_comp_lTensor]
  have hcomul :
      (_root_.TensorProduct.map D.subtype.toLinearMap D.subtype.toLinearMap).lTensor M ∘ₗ
          (comul (R := K) (A := D)).lTensor M =
        (comul (R := K) (A := C)).lTensor M ∘ₗ D.subtype.toLinearMap.lTensor M := by
    rw [← LinearMap.lTensor_comp, D.subtype.map_comp_comul, LinearMap.lTensor_comp]
  -- Only the cancellation step needs the field's canonical additive inverses on M.
  have hinj : Function.Injective
      ((_root_.TensorProduct.map D.subtype.toLinearMap D.subtype.toLinearMap).lTensor M) := by
    let : AddCommGroup M := Module.addCommMonoidToAddCommGroup K (M := M)
    exact Module.Flat.lTensor_preserves_injective_linearMap (M := M)
      (TensorProduct.mapIncl D.toSubmodule D.toSubmodule)
      (Module.Flat.tensorProduct_mapIncl_injective_of_right D.toSubmodule D.toSubmodule)
  apply LinearMap.ext
  intro m
  apply hinj
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  calc
    (_root_.TensorProduct.map D.subtype.toLinearMap D.subtype.toLinearMap).lTensor M
        (_root_.TensorProduct.assoc K M D D (ρ.rTensor D (ρ m))) =
        _root_.TensorProduct.assoc K M C C
          (_root_.TensorProduct.map (D.subtype.toLinearMap.lTensor M) D.subtype.toLinearMap
            (ρ.rTensor D (ρ m))) :=
      TensorProduct.map_map_assoc (LinearMap.id : M →ₗ[K] M)
        D.subtype.toLinearMap D.subtype.toLinearMap _
    _ = _root_.TensorProduct.assoc K M C C
        (X.coaction.rTensor C (D.subtype.toLinearMap.lTensor M (ρ m))) :=
      congrArg (_root_.TensorProduct.assoc K M C C) (LinearMap.congr_fun hρ_tensor (ρ m))
    _ = _root_.TensorProduct.assoc K M C C (X.coaction.rTensor C (X.coaction m)) := by
      rw [hρ_apply]
    _ = (comul (R := K) (A := C)).lTensor M (X.coaction m) := X.coassoc_apply m
    _ = (comul (R := K) (A := C)).lTensor M
        (D.subtype.toLinearMap.lTensor M (ρ m)) := by rw [hρ_apply]
    _ = (_root_.TensorProduct.map D.subtype.toLinearMap D.subtype.toLinearMap).lTensor M
        ((comul (R := K) (A := D)).lTensor M (ρ m)) :=
      (LinearMap.congr_fun hcomul (ρ m)).symm

private theorem coactionCodRestrict_counit_comp (X : RightComodule K C M)
    (D : _root_.Subcoalgebra K C)
    (h : ∀ m : M, X.coaction m ∈ LinearMap.range (D.subtype.toLinearMap.lTensor M)) :
    (counit (R := K) (A := D)).lTensor M ∘ₗ X.coactionCodRestrict D h =
      (_root_.TensorProduct.rid K M).symm.toLinearMap := by
  rw [← D.subtype.counit_comp, LinearMap.lTensor_comp, LinearMap.comp_assoc,
    X.subtype_lTensor_comp_coactionCodRestrict D h]
  exact X.counit_comp

/-- The right comodule on the same module with coacting coalgebra corestricted to `D`. -/
noncomputable def restrictCoalgebra (X : RightComodule K C M)
    (D : _root_.Subcoalgebra K C)
    (h : ∀ m : M, X.coaction m ∈ LinearMap.range (D.subtype.toLinearMap.lTensor M)) :
    RightComodule K D M where
  coaction := X.coactionCodRestrict D h
  coassoc := by exact coactionCodRestrict_coassoc X D h
  counit_comp := by exact coactionCodRestrict_counit_comp X D h

/-- The coaction of the corestricted comodule is the specified linear lift. -/
@[simp] theorem restrictCoalgebra_coaction (X : RightComodule K C M)
    (D : _root_.Subcoalgebra K C)
    (h : ∀ m : M, X.coaction m ∈ LinearMap.range (D.subtype.toLinearMap.lTensor M)) :
    (X.restrictCoalgebra D h).coaction = X.coactionCodRestrict D h :=
  rfl

/-- The coaction of the corestricted comodule maps to the original coaction under inclusion. -/
theorem subtype_lTensor_comp_restrictCoalgebra_coaction (X : RightComodule K C M)
    (D : _root_.Subcoalgebra K C)
    (h : ∀ m : M, X.coaction m ∈ LinearMap.range (D.subtype.toLinearMap.lTensor M)) :
    D.subtype.toLinearMap.lTensor M ∘ₗ (X.restrictCoalgebra D h).coaction = X.coaction :=
  X.subtype_lTensor_comp_coactionCodRestrict D h

/-- The coacting coalgebra has a unique corestriction to `D` precisely when the
coefficient span is contained in its underlying submodule, as in the classical
coefficient-coalgebra construction from Sweedler's *Hopf Algebras*. -/
theorem existsUnique_restrictCoalgebra_iff (X : RightComodule K C M)
    (D : _root_.Subcoalgebra K C) :
    (∃! Y : RightComodule K D M, D.subtype.toLinearMap.lTensor M ∘ₗ Y.coaction =
      X.coaction) ↔ X.coefficientSpan ≤ D.toSubmodule := by
  constructor
  · rintro ⟨Y, hY, _⟩
    apply (X.coaction_mem_range_iff_coefficientSpan_le D).mp
    intro m
    exact ⟨Y.coaction m, LinearMap.congr_fun hY m⟩
  · intro h
    have hρ := (X.coaction_mem_range_iff_coefficientSpan_le D).mpr h
    refine ⟨X.restrictCoalgebra D hρ,
      X.subtype_lTensor_comp_restrictCoalgebra_coaction D hρ, ?_⟩
    intro Y hY
    apply Coalgebra.RightComodule.ext
    apply LinearMap.ext
    intro m
    have hinj : Function.Injective (D.subtype.toLinearMap.lTensor M) := by
      let : AddCommGroup M := Module.addCommMonoidToAddCommGroup K (M := M)
      exact Module.Flat.lTensor_preserves_injective_linearMap
        (R := K) (M := M) D.subtype.toLinearMap D.subtype_injective
    apply hinj
    exact (LinearMap.congr_fun hY m).trans
      (X.subtype_lTensor_coactionCodRestrict D hρ m).symm

/-- The original module as a right comodule over its coefficient subcoalgebra. -/
noncomputable def coefficientComodule (X : RightComodule K C M) :
    RightComodule K X.coefficientSubcoalgebra M :=
  X.restrictCoalgebra X.coefficientSubcoalgebra
    ((X.coaction_mem_range_iff_coefficientSpan_le X.coefficientSubcoalgebra).mpr le_rfl)

/-- Inclusion of the coefficient subcoalgebra intertwines the two coactions. -/
theorem subtype_lTensor_comp_coefficientComodule_coaction (X : RightComodule K C M) :
    X.coefficientSubcoalgebra.subtype.toLinearMap.lTensor M ∘ₗ
        X.coefficientComodule.coaction = X.coaction :=
  X.subtype_lTensor_comp_restrictCoalgebra_coaction X.coefficientSubcoalgebra _

/-- The coefficient-comodule inclusion equation evaluated at an element. -/
@[simp] theorem subtype_lTensor_coefficientComodule_coaction
    (X : RightComodule K C M) (m : M) :
    DFunLike.coe (F := M ⊗[K] X.coefficientSpan →ₗ[K] M ⊗[K] C)
      (α := M ⊗[K] X.coefficientSpan) (β := fun _ => M ⊗[K] C)
      (X.coefficientSpan.subtype.lTensor (N := X.coefficientSpan) M)
      (X.coefficientComodule.coaction m) = X.coaction m :=
  LinearMap.congr_fun X.subtype_lTensor_comp_coefficientComodule_coaction m

/-- A module-finite right comodule has a finitely generated coefficient subcoalgebra.
This is the finite-comodule coefficient theorem from Sweedler's *Hopf Algebras*. -/
theorem coefficientSubcoalgebra_fg [Module.Finite K M] (X : RightComodule K C M) :
    X.coefficientSubcoalgebra.toSubmodule.FG := by
  classical
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup K (M := M)
  simpa only [coefficientSubcoalgebra_toSubmodule] using
    X.coefficientSpan_fg (Module.finBasis K M)

example (X : RightComodule K C M) :
    ∃ Y : RightComodule K X.coefficientSubcoalgebra M,
      X.coefficientSubcoalgebra.subtype.toLinearMap.lTensor M ∘ₗ Y.coaction = X.coaction :=
  ⟨X.coefficientComodule, X.subtype_lTensor_comp_coefficientComodule_coaction⟩

/-- Changing the corestricted coacting coalgebra along its inclusion recovers the original
comodule. -/
@[simp] theorem mapCoalgebra_restrictCoalgebra (X : RightComodule K C M)
    (D : _root_.Subcoalgebra K C)
    (h : ∀ m : M, X.coaction m ∈ LinearMap.range (D.subtype.toLinearMap.lTensor M)) :
    (X.restrictCoalgebra D h).mapCoalgebra D.subtype = X := by
  apply Coalgebra.RightComodule.ext
  rw [mapCoalgebra_coaction]
  exact X.subtype_lTensor_comp_restrictCoalgebra_coaction D h

end Field

end Coalgebra.RightComodule

namespace Coalgebra.RightComoduleHom

section FieldCarrier

variable {K : Type u} {C : Type v} {M : Type w} {N : Type*}
variable [Field K] [AddCommGroup C] [Module K C] [Coalgebra K C]
variable [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
variable {X : RightComodule K C M} {Y : RightComodule K C N}

/-- A surjective comodule morphism decreases the underlying submodule of the
coefficient subcoalgebra, since every target vector has a source lift. -/
theorem coefficientSubcoalgebra_toSubmodule_le_of_surjective
    (f : RightComoduleHom X Y) (hf : Function.Surjective f) :
    Y.coefficientSubcoalgebra.toSubmodule ≤ X.coefficientSubcoalgebra.toSubmodule := by
  simpa only [RightComodule.coefficientSubcoalgebra_toSubmodule] using
    f.coefficientSpan_le_of_surjective hf

/-- A bijective comodule morphism preserves the coefficient subcoalgebra. -/
theorem coefficientSubcoalgebra_eq_of_bijective
    (f : RightComoduleHom X Y) (hf : Function.Bijective f) :
    X.coefficientSubcoalgebra = Y.coefficientSubcoalgebra := by
  apply _root_.Subcoalgebra.toSubmodule_injective
  simpa only [RightComodule.coefficientSubcoalgebra_toSubmodule] using
    f.coefficientSpan_eq_of_bijective hf

/-- An injective comodule morphism over a field increases the underlying
submodule of the coefficient subcoalgebra, by extension of linear functionals. -/
theorem coefficientSubcoalgebra_toSubmodule_le_of_injective
    (f : RightComoduleHom X Y) (hf : Function.Injective f) :
    X.coefficientSubcoalgebra.toSubmodule ≤ Y.coefficientSubcoalgebra.toSubmodule := by
  simpa only [RightComodule.coefficientSubcoalgebra_toSubmodule] using
    f.coefficientSpan_le_of_injective hf

end FieldCarrier

end Coalgebra.RightComoduleHom
