/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Scalar-extension images of submodules

Commuting tensor factors identifies the right-order tensor-inclusion image with
`Submodule.baseChange`. An arbitrary linear map on the coefficient factor carries
one scalar-extension image into another. Neither assertion requires injectivity
of the tensor inclusion or flatness, and the coefficient algebras may be
noncommutative semirings.

Over a field, linear functionals on the coefficient module detect membership in
the image of a submodule inclusion. This criterion needs no algebra structure on
the coefficient module, and its universe is independent of the ambient space.
Its scalar-extension specialization retains the original `U.subtype.baseChange R`.

## Implementation notes

The coefficient criterion chooses a field basis internally and uses Mathlib's
`TensorProduct.equivFinsuppOfBasisLeft` coefficient and reconstruction formulas.
No basis, finite-dimensionality, flatness or nonzero-module assumption is required
from callers. The specialization to scalar extension uses the stock function
agreement `LinearMap.baseChange_eq_ltensor` and `LinearMap.lTensor_def`.
The coefficient module need only be an additive commutative monoid.
`Module.addCommMonoidToAddCommGroup` supplies the additive group needed for the
field-basis choice, retaining the original additive-monoid and module parents.

## References

* Mathlib's tensor-map, basis, commutativity and scalar-extension formalizations.
* C. Kassel, *Quantum Groups*, §II.4, for tensor-product conventions.
-/

@[expose] public section

universe uR uA uB uM uK uT uV

open scoped TensorProduct

namespace TensorProduct

variable {R : Type uR} {A : Type uA} {M : Type uM}
variable [CommSemiring R] [Semiring A] [Algebra R A]
variable [AddCommMonoid M] [Module R M]

/-- Commutation identifies the right-order tensor-inclusion image with the
scalar-extension image of a submodule. -/
theorem comm_mem_baseChange_iff (U : Submodule R M) (y : M ⊗[R] A) :
    TensorProduct.comm R M A y ∈ U.baseChange A ↔
      y ∈ LinearMap.range (U.subtype.rTensor A) := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨TensorProduct.comm R A U t, ?_⟩
    apply (TensorProduct.comm R M A).injective
    exact (LinearMap.congr_fun
      (LinearMap.comm_comp_rTensor_comp_comm_eq (Q := A) U.subtype) t).trans ht
  · rintro ⟨t, ht⟩
    refine ⟨TensorProduct.comm R U A t, ?_⟩
    calc
      U.subtype.baseChange A (TensorProduct.comm R U A t) =
          TensorProduct.comm R M A (U.subtype.rTensor A t) :=
        TensorProduct.map_comm (LinearMap.id : A →ₗ[R] A) U.subtype t
      _ = TensorProduct.comm R M A y :=
        congrArg (TensorProduct.comm R M A) ht

end TensorProduct

namespace Submodule

variable {R : Type uR} {A : Type uA} {B : Type uB} {M : Type uM}
variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
variable [AddCommMonoid M] [Module R M]

/-- A linear map on the coefficient factor transports scalar-extension images.
The tensor transport is `R`-linear; it need not be linear over either coefficient
algebra. -/
theorem map_mem_baseChange (U : Submodule R M) (f : A →ₗ[R] B)
    {z : A ⊗[R] M} (hz : z ∈ U.baseChange A) :
    TensorProduct.map f (LinearMap.id : M →ₗ[R] M) z ∈ U.baseChange B := by
  obtain ⟨w, rfl⟩ := hz
  refine ⟨TensorProduct.map f (LinearMap.id : U →ₗ[R] U) w, ?_⟩
  change TensorProduct.map (LinearMap.id : B →ₗ[R] B) U.subtype
      (TensorProduct.map f (LinearMap.id : U →ₗ[R] U) w) =
    TensorProduct.map f (LinearMap.id : M →ₗ[R] M)
      (TensorProduct.map (LinearMap.id : A →ₗ[R] A) U.subtype w)
  simp only [TensorProduct.map_map, LinearMap.id_comp, LinearMap.comp_id]

end Submodule

namespace TensorProduct

variable {K : Type uK} {T : Type uT} {V : Type uV}
variable [Field K] [AddCommMonoid T] [AddCommMonoid V] [Module K T] [Module K V]

/-- A tensor lies in the image of the inclusion of a submodule on the right if
and only if every linear functional on the left contracts it into that submodule.
The coefficient module and the ambient space may have independent universes and
arbitrary dimensions. -/
theorem mem_range_map_id_subtype_iff (U : Submodule K V) (w : T ⊗[K] V) :
    w ∈ LinearMap.range (TensorProduct.map (LinearMap.id : T →ₗ[K] T) U.subtype) ↔
      ∀ f : T →ₗ[K] K,
        TensorProduct.lid K V
          (TensorProduct.map f (LinearMap.id : V →ₗ[K] V) w) ∈ U := by
  classical
  constructor
  · rintro ⟨x, rfl⟩ f
    induction x using TensorProduct.inductionOn with
    | tmul t v =>
        simpa only [TensorProduct.map_tmul, LinearMap.id_apply,
          Submodule.subtype_apply, TensorProduct.lid_tmul] using U.smul_mem (f t) v.property
    | add x y hx hy =>
        simpa only [map_add] using U.add_mem hx hy
  · intro h
    let : AddCommGroup T := Module.addCommMonoidToAddCommGroup K
    let b := Module.Free.chooseBasis K T
    let c := TensorProduct.equivFinsuppOfBasisLeft (N := V) b w
    have hc (i : Module.Free.ChooseBasisIndex K T) : c i ∈ U := by
      simpa only [c, TensorProduct.equivFinsuppOfBasisLeft_apply, LinearMap.rTensor_def]
        using h (b.coord i)
    have hw : c.sum (fun i v ↦ b i ⊗ₜ[K] v) = w := by
      rw [← TensorProduct.equivFinsuppOfBasisLeft_symm_apply]
      exact (TensorProduct.equivFinsuppOfBasisLeft b).symm_apply_apply w
    rw [← hw]
    change (∑ i ∈ c.support, b i ⊗ₜ[K] c i) ∈
      LinearMap.range (TensorProduct.map (LinearMap.id : T →ₗ[K] T) U.subtype)
    apply Submodule.sum_mem
    intro i _
    refine ⟨b i ⊗ₜ[K] (⟨c i, hc i⟩ : U), ?_⟩
    simp only [TensorProduct.map_tmul, LinearMap.id_apply, Submodule.subtype_apply]

end TensorProduct

namespace Submodule

variable {K : Type uK} {R : Type uR} {V : Type uV}
variable [Field K] [Semiring R] [Algebra K R] [AddCommMonoid V] [Module K V]

/-- Linear functionals on the coefficient algebra detect membership in the image
of the original scalar-extended subtype map. The coefficient algebra may be a
noncommutative semiring, including the zero semiring. -/
theorem mem_range_baseChange_subtype_iff (U : Submodule K V) (w : R ⊗[K] V) :
    w ∈ LinearMap.range (U.subtype.baseChange R) ↔
      ∀ f : R →ₗ[K] K,
        TensorProduct.lid K V
          (TensorProduct.map f (LinearMap.id : V →ₗ[K] V) w) ∈ U := by
  simpa only [LinearMap.mem_range, LinearMap.baseChange_eq_ltensor, LinearMap.lTensor_def]
    using TensorProduct.mem_range_map_id_subtype_iff (T := R) U w

end Submodule
