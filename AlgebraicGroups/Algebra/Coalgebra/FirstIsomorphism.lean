/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.Quotient
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Coalgebra.Equiv

/-!
# The first isomorphism construction for surjective coalgebra morphisms

A surjective coalgebra morphism identifies its target with the quotient by its linear kernel.
`CoalgHomClass.quotKerCoalgebraStruct` selects the quotient structure supplied by Mathlib, using
coideality of the kernel. `CoalgHomClass.quotKerEquivOfSurjective` promotes the descended morphism
to an equivalence. The representative formula and compatibility with the linear first
isomorphism describe this construction without unfolding it.

Only `CoalgebraStruct` is required on either endpoint: the construction does not use the
coalgebra laws, flatness or a field hypothesis. Scalars form a commutative ring, both modules
are additive commutative groups, and all four universes are independent.

## References

- `Mathlib.RingTheory.Coalgebra.Quotient` supplies the quotient coalgebra structure.
- `AlgebraicGroups.Algebra.Coalgebra.Quotient` supplies kernel coideality and
  `Submodule.liftQCoalgHom`, with its quotient universal property.
- `Mathlib.LinearAlgebra.Isomorphisms` supplies `LinearMap.quotKerEquivOfSurjective`.
- `Mathlib.RingTheory.Coalgebra.Equiv` supplies `CoalgEquiv.ofBijective`.
-/

@[expose] public section

universe u v w z

namespace CoalgHomClass

variable {R : Type u} [rR : CommRing R]
variable {C : Type v} [aC : AddCommGroup C] [mC : Module R C]
variable [cC : CoalgebraStruct R C]
variable {D : Type w} [aD : AddCommGroup D] [mD : Module R D]
variable [cD : CoalgebraStruct R D]
variable {F : Type z} [FunLike F C D] [CoalgHomClass F R C D]

/-- The quotient coalgebra structure on the kernel quotient of a surjective morphism.

This is the existing quotient structure, selected using coideality of the kernel; it is not
an additional instance. -/
@[instance_reducible]
def quotKerCoalgebraStruct (f : F) (hf : Function.Surjective f) :
    CoalgebraStruct R (C ⧸ (f : C →ₗ[R] D).ker) := by
  letI : (f : C →ₗ[R] D).ker.IsCoideal := ker_isCoideal_of_surjective f hf
  exact inferInstance

/-- The quotient by the kernel of a surjective coalgebra morphism is canonically equivalent
to its target, via the descended morphism. -/
noncomputable def quotKerEquivOfSurjective (f : F) (hf : Function.Surjective f) :
    @CoalgEquiv R (inferInstance : CommSemiring R)
      (C ⧸ (f : C →ₗ[R] D).ker) D
      (inferInstance : AddCommMonoid (C ⧸ (f : C →ₗ[R] D).ker))
      (inferInstance : AddCommMonoid D)
      (inferInstance : Module R (C ⧸ (f : C →ₗ[R] D).ker)) mD
      (quotKerCoalgebraStruct f hf) cD := by
  letI : (f : C →ₗ[R] D).ker.IsCoideal := ker_isCoideal_of_surjective f hf
  exact CoalgEquiv.ofBijective
    (f := (f : C →ₗ[R] D).ker.liftQCoalgHom (CoalgHom.ofClass f) le_rfl)
    (by
      have h :
          ⇑((f : C →ₗ[R] D).ker.liftQCoalgHom
            (CoalgHom.ofClass f) le_rfl) =
            ⇑((f : C →ₗ[R] D).quotKerEquivOfSurjective hf) := by
        funext x
        obtain ⟨y, rfl⟩ := (f : C →ₗ[R] D).ker.mkQ_surjective x
        calc
          _ = f y := Submodule.liftQCoalgHom_mk _ _ _ y
          _ = _ := (LinearMap.quotKerEquivOfSurjective_apply_mk
            (f : C →ₗ[R] D) hf y).symm
      rw [h]
      exact ((f : C →ₗ[R] D).quotKerEquivOfSurjective hf).bijective)

/-- The equivalence sends the class of a representative to its image. -/
@[simp]
theorem quotKerEquivOfSurjective_apply_mk (f : F) (hf : Function.Surjective f) (x : C) :
    quotKerEquivOfSurjective f hf
      (Submodule.Quotient.mk (p := (f : C →ₗ[R] D).ker) x) = f x :=
  rfl

/-- The inverse sends an image to the class of any of its preimages. -/
@[simp]
theorem quotKerEquivOfSurjective_symm_apply (f : F) (hf : Function.Surjective f) (x : C) :
    (@CoalgEquiv.symm R (C ⧸ (f : C →ₗ[R] D).ker) D
      (inferInstance : CommSemiring R)
      (inferInstance : AddCommMonoid (C ⧸ (f : C →ₗ[R] D).ker))
      (inferInstance : AddCommMonoid D)
      (inferInstance : Module R (C ⧸ (f : C →ₗ[R] D).ker)) mD
      (quotKerCoalgebraStruct f hf) cD
      (quotKerEquivOfSurjective f hf)) (f x) =
      Submodule.Quotient.mk (p := (f : C →ₗ[R] D).ker) x := by
  simpa only [quotKerEquivOfSurjective_apply_mk] using
    (@CoalgEquiv.symm_apply_apply R (C ⧸ (f : C →ₗ[R] D).ker) D
      (inferInstance : CommSemiring R)
      (inferInstance : AddCommMonoid (C ⧸ (f : C →ₗ[R] D).ker))
      (inferInstance : AddCommMonoid D)
      (inferInstance : Module R (C ⧸ (f : C →ₗ[R] D).ker)) mD
      (quotKerCoalgebraStruct f hf) cD
      (quotKerEquivOfSurjective f hf)
      (Submodule.Quotient.mk (p := (f : C →ₗ[R] D).ker) x))

/-- Forgetting the coalgebra structure gives the linear first isomorphism. -/
theorem quotKerEquivOfSurjective_toLinearEquiv (f : F) (hf : Function.Surjective f) :
    @CoalgEquiv.toLinearEquiv R (inferInstance : CommSemiring R)
      (C ⧸ (f : C →ₗ[R] D).ker) D
      (inferInstance : AddCommMonoid (C ⧸ (f : C →ₗ[R] D).ker))
      (inferInstance : AddCommMonoid D)
      (inferInstance : Module R (C ⧸ (f : C →ₗ[R] D).ker)) mD
      (quotKerCoalgebraStruct f hf) cD
      (quotKerEquivOfSurjective f hf) =
      (f : C →ₗ[R] D).quotKerEquivOfSurjective hf := by
  apply LinearEquiv.ext
  intro x
  obtain ⟨y, rfl⟩ := (f : C →ₗ[R] D).ker.mkQ_surjective x
  exact (quotKerEquivOfSurjective_apply_mk f hf y).trans
    (LinearMap.quotKerEquivOfSurjective_apply_mk (f : C →ₗ[R] D) hf y).symm

/-- The selected structure agrees with the quotient structure from any coideality proof. -/
theorem quotKerCoalgebraStruct_eq_stock (f : F) (hf : Function.Surjective f)
    [hker : (f : C →ₗ[R] D).ker.IsCoideal] :
    quotKerCoalgebraStruct f hf =
      (letI : (f : C →ₗ[R] D).ker.IsCoideal := hker
       inferInstance : CoalgebraStruct R (C ⧸ (f : C →ₗ[R] D).ker)) :=
  rfl

/-- The underlying coalgebra morphism is the existing quotient lift, so its factorization
and uniqueness are given by `Submodule.liftQCoalgHom_comp_mkQCoalgHom` and
`Submodule.liftQCoalgHom_unique`. -/
theorem quotKerEquivOfSurjective_toCoalgHom (f : F) (hf : Function.Surjective f)
    [hker : (f : C →ₗ[R] D).ker.IsCoideal] :
    (quotKerEquivOfSurjective f hf).toCoalgHom =
      @Submodule.liftQCoalgHom R rR C aC mC cC D aD mD cD
        (f : C →ₗ[R] D).ker hker (CoalgHom.ofClass f) le_rfl :=
  rfl

end CoalgHomClass
