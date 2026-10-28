/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Coalgebra.TensorProduct

/-!
# Tensor products and coherence of coalgebra maps

For a commutative `R`-algebra `S`, an `S`-linear coalgebra homomorphism on the first
factor and an `R`-linear coalgebra homomorphism on the second induce an `S`-linear
coalgebra homomorphism on their tensor products over `R`. The endpoints need only
comultiplication and counit data, not the coalgebra laws.

* `TensorProduct.mapCoalgHom` bundles `TensorProduct.AlgebraTensorModule.map` using
  the canonical tensor coalgebra data.
* `TensorProduct.mapCoalgHom_id` and `TensorProduct.mapCoalgHom_comp` express
  functoriality.
* `TensorProduct.mapCoalgHom_eq_coalgebraTensorProductMap` identifies this construction
  with Mathlib's tensor product of coalgebra homomorphisms when the endpoints satisfy
  the full coalgebra laws.
* `Coalgebra.TensorProduct.assoc_pentagon` and `Coalgebra.TensorProduct.assoc_triangle`
  give the pentagon and triangle identities for tensor coalgebra homomorphisms.

## References

The tensor coalgebra data and full-law tensor product of coalgebra homomorphisms are
Mathlib's constructions, due to Amelia Livingston and Andrew Yang, in
`Mathlib.RingTheory.Coalgebra.TensorProduct`. Here preservation is generalized to
`CoalgebraStruct` endpoints. The proof uses the heterobasic tensor shuffle and linear
map composition from `Mathlib.LinearAlgebra.TensorProduct.Tower`, together with the
preservation fields from `Mathlib.RingTheory.Coalgebra.Hom`. The coherence identities
reuse Mathlib's tensor associativity coherence and tensor balancing from
`Mathlib.LinearAlgebra.TensorProduct.Associator` and `.Defs`.
-/

@[expose] public section

universe uR uS uM uN uP uQ uN' uQ' uC uD uE uF

open scoped TensorProduct

namespace TensorProduct

variable {R : Type uR} {S : Type uS}
variable {M : Type uM} {N : Type uN} {P : Type uP} {Q : Type uQ}
variable [CommSemiring R] [CommSemiring S] [Algebra R S]
variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q]
variable [Module R M] [Module R N] [Module R P] [Module R Q]
variable [Module S M] [IsScalarTower R S M] [Module S N] [IsScalarTower R S N]

section CoalgebraStruct

variable [CoalgebraStruct S M] [CoalgebraStruct S N]
variable [CoalgebraStruct R P] [CoalgebraStruct R Q]

/-- The tensor product over `R` of an `S`-linear and an `R`-linear coalgebra
homomorphism, with the canonical `S`-coalgebra data on both tensor products.
Only comultiplication and counit data are required on the four factors. -/
noncomputable def mapCoalgHom (f : M →ₗc[S] N) (g : P →ₗc[R] Q) :
    M ⊗[R] P →ₗc[S] N ⊗[R] Q where
  toLinearMap := AlgebraTensorModule.map f.toLinearMap g.toLinearMap
  counit_comp := by
    change Coalgebra.counit (R := S) (A := N ⊗[R] Q) ∘ₗ
        AlgebraTensorModule.map f.toLinearMap g.toLinearMap =
      Coalgebra.counit (R := S) (A := M ⊗[R] P)
    apply AlgebraTensorModule.ext
    intro m p
    change Coalgebra.counit (R := R) (g p) • Coalgebra.counit (R := S) (f m) =
      Coalgebra.counit (R := R) p • Coalgebra.counit (R := S) m
    rw [CoalgHomClass.counit_comp_apply g p, CoalgHomClass.counit_comp_apply f m]
  map_comp_comul := by
    -- Naturality of the heterobasic shuffle reduces to four pure tensors.
    have hshuffle :
        TensorProduct.map (AlgebraTensorModule.map f.toLinearMap g.toLinearMap)
            (AlgebraTensorModule.map f.toLinearMap g.toLinearMap) ∘ₗ
          (AlgebraTensorModule.tensorTensorTensorComm R S R S M M P P).toLinearMap =
        (AlgebraTensorModule.tensorTensorTensorComm R S R S N N Q Q).toLinearMap ∘ₗ
          AlgebraTensorModule.map (TensorProduct.map f.toLinearMap f.toLinearMap)
            (TensorProduct.map g.toLinearMap g.toLinearMap) := by
      ext m₁ m₂ p₁ p₂
      rfl
    rw [comul_def, comul_def, ← LinearMap.comp_assoc, hshuffle,
      LinearMap.comp_assoc, ← AlgebraTensorModule.map_comp, f.map_comp_comul,
      g.map_comp_comul, AlgebraTensorModule.map_comp, ← LinearMap.comp_assoc]

/-- The underlying linear map is the heterobasic tensor product of the factor maps. -/
@[simp]
theorem mapCoalgHom_toLinearMap (f : M →ₗc[S] N) (g : P →ₗc[R] Q) :
    (mapCoalgHom f g : M ⊗[R] P →ₗ[S] N ⊗[R] Q) =
      AlgebraTensorModule.map f.toLinearMap g.toLinearMap :=
  rfl

/-- The tensor product of coalgebra homomorphisms acts factorwise on pure tensors. -/
@[simp]
theorem mapCoalgHom_tmul (f : M →ₗc[S] N) (g : P →ₗc[R] Q) (m : M) (p : P) :
    mapCoalgHom f g (m ⊗ₜ[R] p) = f m ⊗ₜ[R] g p :=
  rfl

/-- Tensoring identity coalgebra homomorphisms gives the identity. -/
@[simp]
theorem mapCoalgHom_id :
    mapCoalgHom (CoalgHom.id S M) (CoalgHom.id R P) =
      CoalgHom.id S (M ⊗[R] P) := by
  apply CoalgHom.coe_linearMap_injective
  exact AlgebraTensorModule.map_id

variable {N' : Type uN'} {Q' : Type uQ'}
variable [AddCommMonoid N'] [Module R N'] [Module S N'] [IsScalarTower R S N']
variable [CoalgebraStruct S N']
variable [AddCommMonoid Q'] [Module R Q'] [CoalgebraStruct R Q']

/-- Tensor products of coalgebra homomorphisms preserve composition. -/
@[simp]
theorem mapCoalgHom_comp (f₁ : M →ₗc[S] N) (f₂ : N →ₗc[S] N')
    (g₁ : P →ₗc[R] Q) (g₂ : Q →ₗc[R] Q') :
    mapCoalgHom (f₂.comp f₁) (g₂.comp g₁) =
      (mapCoalgHom f₂ g₂).comp (mapCoalgHom f₁ g₁) := by
  apply CoalgHom.coe_linearMap_injective
  exact AlgebraTensorModule.map_comp f₂.toLinearMap f₁.toLinearMap
    g₂.toLinearMap g₁.toLinearMap

end CoalgebraStruct

section Coalgebra

variable [Coalgebra S M] [Coalgebra S N] [Coalgebra R P] [Coalgebra R Q]

/-- For full coalgebras, `mapCoalgHom` agrees with Mathlib's tensor product of
coalgebra homomorphisms. -/
theorem mapCoalgHom_eq_coalgebraTensorProductMap (f : M →ₗc[S] N) (g : P →ₗc[R] Q) :
    mapCoalgHom f g = Coalgebra.TensorProduct.map (R := R) (S := S) f g := by
  apply CoalgHom.coe_linearMap_injective
  rfl

end Coalgebra

end TensorProduct

namespace Coalgebra.TensorProduct

variable (R : Type uR) [CommSemiring R]
variable (C : Type uC) (D : Type uD)
variable [AddCommMonoid C] [AddCommMonoid D] [Module R C] [Module R D]
variable [Coalgebra R C] [Coalgebra R D]

section Pentagon

variable (E : Type uE) (F : Type uF)
variable [AddCommMonoid E] [AddCommMonoid F] [Module R E] [Module R F]
variable [Coalgebra R E] [Coalgebra R F]

/-- The three-edge and two-edge associator paths for four tensor coalgebras agree. -/
theorem assoc_pentagon :
    (map (R := R) (S := R) (CoalgHom.id R C)
        (Coalgebra.TensorProduct.assoc R R D E F).toCoalgHom).comp
        ((Coalgebra.TensorProduct.assoc R R C (D ⊗[R] E) F).toCoalgHom.comp
          (map (R := R) (S := R) (Coalgebra.TensorProduct.assoc R R C D E).toCoalgHom
            (CoalgHom.id R F))) =
      (Coalgebra.TensorProduct.assoc R R C D (E ⊗[R] F)).toCoalgHom.comp
        (Coalgebra.TensorProduct.assoc R R (C ⊗[R] D) E F).toCoalgHom := by
  apply CoalgHom.coe_linearMap_injective
  refine _root_.TensorProduct.ext_fourfold fun (c : C) (d : D) (e : E) (f : F) => ?_
  change c ⊗ₜ[R] (d ⊗ₜ[R] (e ⊗ₜ[R] f)) = c ⊗ₜ[R] (d ⊗ₜ[R] (e ⊗ₜ[R] f))
  rfl

end Pentagon

/-- The right unitor tensored with the identity agrees with the associator followed
by the identity tensored with the left unitor, using the scalar coalgebra on `R`. -/
theorem assoc_triangle :
    map (R := R) (S := R) (Coalgebra.TensorProduct.rid R R C).toCoalgHom (CoalgHom.id R D) =
      (map (R := R) (S := R) (CoalgHom.id R C) (Coalgebra.TensorProduct.lid R D).toCoalgHom).comp
        (Coalgebra.TensorProduct.assoc R R C R D).toCoalgHom := by
  apply CoalgHom.coe_linearMap_injective
  refine _root_.TensorProduct.ext_threefold fun (c : C) (s : R) (d : D) => ?_
  change (s • c) ⊗ₜ[R] d = c ⊗ₜ[R] (s • d)
  exact _root_.TensorProduct.smul_tmul s c d

end Coalgebra.TensorProduct
