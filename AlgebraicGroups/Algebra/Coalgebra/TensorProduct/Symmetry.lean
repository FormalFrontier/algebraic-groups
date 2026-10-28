/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Coalgebra.TensorProduct

/-!
# Symmetry of tensor products of coalgebras

The tensor permutation preserves the canonical counit and comultiplication over a
commutative semiring. Its inverse, involutivity and naturality are bundled here.
The proof uses a four-factor shuffle identity and Mathlib's tensor coalgebra
construction by Amelia Livingston and Andrew Yang.
-/

@[expose] public section

open scoped TensorProduct

universe uR uC uD uC' uD'

namespace Coalgebra.TensorProduct

variable (R : Type uR) (C : Type uC) (D : Type uD)
variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid D] [Module R D] [Coalgebra R D]

omit [Coalgebra R C] [Coalgebra R D] in
private theorem comm_shuffle :
    _root_.TensorProduct.map
        (_root_.TensorProduct.comm R C D).toLinearMap
        (_root_.TensorProduct.comm R C D).toLinearMap ∘ₗ
      (_root_.TensorProduct.tensorTensorTensorComm R C C D D).toLinearMap =
    (_root_.TensorProduct.tensorTensorTensorComm R D D C C).toLinearMap ∘ₗ
      (_root_.TensorProduct.comm R (C ⊗[R] C) (D ⊗[R] D)).toLinearMap := by
  apply _root_.TensorProduct.ext_fourfold'
  intro c₁ c₂ d₁ d₂
  rfl

/-- Interchange the two factors of the tensor product of coalgebras. -/
noncomputable def comm : C ⊗[R] D ≃ₗc[R] D ⊗[R] C :=
  { _root_.TensorProduct.comm R C D with
    counit_comp := by ext; simp [mul_comm]
    map_comp_comul := by
      apply _root_.TensorProduct.ext'
      intro c d
      simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
        _root_.TensorProduct.comm_tmul, _root_.TensorProduct.comul_tmul,
        _root_.TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_eq] using
        LinearMap.congr_fun (comm_shuffle R C D)
          (comul (R := R) c ⊗ₜ[R] comul (R := R) d) }

/-- Forgetting the coalgebra structure gives the tensor permutation. -/
@[simp] theorem comm_toLinearEquiv :
    (comm R C D).toLinearEquiv = _root_.TensorProduct.comm R C D := rfl

/-- The coefficient homomorphism has the tensor permutation as its linear map. -/
@[simp] theorem comm_toCoalgHom_toLinearMap :
    ((comm R C D : C ⊗[R] D →ₗc[R] D ⊗[R] C) :
        C ⊗[R] D →ₗ[R] D ⊗[R] C) =
      (_root_.TensorProduct.comm R C D).toLinearMap := rfl

/-- Symmetry interchanges pure factors. -/
@[simp] theorem comm_tmul (c : C) (d : D) :
    comm R C D (c ⊗ₜ[R] d) = d ⊗ₜ[R] c := rfl

/-- Inverse symmetry interchanges pure factors. -/
theorem comm_symm_tmul (c : C) (d : D) :
    (comm R C D).symm (d ⊗ₜ[R] c) = c ⊗ₜ[R] d := rfl

/-- The inverse is symmetry with exchanged coefficient types. -/
@[simp] theorem comm_symm : (comm R C D).symm = comm R D C := by
  apply CoalgEquiv.ext
  intro z
  rfl

/-- Interchanging the factors twice is the identity coalgebra equivalence. -/
@[simp] theorem comm_trans_comm :
    (comm R C D).trans (comm R D C) = CoalgEquiv.refl R (C ⊗[R] D) := by
  apply CoalgEquiv.ext
  intro z
  exact (_root_.TensorProduct.comm R C D).symm_apply_apply z

variable {R C D}
variable {C' : Type uC'} {D' : Type uD'}
variable [AddCommMonoid C'] [Module R C'] [Coalgebra R C']
variable [AddCommMonoid D'] [Module R D'] [Coalgebra R D']

/-- Coefficient symmetry is natural in both coalgebra homomorphisms. -/
theorem comm_naturality (f : C →ₗc[R] C') (g : D →ₗc[R] D') :
    (comm R C' D').toCoalgHom.comp (map f g) =
      (map g f).comp (comm R C D).toCoalgHom := by
  apply CoalgHom.coe_linearMap_injective
  refine _root_.TensorProduct.ext' fun (c : C) (d : D) => ?_
  rfl

end Coalgebra.TensorProduct

universe uE

namespace Coalgebra.TensorProduct

variable (R : Type uR) (C : Type uC) (D : Type uD) (E : Type uE)
variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid D] [Module R D] [Coalgebra R D]
variable [AddCommMonoid E] [Module R E] [Coalgebra R E]

/-- The three-edge hexagon for tensor coalgebras. Both routes permute the
three factors from `((C ⊗ D) ⊗ E)` to `D ⊗ (E ⊗ C)`. The carrier calculation
follows Mathlib's `SemimoduleCat.MonoidalCategory.hexagon_forward`, without its
common carrier-universe restriction. -/
theorem comm_hexagon :
    (Coalgebra.TensorProduct.assoc R R D E C).toCoalgHom.comp
        ((comm R C (D ⊗[R] E)).toCoalgHom.comp
          (Coalgebra.TensorProduct.assoc R R C D E).toCoalgHom) =
      (map (CoalgHom.id R D) (comm R C E).toCoalgHom).comp
        ((Coalgebra.TensorProduct.assoc R R D C E).toCoalgHom.comp
          (map (comm R C D).toCoalgHom (CoalgHom.id R E))) := by
  apply CoalgHom.coe_linearMap_injective
  apply _root_.TensorProduct.ext_threefold
  intro c d e
  rfl

/-- The reverse hexagon is the inverse of `comm_hexagon R E C D`.
It maps `C ⊗ (D ⊗ E)` to `(E ⊗ C) ⊗ D`. -/
theorem comm_hexagon_reverse :
    (Coalgebra.TensorProduct.assoc R R E C D).symm.toCoalgHom.comp
        ((comm R (C ⊗[R] D) E).toCoalgHom.comp
          (Coalgebra.TensorProduct.assoc R R C D E).symm.toCoalgHom) =
      (map (comm R C E).toCoalgHom (CoalgHom.id R D)).comp
        ((Coalgebra.TensorProduct.assoc R R C E D).symm.toCoalgHom.comp
          (map (CoalgHom.id R C) (comm R D E).toCoalgHom)) := by
  let pL : ((E ⊗[R] C) ⊗[R] D) →ₗc[R] C ⊗[R] (D ⊗[R] E) :=
    (Coalgebra.TensorProduct.assoc R R C D E).toCoalgHom.comp
      ((comm R E (C ⊗[R] D)).toCoalgHom.comp
        (Coalgebra.TensorProduct.assoc R R E C D).toCoalgHom)
  let pS : ((E ⊗[R] C) ⊗[R] D) →ₗc[R] C ⊗[R] (D ⊗[R] E) :=
    (map (CoalgHom.id R C) (comm R E D).toCoalgHom).comp
      ((Coalgebra.TensorProduct.assoc R R C E D).toCoalgHom.comp
        (map (comm R E C).toCoalgHom (CoalgHom.id R D)))
  let qL : C ⊗[R] (D ⊗[R] E) →ₗc[R] (E ⊗[R] C) ⊗[R] D :=
    (Coalgebra.TensorProduct.assoc R R E C D).symm.toCoalgHom.comp
      ((comm R (C ⊗[R] D) E).toCoalgHom.comp
        (Coalgebra.TensorProduct.assoc R R C D E).symm.toCoalgHom)
  let qS : C ⊗[R] (D ⊗[R] E) →ₗc[R] (E ⊗[R] C) ⊗[R] D :=
    (map (comm R C E).toCoalgHom (CoalgHom.id R D)).comp
      ((Coalgebra.TensorProduct.assoc R R C E D).symm.toCoalgHom.comp
        (map (CoalgHom.id R C) (comm R D E).toCoalgHom))
  have h : pL = pS := comm_hexagon R E C D
  -- These are inverse identities, not a second hexagon calculation.
  have hpL : pL.comp qL = CoalgHom.id R (C ⊗[R] (D ⊗[R] E)) := by
    apply CoalgHom.coe_linearMap_injective
    apply _root_.TensorProduct.ext_threefold'
    intro c d e
    rfl
  have hpS : qS.comp pS = CoalgHom.id R ((E ⊗[R] C) ⊗[R] D) := by
    apply CoalgHom.coe_linearMap_injective
    apply _root_.TensorProduct.ext_threefold
    intro e c d
    rfl
  change qL = qS
  calc
    qL = (CoalgHom.id R ((E ⊗[R] C) ⊗[R] D)).comp qL :=
      (CoalgHom.id_comp qL).symm
    _ = (qS.comp pS).comp qL := by rw [hpS]
    _ = (qS.comp pL).comp qL := by rw [h]
    _ = qS.comp (pL.comp qL) := CoalgHom.comp_assoc qS pL qL
    _ = qS := by rw [hpL, CoalgHom.comp_id]

/-- Symmetry followed by the right unitor is the left unitor. The scalar
coalgebra is the canonical `CommSemiring.toCoalgebra R`. This is the bundled
coalgebra version of `TensorProduct.comm_trans_rid`. -/
theorem comm_unit_left :
    (Coalgebra.TensorProduct.rid R R C).toCoalgHom.comp (comm R R C).toCoalgHom =
      (Coalgebra.TensorProduct.lid R C).toCoalgHom := by
  apply CoalgHom.coe_linearMap_injective
  exact congrArg LinearEquiv.toLinearMap
    (_root_.TensorProduct.comm_trans_rid (R := R) (M := C))

/-- Symmetry followed by the left unitor is the right unitor. This is the
bundled coalgebra version of `TensorProduct.comm_trans_lid`. -/
theorem comm_unit_right :
    (Coalgebra.TensorProduct.lid R C).toCoalgHom.comp (comm R C R).toCoalgHom =
      (Coalgebra.TensorProduct.rid R R C).toCoalgHom := by
  apply CoalgHom.coe_linearMap_injective
  exact congrArg LinearEquiv.toLinearMap
    (_root_.TensorProduct.comm_trans_lid (R := R) (M := C))

end Coalgebra.TensorProduct
