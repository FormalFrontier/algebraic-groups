/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Coalgebra.Basic
public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.Transport
public import AlgebraicGroups.Algebra.Coalgebra.RightComodule
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.RingTheory.Coalgebra.MonoidAlgebra

/-!
# Transport of regular comodules and its boundary cases

The diagonal natural-coefficient comodule is transported by translation of its
integer-labelled basis. The resulting coaction differs from the regular one.
We check the canonical transport morphisms, inverse recovery, composition, and
the zero subcomodule, keeping the scalar and coalgebra structures fixed.

## References

Mathlib supplies arrow congruence, tensor equivalences, label permutations and
the diagonal monoid-algebra coalgebra. The specified regular comodule uses
`TauCeti.Comodule`; its bottom subcomodule uses `TauCeti.Subcomodule`.
-/

@[expose] public section

universe uR uC uV uW uZ

open scoped TensorProduct
open Coalgebra

namespace TauCeti.Comodule

noncomputable section

private def conjugatedCoaction {R : Type uR} {C : Type uC} {V : Type uV} {W : Type uW}
    [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
    [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]
    (X : Comodule R C V) (e : V ≃ₗ[R] W) : W →ₗ[R] W ⊗[R] C :=
  letI := X
  transportCoact (C := C) e

private abbrev Diagonal := MonoidAlgebra ℕ (Multiplicative ℤ)

/-- The coefficient-one vector at an integer label. -/
private def delta (n : ℤ) : Diagonal :=
  MonoidAlgebra.single (Multiplicative.ofAdd n) 1

/-- The regular comodule of the diagonal natural-coefficient coalgebra. -/
@[instance_reducible] private def diagonalRegular : Comodule ℕ Diagonal Diagonal :=
  Comodule.instSelf ℕ Diagonal

/-- Translation of the integer labels by one. -/
private def labelShift : Multiplicative ℤ ≃ Multiplicative ℤ :=
  Equiv.mulRight (Multiplicative.ofAdd (1 : ℤ))

/-- The linear equivalence induced by translating the integer labels. -/
private def shift : Diagonal ≃ₗ[ℕ] Diagonal :=
  MonoidAlgebra.mapDomainLinearEquiv ℕ ℕ labelShift

/-- The diagonal regular comodule transported by translation of its module basis. -/
@[instance_reducible] private def shiftedRegular : Comodule ℕ Diagonal Diagonal :=
  (letI := diagonalRegular; Transport (C := Diagonal) shift)

/-- The regular coact conjugated by translation of its module basis. -/
private def shiftedCoaction : Diagonal →ₗ[ℕ] Diagonal ⊗[ℕ] Diagonal :=
  shiftedRegular.coact

private theorem shiftedCoaction_coassoc :
    (TensorProduct.assoc ℕ Diagonal Diagonal Diagonal).toLinearMap ∘ₗ
        shiftedCoaction.rTensor Diagonal ∘ₗ shiftedCoaction =
      (comul (R := ℕ) (A := Diagonal)).lTensor Diagonal ∘ₗ shiftedCoaction :=
  shiftedRegular.coassoc

private theorem shiftedCoaction_counit_comp :
    (counit (R := ℕ) (A := Diagonal)).lTensor Diagonal ∘ₗ shiftedCoaction =
      (TensorProduct.rid ℕ Diagonal).symm.toLinearMap :=
  shiftedRegular.lTensor_counit_comp_coact

private theorem shift_delta (n : ℤ) : shift (delta n) = delta (n + 1) := by
  simp only [shift, delta, MonoidAlgebra.mapDomainLinearEquiv_single,
    labelShift, Equiv.coe_mulRight, ofAdd_add]

private theorem shift_symm_delta (n : ℤ) : shift.symm (delta n) = delta (n - 1) := by
  apply shift.injective
  rw [shift.apply_symm_apply, shift_delta, sub_add_cancel]

private theorem diagonalRegular_coact_delta (n : ℤ) :
    diagonalRegular.coact (delta n) = delta n ⊗ₜ[ℕ] delta n := by
  change Coalgebra.comul (R := ℕ) (delta n) = _
  simp only [delta,
    MonoidAlgebra.comul_single, CommSemiring.comul_apply, TensorProduct.map_tmul,
    MonoidAlgebra.lsingle_apply]

private theorem shiftedCoaction_delta (n : ℤ) :
    shiftedCoaction (delta n) = delta n ⊗ₜ[ℕ] delta (n - 1) := by
  change ((letI := diagonalRegular; Transport (C := Diagonal) shift)).coact (delta n) = _
  rw [transport_coact_apply, shift_symm_delta,
    diagonalRegular_coact_delta, TensorProduct.map_tmul, LinearMap.id_apply,
        LinearEquiv.coe_coe, shift_delta, sub_add_cancel]

private theorem shiftedCoaction_delta_zero_ne :
    shiftedCoaction (delta 0) ≠ diagonalRegular.coact (delta 0) ∧
      shiftedCoaction (delta 0) ≠ 0 := by
  have hshifted : shiftedCoaction (delta 0) = delta 0 ⊗ₜ[ℕ] delta (-1) := by
    simpa only [zero_sub] using shiftedCoaction_delta 0
  have hregular : diagonalRegular.coact (delta 0) = delta 0 ⊗ₜ[ℕ] delta 0 := by
    exact diagonalRegular_coact_delta 0
  -- Applying the counit to the first factor detects the unchanged coalgebra label.
  have hdetect (d : Diagonal) :
      TensorProduct.lid ℕ Diagonal
        ((counit (R := ℕ) (A := Diagonal)).rTensor Diagonal (delta 0 ⊗ₜ[ℕ] d)) = d := by
    simp [delta]
  constructor
  · intro h
    have hd : delta (-1) = delta 0 := by
      have ht := congrArg (fun t : Diagonal ⊗[ℕ] Diagonal =>
        TensorProduct.lid ℕ Diagonal
          ((counit (R := ℕ) (A := Diagonal)).rTensor Diagonal t)) h
      simpa only [hshifted, hregular, hdetect] using ht
    have hc := congrArg (fun d : Diagonal => d.coeff (Multiplicative.ofAdd (-1 : ℤ))) hd
    simp [delta] at hc
  · intro h
    have hd : delta (-1) = 0 := by
      have ht := congrArg (fun t : Diagonal ⊗[ℕ] Diagonal =>
        TensorProduct.lid ℕ Diagonal
          ((counit (R := ℕ) (A := Diagonal)).rTensor Diagonal t)) h
      simpa only [hshifted, hdetect, map_zero] using ht
    simp [delta] at hd


attribute [local instance] diagonalRegular

private def shiftForward :
    @Hom ℕ Diagonal Diagonal Diagonal _ _ _ _ _ _ diagonalRegular _ _ shiftedRegular :=
  transportToHom (C := Diagonal) shift

private def shiftBackward :
    @Hom ℕ Diagonal Diagonal Diagonal _ _ _ _ _ _ shiftedRegular _ _ diagonalRegular :=
  transportInvHom (C := Diagonal) shift

private theorem shiftForward_apply (v : Diagonal) : shiftForward v = shift v :=
  transportToHom_apply shift v

private theorem shiftBackward_apply (v : Diagonal) : shiftBackward v = shift.symm v :=
  transportInvHom_apply shift v

/-- The canonical colinear pair, repeated transport and inverse recovery on the translated model. -/
example (n : ℤ) :
    (shiftedCoaction (delta 0) ≠ diagonalRegular.coact (delta 0) ∧
      shiftedCoaction (delta 0) ≠ 0) ∧
    ¬ (diagonalRegular.coact ∘ₗ shift.toLinearMap =
      shift.toLinearMap.rTensor Diagonal ∘ₗ diagonalRegular.coact) ∧
    shiftedRegular.coact (shiftForward (delta n)) = delta (n + 1) ⊗ₜ[ℕ] delta n ∧
    shiftBackward (delta n) = delta (n - 1) ∧
    diagonalRegular.coact (shiftBackward (delta n)) =
      delta (n - 1) ⊗ₜ[ℕ] delta (n - 1) ∧
    (letI := shiftedRegular; Transport (C := Diagonal) shift).coact (delta n) =
      delta n ⊗ₜ[ℕ] delta (n - 2) ∧
    (letI := shiftedRegular; Transport (C := Diagonal) shift.symm) = diagonalRegular ∧
    shiftBackward (shiftForward (delta n)) = delta n ∧
    shiftForward (shiftBackward (delta n)) = delta n := by
  refine ⟨shiftedCoaction_delta_zero_ne, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have htransport := (transport_eq_iff_colinear shift diagonalRegular).mpr h
    exact shiftedCoaction_delta_zero_ne.1
      (congrArg (fun X : Comodule ℕ Diagonal Diagonal ↦ X.coact (delta 0)) htransport)
  · rw [shiftForward_apply, shift_delta]
    change shiftedCoaction (delta (n + 1)) = _
    simpa only [add_sub_cancel_right] using shiftedCoaction_delta (n + 1)
  · rw [shiftBackward_apply, shift_symm_delta]
  · rw [shiftBackward_apply, shift_symm_delta, diagonalRegular_coact_delta]
  · rw [@transport_coact_apply ℕ Diagonal Diagonal Diagonal _ _ _ _ _ _
      shiftedRegular _ _ shift, shift_symm_delta]
    change TensorProduct.map shift.toLinearMap LinearMap.id
      (shiftedCoaction (delta (n - 1))) = _
    rw [shiftedCoaction_delta, TensorProduct.map_tmul, LinearMap.id_apply,
      LinearEquiv.coe_coe, shift_delta, sub_add_cancel, sub_sub, one_add_one_eq_two]
  · exact transport_symm shift
  · rw [shiftBackward_apply, shiftForward_apply, shift.symm_apply_apply]
  · rw [shiftForward_apply, shiftBackward_apply, shift.apply_symm_apply]

/-- The bottom carrier is a canonical subcomodule, with its canonical induced coaction. -/
private def diagonalBottom : TauCeti.Subcomodule ℕ Diagonal Diagonal := ⊥

private theorem conjugatedCoaction_bottom_refl :
    conjugatedCoaction (TauCeti.Subcomodule.instComodule diagonalBottom)
      (LinearEquiv.refl ℕ diagonalBottom) =
      (TauCeti.Subcomodule.instComodule diagonalBottom).coact := by
  exact transportCoact_refl

example :
    (letI := TauCeti.Subcomodule.instComodule diagonalBottom
     Transport (C := Diagonal) (LinearEquiv.refl ℕ diagonalBottom)) =
      TauCeti.Subcomodule.instComodule diagonalBottom ∧
    (letI := TauCeti.Subcomodule.instComodule diagonalBottom
     transportToHom (C := Diagonal) (LinearEquiv.refl ℕ diagonalBottom) 0) = 0 ∧
    (letI := TauCeti.Subcomodule.instComodule diagonalBottom
     transportInvHom (C := Diagonal) (LinearEquiv.refl ℕ diagonalBottom) 0) = 0 := by
  refine ⟨transport_refl, ?_, ?_⟩ <;> simp only [transportToHom_apply,
    transportInvHom_apply, LinearEquiv.refl_apply, LinearEquiv.refl_symm]

end

end TauCeti.Comodule

namespace TauCeti.Comodule

section CarrierTransport

variable {R : Type uR} {C : Type uC} {V : Type uV} {W : Type uW} {Z : Type uZ}
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]
variable [AddCommMonoid Z] [Module R Z]

/-- The function type for transporting a specified right coact along a carrier
linear equivalence, with the scalar and coalgebra structures unchanged. -/
private def carrierTransportType : Type _ :=
  (X : Comodule R C V) → (e : V ≃ₗ[R] W) → Comodule R C W

/-- The coact, pullback, uniqueness and colinearity equations for carrier transport.
The tensor map acts on the module factor and fixes the coalgebra factor. All right
comodules on `W` use its given additive and scalar-module structures. -/
private def carrierTransportCoaction
    (transport : carrierTransportType (R := R) (C := C) (V := V) (W := W)) : Prop :=
  ∀ (X : Comodule R C V) (e : V ≃ₗ[R] W),
    (transport X e).coact = conjugatedCoaction X e ∧
    (transport X e).coact =
      e.toLinearMap.rTensor C ∘ₗ X.coact ∘ₗ e.symm.toLinearMap ∧
    (∀ w : W, (transport X e).coact w =
      e.toLinearMap.rTensor C (X.coact (e.symm w))) ∧
    (e.symm.toLinearMap.rTensor C ∘ₗ (transport X e).coact ∘ₗ e.toLinearMap =
      X.coact) ∧
    (∀ Y : Comodule R C W,
      transport X e = Y ↔ Y.coact = conjugatedCoaction X e) ∧
    (∀ Y : Comodule R C W,
      transport X e = Y ↔
        Y.coact ∘ₗ e.toLinearMap = e.toLinearMap.rTensor C ∘ₗ X.coact) ∧
    ((transport X e).coact ∘ₗ e.toLinearMap =
      e.toLinearMap.rTensor C ∘ₗ X.coact) ∧
    (∀ v : V, (transport X e).coact (e v) =
      e.toLinearMap.rTensor C (X.coact v)) ∧
    (X.coact ∘ₗ e.symm.toLinearMap =
      e.symm.toLinearMap.rTensor C ∘ₗ (transport X e).coact) ∧
    (∀ w : W, X.coact (e.symm w) =
      e.symm.toLinearMap.rTensor C ((transport X e).coact w))

/-- Identity, composition, inverse transport and recovery of specified coacts.
The five functions represent the indicated specializations of one carrier-transport
construction. Their separate domains and codomains keep the universes of `V`, `W`
and `Z` independent; every specialization fixes the same coalgebra and given module structures. -/
private def carrierTransportCoherence
    (transportVW : carrierTransportType (R := R) (C := C) (V := V) (W := W))
    (transportWZ : carrierTransportType (R := R) (C := C) (V := W) (W := Z))
    (transportVZ : carrierTransportType (R := R) (C := C) (V := V) (W := Z))
    (transportWV : carrierTransportType (R := R) (C := C) (V := W) (W := V))
    (transportVV : carrierTransportType (R := R) (C := C) (V := V) (W := V)) : Prop :=
  carrierTransportCoaction transportVW ∧
  carrierTransportCoaction transportWZ ∧
  carrierTransportCoaction transportVZ ∧
  carrierTransportCoaction transportWV ∧
  carrierTransportCoaction transportVV ∧
  (∀ X : Comodule R C V, transportVV X (LinearEquiv.refl R V) = X) ∧
  (∀ (X : Comodule R C V) (e : V ≃ₗ[R] W) (f : W ≃ₗ[R] Z),
    transportWZ (transportVW X e) f = transportVZ X (e.trans f)) ∧
  (∀ (X : Comodule R C V) (e : V ≃ₗ[R] W),
    transportWV (transportVW X e) e.symm = X) ∧
  (∀ (Y : Comodule R C W) (e : V ≃ₗ[R] W),
    transportVW (transportWV Y e.symm) e = Y) ∧
  (∀ (X : Comodule R C V) (Y : Comodule R C W) (e : V ≃ₗ[R] W),
    transportWV Y e.symm = X ↔ transportVW X e = Y)

end CarrierTransport

/-- Carrier-transport equations on the translated diagonal regular coact and
on the identity of its bottom subcomodule. The raw translated coact satisfies
`shiftedCoaction_delta` and `shiftedCoaction_delta_zero_ne`, while the bottom
identity satisfies `conjugatedCoaction_bottom_refl`. The tensor extension of translation
fixes the second factor; translation is not an automorphism of the fixed regular comodule. -/
private def diagonalCarrierTransportEquations
    (transport : carrierTransportType (R := ℕ) (C := Diagonal)
      (V := Diagonal) (W := Diagonal))
    (transportBottom : carrierTransportType (R := ℕ) (C := Diagonal)
      (V := diagonalBottom) (W := diagonalBottom)) : Prop :=
  (transport diagonalRegular shift).coact = shiftedCoaction ∧
  (∀ n : ℤ, (transport diagonalRegular shift).coact (delta n) =
    delta n ⊗ₜ[ℕ] delta (n - 1)) ∧
  ((transport diagonalRegular shift).coact (delta 0) ≠
      diagonalRegular.coact (delta 0) ∧
    (transport diagonalRegular shift).coact (delta 0) ≠ 0) ∧
  transport diagonalRegular (LinearEquiv.refl ℕ Diagonal) = diagonalRegular ∧
  transportBottom (TauCeti.Subcomodule.instComodule diagonalBottom)
    (LinearEquiv.refl ℕ diagonalBottom) = (TauCeti.Subcomodule.instComodule diagonalBottom)

end TauCeti.Comodule
