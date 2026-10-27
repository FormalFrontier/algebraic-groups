/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Coalgebra.Basic
import AlgebraicGroups.Algebra.Coalgebra.RightComodule.Transport
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Algebra.Ring.Nat
import Mathlib.RingTheory.Coalgebra.MonoidAlgebra

/-!
# Conjugated right coactions and basis permutations

Arrow congruence along a linear equivalence `V ≃ₗ[R] W` sends the coaction of a
specified right `C`-comodule on `V` to a linear map `W →ₗ[R] W ⊗[R] C`.
The coalgebra `C` and its scalar-module structures stay fixed.

For the diagonal coalgebra on `MonoidAlgebra ℕ (Multiplicative ℤ)`, translation
of the integer basis labels leads to the equation `δₙ ↦ δₙ ⊗ δₙ₋₁`.
The equations below concern coassociativity, right counitality, the translated
basis and identity on the bottom subcomodule of the regular comodule. The
canonical inverse colinear maps and successive transport are exercised on the
same translated basis, including recovery of the original specified coaction.

## References

Mathlib supplies arrow congruence, tensor equivalences, label permutations and
the diagonal monoid-algebra coalgebra. The specified regular comodule and its
bottom subcomodule come from `Coalgebra.RightComodule`.
-/

@[expose] public section

universe uR uC uV uW uZ

open scoped TensorProduct

namespace Coalgebra.RightComodule

noncomputable section

section Conjugation

variable {R : Type uR} {C : Type uC} {V : Type uV} {W : Type uW}
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]

/-- Conjugation of a specified coaction, changing only its module factor. -/
private def conjugatedCoaction (X : RightComodule R C V) (e : V ≃ₗ[R] W) :
    W →ₗ[R] W ⊗[R] C :=
  (transport X e).coaction

end Conjugation

private abbrev Diagonal := MonoidAlgebra ℕ (Multiplicative ℤ)

/-- The coefficient-one vector at an integer label. -/
private def delta (n : ℤ) : Diagonal :=
  MonoidAlgebra.single (Multiplicative.ofAdd n) 1

/-- The regular comodule of the diagonal natural-coefficient coalgebra. -/
private def diagonalRegular : RightComodule ℕ Diagonal Diagonal :=
  RightComodule.regular ℕ Diagonal

/-- Translation of the integer labels by one. -/
private def labelShift : Multiplicative ℤ ≃ Multiplicative ℤ :=
  Equiv.mulRight (Multiplicative.ofAdd (1 : ℤ))

/-- The linear equivalence induced by translating the integer labels. -/
private def shift : Diagonal ≃ₗ[ℕ] Diagonal :=
  MonoidAlgebra.mapDomainLinearEquiv ℕ ℕ labelShift

/-- The diagonal regular comodule transported by translation of its module basis. -/
private def shiftedRegular : RightComodule ℕ Diagonal Diagonal :=
  diagonalRegular.transport shift

/-- The regular coaction conjugated by translation of its module basis. -/
private def shiftedCoaction : Diagonal →ₗ[ℕ] Diagonal ⊗[ℕ] Diagonal :=
  shiftedRegular.coaction

private theorem shiftedCoaction_coassoc :
    (TensorProduct.assoc ℕ Diagonal Diagonal Diagonal).toLinearMap ∘ₗ
        shiftedCoaction.rTensor Diagonal ∘ₗ shiftedCoaction =
      (comul (R := ℕ) (A := Diagonal)).lTensor Diagonal ∘ₗ shiftedCoaction :=
  shiftedRegular.coassoc

private theorem shiftedCoaction_counit_comp :
    (counit (R := ℕ) (A := Diagonal)).lTensor Diagonal ∘ₗ shiftedCoaction =
      (TensorProduct.rid ℕ Diagonal).symm.toLinearMap :=
  shiftedRegular.counit_comp

private theorem shift_delta (n : ℤ) : shift (delta n) = delta (n + 1) := by
  simp only [shift, delta, MonoidAlgebra.mapDomainLinearEquiv_single,
    labelShift, Equiv.coe_mulRight, ofAdd_add]

private theorem shift_symm_delta (n : ℤ) : shift.symm (delta n) = delta (n - 1) := by
  apply shift.injective
  rw [shift.apply_symm_apply, shift_delta, sub_add_cancel]

private theorem diagonalRegular_coaction_delta (n : ℤ) :
    diagonalRegular.coaction (delta n) = delta n ⊗ₜ[ℕ] delta n := by
  simp only [diagonalRegular, RightComodule.regular_coaction, delta,
    MonoidAlgebra.comul_single, CommSemiring.comul_apply, TensorProduct.map_tmul,
    MonoidAlgebra.lsingle_apply]

private theorem shiftedCoaction_delta (n : ℤ) :
    shiftedCoaction (delta n) = delta n ⊗ₜ[ℕ] delta (n - 1) := by
  change (diagonalRegular.transport shift).coaction (delta n) = _
  rw [transport_coaction, LinearEquiv.arrowCongr_apply, shift_symm_delta,
    diagonalRegular_coaction_delta, LinearEquiv.rTensor_tmul, shift_delta, sub_add_cancel]

private theorem shiftedCoaction_delta_zero_ne :
    shiftedCoaction (delta 0) ≠ diagonalRegular.coaction (delta 0) ∧
      shiftedCoaction (delta 0) ≠ 0 := by
  have hshifted : shiftedCoaction (delta 0) = delta 0 ⊗ₜ[ℕ] delta (-1) := by
    simpa only [zero_sub] using shiftedCoaction_delta 0
  have hregular : diagonalRegular.coaction (delta 0) = delta 0 ⊗ₜ[ℕ] delta 0 := by
    simp [diagonalRegular, delta]
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

/-- The canonical colinear pair on a genuinely changed coaction, its second
transport and inverse recovery, evaluated on the integer-labelled basis. -/
example (n : ℤ) :
    (shiftedCoaction (delta 0) ≠ diagonalRegular.coaction (delta 0) ∧
      shiftedCoaction (delta 0) ≠ 0) ∧
    ¬ (diagonalRegular.coaction ∘ₗ shift.toLinearMap =
      shift.toLinearMap.rTensor Diagonal ∘ₗ diagonalRegular.coaction) ∧
    shiftedRegular.coaction (transportHom diagonalRegular shift (delta n)) =
      delta (n + 1) ⊗ₜ[ℕ] delta n ∧
    transportInvHom diagonalRegular shift (delta n) = delta (n - 1) ∧
    diagonalRegular.coaction (transportInvHom diagonalRegular shift (delta n)) =
      delta (n - 1) ⊗ₜ[ℕ] delta (n - 1) ∧
    (shiftedRegular.transport shift).coaction (delta n) = delta n ⊗ₜ[ℕ] delta (n - 2) ∧
    shiftedRegular.transport shift.symm = diagonalRegular ∧
    (transportInvHom diagonalRegular shift).comp (transportHom diagonalRegular shift)
      (delta n) = delta n ∧
    (transportHom diagonalRegular shift).comp (transportInvHom diagonalRegular shift)
      (delta n) = delta n := by
  refine ⟨shiftedCoaction_delta_zero_ne, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have htransport : diagonalRegular.transport shift = diagonalRegular :=
      (transport_eq_iff_colinear diagonalRegular shift diagonalRegular).mpr h
    exact shiftedCoaction_delta_zero_ne.1
      (congrArg (fun X : RightComodule ℕ Diagonal Diagonal ↦ X.coaction (delta 0)) htransport)
  · calc
      shiftedRegular.coaction (transportHom diagonalRegular shift (delta n)) =
          (transportHom diagonalRegular shift).toLinearMap.rTensor Diagonal
            (diagonalRegular.coaction (delta n)) :=
        (transportHom diagonalRegular shift).colinear_apply (delta n)
      _ = delta (n + 1) ⊗ₜ[ℕ] delta n := by
        rw [transportHom_toLinearMap, diagonalRegular_coaction_delta,
          LinearMap.rTensor_tmul, LinearEquiv.coe_coe, shift_delta]
  · rw [transportInvHom_apply, shift_symm_delta]
  · calc
      diagonalRegular.coaction (transportInvHom diagonalRegular shift (delta n)) =
          (transportInvHom diagonalRegular shift).toLinearMap.rTensor Diagonal
            (shiftedRegular.coaction (delta n)) :=
        (transportInvHom diagonalRegular shift).colinear_apply (delta n)
      _ = delta (n - 1) ⊗ₜ[ℕ] delta (n - 1) := by
        rw [transportInvHom_toLinearMap,
          show shiftedRegular.coaction (delta n) = delta n ⊗ₜ[ℕ] delta (n - 1) from
            shiftedCoaction_delta n,
          LinearMap.rTensor_tmul, LinearEquiv.coe_coe, shift_symm_delta]
  · rw [show shiftedRegular.transport shift = diagonalRegular.transport (shift.trans shift) from
        transport_trans diagonalRegular shift shift,
      transport_coaction_apply, LinearEquiv.symm_trans_apply,
      shift_symm_delta, shift_symm_delta, diagonalRegular_coaction_delta,
      LinearMap.rTensor_tmul, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
      shift_delta, shift_delta, sub_add_cancel, sub_add_cancel, sub_sub, one_add_one_eq_two]
  · exact transport_symm diagonalRegular shift
  · rw [transportInvHom_comp_transportHom, RightComoduleHom.id_apply]
  · rw [transportHom_comp_transportInvHom, RightComoduleHom.id_apply]

/-- The bottom subcomodule of the diagonal regular comodule. -/
private def diagonalBottom : diagonalRegular.Subcomodule :=
  Subcomodule.bot diagonalRegular

private theorem conjugatedCoaction_bottom_refl :
    conjugatedCoaction diagonalBottom.comodule
        (LinearEquiv.refl ℕ diagonalBottom.toSubmodule) =
      diagonalBottom.comodule.coaction := by
  apply LinearMap.ext
  intro x
  simp only [conjugatedCoaction, transport_coaction, LinearEquiv.arrowCongr_apply,
    LinearEquiv.rTensor_refl,
    LinearEquiv.refl_symm, LinearEquiv.refl_apply]

/-- The same construction includes the bottom carrier and its identity equivalence. -/
example :
    diagonalBottom.comodule.transport (LinearEquiv.refl ℕ diagonalBottom.toSubmodule) =
        diagonalBottom.comodule ∧
    transportHom diagonalBottom.comodule (LinearEquiv.refl ℕ diagonalBottom.toSubmodule) 0 = 0 ∧
    transportInvHom diagonalBottom.comodule
      (LinearEquiv.refl ℕ diagonalBottom.toSubmodule) 0 = 0 := by
  refine ⟨transport_refl diagonalBottom.comodule, ?_, ?_⟩
  · rw [transportHom_apply, LinearEquiv.refl_apply]
  · rw [transportInvHom_apply, LinearEquiv.refl_symm, LinearEquiv.refl_apply]

end

end Coalgebra.RightComodule

namespace Coalgebra.RightComodule

section CarrierTransport

variable {R : Type uR} {C : Type uC} {V : Type uV} {W : Type uW} {Z : Type uZ}
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]
variable [AddCommMonoid Z] [Module R Z]

/-- The function type for transporting a specified right coaction along a carrier
linear equivalence, with the scalar and coalgebra structures unchanged. -/
private def carrierTransportType : Type _ :=
  (X : RightComodule R C V) → (e : V ≃ₗ[R] W) → RightComodule R C W

/-- The coaction, pullback, uniqueness and colinearity equations for carrier transport.
The tensor map acts on the module factor and fixes the coalgebra factor. All right
comodules on `W` use its given additive and scalar-module structures. -/
private def carrierTransportCoaction
    (transport : carrierTransportType (R := R) (C := C) (V := V) (W := W)) : Prop :=
  ∀ (X : RightComodule R C V) (e : V ≃ₗ[R] W),
    (transport X e).coaction = conjugatedCoaction X e ∧
    (transport X e).coaction =
      e.toLinearMap.rTensor C ∘ₗ X.coaction ∘ₗ e.symm.toLinearMap ∧
    (∀ w : W, (transport X e).coaction w =
      e.toLinearMap.rTensor C (X.coaction (e.symm w))) ∧
    (e.symm.toLinearMap.rTensor C ∘ₗ (transport X e).coaction ∘ₗ e.toLinearMap =
      X.coaction) ∧
    (∀ Y : RightComodule R C W,
      transport X e = Y ↔ Y.coaction = conjugatedCoaction X e) ∧
    (∀ Y : RightComodule R C W,
      transport X e = Y ↔
        Y.coaction ∘ₗ e.toLinearMap = e.toLinearMap.rTensor C ∘ₗ X.coaction) ∧
    ((transport X e).coaction ∘ₗ e.toLinearMap =
      e.toLinearMap.rTensor C ∘ₗ X.coaction) ∧
    (∀ v : V, (transport X e).coaction (e v) =
      e.toLinearMap.rTensor C (X.coaction v)) ∧
    (X.coaction ∘ₗ e.symm.toLinearMap =
      e.symm.toLinearMap.rTensor C ∘ₗ (transport X e).coaction) ∧
    (∀ w : W, X.coaction (e.symm w) =
      e.symm.toLinearMap.rTensor C ((transport X e).coaction w))

/-- Identity, composition, inverse transport and recovery of specified coactions.
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
  (∀ X : RightComodule R C V, transportVV X (LinearEquiv.refl R V) = X) ∧
  (∀ (X : RightComodule R C V) (e : V ≃ₗ[R] W) (f : W ≃ₗ[R] Z),
    transportWZ (transportVW X e) f = transportVZ X (e.trans f)) ∧
  (∀ (X : RightComodule R C V) (e : V ≃ₗ[R] W),
    transportWV (transportVW X e) e.symm = X) ∧
  (∀ (Y : RightComodule R C W) (e : V ≃ₗ[R] W),
    transportVW (transportWV Y e.symm) e = Y) ∧
  (∀ (X : RightComodule R C V) (Y : RightComodule R C W) (e : V ≃ₗ[R] W),
    transportWV Y e.symm = X ↔ transportVW X e = Y)

end CarrierTransport

/-- Carrier-transport equations on the translated diagonal regular coaction and
on the identity of its bottom subcomodule. The raw translated coaction satisfies
`shiftedCoaction_delta` and `shiftedCoaction_delta_zero_ne`, while the bottom
identity satisfies `conjugatedCoaction_bottom_refl`. The tensor extension of translation
fixes the second factor; translation is not an automorphism of the fixed regular comodule. -/
private def diagonalCarrierTransportEquations
    (transport : carrierTransportType (R := ℕ) (C := Diagonal)
      (V := Diagonal) (W := Diagonal))
    (transportBottom : carrierTransportType (R := ℕ) (C := Diagonal)
      (V := diagonalBottom.toSubmodule) (W := diagonalBottom.toSubmodule)) : Prop :=
  (transport diagonalRegular shift).coaction = shiftedCoaction ∧
  (∀ n : ℤ, (transport diagonalRegular shift).coaction (delta n) =
    delta n ⊗ₜ[ℕ] delta (n - 1)) ∧
  ((transport diagonalRegular shift).coaction (delta 0) ≠
      diagonalRegular.coaction (delta 0) ∧
    (transport diagonalRegular shift).coaction (delta 0) ≠ 0) ∧
  transport diagonalRegular (LinearEquiv.refl ℕ Diagonal) = diagonalRegular ∧
  transportBottom diagonalBottom.comodule
    (LinearEquiv.refl ℕ diagonalBottom.toSubmodule) = diagonalBottom.comodule

end Coalgebra.RightComodule
