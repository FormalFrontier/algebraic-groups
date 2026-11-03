/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Coalgebra.Equiv

/-!
# Coalgebras along a semilinear equivalence

Mathlib defines `LinearEquiv.coalgebraStruct` and `LinearEquiv.coalgebra` by transporting
comultiplication and counit along a linear equivalence. This file records their formulas
as equalities of linear maps and on individual elements. The structure being projected
is explicit, so these formulas do not require a coalgebra instance on the source module.

The data formulas only require a commutative semiring and additive commutative monoids.
The formulas for `LinearEquiv.coalgebra` use the same data formulas when the target is a
coalgebra. `LinearEquiv.toCoalgEquiv` bundles the equivalence from the pulled-back
coalgebra data to the given data; neither side needs the coalgebra laws.

`LinearEquiv.coalgebraStructOfRingEquiv` also changes the scalar semiring along a
ring equivalence `σ : R ≃+* S`. It pulls back the comultiplication using Mathlib's
semilinear tensor equivalence and the counit using `σ.symm`. The given module
structures are retained, and the two semirings and two modules may lie in independent
universes. `LinearEquiv.coalgebraOfRingEquiv` proves coassociativity and both counit
laws for exactly these data when the target is a coalgebra. At the identity scalar
equivalence the two constructors are exactly Mathlib's `LinearEquiv.coalgebraStruct`
and `LinearEquiv.coalgebra`, respectively.

For example, a pure-tensor expression in the target gives a pure-tensor expression in
the source. Under the module hypotheses below, one can write:

```lean
example [Coalgebra R B] (e : A ≃ₗ[R] B) (x : A) (b₁ b₂ : B)
    (h : Coalgebra.comul (R := R) (e x) = b₁ ⊗ₜ[R] b₂) :
    @CoalgebraStruct.comul R A _ _ _ (e.coalgebra R).toCoalgebraStruct x =
      e.symm b₁ ⊗ₜ[R] e.symm b₂ := by
  rw [LinearEquiv.coalgebra_comul_apply, h, TensorProduct.map_tmul]
```

## References

`Mathlib.RingTheory.Coalgebra.Basic` defines both transported structures, including
coassociativity and the two counitality laws for `LinearEquiv.coalgebra`.
`Mathlib.RingTheory.Coalgebra.Equiv` supplies coalgebra equivalences and their inverses.
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace LinearEquiv

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommSemiring R] [AddCommMonoid A] [Module R A] [AddCommMonoid B]
  [moduleRB : Module R B]

/-- Comultiplication in the transported data is conjugated by the linear equivalence
and the tensor product of its inverse. -/
@[simp]
theorem coalgebraStruct_comul [CoalgebraStruct R B] (e : A ≃ₗ[R] B) :
    @CoalgebraStruct.comul R A _ _ _ (e.coalgebraStruct R) =
      TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap ∘ₗ
        Coalgebra.comul (R := R) (A := B) ∘ₗ e.toLinearMap :=
  rfl

/-- The counit in the transported data is the target counit composed with the
linear equivalence. -/
@[simp]
theorem coalgebraStruct_counit [CoalgebraStruct R B] (e : A ≃ₗ[R] B) :
    @CoalgebraStruct.counit R A _ _ _ (e.coalgebraStruct R) =
      Coalgebra.counit (R := R) (A := B) ∘ₗ e.toLinearMap :=
  rfl

/-- Transported comultiplication applies the tensor product of the inverse equivalence
to the comultiplication of the image. -/
@[simp]
theorem coalgebraStruct_comul_apply [CoalgebraStruct R B] (e : A ≃ₗ[R] B) (x : A) :
    @CoalgebraStruct.comul R A _ _ _ (e.coalgebraStruct R) x =
      TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap
        (Coalgebra.comul (R := R) (A := B) (e x)) :=
  LinearMap.congr_fun (coalgebraStruct_comul e) x

/-- The transported counit agrees with the target counit on the image. -/
@[simp]
theorem coalgebraStruct_counit_apply [CoalgebraStruct R B] (e : A ≃ₗ[R] B) (x : A) :
    @CoalgebraStruct.counit R A _ _ _ (e.coalgebraStruct R) x =
      Coalgebra.counit (R := R) (A := B) (e x) :=
  LinearMap.congr_fun (coalgebraStruct_counit e) x

/-- A linear equivalence identifies its pulled-back coalgebra data with the given data.
The source structure is exactly `LinearEquiv.coalgebraStruct`; no coalgebra laws are needed. -/
def toCoalgEquiv [c : CoalgebraStruct R B] (e : A ≃ₗ[R] B) :
    @CoalgEquiv R _ A B _ _ _ _ (e.coalgebraStruct R) c :=
  letI : CoalgebraStruct R A := e.coalgebraStruct R
  { e with
    counit_comp := rfl
    map_comp_comul := by
      simp only [coalgebraStruct_comul, ← LinearMap.comp_assoc,
        ← TensorProduct.map_comp, LinearEquiv.comp_symm, TensorProduct.map_id,
        LinearMap.id_comp] }

/-- The coalgebra equivalence of pulled-back data has the original linear equivalence. -/
@[simp]
theorem toCoalgEquiv_toLinearEquiv [c : CoalgebraStruct R B] (e : A ≃ₗ[R] B) :
    @CoalgEquiv.toLinearEquiv R _ A B _ _ _ _ (e.coalgebraStruct R) c
      (@toCoalgEquiv R A B _ _ _ _ _ c e) = e := rfl

/-- The coalgebra equivalence of pulled-back data acts by the original equivalence. -/
theorem toCoalgEquiv_apply [c : CoalgebraStruct R B] (e : A ≃ₗ[R] B) (x : A) :
    (@CoalgEquiv.toLinearEquiv R _ A B _ _ _ _ (e.coalgebraStruct R) c
      (@toCoalgEquiv R A B _ _ _ _ _ c e)) x = e x := rfl

/-- The inverse coalgebra equivalence acts by the inverse linear equivalence. -/
theorem toCoalgEquiv_symm_apply [c : CoalgebraStruct R B] (e : A ≃ₗ[R] B) (y : B) :
    (@CoalgEquiv.toLinearEquiv R _ B A _ _ _ _ c (e.coalgebraStruct R)
      (@CoalgEquiv.symm R A B _ _ _ _ _ (e.coalgebraStruct R) c
        (@toCoalgEquiv R A B _ _ _ _ _ c e))) y = e.symm y := rfl

/-- Comultiplication of the transported coalgebra is conjugated by the linear equivalence
and the tensor product of its inverse. -/
@[simp]
theorem coalgebra_comul [Coalgebra R B] (e : A ≃ₗ[R] B) :
    @CoalgebraStruct.comul R A _ _ _ (e.coalgebra R).toCoalgebraStruct =
      TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap ∘ₗ
        Coalgebra.comul (R := R) (A := B) ∘ₗ e.toLinearMap :=
  coalgebraStruct_comul e

/-- The counit of the transported coalgebra is the target counit composed with the
linear equivalence. -/
@[simp]
theorem coalgebra_counit [Coalgebra R B] (e : A ≃ₗ[R] B) :
    @CoalgebraStruct.counit R A _ _ _ (e.coalgebra R).toCoalgebraStruct =
      Coalgebra.counit (R := R) (A := B) ∘ₗ e.toLinearMap :=
  coalgebraStruct_counit e

/-- Comultiplication of the transported coalgebra applies the tensor product of the inverse
equivalence to the comultiplication of the image. -/
@[simp]
theorem coalgebra_comul_apply [Coalgebra R B] (e : A ≃ₗ[R] B) (x : A) :
    @CoalgebraStruct.comul R A _ _ _ (e.coalgebra R).toCoalgebraStruct x =
      TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap
        (Coalgebra.comul (R := R) (A := B) (e x)) :=
  coalgebraStruct_comul_apply e x

/-- The counit of the transported coalgebra agrees with the target counit on the image. -/
@[simp]
theorem coalgebra_counit_apply [Coalgebra R B] (e : A ≃ₗ[R] B) (x : A) :
    @CoalgebraStruct.counit R A _ _ _ (e.coalgebra R).toCoalgebraStruct x =
      Coalgebra.counit (R := R) (A := B) (e x) :=
  coalgebraStruct_counit_apply e x

section RingEquiv

omit [Module R B]

universe uS

variable {S : Type uS} [CommSemiring S] [Module S B]

-- Use the canonical inverse of a scalar equivalence without adding inverse-pair premises.
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- Pull back coalgebra data along a semilinear equivalence over a ring equivalence.
The comultiplication is conjugated through the tensor equivalence, and the counit is
composed with the inverse scalar equivalence. This constructs data, not coalgebra laws. -/
@[instance_reducible]
def coalgebraStructOfRingEquiv [CoalgebraStruct S B] (σ : R ≃+* S)
    (e : A ≃ₛₗ[(σ : R →+* S)] B) : CoalgebraStruct R A where
  comul := (TensorProduct.congr e e).symm.toLinearMap ∘ₛₗ
    Coalgebra.comul (R := S) ∘ₛₗ e.toLinearMap
  counit := (σ.symm : S →+* R).toSemilinearMap ∘ₛₗ
    Coalgebra.counit (R := S) ∘ₛₗ e.toLinearMap

/-- Comultiplication is conjugation by the equivalence and its tensor square. -/
@[simp]
theorem coalgebraStructOfRingEquiv_comul [CoalgebraStruct S B] (σ : R ≃+* S)
    (e : A ≃ₛₗ[(σ : R →+* S)] B) :
    @CoalgebraStruct.comul R A _ _ _ (coalgebraStructOfRingEquiv σ e) =
      TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap ∘ₛₗ
        Coalgebra.comul (R := S) ∘ₛₗ e.toLinearMap := rfl

/-- The counit changes scalars by the inverse ring equivalence. -/
@[simp]
theorem coalgebraStructOfRingEquiv_counit [CoalgebraStruct S B] (σ : R ≃+* S)
    (e : A ≃ₛₗ[(σ : R →+* S)] B) :
    @CoalgebraStruct.counit R A _ _ _ (coalgebraStructOfRingEquiv σ e) =
      (σ.symm : S →+* R).toSemilinearMap ∘ₛₗ
        Coalgebra.counit (R := S) ∘ₛₗ e.toLinearMap := rfl

/-- The transported comultiplication applies the inverse tensor equivalence. -/
@[simp]
theorem coalgebraStructOfRingEquiv_comul_apply [CoalgebraStruct S B] (σ : R ≃+* S)
    (e : A ≃ₛₗ[(σ : R →+* S)] B) (x : A) :
    @CoalgebraStruct.comul R A _ _ _ (coalgebraStructOfRingEquiv σ e) x =
      TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap
        (Coalgebra.comul (R := S) (e x)) := rfl

/-- The transported counit is the inverse scalar equivalence applied to the target counit. -/
@[simp]
theorem coalgebraStructOfRingEquiv_counit_apply [CoalgebraStruct S B] (σ : R ≃+* S)
    (e : A ≃ₛₗ[(σ : R →+* S)] B) (x : A) :
    @CoalgebraStruct.counit R A _ _ _ (coalgebraStructOfRingEquiv σ e) x =
      σ.symm (Coalgebra.counit (R := S) (e x)) := rfl

/-- The tensor square of the semilinear equivalence intertwines the comultiplications. -/
theorem congr_coalgebraStructOfRingEquiv_comul [CoalgebraStruct S B] (σ : R ≃+* S)
    (e : A ≃ₛₗ[(σ : R →+* S)] B) (x : A) :
    TensorProduct.congr e e
        (@CoalgebraStruct.comul R A _ _ _ (coalgebraStructOfRingEquiv σ e) x) =
      Coalgebra.comul (R := S) (e x) :=
  (TensorProduct.congr e e).apply_symm_apply _

/-- A pure-tensor comultiplication in the target pulls back to the corresponding
pure tensor over the source semiring. -/
theorem coalgebraStructOfRingEquiv_comul_eq_tmul [CoalgebraStruct S B] (σ : R ≃+* S)
    (e : A ≃ₛₗ[(σ : R →+* S)] B) (x : A) (b₁ b₂ : B)
    (h : Coalgebra.comul (R := S) (e x) = b₁ ⊗ₜ[S] b₂) :
    @CoalgebraStruct.comul R A _ _ _ (coalgebraStructOfRingEquiv σ e) x =
      e.symm b₁ ⊗ₜ[R] e.symm b₂ := by
  simp only [coalgebraStructOfRingEquiv_comul_apply, h, TensorProduct.map_tmul,
    LinearEquiv.coe_coe]

include moduleRB in
/-- At the identity scalar equivalence, pullback is exactly Mathlib's coalgebra data. -/
@[simp]
theorem coalgebraStructOfRingEquiv_refl [CoalgebraStruct R B] (e : A ≃ₗ[R] B) :
    coalgebraStructOfRingEquiv (RingEquiv.refl R) e = e.coalgebraStruct R := rfl

include moduleRB in
/-- At the identity scalar equivalence, the data agree with the data parent of
Mathlib's lawful coalgebra transport. -/
theorem coalgebraStructOfRingEquiv_refl_eq_coalgebra [Coalgebra R B] (e : A ≃ₗ[R] B) :
    coalgebraStructOfRingEquiv (RingEquiv.refl R) e = (e.coalgebra R).toCoalgebraStruct := rfl

/-- Pull back a coalgebra along a semilinear equivalence over a ring equivalence.
The original module structure is retained, and the data parent is exactly
`coalgebraStructOfRingEquiv σ e`. -/
@[instance_reducible]
def coalgebraOfRingEquiv [Coalgebra S B] (σ : R ≃+* S)
    (e : A ≃ₛₗ[(σ : R →+* S)] B) : Coalgebra R A where
  __ := coalgebraStructOfRingEquiv σ e
  coassoc := by
    let : CoalgebraStruct R A := coalgebraStructOfRingEquiv σ e
    have hδ (a : A) : TensorProduct.congr e e (Coalgebra.comul (R := R) a) =
        Coalgebra.comul (R := S) (e a) :=
      congr_coalgebraStructOfRingEquiv_comul σ e a
    have hleft :
        (TensorProduct.congr (TensorProduct.congr e e) e).toLinearMap ∘ₛₗ
            (Coalgebra.comul (R := R) (A := A)).rTensor A =
          (Coalgebra.comul (R := S) (A := B)).rTensor B ∘ₛₗ
            (TensorProduct.congr e e).toLinearMap := by
      apply TensorProduct.ext'
      intro a b
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.rTensor_tmul,
        TensorProduct.congr_tmul, hδ]
    have hright :
        (TensorProduct.congr e (TensorProduct.congr e e)).toLinearMap ∘ₛₗ
            (Coalgebra.comul (R := R) (A := A)).lTensor A =
          (Coalgebra.comul (R := S) (A := B)).lTensor B ∘ₛₗ
            (TensorProduct.congr e e).toLinearMap := by
      apply TensorProduct.ext'
      intro a b
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.lTensor_tmul,
        TensorProduct.congr_tmul, hδ]
    have hassoc :
        (TensorProduct.congr e (TensorProduct.congr e e)).toLinearMap ∘ₛₗ
            (TensorProduct.assoc R A A A).toLinearMap =
          (TensorProduct.assoc S B B B).toLinearMap ∘ₛₗ
            (TensorProduct.congr (TensorProduct.congr e e) e).toLinearMap :=
      TensorProduct.ext_threefold fun _ _ _ => rfl
    apply LinearMap.ext
    intro a
    apply (TensorProduct.congr e (TensorProduct.congr e e)).injective
    change TensorProduct.congr e (TensorProduct.congr e e)
        (TensorProduct.assoc R A A A
          ((Coalgebra.comul (R := R) (A := A)).rTensor A (Coalgebra.comul (R := R) a))) =
      TensorProduct.congr e (TensorProduct.congr e e)
        ((Coalgebra.comul (R := R) (A := A)).lTensor A (Coalgebra.comul (R := R) a))
    calc
      _ = TensorProduct.assoc S B B B
          (TensorProduct.congr (TensorProduct.congr e e) e
            ((Coalgebra.comul (R := R) (A := A)).rTensor A
              (Coalgebra.comul (R := R) a))) :=
        LinearMap.congr_fun hassoc _
      _ = TensorProduct.assoc S B B B
          ((Coalgebra.comul (R := S) (A := B)).rTensor B
            (TensorProduct.congr e e (Coalgebra.comul (R := R) a))) :=
        congrArg (TensorProduct.assoc S B B B) (LinearMap.congr_fun hleft _)
      _ = (Coalgebra.comul (R := S) (A := B)).lTensor B
          (Coalgebra.comul (R := S) (e a)) := by
        rw [hδ, Coalgebra.coassoc_apply]
      _ = _ := by
        simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, hδ] using
          (LinearMap.congr_fun hright (Coalgebra.comul (R := R) a)).symm
  rTensor_counit_comp_comul := by
    let : CoalgebraStruct R A := coalgebraStructOfRingEquiv σ e
    have h :
        (TensorProduct.congr σ.toSemilinearEquiv e).toLinearMap ∘ₛₗ
            (Coalgebra.counit (R := R) (A := A)).rTensor A =
          (Coalgebra.counit (R := S) (A := B)).rTensor B ∘ₛₗ
            (TensorProduct.congr e e).toLinearMap := by
      apply TensorProduct.ext'
      intro a b
      simp
    apply LinearMap.ext
    intro a
    apply (TensorProduct.congr σ.toSemilinearEquiv e).injective
    change TensorProduct.congr σ.toSemilinearEquiv e
        ((Coalgebra.counit (R := R) (A := A)).rTensor A (Coalgebra.comul (R := R) a)) =
      TensorProduct.congr σ.toSemilinearEquiv e (1 ⊗ₜ[R] a)
    calc
      _ = (Coalgebra.counit (R := S) (A := B)).rTensor B
          (TensorProduct.congr e e (Coalgebra.comul (R := R) a)) :=
        LinearMap.congr_fun h _
      _ = 1 ⊗ₜ[S] e a := by
        rw [congr_coalgebraStructOfRingEquiv_comul, Coalgebra.rTensor_counit_comul]
      _ = _ := by simp
  lTensor_counit_comp_comul := by
    let : CoalgebraStruct R A := coalgebraStructOfRingEquiv σ e
    have h :
        (TensorProduct.congr e σ.toSemilinearEquiv).toLinearMap ∘ₛₗ
            (Coalgebra.counit (R := R) (A := A)).lTensor A =
          (Coalgebra.counit (R := S) (A := B)).lTensor B ∘ₛₗ
            (TensorProduct.congr e e).toLinearMap := by
      apply TensorProduct.ext'
      intro a b
      simp
    apply LinearMap.ext
    intro a
    apply (TensorProduct.congr e σ.toSemilinearEquiv).injective
    change TensorProduct.congr e σ.toSemilinearEquiv
        ((Coalgebra.counit (R := R) (A := A)).lTensor A (Coalgebra.comul (R := R) a)) =
      TensorProduct.congr e σ.toSemilinearEquiv (a ⊗ₜ[R] 1)
    calc
      _ = (Coalgebra.counit (R := S) (A := B)).lTensor B
          (TensorProduct.congr e e (Coalgebra.comul (R := R) a)) :=
        LinearMap.congr_fun h _
      _ = e a ⊗ₜ[S] 1 := by
        rw [congr_coalgebraStructOfRingEquiv_comul, Coalgebra.lTensor_counit_comul]
      _ = _ := by simp

/-- The data parent of semilinear coalgebra transport is the data pullback. -/
theorem coalgebraOfRingEquiv_toCoalgebraStruct [Coalgebra S B] (σ : R ≃+* S)
    (e : A ≃ₛₗ[(σ : R →+* S)] B) :
    (coalgebraOfRingEquiv σ e).toCoalgebraStruct = coalgebraStructOfRingEquiv σ e := rfl

/-- Comultiplication of the pulled-back coalgebra is tensor conjugation. -/
@[simp]
theorem coalgebraOfRingEquiv_comul [Coalgebra S B] (σ : R ≃+* S)
    (e : A ≃ₛₗ[(σ : R →+* S)] B) :
    @CoalgebraStruct.comul R A _ _ _ (coalgebraOfRingEquiv σ e).toCoalgebraStruct =
      TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap ∘ₛₗ
        Coalgebra.comul (R := S) ∘ₛₗ e.toLinearMap := rfl

/-- The pulled-back coalgebra counit changes scalars by the inverse ring equivalence. -/
@[simp]
theorem coalgebraOfRingEquiv_counit [Coalgebra S B] (σ : R ≃+* S)
    (e : A ≃ₛₗ[(σ : R →+* S)] B) :
    @CoalgebraStruct.counit R A _ _ _ (coalgebraOfRingEquiv σ e).toCoalgebraStruct =
      (σ.symm : S →+* R).toSemilinearMap ∘ₛₗ
        Coalgebra.counit (R := S) ∘ₛₗ e.toLinearMap := rfl

/-- Comultiplication of the pulled-back coalgebra at an element. -/
@[simp]
theorem coalgebraOfRingEquiv_comul_apply [Coalgebra S B] (σ : R ≃+* S)
    (e : A ≃ₛₗ[(σ : R →+* S)] B) (x : A) :
    @CoalgebraStruct.comul R A _ _ _ (coalgebraOfRingEquiv σ e).toCoalgebraStruct x =
      TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap
        (Coalgebra.comul (R := S) (e x)) := rfl

/-- The counit of the pulled-back coalgebra at an element. -/
@[simp]
theorem coalgebraOfRingEquiv_counit_apply [Coalgebra S B] (σ : R ≃+* S)
    (e : A ≃ₛₗ[(σ : R →+* S)] B) (x : A) :
    @CoalgebraStruct.counit R A _ _ _ (coalgebraOfRingEquiv σ e).toCoalgebraStruct x =
      σ.symm (Coalgebra.counit (R := S) (e x)) := rfl

/-- The tensor equivalence identifies the pulled-back and target comultiplications. -/
theorem congr_coalgebraOfRingEquiv_comul [Coalgebra S B] (σ : R ≃+* S)
    (e : A ≃ₛₗ[(σ : R →+* S)] B) (x : A) :
    TensorProduct.congr e e
        (@CoalgebraStruct.comul R A _ _ _ (coalgebraOfRingEquiv σ e).toCoalgebraStruct x) =
      Coalgebra.comul (R := S) (e x) :=
  congr_coalgebraStructOfRingEquiv_comul σ e x

include moduleRB in
/-- Identity scalar transport is exactly Mathlib's full coalgebra constructor. -/
@[simp]
theorem coalgebraOfRingEquiv_refl [Coalgebra R B] (e : A ≃ₗ[R] B) :
    coalgebraOfRingEquiv (RingEquiv.refl R) e = e.coalgebra R := rfl

end RingEquiv

end LinearEquiv
