/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.ComoduleBaseChange
public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.WeightSpace
public import Mathlib.RingTheory.Flat.Equalizer

/-!
# Flat scalar extension of right-comodule weight spaces

For a specified right comodule `X` over a commutative ring `R` and a flat
commutative `R`-algebra `S`, scalar extension identifies `S ⊗[R] X.weightSpace c`
with the weight space of `X.baseChange S` at `1 ⊗ₜ[R] c`. The element `c` is
arbitrary; neither the coalgebra nor the comodule module needs to be flat.

The comparison retains the original tensor-inclusion map. Its inclusion and
inverse squares hold on every vector, and it is natural in colinear maps.
Group-like weights, and unit weights when a bialgebra structure is given,
are specializations of this construction.

## References

The construction uses Mathlib's flat equalizer comparison in
`Mathlib.RingTheory.Flat.Equalizer` and tensor-distribution equivalence, together
with the specified-comodule scalar extension and weight spaces in this library.
-/

@[expose] public section

universe u v w z a

open scoped TensorProduct

namespace Coalgebra.RightComodule

section CommSemiring

variable {R : Type u} {C : Type v} {W : Type w}
variable [CommSemiring R] [AddCommMonoid C] [Module R C]
variable [AddCommMonoid W] [Module R W]
variable (S : Type z) [CommSemiring S] [Algebra R S]

private theorem distribBaseChange_comp_tmul (c : C) :
    (_root_.TensorProduct.AlgebraTensorModule.distribBaseChange R S W C).toLinearMap ∘ₗ
        ((TensorProduct.mk R W C).flip c).baseChange S =
      (TensorProduct.mk S (S ⊗[R] W) (S ⊗[R] C)).flip ((1 : S) ⊗ₜ[R] c) := by
  apply _root_.TensorProduct.AlgebraTensorModule.ext
  intro s w
  simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearMap.flip_apply,
    TensorProduct.mk_apply, LinearEquiv.coe_coe,
    _root_.TensorProduct.AlgebraTensorModule.distribBaseChange_tmul]

variable [Coalgebra R C]

private theorem weightSpace_baseChange_eq (X : RightComodule R C W) (c : C) :
    (X.baseChange S).weightSpace ((1 : S) ⊗ₜ[R] c) =
      LinearMap.eqLocus (X.coaction.baseChange S)
        (((TensorProduct.mk R W C).flip c).baseChange S) := by
  ext t
  change (X.baseChange S).coaction t =
      (TensorProduct.mk S (S ⊗[R] W) (S ⊗[R] C)).flip ((1 : S) ⊗ₜ[R] c) t ↔ _
  rw [baseChange_coaction, ← distribBaseChange_comp_tmul S c]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  exact (_root_.TensorProduct.AlgebraTensorModule.distribBaseChange R S W C).injective.eq_iff

end CommSemiring

section CommRing

variable {R : Type u} {C : Type v} {W : Type w}
variable [CommRing R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid W] [Module R W]
variable (S : Type z) [CommRing S] [Algebra R S] [Module.Flat R S]

/-- Flat scalar extension identifies the original weight space with the weight
space of the scalar-extended specified comodule at `1 ⊗ c`.

This is Mathlib's flat equalizer equivalence, followed by the identification
with the existing scalar-extended coaction. -/
noncomputable def weightSpaceBaseChangeEquiv (X : RightComodule R C W) (c : C) :
    S ⊗[R] X.weightSpace c ≃ₗ[S]
      (X.baseChange S).weightSpace ((1 : S) ⊗ₜ[R] c) := by
  letI : AddCommGroup W := Module.addCommMonoidToAddCommGroup R
  letI : AddCommGroup (W ⊗[R] C) := Module.addCommMonoidToAddCommGroup R
  exact (LinearMap.tensorEqLocusEquiv S S X.coaction
    ((TensorProduct.mk R W C).flip c)).trans
      (LinearEquiv.ofEq _ _ (by exact (weightSpace_baseChange_eq S X c).symm))

/-- On every tensor, the ambient value of the comparison is the scalar extension
of the original weight-space inclusion. -/
@[simp] theorem coe_weightSpaceBaseChangeEquiv (X : RightComodule R C W) (c : C)
    (t : S ⊗[R] X.weightSpace c) :
    (X.weightSpaceBaseChangeEquiv S c t : S ⊗[R] W) =
      (X.weightSpace c).subtype.baseChange S t := by
  let : AddCommGroup W := Module.addCommMonoidToAddCommGroup R
  let : AddCommGroup (W ⊗[R] C) := Module.addCommMonoidToAddCommGroup R
  change ((LinearMap.tensorEqLocusEquiv S S X.coaction
    ((TensorProduct.mk R W C).flip c)) t : S ⊗[R] W) = _
  exact LinearMap.tensorEqLocus_coe S S X.coaction ((TensorProduct.mk R W C).flip c) t

/-- A pure tensor retains its original underlying vector under the comparison. -/
theorem coe_weightSpaceBaseChangeEquiv_tmul (X : RightComodule R C W) (c : C)
    (s : S) (w : X.weightSpace c) :
    (X.weightSpaceBaseChangeEquiv S c (s ⊗ₜ[R] w) : S ⊗[R] W) =
      s ⊗ₜ[R] (w : W) := by
  rw [coe_weightSpaceBaseChangeEquiv, LinearMap.baseChange_tmul, Submodule.subtype_apply]

/-- The comparison commutes with the original scalar-extended subtype inclusion. -/
@[simp] theorem subtype_comp_weightSpaceBaseChangeEquiv (X : RightComodule R C W) (c : C) :
    ((X.baseChange S).weightSpace ((1 : S) ⊗ₜ[R] c)).subtype ∘ₗ
        (X.weightSpaceBaseChangeEquiv S c).toLinearMap =
      (X.weightSpace c).subtype.baseChange S := by
  apply LinearMap.ext
  intro t
  exact coe_weightSpaceBaseChangeEquiv S X c t

/-- The inverse square recovers every vector of the scalar-extended weight space. -/
@[simp] theorem baseChange_subtype_comp_weightSpaceBaseChangeEquiv_symm
    (X : RightComodule R C W) (c : C) :
    (X.weightSpace c).subtype.baseChange S ∘ₗ
        (X.weightSpaceBaseChangeEquiv S c).symm.toLinearMap =
      ((X.baseChange S).weightSpace ((1 : S) ⊗ₜ[R] c)).subtype := by
  apply LinearMap.ext
  intro t
  change (X.weightSpace c).subtype.baseChange S
    ((X.weightSpaceBaseChangeEquiv S c).symm t) = (t : S ⊗[R] W)
  rw [← coe_weightSpaceBaseChangeEquiv]
  exact congrArg Subtype.val ((X.weightSpaceBaseChangeEquiv S c).apply_symm_apply t)

/-- Flat weight-space comparison is natural in the original colinear map,
as an equality in the ambient scalar-extended module on every tensor. -/
theorem weightSpaceBaseChangeEquiv_naturality
    {V : Type a} [AddCommMonoid V] [Module R V]
    {X : RightComodule R C W} {Y : RightComodule R C V}
    (f : Coalgebra.RightComoduleHom X Y) (c : C) (t : S ⊗[R] X.weightSpace c) :
    ((Y.weightSpaceBaseChangeEquiv S c)
        (((f.toLinearMap.comp (X.weightSpace c).subtype).codRestrict
          (Y.weightSpace c)
          (fun w => f.map_mem_weightSpace c w.property)).baseChange S t) : S ⊗[R] V) =
      f.toLinearMap.baseChange S (X.weightSpaceBaseChangeEquiv S c t : S ⊗[R] W) := by
  rw [coe_weightSpaceBaseChangeEquiv, coe_weightSpaceBaseChangeEquiv]
  have h : (Y.weightSpace c).subtype ∘ₗ
      ((f.toLinearMap.comp (X.weightSpace c).subtype).codRestrict
        (Y.weightSpace c) (fun w => f.map_mem_weightSpace c w.property)) =
      f.toLinearMap ∘ₗ (X.weightSpace c).subtype := rfl
  have hs := congrArg (fun g => (LinearMap.baseChange S g) t) h
  simpa only [LinearMap.baseChange_comp, LinearMap.comp_apply] using hs

end CommRing

end Coalgebra.RightComodule
