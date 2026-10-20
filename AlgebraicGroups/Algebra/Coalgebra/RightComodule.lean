/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.FiniteSubcoalgebra
public import AlgebraicGroups.Algebra.TensorProduct.Submodule
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Flat.Basic

/-!
# Right comodules and finite subcomodule containment

`Coalgebra.RightComodule R C M` specifies a linear coaction
`ρ : M →ₗ[R] M ⊗[R] C` satisfying coassociativity and right counitality on
an existing module. The scalars are a commutative semiring, `C` is a coalgebra,
and `C` and `M` are modules with additive commutative monoid structures.
Their universes are independent. Different coactions on the same module are
different values, not competing instances. These definitions require no
flatness, projectivity or freeness.

## Main definitions and results

* `RightComodule.coaction_injective` follows from the counit normal form.
  Equality and zero simp lemmas cancel the coaction, and
  `RightComodule.coaction_eq_zero_iff` characterizes the zero coaction map by
  `Subsingleton M`.
* `RightComoduleHom` is a linear map intertwining the specified coactions, with
  underlying map `toLinearMap`, identities and composition.
  `RightComoduleHom.colinear_symm` gives colinearity of the inverse of a linear
  equivalence whose forward map intertwines the two specified coactions.
* `RightComodule.IsStable` describes image stability for every member of an
  existing submodule in the range of `U ⊗ C → M ⊗ C`.
  `RightComodule.Subcomodule` instead carries a coaction on the submodule subtype
  and a colinear inclusion, bundled as `Subcomodule.subtype`. Every such
  subcomodule is image-stable, without flatness assumptions.
* For a commutative algebra carrying a coalgebra on its canonical module,
  `RightComodule.isStable_iff_id_evaluation_mem_baseChange` detects image
  stability by identity evaluation on the scalar-extension image.
  `RightComodule.isStable_iff_forall_evaluation_mem_baseChange` gives the
  equivalent family of algebra-valued tests in a compatible maximum universe.
  The one-algebra forward implication has an independent target universe.
  None of these evaluation results requires flatness or a subtype coaction.
* Under `[Module.Flat R C]`, `Subcomodule.ofIsStable` constructs the induced
  subtype coaction using Mathlib's injective codomain lift. Flatness transfers
  the coaction laws through the tensor inclusion and makes the coaction unique;
  `Subcomodule.ext` identifies subcomodules with the same underlying submodule.
  `Subcomodule.existsUnique_factorization` gives the unique colinear
  factorization of a comodule morphism whose values lie in the subcomodule.
* Under `[Module.Projective R C]`,
  `RightComodule.exists_fg_subcomodule_of_finite` places every finite subset of
  `M` in a subcomodule whose underlying submodule is finitely generated.
  Its subtype coaction and colinear inclusion give image stability for every
  member. Neither module need be finitely generated, and `M` need not be
  projective or free. The proof uses the coefficient argument in
  `FiniteSubcoalgebra`; the regular-coaction specialization reuses its
  right-coideal theorem.
* `RightComodule.directed_fg_toSubmodule` makes the underlying submodules of
  module-finite subcomodules directed under `[Module.Projective R C]`.
* `RightComodule.iUnion_fg_eq_univ` says that these same subcomodules cover `M`.

The regular and scalar constructors give coactions by comultiplication and the
inverse right unitor. `RightComodule.ofTensor` gives `m ↦ m ⊗ e` when
`comul e = e ⊗ e` and `counit e • m = m` for every `m`. It does not require
`counit e = 1` or a surjective counit. The scalar and constant-tensor
constructions also give subtype coactions directly.

## Limitations

No arbitrary-intersection or complete-lattice structure is asserted here.

## References

* M. E. Sweedler, *Hopf Algebras*, W. A. Benjamin, 1969, for classical
  comodules and the coefficient method (bibliographic credit).
* C. Kassel, *Quantum Groups*, §II.4, for tensor-product conventions.
* Mathlib's coalgebra, tensor-product, flatness and linear-map formalizations.
-/

@[expose] public section

universe u v w z

open scoped TensorProduct

namespace Coalgebra

/-- A specified right coaction of an `R`-coalgebra `C` on an existing `R`-module `M`. -/
structure RightComodule (R : Type u) (C : Type v) (M : Type w)
    [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
    [AddCommMonoid M] [Module R M] where
  /-- The right coaction, with coalgebra factor on the right. -/
  coaction : M →ₗ[R] M ⊗[R] C
  /-- Coassociativity of the right coaction. -/
  coassoc : TensorProduct.assoc R M C C ∘ₗ coaction.rTensor C ∘ₗ coaction =
    (comul (R := R) (A := C)).lTensor M ∘ₗ coaction
  /-- Right counitality, expressed using the inverse right unitor. -/
  counit_comp : (counit (R := R) (A := C)).lTensor M ∘ₗ coaction =
    (TensorProduct.rid R M).symm.toLinearMap

namespace RightComodule

variable {R : Type u} {C : Type v} {M : Type w}
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M]

/-- Right comodules on a fixed module are determined by their coaction maps. -/
@[ext] theorem ext {X Y : RightComodule R C M} (h : X.coaction = Y.coaction) : X = Y := by
  cases X
  cases Y
  cases h
  rfl

@[simp] theorem coaction_mk (rho hcoassoc hcounit) :
    (mk rho hcoassoc hcounit : RightComodule R C M).coaction = rho := rfl

/-- Coassociativity evaluated at an element. -/
@[simp] theorem coassoc_apply (X : RightComodule R C M) (m : M) :
    TensorProduct.assoc R M C C (X.coaction.rTensor C (X.coaction m)) =
      (comul (R := R)).lTensor M (X.coaction m) :=
  LinearMap.congr_fun X.coassoc m

/-- Coassociativity with the inverse associator. -/
@[simp] theorem coassoc_symm_apply (X : RightComodule R C M) (m : M) :
    (TensorProduct.assoc R M C C).symm
        ((comul (R := R)).lTensor M (X.coaction m)) =
      X.coaction.rTensor C (X.coaction m) := by
  rw [(TensorProduct.assoc R M C C).symm_apply_eq, X.coassoc_apply]

/-- The counit normal form is `m ⊗ 1`, with no surjectivity assumption on the counit. -/
@[simp] theorem counit_coaction (X : RightComodule R C M) (m : M) :
    (counit (R := R)).lTensor M (X.coaction m) = m ⊗ₜ[R] 1 :=
  LinearMap.congr_fun X.counit_comp m

/-- Composing the right counit with the right unitor recovers the element. -/
@[simp] theorem rid_counit_coaction (X : RightComodule R C M) (m : M) :
    TensorProduct.rid R M ((counit (R := R)).lTensor M (X.coaction m)) = m := by
  simp

/-- The coaction is injective: applying the counit and right unitor cancels it. -/
theorem coaction_injective (X : RightComodule R C M) : Function.Injective X.coaction := by
  intro m n h
  simpa only [X.rid_counit_coaction] using
    congrArg (fun t : M ⊗[R] C ↦
      TensorProduct.rid R M ((counit (R := R)).lTensor M t)) h

/-- Equality of coactions is equality of elements. -/
@[simp] theorem coaction_inj (X : RightComodule R C M) {m n : M} :
    X.coaction m = X.coaction n ↔ m = n :=
  X.coaction_injective.eq_iff

/-- A coaction vanishes at an element exactly when that element is zero. -/
@[simp] theorem coaction_eq_zero (X : RightComodule R C M) {m : M} :
    X.coaction m = 0 ↔ m = 0 :=
  X.coaction.map_eq_zero_iff X.coaction_injective

/-- Zero equals an element's coaction exactly when zero equals that element. -/
@[simp] theorem zero_eq_coaction (X : RightComodule R C M) {m : M} :
    0 = X.coaction m ↔ 0 = m := by
  rw [eq_comm, X.coaction_eq_zero, eq_comm]

/-- The coaction map is zero exactly when its underlying module is subsingleton. -/
@[simp] theorem coaction_eq_zero_iff (X : RightComodule R C M) :
    X.coaction = 0 ↔ Subsingleton M := by
  constructor
  · intro h
    have hz (m : M) : m = 0 := X.coaction_eq_zero.mp (LinearMap.congr_fun h m)
    exact ⟨fun m n ↦ (hz m).trans (hz n).symm⟩
  · intro h
    let := h
    ext m
    rw [Subsingleton.elim m 0]
    exact map_zero X.coaction

/-- The regular right comodule of a coalgebra, with coaction its comultiplication. -/
def regular (R : Type u) (C : Type v)
    [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C] :
    RightComodule R C C where
  coaction := comul
  coassoc := Coalgebra.coassoc
  counit_comp := Coalgebra.lTensor_counit_comp_comul

@[simp] theorem regular_coaction (c : C) :
    (regular R C).coaction c = comul (R := R) c := rfl

/-- A constant-tensor coaction. Counitality needs only that the counit of `e`
acts as the identity on `M`; it need not equal one in the scalar semiring. -/
def ofTensor (e : C) (hcomul : comul (R := R) e = e ⊗ₜ[R] e)
    (hcounit : ∀ m : M, counit (R := R) e • m = m) : RightComodule R C M where
  coaction := (TensorProduct.mk R M C).flip e
  coassoc := by
    ext m
    simp [LinearMap.lTensor_tmul, hcomul]
  counit_comp := by
    ext m
    simp only [LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply,
      LinearMap.lTensor_tmul, LinearEquiv.coe_coe, TensorProduct.rid_symm_apply]
    calc
      m ⊗ₜ[R] counit (R := R) e = counit (R := R) e • (m ⊗ₜ[R] (1 : R)) := by
        rw [← TensorProduct.tmul_smul]
        simp
      _ = (counit (R := R) e • m) ⊗ₜ[R] (1 : R) := TensorProduct.smul_tmul' _ _ _
      _ = m ⊗ₜ[R] (1 : R) := by rw [hcounit]

@[simp] theorem ofTensor_coaction (e : C) (hcomul hcounit) (m : M) :
    (ofTensor e hcomul hcounit : RightComodule R C M).coaction m = m ⊗ₜ[R] e := rfl

/-- Image stability of an existing submodule, without a chosen subtype coaction. -/
def IsStable (X : RightComodule R C M) (U : Submodule R M) : Prop :=
  ∀ m ∈ U, X.coaction m ∈ LinearMap.range (U.subtype.rTensor C)

/-- The image-stability condition concerns every member of the submodule. -/
theorem isStable_iff (X : RightComodule R C M) (U : Submodule R M) :
    X.IsStable U ↔ ∀ m ∈ U, X.coaction m ∈ LinearMap.range (U.subtype.rTensor C) := Iff.rfl

/-- A stable submodule has a tensor-inclusion preimage for each member. -/
theorem IsStable.coaction_mem_range {X : RightComodule R C M} {U : Submodule R M}
    (h : X.IsStable U) (m : M) (hm : m ∈ U) :
    ∃ t : U ⊗[R] C, U.subtype.rTensor C t = X.coaction m := h m hm

end RightComodule

/-- A linear map intertwining two specified right coactions. -/
structure RightComoduleHom {R : Type u} {C : Type v} {M : Type w} {N : Type z}
    [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    (X : RightComodule R C M) (Y : RightComodule R C N) extends M →ₗ[R] N where
  /-- The underlying linear map is right-colinear. -/
  colinear : Y.coaction ∘ₗ toLinearMap = toLinearMap.rTensor C ∘ₗ X.coaction

namespace RightComoduleHom

variable {R C M N P : Type*} [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
variable [AddCommMonoid P] [Module R P]
variable {X : RightComodule R C M} {Y : RightComodule R C N} {Z : RightComodule R C P}

instance : FunLike (RightComoduleHom X Y) M N where
  coe f := f.toLinearMap
  coe_injective f g h := by
    have hmap : f.toLinearMap = g.toLinearMap := DFunLike.coe_injective h
    cases f
    cases g
    cases hmap
    rfl

instance : CoeOut (RightComoduleHom X Y) (M →ₗ[R] N) := ⟨toLinearMap⟩

@[simp] theorem toLinearMap_apply (f : RightComoduleHom X Y) (m : M) :
    f.toLinearMap m = f m := rfl

/-- Right-comodule morphisms are determined by their values. -/
@[ext] theorem ext {f g : RightComoduleHom X Y} (h : ∀ m, f m = g m) : f = g :=
  DFunLike.ext _ _ h

/-- Colinearity evaluated at an element. -/
theorem colinear_apply (f : RightComoduleHom X Y) (m : M) :
    Y.coaction (f m) = f.toLinearMap.rTensor C (X.coaction m) :=
  LinearMap.congr_fun f.colinear m

/-- The inverse of a linear equivalence intertwining two specified right coactions
intertwines those coactions in the opposite direction. -/
theorem colinear_symm {R : Type u} {C : Type v} {M : Type w} {N : Type z}
    [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    {X : RightComodule R C M} {Y : RightComodule R C N}
    (e : M ≃ₗ[R] N)
    (h : Y.coaction ∘ₗ e.toLinearMap = e.toLinearMap.rTensor C ∘ₗ X.coaction) :
    X.coaction ∘ₗ e.symm.toLinearMap = e.symm.toLinearMap.rTensor C ∘ₗ Y.coaction := by
  rw [← LinearEquiv.coe_rTensor, ← LinearEquiv.symm_rTensor,
    LinearEquiv.eq_toLinearMap_symm_comp (e₁₂ := e.rTensor C),
    ← LinearMap.comp_assoc, LinearEquiv.comp_toLinearMap_symm_eq (e₁₂ := e),
    LinearEquiv.coe_rTensor]
  exact h.symm

/-- The identity right-comodule morphism. -/
def id (X : RightComodule R C M) : RightComoduleHom X X where
  toLinearMap := LinearMap.id
  colinear := by simp [LinearMap.rTensor_id]

@[simp] theorem id_apply (X : RightComodule R C M) (m : M) : id X m = m := rfl

/-- Composition of right-comodule morphisms. -/
def comp (g : RightComoduleHom Y Z) (f : RightComoduleHom X Y) : RightComoduleHom X Z where
  toLinearMap := g.toLinearMap ∘ₗ f.toLinearMap
  colinear := by
    calc
      Z.coaction ∘ₗ (g.toLinearMap ∘ₗ f.toLinearMap) =
          (Z.coaction ∘ₗ g.toLinearMap) ∘ₗ f.toLinearMap := by rw [LinearMap.comp_assoc]
      _ = (g.toLinearMap.rTensor C ∘ₗ Y.coaction) ∘ₗ f.toLinearMap := by rw [g.colinear]
      _ = g.toLinearMap.rTensor C ∘ₗ (Y.coaction ∘ₗ f.toLinearMap) := by
        rw [LinearMap.comp_assoc]
      _ = g.toLinearMap.rTensor C ∘ₗ (f.toLinearMap.rTensor C ∘ₗ X.coaction) := by
        rw [f.colinear]
      _ = (g.toLinearMap ∘ₗ f.toLinearMap).rTensor C ∘ₗ X.coaction := by
        rw [LinearMap.rTensor_comp, LinearMap.comp_assoc]

@[simp] theorem comp_apply (g : RightComoduleHom Y Z) (f : RightComoduleHom X Y) (m : M) :
    g.comp f m = g (f m) := rfl

@[simp] theorem id_comp (f : RightComoduleHom X Y) : (id Y).comp f = f := by ext; rfl
@[simp] theorem comp_id (f : RightComoduleHom X Y) : f.comp (id X) = f := by ext; rfl

/-- Composition of right-comodule morphisms is associative. -/
theorem comp_assoc {Q : Type*} [AddCommMonoid Q] [Module R Q]
    {W : RightComodule R C Q} (h : RightComoduleHom Z W)
    (g : RightComoduleHom Y Z) (f : RightComoduleHom X Y) :
    (h.comp g).comp f = h.comp (g.comp f) := by ext; rfl

end RightComoduleHom

namespace RightComoduleHom

/-!
## Module structure on comodule morphisms

The operations use the existing underlying linear map and preserve colinearity by
linearity of tensoring. The class/coercion and injective additive/module construction
follow Mathlib's `RepresentationTheory/Intertwining.lean`, by Stepan Nesterov and
Edison Xie, together with Mathlib's linear-map and tensor-product APIs.
-/

/-
The Intertwining formalization has the following notice:
Copyright (c) 2025 Stepan Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stepan Nesterov, Edison Xie
-/

variable {R : Type u} {C : Type v} {M : Type w} {N : Type z}
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
variable {X : RightComodule R C M} {Y : RightComodule R C N}

instance instLinearMapClass : LinearMapClass (RightComoduleHom X Y) R M N where
  map_add f := f.toLinearMap.map_add
  map_smulₛₗ f := f.toLinearMap.map_smul

/-- The generic linear map agrees with the original underlying linear map. -/
@[simp] theorem ofClass_eq_toLinearMap (f : RightComoduleHom X Y) :
    LinearMap.ofClass f = f.toLinearMap := rfl

/-- The original linear-map coercion is the underlying linear map. -/
theorem coe_eq_toLinearMap (f : RightComoduleHom X Y) :
    (f : M →ₗ[R] N) = f.toLinearMap := rfl

/-- The underlying linear map and the original function coercion agree. -/
@[simp] theorem coe_toLinearMap (f : RightComoduleHom X Y) :
    (f.toLinearMap : M → N) = f := rfl

/-- Forgetting colinearity is injective. -/
theorem toLinearMap_injective :
    Function.Injective (fun f : RightComoduleHom X Y ↦ f.toLinearMap) := by
  intro f g h
  exact ext (fun m ↦ LinearMap.congr_fun h m)

instance instZero : Zero (RightComoduleHom X Y) where
  zero :=
    { toLinearMap := 0
      colinear := by simp }

@[simp] theorem zero_apply (m : M) : (0 : RightComoduleHom X Y) m = 0 := rfl

@[simp] theorem toLinearMap_zero : (0 : RightComoduleHom X Y).toLinearMap = 0 := rfl

instance instAdd : Add (RightComoduleHom X Y) where
  add f g :=
    { toLinearMap := f.toLinearMap + g.toLinearMap
      colinear := by
        simp only [LinearMap.comp_add, LinearMap.rTensor_add, LinearMap.add_comp,
          f.colinear, g.colinear] }

@[simp] theorem add_apply (f g : RightComoduleHom X Y) (m : M) :
    (f + g) m = f m + g m := rfl

@[simp] theorem toLinearMap_add (f g : RightComoduleHom X Y) :
    (f + g).toLinearMap = f.toLinearMap + g.toLinearMap := rfl

instance instSMulNat : SMul ℕ (RightComoduleHom X Y) where
  smul n f :=
    { toLinearMap := n • f.toLinearMap
      colinear := by
        have ht : (n • f.toLinearMap).rTensor C = n • f.toLinearMap.rTensor C :=
          map_nsmul (LinearMap.rTensorHom C) n f.toLinearMap
        rw [ht]
        ext m
        simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_nsmul]
        exact congrArg (fun t : N ⊗[R] C ↦ n • t) (f.colinear_apply m) }

instance instAddCommMonoid : AddCommMonoid (RightComoduleHom X Y) :=
  toLinearMap_injective.addCommMonoid
    (fun f : RightComoduleHom X Y ↦ f.toLinearMap)
    toLinearMap_zero toLinearMap_add (fun _ _ ↦ rfl)

instance instSMul : SMul R (RightComoduleHom X Y) where
  smul r f :=
    { toLinearMap := r • f.toLinearMap
      colinear := by
        simp only [LinearMap.comp_smul, LinearMap.rTensor_smul, LinearMap.smul_comp,
          f.colinear] }

@[simp] theorem smul_apply (r : R) (f : RightComoduleHom X Y) (m : M) :
    (r • f) m = r • f m := rfl

@[simp] theorem toLinearMap_smul (r : R) (f : RightComoduleHom X Y) :
    (r • f).toLinearMap = r • f.toLinearMap := rfl

instance instModule : Module R (RightComoduleHom X Y) :=
  Function.Injective.module R
    { toFun := fun f : RightComoduleHom X Y ↦ f.toLinearMap
      map_zero' := toLinearMap_zero
      map_add' := toLinearMap_add }
    toLinearMap_injective toLinearMap_smul

/-- Forget colinearity as a linear map on the module of comodule morphisms. -/
def toLinearMapₗ (X : RightComodule R C M) (Y : RightComodule R C N) :
    RightComoduleHom X Y →ₗ[R] (M →ₗ[R] N) where
  toFun := toLinearMap
  map_add' := toLinearMap_add
  map_smul' := toLinearMap_smul

@[simp] theorem toLinearMapₗ_apply (X : RightComodule R C M) (Y : RightComodule R C N)
    (f : RightComoduleHom X Y) : toLinearMapₗ X Y f = f.toLinearMap := rfl

/-- The bundled linear map forgetting colinearity is injective. -/
theorem toLinearMapₗ_injective (X : RightComodule R C M) (Y : RightComodule R C N) :
    Function.Injective (toLinearMapₗ X Y) := toLinearMap_injective

end RightComoduleHom

namespace RightComodule

variable {R : Type u} {C : Type v} {M : Type w}
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M]

/-- A subcomodule is an existing submodule with a specified right coaction on
its subtype and a colinear inclusion. The subtype coaction is part of the data. -/
structure Subcomodule (X : RightComodule R C M) extends Submodule R M where
  /-- The right comodule on the existing submodule subtype. -/
  comodule : RightComodule R C toSubmodule
  /-- The subtype inclusion intertwines the coactions. -/
  subtype_colinear : toSubmodule.subtype.rTensor C ∘ₗ comodule.coaction =
    X.coaction ∘ₗ toSubmodule.subtype

namespace Subcomodule

variable {X : RightComodule R C M}

-- There is deliberately no SetLike instance: the subtype coaction is chosen data.
instance : Membership M X.Subcomodule := ⟨fun U m ↦ m ∈ U.toSubmodule⟩
instance : CoeOut X.Subcomodule (Submodule R M) := ⟨toSubmodule⟩
instance : CoeOut X.Subcomodule (Set M) := ⟨fun U ↦ (U.toSubmodule : Set M)⟩

@[simp] theorem mem_toSubmodule (U : X.Subcomodule) (m : M) :
    m ∈ U.toSubmodule ↔ m ∈ U := Iff.rfl

@[simp] theorem mem_mk (U : Submodule R M) (Y h) (m : M) :
    m ∈ (mk U Y h : X.Subcomodule) ↔ m ∈ U := Iff.rfl

/-- Inclusion of a subcomodule as a bundled right-comodule morphism. -/
def subtype (U : X.Subcomodule) : RightComoduleHom U.comodule X where
  toLinearMap := U.toSubmodule.subtype
  colinear := U.subtype_colinear.symm

@[simp] theorem subtype_apply (U : X.Subcomodule) (m : U.toSubmodule) :
    U.subtype m = (m : M) := rfl

/-- Any specified subtype coaction with colinear inclusion gives image stability,
without flatness of the coacting coalgebra. -/
theorem isStable (U : X.Subcomodule) : X.IsStable U.toSubmodule := by
  intro m hm
  refine ⟨U.comodule.coaction ⟨m, hm⟩, ?_⟩
  exact LinearMap.congr_fun U.subtype_colinear ⟨m, hm⟩

/-- Every member of a subcomodule has coaction in the range of the tensor inclusion. -/
theorem coaction_mem (U : X.Subcomodule) (m : M) (hm : m ∈ U) :
    X.coaction m ∈ LinearMap.range (U.toSubmodule.subtype.rTensor C) := U.isStable m hm

/-- The tensor range is characterized by a preimage, without flatness assumptions. -/
theorem coaction_mem_range_iff (U : X.Subcomodule) (m : M) :
    X.coaction m ∈ LinearMap.range (U.toSubmodule.subtype.rTensor C) ↔
      ∃ t : U.toSubmodule ⊗[R] C, U.toSubmodule.subtype.rTensor C t = X.coaction m := Iff.rfl

/-- The zero submodule with its zero subtype coaction. -/
def bot (X : RightComodule R C M) : X.Subcomodule where
  toSubmodule := ⊥
  comodule := {
    coaction := 0
    coassoc := by ext m; simp
    counit_comp := by
      ext m
      have hm : m = 0 := Subsingleton.elim _ _
      simp [hm] }
  subtype_colinear := by
    ext m
    have hm : m = 0 := Subsingleton.elim _ _
    simp [hm]

@[simp] theorem bot_toSubmodule (X : RightComodule R C M) :
    (bot X).toSubmodule = ⊥ := rfl

section Flat

variable [Module.Flat R C]

/-- The linear lift of an image-stable coaction supplied by `LinearMap.codLift`. -/
noncomputable def coactionLift (X : RightComodule R C M) (U : Submodule R M)
    (h : X.IsStable U) : U →ₗ[R] U ⊗[R] C :=
  (X.coaction.domRestrict U).codLift (U.subtype.rTensor C)
    (Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective)
    (fun m ↦ h m m.property)

/-- The linear lift satisfies the characteristic inclusion equation. -/
theorem subtype_rTensor_comp_coactionLift (X : RightComodule R C M) (U : Submodule R M)
    (h : X.IsStable U) :
    U.subtype.rTensor C ∘ₗ coactionLift X U h = X.coaction ∘ₗ U.subtype :=
  LinearMap.comp_codLift _ _ _ _

/-- The lifted coaction maps to the ambient coaction under the tensor inclusion. -/
@[simp] theorem subtype_rTensor_coactionLift (X : RightComodule R C M) (U : Submodule R M)
    (h : X.IsStable U) (m : U) :
    U.subtype.rTensor C (coactionLift X U h m) = X.coaction (m : M) :=
  LinearMap.congr_fun (subtype_rTensor_comp_coactionLift X U h) m

/-- Coassociativity of the lifted subtype coaction. -/
theorem coactionLift_coassoc (X : RightComodule R C M) (U : Submodule R M)
    (h : X.IsStable U) :
    TensorProduct.assoc R U C C ∘ₗ (coactionLift X U h).rTensor C ∘ₗ coactionLift X U h =
      (comul (R := R) (A := C)).lTensor U ∘ₗ coactionLift X U h := by
  let ρ := coactionLift X U h
  have hρ : U.subtype.rTensor C ∘ₗ ρ = X.coaction ∘ₗ U.subtype :=
    subtype_rTensor_comp_coactionLift X U h
  have hρ_tensor :
      (U.subtype.rTensor C).rTensor C ∘ₗ ρ.rTensor C =
        X.coaction.rTensor C ∘ₗ U.subtype.rTensor C := by
    simpa only [LinearMap.rTensor_comp] using
      congrArg (fun f : U →ₗ[R] M ⊗[R] C ↦ f.rTensor C) hρ
  -- Tensor the same injective inclusion by the flat coalgebra twice, then
  -- transport injectivity through the associators.
  have hi : Function.Injective (U.subtype.rTensor C) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective
  have hi₂ : Function.Injective ((U.subtype.rTensor C).rTensor C) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ hi
  have hi_assoc : Function.Injective (U.subtype.rTensor (C ⊗[R] C)) := by
    rw [LinearMap.rTensor_tensor]
    exact (TensorProduct.assoc R M C C).injective.comp
      (hi₂.comp (TensorProduct.assoc R U C C).symm.injective)
  have hassoc (t : (U ⊗[R] C) ⊗[R] C) :
      U.subtype.rTensor (C ⊗[R] C) (TensorProduct.assoc R U C C t) =
        TensorProduct.assoc R M C C ((U.subtype.rTensor C).rTensor C t) := by
    rw [LinearMap.rTensor_tensor]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  have hcomul :
      U.subtype.rTensor (C ⊗[R] C) ∘ₗ (comul (R := R) (A := C)).lTensor U =
        (comul (R := R) (A := C)).lTensor M ∘ₗ U.subtype.rTensor C := by
    rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  ext m
  apply hi_assoc
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  calc
    U.subtype.rTensor (C ⊗[R] C)
        (TensorProduct.assoc R U C C (ρ.rTensor C (ρ m))) =
        TensorProduct.assoc R M C C
          ((U.subtype.rTensor C).rTensor C (ρ.rTensor C (ρ m))) := hassoc _
    _ = TensorProduct.assoc R M C C
        (X.coaction.rTensor C (U.subtype.rTensor C (ρ m))) :=
      congrArg (TensorProduct.assoc R M C C) (LinearMap.congr_fun hρ_tensor (ρ m))
    _ = TensorProduct.assoc R M C C (X.coaction.rTensor C (X.coaction (m : M))) := by
      rw [show U.subtype.rTensor C (ρ m) = X.coaction (m : M) from
        subtype_rTensor_coactionLift X U h m]
    _ = (comul (R := R) (A := C)).lTensor M (X.coaction (m : M)) := X.coassoc_apply _
    _ = (comul (R := R) (A := C)).lTensor M (U.subtype.rTensor C (ρ m)) := by
      rw [show U.subtype.rTensor C (ρ m) = X.coaction (m : M) from
        subtype_rTensor_coactionLift X U h m]
    _ = U.subtype.rTensor (C ⊗[R] C) ((comul (R := R) (A := C)).lTensor U (ρ m)) :=
      (LinearMap.congr_fun hcomul (ρ m)).symm

/-- Right counitality of the lifted subtype coaction. -/
theorem coactionLift_counit_comp (X : RightComodule R C M) (U : Submodule R M)
    (h : X.IsStable U) :
    (counit (R := R) (A := C)).lTensor U ∘ₗ coactionLift X U h =
      (TensorProduct.rid R U).symm.toLinearMap := by
  have hnatural :
      U.subtype ∘ₗ (TensorProduct.rid R U).toLinearMap ∘ₗ
          (counit (R := R) (A := C)).lTensor U =
        (TensorProduct.rid R M).toLinearMap ∘ₗ
          (counit (R := R) (A := C)).lTensor M ∘ₗ U.subtype.rTensor C := by
    ext m c
    simp
  apply LinearMap.ext
  intro m
  apply (TensorProduct.rid R U).injective
  apply Subtype.val_injective
  calc
    ↑((TensorProduct.rid R U)
        (((counit (R := R) (A := C)).lTensor U ∘ₗ coactionLift X U h) m)) =
        (TensorProduct.rid R M)
          ((counit (R := R) (A := C)).lTensor M
            (U.subtype.rTensor C (coactionLift X U h m))) :=
      LinearMap.congr_fun hnatural (coactionLift X U h m)
    _ = (m : M) := by
      rw [show U.subtype.rTensor C (coactionLift X U h m) = X.coaction (m : M) from
        LinearMap.congr_fun (subtype_rTensor_comp_coactionLift X U h) m]
      exact X.rid_counit_coaction (m : M)
    _ = ↑((TensorProduct.rid R U) ((TensorProduct.rid R U).symm.toLinearMap m)) := by
      simp

/-- A stable submodule has its induced subtype right coaction when the coalgebra is flat. -/
noncomputable def ofIsStable (X : RightComodule R C M) (U : Submodule R M)
    (h : X.IsStable U) : X.Subcomodule where
  toSubmodule := U
  comodule := {
    coaction := coactionLift X U h
    coassoc := coactionLift_coassoc X U h
    counit_comp := coactionLift_counit_comp X U h }
  subtype_colinear := subtype_rTensor_comp_coactionLift X U h

@[simp] theorem ofIsStable_toSubmodule (X : RightComodule R C M) (U : Submodule R M)
    (h : X.IsStable U) : (ofIsStable X U h).toSubmodule = U := rfl

@[simp] theorem ofIsStable_coaction (X : RightComodule R C M) (U : Submodule R M)
    (h : X.IsStable U) : (ofIsStable X U h).comodule.coaction = coactionLift X U h := rfl

/-- Under flatness, the underlying submodule determines a subcomodule uniquely. -/
@[ext] theorem ext {U V : X.Subcomodule} (h : U.toSubmodule = V.toSubmodule) : U = V := by
  rcases U with ⟨U, Y, hY⟩
  rcases V with ⟨V, Z, hZ⟩
  change U = V at h
  subst V
  have hcomodule : Y = Z := by
    apply RightComodule.ext
    apply LinearMap.ext
    intro m
    apply Module.Flat.rTensor_preserves_injective_linearMap (M := C) U.subtype
      Subtype.val_injective
    exact (LinearMap.congr_fun hY m).trans (LinearMap.congr_fun hZ m).symm
  cases hcomodule
  rfl

/-- Any subcomodule agrees with the induced one on its underlying stable submodule. -/
theorem ofIsStable_eq (U : X.Subcomodule) : ofIsStable X U.toSubmodule U.isStable = U :=
  ext rfl

/-- A colinear map with values in a subcomodule has a unique colinear
factorization through its specified subtype coaction. -/
theorem existsUnique_factorization (U : X.Subcomodule) {N : Type z}
    [AddCommMonoid N] [Module R N] (Y : RightComodule R C N)
    (f : RightComoduleHom Y X) (hmem : ∀ n, f n ∈ U) :
    ∃! g : RightComoduleHom Y U.comodule, U.subtype.comp g = f := by
  let l : N →ₗ[R] U.toSubmodule :=
    LinearMap.codRestrict U.toSubmodule f.toLinearMap hmem
  have hl : U.toSubmodule.subtype ∘ₗ l = f.toLinearMap :=
    LinearMap.subtype_comp_codRestrict f.toLinearMap U.toSubmodule hmem
  have hinj : Function.Injective (U.toSubmodule.subtype.rTensor C) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective
  let g : RightComoduleHom Y U.comodule := {
    toLinearMap := l
    colinear := by
      apply LinearMap.ext
      intro n
      apply hinj
      calc
        U.toSubmodule.subtype.rTensor C (U.comodule.coaction (l n)) =
            X.coaction (U.toSubmodule.subtype (l n)) :=
          LinearMap.congr_fun U.subtype_colinear (l n)
        _ = X.coaction (f n) :=
          congrArg X.coaction (LinearMap.congr_fun hl n)
        _ = f.toLinearMap.rTensor C (Y.coaction n) := f.colinear_apply n
        _ = U.toSubmodule.subtype.rTensor C (l.rTensor C (Y.coaction n)) := by
          rw [← LinearMap.rTensor_comp_apply, hl] }
  have hg : U.subtype.comp g = f := by
    apply RightComoduleHom.ext
    intro n
    exact LinearMap.congr_fun hl n
  refine ⟨g, hg, ?_⟩
  intro g' hg'
  apply RightComoduleHom.ext
  intro n
  apply Subtype.val_injective
  have hcomp : U.subtype.comp g' = U.subtype.comp g := hg'.trans hg.symm
  simpa only [RightComoduleHom.comp_apply, subtype_apply] using
    congrArg (fun k : RightComoduleHom Y X ↦ k n) hcomp

end Flat
end Subcomodule

/-- Every finite subset of a right comodule over a projective coalgebra is
contained in a module-finitely-generated submodule with a subtype coaction and
colinear inclusion. Stability holds for every member, not only for a chosen
generating set. This extends the
classical coefficient method for comodules from Sweedler's *Hopf Algebras*;
projectivity is imposed on the coalgebra, never on the ambient comodule. -/
theorem exists_fg_subcomodule_of_finite [Module.Projective R C]
    (X : RightComodule R C M) {s : Set M} (hs : s.Finite) :
    ∃ U : X.Subcomodule, s ⊆ (U : Set M) ∧ U.toSubmodule.FG := by
  obtain ⟨U, hsU, hfg, hstable⟩ :=
    exists_fg_submodule_coaction_right_closed_of_finite
      X.coaction X.coassoc X.counit_comp hs
  exact ⟨Subcomodule.ofIsStable X U hstable, hsU, hfg⟩

variable (X : RightComodule R C M)

/-- The underlying submodules of module-finite subcomodules are directed when
the coacting coalgebra is projective. -/
theorem directed_fg_toSubmodule [Module.Projective R C] :
    Directed (· ≤ ·)
      (fun U : {U : X.Subcomodule // Module.Finite R U.toSubmodule} =>
        U.val.toSubmodule) := by
  intro U V
  have hfg : (U.val.toSubmodule ⊔ V.val.toSubmodule).FG :=
    (Module.Finite.iff_fg.mp U.property).sup (Module.Finite.iff_fg.mp V.property)
  obtain ⟨s, hs, hspan⟩ := Submodule.fg_def.mp hfg
  obtain ⟨W, hsW, hW⟩ := X.exists_fg_subcomodule_of_finite hs
  have hle : U.val.toSubmodule ⊔ V.val.toSubmodule ≤ W.toSubmodule := by
    rw [← hspan]
    exact Submodule.span_le.mpr hsW
  exact ⟨⟨W, Module.Finite.iff_fg.mpr hW⟩,
    le_sup_left.trans hle, le_sup_right.trans hle⟩

/-- Every element lies in a module-finite subcomodule when the coacting
coalgebra is projective. -/
theorem iUnion_fg_eq_univ [Module.Projective R C] :
    (⋃ U : {U : X.Subcomodule // Module.Finite R U.toSubmodule},
      (U.val : Set M)) = Set.univ := by
  apply Set.iUnion_eq_univ_iff.mpr
  intro m
  obtain ⟨U, hmU, hU⟩ := X.exists_fg_subcomodule_of_finite (Set.finite_singleton m)
  exact ⟨⟨U, Module.Finite.iff_fg.mpr hU⟩, hmU (Set.mem_singleton m)⟩

end RightComodule

/-- The regular-comodule specialization uses the existing projective-coalgebra
right-coideal theorem, with its scalar argument and finite-subset convention. -/
theorem exists_fg_regular_subcomodule_of_finite {K : Type u} {C : Type v}
    [CommSemiring K] [AddCommMonoid C] [Module K C] [Coalgebra K C]
    [Module.Projective K C] {s : Set C} (hs : s.Finite) :
    ∃ U : (RightComodule.regular K C).Subcomodule,
      s ⊆ (U : Set C) ∧ U.toSubmodule.FG := by
  obtain ⟨U, hsU, hfg, hclosed⟩ :=
    exists_fg_submodule_comul_right_closed_of_finite (K := K) hs
  exact ⟨RightComodule.Subcomodule.ofIsStable (RightComodule.regular K C) U hclosed, hsU, hfg⟩

end Coalgebra

namespace Coalgebra.RightComodule

variable {R : Type u} {M : Type w}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The scalar right comodule, with coaction the inverse right unitor. -/
def scalar (R : Type u) (M : Type w) [CommSemiring R] [AddCommMonoid M] [Module R M] :
    RightComodule R R M where
  coaction := (TensorProduct.rid R M).symm.toLinearMap
  coassoc := by
    ext m
    simp [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]
  counit_comp := by
    ext m
    simp [LinearMap.lTensor_tmul]

@[simp] theorem scalar_coaction (m : M) : (scalar R M).coaction m = m ⊗ₜ[R] 1 := rfl

/-- Every submodule has the direct scalar subtype coaction, with colinear inclusion. -/
def scalarSubcomodule (U : Submodule R M) : (scalar R M).Subcomodule where
  toSubmodule := U
  comodule := scalar R U
  subtype_colinear := by
    ext m
    simp

@[simp] theorem scalarSubcomodule_toSubmodule (U : Submodule R M) :
    (scalarSubcomodule U).toSubmodule = U := rfl

@[simp] theorem scalarSubcomodule_comodule (U : Submodule R M) :
    (scalarSubcomodule U).comodule = scalar R U := rfl

/-- Every submodule satisfies image stability under the scalar coaction. -/
theorem scalar_isStable (U : Submodule R M) : (scalar R M).IsStable U :=
  (scalarSubcomodule U).isStable

/-- The direct scalar coaction on a subtype commutes with its inclusion.
This does not use the general induced-subtype construction. -/
theorem scalar_subtype_colinear (U : Submodule R M) :
    U.subtype.rTensor R ∘ₗ (scalar R U).coaction = (scalar R M).coaction ∘ₗ U.subtype := by
  ext m
  simp

end Coalgebra.RightComodule

/-! ## Algebra-valued evaluation and image stability -/

universe uR uC uM uA uB

namespace Coalgebra.RightComodule

variable {R₀ : Type uR} {C₀ : Type uC} {M₀ : Type uM}
variable [CommSemiring R₀] [CommSemiring C₀]
variable [Algebra R₀ C₀] [Coalgebra R₀ C₀]
variable [AddCommMonoid M₀] [Module R₀ M₀]

/-- Evaluation on a pure tensor uses the left scalar action: a coaction term
`mᵢ ⊗ cᵢ` contributes `(a * α cᵢ) ⊗ mᵢ`. -/
theorem evaluation_tmul
    (X : Coalgebra.RightComodule R₀ C₀ M₀)
    {A : Type uA} [CommSemiring A] [Algebra R₀ A]
    (α : C₀ →ₐ[R₀] A) (a : A) (m : M₀) :
    LinearMap.liftBaseChange A
        ((TensorProduct.map (AlgHom.toLinearMap α)
            (LinearMap.id : M₀ →ₗ[R₀] M₀)).comp
          ((TensorProduct.comm R₀ M₀ C₀).toLinearMap.comp X.coaction))
        (a ⊗ₜ[R₀] m) =
      a • TensorProduct.map (AlgHom.toLinearMap α)
        (LinearMap.id : M₀ →ₗ[R₀] M₀)
        (TensorProduct.comm R₀ M₀ C₀ (X.coaction m)) := by
  rw [LinearMap.liftBaseChange_tmul]
  rfl

/-- The identity one-tensor test recovers the commuted original coaction. -/
theorem id_evaluation_one_tmul
    (X : Coalgebra.RightComodule R₀ C₀ M₀) (m : M₀) :
    LinearMap.liftBaseChange C₀
        ((TensorProduct.map (AlgHom.toLinearMap (AlgHom.id R₀ C₀))
            (LinearMap.id : M₀ →ₗ[R₀] M₀)).comp
          ((TensorProduct.comm R₀ M₀ C₀).toLinearMap.comp X.coaction))
        (1 ⊗ₜ[R₀] m) =
      TensorProduct.comm R₀ M₀ C₀ (X.coaction m) := by
  rw [LinearMap.liftBaseChange_one_tmul]
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_id,
    TensorProduct.map_id, LinearMap.id_apply]
  rfl

/-- Evaluation is natural in its target algebra, as an equality of elements
of the target tensor product. The tensor transport is only `R₀`-linear. -/
theorem evaluation_naturality
    (X : Coalgebra.RightComodule R₀ C₀ M₀)
    {A : Type uA} {B : Type uB}
    [CommSemiring A] [CommSemiring B] [Algebra R₀ A] [Algebra R₀ B]
    (α : C₀ →ₐ[R₀] A) (q : A →ₐ[R₀] B) (z : A ⊗[R₀] M₀) :
    TensorProduct.map (AlgHom.toLinearMap q)
        (LinearMap.id : M₀ →ₗ[R₀] M₀)
        (LinearMap.liftBaseChange A
          ((TensorProduct.map (AlgHom.toLinearMap α)
              (LinearMap.id : M₀ →ₗ[R₀] M₀)).comp
            ((TensorProduct.comm R₀ M₀ C₀).toLinearMap.comp X.coaction)) z) =
      LinearMap.liftBaseChange B
        ((TensorProduct.map (AlgHom.toLinearMap (q.comp α))
            (LinearMap.id : M₀ →ₗ[R₀] M₀)).comp
          ((TensorProduct.comm R₀ M₀ C₀).toLinearMap.comp X.coaction))
        (TensorProduct.map (AlgHom.toLinearMap q)
          (LinearMap.id : M₀ →ₗ[R₀] M₀) z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a m =>
      have h (y : C₀ ⊗[R₀] M₀) :
          TensorProduct.map (AlgHom.toLinearMap q)
              (LinearMap.id : M₀ →ₗ[R₀] M₀)
              (a • TensorProduct.map (AlgHom.toLinearMap α)
                (LinearMap.id : M₀ →ₗ[R₀] M₀) y) =
            q a • TensorProduct.map (AlgHom.toLinearMap (q.comp α))
              (LinearMap.id : M₀ →ₗ[R₀] M₀) y := by
        induction y using TensorProduct.inductionOn with
        | tmul c n =>
            simp [TensorProduct.smul_tmul', smul_eq_mul]
        | add y y' hy hy' =>
            simpa only [map_add, smul_add] using
              congrArg₂ (fun x x' : B ⊗[R₀] M₀ => x + x') hy hy'
      simpa only [evaluation_tmul, TensorProduct.map_tmul,
        AlgHom.toLinearMap_apply, LinearMap.id_apply] using
        h (TensorProduct.comm R₀ M₀ C₀ (X.coaction m))
  | add z z' hz hz' =>
      simpa only [map_add] using
        congrArg₂ (fun x x' : B ⊗[R₀] M₀ => x + x') hz hz'

/-- Stability preserves the scalar-extension image under every one-algebra
evaluation, with the algebra universe independent of the coalgebra universe. -/
theorem IsStable.evaluation_mem_baseChange
    {X : Coalgebra.RightComodule R₀ C₀ M₀} {U : Submodule R₀ M₀}
    (hU : X.IsStable U)
    {A : Type uA} [CommSemiring A] [Algebra R₀ A]
    (α : C₀ →ₐ[R₀] A) (z : A ⊗[R₀] M₀) (hz : z ∈ U.baseChange A) :
    LinearMap.liftBaseChange A
        ((TensorProduct.map (AlgHom.toLinearMap α)
            (LinearMap.id : M₀ →ₗ[R₀] M₀)).comp
          ((TensorProduct.comm R₀ M₀ C₀).toLinearMap.comp X.coaction)) z
      ∈ U.baseChange A := by
  have hmem (m : M₀) (hm : m ∈ U) :
      TensorProduct.map (AlgHom.toLinearMap α)
          (LinearMap.id : M₀ →ₗ[R₀] M₀)
          (TensorProduct.comm R₀ M₀ C₀ (X.coaction m)) ∈ U.baseChange A := by
    exact U.map_mem_baseChange (AlgHom.toLinearMap α)
      ((TensorProduct.comm_mem_baseChange_iff U (X.coaction m)).mpr
        (hU.coaction_mem_range m hm))
  obtain ⟨w, rfl⟩ := hz
  induction w using TensorProduct.inductionOn with
  | tmul a u =>
      rw [LinearMap.baseChange_tmul, evaluation_tmul]
      exact (U.baseChange A).smul_mem a (hmem (u : M₀) u.property)
  | add w w' hw hw' =>
      simpa only [map_add] using (U.baseChange A).add_mem hw hw'

/-- The identity-algebra evaluation criterion for image stability, with the
right-coaction convention of Sweedler, *Hopf Algebras*. No subtype coaction or
tensor-inclusion injectivity is required. -/
theorem isStable_iff_id_evaluation_mem_baseChange
    (X : Coalgebra.RightComodule R₀ C₀ M₀) (U : Submodule R₀ M₀) :
    X.IsStable U ↔
      ∀ z ∈ U.baseChange C₀,
        LinearMap.liftBaseChange C₀
          ((TensorProduct.map (AlgHom.toLinearMap (AlgHom.id R₀ C₀))
              (LinearMap.id : M₀ →ₗ[R₀] M₀)).comp
            ((TensorProduct.comm R₀ M₀ C₀).toLinearMap.comp X.coaction)) z
          ∈ U.baseChange C₀ := by
  constructor
  · intro hU z hz
    exact hU.evaluation_mem_baseChange (AlgHom.id R₀ C₀) z hz
  · intro h
    apply (X.isStable_iff U).2
    intro m hm
    apply (TensorProduct.comm_mem_baseChange_iff U (X.coaction m)).mp
    rw [← X.id_evaluation_one_tmul m]
    exact h (1 ⊗ₜ[R₀] m) (Submodule.tmul_mem_baseChange_of_mem 1 hm)

/-- Image stability is detected by evaluations in all commutative algebras in
the compatible maximum universe, with the right-coaction convention of Sweedler,
*Hopf Algebras*. The lifted coefficient algebra supplies the detector without
restricting the independently universe-polymorphic forward implication. -/
theorem isStable_iff_forall_evaluation_mem_baseChange
    (X : Coalgebra.RightComodule R₀ C₀ M₀) (U : Submodule R₀ M₀) :
    X.IsStable U ↔
      ∀ (A : Type (max uC uA)) [CommSemiring A] [Algebra R₀ A]
          (α : C₀ →ₐ[R₀] A),
        ∀ z ∈ U.baseChange A,
          LinearMap.liftBaseChange A
            ((TensorProduct.map (AlgHom.toLinearMap α)
                (LinearMap.id : M₀ →ₗ[R₀] M₀)).comp
              ((TensorProduct.comm R₀ M₀ C₀).toLinearMap.comp X.coaction)) z
            ∈ U.baseChange A := by
  constructor
  · intro hX A _ _ α z hz
    exact hX.evaluation_mem_baseChange (A := A) α z hz
  · intro h
    apply (X.isStable_iff U).2
    intro m hm
    let L : Type (max uC uA) := ULift.{uA} C₀
    let e : L ≃ₐ[R₀] C₀ := ULift.algEquiv (R := R₀) (A := C₀)
    let α : C₀ →ₐ[R₀] L := e.symm.toAlgHom
    let downM : L ⊗[R₀] M₀ →ₗ[R₀] C₀ ⊗[R₀] M₀ :=
      TensorProduct.map e.toLinearMap (LinearMap.id : M₀ →ₗ[R₀] M₀)
    have hcancel (y : C₀ ⊗[R₀] M₀) :
        downM (TensorProduct.map (AlgHom.toLinearMap α)
          (LinearMap.id : M₀ →ₗ[R₀] M₀) y) = y := by
      induction y using TensorProduct.inductionOn with
      | tmul c m' =>
          change e (e.symm c) ⊗ₜ[R₀] m' = c ⊗ₜ[R₀] m'
          rw [e.apply_symm_apply]
      | add x y hx hy =>
          simp only [map_add, hx, hy]
    have hz :=
      h L α ((1 : L) ⊗ₜ[R₀] m)
        (Submodule.tmul_mem_baseChange_of_mem (1 : L) hm)
    rw [LinearMap.liftBaseChange_one_tmul] at hz
    have hdown := U.map_mem_baseChange e.toLinearMap hz
    change downM (TensorProduct.map (AlgHom.toLinearMap α)
      (LinearMap.id : M₀ →ₗ[R₀] M₀)
      (TensorProduct.comm R₀ M₀ C₀ (X.coaction m))) ∈ U.baseChange C₀ at hdown
    rw [hcancel] at hdown
    exact (TensorProduct.comm_mem_baseChange_iff U (X.coaction m)).mp hdown

end Coalgebra.RightComodule
