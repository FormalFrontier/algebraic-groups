/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.RingTheory.HopfAlgebra.Convolution
public import Mathlib.RingTheory.Bialgebra.Hom
public import Mathlib.RingTheory.Coalgebra.GroupLike
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Hopf tensor products and the counit fiber

For a central bialgebra map from a commutative bialgebra `A` to a possibly
noncommutative Hopf algebra `B`, comultiplication identifies `B ⊗[A] B` with
`B ⊗[R] (B / (ker ε_A)B)` as left `B`-modules. Both actions are on the first
factor. The linear construction uses only the module structure on the quotient.
When `B` is commutative, the same equivalence respects the quotient-ring and
tensor-product multiplications, giving an equivalence of `B`-algebras with the
same forward and inverse functions.

The antipode of `B` supplies the inverse. No antipode on `A`, injectivity,
flatness, or finiteness assumption is needed. The compatibility equations concern
`IsScalarTower.toAlgHom R A B`, whose underlying map is the original
`algebraMap A B`; no other scalar structure is substituted.

## Main declarations

* `HopfAlgebra.tensorQuotientEquiv`: the equivalence for the original tensor
  products, module quotient, and first-factor actions.
* `HopfAlgebra.tensorQuotientEquiv_tmul` and
  `HopfAlgebra.tensorQuotientEquiv_symm_tmul`: finite-comultiplication formulas
  for both directions. These are the computation API for the opaque construction.
* `HopfAlgebra.tensorQuotientEquiv_symm_mul_tmul_of_isGroupLikeElem`: the
  resulting coordinate conversion for a group-like element.
* `HopfAlgebra.tensorQuotientAlgEquiv`: the algebra equivalence when `B` is
  commutative. Its underlying linear equivalence is characterized by
  `HopfAlgebra.tensorQuotientAlgEquiv_toLinearEquiv`, so the same finite formulas
  compute both directions.

## References

* Mathlib, `RingTheory/HopfAlgebra/Convolution`: antipode antimultiplicativity
  and convolution of linear maps.
* Mathlib, `LinearAlgebra/TensorProduct/Tower` and `LinearAlgebra/Quotient/Basic`:
  the tensor and quotient universal properties.
* Mathlib, `Algebra/Algebra/Equiv`, `RingTheory/TensorProduct/Maps`, and
  `RingTheory/Ideal/Quotient/Operations`: algebra refinement of linear equivalences,
  multiplication on tensor generators, and the quotient algebra structure.
-/

public section

noncomputable section

universe uR uA uB uι

open scoped BigOperators TensorProduct
open TensorProduct WithConv

namespace HopfAlgebra

variable (R : Type uR) (A : Type uA) (B : Type uB)
variable [CommRing R] [CommRing A] [Bialgebra R A]
variable [Ring B] [HopfAlgebra R B] [Algebra A B] [IsScalarTower R A B]

local notation "I" => RingHom.ker (Bialgebra.counitAlgHom R A : A →+* R)
local notation "J" => Ideal.map (algebraMap A B) I
local notation "Q" => B ⧸ J
local notation "U" => B ⊗[A] B
local notation "V" => B ⊗[R] Q
local notation "i" => algebraMap A B
local notation "S" => antipode R (A := B)

private def quotientMap : B →ₗ[R] Q :=
  (Submodule.Quotient.restrictScalarsEquiv R J).toLinearMap ∘ₗ
    (Submodule.restrictScalars R J).mkQ

omit [IsScalarTower R A B] in
@[simp] private theorem quotientMap_apply (b : B) :
    quotientMap R A B b = Submodule.Quotient.mk b := rfl

-- Keep the all-coefficient scalar relation separate: this is the only step
-- using subtraction in the base and the central bialgebra.
private theorem quotientMap_mul_algebraMap (a : A) (b : B) :
    quotientMap R A B (b * i a) =
      Bialgebra.counitAlgHom R A a • quotientMap R A B b := by
  rw [quotientMap_apply, quotientMap_apply, ← Submodule.Quotient.mk_smul]
  apply (Submodule.Quotient.eq _).2
  have ha : a - algebraMap R A (Bialgebra.counitAlgHom R A a) ∈ I := by
    rw [RingHom.mem_ker]
    change Bialgebra.counitAlgHom R A
      (a - algebraMap R A (Bialgebra.counitAlgHom R A a)) = 0
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply, sub_self]
  have hb : b * i (a - algebraMap R A (Bialgebra.counitAlgHom R A a)) ∈ J :=
    Ideal.mul_mem_left _ b (Ideal.mem_map_of_mem (algebraMap A B) ha)
  simpa only [map_sub, mul_sub, ← IsScalarTower.algebraMap_apply R A B,
    Algebra.smul_def, Algebra.commutes] using hb

private def forwardSeed : B →ₗ[R] V :=
  TensorProduct.map LinearMap.id (quotientMap R A B) ∘ₗ Coalgebra.comul

omit [IsScalarTower R A B] in
private theorem forwardSeed_repr {ι : Type uι} (c : B) (r : Coalgebra.Repr R c ι) :
    forwardSeed R A B c =
      ∑ k ∈ r.index, r.left k ⊗ₜ[R] quotientMap R A B (r.right k) := by
  change TensorProduct.map LinearMap.id (quotientMap R A B) (Coalgebra.comul c) = _
  rw [← r.eq, map_sum]
  simp only [TensorProduct.map_tmul, LinearMap.id_apply]

private def inverseSeed : B →ₗ[R] U :=
  (toConv
      (((Algebra.TensorProduct.includeLeft : B →ₐ[A] U).restrictScalars R).toLinearMap
        ∘ₗ S) *
    toConv
      ((Algebra.TensorProduct.includeRight : B →ₐ[A] U).restrictScalars R).toLinearMap).ofConv

private theorem inverseSeed_repr {ι : Type uι} (c : B) (r : Coalgebra.Repr R c ι) :
    inverseSeed R A B c = ∑ k ∈ r.index, S (r.left k) ⊗ₜ[A] r.right k := by
  rw [inverseSeed, r.convMul_apply]
  simp [Algebra.TensorProduct.tmul_mul_tmul]

variable
  (counit_comp :
    (Bialgebra.counitAlgHom R B).comp (IsScalarTower.toAlgHom R A B) =
      Bialgebra.counitAlgHom R A)
  (map_comp_comul :
    (Algebra.TensorProduct.map
      (IsScalarTower.toAlgHom R A B)
      (IsScalarTower.toAlgHom R A B)).comp (Bialgebra.comulAlgHom R A) =
        (Bialgebra.comulAlgHom R B).comp (IsScalarTower.toAlgHom R A B))

private def scalarBialgHom : A →ₐc[R] B :=
  BialgHom.ofAlgHom (IsScalarTower.toAlgHom R A B) counit_comp map_comp_comul

@[simp] private theorem scalarBialgHom_apply (a : A) :
    scalarBialgHom R A B counit_comp map_comp_comul a = i a := rfl

omit [Bialgebra R A] [IsScalarTower R A B] in
private theorem antipode_algebraMap_comm (a : A) (c : B) :
    S (i a) * S c = S c * S (i a) := by
  rw [← antipode_mul_antidistrib, ← antipode_mul_antidistrib, Algebra.commutes]

include counit_comp map_comp_comul in
private theorem inverseSeed_mul_algebraMap (c : B) (a : A) :
    inverseSeed R A B (c * i a) =
      Bialgebra.counitAlgHom R A a • inverseSeed R A B c := by
  classical
  let r := Coalgebra.Repr.arbitrary R c
  let t := Coalgebra.Repr.arbitrary R a
  let f := scalarBialgHom R A B counit_comp map_comp_comul
  let ht : Coalgebra.Repr R (i a) (A × A) := t.induced f
  have htindex : ht.index = t.index := rfl
  have htleft (k) : ht.left k = i (t.left k) := rfl
  have htright (k) : ht.right k = i (t.right k) := rfl
  have heps : Coalgebra.counit (R := R) (i a) = Bialgebra.counitAlgHom R A a :=
    CoalgHomClass.counit_comp_apply f a
  have hs : ∑ k ∈ t.index, S (i (t.left k)) * i (t.right k) =
      algebraMap R B (Bialgebra.counitAlgHom R A a) := by
    simpa only [htindex, htleft, htright, heps]
      using sum_antipode_mul_eq_algebraMap_counit ht
  have hterm (x y : B) (v w : A) :
      S (x * i v) ⊗ₜ[A] (y * i w) =
        (S x * (S (i v) * i w)) ⊗ₜ[A] y := by
    rw [antipode_mul_antidistrib, antipode_algebraMap_comm R A B,
      ← Algebra.commutes w y, ← Algebra.smul_def w y, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul' w, Algebra.smul_def, Algebra.commutes w, mul_assoc]
  rw [inverseSeed_repr R A B _ (r.mul ht)]
  simp only [Coalgebra.Repr.mul_index, Coalgebra.Repr.mul_left,
    Coalgebra.Repr.mul_right, Finset.sum_product, htindex, htleft, htright]
  simp_rw [hterm]
  have hsum (x y : B) :
      (∑ k ∈ t.index, (S x * (S (i (t.left k)) * i (t.right k))) ⊗ₜ[A] y) =
        Bialgebra.counitAlgHom R A a • (S x ⊗ₜ[A] y) := by
    rw [← TensorProduct.sum_tmul, ← Finset.mul_sum, hs]
    change ((S x * algebraMap R B (Bialgebra.counitAlgHom R A a)) ⊗ₜ[A] y) =
      (Bialgebra.counitAlgHom R A a • S x) ⊗ₜ[A] y
    rw [Algebra.smul_def, Algebra.commutes]
  simp_rw [hsum]
  rw [← Finset.smul_sum, ← inverseSeed_repr R A B c r]

include counit_comp map_comp_comul in
private theorem forwardSeed_smul (a : A) (c : B) :
    forwardSeed R A B (a • c) = a • forwardSeed R A B c := by
  classical
  let r := Coalgebra.Repr.arbitrary R c
  let t := Coalgebra.Repr.arbitrary R a
  let f := scalarBialgHom R A B counit_comp map_comp_comul
  let ht : Coalgebra.Repr R (i a) (A × A) := t.induced f
  have htindex : ht.index = t.index := rfl
  have htleft (k) : ht.left k = i (t.left k) := rfl
  have htright (k) : ht.right k = i (t.right k) := rfl
  have hcounit : ∑ k ∈ t.index,
      Coalgebra.counit (R := R) (t.right k) • t.left k = a := by
    simpa only [map_sum, TensorProduct.rid_tmul, one_smul]
      using congrArg (TensorProduct.rid R A) (Coalgebra.sum_tmul_counit_eq t)
  have hsum (x : B) (z : Q) :
      (∑ k ∈ t.index, (x * i (t.left k)) ⊗ₜ[R]
        (Bialgebra.counitAlgHom R A (t.right k) • z)) =
          a • (x ⊗ₜ[R] z) := by
    let F : A →ₗ[R] V :=
      ((TensorProduct.mk R B Q).flip z) ∘ₗ
        (LinearMap.mulLeft R x) ∘ₗ (IsScalarTower.toAlgHom R A B).toLinearMap
    have hF (v : A) : F v = (x * i v) ⊗ₜ[R] z := rfl
    have h := congrArg F hcounit
    rw [map_sum] at h
    simp only [map_smul] at h
    simp only [hF] at h
    simpa only [TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      Bialgebra.counitAlgHom_apply, Algebra.smul_def, Algebra.commutes] using h
  rw [Algebra.smul_def, Algebra.commutes a c,
    forwardSeed_repr R A B _ (r.mul ht)]
  simp only [Coalgebra.Repr.mul_index, Coalgebra.Repr.mul_left,
    Coalgebra.Repr.mul_right, Finset.sum_product, htindex, htleft, htright]
  simp_rw [quotientMap_mul_algebraMap R A B, hsum]
  rw [← Finset.smul_sum, ← forwardSeed_repr R A B c r]

private def forwardMap : U →ₗ[B] V :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun b =>
        { toFun := fun c => b • forwardSeed R A B c
          map_add' := fun c d => by rw [map_add, smul_add]
          map_smul' := fun a c => by
            rw [forwardSeed_smul R A B counit_comp map_comp_comul,
              smul_comm, RingHom.id_apply] }
      map_add' := fun b d => by
        apply LinearMap.ext; intro c
        exact add_smul b d (forwardSeed R A B c)
      map_smul' := fun b d => by
        apply LinearMap.ext; intro c
        exact mul_smul b d (forwardSeed R A B c) }

@[simp] private theorem forwardMap_tmul (b c : B) :
    forwardMap R A B counit_comp map_comp_comul (b ⊗ₜ[A] c) =
      b • forwardSeed R A B c := rfl

include counit_comp map_comp_comul in
private theorem inverseSeed_kills (x : B) (hx : x ∈ J) :
    inverseSeed R A B x = 0 := by
  have hall : ∀ d : B, inverseSeed R A B (d * x) = 0 := by
    induction hx using Submodule.span_induction with
    | mem y hy =>
        rcases hy with ⟨a, ha, rfl⟩
        intro d
        rw [inverseSeed_mul_algebraMap R A B counit_comp map_comp_comul]
        have ha' : Bialgebra.counitAlgHom R A a = 0 := ha
        rw [ha', zero_smul]
    | zero => intro d; simp
    | add y z hy hz ihy ihz => intro d; simp [mul_add, ihy, ihz]
    | smul d y hy ih => intro e; simpa [smul_eq_mul, mul_assoc] using ih (e * d)
  simpa using hall 1

private def inverseQuotient : Q →ₗ[R] U :=
  ((Submodule.restrictScalars R J).liftQ (inverseSeed R A B)
    (fun x hx => inverseSeed_kills R A B counit_comp map_comp_comul x hx)) ∘ₗ
      (Submodule.Quotient.restrictScalarsEquiv R J).symm.toLinearMap

@[simp] private theorem inverseQuotient_mk (c : B) :
    inverseQuotient R A B counit_comp map_comp_comul (Submodule.Quotient.mk c) =
      inverseSeed R A B c := rfl

private def inverseMap : V →ₗ[B] U :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun b =>
        { toFun := fun z => b • inverseQuotient R A B counit_comp map_comp_comul z
          map_add' := fun z w => by rw [map_add, smul_add]
          map_smul' := fun r z => by rw [map_smul, smul_comm, RingHom.id_apply] }
      map_add' := fun b d => by
        apply LinearMap.ext; intro z
        exact add_smul b d (inverseQuotient R A B counit_comp map_comp_comul z)
      map_smul' := fun b d => by
        apply LinearMap.ext; intro z
        exact mul_smul b d (inverseQuotient R A B counit_comp map_comp_comul z) }

@[simp] private theorem inverseMap_tmul (b : B) (z : Q) :
    inverseMap R A B counit_comp map_comp_comul (b ⊗ₜ[R] z) =
      b • inverseQuotient R A B counit_comp map_comp_comul z := rfl

-- Apply coassociativity before contracting the first two coproduct legs.
-- These identities live in the ordinary R-tensor product; the final maps below
-- apply only the canonical scalar-balancing and quotient maps to them.
omit [CommRing A] [Bialgebra R A] [Algebra A B] [IsScalarTower R A B] in
private theorem contract_antipode_left (c : B) :
    TensorProduct.map
      (LinearMap.mul' R B ∘ₗ TensorProduct.map S LinearMap.id) LinearMap.id
      ((TensorProduct.assoc R B B B).symm
        (TensorProduct.map LinearMap.id Coalgebra.comul (Coalgebra.comul c))) =
      (1 : B) ⊗ₜ[R] c := by
  change TensorProduct.map
    (LinearMap.mul' R B ∘ₗ TensorProduct.map S LinearMap.id) LinearMap.id
    ((TensorProduct.assoc R B B B).symm
      (Coalgebra.comul.lTensor B (Coalgebra.comul c))) = _
  rw [Coalgebra.coassoc_symm_apply]
  change TensorProduct.map
    (LinearMap.mul' R B ∘ₗ TensorProduct.map S LinearMap.id) LinearMap.id
      (TensorProduct.map Coalgebra.comul LinearMap.id (Coalgebra.comul c)) = _
  rw [TensorProduct.map_map, LinearMap.id_comp]
  have h : (LinearMap.mul' R B ∘ₗ TensorProduct.map S LinearMap.id) ∘ₗ
      Coalgebra.comul = Algebra.linearMap R B ∘ₗ Coalgebra.counit :=
    mul_antipode_rTensor_comul
  rw [h]
  calc
    TensorProduct.map (Algebra.linearMap R B ∘ₗ Coalgebra.counit) LinearMap.id
        (Coalgebra.comul c) =
      TensorProduct.map (Algebra.linearMap R B) LinearMap.id
        (Coalgebra.counit.rTensor B (Coalgebra.comul c)) := by
          rw [LinearMap.rTensor_def, TensorProduct.map_map, LinearMap.id_comp]
    _ = _ := by rw [Coalgebra.rTensor_counit_comul]; simp

omit [CommRing A] [Bialgebra R A] [Algebra A B] [IsScalarTower R A B] in
private theorem contract_antipode_right (c : B) :
    TensorProduct.map
      (LinearMap.mul' R B ∘ₗ TensorProduct.map LinearMap.id S) LinearMap.id
      ((TensorProduct.assoc R B B B).symm
        (TensorProduct.map LinearMap.id Coalgebra.comul (Coalgebra.comul c))) =
      (1 : B) ⊗ₜ[R] c := by
  change TensorProduct.map
    (LinearMap.mul' R B ∘ₗ TensorProduct.map LinearMap.id S) LinearMap.id
    ((TensorProduct.assoc R B B B).symm
      (Coalgebra.comul.lTensor B (Coalgebra.comul c))) = _
  rw [Coalgebra.coassoc_symm_apply]
  change TensorProduct.map
    (LinearMap.mul' R B ∘ₗ TensorProduct.map LinearMap.id S) LinearMap.id
      (TensorProduct.map Coalgebra.comul LinearMap.id (Coalgebra.comul c)) = _
  rw [TensorProduct.map_map, LinearMap.id_comp]
  have h : (LinearMap.mul' R B ∘ₗ TensorProduct.map LinearMap.id S) ∘ₗ
      Coalgebra.comul = Algebra.linearMap R B ∘ₗ Coalgebra.counit :=
    mul_antipode_lTensor_comul
  rw [h]
  calc
    TensorProduct.map (Algebra.linearMap R B ∘ₗ Coalgebra.counit) LinearMap.id
        (Coalgebra.comul c) =
      TensorProduct.map (Algebra.linearMap R B) LinearMap.id
        (Coalgebra.counit.rTensor B (Coalgebra.comul c)) := by
          rw [LinearMap.rTensor_def, TensorProduct.map_map, LinearMap.id_comp]
    _ = _ := by rw [Coalgebra.rTensor_counit_comul]; simp

private theorem forwardMap_inverseSeed (c : B) :
    forwardMap R A B counit_comp map_comp_comul (inverseSeed R A B c) =
      (1 : B) ⊗ₜ[R] quotientMap R A B c := by
  let F : B ⊗[R] V →ₗ[R] V :=
    TensorProduct.lift ((Algebra.lsmul R R V).toLinearMap ∘ₗ S)
  let D : B ⊗[R] (B ⊗[R] B) →ₗ[R] V :=
    TensorProduct.map LinearMap.id (quotientMap R A B) ∘ₗ
      TensorProduct.map
        (LinearMap.mul' R B ∘ₗ TensorProduct.map S LinearMap.id) LinearMap.id ∘ₗ
          (TensorProduct.assoc R B B B).symm.toLinearMap
  have hF (x : B) (v : V) : F (x ⊗ₜ[R] v) = S x • v := rfl
  have hDt (x y z : B) : D (x ⊗ₜ[R] (y ⊗ₜ[R] z)) =
      (S x * y) ⊗ₜ[R] quotientMap R A B z := rfl
  have hD : F ∘ₗ TensorProduct.map LinearMap.id
      (TensorProduct.map LinearMap.id (quotientMap R A B)) = D := by
    apply TensorProduct.ext_threefold'
    intro x y z
    simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
      hF, hDt, TensorProduct.smul_tmul', smul_eq_mul]
  have hseed (x : B) :
      forwardMap R A B counit_comp map_comp_comul (inverseSeed R A B x) =
        F (TensorProduct.map LinearMap.id (forwardSeed R A B) (Coalgebra.comul x)) := by
    rw [inverseSeed_repr R A B x (Coalgebra.Repr.arbitrary R x),
      ← (Coalgebra.Repr.arbitrary R x).eq]
    simp only [map_sum, TensorProduct.map_tmul, LinearMap.id_apply,
      forwardMap_tmul, hF]
  rw [hseed c]
  have hg : TensorProduct.map (LinearMap.id : B →ₗ[R] B) (forwardSeed R A B) =
      TensorProduct.map LinearMap.id (TensorProduct.map LinearMap.id (quotientMap R A B)) ∘ₗ
        TensorProduct.map LinearMap.id Coalgebra.comul := by
    rw [← TensorProduct.map_comp, LinearMap.id_comp]
    rfl
  rw [hg]
  change (F ∘ₗ TensorProduct.map LinearMap.id
      (TensorProduct.map LinearMap.id (quotientMap R A B)))
        (TensorProduct.map LinearMap.id Coalgebra.comul (Coalgebra.comul c)) = _
  rw [hD]
  change TensorProduct.map LinearMap.id (quotientMap R A B)
    (TensorProduct.map
      (LinearMap.mul' R B ∘ₗ TensorProduct.map S LinearMap.id) LinearMap.id
      ((TensorProduct.assoc R B B B).symm
        (TensorProduct.map LinearMap.id Coalgebra.comul (Coalgebra.comul c)))) = _
  rw [contract_antipode_left R B c]
  simp only [TensorProduct.map_tmul, LinearMap.id_apply]

private theorem inverseMap_forwardSeed (c : B) :
    inverseMap R A B counit_comp map_comp_comul (forwardSeed R A B c) =
      (1 : B) ⊗ₜ[A] c := by
  let p : B ⊗[R] B →ₗ[R] U := TensorProduct.mapOfCompatibleSMul A R R B B
  let F : B ⊗[R] U →ₗ[R] U :=
    TensorProduct.lift (Algebra.lsmul R R U).toLinearMap
  let D : B ⊗[R] (B ⊗[R] B) →ₗ[R] U :=
    p ∘ₗ TensorProduct.map
      (LinearMap.mul' R B ∘ₗ TensorProduct.map LinearMap.id S) LinearMap.id ∘ₗ
        (TensorProduct.assoc R B B B).symm.toLinearMap
  have hF (x : B) (v : U) : F (x ⊗ₜ[R] v) = x • v := rfl
  have hD : F ∘ₗ TensorProduct.map LinearMap.id
      (p ∘ₗ TensorProduct.map S LinearMap.id) = D := by
    apply TensorProduct.ext_threefold'
    intro x y z
    simp [F, D, p, TensorProduct.smul_tmul', smul_eq_mul]
  have hh : inverseSeed R A B = p ∘ₗ TensorProduct.map S LinearMap.id ∘ₗ
      Coalgebra.comul := by
    apply LinearMap.ext; intro x
    rw [inverseSeed_repr R A B x (Coalgebra.Repr.arbitrary R x)]
    simp [p, LinearMap.comp_apply,
      ← (Coalgebra.Repr.arbitrary R x).eq, map_sum]
  have hseed (x : B) :
      inverseMap R A B counit_comp map_comp_comul (forwardSeed R A B x) =
        F (TensorProduct.map LinearMap.id (inverseSeed R A B) (Coalgebra.comul x)) := by
    rw [forwardSeed_repr R A B x (Coalgebra.Repr.arbitrary R x),
      ← (Coalgebra.Repr.arbitrary R x).eq]
    simp only [map_sum, TensorProduct.map_tmul, LinearMap.id_apply,
      inverseMap_tmul, quotientMap_apply, inverseQuotient_mk, hF]
  rw [hseed c, hh]
  have hm : TensorProduct.map (LinearMap.id : B →ₗ[R] B)
      (p ∘ₗ TensorProduct.map S LinearMap.id ∘ₗ Coalgebra.comul) =
      TensorProduct.map LinearMap.id (p ∘ₗ TensorProduct.map S LinearMap.id) ∘ₗ
        TensorProduct.map LinearMap.id Coalgebra.comul := by
    rw [← TensorProduct.map_comp, LinearMap.id_comp]
    rfl
  rw [hm]
  change (F ∘ₗ TensorProduct.map LinearMap.id (p ∘ₗ TensorProduct.map S LinearMap.id))
    (TensorProduct.map LinearMap.id Coalgebra.comul (Coalgebra.comul c)) = _
  rw [hD]
  change p (TensorProduct.map
    (LinearMap.mul' R B ∘ₗ TensorProduct.map LinearMap.id S) LinearMap.id
    ((TensorProduct.assoc R B B B).symm
      (TensorProduct.map LinearMap.id Coalgebra.comul (Coalgebra.comul c)))) = _
  rw [contract_antipode_right R B c]
  simp [p]

/-- The left `B`-linear tensor–quotient equivalence given by comultiplication on
the second factor. Its inverse uses the antipode of `B`; `A` need only be a bialgebra.
The quotient is the module quotient by the left ideal extended from the counit kernel. -/
def tensorQuotientEquiv : U ≃ₗ[B] V :=
  LinearEquiv.ofLinearMap
    (forwardMap R A B counit_comp map_comp_comul)
    (inverseMap R A B counit_comp map_comp_comul)
    (by
      apply TensorProduct.AlgebraTensorModule.ext
      intro b z
      induction z using Submodule.Quotient.induction_on with
      | _ c =>
        simp only [LinearMap.comp_apply, inverseMap_tmul, inverseQuotient_mk,
          map_smul, forwardMap_inverseSeed, TensorProduct.smul_tmul', smul_eq_mul,
          mul_one, LinearMap.id_apply, quotientMap_apply])
    (by
      apply TensorProduct.AlgebraTensorModule.ext
      intro b c
      simp only [LinearMap.comp_apply, forwardMap_tmul, map_smul,
        inverseMap_forwardSeed, TensorProduct.smul_tmul', smul_eq_mul,
        mul_one, LinearMap.id_apply])

/-- The tensor–quotient equivalence on pure tensors, for any finite representation
of the comultiplication of the second factor. -/
theorem tensorQuotientEquiv_tmul {ι : Type uι} (b c : B) (r : Coalgebra.Repr R c ι) :
    tensorQuotientEquiv R A B counit_comp map_comp_comul (b ⊗ₜ[A] c) =
      ∑ k ∈ r.index, (b * r.left k) ⊗ₜ[R] Submodule.Quotient.mk (r.right k) := by
  change forwardMap R A B counit_comp map_comp_comul (b ⊗ₜ[A] c) = _
  rw [forwardMap_tmul, forwardSeed_repr R A B c r]
  simp only [Finset.smul_sum, TensorProduct.smul_tmul', smul_eq_mul, quotientMap_apply]

/-- The inverse tensor–quotient equivalence on quotient representatives, for any
finite representation of their comultiplication. -/
theorem tensorQuotientEquiv_symm_tmul {ι : Type uι} (b c : B) (r : Coalgebra.Repr R c ι) :
    (tensorQuotientEquiv R A B counit_comp map_comp_comul).symm
      (b ⊗ₜ[R] Submodule.Quotient.mk c) =
      ∑ k ∈ r.index, (b * antipode R (r.left k)) ⊗ₜ[A] r.right k := by
  change inverseMap R A B counit_comp map_comp_comul
    (b ⊗ₜ[R] Submodule.Quotient.mk c) = _
  rw [inverseMap_tmul, inverseQuotient_mk, inverseSeed_repr R A B c r]
  simp only [Finset.smul_sum, TensorProduct.smul_tmul', smul_eq_mul]

/-- The tensor–quotient equivalence fixes tensors whose second factor is one. -/
@[simp] theorem tensorQuotientEquiv_tmul_one (b : B) :
    tensorQuotientEquiv R A B counit_comp map_comp_comul (b ⊗ₜ[A] (1 : B)) =
      b ⊗ₜ[R] (Submodule.Quotient.mk (1 : B)) := by
  change b • forwardSeed R A B 1 = _
  have h : forwardSeed R A B 1 = (1 : B) ⊗ₜ[R] quotientMap R A B 1 := by
    change TensorProduct.map LinearMap.id (quotientMap R A B) (Coalgebra.comul 1) = _
    simp only [Bialgebra.comul_one, Algebra.TensorProduct.one_def,
      TensorProduct.map_tmul, LinearMap.id_apply]
  rw [h, TensorProduct.smul_tmul', smul_eq_mul, mul_one, quotientMap_apply]

/-- The inverse equivalence fixes tensors whose quotient representative is one. -/
@[simp] theorem tensorQuotientEquiv_symm_tmul_one (b : B) :
    (tensorQuotientEquiv R A B counit_comp map_comp_comul).symm
      (b ⊗ₜ[R] Submodule.Quotient.mk (1 : B)) = b ⊗ₜ[A] (1 : B) := by
  rw [← tensorQuotientEquiv_tmul_one R A B counit_comp map_comp_comul]
  exact (tensorQuotientEquiv R A B counit_comp map_comp_comul).symm_apply_apply _

/-- For a group-like element, multiplication in the first coordinate is undone
by the inverse tensor–quotient equivalence. This gives the coordinate conversion
`(b c, [c]) ↦ (b, c)` without commutativity of `B`. -/
theorem tensorQuotientEquiv_symm_mul_tmul_of_isGroupLikeElem (b c : B)
    (hc : IsGroupLikeElem R c) :
    (tensorQuotientEquiv R A B counit_comp map_comp_comul).symm
      ((b * c) ⊗ₜ[R] Submodule.Quotient.mk c) = b ⊗ₜ[A] c := by
  let r : Coalgebra.Repr R c Unit :=
    { index := {()}
      left := fun _ => c
      right := fun _ => c
      eq := by simpa using hc.comul_eq_tmul_self.symm }
  have h := tensorQuotientEquiv_tmul R A B counit_comp map_comp_comul b c r
  simp only [r, Finset.sum_singleton] at h
  rw [← h]
  exact (tensorQuotientEquiv R A B counit_comp map_comp_comul).symm_apply_apply _

end HopfAlgebra

namespace HopfAlgebra

variable (R : Type uR) (A : Type uA) (B : Type uB)
variable [CommRing R] [CommRing A] [Bialgebra R A]
variable [CommRing B] [HopfAlgebra R B] [Algebra A B] [IsScalarTower R A B]
variable
  (counit_comp :
    (Bialgebra.counitAlgHom R B).comp (IsScalarTower.toAlgHom R A B) =
      Bialgebra.counitAlgHom R A)
  (map_comp_comul :
    (Algebra.TensorProduct.map
      (IsScalarTower.toAlgHom R A B)
      (IsScalarTower.toAlgHom R A B)).comp (Bialgebra.comulAlgHom R A) =
        (Bialgebra.comulAlgHom R B).comp (IsScalarTower.toAlgHom R A B))

local notation "J" =>
  Ideal.map (algebraMap A B) (RingHom.ker (Bialgebra.counitAlgHom R A : A →+* R))
local notation "Q" => B ⧸ J
local notation "U" => B ⊗[A] B

private theorem tensorQuotientEquiv_map_one :
    tensorQuotientEquiv R A B counit_comp map_comp_comul 1 = 1 := by
  change tensorQuotientEquiv R A B counit_comp map_comp_comul
    ((1 : B) ⊗ₜ[A] (1 : B)) = (1 : B) ⊗ₜ[R] (1 : Q)
  exact tensorQuotientEquiv_tmul_one R A B counit_comp map_comp_comul 1

private theorem tensorQuotientEquiv_map_mul (x y : U) :
    tensorQuotientEquiv R A B counit_comp map_comp_comul (x * y) =
      tensorQuotientEquiv R A B counit_comp map_comp_comul x *
        tensorQuotientEquiv R A B counit_comp map_comp_comul y := by
  classical
  refine LinearMap.map_mul_of_map_mul_tmul
    (f := (tensorQuotientEquiv R A B counit_comp map_comp_comul).toLinearMap) ?_ x y
  intro b d c e
  simp only [LinearEquiv.coe_toLinearMap]
  let r := Coalgebra.Repr.arbitrary R c
  let t := Coalgebra.Repr.arbitrary R e
  have hq (v w : B) :
      (Submodule.Quotient.mk (v * w) : Q) =
        (Submodule.Quotient.mk v : Q) * Submodule.Quotient.mk w :=
    (Ideal.Quotient.mk J).map_mul v w
  rw [tensorQuotientEquiv_tmul R A B counit_comp map_comp_comul _ _ (r.mul t),
    tensorQuotientEquiv_tmul R A B counit_comp map_comp_comul _ _ r,
    tensorQuotientEquiv_tmul R A B counit_comp map_comp_comul _ _ t]
  simp only [Coalgebra.Repr.mul_index, Coalgebra.Repr.mul_left,
    Coalgebra.Repr.mul_right, Finset.sum_product, Finset.sum_mul, Finset.mul_sum,
    Algebra.TensorProduct.tmul_mul_tmul, hq]
  -- Align the two finite summations with the product representation.
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_mul_mul_comm b d (r.left k) (t.left l)]

/-- The `B`-algebra tensor–quotient equivalence induced by comultiplication on the
second factor. Its underlying `B`-linear equivalence is `tensorQuotientEquiv`. -/
def tensorQuotientAlgEquiv :
    (B ⊗[A] B) ≃ₐ[B]
      (B ⊗[R] (B ⧸
        ((RingHom.ker ((Bialgebra.counitAlgHom R A).toRingHom)).map
          (algebraMap A B)))) :=
  AlgEquiv.ofLinearEquiv
    (tensorQuotientEquiv R A B counit_comp map_comp_comul)
    (tensorQuotientEquiv_map_one R A B counit_comp map_comp_comul)
    (tensorQuotientEquiv_map_mul R A B counit_comp map_comp_comul)

/-- Forgetting multiplication recovers the `B`-linear tensor–quotient equivalence. -/
@[simp] theorem tensorQuotientAlgEquiv_toLinearEquiv :
    (tensorQuotientAlgEquiv R A B counit_comp map_comp_comul).toLinearEquiv =
      tensorQuotientEquiv R A B counit_comp map_comp_comul :=
  AlgEquiv.toLinearEquiv_ofLinearEquiv _ _ _

end HopfAlgebra
