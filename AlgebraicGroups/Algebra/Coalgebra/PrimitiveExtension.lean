/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.GroupLikeHom
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.Coalgebra.Primitive
public import Mathlib.Algebra.Algebra.Epi
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The primitive-extension coalgebra

The module `TrivSqZeroExt R M` has a coalgebra structure with counit the first
projection. The element `inl 1` is group-like and each `inr m` is primitive
relative to it. This construction uses only a commutative semiring and a module;
it does not assert compatibility with the square-zero extension multiplication.

The proofs use Mathlib's product linear maps, tensor associator, and the stock
`TrivSqZeroExt` decomposition. Coaugmentation is read through
`GroupLike.coalgHomEquiv`, rather than an additional pointed structure.

Group-like elements have coordinates `(1, m)` with `m ⊗ₜ[R] m = 0`. For an epi
semiring algebra this becomes `m * m = 0`, using Mathlib's multiplication map and
`Algebra.IsEpi.injective_lift_mul`. The ideal-quotient specialization identifies
such points with representatives whose squares belong to the ideal.
-/

@[expose] public section

universe u v w

open scoped TensorProduct
open Coalgebra CoalgebraStruct

namespace TrivSqZeroExt

/-- Scalar multiplication of the distinguished point is the first-summand inclusion.
No right action on `M` is required. -/
@[simp] theorem smul_one_eq_inl {R : Type u} {M : Type v}
    [Monoid R] [AddMonoid M] [DistribMulAction R M] (r : R) :
    r • (1 : TrivSqZeroExt R M) = inl r := by
  simpa only [smul_eq_mul, mul_one, inl_one] using
    (inl_smul (M := M) r (1 : R)).symm

variable {R : Type u} {M : Type v}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]

private theorem linearMap_ext_one_inr {N : Type w} [AddCommMonoid N] [Module R N]
    {f h : TrivSqZeroExt R M →ₗ[R] N}
    (hg : f (inl 1) = h (inl 1)) (hj : ∀ m, f (inr m) = h (inr m)) : f = h := by
  apply linearMap_ext (hr := hj)
  intro r
  have hr : (inl r : TrivSqZeroExt R M) = r • inl 1 := by
    simp
  rw [hr, map_smul, map_smul, hg]

/-- The first-coordinate linear map on the primitive extension. -/
def primitiveCounit : TrivSqZeroExt R M →ₗ[R] R :=
  { LinearMap.fst R R M with toFun := fst }

/-- The linear counit is the scalar coordinate. -/
theorem primitiveCounit_apply (x : TrivSqZeroExt R M) :
    primitiveCounit x = x.fst := rfl

/-- The primitive-extension comultiplication as a linear map. -/
noncomputable def primitiveComul :
    TrivSqZeroExt R M →ₗ[R] TrivSqZeroExt R M ⊗[R] TrivSqZeroExt R M :=
  let g : TrivSqZeroExt R M := inl 1
  let p : TrivSqZeroExt R M →ₗ[R] R := primitiveCounit
  let a : TrivSqZeroExt R M →ₗ[R] TrivSqZeroExt R M ⊗[R] TrivSqZeroExt R M :=
    (LinearMap.toSpanSingleton R _ (g ⊗ₜ[R] g)).comp p
  let b : TrivSqZeroExt R M →ₗ[R] TrivSqZeroExt R M ⊗[R] TrivSqZeroExt R M :=
    ((TensorProduct.mk R _ _ g).comp (inrHom R M)).comp (sndHom R M)
  let c : TrivSqZeroExt R M →ₗ[R] TrivSqZeroExt R M ⊗[R] TrivSqZeroExt R M :=
    (((TensorProduct.mk R _ _).flip g).comp (inrHom R M)).comp (sndHom R M)
  a + b + c

/-- The primitive comultiplication is the sum of three characteristic tensors. -/
theorem primitiveComul_apply (x : TrivSqZeroExt R M) :
    primitiveComul x =
      x.fst • (inl 1 ⊗ₜ[R] inl 1) + inl 1 ⊗ₜ[R] inr x.snd +
        inr x.snd ⊗ₜ[R] inl 1 := rfl

/-- The coalgebra with a distinguished group-like `inl 1` and primitive summand `M`.
Its module structure is the existing one on `TrivSqZeroExt R M`. -/
noncomputable instance instCoalgebra : Coalgebra R (TrivSqZeroExt R M) where
  comul := primitiveComul
  counit := primitiveCounit
  coassoc := by
    apply linearMap_ext_one_inr
    · simp [LinearMap.comp_apply, primitiveComul_apply]
    · intro m
      simp [LinearMap.comp_apply, primitiveComul_apply,
        TensorProduct.add_tmul, TensorProduct.tmul_add, add_assoc]
  rTensor_counit_comp_comul := by
    apply linearMap_ext_one_inr
    · simp [LinearMap.comp_apply, primitiveComul_apply, primitiveCounit_apply]
    · intro m
      simp [LinearMap.comp_apply, primitiveComul_apply, primitiveCounit_apply]
  lTensor_counit_comp_comul := by
    apply linearMap_ext_one_inr
    · simp [LinearMap.comp_apply, primitiveComul_apply, primitiveCounit_apply]
    · intro m
      simp [LinearMap.comp_apply, primitiveComul_apply, primitiveCounit_apply]

/-- The counit is the first projection. -/
@[simp] theorem counit_apply (x : TrivSqZeroExt R M) : counit (R := R) x = x.fst := rfl

/-- The three-term comultiplication formula; expansion is deliberately not a simp rule. -/
theorem comul_apply (x : TrivSqZeroExt R M) :
    comul (R := R) x = x.fst • (inl 1 ⊗ₜ[R] inl 1) +
      inl 1 ⊗ₜ[R] inr x.snd + inr x.snd ⊗ₜ[R] inl 1 := rfl

@[simp] theorem counit_inl (r : R) :
    counit (R := R) (inl r : TrivSqZeroExt R M) = r := rfl

@[simp] theorem counit_inr (m : M) :
    counit (R := R) (inr m : TrivSqZeroExt R M) = 0 := rfl

@[simp] theorem comul_inl (r : R) :
    comul (R := R) (inl r : TrivSqZeroExt R M) = r • (inl 1 ⊗ₜ[R] inl 1) := by
  simp [comul_apply]

@[simp] theorem comul_inr (m : M) :
    comul (R := R) (inr m : TrivSqZeroExt R M) =
      inl 1 ⊗ₜ[R] inr m + inr m ⊗ₜ[R] inl 1 := by
  simp [comul_apply]

/-- The distinguished point has counit one. -/
@[simp] theorem counit_one : counit (R := R) (1 : TrivSqZeroExt R M) = 1 := rfl

/-- Comultiplication at the distinguished point, in the stock simp normal form. -/
@[simp] theorem comul_one :
    comul (R := R) (1 : TrivSqZeroExt R M) = 1 ⊗ₜ[R] 1 := by
  simpa only [inl_one, one_smul] using (comul_inl (R := R) (M := M) 1)

/-- The distinguished point of the primitive extension is group-like. -/
theorem isGroupLikeElem_inl_one : IsGroupLikeElem R (inl 1 : TrivSqZeroExt R M) where
  counit_eq_one := counit_inl 1
  comul_eq_tmul_self := by simp

/-- Every element of the second summand has zero counit and is skew primitive. -/
theorem isSkewPrimitiveElem_inr (m : M) :
    Coalgebra.IsSkewPrimitiveElem R (inl 1) (inl 1) (inr m : TrivSqZeroExt R M) where
  counit_eq_zero := counit_inr m
  comul_eq_tmul_add_tmul := comul_inr m

/-- Coalgebra maps out of the primitive extension are determined by the distinguished
point and their values on the primitive summand. -/
theorem hom_ext {D : Type w} [AddCommMonoid D] [Module R D] [Coalgebra R D]
    {F G : TrivSqZeroExt R M →ₗc[R] D}
    (hg : F (inl 1) = G (inl 1)) (hj : ∀ m, F (inr m) = G (inr m)) : F = G := by
  have h : F.toLinearMap = G.toLinearMap := linearMap_ext_one_inr hg hj
  exact CoalgHom.ext fun x => LinearMap.congr_fun h x

/-- Comultiplication of the primitive extension is invariant under tensor swap. -/
instance instIsCocomm : Coalgebra.IsCocomm R (TrivSqZeroExt R M) where
  comm_comp_comul := by
    apply linearMap_ext_one_inr
    · simp [LinearMap.comp_apply]
    · intro m
      simp [LinearMap.comp_apply, add_comm]

/-- The scalar-source coalgebra map associated to the distinguished point is `inl`. -/
theorem coalgHomEquiv_inl_one_apply (r : R) :
    GroupLike.coalgHomEquiv
      (⟨inl 1, isGroupLikeElem_inl_one⟩ : GroupLike R (TrivSqZeroExt R M)) r = inl r := by
  simp only [GroupLike.coalgHomEquiv_apply, inl_one, smul_one_eq_inl]

/-- The coaugmentation has the stock first-summand linear inclusion underneath. -/
@[simp] theorem coe_coalgHomEquiv_one :
    (GroupLike.coalgHomEquiv
      (⟨1, isGroupLikeElem_inl_one⟩ : GroupLike R (TrivSqZeroExt R M)) :
        R →ₗ[R] TrivSqZeroExt R M) = LinearMap.inl R R M := by
  apply LinearMap.ext
  intro r
  exact coalgHomEquiv_inl_one_apply r

/-- The coaugmentation has the existing first-summand linear inclusion underneath. -/
theorem coalgHomEquiv_inl_one_toLinearMap :
    (GroupLike.coalgHomEquiv
      (⟨inl 1, isGroupLikeElem_inl_one⟩ : GroupLike R (TrivSqZeroExt R M))).toLinearMap =
      LinearMap.inl R R M :=
  coe_coalgHomEquiv_one

/-- The coalgebra counit retracts the coaugmentation at the distinguished point. -/
@[simp] theorem counitCoalgHom_comp_coalgHomEquiv_one :
    (Coalgebra.counitCoalgHom R (TrivSqZeroExt R M)).comp
      (GroupLike.coalgHomEquiv
        (⟨1, isGroupLikeElem_inl_one⟩ : GroupLike R (TrivSqZeroExt R M))) =
      CoalgHom.id R R := by
  apply CoalgHom.ext
  intro r
  simp

/-- The coalgebra counit retracts the coaugmentation. -/
theorem counitCoalgHom_comp_coalgHomEquiv_inl_one :
    (Coalgebra.counitCoalgHom R (TrivSqZeroExt R M)).comp
      (GroupLike.coalgHomEquiv
        (⟨inl 1, isGroupLikeElem_inl_one⟩ : GroupLike R (TrivSqZeroExt R M))) =
      CoalgHom.id R R :=
  counitCoalgHom_comp_coalgHomEquiv_one

/-- Group-like elements are precisely the points with scalar coordinate one and
vanishing tensor square of the module coordinate. No cancellation is required. -/
theorem isGroupLikeElem_iff (x : TrivSqZeroExt R M) :
    IsGroupLikeElem R x ↔ x.fst = 1 ∧ x.snd ⊗ₜ[R] x.snd = 0 := by
  constructor
  · intro hx
    refine ⟨by simpa only [counit_apply] using hx.counit_eq_one, ?_⟩
    let p : TrivSqZeroExt R M →ₗ[R] M := sndHom R M
    have h := congrArg (TensorProduct.map p p) hx.comul_eq_tmul_self
    simpa only [p, comul_apply, map_add, map_smul, TensorProduct.map_tmul,
      sndHom_apply, snd_inl, snd_inr, TensorProduct.zero_tmul, TensorProduct.tmul_zero,
      smul_zero, zero_add] using h.symm
  · rintro ⟨hf, hm⟩
    have hj : (inr x.snd : TrivSqZeroExt R M) ⊗ₜ[R]
        (inr x.snd : TrivSqZeroExt R M) = 0 := by
      have h := congrArg (TensorProduct.map (inrHom R M) (inrHom R M)) hm
      simpa only [TensorProduct.map_tmul, inrHom_apply, map_zero] using h
    have hx : x = inl 1 + inr x.snd := by
      simpa only [hf] using (inl_fst_add_inr_snd_eq x).symm
    refine ⟨by simpa using hf, ?_⟩
    calc
      comul (R := R) x = inl 1 ⊗ₜ[R] inl 1 + inl 1 ⊗ₜ[R] inr x.snd +
          inr x.snd ⊗ₜ[R] inl 1 := by rw [comul_apply, hf, one_smul]
      _ = (inl 1 + inr x.snd) ⊗ₜ[R] (inl 1 + inr x.snd) := by
        simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, hj, add_zero]
        ac_rfl
      _ = x ⊗ₜ[R] x := by rw [← hx]

/-- For an epi semiring algebra, the tensor-square condition is ordinary square-zero.
The target algebra is not required to be commutative. -/
theorem isGroupLikeElem_iff_mul {A : Type w} [Semiring A] [Algebra R A]
    [Algebra.IsEpi R A] (x : TrivSqZeroExt R A) :
    IsGroupLikeElem R x ↔ x.fst = 1 ∧ x.snd * x.snd = 0 := by
  rw [isGroupLikeElem_iff]
  apply and_congr_right
  intro _
  constructor
  · intro h
    simpa only [LinearMap.mul'_apply, map_zero] using
      congrArg (LinearMap.mul' R A) h
  · intro h
    have hinj : Function.Injective (LinearMap.mul' R A) :=
      Algebra.IsEpi.injective_lift_mul
    apply hinj
    simpa only [LinearMap.mul'_apply, map_zero] using h

/-- A representative defines a group-like point in the primitive extension by
`S ⧸ I` exactly when its square belongs to `I`. The epi instance is local;
neither properness of `I` nor nontriviality or reducedness is needed. -/
theorem isGroupLikeElem_quotient_mk_iff {S : Type u} [CommRing S]
    (I : Ideal S) (r : S) :
    IsGroupLikeElem S
      (inl 1 + inr (Ideal.Quotient.mk I r) : TrivSqZeroExt S (S ⧸ I)) ↔ r ^ 2 ∈ I := by
  let : Algebra.IsEpi S (S ⧸ I) :=
    Algebra.isEpi_of_surjective_algebraMap S (S ⧸ I) (by
      rw [Ideal.Quotient.algebraMap_eq]
      exact Ideal.Quotient.mk_surjective)
  rw [isGroupLikeElem_iff_mul]
  simp only [fst_add, fst_inl, fst_inr, add_zero, snd_add, snd_inl, snd_inr,
    zero_add, true_and]
  rw [← pow_two, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]

end TrivSqZeroExt
