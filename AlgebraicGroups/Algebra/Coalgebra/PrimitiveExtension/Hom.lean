/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.PrimitiveExtension
public import AlgebraicGroups.Algebra.Coalgebra.SkewPrimitive

/-!
# Maps from primitive-extension coalgebras

Maps preserving the distinguished group-like element correspond to linear maps
into the existing zero-counital skew-primitive submodule. This equivalence is
natural in the module and in the target coalgebra. Functoriality on linear maps
has the same underlying linear map as the stronger stock algebra-map functor.
No compatibility with multiplication is asserted.
-/

@[expose] public section

noncomputable section

universe u v w x

open scoped TensorProduct
open Coalgebra CoalgebraStruct


namespace TrivSqZeroExt

/-- The stock product map retains the given linear map on the split summand. -/
@[simp] theorem sndHom_comp_prodMap_comp_inrHom
    {R : Type u} {M : Type v} {N : Type w} [Semiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    (f : M →ₗ[R] N) :
    (sndHom R N).comp
      ((LinearMap.prodMap (LinearMap.id : R →ₗ[R] R) f).comp (inrHom R M)) = f := by
  change (LinearMap.snd R R N).comp
    ((LinearMap.prodMap (LinearMap.id : R →ₗ[R] R) f).comp (LinearMap.inr R R M)) = f
  rw [← LinearMap.comp_assoc, LinearMap.prodMap, LinearMap.snd_prod,
    LinearMap.comp_assoc, LinearMap.snd_comp_inr, LinearMap.comp_id]

variable {R : Type u} {M : Type v}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]

section Lift

variable {D : Type w} [AddCommMonoid D] [Module R D] [Coalgebra R D]
variable (c : GroupLike R D)
variable (φ : M →ₗ[R] Coalgebra.skewPrimitive R c.val c.val)

private def liftLinearMap : TrivSqZeroExt R M →ₗ[R] D :=
  LinearMap.coprod (LinearMap.toSpanSingleton R D c.val)
    ((Coalgebra.skewPrimitive R c.val c.val).subtype.comp φ)

private theorem liftLinearMap_apply (x : TrivSqZeroExt R M) :
    liftLinearMap c φ x = x.fst • c.val + (φ x.snd : D) := rfl

@[simp] private theorem liftLinearMap_inl (r : R) :
    liftLinearMap c φ (inl r) = r • c.val := by
  simp [liftLinearMap_apply]

@[simp] private theorem liftLinearMap_inr (m : M) :
    liftLinearMap c φ (inr m) = (φ m : D) := by
  simp [liftLinearMap_apply]

/-- The coalgebra map extending a linear map to zero-counital primitives,
with the prescribed image of the distinguished group-like element. -/
def liftCoalgHom : TrivSqZeroExt R M →ₗc[R] D where
  toLinearMap := LinearMap.coprod (LinearMap.toSpanSingleton R D c.val)
    ((Coalgebra.skewPrimitive R c.val c.val).subtype.comp φ)
  counit_comp := by
    apply linearMap_ext
    · intro r
      change counit (R := R) (liftLinearMap c φ (inl r)) = r
      rw [liftLinearMap_inl, map_smul, c.isGroupLikeElem_val.counit_eq_one]
      simp
    · intro m
      change counit (R := R) (liftLinearMap c φ (inr m)) = 0
      rw [liftLinearMap_inr]
      exact (φ m).property.counit_eq_zero
  map_comp_comul := by
    change (TensorProduct.map (liftLinearMap c φ) (liftLinearMap c φ)).comp comul =
      comul.comp (liftLinearMap c φ)
    apply linearMap_ext
    · intro r
      simp only [LinearMap.comp_apply, comul_inl, map_smul,
        TensorProduct.map_tmul, liftLinearMap_inl, one_smul,
        c.isGroupLikeElem_val.comul_eq_tmul_self]
    · intro m
      simp only [LinearMap.comp_apply, comul_inr, map_add,
        TensorProduct.map_tmul, liftLinearMap_inl, liftLinearMap_inr, one_smul]
      exact (φ m).property.comul_eq_tmul_add_tmul.symm

/-- The characteristic formula for the primitive extension. -/
theorem liftCoalgHom_apply (x : TrivSqZeroExt R M) :
    liftCoalgHom c φ x = x.fst • c.val + (φ x.snd : D) := rfl

@[simp] theorem liftCoalgHom_inl (r : R) :
    liftCoalgHom c φ (inl r) = r • c.val := liftLinearMap_inl c φ r

theorem liftCoalgHom_inl_one : liftCoalgHom c φ (inl 1) = c.val := by
  simp only [liftCoalgHom_inl, one_smul]

/-- The lift takes the distinguished point, in simp normal form, to `c`. -/
@[simp] theorem liftCoalgHom_one : liftCoalgHom c φ 1 = c.val := by
  simpa only [inl_one] using liftCoalgHom_inl_one c φ

@[simp] theorem liftCoalgHom_inr (m : M) :
    liftCoalgHom c φ (inr m) = (φ m : D) := liftLinearMap_inr c φ m

/-- The lift reuses the stock product-linear copairing. -/
@[simp] theorem coe_liftCoalgHom :
    (liftCoalgHom c φ : TrivSqZeroExt R M →ₗ[R] D) =
      LinearMap.coprod (LinearMap.toSpanSingleton R D c.val)
        ((Coalgebra.skewPrimitive R c.val c.val).subtype.comp φ) := rfl

/-- The underlying linear map of the lift is the stock copairing. -/
theorem liftCoalgHom_toLinearMap :
    (liftCoalgHom c φ).toLinearMap =
      LinearMap.coprod (LinearMap.toSpanSingleton R D c.val)
        ((Coalgebra.skewPrimitive R c.val c.val).subtype.comp φ) := rfl

/-- Uniqueness of the coalgebra extension from its distinguished point and
its prescribed values on the primitive summand. -/
theorem liftCoalgHom_unique (F : TrivSqZeroExt R M →ₗc[R] D)
    (hg : F 1 = c.val) (hj : ∀ m, F (inr m) = (φ m : D)) :
    F = liftCoalgHom c φ := by
  apply hom_ext
  · simpa only [inl_one, liftCoalgHom_one] using hg
  · intro m
    simpa only [liftCoalgHom_inr] using hj m

/-- Restrict a pointed coalgebra map to the existing primitive submodule. -/
def restrictCoalgHom (F : TrivSqZeroExt R M →ₗc[R] D)
    (hg : F 1 = c.val) : M →ₗ[R] Coalgebra.skewPrimitive R c.val c.val :=
  LinearMap.codRestrict _ ((F : TrivSqZeroExt R M →ₗ[R] D).comp (inrHom R M)) (fun m => by
    change Coalgebra.IsSkewPrimitiveElem R c.val c.val (F (inr m))
    rw [← hg]
    exact (isSkewPrimitiveElem_inr (R := R) m).map F)

@[simp] theorem restrictCoalgHom_apply (F : TrivSqZeroExt R M →ₗc[R] D)
    (hg : F 1 = c.val) (m : M) :
    (restrictCoalgHom c F hg m : D) = F (inr m) := rfl

/-- The ambient restriction is precisely composition with the stock inclusion. -/
@[simp] theorem subtype_comp_restrictCoalgHom (F : TrivSqZeroExt R M →ₗc[R] D)
    (hg : F 1 = c.val) :
    (Coalgebra.skewPrimitive R c.val c.val).subtype.comp (restrictCoalgHom c F hg) =
      (F : TrivSqZeroExt R M →ₗ[R] D).comp (inrHom R M) := rfl

/-- Pointed coalgebra maps from the primitive extension correspond to linear
maps into the zero-counital primitive submodule. No injectivity is imposed. -/
def liftCoalgHomEquiv :
    {F : TrivSqZeroExt R M →ₗc[R] D // F 1 = c.val} ≃
      (M →ₗ[R] Coalgebra.skewPrimitive R c.val c.val) where
  toFun F := restrictCoalgHom c F.val F.property
  invFun φ := ⟨liftCoalgHom c φ, liftCoalgHom_one c φ⟩
  left_inv F := by
    apply Subtype.ext
    apply hom_ext
    · change liftCoalgHom c _ 1 = F.val 1
      rw [liftCoalgHom_one]
      exact F.property.symm
    · intro m
      change liftCoalgHom c _ (inr m) = F.val (inr m)
      exact liftCoalgHom_inr c _ m
  right_inv φ := by
    apply LinearMap.ext
    intro m
    apply Subtype.ext
    change liftCoalgHom c φ (inr m) = (φ m : D)
    exact liftCoalgHom_inr c φ m

@[simp] theorem liftCoalgHomEquiv_apply
    (F : {F : TrivSqZeroExt R M →ₗc[R] D // F 1 = c.val}) (m : M) :
    (liftCoalgHomEquiv c F m : D) = F.val (inr m) := rfl

@[simp] theorem liftCoalgHomEquiv_symm_val :
    ((liftCoalgHomEquiv c).symm φ).val = liftCoalgHom c φ := rfl

/-- The inverse universal map has the characteristic linear formula. -/
theorem liftCoalgHomEquiv_symm_apply (x : TrivSqZeroExt R M) :
    ((liftCoalgHomEquiv c).symm φ).val x =
      x.fst • c.val + (φ x.snd : D) := rfl

@[simp] theorem lift_restrictCoalgHom (F : TrivSqZeroExt R M →ₗc[R] D)
    (hg : F 1 = c.val) :
    liftCoalgHom c (restrictCoalgHom c F hg) = F := by
  exact congrArg Subtype.val ((liftCoalgHomEquiv c).symm_apply_apply ⟨F, hg⟩)

@[simp] theorem restrict_liftCoalgHom :
    restrictCoalgHom c (liftCoalgHom c φ) (liftCoalgHom_inl_one c φ) = φ :=
  (liftCoalgHomEquiv c).apply_symm_apply φ

end Lift

/-- The primitive summand, bundled using Mathlib's existing submodule. -/
def inrPrimitive :
    M →ₗ[R] Coalgebra.skewPrimitive R (1 : TrivSqZeroExt R M) 1 :=
  LinearMap.codRestrict _ (inrHom R M) (isSkewPrimitiveElem_inr (R := R))

@[simp] theorem inrPrimitive_apply (m : M) :
    (inrPrimitive (R := R) m : TrivSqZeroExt R M) = inr m := rfl

section Map

variable {N : Type w} {P : Type x}
variable [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P]

/-- A linear map induces a coalgebra map, without opposite-module hypotheses. -/
def mapCoalgHom (f : M →ₗ[R] N) : TrivSqZeroExt R M →ₗc[R] TrivSqZeroExt R N :=
  liftCoalgHom (⟨1, isGroupLikeElem_inl_one⟩ : GroupLike R (TrivSqZeroExt R N))
    ((inrPrimitive (R := R) (M := N)).comp f)

/-- The map fixes the scalar summand and applies `f` to the primitive summand. -/
theorem mapCoalgHom_apply (f : M →ₗ[R] N) (x : TrivSqZeroExt R M) :
    mapCoalgHom f x = inl x.fst + inr (f x.snd) := by
  calc
    mapCoalgHom f x = x.fst • (inl 1 : TrivSqZeroExt R N) + inr (f x.snd) :=
      liftCoalgHom_apply
        (⟨1, isGroupLikeElem_inl_one⟩ : GroupLike R (TrivSqZeroExt R N))
        ((inrPrimitive (R := R) (M := N)).comp f) x
    _ = inl x.fst + inr (f x.snd) := by
      have hr : x.fst • (inl 1 : TrivSqZeroExt R N) = inl x.fst := by
        simp
      rw [hr]

@[simp] theorem mapCoalgHom_fst (f : M →ₗ[R] N) (x : TrivSqZeroExt R M) :
    (mapCoalgHom f x).fst = x.fst := by simp [mapCoalgHom_apply]

@[simp] theorem mapCoalgHom_snd (f : M →ₗ[R] N) (x : TrivSqZeroExt R M) :
    (mapCoalgHom f x).snd = f x.snd := by simp [mapCoalgHom_apply]

@[simp] theorem mapCoalgHom_inl (f : M →ₗ[R] N) (r : R) :
    mapCoalgHom f (inl r) = inl r := by simp [mapCoalgHom_apply]

@[simp] theorem mapCoalgHom_inr (f : M →ₗ[R] N) (m : M) :
    mapCoalgHom f (inr m) = inr (f m) := by simp [mapCoalgHom_apply]

theorem mapCoalgHom_inl_one (f : M →ₗ[R] N) :
    mapCoalgHom f (inl 1) = inl 1 := mapCoalgHom_inl f 1

/-- Functoriality fixes the distinguished point in simp normal form. -/
@[simp] theorem mapCoalgHom_one (f : M →ₗ[R] N) :
    mapCoalgHom f 1 = 1 := by
  simpa only [inl_one] using mapCoalgHom_inl_one f

/-- The stock product linear map is the underlying map of functoriality. -/
@[simp] theorem coe_mapCoalgHom (f : M →ₗ[R] N) :
    (mapCoalgHom f : TrivSqZeroExt R M →ₗ[R] TrivSqZeroExt R N) =
      LinearMap.prodMap LinearMap.id f := by
  apply LinearMap.ext
  intro x
  apply TrivSqZeroExt.ext
  · change (mapCoalgHom f x).fst = x.fst
    exact mapCoalgHom_fst f x
  · change (mapCoalgHom f x).snd = f x.snd
    exact mapCoalgHom_snd f x

/-- The underlying linear map of functoriality is the stock product map. -/
theorem mapCoalgHom_toLinearMap (f : M →ₗ[R] N) :
    (mapCoalgHom f).toLinearMap = LinearMap.prodMap LinearMap.id f :=
  coe_mapCoalgHom f

@[simp] theorem mapCoalgHom_id :
    mapCoalgHom (LinearMap.id : M →ₗ[R] M) = CoalgHom.id R _ := by
  apply hom_ext
  · simp
  · intro m
    simp

/-- Functoriality is covariant on the primitive summand. -/
theorem mapCoalgHom_comp (f : M →ₗ[R] N) (h : N →ₗ[R] P) :
    mapCoalgHom (h.comp f) = (mapCoalgHom h).comp (mapCoalgHom f) := by
  apply hom_ext
  · simp
  · intro m
    simp

/-- Functoriality retains the entire given linear map on the split summand. -/
theorem sndHom_comp_mapCoalgHom_comp_inrHom (f : M →ₗ[R] N) :
    (sndHom R N).comp ((mapCoalgHom f).toLinearMap.comp (inrHom R M)) = f := by
  exact (congrArg
    (fun L : TrivSqZeroExt R M →ₗ[R] TrivSqZeroExt R N =>
      (sndHom R N).comp (L.comp (inrHom R M)))
    (mapCoalgHom_toLinearMap f)).trans (sndHom_comp_prodMap_comp_inrHom f)

section StockBridge

variable [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
variable [Module Rᵐᵒᵖ N] [IsCentralScalar R N]

/-- At the stronger stock scope, both functors have the same underlying
linear map. This does not assert a bialgebra structure or an algebraic UP. -/
theorem mapCoalgHom_toLinearMap_eq_map (f : M →ₗ[R] N) :
    (mapCoalgHom f).toLinearMap = (TrivSqZeroExt.map f).toLinearMap := by
  apply linearMap_ext
  · intro r
    exact (mapCoalgHom_inl f r).trans (map_inl f r).symm
  · intro m
    exact (mapCoalgHom_inr f m).trans (map_inr f m).symm

end StockBridge
end Map

section SourceNaturality

variable {N : Type w} [AddCommMonoid N] [Module R N]
variable {D : Type x} [AddCommMonoid D] [Module R D] [Coalgebra R D]
variable (c : GroupLike R D) (f : M →ₗ[R] N)

/-- Lifting commutes with precomposition on the source module. -/
theorem liftCoalgHom_comp_mapCoalgHom
    (φ : N →ₗ[R] Coalgebra.skewPrimitive R c.val c.val) :
    (liftCoalgHom c φ).comp (mapCoalgHom f) = liftCoalgHom c (φ.comp f) := by
  apply hom_ext
  · simp
  · intro m
    simp

/-- Restriction, the forward universal map, is natural in the source. -/
theorem restrictCoalgHom_comp_mapCoalgHom (F : TrivSqZeroExt R N →ₗc[R] D)
    (hg : F 1 = c.val) :
    restrictCoalgHom c (F.comp (mapCoalgHom f))
        (by
          change F (mapCoalgHom f 1) = c.val
          rw [mapCoalgHom_one]
          exact hg) =
      (restrictCoalgHom c F hg).comp f := by
  apply LinearMap.ext
  intro m
  apply Subtype.ext
  change F (mapCoalgHom f (inr m)) = F (inr (f m))
  rw [mapCoalgHom_inr]

/-- Source naturality of the forward universal equivalence. -/
theorem liftCoalgHomEquiv_natural_left
    (F : {F : TrivSqZeroExt R N →ₗc[R] D // F 1 = c.val}) :
    liftCoalgHomEquiv c
        ⟨F.val.comp (mapCoalgHom f), by
          change F.val (mapCoalgHom f 1) = c.val
          rw [mapCoalgHom_one]
          exact F.property⟩ =
      (liftCoalgHomEquiv c F).comp f := by
  apply LinearMap.ext
  intro m
  apply Subtype.ext
  change F.val (mapCoalgHom f (inr m)) = F.val (inr (f m))
  rw [mapCoalgHom_inr]

/-- Source naturality of the inverse universal equivalence. -/
theorem liftCoalgHomEquiv_symm_natural_left
    (φ : N →ₗ[R] Coalgebra.skewPrimitive R c.val c.val) :
    (⟨((liftCoalgHomEquiv c).symm φ).val.comp (mapCoalgHom f),
        by
          change liftCoalgHom c φ (mapCoalgHom f 1) = c.val
          rw [mapCoalgHom_one, liftCoalgHom_one]⟩ :
        {F : TrivSqZeroExt R M →ₗc[R] D // F 1 = c.val}) =
      (liftCoalgHomEquiv c).symm (φ.comp f) := by
  apply Subtype.ext
  exact liftCoalgHom_comp_mapCoalgHom c f φ

end SourceNaturality

section TargetNaturality

variable {D : Type w} {E : Type x}
variable [AddCommMonoid D] [Module R D] [Coalgebra R D]
variable [AddCommMonoid E] [Module R E] [Coalgebra R E]
variable (c : GroupLike R D) (H : D →ₗc[R] E)

/-- Lifting commutes with postcomposition in the target coalgebra. -/
theorem comp_liftCoalgHom (φ : M →ₗ[R] Coalgebra.skewPrimitive R c.val c.val) :
    H.comp (liftCoalgHom c φ) = liftCoalgHom (GroupLike.map H c)
      ((Coalgebra.skewPrimitiveMap H c.val c.val).comp φ) := by
  apply hom_ext
  · exact (congrArg H (liftCoalgHom_inl_one c φ)).trans
      (liftCoalgHom_inl_one (GroupLike.map H c)
        ((Coalgebra.skewPrimitiveMap H c.val c.val).comp φ)).symm
  · intro m
    exact (congrArg H (liftCoalgHom_inr c φ m)).trans
      (liftCoalgHom_inr (GroupLike.map H c)
        ((Coalgebra.skewPrimitiveMap H c.val c.val).comp φ) m).symm

/-- Restriction, the forward universal map, is natural in the target. -/
theorem restrictCoalgHom_comp (F : TrivSqZeroExt R M →ₗc[R] D)
    (hg : F 1 = c.val) :
    restrictCoalgHom (GroupLike.map H c) (H.comp F)
        (by change H (F 1) = H c.val; rw [hg]) =
      (Coalgebra.skewPrimitiveMap H c.val c.val).comp (restrictCoalgHom c F hg) := by
  apply LinearMap.ext
  intro m
  apply Subtype.ext
  rfl

/-- Target naturality of the forward universal equivalence. -/
theorem liftCoalgHomEquiv_natural_right
    (F : {F : TrivSqZeroExt R M →ₗc[R] D // F 1 = c.val}) :
    liftCoalgHomEquiv (GroupLike.map H c)
        ⟨H.comp F.val, by change H (F.val 1) = H c.val; rw [F.property]⟩ =
      (Coalgebra.skewPrimitiveMap H c.val c.val).comp (liftCoalgHomEquiv c F) := by
  apply LinearMap.ext
  intro m
  apply Subtype.ext
  rfl

/-- Target naturality of the inverse universal equivalence. -/
theorem liftCoalgHomEquiv_symm_natural_right
    (φ : M →ₗ[R] Coalgebra.skewPrimitive R c.val c.val) :
    (⟨H.comp ((liftCoalgHomEquiv c).symm φ).val,
        by
          change H (liftCoalgHom c φ 1) = H c.val
          rw [liftCoalgHom_one]⟩ :
        {F : TrivSqZeroExt R M →ₗc[R] E // F 1 = (GroupLike.map H c).val}) =
      (liftCoalgHomEquiv (GroupLike.map H c)).symm
        ((Coalgebra.skewPrimitiveMap H c.val c.val).comp φ) := by
  apply Subtype.ext
  exact comp_liftCoalgHom c H φ

end TargetNaturality

end TrivSqZeroExt
