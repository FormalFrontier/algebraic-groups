/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents, Trellis
-/
module

public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Coalgebra.Equiv
public import Mathlib.RingTheory.Coalgebra.Quotient

import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.Basic

/-!
# Coideal images, joins and coalgebra morphisms on quotients

`Submodule.IsCoideal.map` shows that the ordinary linear image of a coideal
under a coalgebra-structure-preserving map is a coideal. It applies to any
`CoalgHomClass`, without injectivity or surjectivity of the map.

Binary and arbitrary submodule joins of coideals are coideals, by
`Submodule.IsCoideal.sup` and `Submodule.IsCoideal.iSup`. These are explicit proofs:
users can install them locally when constructing a quotient coalgebra. The proof
factors the projection onto the larger quotient through each smaller quotient
as an ordinary linear map, then uses composition of tensor maps. It does not
require a coalgebra structure on the larger quotient in advance.

A coalgebra homomorphism vanishing on a coideal descends uniquely through the
quotient projection by `Submodule.liftQCoalgHom`. A coalgebra homomorphism carrying
one coideal into another induces `Submodule.mapQCoalgHom` between their quotients.
The latter construction respects identity and composition.

These coideal-image, join and quotient-map constructions use Mathlib's quotient coalgebra structure and
linear quotient maps. The scalars are a commutative ring, the modules are additive
commutative groups, and the scalar, source and target universes are independent.
Preservation of counit and comultiplication requires only `CoalgebraStruct`, not
the coalgebra laws. For these constructions, no algebra structure, field
hypothesis, flatness or projectivity is required.

Over a field, `CoalgHomClass.ker_isCoideal` states that the linear kernel of any
coalgebra morphism is a coideal. Both source and target need only
`CoalgebraStruct`, in independent universes, and the morphism need not be
surjective. No finite-dimensionality assumption is made. The field hypothesis
ensures flatness of the target and of the module quotient by the kernel, as used
in tensor-square cancellation for the ordinary linear quotient lift. Flatness of
the two ambient modules alone does not suffice over a general commutative ring.

## References

- `Mathlib.RingTheory.Coalgebra.Quotient` supplies coideals, quotient structures
  and the bundled projection `Coalgebra.Quotient.mkQCoalgHom`.
- `Mathlib.RingTheory.Coalgebra.Hom` supplies bundled coalgebra homomorphisms,
  extensionality and composition.
- `Mathlib.LinearAlgebra.Quotient.Basic` supplies `Submodule.liftQ`,
  `Submodule.mapQ` and the linear quotient universal property.
- `Mathlib.LinearAlgebra.TensorProduct.Map` supplies tensor-map composition.
- The tensor-cancellation method for field kernels uses
  `TensorProduct.map_injective_of_flat_flat` from `Mathlib.RingTheory.Flat.Basic`,
  with vector-space freeness supplied by `Module.Free.of_divisionRing` from
  `Mathlib.LinearAlgebra.Basis.VectorSpace` and flatness by `Module.Flat.of_free`.
-/

@[expose] public section

universe u v w z uF

open Coalgebra

namespace Submodule

variable {R : Type u} [CommRing R]
variable {C : Type v} [AddCommGroup C] [Module R C] [CoalgebraStruct R C]
variable {D : Type w} [AddCommGroup D] [Module R D] [CoalgebraStruct R D]

/-- The ordinary linear image of a coideal under a coalgebra-structure-preserving map
is a coideal. Both endpoints need only coalgebra structures, not coalgebra laws. -/
theorem IsCoideal.map {F : Type uF} [FunLike F C D] [CoalgHomClass F R C D]
    {I : Submodule R C} (hI : I.IsCoideal) (f : F) :
    (I.map (f : C →ₗ[R] D)).IsCoideal := by
  let J := I.map (f : C →ₗ[R] D)
  -- Use the linear quotient map before a coalgebra structure on the image quotient exists.
  let g := I.mapQ J (f : C →ₗ[R] D) (Submodule.le_comap_map _ _)
  have hg : g.comp I.mkQ = J.mkQ.comp (f : C →ₗ[R] D) :=
    Submodule.mapQ_mkQ _ _ _
  constructor
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    exact (CoalgHomClass.counit_comp_apply f x).trans (hI.counit_eq_zero hx)
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    change TensorProduct.map J.mkQ J.mkQ (comul (f x)) = 0
    rw [← CoalgHomClass.map_comp_comul_apply f x, TensorProduct.map_map,
      ← hg, ← TensorProduct.map_map, hI.map_mkQ_comul_eq_zero hx, map_zero]

/-- A submodule whose image under a bijective coalgebra-structure-preserving map is a
coideal is itself a coideal. Both endpoints need only coalgebra structures. -/
theorem IsCoideal.of_map {F : Type uF} [FunLike F C D] [CoalgHomClass F R C D]
    {I : Submodule R C} (f : F) (hf : Function.Bijective f)
    (hImage : (I.map (f : C →ₗ[R] D)).IsCoideal) : I.IsCoideal := by
  let e := CoalgEquiv.ofBijective (f := (f : C →ₗc[R] D)) hf
  have hback : (I.map (f : C →ₗ[R] D)).map (e.symm : D →ₗ[R] C) = I :=
    (Submodule.map_symm_eq_iff e.toLinearEquiv).2 rfl
  exact hback ▸ hImage.map e.symm

/-- A bijective coalgebra-structure-preserving map preserves and reflects coideality. -/
theorem isCoideal_map_iff_of_bijective {F : Type uF}
    [FunLike F C D] [CoalgHomClass F R C D]
    {I : Submodule R C} (f : F) (hf : Function.Bijective f) :
    (I.map (f : C →ₗ[R] D)).IsCoideal ↔ I.IsCoideal :=
  ⟨fun hImage => IsCoideal.of_map f hf hImage, fun hI => hI.map f⟩

/-- Comultiplication of a coideal element vanishes after projecting both tensor
factors modulo any larger submodule. The larger submodule need not be a coideal. -/
theorem IsCoideal.map_mkQ_comul_eq_zero_of_le {I J : Submodule R C}
    (hI : I.IsCoideal) (hIJ : I ≤ J) {x : C} (hx : x ∈ I) :
    TensorProduct.map J.mkQ J.mkQ (comul x) = 0 := by
  let f : (C ⧸ I) →ₗ[R] (C ⧸ J) := I.liftQ J.mkQ (by rwa [ker_mkQ])
  have hf : f.comp I.mkQ = J.mkQ := I.liftQ_mkQ J.mkQ _
  calc
    TensorProduct.map J.mkQ J.mkQ (comul x) =
        TensorProduct.map f f (TensorProduct.map I.mkQ I.mkQ (comul x)) := by
      rw [TensorProduct.map_map, hf]
    _ = 0 := by rw [hI.map_mkQ_comul_eq_zero hx, map_zero]

/-- The binary submodule join of two coideals is a coideal. -/
theorem IsCoideal.sup {I J : Submodule R C} (hI : I.IsCoideal) (hJ : J.IsCoideal) :
    (I ⊔ J).IsCoideal where
  counit_eq_zero := by
    have hIker : I ≤ LinearMap.ker (counit (R := R)) :=
      fun x hx => hI.counit_eq_zero hx
    have hJker : J ≤ LinearMap.ker (counit (R := R)) :=
      fun x hx => hJ.counit_eq_zero hx
    exact fun x hx => (sup_le hIker hJker) hx
  map_mkQ_comul_eq_zero := by
    have hIker : I ≤ LinearMap.ker
        ((TensorProduct.map (I ⊔ J).mkQ (I ⊔ J).mkQ).comp (comul (R := R))) :=
      fun x hx => hI.map_mkQ_comul_eq_zero_of_le le_sup_left hx
    have hJker : J ≤ LinearMap.ker
        ((TensorProduct.map (I ⊔ J).mkQ (I ⊔ J).mkQ).comp (comul (R := R))) :=
      fun x hx => hJ.map_mkQ_comul_eq_zero_of_le le_sup_right hx
    exact fun x hx => (sup_le hIker hJker) hx

/-- An arbitrary submodule join of coideals is a coideal, including an empty join. -/
theorem IsCoideal.iSup {ι : Sort z} (I : ι → Submodule R C)
    (hI : ∀ i, (I i).IsCoideal) : (⨆ i, I i).IsCoideal where
  counit_eq_zero := by
    have hker : (⨆ i, I i) ≤ LinearMap.ker (counit (R := R)) :=
      iSup_le fun i x hx => (hI i).counit_eq_zero hx
    exact fun x hx => hker hx
  map_mkQ_comul_eq_zero := by
    have hker : (⨆ i, I i) ≤ LinearMap.ker
        ((TensorProduct.map (⨆ i, I i).mkQ (⨆ i, I i).mkQ).comp (comul (R := R))) :=
      iSup_le fun i x hx => (hI i).map_mkQ_comul_eq_zero_of_le (le_iSup I i) hx
    exact fun x hx => hker hx

/-- Descend a coalgebra homomorphism vanishing on a coideal through the quotient projection. -/
def liftQCoalgHom (I : Submodule R C) [I.IsCoideal] (f : C →ₗc[R] D)
    (h : I ≤ LinearMap.ker f.toLinearMap) : (C ⧸ I) →ₗc[R] D where
  toLinearMap := I.liftQ f.toLinearMap h
  counit_comp := by
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := I.mkQ_surjective x
    simpa only [CoalgHom.toLinearMap_eq_coe, CoalgHom.coe_toLinearMap,
      LinearMap.comp_apply, mkQ_apply, liftQ_apply,
      Coalgebra.Quotient.counit_mk] using CoalgHomClass.counit_comp_apply f y
  map_comp_comul := by
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := I.mkQ_surjective x
    simpa only [CoalgHom.toLinearMap_eq_coe, CoalgHom.coe_toLinearMap,
      LinearMap.comp_apply, mkQ_apply, Coalgebra.Quotient.comul_mk,
      TensorProduct.map_map, liftQ_mkQ, liftQ_apply] using
      CoalgHomClass.map_comp_comul_apply f y

/-- The linear map underlying the descended homomorphism is the linear quotient lift. -/
@[simp]
theorem liftQCoalgHom_toLinearMap (I : Submodule R C) [I.IsCoideal]
    (f : C →ₗc[R] D) (h : I ≤ LinearMap.ker f.toLinearMap) :
    (I.liftQCoalgHom f h).toLinearMap = I.liftQ f.toLinearMap h :=
  rfl

/-- The descended homomorphism agrees with the original homomorphism on representatives. -/
@[simp]
theorem liftQCoalgHom_mk (I : Submodule R C) [I.IsCoideal]
    (f : C →ₗc[R] D) (h : I ≤ LinearMap.ker f.toLinearMap) (x : C) :
    I.liftQCoalgHom f h (Submodule.Quotient.mk (p := I) x) = f x :=
  rfl

/-- Composing the descended homomorphism with the quotient projection recovers the original. -/
theorem liftQCoalgHom_comp_mkQCoalgHom (I : Submodule R C) [I.IsCoideal]
    (f : C →ₗc[R] D) (h : I ≤ LinearMap.ker f.toLinearMap) :
    (I.liftQCoalgHom f h).comp (Coalgebra.Quotient.mkQCoalgHom I) = f :=
  CoalgHom.ext fun x => liftQCoalgHom_mk I f h x

/-- A coalgebra homomorphism factoring the original through the quotient is its unique lift. -/
theorem liftQCoalgHom_unique (I : Submodule R C) [I.IsCoideal]
    (f : C →ₗc[R] D) (h : I ≤ LinearMap.ker f.toLinearMap)
    (g : (C ⧸ I) →ₗc[R] D) (hg : g.comp (Coalgebra.Quotient.mkQCoalgHom I) = f) :
    g = I.liftQCoalgHom f h := by
  apply CoalgHom.ext
  intro x
  obtain ⟨y, rfl⟩ := I.mkQ_surjective x
  calc
    g (I.mkQ y) = f y := CoalgHom.congr_fun hg y
    _ = I.liftQCoalgHom f h (I.mkQ y) := (liftQCoalgHom_mk I f h y).symm

/-- A coalgebra homomorphism carrying a coideal into a coideal induces a homomorphism
between the quotients. -/
def mapQCoalgHom (I : Submodule R C) (J : Submodule R D) [I.IsCoideal] [J.IsCoideal]
    (f : C →ₗc[R] D) (h : I ≤ J.comap f.toLinearMap) : (C ⧸ I) →ₗc[R] (D ⧸ J) :=
  I.liftQCoalgHom ((Coalgebra.Quotient.mkQCoalgHom J).comp f)
    (by
      have hq : (Coalgebra.Quotient.mkQCoalgHom J : D →ₗ[R] (D ⧸ J)) = J.mkQ := by
        rw [← CoalgHom.toLinearMap_eq_coe]
        rfl
      simpa only [CoalgHom.toLinearMap_eq_coe, CoalgHom.comp_toLinearMap, hq,
        LinearMap.ker_comp, ker_mkQ] using h)

/-- The linear map underlying the induced quotient homomorphism is the linear quotient map. -/
@[simp]
theorem mapQCoalgHom_toLinearMap (I : Submodule R C) (J : Submodule R D)
    [I.IsCoideal] [J.IsCoideal] (f : C →ₗc[R] D) (h : I ≤ J.comap f.toLinearMap) :
    (I.mapQCoalgHom J f h).toLinearMap = I.mapQ J f.toLinearMap h :=
  rfl

/-- The induced quotient homomorphism sends the class of `x` to the class of `f x`. -/
@[simp]
theorem mapQCoalgHom_mk (I : Submodule R C) (J : Submodule R D)
    [I.IsCoideal] [J.IsCoideal] (f : C →ₗc[R] D) (h : I ≤ J.comap f.toLinearMap) (x : C) :
    I.mapQCoalgHom J f h (Submodule.Quotient.mk (p := I) x) =
      Submodule.Quotient.mk (p := J) (f x) :=
  rfl

/-- The induced quotient homomorphism intertwines the two quotient projections. -/
theorem mapQCoalgHom_comp_mkQCoalgHom (I : Submodule R C) (J : Submodule R D)
    [I.IsCoideal] [J.IsCoideal] (f : C →ₗc[R] D) (h : I ≤ J.comap f.toLinearMap) :
    (I.mapQCoalgHom J f h).comp (Coalgebra.Quotient.mkQCoalgHom I) =
      (Coalgebra.Quotient.mkQCoalgHom J).comp f :=
  CoalgHom.ext fun x => mapQCoalgHom_mk I J f h x

/-- The quotient homomorphism induced by the identity is the identity. -/
@[simp]
theorem mapQCoalgHom_id (I : Submodule R C) [I.IsCoideal] :
    I.mapQCoalgHom I (CoalgHom.id R C) (Submodule.comap_id I).symm.le =
      CoalgHom.id R (C ⧸ I) := by
  apply CoalgHom.ext
  intro x
  obtain ⟨y, rfl⟩ := I.mkQ_surjective x
  simpa only [mkQ_apply, CoalgHom.id_apply] using
    (mapQCoalgHom_mk I I (CoalgHom.id R C) (Submodule.comap_id I).symm.le y)

variable {E : Type z} [AddCommGroup E] [Module R E] [CoalgebraStruct R E]

/-- Inducing quotient homomorphisms commutes with composition. -/
theorem mapQCoalgHom_comp (I : Submodule R C) (J : Submodule R D)
    (L : Submodule R E) [I.IsCoideal] [J.IsCoideal] [L.IsCoideal]
    (f : C →ₗc[R] D) (g : D →ₗc[R] E)
    (hf : I ≤ J.comap f.toLinearMap) (hg : J ≤ L.comap g.toLinearMap) :
    I.mapQCoalgHom L (g.comp f) (hf.trans (Submodule.comap_mono hg)) =
      (J.mapQCoalgHom L g hg).comp (I.mapQCoalgHom J f hf) := by
  apply CoalgHom.ext
  intro x
  obtain ⟨y, rfl⟩ := I.mkQ_surjective x
  simp only [mkQ_apply, mapQCoalgHom_mk, CoalgHom.comp_apply]

end Submodule

namespace Submodule

variable {R : Type u} [CommRing R]
variable {C : Type v} [AddCommGroup C] [Module R C] [CoalgebraStruct R C]

/-- The image of a coideal under the canonical quotient projection is a coideal. -/
theorem quotientQuotient_image_isCoideal (I J : Submodule R C)
    [hI : I.IsCoideal] [hJ : J.IsCoideal] : (J.map I.mkQ).IsCoideal :=
  hJ.map (Coalgebra.Quotient.mkQCoalgHom I)

/-- The sum of two coideals is a coideal. -/
theorem quotientQuotient_sup_isCoideal (I J : Submodule R C)
    [hI : I.IsCoideal] [hJ : J.IsCoideal] : (I ⊔ J).IsCoideal :=
  hI.sup hJ

section

attribute [local instance] quotientQuotient_image_isCoideal quotientQuotient_sup_isCoideal

/-- The third isomorphism theorem for canonical quotient coalgebra structures.

The underlying linear equivalence is `quotientQuotientEquivQuotientSup`. The image
and join coideal proofs are installed locally, so both endpoints carry Mathlib's
canonical quotient structures. Compatibility is checked on double quotient
representatives using the quotient formulas and composition of tensor maps.
Only comultiplication and counit data are required;
no coassociativity or counit identities are assumed. When the original structure
is a coalgebra, the quotient coalgebra laws are inherited by the usual instances. -/
def quotientQuotientCoalgEquivQuotientSup (I J : Submodule R C)
    [hI : I.IsCoideal] [hJ : J.IsCoideal] :
    ((C ⧸ I) ⧸ J.map I.mkQ) ≃ₗc[R] (C ⧸ (I ⊔ J)) := by
  letI : (J.map I.mkQ).IsCoideal := hJ.map (Coalgebra.Quotient.mkQCoalgHom I)
  letI : (I ⊔ J).IsCoideal := hI.sup hJ
  let e := quotientQuotientEquivQuotientSup I J
  have he : (e.toLinearMap.comp (J.map I.mkQ).mkQ).comp I.mkQ = (I ⊔ J).mkQ := by
    apply LinearMap.ext
    intro a
    rfl
  exact
    { e with
      counit_comp := by
        apply LinearMap.ext
        intro x
        obtain ⟨y, rfl⟩ := (J.map I.mkQ).mkQ_surjective x
        obtain ⟨a, rfl⟩ := I.mkQ_surjective y
        change counit (R := R) (Quotient.mk (p := I ⊔ J) a) =
          counit (R := R) (Quotient.mk (p := J.map I.mkQ) (Quotient.mk (p := I) a))
        simp only [Coalgebra.Quotient.counit_mk]
      map_comp_comul := by
        apply LinearMap.ext
        intro x
        obtain ⟨y, rfl⟩ := (J.map I.mkQ).mkQ_surjective x
        obtain ⟨a, rfl⟩ := I.mkQ_surjective y
        change TensorProduct.map e.toLinearMap e.toLinearMap
            (comul (R := R) (Quotient.mk (p := J.map I.mkQ) (Quotient.mk (p := I) a))) =
          comul (R := R) (Quotient.mk (p := I ⊔ J) a)
        rw [Coalgebra.Quotient.comul_mk, Coalgebra.Quotient.comul_mk,
          TensorProduct.map_map, TensorProduct.map_map, he, Coalgebra.Quotient.comul_mk] }

/-- The canonical coalgebra equivalence has exactly the stock linear equivalence underneath. -/
@[simp]
theorem quotientQuotientCoalgEquivQuotientSup_toLinearEquiv (I J : Submodule R C)
    [hI : I.IsCoideal] [hJ : J.IsCoideal] :
    (quotientQuotientCoalgEquivQuotientSup I J).toLinearEquiv =
      quotientQuotientEquivQuotientSup I J :=
  rfl

/-- The canonical equivalence sends a twice-projected representative to its class modulo the join. -/
@[simp]
theorem quotientQuotientCoalgEquivQuotientSup_mk_mk (I J : Submodule R C)
    [hI : I.IsCoideal] [hJ : J.IsCoideal] (a : C) :
    quotientQuotientCoalgEquivQuotientSup I J
        (Quotient.mk (p := J.map I.mkQ) (Quotient.mk (p := I) a)) =
      Quotient.mk (p := I ⊔ J) a :=
  rfl

/-- The inverse canonical equivalence sends a class modulo the join to its twice-projected class. -/
@[simp]
theorem quotientQuotientCoalgEquivQuotientSup_symm_mk (I J : Submodule R C)
    [hI : I.IsCoideal] [hJ : J.IsCoideal] (a : C) :
    (quotientQuotientCoalgEquivQuotientSup I J).symm (Quotient.mk (p := I ⊔ J) a) =
      Quotient.mk (p := J.map I.mkQ) (Quotient.mk (p := I) a) := by
  letI : (J.map I.mkQ).IsCoideal := hJ.map (Coalgebra.Quotient.mkQCoalgHom I)
  letI : (I ⊔ J).IsCoideal := hI.sup hJ
  rw [← quotientQuotientCoalgEquivQuotientSup_mk_mk I J a]
  exact (quotientQuotientCoalgEquivQuotientSup I J).toLinearEquiv.symm_apply_apply _

/-- The canonical equivalence intertwines the bundled two-stage and join projections. -/
@[simp]
theorem quotientQuotientCoalgEquivQuotientSup_comp_mkQCoalgHom (I J : Submodule R C)
    [hI : I.IsCoideal] [hJ : J.IsCoideal] :
    (quotientQuotientCoalgEquivQuotientSup I J).toCoalgHom.comp
        ((Coalgebra.Quotient.mkQCoalgHom (J.map I.mkQ)).comp
          (Coalgebra.Quotient.mkQCoalgHom I)) =
      Coalgebra.Quotient.mkQCoalgHom (I ⊔ J) := by
  letI : (J.map I.mkQ).IsCoideal := hJ.map (Coalgebra.Quotient.mkQCoalgHom I)
  letI : (I ⊔ J).IsCoideal := hI.sup hJ
  apply CoalgHom.ext
  intro a
  exact quotientQuotientCoalgEquivQuotientSup_mk_mk I J a

end

end Submodule

namespace CoalgHomClass

section Field

variable {K : Type u} [Field K]
variable {C : Type v} [AddCommGroup C] [Module K C] [CoalgebraStruct K C]
variable {D : Type w} [AddCommGroup D] [Module K D] [CoalgebraStruct K D]
variable {F : Type z} [FunLike F C D] [CoalgHomClass F K C D]

/-- Over a field, the linear kernel of a coalgebra morphism is a coideal, without
surjectivity or coalgebra laws on either module. -/
theorem ker_isCoideal (f : F) :
    (LinearMap.ofClass f : C →ₗ[K] D).ker.IsCoideal := by
  let g : C →ₗ[K] D := LinearMap.ofClass f
  let I := g.ker
  let h : (C ⧸ I) →ₗ[K] D := I.liftQ g le_rfl
  have h_injective : Function.Injective h :=
    LinearMap.ker_eq_bot.mp (I.ker_liftQ_eq_bot g le_rfl le_rfl)
  have hq : h.comp I.mkQ = g := I.liftQ_mkQ g le_rfl
  -- The quotient lift is injective, and over a field its tensor square is too.
  -- Thus the coideal condition can be checked after mapping to the target tensor square.
  have h_tensor_injective : Function.Injective (TensorProduct.map h h) :=
    TensorProduct.map_injective_of_flat_flat h h h_injective h_injective
  constructor
  · intro x hx
    have hxg : f x = 0 := LinearMap.mem_ker.mp hx
    rw [← counit_comp_apply f x, hxg, map_zero]
  · intro x hx
    have hxg : f x = 0 := LinearMap.mem_ker.mp hx
    apply h_tensor_injective
    calc
      TensorProduct.map h h (TensorProduct.map I.mkQ I.mkQ (comul x)) =
          TensorProduct.map g g (comul x) := by
        rw [TensorProduct.map_map, hq]
      _ = comul (f x) := map_comp_comul_apply f x
      _ = 0 := by rw [hxg, map_zero]
      _ = TensorProduct.map h h 0 := (map_zero _).symm

end Field

end CoalgHomClass
