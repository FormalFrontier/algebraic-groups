/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.TensorProduct
public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.TensorProduct.Associator
public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.TensorProduct.Unitors

/-!
# Pentagon and triangle for external tensor products

Both paths are comodule morphisms over the final coefficient coalgebra.
Intermediate coefficient changes are normalized by the tensor-product object
bridge and the coalgebra pentagon and triangle. The path morphisms compose
existing associators and unitors; their characteristic maps are the distinct
carrier associators and unitors.

The carrier proofs use Mathlib's polymorphic tensor associativity coherence
and tensor balancing, without a purity assumption on coactions.

## References

Mathlib's `LinearAlgebra.TensorProduct.Associator` and
`RingTheory.Coalgebra.TensorProduct` supply the tensor maps and coherence API.
-/

@[expose] public section

open scoped TensorProduct

universe uR uC uD uE uF uM uN uP uQ

namespace Coalgebra.RightComodule

variable {R : Type uR} {C : Type uC} {D : Type uD} {E : Type uE} {F : Type uF}
variable {M : Type uM} {N : Type uN} {P : Type uP} {Q : Type uQ}
variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid D] [Module R D] [Coalgebra R D]
variable [AddCommMonoid E] [Module R E] [Coalgebra R E]
variable [AddCommMonoid F] [Module R F] [Coalgebra R F]
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
variable [AddCommMonoid P] [Module R P] [AddCommMonoid Q] [Module R Q]

section Pentagon

variable (X : RightComodule R C M) (Y : RightComodule R D N)
variable (Z : RightComodule R E P) (W : RightComodule R F Q)

/-- The three-edge pentagon path, with all vertices over the final coalgebra. -/
noncomputable def externalTensorPentagonLongHom :
    RightComoduleHom
      ((((X.externalTensor Y).externalTensor Z).externalTensor W).mapCoalgebra
        ((Coalgebra.TensorProduct.assoc R R C D (E ⊗[R] F)).toCoalgHom.comp
          (Coalgebra.TensorProduct.assoc R R (C ⊗[R] D) E F).toCoalgHom))
      (X.externalTensor (Y.externalTensor (Z.externalTensor W))) := by
  let c12 : (C ⊗[R] (D ⊗[R] E)) ⊗[R] F →ₗc[R] C ⊗[R] ((D ⊗[R] E) ⊗[R] F) :=
    (Coalgebra.TensorProduct.assoc R R C (D ⊗[R] E) F).toCoalgHom
  let c23 : C ⊗[R] ((D ⊗[R] E) ⊗[R] F) →ₗc[R] C ⊗[R] (D ⊗[R] (E ⊗[R] F)) :=
    Coalgebra.TensorProduct.map (R := R) (S := R) (CoalgHom.id R C)
      (Coalgebra.TensorProduct.assoc R R D E F).toCoalgHom
  let S0 := (((X.externalTensor Y).externalTensor Z).externalTensor W).mapCoalgebra
    ((Coalgebra.TensorProduct.assoc R R C D (E ⊗[R] F)).toCoalgHom.comp
      (Coalgebra.TensorProduct.assoc R R (C ⊗[R] D) E F).toCoalgHom)
  let S1 := ((X.externalTensor (Y.externalTensor Z)).externalTensor W).mapCoalgebra
    (c23.comp c12)
  let S2 := (X.externalTensor ((Y.externalTensor Z).externalTensor W)).mapCoalgebra c23
  let A01 : RightComoduleHom S0 S1 :=
    { toLinearMap := _root_.TensorProduct.map
        (_root_.TensorProduct.assoc R M N P).toLinearMap (LinearMap.id : Q →ₗ[R] Q)
      colinear := by
        have h := (((externalTensorAssocHom X Y Z).externalTensor
          (RightComoduleHom.id W)).mapCoalgebra (c23.comp c12)).colinear
        simpa only [RightComoduleHom.mapCoalgebra_toLinearMap,
          RightComoduleHom.toLinearMap_externalTensor, externalTensorAssocHom_toLinearMap,
          RightComoduleHom.id, externalTensor_mapCoalgebra_left, mapCoalgebra_comp,
          S0, S1, CoalgHom.comp_assoc, c12, c23,
          Coalgebra.TensorProduct.assoc_pentagon] using h }
  let A12 : RightComoduleHom S1 S2 :=
    { toLinearMap := (_root_.TensorProduct.assoc R M (N ⊗[R] P) Q).toLinearMap
      colinear := by
        simpa only [RightComoduleHom.mapCoalgebra_toLinearMap,
          externalTensorAssocHom_toLinearMap, mapCoalgebra_comp, S1, S2, c12] using
          ((externalTensorAssocHom X (Y.externalTensor Z) W).mapCoalgebra c23).colinear }
  let A23 : RightComoduleHom S2
      (X.externalTensor (Y.externalTensor (Z.externalTensor W))) :=
    { toLinearMap := _root_.TensorProduct.map (LinearMap.id : M →ₗ[R] M)
        (_root_.TensorProduct.assoc R N P Q).toLinearMap
      colinear := by
        simpa only [RightComoduleHom.toLinearMap_externalTensor,
          externalTensorAssocHom_toLinearMap, RightComoduleHom.id,
          externalTensor_mapCoalgebra_right, S2, c23] using
          ((RightComoduleHom.id X).externalTensor (externalTensorAssocHom Y Z W)).colinear }
  exact A23.comp (A12.comp A01)

/-- The two-edge pentagon path over the same final coefficient coalgebra. -/
noncomputable def externalTensorPentagonShortHom :
    RightComoduleHom
      ((((X.externalTensor Y).externalTensor Z).externalTensor W).mapCoalgebra
        ((Coalgebra.TensorProduct.assoc R R C D (E ⊗[R] F)).toCoalgHom.comp
          (Coalgebra.TensorProduct.assoc R R (C ⊗[R] D) E F).toCoalgHom))
      (X.externalTensor (Y.externalTensor (Z.externalTensor W))) := by
  let c43 : (C ⊗[R] D) ⊗[R] (E ⊗[R] F) →ₗc[R] C ⊗[R] (D ⊗[R] (E ⊗[R] F)) :=
    (Coalgebra.TensorProduct.assoc R R C D (E ⊗[R] F)).toCoalgHom
  let A04 : RightComoduleHom
      ((((X.externalTensor Y).externalTensor Z).externalTensor W).mapCoalgebra
        (c43.comp (Coalgebra.TensorProduct.assoc R R (C ⊗[R] D) E F).toCoalgHom))
      (((X.externalTensor Y).externalTensor (Z.externalTensor W)).mapCoalgebra c43) :=
    { toLinearMap := (_root_.TensorProduct.assoc R (M ⊗[R] N) P Q).toLinearMap
      colinear := by
        simpa only [RightComoduleHom.mapCoalgebra_toLinearMap,
          externalTensorAssocHom_toLinearMap, mapCoalgebra_comp] using
          ((externalTensorAssocHom (X.externalTensor Y) Z W).mapCoalgebra c43).colinear }
  exact (externalTensorAssocHom X Y (Z.externalTensor W)).comp A04

/-- The underlying map of the long pentagon path is the three-edge carrier path. -/
@[simp] theorem externalTensorPentagonLongHom_toLinearMap :
    (externalTensorPentagonLongHom X Y Z W).toLinearMap =
      _root_.TensorProduct.map (LinearMap.id : M →ₗ[R] M)
          (_root_.TensorProduct.assoc R N P Q).toLinearMap ∘ₗ
        ((_root_.TensorProduct.assoc R M (N ⊗[R] P) Q).toLinearMap ∘ₗ
          _root_.TensorProduct.map (_root_.TensorProduct.assoc R M N P).toLinearMap
            (LinearMap.id : Q →ₗ[R] Q)) := rfl

/-- The underlying map of the short pentagon path is the two-edge carrier path. -/
@[simp] theorem externalTensorPentagonShortHom_toLinearMap :
    (externalTensorPentagonShortHom X Y Z W).toLinearMap =
      (_root_.TensorProduct.assoc R M N (P ⊗[R] Q)).toLinearMap ∘ₗ
        (_root_.TensorProduct.assoc R (M ⊗[R] N) P Q).toLinearMap := rfl

/-- Evaluate the long pentagon path at an arbitrary tensor. -/
@[simp] theorem externalTensorPentagonLongHom_apply (t : ((M ⊗[R] N) ⊗[R] P) ⊗[R] Q) :
    externalTensorPentagonLongHom X Y Z W t =
      _root_.TensorProduct.map (LinearMap.id : M →ₗ[R] M)
        (_root_.TensorProduct.assoc R N P Q).toLinearMap
        (_root_.TensorProduct.assoc R M (N ⊗[R] P) Q
          (_root_.TensorProduct.map (_root_.TensorProduct.assoc R M N P).toLinearMap
            (LinearMap.id : Q →ₗ[R] Q) t)) := rfl

/-- Evaluate the short pentagon path at an arbitrary tensor. -/
@[simp] theorem externalTensorPentagonShortHom_apply (t : ((M ⊗[R] N) ⊗[R] P) ⊗[R] Q) :
    externalTensorPentagonShortHom X Y Z W t =
      _root_.TensorProduct.assoc R M N (P ⊗[R] Q)
        (_root_.TensorProduct.assoc R (M ⊗[R] N) P Q t) := rfl

/-- The long pentagon path reassociates a fourfold pure tensor. -/
@[simp] theorem externalTensorPentagonLongHom_tmul (m : M) (n : N) (p : P) (q : Q) :
    externalTensorPentagonLongHom X Y Z W (((m ⊗ₜ[R] n) ⊗ₜ[R] p) ⊗ₜ[R] q) =
      m ⊗ₜ[R] (n ⊗ₜ[R] (p ⊗ₜ[R] q)) := rfl

/-- The short pentagon path has the same pure-tensor reassociation. -/
@[simp] theorem externalTensorPentagonShortHom_tmul (m : M) (n : N) (p : P) (q : Q) :
    externalTensorPentagonShortHom X Y Z W (((m ⊗ₜ[R] n) ⊗ₜ[R] p) ⊗ₜ[R] q) =
      m ⊗ₜ[R] (n ⊗ₜ[R] (p ⊗ₜ[R] q)) := rfl

/-- The long pentagon path is colinear over the right-associated coefficient coalgebra. -/
theorem externalTensorPentagonLongHom_colinear :
    (X.externalTensor (Y.externalTensor (Z.externalTensor W))).coaction ∘ₗ
        (externalTensorPentagonLongHom X Y Z W).toLinearMap =
      (externalTensorPentagonLongHom X Y Z W).toLinearMap.rTensor
          (C ⊗[R] (D ⊗[R] (E ⊗[R] F))) ∘ₗ
        ((((X.externalTensor Y).externalTensor Z).externalTensor W).mapCoalgebra
          ((Coalgebra.TensorProduct.assoc R R C D (E ⊗[R] F)).toCoalgHom.comp
            (Coalgebra.TensorProduct.assoc R R (C ⊗[R] D) E F).toCoalgHom)).coaction :=
  (externalTensorPentagonLongHom X Y Z W).colinear

/-- The short pentagon path is colinear over the same final coefficient coalgebra. -/
theorem externalTensorPentagonShortHom_colinear :
    (X.externalTensor (Y.externalTensor (Z.externalTensor W))).coaction ∘ₗ
        (externalTensorPentagonShortHom X Y Z W).toLinearMap =
      (externalTensorPentagonShortHom X Y Z W).toLinearMap.rTensor
          (C ⊗[R] (D ⊗[R] (E ⊗[R] F))) ∘ₗ
        ((((X.externalTensor Y).externalTensor Z).externalTensor W).mapCoalgebra
          ((Coalgebra.TensorProduct.assoc R R C D (E ⊗[R] F)).toCoalgHom.comp
            (Coalgebra.TensorProduct.assoc R R (C ⊗[R] D) E F).toCoalgHom)).coaction :=
  (externalTensorPentagonShortHom X Y Z W).colinear

/-- The pentagon for external tensor products, from Mathlib's tensor carrier coherence. -/
theorem externalTensor_pentagon :
    externalTensorPentagonLongHom X Y Z W = externalTensorPentagonShortHom X Y Z W := by
  apply RightComoduleHom.toLinearMap_injective
  change (externalTensorPentagonLongHom X Y Z W).toLinearMap =
    (externalTensorPentagonShortHom X Y Z W).toLinearMap
  rw [externalTensorPentagonLongHom_toLinearMap, externalTensorPentagonShortHom_toLinearMap]
  refine _root_.TensorProduct.ext_fourfold fun (m : M) (n : N) (p : P) (q : Q) => ?_
  rfl

end Pentagon

section Triangle

variable (X : RightComodule R C M) (Y : RightComodule R D N)

/-- The associator followed by the left unitor, over the final coefficient coalgebra.
The middle object is the canonical regular scalar comodule. -/
noncomputable def externalTensorTriangleLongHom :
    RightComoduleHom
      (((X.externalTensor (regular R R)).externalTensor Y).mapCoalgebra
        (Coalgebra.TensorProduct.map (R := R) (S := R)
          (Coalgebra.TensorProduct.rid R R C).toCoalgHom (CoalgHom.id R D)))
      (X.externalTensor Y) := by
  let t12 : C ⊗[R] (R ⊗[R] D) →ₗc[R] C ⊗[R] D :=
    Coalgebra.TensorProduct.map (R := R) (S := R) (CoalgHom.id R C)
      (Coalgebra.TensorProduct.lid R D).toCoalgHom
  let O0 := ((X.externalTensor (regular R R)).externalTensor Y).mapCoalgebra
    (Coalgebra.TensorProduct.map (R := R) (S := R)
      (Coalgebra.TensorProduct.rid R R C).toCoalgHom (CoalgHom.id R D))
  let O1 := (X.externalTensor ((regular R R).externalTensor Y)).mapCoalgebra t12
  let G01 : RightComoduleHom O0 O1 :=
    { toLinearMap := (_root_.TensorProduct.assoc R M R N).toLinearMap
      colinear := by
        simpa only [RightComoduleHom.mapCoalgebra_toLinearMap,
          externalTensorAssocHom_toLinearMap, mapCoalgebra_comp, O0, O1, t12,
          ← Coalgebra.TensorProduct.assoc_triangle] using
          ((externalTensorAssocHom X (regular R R) Y).mapCoalgebra t12).colinear }
  let G12 : RightComoduleHom O1 (X.externalTensor Y) :=
    { toLinearMap := _root_.TensorProduct.map (LinearMap.id : M →ₗ[R] M)
        (_root_.TensorProduct.lid R N).toLinearMap
      colinear := by
        simpa only [RightComoduleHom.toLinearMap_externalTensor,
          externalTensorLeftUnitor_toLinearMap, RightComoduleHom.id,
          externalTensor_mapCoalgebra_right, O1, t12] using
          ((RightComoduleHom.id X).externalTensor (externalTensorLeftUnitor Y)).colinear }
  exact G12.comp G01

/-- The right unitor tensored with the identity, over the final coefficient coalgebra. -/
noncomputable def externalTensorTriangleShortHom :
    RightComoduleHom
      (((X.externalTensor (regular R R)).externalTensor Y).mapCoalgebra
        (Coalgebra.TensorProduct.map (R := R) (S := R)
          (Coalgebra.TensorProduct.rid R R C).toCoalgHom (CoalgHom.id R D)))
      (X.externalTensor Y) where
  toLinearMap := _root_.TensorProduct.map (_root_.TensorProduct.rid R M).toLinearMap
    (LinearMap.id : N →ₗ[R] N)
  colinear := by
    simpa only [RightComoduleHom.toLinearMap_externalTensor,
      externalTensorRightUnitor_toLinearMap, RightComoduleHom.id,
      externalTensor_mapCoalgebra_left] using
      ((externalTensorRightUnitor X).externalTensor (RightComoduleHom.id Y)).colinear

/-- The long triangle path has the associator-left-unitor carrier map. -/
@[simp] theorem externalTensorTriangleLongHom_toLinearMap :
    (externalTensorTriangleLongHom X Y).toLinearMap =
      _root_.TensorProduct.map (LinearMap.id : M →ₗ[R] M)
          (_root_.TensorProduct.lid R N).toLinearMap ∘ₗ
        (_root_.TensorProduct.assoc R M R N).toLinearMap := rfl

/-- The short triangle path has the right-unitor carrier map. -/
@[simp] theorem externalTensorTriangleShortHom_toLinearMap :
    (externalTensorTriangleShortHom X Y).toLinearMap =
      _root_.TensorProduct.map (_root_.TensorProduct.rid R M).toLinearMap
        (LinearMap.id : N →ₗ[R] N) := rfl

/-- Evaluate the long triangle path at an arbitrary tensor. -/
@[simp] theorem externalTensorTriangleLongHom_apply (t : (M ⊗[R] R) ⊗[R] N) :
    externalTensorTriangleLongHom X Y t =
      _root_.TensorProduct.map (LinearMap.id : M →ₗ[R] M)
        (_root_.TensorProduct.lid R N).toLinearMap (_root_.TensorProduct.assoc R M R N t) := rfl

/-- Evaluate the short triangle path at an arbitrary tensor. -/
@[simp] theorem externalTensorTriangleShortHom_apply (t : (M ⊗[R] R) ⊗[R] N) :
    externalTensorTriangleShortHom X Y t =
      _root_.TensorProduct.map (_root_.TensorProduct.rid R M).toLinearMap
        (LinearMap.id : N →ₗ[R] N) t := rfl

/-- The long triangle path moves the middle scalar onto the right carrier. -/
@[simp] theorem externalTensorTriangleLongHom_tmul (m : M) (s : R) (n : N) :
    externalTensorTriangleLongHom X Y ((m ⊗ₜ[R] s) ⊗ₜ[R] n) =
      m ⊗ₜ[R] (s • n) := rfl

/-- The short triangle path moves the middle scalar onto the left carrier. -/
@[simp] theorem externalTensorTriangleShortHom_tmul (m : M) (s : R) (n : N) :
    externalTensorTriangleShortHom X Y ((m ⊗ₜ[R] s) ⊗ₜ[R] n) =
      (s • m) ⊗ₜ[R] n := rfl

/-- The long triangle path is colinear over the final tensor coefficient coalgebra. -/
theorem externalTensorTriangleLongHom_colinear :
    (X.externalTensor Y).coaction ∘ₗ (externalTensorTriangleLongHom X Y).toLinearMap =
      (externalTensorTriangleLongHom X Y).toLinearMap.rTensor (C ⊗[R] D) ∘ₗ
        (((X.externalTensor (regular R R)).externalTensor Y).mapCoalgebra
          (Coalgebra.TensorProduct.map (R := R) (S := R)
            (Coalgebra.TensorProduct.rid R R C).toCoalgHom (CoalgHom.id R D))).coaction :=
  (externalTensorTriangleLongHom X Y).colinear

/-- The short triangle path is colinear over the same final coefficient coalgebra. -/
theorem externalTensorTriangleShortHom_colinear :
    (X.externalTensor Y).coaction ∘ₗ (externalTensorTriangleShortHom X Y).toLinearMap =
      (externalTensorTriangleShortHom X Y).toLinearMap.rTensor (C ⊗[R] D) ∘ₗ
        (((X.externalTensor (regular R R)).externalTensor Y).mapCoalgebra
          (Coalgebra.TensorProduct.map (R := R) (S := R)
            (Coalgebra.TensorProduct.rid R R C).toCoalgHom (CoalgHom.id R D))).coaction :=
  (externalTensorTriangleShortHom X Y).colinear

/-- The triangle for external tensor products, by Mathlib's tensor balancing law. -/
theorem externalTensor_triangle :
    externalTensorTriangleShortHom X Y = externalTensorTriangleLongHom X Y := by
  apply RightComoduleHom.toLinearMap_injective
  change (externalTensorTriangleShortHom X Y).toLinearMap =
    (externalTensorTriangleLongHom X Y).toLinearMap
  rw [externalTensorTriangleShortHom_toLinearMap, externalTensorTriangleLongHom_toLinearMap]
  refine _root_.TensorProduct.ext_threefold fun (m : M) (s : R) (n : N) => ?_
  change (s • m) ⊗ₜ[R] n = m ⊗ₜ[R] (s • n)
  exact _root_.TensorProduct.smul_tmul s m n

end Triangle

end Coalgebra.RightComodule
