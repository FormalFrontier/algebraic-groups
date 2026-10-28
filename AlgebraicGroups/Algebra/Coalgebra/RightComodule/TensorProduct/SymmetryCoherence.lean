/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.TensorProduct.Associator
public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.TensorProduct.Symmetry
public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.TensorProduct.Unitors

/-!
# Symmetry coherence for external tensor products

The two hexagon paths compose bundled morphisms over the common final
coefficient coalgebra. Coefficient coherence normalizes their sources, before
carrier coherence proves equality. The reverse hexagon is obtained by inverting
the relabelled forward comparison and changing every coefficient by its inverse
path. The scalar comparisons use the canonical regular scalar comodule.

## References

The carrier arguments follow Mathlib's `SemimoduleCat.MonoidalCategory`
hexagons and `TensorProduct.comm_trans_rid` / `comm_trans_lid`, with independent
tensor universes. Coalgebra maps and the bundled external tensor maps are reused.
-/

@[expose] public section

open scoped TensorProduct

universe uR uC uD uE uM uN uP

namespace Coalgebra.RightComodule

noncomputable section

variable {R : Type uR} {C : Type uC} {D : Type uD} {E : Type uE}
variable {M : Type uM} {N : Type uN} {P : Type uP}
variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid D] [Module R D] [Coalgebra R D]
variable [AddCommMonoid E] [Module R E] [Coalgebra R E]
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
variable [AddCommMonoid P] [Module R P]

section Hexagon

variable (X : RightComodule R C M) (Y : RightComodule R D N)
variable (Z : RightComodule R E P)

private abbrev c12 (R : Type uR) [CommSemiring R]
    (C : Type uC) [AddCommMonoid C] [Module R C] [Coalgebra R C]
    (D : Type uD) [AddCommMonoid D] [Module R D] [Coalgebra R D]
    (E : Type uE) [AddCommMonoid E] [Module R E] [Coalgebra R E] :=
  (Coalgebra.TensorProduct.comm R C (D ⊗[R] E)).toCoalgHom

private abbrev c23 (R : Type uR) [CommSemiring R]
    (C : Type uC) [AddCommMonoid C] [Module R C] [Coalgebra R C]
    (D : Type uD) [AddCommMonoid D] [Module R D] [Coalgebra R D]
    (E : Type uE) [AddCommMonoid E] [Module R E] [Coalgebra R E] :=
  (Coalgebra.TensorProduct.assoc R R D E C).toCoalgHom

private abbrev c04 (R : Type uR) [CommSemiring R]
    (C : Type uC) [AddCommMonoid C] [Module R C] [Coalgebra R C]
    (D : Type uD) [AddCommMonoid D] [Module R D] [Coalgebra R D]
    (E : Type uE) [AddCommMonoid E] [Module R E] [Coalgebra R E] :=
  show ((C ⊗[R] D) ⊗[R] E) →ₗc[R] ((D ⊗[R] C) ⊗[R] E) from by
    exact
      Coalgebra.TensorProduct.map (R := R) (S := R)
        (M := C ⊗[R] D) (N := D ⊗[R] C) (P := E) (Q := E)
        (by exact (Coalgebra.TensorProduct.comm R C D).toCoalgHom) (CoalgHom.id R E)

private abbrev c45 (R : Type uR) [CommSemiring R]
    (C : Type uC) [AddCommMonoid C] [Module R C] [Coalgebra R C]
    (D : Type uD) [AddCommMonoid D] [Module R D] [Coalgebra R D]
    (E : Type uE) [AddCommMonoid E] [Module R E] [Coalgebra R E] :=
  (Coalgebra.TensorProduct.assoc R R D C E).toCoalgHom

private abbrev c53 (R : Type uR) [CommSemiring R]
    (C : Type uC) [AddCommMonoid C] [Module R C] [Coalgebra R C]
    (D : Type uD) [AddCommMonoid D] [Module R D] [Coalgebra R D]
    (E : Type uE) [AddCommMonoid E] [Module R E] [Coalgebra R E] :=
  show D ⊗[R] (C ⊗[R] E) →ₗc[R] D ⊗[R] (E ⊗[R] C) from by
    exact
      Coalgebra.TensorProduct.map (R := R) (S := R)
        (M := D) (N := D) (P := C ⊗[R] E) (Q := E ⊗[R] C)
        (CoalgHom.id R D) (by exact (Coalgebra.TensorProduct.comm R C E).toCoalgHom)

private abbrev pCS (R : Type uR) [CommSemiring R]
    (C : Type uC) [AddCommMonoid C] [Module R C] [Coalgebra R C]
    (D : Type uD) [AddCommMonoid D] [Module R D] [Coalgebra R D]
    (E : Type uE) [AddCommMonoid E] [Module R E] [Coalgebra R E] :=
  show ((C ⊗[R] D) ⊗[R] E) →ₗc[R] D ⊗[R] (E ⊗[R] C) from by
    exact
      (c53 R C D E).comp ((c45 R C D E).comp (c04 R C D E))

private abbrev B0 (X : RightComodule R C M) (Y : RightComodule R D N)
    (Z : RightComodule R E P) :=
  (X.externalTensor Y).externalTensor Z

private abbrev B1 (X : RightComodule R C M) (Y : RightComodule R D N)
    (Z : RightComodule R E P) :=
  X.externalTensor (Y.externalTensor Z)

private abbrev B2 (X : RightComodule R C M) (Y : RightComodule R D N)
    (Z : RightComodule R E P) :=
  (Y.externalTensor Z).externalTensor X

private abbrev B3 (X : RightComodule R C M) (Y : RightComodule R D N)
    (Z : RightComodule R E P) :=
  Y.externalTensor (Z.externalTensor X)

private abbrev B4 (X : RightComodule R C M) (Y : RightComodule R D N)
    (Z : RightComodule R E P) :=
  (Y.externalTensor X).externalTensor Z

private abbrev B5 (X : RightComodule R C M) (Y : RightComodule R D N)
    (Z : RightComodule R E P) :=
  Y.externalTensor (X.externalTensor Z)

private abbrev S0 (X : RightComodule R C M) (Y : RightComodule R D N)
    (Z : RightComodule R E P) :=
  (B0 X Y Z).mapCoalgebra (pCS R C D E)

private abbrev S1 (X : RightComodule R C M) (Y : RightComodule R D N)
    (Z : RightComodule R E P) :=
  (B1 X Y Z).mapCoalgebra ((c23 R C D E).comp (c12 R C D E))

private abbrev S2 (X : RightComodule R C M) (Y : RightComodule R D N)
    (Z : RightComodule R E P) :=
  (B2 X Y Z).mapCoalgebra (c23 R C D E)

private abbrev S4 (X : RightComodule R C M) (Y : RightComodule R D N)
    (Z : RightComodule R E P) :=
  (B4 X Y Z).mapCoalgebra ((c53 R C D E).comp (c45 R C D E))

private abbrev S5 (X : RightComodule R C M) (Y : RightComodule R D N)
    (Z : RightComodule R E P) :=
  (B5 X Y Z).mapCoalgebra (c53 R C D E)

/-- Associator, symmetry, associator, with every vertex over `D ⊗ (E ⊗ C)`. -/
def externalTensorHexagonLongHom :
    RightComoduleHom
      (((X.externalTensor Y).externalTensor Z).mapCoalgebra
        (show ((C ⊗[R] D) ⊗[R] E) →ₗc[R] D ⊗[R] (E ⊗[R] C) from by
          exact
            (Coalgebra.TensorProduct.map (R := R) (S := R)
              (M := D) (N := D) (P := C ⊗[R] E) (Q := E ⊗[R] C)
              (CoalgHom.id R D)
              (by exact (Coalgebra.TensorProduct.comm R C E).toCoalgHom)).comp
              (((Coalgebra.TensorProduct.assoc R R D C E).toCoalgHom).comp
                (Coalgebra.TensorProduct.map (R := R) (S := R)
                  (M := C ⊗[R] D) (N := D ⊗[R] C) (P := E) (Q := E)
                  (by exact (Coalgebra.TensorProduct.comm R C D).toCoalgHom)
                  (CoalgHom.id R E)))))
      (Y.externalTensor (Z.externalTensor X)) := by
  let c12 :=
    (Coalgebra.TensorProduct.comm R C (D ⊗[R] E)).toCoalgHom
  let c23 :=
    (Coalgebra.TensorProduct.assoc R R D E C).toCoalgHom
  let c04 :=
    show ((C ⊗[R] D) ⊗[R] E) →ₗc[R] ((D ⊗[R] C) ⊗[R] E) from by
      exact
        Coalgebra.TensorProduct.map (R := R) (S := R)
          (M := C ⊗[R] D) (N := D ⊗[R] C) (P := E) (Q := E)
          (by exact (Coalgebra.TensorProduct.comm R C D).toCoalgHom) (CoalgHom.id R E)
  let c45 :=
    (Coalgebra.TensorProduct.assoc R R D C E).toCoalgHom
  let c53 :=
    show D ⊗[R] (C ⊗[R] E) →ₗc[R] D ⊗[R] (E ⊗[R] C) from by
      exact
        Coalgebra.TensorProduct.map (R := R) (S := R)
          (M := D) (N := D) (P := C ⊗[R] E) (Q := E ⊗[R] C)
          (CoalgHom.id R D) (by exact (Coalgebra.TensorProduct.comm R C E).toCoalgHom)
  let pCS :=
    show ((C ⊗[R] D) ⊗[R] E) →ₗc[R] D ⊗[R] (E ⊗[R] C) from by
      exact
        c53.comp (c45.comp c04)
  let S0 :=
    (((X.externalTensor Y).externalTensor Z)).mapCoalgebra pCS
  let S1 :=
    (X.externalTensor (Y.externalTensor Z)).mapCoalgebra (c23.comp c12)
  let S2 :=
    (((Y.externalTensor Z).externalTensor X)).mapCoalgebra c23
  let A01 : RightComoduleHom S0 S1 :=
    { toLinearMap := (_root_.TensorProduct.assoc R M N P).toLinearMap
      colinear := by
        simpa only [S0, S1, pCS, c12, c23, c04, c45, c53,
          mapCoalgebra_comp, CoalgHom.comp_assoc,
          Coalgebra.TensorProduct.comm_hexagon,
          RightComoduleHom.mapCoalgebra_toLinearMap, externalTensorAssocHom_toLinearMap] using
          ((externalTensorAssocHom X Y Z).mapCoalgebra
            (c23.comp c12)).colinear }
  let A12 : RightComoduleHom S1 S2 :=
    { toLinearMap := (_root_.TensorProduct.comm R M (N ⊗[R] P)).toLinearMap
      colinear := by
        simpa only [S1, S2, c12, c23,
          mapCoalgebra_comp,
          RightComoduleHom.mapCoalgebra_toLinearMap, externalTensorCommHom_toLinearMap] using
          ((externalTensorCommHom X (Y.externalTensor Z)).mapCoalgebra c23).colinear }
  let A23 : RightComoduleHom S2 (Y.externalTensor (Z.externalTensor X)) :=
    externalTensorAssocHom Y Z X
  exact A23.comp (A12.comp A01)

/-- Tensor symmetry, associator, tensor symmetry over the same final coalgebra. -/
def externalTensorHexagonShortHom :
    RightComoduleHom
      (((X.externalTensor Y).externalTensor Z).mapCoalgebra
        (show ((C ⊗[R] D) ⊗[R] E) →ₗc[R] D ⊗[R] (E ⊗[R] C) from by
          exact
            (Coalgebra.TensorProduct.map (R := R) (S := R)
              (M := D) (N := D) (P := C ⊗[R] E) (Q := E ⊗[R] C)
              (CoalgHom.id R D)
              (by exact (Coalgebra.TensorProduct.comm R C E).toCoalgHom)).comp
              (((Coalgebra.TensorProduct.assoc R R D C E).toCoalgHom).comp
                (Coalgebra.TensorProduct.map (R := R) (S := R)
                  (M := C ⊗[R] D) (N := D ⊗[R] C) (P := E) (Q := E)
                  (by exact (Coalgebra.TensorProduct.comm R C D).toCoalgHom)
                  (CoalgHom.id R E)))))
      (Y.externalTensor (Z.externalTensor X)) := by
  let c04 :=
    show ((C ⊗[R] D) ⊗[R] E) →ₗc[R] ((D ⊗[R] C) ⊗[R] E) from by
      exact
        Coalgebra.TensorProduct.map (R := R) (S := R)
          (M := C ⊗[R] D) (N := D ⊗[R] C) (P := E) (Q := E)
          (by exact (Coalgebra.TensorProduct.comm R C D).toCoalgHom) (CoalgHom.id R E)
  let c45 :=
    (Coalgebra.TensorProduct.assoc R R D C E).toCoalgHom
  let c53 :=
    show D ⊗[R] (C ⊗[R] E) →ₗc[R] D ⊗[R] (E ⊗[R] C) from by
      exact
        Coalgebra.TensorProduct.map (R := R) (S := R)
          (M := D) (N := D) (P := C ⊗[R] E) (Q := E ⊗[R] C)
          (CoalgHom.id R D) (by exact (Coalgebra.TensorProduct.comm R C E).toCoalgHom)
  let pCS :=
    show ((C ⊗[R] D) ⊗[R] E) →ₗc[R] D ⊗[R] (E ⊗[R] C) from by
      exact
        c53.comp (c45.comp c04)
  let S0 :=
    (((X.externalTensor Y).externalTensor Z)).mapCoalgebra pCS
  let S4 :=
    (((Y.externalTensor X).externalTensor Z)).mapCoalgebra (c53.comp c45)
  let S5 :=
    ((Y.externalTensor (X.externalTensor Z))).mapCoalgebra c53
  let A04 : RightComoduleHom S0 S4 :=
    { toLinearMap := _root_.TensorProduct.map
        (_root_.TensorProduct.comm R M N).toLinearMap (LinearMap.id : P →ₗ[R] P)
      colinear := by
        simpa only [S0, S4, pCS, c04, c45, c53,
          externalTensor_mapCoalgebra_left, mapCoalgebra_comp,
          CoalgHom.comp_assoc,
          RightComoduleHom.mapCoalgebra_toLinearMap, externalTensorCommHom_toLinearMap,
            RightComoduleHom.toLinearMap_externalTensor, RightComoduleHom.id] using
          (((externalTensorCommHom X Y).externalTensor (RightComoduleHom.id Z)).mapCoalgebra
            (c53.comp c45)).colinear }
  let A45 : RightComoduleHom S4 S5 :=
    { toLinearMap := (_root_.TensorProduct.assoc R N M P).toLinearMap
      colinear := by
        simpa only [S4, S5, c45, c53,
          mapCoalgebra_comp,
          RightComoduleHom.mapCoalgebra_toLinearMap, externalTensorAssocHom_toLinearMap] using
          ((externalTensorAssocHom Y X Z).mapCoalgebra c53).colinear }
  let A53 : RightComoduleHom S5 (Y.externalTensor (Z.externalTensor X)) :=
    { toLinearMap := _root_.TensorProduct.map (LinearMap.id : N →ₗ[R] N)
        (_root_.TensorProduct.comm R M P).toLinearMap
      colinear := by
        simpa only [S5, c53,
          externalTensor_mapCoalgebra_right,
          externalTensorCommHom_toLinearMap, RightComoduleHom.toLinearMap_externalTensor,
            RightComoduleHom.id] using
          ((RightComoduleHom.id Y).externalTensor (externalTensorCommHom X Z)).colinear }
  exact A53.comp (A45.comp A04)

/-- The long path has the three prescribed carrier maps. -/
@[simp] theorem externalTensorHexagonLongHom_toLinearMap :
    (externalTensorHexagonLongHom X Y Z).toLinearMap =
      ((_root_.TensorProduct.assoc R N P M).toLinearMap ∘ₗ
      ((_root_.TensorProduct.comm R M (N ⊗[R] P)).toLinearMap ∘ₗ
        (_root_.TensorProduct.assoc R M N P).toLinearMap)) := rfl

/-- The short path has the two tensor symmetries and carrier associator. -/
@[simp] theorem externalTensorHexagonShortHom_toLinearMap :
    (externalTensorHexagonShortHom X Y Z).toLinearMap =
      (_root_.TensorProduct.map (LinearMap.id : N →ₗ[R] N)
      (_root_.TensorProduct.comm R M P).toLinearMap ∘ₗ
      ((_root_.TensorProduct.assoc R N M P).toLinearMap ∘ₗ
        _root_.TensorProduct.map (_root_.TensorProduct.comm R M N).toLinearMap
          (LinearMap.id : P →ₗ[R] P))) := rfl

/-- Evaluate the long path at an arbitrary tensor. -/
@[simp] theorem externalTensorHexagonLongHom_apply (t : (M ⊗[R] N) ⊗[R] P) :
    externalTensorHexagonLongHom X Y Z t = ((_root_.TensorProduct.assoc R N P M).toLinearMap ∘ₗ
      ((_root_.TensorProduct.comm R M (N ⊗[R] P)).toLinearMap ∘ₗ
        (_root_.TensorProduct.assoc R M N P).toLinearMap)) t := rfl

/-- Evaluate the short path at an arbitrary tensor. -/
@[simp] theorem externalTensorHexagonShortHom_apply (t : (M ⊗[R] N) ⊗[R] P) :
    externalTensorHexagonShortHom X Y Z t = (_root_.TensorProduct.map (LinearMap.id : N →ₗ[R] N)
      (_root_.TensorProduct.comm R M P).toLinearMap ∘ₗ
      ((_root_.TensorProduct.assoc R N M P).toLinearMap ∘ₗ
        _root_.TensorProduct.map (_root_.TensorProduct.comm R M N).toLinearMap
          (LinearMap.id : P →ₗ[R] P))) t := rfl

/-- The long path cyclically permutes a pure triple. -/
@[simp] theorem externalTensorHexagonLongHom_tmul (m : M) (n : N) (p : P) :
    externalTensorHexagonLongHom X Y Z ((m ⊗ₜ[R] n) ⊗ₜ[R] p) =
      n ⊗ₜ[R] (p ⊗ₜ[R] m) := rfl

/-- The short path has the same pure-tensor permutation. -/
@[simp] theorem externalTensorHexagonShortHom_tmul (m : M) (n : N) (p : P) :
    externalTensorHexagonShortHom X Y Z ((m ⊗ₜ[R] n) ⊗ₜ[R] p) =
      n ⊗ₜ[R] (p ⊗ₜ[R] m) := rfl

/-- Colinearity of the long carrier path over the final coefficient coalgebra. -/
theorem externalTensorHexagonLongHom_colinear :
    (Y.externalTensor (Z.externalTensor X)).coaction ∘ₗ
      ((_root_.TensorProduct.assoc R N P M).toLinearMap ∘ₗ
      ((_root_.TensorProduct.comm R M (N ⊗[R] P)).toLinearMap ∘ₗ
        (_root_.TensorProduct.assoc R M N P).toLinearMap)) =
      ((_root_.TensorProduct.assoc R N P M).toLinearMap ∘ₗ
        ((_root_.TensorProduct.comm R M (N ⊗[R] P)).toLinearMap ∘ₗ
          (_root_.TensorProduct.assoc R M N P).toLinearMap)).rTensor (D ⊗[R] (E ⊗[R] C)) ∘ₗ
      (((X.externalTensor Y).externalTensor Z).mapCoalgebra
        (show ((C ⊗[R] D) ⊗[R] E) →ₗc[R] D ⊗[R] (E ⊗[R] C) from by
          exact
            (Coalgebra.TensorProduct.map (R := R) (S := R)
              (M := D) (N := D) (P := C ⊗[R] E) (Q := E ⊗[R] C)
              (CoalgHom.id R D)
              (by exact (Coalgebra.TensorProduct.comm R C E).toCoalgHom)).comp
              (((Coalgebra.TensorProduct.assoc R R D C E).toCoalgHom).comp
                (Coalgebra.TensorProduct.map (R := R) (S := R)
                  (M := C ⊗[R] D) (N := D ⊗[R] C) (P := E) (Q := E)
                  (by exact (Coalgebra.TensorProduct.comm R C D).toCoalgHom)
                  (CoalgHom.id R E))))).coaction := by
  simpa only [externalTensorHexagonLongHom_toLinearMap] using
    (externalTensorHexagonLongHom X Y Z).colinear

/-- Colinearity of the short carrier path over the same coefficient coalgebra. -/
theorem externalTensorHexagonShortHom_colinear :
    (Y.externalTensor (Z.externalTensor X)).coaction ∘ₗ
      (_root_.TensorProduct.map (LinearMap.id : N →ₗ[R] N)
      (_root_.TensorProduct.comm R M P).toLinearMap ∘ₗ
      ((_root_.TensorProduct.assoc R N M P).toLinearMap ∘ₗ
        _root_.TensorProduct.map (_root_.TensorProduct.comm R M N).toLinearMap
          (LinearMap.id : P →ₗ[R] P))) =
      (_root_.TensorProduct.map (LinearMap.id : N →ₗ[R] N)
        (_root_.TensorProduct.comm R M P).toLinearMap ∘ₗ
        ((_root_.TensorProduct.assoc R N M P).toLinearMap ∘ₗ
          _root_.TensorProduct.map (_root_.TensorProduct.comm R M N).toLinearMap
            (LinearMap.id : P →ₗ[R] P))).rTensor (D ⊗[R] (E ⊗[R] C)) ∘ₗ
      (((X.externalTensor Y).externalTensor Z).mapCoalgebra
        (show ((C ⊗[R] D) ⊗[R] E) →ₗc[R] D ⊗[R] (E ⊗[R] C) from by
          exact
            (Coalgebra.TensorProduct.map (R := R) (S := R)
              (M := D) (N := D) (P := C ⊗[R] E) (Q := E ⊗[R] C)
              (CoalgHom.id R D)
              (by exact (Coalgebra.TensorProduct.comm R C E).toCoalgHom)).comp
              (((Coalgebra.TensorProduct.assoc R R D C E).toCoalgHom).comp
                (Coalgebra.TensorProduct.map (R := R) (S := R)
                  (M := C ⊗[R] D) (N := D ⊗[R] C) (P := E) (Q := E)
                  (by exact (Coalgebra.TensorProduct.comm R C D).toCoalgHom)
                  (CoalgHom.id R E))))).coaction := by
  simpa only [externalTensorHexagonShortHom_toLinearMap] using
    (externalTensorHexagonShortHom X Y Z).colinear

/-- The homogeneous Hom hexagon, following Mathlib's tensor carrier hexagon proof. -/
theorem externalTensor_hexagon :
    externalTensorHexagonLongHom X Y Z = externalTensorHexagonShortHom X Y Z := by
  apply RightComoduleHom.toLinearMap_injective
  change (externalTensorHexagonLongHom X Y Z).toLinearMap =
    (externalTensorHexagonShortHom X Y Z).toLinearMap
  rw [externalTensorHexagonLongHom_toLinearMap, externalTensorHexagonShortHom_toLinearMap]
  apply _root_.TensorProduct.ext_threefold
  intro m n p
  rfl

-- Reverse the existing edges over the OLD final coefficient, before reindexing.
private def hexagonLongInvHom : RightComoduleHom (B3 X Y Z) (S0 X Y Z) := by
  let A10 : RightComoduleHom (S1 X Y Z) (S0 X Y Z) :=
    { toLinearMap := (_root_.TensorProduct.assoc R M N P).symm.toLinearMap
      colinear := by
        simpa only [mapCoalgebra_comp, CoalgHom.comp_assoc,
          Coalgebra.TensorProduct.comm_hexagon,
          RightComoduleHom.mapCoalgebra_toLinearMap, externalTensorAssocInvHom_toLinearMap] using
          ((externalTensorAssocInvHom X Y Z).mapCoalgebra
            ((c23 R C D E).comp (c12 R C D E))).colinear }
  let A21 : RightComoduleHom (S2 X Y Z) (S1 X Y Z) :=
    { toLinearMap := (_root_.TensorProduct.comm R M (N ⊗[R] P)).symm.toLinearMap
      colinear := by
        simpa only [mapCoalgebra_comp,
          RightComoduleHom.mapCoalgebra_toLinearMap, externalTensorCommInvHom_toLinearMap] using
          ((externalTensorCommInvHom X (Y.externalTensor Z)).mapCoalgebra (c23 R C D E)).colinear
            }
  let A32 : RightComoduleHom (B3 X Y Z) (S2 X Y Z) := externalTensorAssocInvHom Y Z X
  exact A10.comp (A21.comp A32)

private def hexagonShortInvHom : RightComoduleHom (B3 X Y Z) (S0 X Y Z) := by
  let A40 : RightComoduleHom (S4 X Y Z) (S0 X Y Z) :=
    { toLinearMap := _root_.TensorProduct.map
        (_root_.TensorProduct.comm R M N).symm.toLinearMap (LinearMap.id : P →ₗ[R] P)
      colinear := by
        simpa only [externalTensor_mapCoalgebra_left, mapCoalgebra_comp,
          CoalgHom.comp_assoc,
          RightComoduleHom.mapCoalgebra_toLinearMap, externalTensorCommInvHom_toLinearMap,
            RightComoduleHom.toLinearMap_externalTensor, RightComoduleHom.id] using
          (((externalTensorCommInvHom X Y).externalTensor (RightComoduleHom.id Z)).mapCoalgebra
            ((c53 R C D E).comp (c45 R C D E))).colinear }
  let A54 : RightComoduleHom (S5 X Y Z) (S4 X Y Z) :=
    { toLinearMap := (_root_.TensorProduct.assoc R N M P).symm.toLinearMap
      colinear := by
        simpa only [mapCoalgebra_comp,
          RightComoduleHom.mapCoalgebra_toLinearMap, externalTensorAssocInvHom_toLinearMap] using
          ((externalTensorAssocInvHom Y X Z).mapCoalgebra (c53 R C D E)).colinear }
  let A35 : RightComoduleHom (B3 X Y Z) (S5 X Y Z) :=
    { toLinearMap := _root_.TensorProduct.map (LinearMap.id : N →ₗ[R] N)
        (_root_.TensorProduct.comm R M P).symm.toLinearMap
      colinear := by
        simpa only [externalTensor_mapCoalgebra_right,
          externalTensorCommInvHom_toLinearMap, RightComoduleHom.toLinearMap_externalTensor,
            RightComoduleHom.id] using
          ((RightComoduleHom.id Y).externalTensor (externalTensorCommInvHom X Z)).colinear }
  exact A40.comp (A54.comp A35)

private theorem hexagonLongInvHom_tmul (m : M) (n : N) (p : P) :
    hexagonLongInvHom X Y Z (n ⊗ₜ[R] (p ⊗ₜ[R] m)) =
      (m ⊗ₜ[R] n) ⊗ₜ[R] p := rfl

private theorem hexagonShortInvHom_tmul (m : M) (n : N) (p : P) :
    hexagonShortInvHom X Y Z (n ⊗ₜ[R] (p ⊗ₜ[R] m)) =
      (m ⊗ₜ[R] n) ⊗ₜ[R] p := rfl

private theorem hexagon_inv : hexagonLongInvHom X Y Z = hexagonShortInvHom X Y Z := by
  have hL : (hexagonLongInvHom X Y Z).toLinearMap ∘ₗ
      (externalTensorHexagonLongHom X Y Z).toLinearMap = LinearMap.id := by
    apply _root_.TensorProduct.ext_threefold
    intro m n p
    change hexagonLongInvHom X Y Z
      (externalTensorHexagonLongHom X Y Z ((m ⊗ₜ[R] n) ⊗ₜ[R] p)) =
        (m ⊗ₜ[R] n) ⊗ₜ[R] p
    rw [externalTensorHexagonLongHom_tmul, hexagonLongInvHom_tmul]
  have hS : (externalTensorHexagonShortHom X Y Z).toLinearMap ∘ₗ
      (hexagonShortInvHom X Y Z).toLinearMap = LinearMap.id := by
    apply _root_.TensorProduct.ext_threefold'
    intro n p m
    change externalTensorHexagonShortHom X Y Z
      (hexagonShortInvHom X Y Z (n ⊗ₜ[R] (p ⊗ₜ[R] m))) =
        n ⊗ₜ[R] (p ⊗ₜ[R] m)
    rw [hexagonShortInvHom_tmul, externalTensorHexagonShortHom_tmul]
  apply RightComoduleHom.toLinearMap_injective
  calc
    (hexagonLongInvHom X Y Z).toLinearMap =
        (hexagonLongInvHom X Y Z).toLinearMap ∘ₗ
          ((externalTensorHexagonShortHom X Y Z).toLinearMap ∘ₗ
            (hexagonShortInvHom X Y Z).toLinearMap) := by rw [hS]; rfl
    _ = (hexagonLongInvHom X Y Z).toLinearMap ∘ₗ
          ((externalTensorHexagonLongHom X Y Z).toLinearMap ∘ₗ
            (hexagonShortInvHom X Y Z).toLinearMap) := by
      rw [externalTensor_hexagon X Y Z]
    _ = (hexagonShortInvHom X Y Z).toLinearMap := by
      rw [← LinearMap.comp_assoc, hL]
      rfl

end Hexagon

section Reverse

variable (X : RightComodule R C M) (Y : RightComodule R D N)
variable (Z : RightComodule R E P)

private abbrev d12 (R : Type uR) [CommSemiring R]
    (C : Type uC) [AddCommMonoid C] [Module R C] [Coalgebra R C]
    (D : Type uD) [AddCommMonoid D] [Module R D] [Coalgebra R D]
    (E : Type uE) [AddCommMonoid E] [Module R E] [Coalgebra R E] :=
  (Coalgebra.TensorProduct.comm R E (C ⊗[R] D)).toCoalgHom

private abbrev d23 (R : Type uR) [CommSemiring R]
    (C : Type uC) [AddCommMonoid C] [Module R C] [Coalgebra R C]
    (D : Type uD) [AddCommMonoid D] [Module R D] [Coalgebra R D]
    (E : Type uE) [AddCommMonoid E] [Module R E] [Coalgebra R E] :=
  (Coalgebra.TensorProduct.assoc R R C D E).toCoalgHom

private abbrev d04 (R : Type uR) [CommSemiring R]
    (C : Type uC) [AddCommMonoid C] [Module R C] [Coalgebra R C]
    (D : Type uD) [AddCommMonoid D] [Module R D] [Coalgebra R D]
    (E : Type uE) [AddCommMonoid E] [Module R E] [Coalgebra R E] :=
  show ((E ⊗[R] C) ⊗[R] D) →ₗc[R] ((C ⊗[R] E) ⊗[R] D) from by
    exact
      Coalgebra.TensorProduct.map (R := R) (S := R)
        (M := E ⊗[R] C) (N := C ⊗[R] E) (P := D) (Q := D)
        (by exact (Coalgebra.TensorProduct.comm R E C).toCoalgHom) (CoalgHom.id R D)

private abbrev d45 (R : Type uR) [CommSemiring R]
    (C : Type uC) [AddCommMonoid C] [Module R C] [Coalgebra R C]
    (D : Type uD) [AddCommMonoid D] [Module R D] [Coalgebra R D]
    (E : Type uE) [AddCommMonoid E] [Module R E] [Coalgebra R E] :=
  (Coalgebra.TensorProduct.assoc R R C E D).toCoalgHom

private abbrev d53 (R : Type uR) [CommSemiring R]
    (C : Type uC) [AddCommMonoid C] [Module R C] [Coalgebra R C]
    (D : Type uD) [AddCommMonoid D] [Module R D] [Coalgebra R D]
    (E : Type uE) [AddCommMonoid E] [Module R E] [Coalgebra R E] :=
  show C ⊗[R] (E ⊗[R] D) →ₗc[R] C ⊗[R] (D ⊗[R] E) from by
    exact
      Coalgebra.TensorProduct.map (R := R) (S := R)
        (M := C) (N := C) (P := E ⊗[R] D) (Q := D ⊗[R] E)
        (CoalgHom.id R C) (by exact (Coalgebra.TensorProduct.comm R E D).toCoalgHom)

private abbrev dP (R : Type uR) [CommSemiring R]
    (C : Type uC) [AddCommMonoid C] [Module R C] [Coalgebra R C]
    (D : Type uD) [AddCommMonoid D] [Module R D] [Coalgebra R D]
    (E : Type uE) [AddCommMonoid E] [Module R E] [Coalgebra R E] :=
  show ((E ⊗[R] C) ⊗[R] D) →ₗc[R] C ⊗[R] (D ⊗[R] E) from by
    exact
      (d53 R C D E).comp ((d45 R C D E).comp (d04 R C D E))

private abbrev q (R : Type uR) [CommSemiring R]
    (C : Type uC) [AddCommMonoid C] [Module R C] [Coalgebra R C]
    (D : Type uD) [AddCommMonoid D] [Module R D] [Coalgebra R D]
    (E : Type uE) [AddCommMonoid E] [Module R E] [Coalgebra R E] :=
  show C ⊗[R] (D ⊗[R] E) →ₗc[R] ((E ⊗[R] C) ⊗[R] D) from by
    exact
      (Coalgebra.TensorProduct.map (R := R) (S := R)
        (M := C ⊗[R] E) (N := E ⊗[R] C) (P := D) (Q := D)
        (by exact (Coalgebra.TensorProduct.comm R C E).toCoalgHom) (CoalgHom.id R D)).comp
        ((Coalgebra.TensorProduct.assoc R R C E D).symm.toCoalgHom.comp
          (Coalgebra.TensorProduct.map (R := R) (S := R)
            (M := C) (N := C) (P := D ⊗[R] E) (Q := E ⊗[R] D)
            (CoalgHom.id R C) (by exact (Coalgebra.TensorProduct.comm R D E).toCoalgHom)))

private abbrev V0 (X : RightComodule R C M) (Y : RightComodule R D N)
    (Z : RightComodule R E P) :=
  (Z.externalTensor X).externalTensor Y

private abbrev V1 (X : RightComodule R C M) (Y : RightComodule R D N)
    (Z : RightComodule R E P) :=
  Z.externalTensor (X.externalTensor Y)

private abbrev V2 (X : RightComodule R C M) (Y : RightComodule R D N)
    (Z : RightComodule R E P) :=
  (X.externalTensor Y).externalTensor Z

private abbrev V3 (X : RightComodule R C M) (Y : RightComodule R D N)
    (Z : RightComodule R E P) :=
  X.externalTensor (Y.externalTensor Z)

private abbrev V4 (X : RightComodule R C M) (Y : RightComodule R D N)
    (Z : RightComodule R E P) :=
  (X.externalTensor Z).externalTensor Y

private abbrev V5 (X : RightComodule R C M) (Y : RightComodule R D N)
    (Z : RightComodule R E P) :=
  X.externalTensor (Z.externalTensor Y)

private abbrev O0 (X : RightComodule R C M) (Y : RightComodule R D N)
    (Z : RightComodule R E P) :=
  (V0 X Y Z).mapCoalgebra (dP R C D E)

private abbrev O1 (X : RightComodule R C M) (Y : RightComodule R D N)
    (Z : RightComodule R E P) :=
  (V1 X Y Z).mapCoalgebra ((d23 R C D E).comp (d12 R C D E))

private abbrev O2 (X : RightComodule R C M) (Y : RightComodule R D N)
    (Z : RightComodule R E P) :=
  (V2 X Y Z).mapCoalgebra (d23 R C D E)

private abbrev O4 (X : RightComodule R C M) (Y : RightComodule R D N)
    (Z : RightComodule R E P) :=
  (V4 X Y Z).mapCoalgebra ((d53 R C D E).comp (d45 R C D E))

private abbrev O5 (X : RightComodule R C M) (Y : RightComodule R D N)
    (Z : RightComodule R E P) :=
  (V5 X Y Z).mapCoalgebra (d53 R C D E)

private theorem hexagon_reverse_cancel : (q R C D E).comp (dP R C D E) =
    CoalgHom.id R ((E ⊗[R] C) ⊗[R] D) := by
  apply CoalgHom.coe_linearMap_injective
  apply _root_.TensorProduct.ext_threefold
  exact fun (e : E) (c : C) (d : D) => rfl

private theorem hexagon_reverse_target : (O0 X Y Z).mapCoalgebra (q R C D E) = (V0 X Y Z) := by
  rw [mapCoalgebra_comp, hexagon_reverse_cancel, mapCoalgebra_id]

-- Reverse over the old final coefficient, then reindex each edge by the inverse path.
/-- The reversed long hexagon path, with all six vertices changed along the inverse
short coefficient path to `(E ⊗ C) ⊗ D`. -/
def externalTensorHexagonReverseLongHom :
    RightComoduleHom
      ((X.externalTensor (Y.externalTensor Z)).mapCoalgebra
        (show C ⊗[R] (D ⊗[R] E) →ₗc[R] ((E ⊗[R] C) ⊗[R] D) from by
          exact
            (Coalgebra.TensorProduct.map (R := R) (S := R)
              (M := C ⊗[R] E) (N := E ⊗[R] C) (P := D) (Q := D)
              (by exact (Coalgebra.TensorProduct.comm R C E).toCoalgHom)
              (CoalgHom.id R D)).comp
              ((Coalgebra.TensorProduct.assoc R R C E D).symm.toCoalgHom.comp
                (Coalgebra.TensorProduct.map (R := R) (S := R)
                  (M := C) (N := C) (P := D ⊗[R] E) (Q := E ⊗[R] D)
                  (CoalgHom.id R C)
                  (by exact (Coalgebra.TensorProduct.comm R D E).toCoalgHom)))))
      ((Z.externalTensor X).externalTensor Y) := by
  let d12 :=
    (Coalgebra.TensorProduct.comm R E (C ⊗[R] D)).toCoalgHom
  let d23 :=
    (Coalgebra.TensorProduct.assoc R R C D E).toCoalgHom
  let d04 :=
    show ((E ⊗[R] C) ⊗[R] D) →ₗc[R] ((C ⊗[R] E) ⊗[R] D) from by
      exact
        Coalgebra.TensorProduct.map (R := R) (S := R)
          (M := E ⊗[R] C) (N := C ⊗[R] E) (P := D) (Q := D)
          (by exact (Coalgebra.TensorProduct.comm R E C).toCoalgHom) (CoalgHom.id R D)
  let d45 :=
    (Coalgebra.TensorProduct.assoc R R C E D).toCoalgHom
  let d53 :=
    show C ⊗[R] (E ⊗[R] D) →ₗc[R] C ⊗[R] (D ⊗[R] E) from by
      exact
        Coalgebra.TensorProduct.map (R := R) (S := R)
          (M := C) (N := C) (P := E ⊗[R] D) (Q := D ⊗[R] E)
          (CoalgHom.id R C) (by exact (Coalgebra.TensorProduct.comm R E D).toCoalgHom)
  let dP :=
    show ((E ⊗[R] C) ⊗[R] D) →ₗc[R] C ⊗[R] (D ⊗[R] E) from by
      exact
        d53.comp (d45.comp d04)
  let q :=
    show C ⊗[R] (D ⊗[R] E) →ₗc[R] ((E ⊗[R] C) ⊗[R] D) from by
      exact
        (Coalgebra.TensorProduct.map (R := R) (S := R)
          (M := C ⊗[R] E) (N := E ⊗[R] C) (P := D) (Q := D)
          (by exact (Coalgebra.TensorProduct.comm R C E).toCoalgHom) (CoalgHom.id R D)).comp
          ((Coalgebra.TensorProduct.assoc R R C E D).symm.toCoalgHom.comp
            (Coalgebra.TensorProduct.map (R := R) (S := R)
              (M := C) (N := C) (P := D ⊗[R] E) (Q := E ⊗[R] D)
              (CoalgHom.id R C) (by exact (Coalgebra.TensorProduct.comm R D E).toCoalgHom)))
  let O0 :=
    (((Z.externalTensor X).externalTensor Y)).mapCoalgebra dP
  let O1 :=
    ((Z.externalTensor (X.externalTensor Y))).mapCoalgebra (d23.comp d12)
  let O2 :=
    (((X.externalTensor Y).externalTensor Z)).mapCoalgebra d23
  let A10 : RightComoduleHom O1 O0 :=
    { toLinearMap := (_root_.TensorProduct.assoc R P M N).symm.toLinearMap
      colinear := by
        simpa only [O0, O1, dP, d12, d23, d04, d45, d53,
          mapCoalgebra_comp, CoalgHom.comp_assoc,
          Coalgebra.TensorProduct.comm_hexagon,
          RightComoduleHom.mapCoalgebra_toLinearMap, externalTensorAssocInvHom_toLinearMap] using
          ((externalTensorAssocInvHom Z X Y).mapCoalgebra
            (d23.comp d12)).colinear }
  let A21 : RightComoduleHom O2 O1 :=
    { toLinearMap := (_root_.TensorProduct.comm R P (M ⊗[R] N)).symm.toLinearMap
      colinear := by
        simpa only [O1, O2, d12, d23,
          mapCoalgebra_comp,
          RightComoduleHom.mapCoalgebra_toLinearMap, externalTensorCommInvHom_toLinearMap] using
          ((externalTensorCommInvHom Z (X.externalTensor Y)).mapCoalgebra d23).colinear }
  let A32 : RightComoduleHom (X.externalTensor (Y.externalTensor Z)) O2 :=
    externalTensorAssocInvHom X Y Z
  let A10q : RightComoduleHom (O1.mapCoalgebra q) (((Z.externalTensor X).externalTensor Y)) :=
    { toLinearMap := A10.toLinearMap
      colinear := by
        simpa only [O0, O1, dP, d12, d23, d04, d45, d53, q,
          hexagon_reverse_target,
          RightComoduleHom.mapCoalgebra_toLinearMap] using (A10.mapCoalgebra q).colinear }
  let A21q : RightComoduleHom (O2.mapCoalgebra q)
      (O1.mapCoalgebra q) :=
    A21.mapCoalgebra q
  let A32q : RightComoduleHom ((X.externalTensor (Y.externalTensor Z)).mapCoalgebra q)
      (O2.mapCoalgebra q) :=
    A32.mapCoalgebra q
  exact A10q.comp (A21q.comp A32q)

/-- The reversed short hexagon path over `(E ⊗ C) ⊗ D`, obtained by changing
each reversed edge along the inverse short coefficient path. -/
def externalTensorHexagonReverseShortHom :
    RightComoduleHom
      ((X.externalTensor (Y.externalTensor Z)).mapCoalgebra
        (show C ⊗[R] (D ⊗[R] E) →ₗc[R] ((E ⊗[R] C) ⊗[R] D) from by
          exact
            (Coalgebra.TensorProduct.map (R := R) (S := R)
              (M := C ⊗[R] E) (N := E ⊗[R] C) (P := D) (Q := D)
              (by exact (Coalgebra.TensorProduct.comm R C E).toCoalgHom)
              (CoalgHom.id R D)).comp
              ((Coalgebra.TensorProduct.assoc R R C E D).symm.toCoalgHom.comp
                (Coalgebra.TensorProduct.map (R := R) (S := R)
                  (M := C) (N := C) (P := D ⊗[R] E) (Q := E ⊗[R] D)
                  (CoalgHom.id R C)
                  (by exact (Coalgebra.TensorProduct.comm R D E).toCoalgHom)))))
      ((Z.externalTensor X).externalTensor Y) := by
  let d04 :=
    show ((E ⊗[R] C) ⊗[R] D) →ₗc[R] ((C ⊗[R] E) ⊗[R] D) from by
      exact
        Coalgebra.TensorProduct.map (R := R) (S := R)
          (M := E ⊗[R] C) (N := C ⊗[R] E) (P := D) (Q := D)
          (by exact (Coalgebra.TensorProduct.comm R E C).toCoalgHom) (CoalgHom.id R D)
  let d45 :=
    (Coalgebra.TensorProduct.assoc R R C E D).toCoalgHom
  let d53 :=
    show C ⊗[R] (E ⊗[R] D) →ₗc[R] C ⊗[R] (D ⊗[R] E) from by
      exact
        Coalgebra.TensorProduct.map (R := R) (S := R)
          (M := C) (N := C) (P := E ⊗[R] D) (Q := D ⊗[R] E)
          (CoalgHom.id R C) (by exact (Coalgebra.TensorProduct.comm R E D).toCoalgHom)
  let dP :=
    show ((E ⊗[R] C) ⊗[R] D) →ₗc[R] C ⊗[R] (D ⊗[R] E) from by
      exact
        d53.comp (d45.comp d04)
  let q :=
    show C ⊗[R] (D ⊗[R] E) →ₗc[R] ((E ⊗[R] C) ⊗[R] D) from by
      exact
        (Coalgebra.TensorProduct.map (R := R) (S := R)
          (M := C ⊗[R] E) (N := E ⊗[R] C) (P := D) (Q := D)
          (by exact (Coalgebra.TensorProduct.comm R C E).toCoalgHom) (CoalgHom.id R D)).comp
          ((Coalgebra.TensorProduct.assoc R R C E D).symm.toCoalgHom.comp
            (Coalgebra.TensorProduct.map (R := R) (S := R)
              (M := C) (N := C) (P := D ⊗[R] E) (Q := E ⊗[R] D)
              (CoalgHom.id R C) (by exact (Coalgebra.TensorProduct.comm R D E).toCoalgHom)))
  let O0 :=
    (((Z.externalTensor X).externalTensor Y)).mapCoalgebra dP
  let O4 :=
    (((X.externalTensor Z).externalTensor Y)).mapCoalgebra (d53.comp d45)
  let O5 :=
    ((X.externalTensor (Z.externalTensor Y))).mapCoalgebra d53
  let A40 : RightComoduleHom O4 O0 :=
    { toLinearMap := _root_.TensorProduct.map
        (_root_.TensorProduct.comm R P M).symm.toLinearMap (LinearMap.id : N →ₗ[R] N)
      colinear := by
        simpa only [O0, O4, dP, d04, d45, d53,
          externalTensor_mapCoalgebra_left, mapCoalgebra_comp,
          CoalgHom.comp_assoc,
          RightComoduleHom.mapCoalgebra_toLinearMap, externalTensorCommInvHom_toLinearMap,
            RightComoduleHom.toLinearMap_externalTensor, RightComoduleHom.id] using
          (((externalTensorCommInvHom Z X).externalTensor (RightComoduleHom.id Y)).mapCoalgebra
            (d53.comp d45)).colinear }
  let A54 : RightComoduleHom O5 O4 :=
    { toLinearMap := (_root_.TensorProduct.assoc R M P N).symm.toLinearMap
      colinear := by
        simpa only [O4, O5, d45, d53,
          mapCoalgebra_comp,
          RightComoduleHom.mapCoalgebra_toLinearMap, externalTensorAssocInvHom_toLinearMap] using
          ((externalTensorAssocInvHom X Z Y).mapCoalgebra d53).colinear }
  let A35 : RightComoduleHom (X.externalTensor (Y.externalTensor Z)) O5 :=
    { toLinearMap := _root_.TensorProduct.map (LinearMap.id : M →ₗ[R] M)
        (_root_.TensorProduct.comm R P N).symm.toLinearMap
      colinear := by
        simpa only [O5, d53,
          externalTensor_mapCoalgebra_right,
          externalTensorCommInvHom_toLinearMap, RightComoduleHom.toLinearMap_externalTensor,
            RightComoduleHom.id] using
          ((RightComoduleHom.id X).externalTensor (externalTensorCommInvHom Z Y)).colinear }
  let A40q : RightComoduleHom (O4.mapCoalgebra q) (((Z.externalTensor X).externalTensor Y)) :=
    { toLinearMap := A40.toLinearMap
      colinear := by
        simpa only [O0, O4, dP, d04, d45, d53, q,
          hexagon_reverse_target,
          RightComoduleHom.mapCoalgebra_toLinearMap] using (A40.mapCoalgebra q).colinear }
  let A54q : RightComoduleHom (O5.mapCoalgebra q)
      (O4.mapCoalgebra q) :=
    A54.mapCoalgebra q
  let A35q : RightComoduleHom ((X.externalTensor (Y.externalTensor Z)).mapCoalgebra q)
      (O5.mapCoalgebra q) :=
    A35.mapCoalgebra q
  exact A40q.comp (A54q.comp A35q)

/-- The dual Hom hexagon is the inverse of the relabelled forward one, reindexed
along the inverse short coefficient path at every vertex and edge. -/
theorem externalTensor_hexagon_reverse :
    externalTensorHexagonReverseLongHom X Y Z = externalTensorHexagonReverseShortHom X Y Z := by
  let d04 :=
    show ((E ⊗[R] C) ⊗[R] D) →ₗc[R] ((C ⊗[R] E) ⊗[R] D) from by
      exact
        Coalgebra.TensorProduct.map (R := R) (S := R)
          (M := E ⊗[R] C) (N := C ⊗[R] E) (P := D) (Q := D)
          (by exact (Coalgebra.TensorProduct.comm R E C).toCoalgHom) (CoalgHom.id R D)
  let d45 :=
    (Coalgebra.TensorProduct.assoc R R C E D).toCoalgHom
  let d53 :=
    show C ⊗[R] (E ⊗[R] D) →ₗc[R] C ⊗[R] (D ⊗[R] E) from by
      exact
        Coalgebra.TensorProduct.map (R := R) (S := R)
          (M := C) (N := C) (P := E ⊗[R] D) (Q := D ⊗[R] E)
          (CoalgHom.id R C) (by exact (Coalgebra.TensorProduct.comm R E D).toCoalgHom)
  let dP :=
    show ((E ⊗[R] C) ⊗[R] D) →ₗc[R] C ⊗[R] (D ⊗[R] E) from by
      exact
        d53.comp (d45.comp d04)
  let q :=
    show C ⊗[R] (D ⊗[R] E) →ₗc[R] ((E ⊗[R] C) ⊗[R] D) from by
      exact
        (Coalgebra.TensorProduct.map (R := R) (S := R)
          (M := C ⊗[R] E) (N := E ⊗[R] C) (P := D) (Q := D)
          (by exact (Coalgebra.TensorProduct.comm R C E).toCoalgHom) (CoalgHom.id R D)).comp
          ((Coalgebra.TensorProduct.assoc R R C E D).symm.toCoalgHom.comp
            (Coalgebra.TensorProduct.map (R := R) (S := R)
              (M := C) (N := C) (P := D ⊗[R] E) (Q := E ⊗[R] D)
              (CoalgHom.id R C) (by exact (Coalgebra.TensorProduct.comm R D E).toCoalgHom)))
  let O0 :=
    (((Z.externalTensor X).externalTensor Y)).mapCoalgebra dP
  have h := congrArg (fun f : RightComoduleHom (X.externalTensor (Y.externalTensor Z)) O0 =>
    (f.mapCoalgebra q).toLinearMap) (hexagon_inv Z X Y)
  apply RightComoduleHom.toLinearMap_injective
  change (externalTensorHexagonReverseLongHom X Y Z).toLinearMap =
    (externalTensorHexagonReverseShortHom X Y Z).toLinearMap
  -- Coefficient change preserves the three inverse-edge carrier maps.
  calc
    (externalTensorHexagonReverseLongHom X Y Z).toLinearMap =
        ((hexagonLongInvHom Z X Y).mapCoalgebra q).toLinearMap := by rfl
    _ = ((hexagonShortInvHom Z X Y).mapCoalgebra q).toLinearMap := h
    _ = (externalTensorHexagonReverseShortHom X Y Z).toLinearMap := by rfl

/-- The long reversed Hom has the inverse-associator/symmetry carrier path. -/
theorem externalTensor_hexagon_reverse_long_toLinearMap :
    (externalTensorHexagonReverseLongHom X Y Z).toLinearMap =
      ((_root_.TensorProduct.assoc R P M N).symm.toLinearMap ∘ₗ
      ((_root_.TensorProduct.comm R (M ⊗[R] N) P).toLinearMap ∘ₗ
        (_root_.TensorProduct.assoc R M N P).symm.toLinearMap)) := rfl

/-- The short reversed Hom has the reversed tensor-symmetry carrier path. -/
theorem externalTensor_hexagon_reverse_short_toLinearMap :
    (externalTensorHexagonReverseShortHom X Y Z).toLinearMap = (_root_.TensorProduct.map
      (_root_.TensorProduct.comm R M P).toLinearMap (LinearMap.id : N →ₗ[R] N) ∘ₗ
      ((_root_.TensorProduct.assoc R M P N).symm.toLinearMap ∘ₗ
        _root_.TensorProduct.map (LinearMap.id : M →ₗ[R] M)
          (_root_.TensorProduct.comm R N P).toLinearMap)) := rfl

/-- Whole carrier-map coherence read back from the derived dual Hom law. -/
theorem externalTensor_hexagon_reverse_carrier :
    (externalTensorHexagonReverseLongHom X Y Z).toLinearMap = (_root_.TensorProduct.map
      (_root_.TensorProduct.comm R M P).toLinearMap (LinearMap.id : N →ₗ[R] N) ∘ₗ
      ((_root_.TensorProduct.assoc R M P N).symm.toLinearMap ∘ₗ
        _root_.TensorProduct.map (LinearMap.id : M →ₗ[R] M)
          (_root_.TensorProduct.comm R N P).toLinearMap)) :=
  (congrArg RightComoduleHom.toLinearMap (externalTensor_hexagon_reverse X Y Z)).trans
    (externalTensor_hexagon_reverse_short_toLinearMap X Y Z)

/-- Evaluate the long reversed path at any tensor, not just a pure tensor. -/
theorem externalTensor_hexagon_reverse_long_apply (t : M ⊗[R] (N ⊗[R] P)) :
    externalTensorHexagonReverseLongHom X Y Z t =
      ((_root_.TensorProduct.assoc R P M N).symm.toLinearMap ∘ₗ
      ((_root_.TensorProduct.comm R (M ⊗[R] N) P).toLinearMap ∘ₗ
        (_root_.TensorProduct.assoc R M N P).symm.toLinearMap)) t := rfl

/-- Evaluate the short reversed path at an arbitrary tensor. -/
theorem externalTensor_hexagon_reverse_short_apply (t : M ⊗[R] (N ⊗[R] P)) :
    externalTensorHexagonReverseShortHom X Y Z t = (_root_.TensorProduct.map
      (_root_.TensorProduct.comm R M P).toLinearMap (LinearMap.id : N →ₗ[R] N) ∘ₗ
      ((_root_.TensorProduct.assoc R M P N).symm.toLinearMap ∘ₗ
        _root_.TensorProduct.map (LinearMap.id : M →ₗ[R] M)
          (_root_.TensorProduct.comm R N P).toLinearMap)) t := rfl

/-- The long derived dual path sends `m ⊗ (n ⊗ p)` to `(p ⊗ m) ⊗ n`. -/
theorem externalTensor_hexagon_reverse_long_tmul (m : M) (n : N) (p : P) :
    externalTensorHexagonReverseLongHom X Y Z (m ⊗ₜ[R] (n ⊗ₜ[R] p)) =
      (p ⊗ₜ[R] m) ⊗ₜ[R] n := rfl

/-- The short derived dual path has the same pure-tensor readback. -/
theorem externalTensor_hexagon_reverse_short_tmul (m : M) (n : N) (p : P) :
    externalTensorHexagonReverseShortHom X Y Z (m ⊗ₜ[R] (n ⊗ₜ[R] p)) =
      (p ⊗ₜ[R] m) ⊗ₜ[R] n := rfl

/-- The long dual carrier path is colinear over `(E ⊗ C) ⊗ D`. -/
theorem externalTensor_hexagon_reverse_long_colinear :
    ((Z.externalTensor X).externalTensor Y).coaction ∘ₗ
      ((_root_.TensorProduct.assoc R P M N).symm.toLinearMap ∘ₗ
      ((_root_.TensorProduct.comm R (M ⊗[R] N) P).toLinearMap ∘ₗ
        (_root_.TensorProduct.assoc R M N P).symm.toLinearMap)) =
      ((_root_.TensorProduct.assoc R P M N).symm.toLinearMap ∘ₗ
      ((_root_.TensorProduct.comm R (M ⊗[R] N) P).toLinearMap ∘ₗ
        (_root_.TensorProduct.assoc R M N P).symm.toLinearMap)).rTensor ((E ⊗[R] C) ⊗[R] D) ∘ₗ
      ((X.externalTensor (Y.externalTensor Z)).mapCoalgebra
        (show C ⊗[R] (D ⊗[R] E) →ₗc[R] ((E ⊗[R] C) ⊗[R] D) from by
          exact
            (Coalgebra.TensorProduct.map (R := R) (S := R)
              (M := C ⊗[R] E) (N := E ⊗[R] C) (P := D) (Q := D)
              (by exact (Coalgebra.TensorProduct.comm R C E).toCoalgHom)
              (CoalgHom.id R D)).comp
              ((Coalgebra.TensorProduct.assoc R R C E D).symm.toCoalgHom.comp
                (Coalgebra.TensorProduct.map (R := R) (S := R)
                  (M := C) (N := C) (P := D ⊗[R] E) (Q := E ⊗[R] D)
                  (CoalgHom.id R C)
                  (by exact (Coalgebra.TensorProduct.comm R D E).toCoalgHom))))).coaction := by
  simpa only [externalTensor_hexagon_reverse_long_toLinearMap] using
    (externalTensorHexagonReverseLongHom X Y Z).colinear

/-- The short dual carrier path is colinear over the same final coalgebra. -/
theorem externalTensor_hexagon_reverse_short_colinear :
    ((Z.externalTensor X).externalTensor Y).coaction ∘ₗ (_root_.TensorProduct.map
      (_root_.TensorProduct.comm R M P).toLinearMap (LinearMap.id : N →ₗ[R] N) ∘ₗ
      ((_root_.TensorProduct.assoc R M P N).symm.toLinearMap ∘ₗ
        _root_.TensorProduct.map (LinearMap.id : M →ₗ[R] M)
          (_root_.TensorProduct.comm R N P).toLinearMap)) = (_root_.TensorProduct.map
      (_root_.TensorProduct.comm R M P).toLinearMap (LinearMap.id : N →ₗ[R] N) ∘ₗ
      ((_root_.TensorProduct.assoc R M P N).symm.toLinearMap ∘ₗ
        _root_.TensorProduct.map (LinearMap.id : M →ₗ[R] M)
          (_root_.TensorProduct.comm R N P).toLinearMap)).rTensor ((E ⊗[R] C) ⊗[R] D) ∘ₗ
      ((X.externalTensor (Y.externalTensor Z)).mapCoalgebra
        (show C ⊗[R] (D ⊗[R] E) →ₗc[R] ((E ⊗[R] C) ⊗[R] D) from by
          exact
            (Coalgebra.TensorProduct.map (R := R) (S := R)
              (M := C ⊗[R] E) (N := E ⊗[R] C) (P := D) (Q := D)
              (by exact (Coalgebra.TensorProduct.comm R C E).toCoalgHom)
              (CoalgHom.id R D)).comp
              ((Coalgebra.TensorProduct.assoc R R C E D).symm.toCoalgHom.comp
                (Coalgebra.TensorProduct.map (R := R) (S := R)
                  (M := C) (N := C) (P := D ⊗[R] E) (Q := E ⊗[R] D)
                  (CoalgHom.id R C)
                  (by exact (Coalgebra.TensorProduct.comm R D E).toCoalgHom))))).coaction := by
  simpa only [externalTensor_hexagon_reverse_short_toLinearMap] using
    (externalTensorHexagonReverseShortHom X Y Z).colinear

end Reverse

section Unit

variable (X : RightComodule R C M)

private abbrev lC (R : Type uR) [CommSemiring R]
    (C : Type uC) [AddCommMonoid C] [Module R C] [Coalgebra R C] :=
  (Coalgebra.TensorProduct.lid R C).toCoalgHom

private abbrev rC (R : Type uR) [CommSemiring R]
    (C : Type uC) [AddCommMonoid C] [Module R C] [Coalgebra R C] :=
  (Coalgebra.TensorProduct.rid R R C).toCoalgHom

private abbrev L0 (X : RightComodule R C M) :=
  ((regular R R).externalTensor X).mapCoalgebra (lC R C)

private abbrev R0 (X : RightComodule R C M) :=
  (X.externalTensor (regular R R)).mapCoalgebra (rC R C)

private abbrev sL (R : Type uR) [CommSemiring R]
    (M : Type uM) [AddCommMonoid M] [Module R M] :=
  (_root_.TensorProduct.comm R R M).toLinearMap

private abbrev sR (R : Type uR) [CommSemiring R]
    (M : Type uM) [AddCommMonoid M] [Module R M] :=
  (_root_.TensorProduct.comm R M R).toLinearMap

private abbrev lM (R : Type uR) [CommSemiring R]
    (M : Type uM) [AddCommMonoid M] [Module R M] :=
  (_root_.TensorProduct.lid R M).toLinearMap

private abbrev rM (R : Type uR) [CommSemiring R]
    (M : Type uM) [AddCommMonoid M] [Module R M] :=
  (_root_.TensorProduct.rid R M).toLinearMap

-- Local typed values: coefficient change acts on BOTH endpoints of symmetry.
/-- Symmetry followed by the right unitor is the left unitor, over coefficient `C`. -/
theorem externalTensor_comm_leftUnitor :
    (externalTensorRightUnitor X).comp (show RightComoduleHom
        (((regular R R).externalTensor X).mapCoalgebra
          (Coalgebra.TensorProduct.lid R C).toCoalgHom)
        ((X.externalTensor (regular R R)).mapCoalgebra
          (Coalgebra.TensorProduct.rid R R C).toCoalgHom) from
      { toLinearMap := ((_root_.TensorProduct.comm R R M).toLinearMap), colinear := by
          simpa only [mapCoalgebra_comp, Coalgebra.TensorProduct.comm_unit_left,
            RightComoduleHom.mapCoalgebra_toLinearMap, externalTensorCommHom_toLinearMap] using
            ((externalTensorCommHom (regular R R) X).mapCoalgebra
              (Coalgebra.TensorProduct.rid R R C).toCoalgHom).colinear }) =
        externalTensorLeftUnitor X := by
  apply RightComoduleHom.toLinearMap_injective
  exact congrArg LinearEquiv.toLinearMap
    (_root_.TensorProduct.comm_trans_rid (R := R) (M := M))

/-- The opposite comparison follows from the first and coefficient-normalized
involutivity; both symmetries here are Homs over the final coefficient `C`. -/
theorem externalTensor_comm_rightUnitor :
    (externalTensorLeftUnitor X).comp (show RightComoduleHom
        ((X.externalTensor (regular R R)).mapCoalgebra
          (Coalgebra.TensorProduct.rid R R C).toCoalgHom)
        (((regular R R).externalTensor X).mapCoalgebra
          (Coalgebra.TensorProduct.lid R C).toCoalgHom) from
      { toLinearMap := ((_root_.TensorProduct.comm R M R).toLinearMap), colinear := by
          simpa only [mapCoalgebra_comp, Coalgebra.TensorProduct.comm_unit_right,
            RightComoduleHom.mapCoalgebra_toLinearMap, externalTensorCommHom_toLinearMap] using
            ((externalTensorCommHom X (regular R R)).mapCoalgebra
              (Coalgebra.TensorProduct.lid R C).toCoalgHom).colinear }) =
        externalTensorRightUnitor X := by
  have hinv :
      (_root_.TensorProduct.comm R R M).toLinearMap ∘ₗ
        (_root_.TensorProduct.comm R M R).toLinearMap =
          (LinearMap.id : M ⊗[R] R →ₗ[R] M ⊗[R] R) := by
    apply _root_.TensorProduct.ext'
    intro m a
    rfl
  have h := congrArg
    (fun f : RightComoduleHom
      (((regular R R).externalTensor X).mapCoalgebra
        (Coalgebra.TensorProduct.lid R C).toCoalgHom) X =>
      f.toLinearMap ∘ₗ (_root_.TensorProduct.comm R M R).toLinearMap)
    (externalTensor_comm_leftUnitor X)
  apply RightComoduleHom.toLinearMap_injective
  change (_root_.TensorProduct.lid R M).toLinearMap ∘ₗ
    (_root_.TensorProduct.comm R M R).toLinearMap =
      (_root_.TensorProduct.rid R M).toLinearMap
  change
    ((_root_.TensorProduct.rid R M).toLinearMap ∘ₗ
      (_root_.TensorProduct.comm R R M).toLinearMap) ∘ₗ
      (_root_.TensorProduct.comm R M R).toLinearMap =
        (_root_.TensorProduct.lid R M).toLinearMap ∘ₗ
          (_root_.TensorProduct.comm R M R).toLinearMap at h
  rw [LinearMap.comp_assoc, hinv, LinearMap.comp_id] at h
  exact h.symm

/-- Characteristic whole carrier map of the left-unit comparison. -/
theorem externalTensor_comm_leftUnitor_toLinearMap :
    ((externalTensorRightUnitor X).comp (show RightComoduleHom
        (((regular R R).externalTensor X).mapCoalgebra
          (Coalgebra.TensorProduct.lid R C).toCoalgHom)
        ((X.externalTensor (regular R R)).mapCoalgebra
          (Coalgebra.TensorProduct.rid R R C).toCoalgHom) from
      { toLinearMap := ((_root_.TensorProduct.comm R R M).toLinearMap), colinear := by
          simpa only [mapCoalgebra_comp, Coalgebra.TensorProduct.comm_unit_left,
            RightComoduleHom.mapCoalgebra_toLinearMap, externalTensorCommHom_toLinearMap] using
            ((externalTensorCommHom (regular R R) X).mapCoalgebra
              (Coalgebra.TensorProduct.rid R R C).toCoalgHom).colinear })).toLinearMap =
        (_root_.TensorProduct.rid R M).toLinearMap ∘ₗ
          (_root_.TensorProduct.comm R R M).toLinearMap := rfl

/-- Characteristic whole carrier map of the right-unit comparison. -/
theorem externalTensor_comm_rightUnitor_toLinearMap :
    ((externalTensorLeftUnitor X).comp (show RightComoduleHom
        ((X.externalTensor (regular R R)).mapCoalgebra
          (Coalgebra.TensorProduct.rid R R C).toCoalgHom)
        (((regular R R).externalTensor X).mapCoalgebra
          (Coalgebra.TensorProduct.lid R C).toCoalgHom) from
      { toLinearMap := ((_root_.TensorProduct.comm R M R).toLinearMap), colinear := by
          simpa only [mapCoalgebra_comp, Coalgebra.TensorProduct.comm_unit_right,
            RightComoduleHom.mapCoalgebra_toLinearMap, externalTensorCommHom_toLinearMap] using
            ((externalTensorCommHom X (regular R R)).mapCoalgebra
              (Coalgebra.TensorProduct.lid R C).toCoalgHom).colinear })).toLinearMap =
        (_root_.TensorProduct.lid R M).toLinearMap ∘ₗ
          (_root_.TensorProduct.comm R M R).toLinearMap := rfl

/-- Arbitrary-input readback of the symmetry/right-unitor composite. -/
theorem externalTensor_comm_leftUnitor_apply (t : R ⊗[R] M) :
    (externalTensorRightUnitor X).comp (show RightComoduleHom
        (((regular R R).externalTensor X).mapCoalgebra
          (Coalgebra.TensorProduct.lid R C).toCoalgHom)
        ((X.externalTensor (regular R R)).mapCoalgebra
          (Coalgebra.TensorProduct.rid R R C).toCoalgHom) from
      { toLinearMap := ((_root_.TensorProduct.comm R R M).toLinearMap), colinear := by
          simpa only [mapCoalgebra_comp, Coalgebra.TensorProduct.comm_unit_left,
            RightComoduleHom.mapCoalgebra_toLinearMap, externalTensorCommHom_toLinearMap] using
            ((externalTensorCommHom (regular R R) X).mapCoalgebra
              (Coalgebra.TensorProduct.rid R R C).toCoalgHom).colinear }) t =
        (_root_.TensorProduct.rid R M).toLinearMap
          ((_root_.TensorProduct.comm R R M).toLinearMap t) := rfl

/-- Arbitrary-input readback of the symmetry/left-unitor composite. -/
theorem externalTensor_comm_rightUnitor_apply (t : M ⊗[R] R) :
    (externalTensorLeftUnitor X).comp (show RightComoduleHom
        ((X.externalTensor (regular R R)).mapCoalgebra
          (Coalgebra.TensorProduct.rid R R C).toCoalgHom)
        (((regular R R).externalTensor X).mapCoalgebra
          (Coalgebra.TensorProduct.lid R C).toCoalgHom) from
      { toLinearMap := ((_root_.TensorProduct.comm R M R).toLinearMap), colinear := by
          simpa only [mapCoalgebra_comp, Coalgebra.TensorProduct.comm_unit_right,
            RightComoduleHom.mapCoalgebra_toLinearMap, externalTensorCommHom_toLinearMap] using
            ((externalTensorCommHom X (regular R R)).mapCoalgebra
              (Coalgebra.TensorProduct.lid R C).toCoalgHom).colinear }) t =
        (_root_.TensorProduct.lid R M).toLinearMap
          ((_root_.TensorProduct.comm R M R).toLinearMap t) := rfl

/-- The left-unit comparison sends `a ⊗ m` to `a • m`. -/
theorem externalTensor_comm_leftUnitor_tmul (a : R) (m : M) :
    (externalTensorRightUnitor X).comp (show RightComoduleHom
        (((regular R R).externalTensor X).mapCoalgebra
          (Coalgebra.TensorProduct.lid R C).toCoalgHom)
        ((X.externalTensor (regular R R)).mapCoalgebra
          (Coalgebra.TensorProduct.rid R R C).toCoalgHom) from
      { toLinearMap := ((_root_.TensorProduct.comm R R M).toLinearMap), colinear := by
          simpa only [mapCoalgebra_comp, Coalgebra.TensorProduct.comm_unit_left,
            RightComoduleHom.mapCoalgebra_toLinearMap, externalTensorCommHom_toLinearMap] using
            ((externalTensorCommHom (regular R R) X).mapCoalgebra
              (Coalgebra.TensorProduct.rid R R C).toCoalgHom).colinear }) (a ⊗ₜ[R] m) =
        a • m := rfl

/-- The right-unit comparison sends `m ⊗ a` to `a • m`. -/
theorem externalTensor_comm_rightUnitor_tmul (a : R) (m : M) :
    (externalTensorLeftUnitor X).comp (show RightComoduleHom
        ((X.externalTensor (regular R R)).mapCoalgebra
          (Coalgebra.TensorProduct.rid R R C).toCoalgHom)
        (((regular R R).externalTensor X).mapCoalgebra
          (Coalgebra.TensorProduct.lid R C).toCoalgHom) from
      { toLinearMap := ((_root_.TensorProduct.comm R M R).toLinearMap), colinear := by
          simpa only [mapCoalgebra_comp, Coalgebra.TensorProduct.comm_unit_right,
            RightComoduleHom.mapCoalgebra_toLinearMap, externalTensorCommHom_toLinearMap] using
            ((externalTensorCommHom X (regular R R)).mapCoalgebra
              (Coalgebra.TensorProduct.lid R C).toCoalgHom).colinear }) (m ⊗ₜ[R] a) =
        a • m := rfl

/-- Colinearity of the symmetry/right-unitor carrier composite at final `C`. -/
theorem externalTensor_comm_leftUnitor_colinear :
    X.coaction ∘ₗ
      ((_root_.TensorProduct.rid R M).toLinearMap ∘ₗ
        (_root_.TensorProduct.comm R R M).toLinearMap) =
      ((_root_.TensorProduct.rid R M).toLinearMap ∘ₗ
        (_root_.TensorProduct.comm R R M).toLinearMap).rTensor C ∘ₗ
          (((regular R R).externalTensor X).mapCoalgebra
            (Coalgebra.TensorProduct.lid R C).toCoalgHom).coaction :=
  ((externalTensorRightUnitor X).comp (show RightComoduleHom
        (((regular R R).externalTensor X).mapCoalgebra
          (Coalgebra.TensorProduct.lid R C).toCoalgHom)
        ((X.externalTensor (regular R R)).mapCoalgebra
          (Coalgebra.TensorProduct.rid R R C).toCoalgHom) from
      { toLinearMap := ((_root_.TensorProduct.comm R R M).toLinearMap), colinear := by
          simpa only [mapCoalgebra_comp, Coalgebra.TensorProduct.comm_unit_left,
            RightComoduleHom.mapCoalgebra_toLinearMap, externalTensorCommHom_toLinearMap] using
            ((externalTensorCommHom (regular R R) X).mapCoalgebra
              (Coalgebra.TensorProduct.rid R R C).toCoalgHom).colinear })).colinear

/-- Colinearity of the symmetry/left-unitor carrier composite at final `C`. -/
theorem externalTensor_comm_rightUnitor_colinear :
    X.coaction ∘ₗ
      ((_root_.TensorProduct.lid R M).toLinearMap ∘ₗ
        (_root_.TensorProduct.comm R M R).toLinearMap) =
      ((_root_.TensorProduct.lid R M).toLinearMap ∘ₗ
        (_root_.TensorProduct.comm R M R).toLinearMap).rTensor C ∘ₗ
          ((X.externalTensor (regular R R)).mapCoalgebra
            (Coalgebra.TensorProduct.rid R R C).toCoalgHom).coaction :=
  ((externalTensorLeftUnitor X).comp (show RightComoduleHom
        ((X.externalTensor (regular R R)).mapCoalgebra
          (Coalgebra.TensorProduct.rid R R C).toCoalgHom)
        (((regular R R).externalTensor X).mapCoalgebra
          (Coalgebra.TensorProduct.lid R C).toCoalgHom) from
      { toLinearMap := ((_root_.TensorProduct.comm R M R).toLinearMap), colinear := by
          simpa only [mapCoalgebra_comp, Coalgebra.TensorProduct.comm_unit_right,
            RightComoduleHom.mapCoalgebra_toLinearMap, externalTensorCommHom_toLinearMap] using
            ((externalTensorCommHom X (regular R R)).mapCoalgebra
              (Coalgebra.TensorProduct.lid R C).toCoalgHom).colinear })).colinear

end Unit

end

end Coalgebra.RightComodule
