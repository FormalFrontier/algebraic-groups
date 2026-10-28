/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.SchemePoints
public import Mathlib.AlgebraicGeometry.Group.Affine

/-!
# Coordinates of the canonical global-sections convolution equivalence

Tau Ceti supplies the multiplicative equivalence for arbitrary test schemes.
These additional coordinate formulas identify its underlying ring map and its
specialization on affine test schemes. The original Formal Frontier convolution
construction and naturality proofs are replaced by the canonical API.

## References

Mathlib's relative Gamma-Spec adjunction and global-sections isomorphism;
Tau Ceti's CommHopfAlgCat.SchemePoints for convolution and naturality.
-/

public section
noncomputable section
open CategoryTheory
open scoped CategoryTheory.MonObj
universe u
namespace AlgebraicGeometry
variable (R : Type u) [CommRing R]

/-- The bundled global-sections algebra has the structural map obtained by
pulling back along the structure morphism of the over-scheme. -/
theorem algΓ_obj_algebraMap (X : Over (Spec (.of R))) :
    CommRingCat.ofHom (algebraMap R ((algΓ (.of R)).obj X).unop) =
      (Scheme.ΓSpecIso (.of R)).inv ≫ X.hom.appTop := rfl

/-- The ring map underlying `algΓ` on a morphism is pullback on global sections. -/
theorem algΓ_map_toRingHom {X Y : Over (Spec (.of R))} (f : X ⟶ Y) :
    CommRingCat.ofHom (((algΓ (.of R)).map f).unop.hom.toRingHom) =
      f.left.appTop := rfl

/-- The canonical equivalence records pullback on global sections. -/
theorem schemePointsAlgΓMulEquiv_toRingHom (X : Over (Spec (.of R)))
    (A : Type u) [CommRing A] [Bialgebra R A]
    (h : X ⟶ (Spec (.of A)).asOver (Spec (.of R))) :
    CommRingCat.ofHom
      (TauCeti.CommHopfAlgCat.schemePointsAlgΓMulEquiv (R := R) A X h).ofConv.toRingHom =
      (Scheme.ΓSpecIso (.of A)).inv ≫ h.left.appTop := by
  rw [TauCeti.CommHopfAlgCat.schemePointsAlgΓMulEquiv_apply]
  rfl

/-- On an affine source, identifying global sections with its coordinate ring
recovers the inverse of Mathlib's affine `Spec.mapMulEquiv`. The coefficient
identification is `ΓSpecIso.hom : Γ(Spec T) ⟶ T`. -/
theorem schemePointsAlgΓMulEquiv_spec (A T : Type u)
    [CommRing A] [Bialgebra R A] [CommRing T] [Algebra R T]
    (h : (Spec (.of T)).asOver (Spec (.of R)) ⟶
      (Spec (.of A)).asOver (Spec (.of R))) :
    (Scheme.ΓSpecIso (.of T)).hom.hom.comp
      (TauCeti.CommHopfAlgCat.schemePointsAlgΓMulEquiv (R := R) A
        ((Spec (.of T)).asOver (Spec (.of R))) h).ofConv.toRingHom =
        ((Spec.mapMulEquiv (R := R) (S := A) (T := T)).symm h).ofConv.toRingHom := by
  let hs : Spec (.of T) ⟶ Spec (.of A) := h.left
  have coordinates :
      CommRingCat.ofHom
          (TauCeti.CommHopfAlgCat.schemePointsAlgΓMulEquiv (R := R) A
        ((Spec (.of T)).asOver (Spec (.of R))) h).ofConv.toRingHom
          ≫
        (Scheme.ΓSpecIso (.of T)).hom = Spec.preimage hs := by
    calc
      _ = ((Scheme.ΓSpecIso (.of A)).inv ≫ hs.appTop) ≫
          (Scheme.ΓSpecIso (.of T)).hom :=
        congrArg (fun k : CommRingCat.of A ⟶ Γ(Spec (.of T), ⊤) ↦
          k ≫ (Scheme.ΓSpecIso (.of T)).hom)
          (schemePointsAlgΓMulEquiv_toRingHom R
            ((Spec (.of T)).asOver (Spec (.of R))) A h)
      _ = ((Scheme.ΓSpecIso (.of A)).inv ≫
          (Spec.map (Spec.preimage hs)).appTop) ≫ (Scheme.ΓSpecIso (.of T)).hom :=
        congrArg (fun k : Spec (.of T) ⟶ Spec (.of A) ↦
          ((Scheme.ΓSpecIso (.of A)).inv ≫ k.appTop) ≫
            (Scheme.ΓSpecIso (.of T)).hom) (Spec.map_preimage hs).symm
      _ = (Spec.preimage hs ≫ (Scheme.ΓSpecIso (.of T)).inv) ≫
          (Scheme.ΓSpecIso (.of T)).hom :=
        congrArg (fun k : CommRingCat.of A ⟶ Γ(Spec (.of T), ⊤) ↦
          k ≫ (Scheme.ΓSpecIso (.of T)).hom)
          (Scheme.ΓSpecIso_inv_naturality (Spec.preimage hs)).symm
      _ = Spec.preimage hs := by
        rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact congrArg CommRingCat.Hom.hom coordinates


end AlgebraicGeometry
