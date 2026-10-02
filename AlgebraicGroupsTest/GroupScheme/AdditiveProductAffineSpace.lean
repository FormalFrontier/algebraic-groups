/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.AdditiveProductAffineSpace
public import Mathlib.Data.ZMod.Basic

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

variable (K : Type u) [CommRing K] (D : Type u) [Fintype D]

example : (∏ᶜ fun _ : D => additiveGroupScheme K).X ≅
    (Spec (.of (MvPolynomial D K))).asOver (Spec (.of K)) :=
  additiveGroupProductUnderlyingSpecIso K D

example : (∏ᶜ fun _ : D => additiveGroupScheme K).X ≅
    (AffineSpace D (Spec (.of K))).asOver (Spec (.of K)) :=
  additiveGroupProductUnderlyingAffineSpaceIso K D

example (d : D) :
    additiveProductCoordinateAlgHom K D d (additiveGroupCoordinate K) =
      MvPolynomial.X d :=
  additiveProductCoordinateAlgHom_coordinate K D d

example (d : D) :
    (additiveGroupProductUnderlyingSpecIso K D).hom ≫
        additiveGroupAffineProductProjection K D d =
      (Limits.Pi.π (fun _ : D => additiveGroupScheme K) d).hom.hom :=
  additiveGroupProductUnderlyingSpecIso_hom_projection K D d

example (d : D) (T : Over (Spec (.of K)))
    (h : T ⟶ (∏ᶜ fun _ : D => additiveGroupScheme K).X) :
    additiveGroupGlobalCoordinate K T
        (h ≫ (Limits.Pi.π (fun _ : D => additiveGroupScheme K) d).hom.hom) =
      additiveGroupAffineProductGlobalCoordinate K D d T
        (h ≫ (additiveGroupProductUnderlyingAffineSpaceIso K D).hom ≫
          (additiveGroupAffineProductSpecToSpaceIso K D).inv) :=
  additiveGroupProductUnderlyingAffineSpaceIso_coordinate K D d T h

example : (∏ᶜ fun _ : Fin 0 => additiveGroupScheme ℤ).X ≅
    (AffineSpace (Fin 0) (Spec (.of ℤ))).asOver (Spec (.of ℤ)) :=
  additiveGroupProductUnderlyingAffineSpaceIso ℤ (Fin 0)

example : (∏ᶜ fun _ : Fin 2 => additiveGroupScheme ℤ).X ≅
    (Spec (.of (MvPolynomial (Fin 2) ℤ))).asOver (Spec (.of ℤ)) :=
  additiveGroupProductUnderlyingSpecIso ℤ (Fin 2)

example :
    (additiveGroupProductUnderlyingSpecIso ℤ (Fin 2)).hom ≫
        additiveGroupAffineProductProjection ℤ (Fin 2) (0 : Fin 2) =
      (Limits.Pi.π (fun _ : Fin 2 => additiveGroupScheme ℤ) (0 : Fin 2)).hom.hom :=
  additiveGroupProductUnderlyingSpecIso_hom_projection ℤ (Fin 2) (0 : Fin 2)

example : (∏ᶜ fun _ : Fin 2 => additiveGroupScheme (ZMod 1)).X ≅
    (AffineSpace (Fin 2) (Spec (.of (ZMod 1)))).asOver (Spec (.of (ZMod 1))) :=
  additiveGroupProductUnderlyingAffineSpaceIso (ZMod 1) (Fin 2)

example : (∏ᶜ fun _ : Fin 0 => additiveGroupScheme (ZMod 1)).X ≅
    (Spec (.of (MvPolynomial (Fin 0) (ZMod 1)))).asOver (Spec (.of (ZMod 1))) :=
  additiveGroupProductUnderlyingSpecIso (ZMod 1) (Fin 0)
