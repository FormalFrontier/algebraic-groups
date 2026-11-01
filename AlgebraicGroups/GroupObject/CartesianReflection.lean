/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import AlgebraicGroups.GroupObject.Reflection

/-!
# Fully faithful reflection of Cartesian group objects

A fully faithful functor between Cartesian monoidal categories reflects a supplied group
object on its image to a group object on the same source object. The construction uses
representability of the restriction of the group-valued Yoneda functor.

The construction follows Mathlib's `CategoryTheory.yonedaGrpObj`,
`CategoryTheory.yonedaGrpObjRepresentableBy` and `CategoryTheory.GrpObj.ofRepresentableBy`,
generalizing its fully faithful group reflection and providing a bridge to that construction.

The reflected monoid parent agrees with fully faithful monoid reflection for any supplied
Oplax monoidal structure. Its inverse is the preimage of the supplied inverse, without an
Oplax assumption. For a monoidal functor it agrees with fully faithful group reflection.
-/

@[expose] public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite

universe uC vC uD vD

namespace CategoryTheory.Functor

private theorem homEquiv_ofRepresentableBy_mul
    {C : Type uC} [Category.{vC} C] [CartesianMonoidalCategory C]
    (X : C) (K : Cᵒᵖ ⥤ GrpCat.{vD})
    (α : (K ⋙ forget GrpCat).RepresentableBy X) :
    α.homEquiv (GrpObj.ofRepresentableBy X K α).toMonObj.mul =
      α.homEquiv (fst X X) * α.homEquiv (snd X X) := by
  change α.homEquiv
      (α.homEquiv.symm (α.homEquiv (fst X X) * α.homEquiv (snd X X))) = _
  exact α.homEquiv.apply_symm_apply _

private theorem homEquiv_ofRepresentableBy_inv
    {C : Type uC} [Category.{vC} C] [CartesianMonoidalCategory C]
    (X : C) (K : Cᵒᵖ ⥤ GrpCat.{vD})
    (α : (K ⋙ forget GrpCat).RepresentableBy X) :
    α.homEquiv (GrpObj.ofRepresentableBy X K α).inv =
      (α.homEquiv (𝟙 X))⁻¹ := by
  change α.homEquiv (α.homEquiv.symm (α.homEquiv (𝟙 X))⁻¹) = _
  exact α.homEquiv.apply_symm_apply _

private def FullyFaithful.cartesianRepresentation
    {C : Type uC} [cC : Category.{vC} C]
    {D : Type uD} [cD : Category.{vD} D]
    [cartD : CartesianMonoidalCategory D]
    {F : C ⥤ D} (hF : F.FullyFaithful) (X : C)
    [Γ : GrpObj (F.obj X)] :
    ((F.op ⋙ yonedaGrpObj (F.obj X)) ⋙ forget GrpCat).RepresentableBy X where
  homEquiv {T} :=
    (hF.homEquiv (X := T) (Y := X)).trans
      (yonedaGrpObjRepresentableBy (F.obj X)).homEquiv
  homEquiv_comp f g := by
    let β := yonedaGrpObjRepresentableBy (F.obj X)
    change β.homEquiv (F.map (f ≫ g)) =
      (yonedaGrpObj (F.obj X) ⋙ forget GrpCat).map (F.map f).op
        (β.homEquiv (F.map g))
    rw [Functor.map_comp]
    exact β.homEquiv_comp (F.map f) (F.map g)

private theorem yonedaGrpObjRepresentableBy_mul
    {D : Type uD} [Category.{vD} D] [CartesianMonoidalCategory D]
    (A : D) [Γ : GrpObj A] {T : D} (f : T ⟶ A ⊗ A) :
    (yonedaGrpObjRepresentableBy A).homEquiv (f ≫ Γ.toMonObj.mul) =
      (yonedaGrpObjRepresentableBy A).homEquiv (f ≫ fst A A) *
        (yonedaGrpObjRepresentableBy A).homEquiv (f ≫ snd A A) := by
  let G := yonedaGrpObj A
  let β := yonedaGrpObjRepresentableBy A
  have hmul := homEquiv_ofRepresentableBy_mul A G β
  have hparent :
      (GrpObj.ofRepresentableBy A G β).toMonObj.mul = Γ.toMonObj.mul :=
    congrArg (fun Δ : GrpObj A => Δ.toMonObj.mul)
      (GrpObj.ofRepresentableBy_yonedaGrpObjRepresentableBy A)
  rw [hparent] at hmul
  calc
    β.homEquiv (f ≫ Γ.toMonObj.mul) =
        (G.map f.op) (β.homEquiv Γ.toMonObj.mul) :=
      β.homEquiv_comp f Γ.toMonObj.mul
    _ = (G.map f.op)
        (β.homEquiv (fst A A) * β.homEquiv (snd A A)) := by rw [hmul]
    _ = (G.map f.op) (β.homEquiv (fst A A)) *
        (G.map f.op) (β.homEquiv (snd A A)) :=
      map_mul (ConcreteCategory.hom (G.map f.op)) _ _
    _ = β.homEquiv (f ≫ fst A A) * β.homEquiv (f ≫ snd A A) := by
      change
        (yonedaGrpObj A ⋙ forget GrpCat).map f.op (β.homEquiv (fst A A)) *
            (yonedaGrpObj A ⋙ forget GrpCat).map f.op (β.homEquiv (snd A A)) =
          β.homEquiv (f ≫ fst A A) * β.homEquiv (f ≫ snd A A)
      rw [← β.homEquiv_comp, ← β.homEquiv_comp]

private theorem yonedaGrpObjRepresentableBy_inv
    {D : Type uD} [Category.{vD} D] [CartesianMonoidalCategory D]
    (A : D) [Γ : GrpObj A] :
    (yonedaGrpObjRepresentableBy A).homEquiv Γ.inv =
      ((yonedaGrpObjRepresentableBy A).homEquiv (𝟙 A))⁻¹ := by
  let G := yonedaGrpObj A
  let β := yonedaGrpObjRepresentableBy A
  have hinv := homEquiv_ofRepresentableBy_inv A G β
  have hoperation : (GrpObj.ofRepresentableBy A G β).inv = Γ.inv :=
    congrArg (fun Δ : GrpObj A => Δ.inv)
      (GrpObj.ofRepresentableBy_yonedaGrpObjRepresentableBy A)
  rw [hoperation] at hinv
  exact hinv

/-- The group object on `X` reflected from the supplied group object on `F.obj X` by a
fully faithful functor between Cartesian monoidal categories. -/
@[instance_reducible]
def FullyFaithful.grpObjOfCartesian
    {C : Type uC} [cC : Category.{vC} C]
    [cartC : CartesianMonoidalCategory C]
    {D : Type uD} [cD : Category.{vD} D]
    [cartD : CartesianMonoidalCategory D]
    {F : C ⥤ D} (hF : F.FullyFaithful) (X : C)
    [Γ : GrpObj (F.obj X)] : GrpObj X :=
  GrpObj.ofRepresentableBy X (F.op ⋙ yonedaGrpObj (F.obj X))
    { homEquiv {T} :=
        (hF.homEquiv (X := T) (Y := X)).trans
          (yonedaGrpObjRepresentableBy (F.obj X)).homEquiv
      homEquiv_comp f g := by
        let β := yonedaGrpObjRepresentableBy (F.obj X)
        change β.homEquiv (F.map (f ≫ g)) =
          (yonedaGrpObj (F.obj X) ⋙ forget GrpCat).map (F.map f).op
            (β.homEquiv (F.map g))
        rw [Functor.map_comp]
        exact β.homEquiv_comp (F.map f) (F.map g) }

/-- The monoid parent of the Cartesian reflected group is the existing Oplax fully faithful
reflection of the supplied monoid parent. -/
theorem FullyFaithful.grpObjOfCartesian_toMonObj
    {C : Type uC} [cC : Category.{vC} C]
    [cartC : CartesianMonoidalCategory C]
    {D : Type uD} [cD : Category.{vD} D]
    [cartD : CartesianMonoidalCategory D]
    {F : C ⥤ D} [oF : F.OplaxMonoidal]
    (hF : F.FullyFaithful) (X : C) [Γ : GrpObj (F.obj X)] :
    (hF.grpObjOfCartesian X (Γ := Γ)).toMonObj = hF.monObj X := by
  let β := yonedaGrpObjRepresentableBy (F.obj X)
  have hmul :
      β.homEquiv (F.map (hF.grpObjOfCartesian X (Γ := Γ)).toMonObj.mul) =
        β.homEquiv (F.map (fst X X)) * β.homEquiv (F.map (snd X X)) := by
    let α := FullyFaithful.cartesianRepresentation hF X (Γ := Γ)
    change
      α.homEquiv
          (GrpObj.ofRepresentableBy X (F.op ⋙ yonedaGrpObj (F.obj X)) α).toMonObj.mul =
        α.homEquiv (fst X X) * α.homEquiv (snd X X)
    exact homEquiv_ofRepresentableBy_mul X (F.op ⋙ yonedaGrpObj (F.obj X)) α
  apply MonObj.ext
  apply hF.map_injective
  calc
    F.map (hF.grpObjOfCartesian X (Γ := Γ)).toMonObj.mul =
        OplaxMonoidal.δ F X X ≫ Γ.toMonObj.mul := by
      apply β.homEquiv.injective
      calc
        β.homEquiv (F.map (hF.grpObjOfCartesian X (Γ := Γ)).toMonObj.mul) =
            β.homEquiv (F.map (fst X X)) * β.homEquiv (F.map (snd X X)) := hmul
        _ = β.homEquiv (OplaxMonoidal.δ F X X ≫ Γ.toMonObj.mul) := by
          symm
          simpa only [OplaxMonoidal.δ_fst, OplaxMonoidal.δ_snd] using
            yonedaGrpObjRepresentableBy_mul (F.obj X) (OplaxMonoidal.δ F X X)
    _ = F.map (hF.monObj X).mul := (hF.map_preimage _).symm

/-- The inverse of the Cartesian reflected group is the fully faithful preimage of the
supplied inverse. -/
theorem FullyFaithful.grpObjOfCartesian_inv
    {C : Type uC} [cC : Category.{vC} C]
    [cartC : CartesianMonoidalCategory C]
    {D : Type uD} [cD : Category.{vD} D]
    [cartD : CartesianMonoidalCategory D]
    {F : C ⥤ D} (hF : F.FullyFaithful) (X : C)
    [Γ : GrpObj (F.obj X)] :
    (hF.grpObjOfCartesian X (Γ := Γ)).inv = hF.preimage Γ.inv := by
  let β := yonedaGrpObjRepresentableBy (F.obj X)
  have hinv :
      β.homEquiv (F.map (hF.grpObjOfCartesian X (Γ := Γ)).inv) =
        (β.homEquiv (F.map (𝟙 X)))⁻¹ := by
    let α := FullyFaithful.cartesianRepresentation hF X (Γ := Γ)
    change
      α.homEquiv (GrpObj.ofRepresentableBy X (F.op ⋙ yonedaGrpObj (F.obj X)) α).inv =
        (α.homEquiv (𝟙 X))⁻¹
    exact homEquiv_ofRepresentableBy_inv X (F.op ⋙ yonedaGrpObj (F.obj X)) α
  apply hF.map_injective
  calc
    F.map (hF.grpObjOfCartesian X (Γ := Γ)).inv = Γ.inv := by
      apply β.homEquiv.injective
      calc
        β.homEquiv (F.map (hF.grpObjOfCartesian X (Γ := Γ)).inv) =
            (β.homEquiv (F.map (𝟙 X)))⁻¹ := hinv
        _ = (β.homEquiv (𝟙 (F.obj X)))⁻¹ := by rw [Functor.map_id]
        _ = β.homEquiv Γ.inv := (yonedaGrpObjRepresentableBy_inv (F.obj X)).symm
    _ = F.map (hF.preimage Γ.inv) := (hF.map_preimage Γ.inv).symm

/-- For a monoidal fully faithful functor, Cartesian group reflection agrees with the existing
fully faithful group reflection. -/
theorem FullyFaithful.grpObjOfCartesian_eq_grpObj
    {C : Type uC} [cC : Category.{vC} C]
    [cartC : CartesianMonoidalCategory C]
    {D : Type uD} [cD : Category.{vD} D]
    [cartD : CartesianMonoidalCategory D]
    {F : C ⥤ D} [mF : F.Monoidal]
    (hF : F.FullyFaithful) (X : C) [Γ : GrpObj (F.obj X)] :
    hF.grpObjOfCartesian X (Γ := Γ) = hF.grpObj X := by
  apply GrpObj.toMonObj_injective
  exact hF.grpObjOfCartesian_toMonObj X (Γ := Γ)

end CategoryTheory.Functor
