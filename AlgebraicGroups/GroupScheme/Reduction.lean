/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Scheme.Reduction
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Reduction of group schemes

This file packages the reduction of the underlying scheme of an object over a
base scheme as another object over that base. If the base and the Cartesian
square of the reduction are reduced, the group operations restrict to the
reduction. The canonical inclusion is then a monoid-object homomorphism.

No preservation of fibre products by scheme reduction is asserted here. The
reducedness of the exact tensor object needed to restrict multiplication is an
explicit hypothesis.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

universe u

variable {S : Scheme.{u}}

/-- The reduction of the underlying scheme of an object over `S`, equipped with
its composite structure morphism to `S`.

This is an abbreviation so that the dependent `Over` types reduce to the
underlying scheme reduction without requiring transports. -/
noncomputable abbrev Scheme.reductionOver (G : Over S) : Over S :=
  Over.mk (Scheme.reductionι.app G.left ≫ G.hom)

/-- The canonical inclusion of the reduction of an object over `S`. -/
noncomputable abbrev Scheme.reductionOverι (G : Over S) :
    Scheme.reductionOver G ⟶ G :=
  Over.homMk (Scheme.reductionι.app G.left)

instance Scheme.reductionOverι_mono (G : Over S) : Mono (Scheme.reductionOverι G) := by
  let _ : Mono (Scheme.reductionι.app G.left) := by
    change Mono G.left.nilradical.subschemeι
    infer_instance
  exact Over.mono_of_mono_left _

/-- The canonical inclusion of a group-scheme reduction is a closed immersion. -/
instance Scheme.reductionOverι_isClosedImmersion (G : Over S) :
    IsClosedImmersion (Scheme.reductionOverι G).left := by
  change IsClosedImmersion G.left.nilradical.subschemeι
  infer_instance

instance Scheme.reductionOver_isReduced (G : Over S) :
    IsReduced (Scheme.reductionOver G).left := by
  change IsReduced (Scheme.reduction.obj G.left)
  infer_instance

private noncomputable def Scheme.Hom.liftReduction {Y X : Scheme.{u}}
    (f : Y ⟶ X) [IsReduced Y] : Y ⟶ Scheme.reduction.obj X :=
  f.liftNilradicalSubscheme ≫ eqToHom (Scheme.reduction_obj X).symm

private lemma Scheme.Hom.liftReduction_fac {Y X : Scheme.{u}}
    (f : Y ⟶ X) [IsReduced Y] :
    f.liftReduction ≫ Scheme.reductionι.app X = f := by
  change f.liftNilradicalSubscheme ≫ X.nilradical.subschemeι = f
  exact f.liftNilradicalSubscheme_fac

/-- The unit of a group object restricts to its reduction when the base is reduced. -/
noncomputable def Scheme.reductionOverOne (G : Over S) [GrpObj G] [IsReduced S] :
    𝟙_ (Over S) ⟶ Scheme.reductionOver G := by
  let _ : IsReduced (𝟙_ (Over S)).left := by
    simpa only [Over.tensorUnit_left] using (inferInstance : IsReduced S)
  exact Over.homMk (Scheme.Hom.liftReduction η[G].left) (by
    rw [show (Scheme.reductionOver G).hom =
      Scheme.reductionι.app G.left ≫ G.hom from rfl, ← Category.assoc,
      Scheme.Hom.liftReduction_fac]
    exact η[G].w)

@[reassoc]
lemma Scheme.reductionOverOne_comp_ι (G : Over S) [GrpObj G] [IsReduced S] :
    Scheme.reductionOverOne G ≫ Scheme.reductionOverι G = η[G] := by
  let _ : IsReduced (𝟙_ (Over S)).left := by
    simpa only [Over.tensorUnit_left] using (inferInstance : IsReduced S)
  ext
  exact Scheme.Hom.liftReduction_fac _

/-- Multiplication of a group object restricts to its reduction when the
Cartesian square of that reduction is reduced. -/
noncomputable def Scheme.reductionOverMul (G : Over S) [GrpObj G]
    [IsReduced ((Scheme.reductionOver G ⊗ Scheme.reductionOver G).left)] :
    Scheme.reductionOver G ⊗ Scheme.reductionOver G ⟶ Scheme.reductionOver G :=
  Over.homMk (Scheme.Hom.liftReduction
    ((Scheme.reductionOverι G ⊗ₘ Scheme.reductionOverι G) ≫ μ[G]).left) (by
      rw [show (Scheme.reductionOver G).hom =
        Scheme.reductionι.app G.left ≫ G.hom from rfl, ← Category.assoc,
        Scheme.Hom.liftReduction_fac]
      exact ((Scheme.reductionOverι G ⊗ₘ Scheme.reductionOverι G) ≫ μ[G]).w)

@[reassoc]
lemma Scheme.reductionOverMul_comp_ι (G : Over S) [GrpObj G]
    [IsReduced ((Scheme.reductionOver G ⊗ Scheme.reductionOver G).left)] :
    Scheme.reductionOverMul G ≫ Scheme.reductionOverι G =
      (Scheme.reductionOverι G ⊗ₘ Scheme.reductionOverι G) ≫ μ[G] := by
  ext
  exact Scheme.Hom.liftReduction_fac _

/-- Inversion of a group object restricts to its reduction. -/
noncomputable def Scheme.reductionOverInv (G : Over S) [GrpObj G] :
    Scheme.reductionOver G ⟶ Scheme.reductionOver G :=
  Over.homMk (Scheme.Hom.liftReduction
    (Scheme.reductionι.app G.left ≫ ι[G].left)) (by
    rw [show (Scheme.reductionOver G).hom =
      Scheme.reductionι.app G.left ≫ G.hom from rfl, ← Category.assoc,
      Scheme.Hom.liftReduction_fac]
    exact (Scheme.reductionOverι G ≫ ι[G]).w)

@[reassoc]
lemma Scheme.reductionOverInv_comp_ι (G : Over S) [GrpObj G] :
    Scheme.reductionOverInv G ≫ Scheme.reductionOverι G =
      Scheme.reductionOverι G ≫ ι[G] := by
  ext
  exact Scheme.Hom.liftReduction_fac _

/-- The reduction of a group scheme is a group scheme provided the base and the
Cartesian square of the reduction are reduced. -/
noncomputable instance Scheme.reductionOver_grpObj (G : Over S) [GrpObj G] [IsReduced S]
    [IsReduced ((Scheme.reductionOver G ⊗ Scheme.reductionOver G).left)] :
    GrpObj (Scheme.reductionOver G) := by
  let i := Scheme.reductionOverι G
  let one := Scheme.reductionOverOne G
  let mul := Scheme.reductionOverMul G
  let inv := Scheme.reductionOverInv G
  have one_i : one ≫ i = η[G] := Scheme.reductionOverOne_comp_ι G
  have mul_i : mul ≫ i = (i ⊗ₘ i) ≫ μ[G] := Scheme.reductionOverMul_comp_ι G
  have inv_i : inv ≫ i = i ≫ ι[G] := Scheme.reductionOverInv_comp_ι G
  letI : MonObj (Scheme.reductionOver G) :=
    { one := one
      mul := mul
      one_mul := by
        apply (cancel_mono i).1
        rw [Category.assoc, mul_i, ← tensorHom_id, tensorHom_comp_tensorHom_assoc,
          Category.id_comp, one_i]
        rw [← Category.id_comp η[G], ← Category.comp_id i]
        rw [← tensorHom_comp_tensorHom_assoc (𝟙 (𝟙_ (Over S))) i η[G] (𝟙 G) μ[G]]
        simp
      mul_one := by
        apply (cancel_mono i).1
        rw [Category.assoc, mul_i, ← id_tensorHom, tensorHom_comp_tensorHom_assoc,
          Category.id_comp, one_i]
        rw [← Category.comp_id i, ← Category.id_comp η[G]]
        rw [← tensorHom_comp_tensorHom_assoc i (𝟙 (𝟙_ (Over S))) (𝟙 G) η[G] μ[G]]
        simp
      mul_assoc := by
        apply (cancel_mono i).1
        simp only [Category.assoc, mul_i]
        calc
          mul ▷ Scheme.reductionOver G ≫ (i ⊗ₘ i) ≫ μ[G] =
              ((i ⊗ₘ i) ⊗ₘ i) ≫ (μ[G] ▷ G) ≫ μ[G] := by
            rw [← tensorHom_id, tensorHom_comp_tensorHom_assoc, Category.id_comp, mul_i]
            simpa only [Category.comp_id, tensorHom_id, Category.assoc] using
              (tensorHom_comp_tensorHom_assoc (i ⊗ₘ i) i μ[G] (𝟙 G) μ[G]).symm
          _ = ((i ⊗ₘ i) ⊗ₘ i) ≫ (α_ G G G).hom ≫ (G ◁ μ[G]) ≫ μ[G] := by
            rw [MonObj.mul_assoc]
          _ = (α_ (Scheme.reductionOver G) (Scheme.reductionOver G)
                (Scheme.reductionOver G)).hom ≫
              (i ⊗ₘ (i ⊗ₘ i)) ≫ (G ◁ μ[G]) ≫ μ[G] := by
            rw [associator_naturality_assoc]
          _ = (α_ (Scheme.reductionOver G) (Scheme.reductionOver G)
                (Scheme.reductionOver G)).hom ≫
              Scheme.reductionOver G ◁ mul ≫ (i ⊗ₘ i) ≫ μ[G] := by
            have hright : Scheme.reductionOver G ◁ mul ≫ (i ⊗ₘ i) ≫ μ[G] =
                (i ⊗ₘ (i ⊗ₘ i)) ≫ (G ◁ μ[G]) ≫ μ[G] := by
              rw [← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.id_comp, mul_i]
              simpa only [Category.comp_id, id_tensorHom, Category.assoc] using
                (tensorHom_comp_tensorHom_assoc i (i ⊗ₘ i) (𝟙 G) μ[G] μ[G]).symm
            simp only [hright] }
  exact
    { inv := inv
      left_inv := by
        apply (cancel_mono i).1
        change (lift inv (𝟙 _) ≫ mul) ≫ i = (toUnit _ ≫ one) ≫ i
        rw [Category.assoc, mul_i, ← Category.assoc, lift_map]
        simp [inv_i, one_i]
      right_inv := by
        apply (cancel_mono i).1
        change (lift (𝟙 _) inv ≫ mul) ≫ i = (toUnit _ ≫ one) ≫ i
        rw [Category.assoc, mul_i, ← Category.assoc, lift_map]
        simp [inv_i, one_i] }

/-- The canonical inclusion from the reduction of a group scheme is a
monoid-object homomorphism. -/
instance Scheme.reductionOverι_isMonHom (G : Over S) [GrpObj G] [IsReduced S]
    [IsReduced ((Scheme.reductionOver G ⊗ Scheme.reductionOver G).left)] :
    IsMonHom (Scheme.reductionOverι G) where
  one_hom := Scheme.reductionOverOne_comp_ι G
  mul_hom := Scheme.reductionOverMul_comp_ι G

end AlgebraicGeometry
