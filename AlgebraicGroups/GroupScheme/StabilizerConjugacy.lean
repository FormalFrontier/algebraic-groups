/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupObject.StabilizerConjugacy
public import AlgebraicGroups.GroupScheme.Stabilizer

/-!
# Conjugacy of stabilizer group schemes

The internal conjugacy isomorphism in `Over S` identifies the original
stabilizer schemes over `S`. The comparison with their scheme-theoretic orbit
fibres preserves both projections. All generalized-point formulas apply to
every test `S`-scheme, including nonreduced schemes; no geometric hypotheses
are needed. The pullback comparisons are those of `GroupScheme.Stabilizer`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped MonObj

namespace CategoryTheory.ModObj

variable {S : Scheme.{u}} {G X : Over S} [GrpObj G] [ModObj G X]
  (x : 𝟙_ (Over S) ⟶ X) (g : 𝟙_ (Over S) ⟶ G)

/-- The conjugacy isomorphism on the original underlying stabilizer schemes. -/
def stabilizerConjUnderlyingIso :
    (stabilizer G x).left ≅ (stabilizer G (g • x)).left :=
  (Over.forget S).mapIso (asIso (stabilizerConjIso x g).hom.hom.hom)

/-- The forward scheme morphism is the underlying forward stabilizer restriction. -/
theorem stabilizerConjUnderlyingIso_hom :
    (stabilizerConjUnderlyingIso x g).hom = (stabilizerConjIso x g).hom.hom.hom.left := by
  simp only [stabilizerConjUnderlyingIso, Functor.mapIso_hom, asIso_hom, Over.forget_map]

/-- The inverse scheme morphism is the underlying inverse stabilizer restriction. -/
theorem stabilizerConjUnderlyingIso_inv :
    (stabilizerConjUnderlyingIso x g).inv = (stabilizerConjIso x g).inv.hom.hom.left := by
  have h : inv (stabilizerConjIso x g).hom.hom.hom =
      (stabilizerConjIso x g).inv.hom.hom :=
    IsIso.inv_eq_of_hom_inv_id (stabilizerConjIso_hom_inv_id x g)
  simp only [stabilizerConjUnderlyingIso, Functor.mapIso_inv, asIso_inv, h, Over.forget_map]

/-- Forward conjugacy preserves the original structure maps to the base scheme. -/
@[reassoc]
theorem stabilizerConjUnderlyingIso_hom_structure :
    (stabilizerConjUnderlyingIso x g).hom ≫ (stabilizer G (g • x)).hom =
      (stabilizer G x).hom := by
  simpa only [stabilizerConjUnderlyingIso_hom] using
    Over.w (stabilizerConjIso x g).hom.hom.hom

/-- Inverse conjugacy preserves the original structure maps to the base scheme. -/
@[reassoc]
theorem stabilizerConjUnderlyingIso_inv_structure :
    (stabilizerConjUnderlyingIso x g).inv ≫ (stabilizer G x).hom =
      (stabilizer G (g • x)).hom := by
  simpa only [stabilizerConjUnderlyingIso_inv] using
    Over.w (stabilizerConjIso x g).inv.hom.hom

/-- The forward inclusion square on underlying schemes. -/
@[reassoc (attr := simp)]
theorem stabilizerConjUnderlyingIso_hom_ι :
    (stabilizerConjUnderlyingIso x g).hom ≫ (stabilizerι G (g • x)).left =
      (stabilizerι G x).left ≫ (GrpObj.conjBy g).left := by
  simpa only [stabilizerConjUnderlyingIso_hom, Over.comp_left] using
    congrArg (fun f : stabilizer G x ⟶ G ↦ f.left) (stabilizerConjIso_hom_ι x g)

/-- The inverse inclusion square on underlying schemes. -/
@[reassoc (attr := simp)]
theorem stabilizerConjUnderlyingIso_inv_ι :
    (stabilizerConjUnderlyingIso x g).inv ≫ (stabilizerι G x).left =
      (stabilizerι G (g • x)).left ≫ (GrpObj.conjBy g⁻¹).left := by
  simpa only [stabilizerConjUnderlyingIso_inv, Over.comp_left] using
    congrArg (fun f : stabilizer G (g • x) ⟶ G ↦ f.left) (stabilizerConjIso_inv_ι x g)

/-- The induced conjugacy isomorphism of the two scheme-theoretic orbit fibres. -/
def stabilizerConjFiberIso :
    pullback (orbitMap G x).left x.left ≅
      pullback (orbitMap G (g • x)).left (g • x).left :=
  (stabilizerUnderlyingIso G x).symm ≪≫ stabilizerConjUnderlyingIso x g ≪≫
    stabilizerUnderlyingIso G (g • x)

/-- On orbit fibres, the forward first projection is conjugation in the original group scheme. -/
@[reassoc (attr := simp)]
theorem stabilizerConjFiberIso_hom_fst :
    (stabilizerConjFiberIso x g).hom ≫ pullback.fst _ _ =
      pullback.fst (orbitMap G x).left x.left ≫ (GrpObj.conjBy g).left := by
  simp [stabilizerConjFiberIso, Category.assoc]

/-- On orbit fibres, the forward second projection is the original structure map. -/
@[reassoc (attr := simp)]
theorem stabilizerConjFiberIso_hom_snd :
    (stabilizerConjFiberIso x g).hom ≫ pullback.snd _ _ =
      pullback.snd (orbitMap G x).left x.left := by
  simp [stabilizerConjFiberIso, Category.assoc,
    stabilizerConjUnderlyingIso_hom_structure]

/-- On orbit fibres, the inverse first projection is inverse conjugation. -/
@[reassoc (attr := simp)]
theorem stabilizerConjFiberIso_inv_fst :
    (stabilizerConjFiberIso x g).inv ≫ pullback.fst _ _ =
      pullback.fst (orbitMap G (g • x)).left (g • x).left ≫ (GrpObj.conjBy g⁻¹).left := by
  simp [stabilizerConjFiberIso, Category.assoc]

/-- On orbit fibres, the inverse second projection is the original structure map. -/
@[reassoc (attr := simp)]
theorem stabilizerConjFiberIso_inv_snd :
    (stabilizerConjFiberIso x g).inv ≫ pullback.snd _ _ =
      pullback.snd (orbitMap G (g • x)).left (g • x).left := by
  simp [stabilizerConjFiberIso, Category.assoc,
    stabilizerConjUnderlyingIso_inv_structure]

/-- Forward conjugacy on every test `S`-scheme, with its original group of generalized points. -/
theorem stabilizerConjUnderlyingIso_hom_apply_ι (T : Over S)
    (a : T ⟶ stabilizer G x) :
    (a.left ≫ (stabilizerConjUnderlyingIso x g).hom) ≫ (stabilizerι G (g • x)).left =
      ((toUnit T ≫ g) * (a ≫ stabilizerι G x) * (toUnit T ≫ g)⁻¹).left := by
  simpa only [stabilizerConjUnderlyingIso_hom, Over.comp_left] using
    congrArg (fun f : T ⟶ G ↦ f.left) (stabilizerConjIso_hom_apply_ι x g a)

/-- Inverse conjugacy on every test `S`-scheme, without any reducedness condition. -/
theorem stabilizerConjUnderlyingIso_inv_apply_ι (T : Over S)
    (b : T ⟶ stabilizer G (g • x)) :
    (b.left ≫ (stabilizerConjUnderlyingIso x g).inv) ≫ (stabilizerι G x).left =
      ((toUnit T ≫ g)⁻¹ * (b ≫ stabilizerι G (g • x)) * (toUnit T ≫ g)).left := by
  simpa only [stabilizerConjUnderlyingIso_inv, Over.comp_left] using
    congrArg (fun f : T ⟶ G ↦ f.left) (stabilizerConjIso_inv_apply_ι x g b)

end CategoryTheory.ModObj
