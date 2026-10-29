/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupObject.Hom
public import AlgebraicGroups.GroupObject.Stabilizer

/-!
# Conjugacy of stabilizers of sections

For the given internal action, an arbitrary group section `g` transports the
stabilizer of `x` to the stabilizer of `g • x`. The isomorphism restricts
Mathlib's conjugation morphism and uses the two original chosen pullbacks.
Its inverse lands in the original stabilizer, without choosing a pullback at
`g⁻¹ • (g • x)`.

The generalized-point formulas use Mathlib's Hom group and Hom action.
`stabilizerConjPointsEquiv` transports the existing `stabilizerHomEquiv` and
is natural for every test morphism. The ordinary group-action conjugacy theorem
is already provided by `MulAction.stabilizerEquivStabilizer`.
-/

@[expose] public section

noncomputable section

universe v u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped MonObj

namespace CategoryTheory.GrpObj

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {G : C} [GrpObj G] (g : 𝟙_ C ⟶ G)

/-- Conjugation by an arbitrary group section, obtained by fixing the first
argument of Mathlib's conjugation morphism. -/
def conjBy : G ⟶ G :=
  lift (toUnit G ≫ g) (𝟙 G) ≫ conj G

/-- Evaluation of fixed-section conjugation on every generalized point. -/
@[reassoc]
theorem comp_conjBy {T : C} (h : T ⟶ G) :
    h ≫ conjBy g = (toUnit T ≫ g) * h * (toUnit T ≫ g)⁻¹ := by
  rw [conjBy, ← Category.assoc, comp_lift, Category.comp_id,
    comp_toUnit_assoc, lift_conj_eq_mul_mul_inv]

/-- Fixing a group section in conjugation gives a monoid morphism, without
requiring that section itself to be a monoid morphism. -/
instance conjBy_isMonHom : IsMonHom (conjBy g) :=
  isMonHom_of_mul_hom (conjBy g) (by
    simp only [MonObj.mul_eq_mul, MonObj.comp_mul, tensorHom_fst,
      tensorHom_snd, comp_conjBy]
    simp [_root_.mul_assoc])

/-- Fixed-section conjugation followed by inverse conjugation is the identity. -/
@[reassoc (attr := simp)]
theorem conjBy_comp_conjBy_inv : conjBy g ≫ conjBy g⁻¹ = 𝟙 G := by
  have hc : conjBy g = (toUnit G ≫ g) * (𝟙 G) * (toUnit G ≫ g)⁻¹ := by
    simpa only [Category.id_comp] using comp_conjBy g (𝟙 G)
  rw [comp_conjBy]
  simp [GrpObj.comp_inv, hc, _root_.mul_assoc]

/-- Inverse conjugation followed by fixed-section conjugation is the identity. -/
@[reassoc (attr := simp)]
theorem conjBy_inv_comp_conjBy : conjBy g⁻¹ ≫ conjBy g = 𝟙 G := by
  simpa only [_root_.inv_inv] using conjBy_comp_conjBy_inv (g⁻¹)

/-- Fixed-section conjugation bundled as a morphism of the original group object. -/
@[simps!]
def conjByHom : Grp.mk G ⟶ Grp.mk G :=
  Grp.homMk (A := Grp.mk G) (B := Grp.mk G) (conjBy g)

/-- The bundled conjugation morphism has bundled inverse conjugation as a right inverse. -/
@[reassoc (attr := simp)]
theorem conjByHom_comp_inv : conjByHom g ≫ conjByHom g⁻¹ = 𝟙 (Grp.mk G) := by
  ext
  exact conjBy_comp_conjBy_inv g

/-- The bundled conjugation morphism has bundled inverse conjugation as a left inverse. -/
@[reassoc (attr := simp)]
theorem conjByHom_inv_comp : conjByHom g⁻¹ ≫ conjByHom g = 𝟙 (Grp.mk G) := by
  ext
  exact conjBy_inv_comp_conjBy g

end CategoryTheory.GrpObj

namespace CategoryTheory.ModObj

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {G X : C}

section Monoid

variable [MonObj G] [ModObj G X] (x : 𝟙_ C ⟶ X) (g : 𝟙_ C ⟶ G)

/-- Translating a section uses the original action on every test object. -/
theorem comp_smul_section (T : C) :
    toUnit T ≫ (lift g x ≫ γ[G, X]) =
      (toUnit T ≫ g) • (toUnit T ≫ x) :=
  comp_smul (toUnit T) g x

end Monoid

variable [GrpObj G] [ModObj G X] (x : 𝟙_ C ⟶ X) (g : 𝟙_ C ⟶ G)
  [HasPullback (orbitMap G x) x]
  [HasPullback (orbitMap G (g • x)) (g • x)]

omit [HasPullback (orbitMap G (g • x)) (g • x)] in
private theorem stabilizerConj_fixes {T : C} (a : T ⟶ stabilizer G x) :
    ((a ≫ stabilizerι G x) ≫ GrpObj.conjBy g) • (toUnit T ≫ (g • x)) =
      toUnit T ≫ (g • x) := by
  rw [GrpObj.comp_conjBy]
  simp only [comp_smul]
  rw [SemigroupAction.mul_smul, SemigroupAction.mul_smul,
    inv_smul_smul, stabilizer_fixes]

omit [HasPullback (orbitMap G x) x] in
private theorem stabilizerConjInv_fixes {T : C}
    (b : T ⟶ stabilizer G (g • x)) :
    ((b ≫ stabilizerι G (g • x)) ≫ GrpObj.conjBy g⁻¹) • (toUnit T ≫ x) =
      toUnit T ≫ x := by
  have hb : (b ≫ stabilizerι G (g • x)) •
      ((toUnit T ≫ g) • (toUnit T ≫ x)) =
        (toUnit T ≫ g) • (toUnit T ≫ x) := by
    simpa only [comp_smul] using stabilizer_fixes (G := G) (g • x) b
  rw [GrpObj.comp_conjBy]
  simp only [GrpObj.comp_inv, inv_inv]
  rw [SemigroupAction.mul_smul, SemigroupAction.mul_smul, hb, inv_smul_smul]

/-- Conjugation by a group section restricts to an isomorphism of the two
chosen stabilizer group objects. Here `g • x = lift g x ≫ γ[G, X]` uses the
given action, and no homomorphism condition is imposed on `g`. -/
def stabilizerConjIso :
    Grp.mk (stabilizer G x) ≅ Grp.mk (stabilizer G (g • x)) := by
  let f := stabilizerLiftHom (G := G) (g • x) (Grp.mk (stabilizer G x))
    (stabilizerιHom (G := G) x ≫ GrpObj.conjByHom g) (by
      simp only [Grp.comp_hom_hom, stabilizerιHom_hom_hom,
        GrpObj.conjByHom_hom_hom, comp_orbitMap]
      simpa only [Category.id_comp] using stabilizerConj_fixes x g (𝟙 _))
  let k := stabilizerLiftHom (G := G) x (Grp.mk (stabilizer G (g • x)))
    (stabilizerιHom (G := G) (g • x) ≫ GrpObj.conjByHom g⁻¹) (by
      simp only [Grp.comp_hom_hom, stabilizerιHom_hom_hom,
        GrpObj.conjByHom_hom_hom, comp_orbitMap]
      simpa only [Category.id_comp] using stabilizerConjInv_fixes x g (𝟙 _))
  have hf : f ≫ stabilizerιHom (G := G) (g • x) =
      stabilizerιHom (G := G) x ≫ GrpObj.conjByHom g :=
    stabilizerLiftHom_ι (G := G) (g • x) _ _ _
  have hk : k ≫ stabilizerιHom (G := G) x =
      stabilizerιHom (G := G) (g • x) ≫ GrpObj.conjByHom g⁻¹ :=
    stabilizerLiftHom_ι (G := G) x _ _ _
  refine ⟨f, k, ?_, ?_⟩
  · apply Grp.hom_ext
    apply stabilizer_hom_ext (G := G) x
    have h : (f ≫ k) ≫ stabilizerιHom (G := G) x = stabilizerιHom (G := G) x := by
      rw [Category.assoc, hk, ← Category.assoc, hf, Category.assoc,
        GrpObj.conjByHom_comp_inv, Category.comp_id]
    simpa only [Grp.comp_hom_hom, Grp.id_hom_hom, stabilizerιHom_hom_hom,
      Category.id_comp] using
      congrArg (fun f : Grp.mk (stabilizer G x) ⟶ Grp.mk G ↦ f.hom.hom) h
  · apply Grp.hom_ext
    apply stabilizer_hom_ext (G := G) (g • x)
    have h : (k ≫ f) ≫ stabilizerιHom (G := G) (g • x) =
        stabilizerιHom (G := G) (g • x) := by
      rw [Category.assoc, hf, ← Category.assoc, hk, Category.assoc,
        GrpObj.conjByHom_inv_comp, Category.comp_id]
    simpa only [Grp.comp_hom_hom, Grp.id_hom_hom, stabilizerιHom_hom_hom,
      Category.id_comp] using
      congrArg (fun f : Grp.mk (stabilizer G (g • x)) ⟶ Grp.mk G ↦ f.hom.hom) h

/-- The forward inclusion square in the category of group objects. -/
@[reassoc]
theorem stabilizerConjIso_hom_ιHom :
    (stabilizerConjIso x g).hom ≫ stabilizerιHom (G := G) (g • x) =
      stabilizerιHom (G := G) x ≫ GrpObj.conjByHom g :=
  stabilizerLiftHom_ι (G := G) (g • x) (Grp.mk (stabilizer G x))
    (stabilizerιHom (G := G) x ≫ GrpObj.conjByHom g) (by
      simp only [Grp.comp_hom_hom, stabilizerιHom_hom_hom,
        GrpObj.conjByHom_hom_hom, comp_orbitMap]
      simpa only [Category.id_comp] using stabilizerConj_fixes x g (𝟙 _))

/-- The inverse inclusion square in the category of group objects. -/
@[reassoc]
theorem stabilizerConjIso_inv_ιHom :
    (stabilizerConjIso x g).inv ≫ stabilizerιHom (G := G) x =
      stabilizerιHom (G := G) (g • x) ≫ GrpObj.conjByHom g⁻¹ :=
  stabilizerLiftHom_ι (G := G) x (Grp.mk (stabilizer G (g • x)))
    (stabilizerιHom (G := G) (g • x) ≫ GrpObj.conjByHom g⁻¹) (by
      simp only [Grp.comp_hom_hom, stabilizerιHom_hom_hom,
        GrpObj.conjByHom_hom_hom, comp_orbitMap]
      simpa only [Category.id_comp] using stabilizerConjInv_fixes x g (𝟙 _))

/-- The underlying forward morphism is the restriction of conjugation. -/
@[reassoc (attr := simp)]
theorem stabilizerConjIso_hom_ι :
    (stabilizerConjIso x g).hom.hom.hom ≫ stabilizerι G (g • x) =
      stabilizerι G x ≫ GrpObj.conjBy g := by
  simpa only [Grp.comp_hom_hom, stabilizerιHom_hom_hom, GrpObj.conjByHom_hom_hom] using
    congrArg (fun f : Grp.mk (stabilizer G x) ⟶ Grp.mk G ↦ f.hom.hom)
      (stabilizerConjIso_hom_ιHom x g)

/-- The underlying inverse morphism restricts inverse conjugation and targets
exactly the original chosen stabilizer. -/
@[reassoc (attr := simp)]
theorem stabilizerConjIso_inv_ι :
    (stabilizerConjIso x g).inv.hom.hom ≫ stabilizerι G x =
      stabilizerι G (g • x) ≫ GrpObj.conjBy g⁻¹ := by
  simpa only [Grp.comp_hom_hom, stabilizerιHom_hom_hom, GrpObj.conjByHom_hom_hom] using
    congrArg (fun f : Grp.mk (stabilizer G (g • x)) ⟶ Grp.mk G ↦ f.hom.hom)
      (stabilizerConjIso_inv_ιHom x g)

/-- The forward restriction followed by the inverse is the identity on the
original chosen pullback. -/
@[reassoc (attr := simp)]
theorem stabilizerConjIso_hom_inv_id :
    (stabilizerConjIso x g).hom.hom.hom ≫ (stabilizerConjIso x g).inv.hom.hom =
      𝟙 (stabilizer G x) := by
  simpa only [Grp.comp_hom_hom, Grp.id_hom_hom] using
    congrArg (fun f : Grp.mk (stabilizer G x) ⟶ Grp.mk (stabilizer G x) ↦ f.hom.hom)
      (stabilizerConjIso x g).hom_inv_id

/-- The inverse restriction followed by the forward restriction is the identity. -/
@[reassoc (attr := simp)]
theorem stabilizerConjIso_inv_hom_id :
    (stabilizerConjIso x g).inv.hom.hom ≫ (stabilizerConjIso x g).hom.hom.hom =
      𝟙 (stabilizer G (g • x)) := by
  simpa only [Grp.comp_hom_hom, Grp.id_hom_hom] using
    congrArg
      (fun f : Grp.mk (stabilizer G (g • x)) ⟶ Grp.mk (stabilizer G (g • x)) ↦ f.hom.hom)
      (stabilizerConjIso x g).inv_hom_id

/-- The inclusion square uniquely determines the forward restriction. -/
theorem stabilizerConjIso_hom_unique {f : stabilizer G x ⟶ stabilizer G (g • x)}
    (hf : f ≫ stabilizerι G (g • x) = stabilizerι G x ≫ GrpObj.conjBy g) :
    f = (stabilizerConjIso x g).hom.hom.hom :=
  stabilizer_hom_ext (G := G) (g • x) (hf.trans (stabilizerConjIso_hom_ι x g).symm)

/-- The inclusion square uniquely determines the inverse restriction. -/
theorem stabilizerConjIso_inv_unique {f : stabilizer G (g • x) ⟶ stabilizer G x}
    (hf : f ≫ stabilizerι G x = stabilizerι G (g • x) ≫ GrpObj.conjBy g⁻¹) :
    f = (stabilizerConjIso x g).inv.hom.hom :=
  stabilizer_hom_ext (G := G) x (hf.trans (stabilizerConjIso_inv_ι x g).symm)

/-- On every test object, the forward restriction sends `h` to `g * h * g⁻¹`. -/
theorem stabilizerConjIso_hom_apply_ι {T : C} (a : T ⟶ stabilizer G x) :
    (a ≫ (stabilizerConjIso x g).hom.hom.hom) ≫ stabilizerι G (g • x) =
      (toUnit T ≫ g) * (a ≫ stabilizerι G x) * (toUnit T ≫ g)⁻¹ := by
  rw [Category.assoc, stabilizerConjIso_hom_ι, ← Category.assoc, GrpObj.comp_conjBy]

/-- On every test object, the inverse restriction sends `k` to `g⁻¹ * k * g`. -/
theorem stabilizerConjIso_inv_apply_ι {T : C} (b : T ⟶ stabilizer G (g • x)) :
    (b ≫ (stabilizerConjIso x g).inv.hom.hom) ≫ stabilizerι G x =
      (toUnit T ≫ g)⁻¹ * (b ≫ stabilizerι G (g • x)) * (toUnit T ≫ g) := by
  rw [Category.assoc, stabilizerConjIso_inv_ι, ← Category.assoc]
  simp only [GrpObj.comp_conjBy, GrpObj.comp_inv, inv_inv]

/-- Conjugacy on ordinary stabilizer subgroups induced by the internal isomorphism
through the existing generalized-point stabilizer equivalences. -/
def stabilizerConjPointsEquiv (T : C) :
    MulAction.stabilizer (T ⟶ G) (toUnit T ≫ x) ≃*
      MulAction.stabilizer (T ⟶ G) (toUnit T ≫ (g • x)) :=
  ((stabilizerHomEquiv (G := G) x T).symm.trans
    (Hom.mulEquivCongrRight (asIso (stabilizerConjIso x g).hom.hom.hom) T)).trans
    (stabilizerHomEquiv (G := G) (g • x) T)

/-- The conjugacy equivalence agrees with postcomposition under `stabilizerHomEquiv`. -/
@[simp]
theorem stabilizerConjPointsEquiv_homEquiv (T : C) (a : T ⟶ stabilizer G x) :
    stabilizerConjPointsEquiv x g T (stabilizerHomEquiv (G := G) x T a) =
      stabilizerHomEquiv (G := G) (g • x) T
        (a ≫ (stabilizerConjIso x g).hom.hom.hom) := by
  simp [stabilizerConjPointsEquiv]
  rfl

/-- The inverse conjugacy equivalence agrees with inverse postcomposition under
`stabilizerHomEquiv`. -/
@[simp]
theorem stabilizerConjPointsEquiv_symm_homEquiv (T : C)
    (b : T ⟶ stabilizer G (g • x)) :
    (stabilizerConjPointsEquiv x g T).symm (stabilizerHomEquiv (G := G) (g • x) T b) =
      stabilizerHomEquiv (G := G) x T
        (b ≫ (stabilizerConjIso x g).inv.hom.hom) := by
  apply (stabilizerConjPointsEquiv x g T).injective
  rw [MulEquiv.apply_symm_apply, stabilizerConjPointsEquiv_homEquiv,
    Category.assoc, stabilizerConjIso_inv_hom_id, Category.comp_id]

/-- The induced ordinary-stabilizer equivalence has the conjugation formula. -/
@[simp]
theorem stabilizerConjPointsEquiv_apply (T : C)
    (a : MulAction.stabilizer (T ⟶ G) (toUnit T ≫ x)) :
    (stabilizerConjPointsEquiv x g T a).val =
      (toUnit T ≫ g) * a.val * (toUnit T ≫ g)⁻¹ := by
  obtain ⟨a, rfl⟩ := (stabilizerHomEquiv (G := G) x T).surjective a
  simpa only [stabilizerConjPointsEquiv_homEquiv, stabilizerHomEquiv_apply] using
    stabilizerConjIso_hom_apply_ι x g a

/-- The inverse induced equivalence has the inverse-conjugation formula. -/
@[simp]
theorem stabilizerConjPointsEquiv_symm_apply (T : C)
    (b : MulAction.stabilizer (T ⟶ G) (toUnit T ≫ (g • x))) :
    ((stabilizerConjPointsEquiv x g T).symm b).val =
      (toUnit T ≫ g)⁻¹ * b.val * (toUnit T ≫ g) := by
  obtain ⟨b, rfl⟩ := (stabilizerHomEquiv (G := G) (g • x) T).surjective b
  simpa only [stabilizerConjPointsEquiv_symm_homEquiv, stabilizerHomEquiv_apply] using
    stabilizerConjIso_inv_apply_ι x g b

/-- Conjugacy commutes with precomposition by every morphism of test objects. -/
theorem stabilizerConjPointsEquiv_natural {T T' : C} (f : T' ⟶ T)
    (a : MulAction.stabilizer (T ⟶ G) (toUnit T ≫ x)) :
    stabilizerPrecomp (G := G) (g • x) f (stabilizerConjPointsEquiv x g T a) =
      stabilizerConjPointsEquiv x g T' (stabilizerPrecomp (G := G) x f a) := by
  apply Subtype.ext
  simp only [stabilizerPrecomp_apply, stabilizerConjPointsEquiv_apply,
    MonObj.comp_mul, GrpObj.comp_inv, comp_toUnit_assoc]

end CategoryTheory.ModObj
