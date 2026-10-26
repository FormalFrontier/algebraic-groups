/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.AffineHomOver
public import Mathlib.AlgebraicGeometry.Group.Affine

/-!
# Affine-target morphisms and convolution on global sections

For a commutative `R`-bialgebra `A`, morphisms from any scheme over `Spec R`
to `Spec A` carry the pointwise monoid structure induced by `bialgSpec`.
The global-sections comparison refines `affineSpecHomOverEquiv` to a
multiplicative equivalence with `WithConv (A →ₐ[R] Γ(X))`.

The geometric target is `(Spec (.of A)).asOver (Spec (.of R))`, with Mathlib's
bialgebra-induced `MonObj`. The target isomorphism in `AffineHomOver` compares this
presentation with `algSpec.obj` in the underlying equivalence. The coefficient
algebra is the bundled object of `algΓ`; no affineness assumption on the source
or separate algebra structure on its global sections is required.

The two monoid structures are independent: `CategoryTheory.Hom.monoid` uses
the diagonal followed by the target multiplication, and `AlgHom` convolution
uses the coproduct of `A`. The bundled equivalence supplies `map_one` and
`map_mul`. On affine sources the comparison agrees with `Spec.mapMulEquiv.symm`
after applying `Scheme.ΓSpecIso.hom` to the coefficients.

## References

- Mathlib, `bialgSpec`, `instMonObjSpecAsOverSpec`, `Hom.monoid`, and
  `AlgHom.convMul_def`: the geometric and algebraic monoid structures.
- Mathlib, `algΓAlgSpecAdjunction`, `Spec.mapMulEquiv`, and `Scheme.ΓSpecIso`:
  the global-sections comparison and its affine specialization.
-/

@[expose] public section

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

/-- The affine-target global-sections equivalence sends geometric pointwise
multiplication to bialgebra convolution, using the target comparison. -/
theorem affineSpecHomOverEquiv_map_mul (X : Over (Spec (.of R)))
    (A : Type u) [CommRing A] [Bialgebra R A]
    (f g : X ⟶ (Spec (.of A)).asOver (Spec (.of R))) :
    WithConv.toConv (affineSpecHomOverEquiv R X A
      ((f * g) ≫ (affineSpecHomOverTargetIso R A).inv)) =
      WithConv.toConv (affineSpecHomOverEquiv R X A
        (f ≫ (affineSpecHomOverTargetIso R A).inv)) *
      WithConv.toConv (affineSpecHomOverEquiv R X A
        (g ≫ (affineSpecHomOverTargetIso R A).inv)) := by
  let T := ((algΓ (.of R)).obj X).unop
  let k : X ⟶ (Spec (.of T)).asOver (Spec (.of R)) :=
    (algΓAlgSpecAdjunction (.of R)).unit.app X ≫
      (affineSpecHomOverTargetIso R T).hom
  have factor (q : WithConv (A →ₐ[R] T)) :
      (affineSpecHomOverEquiv R X A).symm q.ofConv ≫
          (affineSpecHomOverTargetIso R A).hom =
        k ≫ Spec.mapMulEquiv (R := R) (S := A) (T := T) q := by
    change (algΓAlgSpecAdjunction (.of R)).homEquiv X
        (.op (CommAlgCat.of R A)) (CommAlgCat.ofHom q.ofConv).op ≫
          (affineSpecHomOverTargetIso R A).hom = _
    rw [Adjunction.homEquiv_unit]
    apply Over.OverMorphism.ext
    change (((algΓAlgSpecAdjunction (.of R)).unit.app X).left ≫
        Spec.map (CommRingCat.ofHom q.ofConv.toRingHom)) ≫ 𝟙 _ =
      (((algΓAlgSpecAdjunction (.of R)).unit.app X).left ≫ 𝟙 _) ≫
        Spec.map (CommRingCat.ofHom q.ofConv.toRingHom)
    simp only [Category.comp_id]
  have inverse_mul (p q : WithConv (A →ₐ[R] T)) :
      (affineSpecHomOverEquiv R X A).symm (p * q).ofConv ≫
          (affineSpecHomOverTargetIso R A).hom =
        ((affineSpecHomOverEquiv R X A).symm p.ofConv ≫
          (affineSpecHomOverTargetIso R A).hom) *
        ((affineSpecHomOverEquiv R X A).symm q.ofConv ≫
          (affineSpecHomOverTargetIso R A).hom) := by
    calc
      _ = k ≫ Spec.mapMulEquiv (R := R) (S := A) (T := T) (p * q) := factor _
      _ = (k ≫ Spec.mapMulEquiv (R := R) (S := A) (T := T) p) *
          (k ≫ Spec.mapMulEquiv (R := R) (S := A) (T := T) q) := by
        rw [map_mul, MonObj.comp_mul]
      _ = _ := by rw [← factor p, ← factor q]
  apply WithConv.ofConv_injective
  apply (affineSpecHomOverEquiv R X A).symm.injective
  apply (cancel_mono (affineSpecHomOverTargetIso R A).hom).1
  simp only [Equiv.symm_apply_apply, inverse_mul,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Morphisms from an arbitrary over-scheme to the spectrum of a commutative
bialgebra correspond multiplicatively to convolution algebra maps into global
sections. The underlying equivalence is `affineSpecHomOverEquiv`, after the
spectrum target comparison and `WithConv.toConv`. -/
def affineSpecHomOverMulEquiv (X : Over (Spec (.of R)))
    (A : Type u) [CommRing A] [Bialgebra R A] :
    (X ⟶ (Spec (.of A)).asOver (Spec (.of R))) ≃*
      WithConv (A →ₐ[R] ((algΓ (.of R)).obj X).unop) where
  toEquiv := ((affineSpecHomOverTargetIso R A).symm.homToEquiv).trans
    ((affineSpecHomOverEquiv R X A).trans (WithConv.equiv _).symm)
  map_mul' f g := affineSpecHomOverEquiv_map_mul R X A f g

/-- Forgetting `WithConv` recovers the underlying affine-target equivalence. -/
@[simp] theorem affineSpecHomOverMulEquiv_apply_ofConv (X : Over (Spec (.of R)))
    (A : Type u) [CommRing A] [Bialgebra R A]
    (h : X ⟶ (Spec (.of A)).asOver (Spec (.of R))) :
    (affineSpecHomOverMulEquiv R X A h).ofConv =
      affineSpecHomOverEquiv R X A
        (h ≫ (affineSpecHomOverTargetIso R A).inv) := rfl

/-- The inverse forgets `WithConv`, uses the underlying equivalence, and
returns to the spectrum presentation of the target. -/
@[simp] theorem affineSpecHomOverMulEquiv_symm_apply (X : Over (Spec (.of R)))
    (A : Type u) [CommRing A] [Bialgebra R A]
    (q : WithConv (A →ₐ[R] ((algΓ (.of R)).obj X).unop)) :
    (affineSpecHomOverMulEquiv R X A).symm q =
      (affineSpecHomOverEquiv R X A).symm q.ofConv ≫
        (affineSpecHomOverTargetIso R A).hom := rfl

/-- The forward ring map is pullback on global sections, normalized by the
inverse of the spectrum global-sections isomorphism. -/
theorem affineSpecHomOverMulEquiv_apply_toRingHom (X : Over (Spec (.of R)))
    (A : Type u) [CommRing A] [Bialgebra R A]
    (h : X ⟶ (Spec (.of A)).asOver (Spec (.of R))) :
    CommRingCat.ofHom (affineSpecHomOverMulEquiv R X A h).ofConv.toRingHom =
      (Scheme.ΓSpecIso (.of A)).inv ≫ h.left.appTop := by
  rw [affineSpecHomOverMulEquiv_apply_ofConv,
    affineSpecHomOverEquiv_apply_toRingHom]
  let hs : X.left ⟶ Spec (.of A) := h.left
  change (Scheme.ΓSpecIso (.of A)).inv ≫ (hs ≫ 𝟙 (Spec (.of A))).appTop =
    (Scheme.ΓSpecIso (.of A)).inv ≫ hs.appTop
  exact congrArg (fun k : X.left ⟶ Spec (.of A) ↦
    (Scheme.ΓSpecIso (.of A)).inv ≫ k.appTop) (Category.comp_id hs)

/-- The inverse has underlying scheme map given by the affinization unit
followed by the spectrum of the coordinate map. -/
theorem affineSpecHomOverMulEquiv_symm_apply_left (X : Over (Spec (.of R)))
    (A : Type u) [CommRing A] [Bialgebra R A]
    (q : WithConv (A →ₐ[R] ((algΓ (.of R)).obj X).unop)) :
    ((affineSpecHomOverMulEquiv R X A).symm q).left =
      X.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom q.ofConv.toRingHom) := by
  let φ : CommRingCat.of A ⟶ Γ(X.left, ⊤) :=
    CommRingCat.ofHom q.ofConv.toRingHom
  have unit_formula :
      (ΓSpec.adjunction.homEquiv X.left (.op (.of A))) φ.op =
        X.left.toSpecΓ ≫ Spec.map φ := rfl
  apply ext_to_Spec
  change (Scheme.ΓSpecIso (.of A)).inv ≫
      ((affineSpecHomOverMulEquiv R X A).symm q).left.appTop =
    (Scheme.ΓSpecIso (.of A)).inv ≫
      (X.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom q.ofConv.toRingHom)).appTop
  rw [← affineSpecHomOverMulEquiv_apply_toRingHom R X A
    ((affineSpecHomOverMulEquiv R X A).symm q), MulEquiv.apply_symm_apply]
  exact (ΓSpecIso_inv_ΓSpec_adjunction_homEquiv (X := X.left) φ).symm.trans
    (congrArg (fun k : X.left ⟶ Spec (.of A) ↦
      (Scheme.ΓSpecIso (.of A)).inv ≫ k.appTop) unit_formula)

/-- Pullback along any morphism of over-schemes corresponds to postcomposition
by the canonical algebra map on global sections. -/
theorem affineSpecHomOverMulEquiv_naturality_source
    (X Y : Over (Spec (.of R))) (A : Type u) [CommRing A] [Bialgebra R A]
    (f : Y ⟶ X) (h : X ⟶ (Spec (.of A)).asOver (Spec (.of R))) :
    affineSpecHomOverMulEquiv R Y A (f ≫ h) =
      WithConv.toConv (((algΓ (.of R)).map f).unop.hom.comp
        (affineSpecHomOverMulEquiv R X A h).ofConv) := by
  apply WithConv.ofConv_injective
  simp only [affineSpecHomOverMulEquiv_apply_ofConv,
    Category.assoc]
  apply AlgHom.ext
  intro a
  exact congrArg (fun k : (algΓ (.of R)).obj Y ⟶
      Opposite.op (CommAlgCat.of R A) ↦ k.unop.hom a)
    ((algΓAlgSpecAdjunction (.of R)).homEquiv_naturality_left_symm f
      (h ≫ (affineSpecHomOverTargetIso R A).inv))

/-- A bialgebra map induces a monoid-scheme map of affine targets, and its
point map corresponds to precomposition on convolution algebra maps. -/
theorem affineSpecHomOverMulEquiv_naturality_target (X : Over (Spec (.of R)))
    (A B : Type u) [CommRing A] [Bialgebra R A] [CommRing B] [Bialgebra R B]
    (f : B →ₐc[R] A) (h : X ⟶ (Spec (.of A)).asOver (Spec (.of R))) :
    affineSpecHomOverMulEquiv R X B
      (h ≫ ((bialgSpec (.of R)).map (CommBialgCat.ofHom f).op).hom) =
      WithConv.toConv ((affineSpecHomOverMulEquiv R X A h).ofConv.comp f.toAlgHom) := by
  let b : (Spec (.of A)).asOver (Spec (.of R)) ⟶
      (Spec (.of B)).asOver (Spec (.of R)) :=
    ((bialgSpec (.of R)).map (CommBialgCat.ofHom f).op).hom
  let a : (algSpec (.of R)).obj (.op (CommAlgCat.of R A)) ⟶
      (algSpec (.of R)).obj (.op (CommAlgCat.of R B)) :=
    (algSpec (.of R)).map (CommAlgCat.ofHom f.toAlgHom).op
  have target_naturality :
      b ≫ (affineSpecHomOverTargetIso R B).inv =
        (affineSpecHomOverTargetIso R A).inv ≫ a := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom f.toAlgHom.toRingHom) ≫ 𝟙 (Spec (.of B)) =
      𝟙 (Spec (.of A)) ≫ Spec.map (CommRingCat.ofHom f.toAlgHom.toRingHom)
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  have composite :
      (h ≫ b) ≫ (affineSpecHomOverTargetIso R B).inv =
        (h ≫ (affineSpecHomOverTargetIso R A).inv) ≫ a := by
    calc
      _ = h ≫ (b ≫ (affineSpecHomOverTargetIso R B).inv) :=
        Category.assoc h b (affineSpecHomOverTargetIso R B).inv
      _ = h ≫ ((affineSpecHomOverTargetIso R A).inv ≫ a) :=
        congrArg (fun k : (Spec (.of A)).asOver (Spec (.of R)) ⟶
            (algSpec (.of R)).obj (.op (CommAlgCat.of R B)) ↦ h ≫ k)
          target_naturality
      _ = _ := (Category.assoc h (affineSpecHomOverTargetIso R A).inv a).symm
  apply WithConv.ofConv_injective
  change affineSpecHomOverEquiv R X B
      ((h ≫ b) ≫ (affineSpecHomOverTargetIso R B).inv) =
    (affineSpecHomOverEquiv R X A
      (h ≫ (affineSpecHomOverTargetIso R A).inv)).comp f.toAlgHom
  exact (congrArg (affineSpecHomOverEquiv R X B) composite).trans
    (affineSpecHomOverEquiv_comp R X A B f.toAlgHom
      (h ≫ (affineSpecHomOverTargetIso R A).inv))

/-- On an affine source, identifying global sections with its coordinate ring
recovers the inverse of Mathlib's affine `Spec.mapMulEquiv`. The coefficient
identification is `ΓSpecIso.hom : Γ(Spec T) ⟶ T`. -/
theorem affineSpecHomOverMulEquiv_spec (A T : Type u)
    [CommRing A] [Bialgebra R A] [CommRing T] [Algebra R T]
    (h : (Spec (.of T)).asOver (Spec (.of R)) ⟶
      (Spec (.of A)).asOver (Spec (.of R))) :
    (Scheme.ΓSpecIso (.of T)).hom.hom.comp
      (affineSpecHomOverMulEquiv R ((Spec (.of T)).asOver (Spec (.of R))) A h).ofConv.toRingHom =
        ((Spec.mapMulEquiv (R := R) (S := A) (T := T)).symm h).ofConv.toRingHom := by
  let hs : Spec (.of T) ⟶ Spec (.of A) := h.left
  have coordinates :
      CommRingCat.ofHom
          (affineSpecHomOverMulEquiv R ((Spec (.of T)).asOver (Spec (.of R))) A h).ofConv.toRingHom
          ≫
        (Scheme.ΓSpecIso (.of T)).hom = Spec.preimage hs := by
    calc
      _ = ((Scheme.ΓSpecIso (.of A)).inv ≫ hs.appTop) ≫
          (Scheme.ΓSpecIso (.of T)).hom :=
        congrArg (fun k : CommRingCat.of A ⟶ Γ(Spec (.of T), ⊤) ↦
          k ≫ (Scheme.ΓSpecIso (.of T)).hom)
          (affineSpecHomOverMulEquiv_apply_toRingHom R
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
