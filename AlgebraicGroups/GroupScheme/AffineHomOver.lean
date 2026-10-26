/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.Additive
public import Mathlib.AlgebraicGeometry.AffineSpace

/-!
# Morphisms to affine schemes over a base

The `algΓ`/`algSpec` adjunction identifies morphisms from any scheme over
`Spec K` to an affine `K`-scheme with algebra maps into global sections.
For the underlying additive group scheme these maps are individual sections.
No field or affineness assumption on the source is needed.

Milne's affine-point formula and additive-group example concern schemes over
a field and affine test schemes; the adjunction here also applies to arbitrary
source schemes over any commutative base ring.

## References

- James S. Milne, *Algebraic Groups* (2017), items 1.4 and 2.1: the
  field-based affine functor-of-points formula and additive-group example.
- Mathlib, `algΓAlgSpecAdjunction` and its naturality, together with
  `SymmetricAlgebra.lift` and `LinearMap.ringLmapEquivSelf`: the adjunction
  and algebraic equivalences used for the arbitrary-base statements.
-/

public section

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K]

/-- Maps from an arbitrary scheme over `Spec K` to an affine `K`-scheme are
algebra maps into its global sections; the source need not be affine. This
uses Mathlib's `algΓAlgSpecAdjunction`; for affine tests over a field, Milne's
*Algebraic Groups* (2017), item 1.4 gives the antecedent. -/
@[expose] def affineSpecHomOverEquiv (X : Over (Spec (.of K)))
    (A : Type u) [CommRing A] [Algebra K A] :
    (X ⟶ (algSpec (.of K)).obj (.op (CommAlgCat.of K A))) ≃
      (A →ₐ[K] ((algΓ (.of K)).obj X).unop) where
  toFun h := ((algΓAlgSpecAdjunction (.of K)).homEquiv X
    (.op (CommAlgCat.of K A))).symm h |>.unop.hom
  invFun h := (algΓAlgSpecAdjunction (.of K)).homEquiv X
    (.op (CommAlgCat.of K A)) (CommAlgCat.ofHom h).op
  left_inv h := by
    simpa only [CommAlgCat.ofHom_hom, Quiver.Hom.op_unop] using
      ((algΓAlgSpecAdjunction (.of K)).homEquiv X
        (.op (CommAlgCat.of K A))).apply_symm_apply h
  right_inv h := by
    simp only [Quiver.Hom.unop_op, Equiv.symm_apply_apply, CommAlgCat.hom_ofHom]

section

variable (R : Type u) [CommRing R]

/-- The `algSpec` presentation of an affine target is isomorphic over the base
to its spectrum with the algebra-induced structure morphism. -/
@[expose]
def affineSpecHomOverTargetIso (A : Type u) [CommRing A] [Algebra R A] :
    (algSpec (.of R)).obj (.op (CommAlgCat.of R A)) ≅
      (Spec (.of A)).asOver (Spec (.of R)) :=
  Over.isoMk (Iso.refl (Spec (.of A))) (by
    change 𝟙 (Spec (.of A)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap R A))
    exact Category.id_comp _)

/-- The target comparison is the identity on the underlying spectrum. -/
@[simp] theorem affineSpecHomOverTargetIso_hom_left
    (A : Type u) [CommRing A] [Algebra R A] :
    (affineSpecHomOverTargetIso R A).hom.left = 𝟙 (Spec (.of A)) := rfl

/-- The inverse target comparison is the identity on the underlying spectrum. -/
@[simp] theorem affineSpecHomOverTargetIso_inv_left
    (A : Type u) [CommRing A] [Algebra R A] :
    (affineSpecHomOverTargetIso R A).inv.left = 𝟙 (Spec (.of A)) := rfl

/-- The underlying ring map of the affine-target comparison is pullback on global
sections, normalized by the inverse spectrum global-sections isomorphism. -/
theorem affineSpecHomOverEquiv_apply_toRingHom
    (X : Over (Spec (.of R))) (A : Type u) [CommRing A] [Algebra R A]
    (h : X ⟶ (algSpec (.of R)).obj (.op (CommAlgCat.of R A))) :
    CommRingCat.ofHom (affineSpecHomOverEquiv R X A h).toRingHom =
      (Scheme.ΓSpecIso (.of A)).inv ≫ h.left.appTop := by
  change CommRingCat.ofHom
    ((((algΓAlgSpecAdjunction (.of R)).homEquiv X
      (.op (CommAlgCat.of R A))).symm h).unop.hom.toRingHom) = _
  rw [Adjunction.homEquiv_symm_apply]
  rfl

end

/-- Maps of affine targets act on global-section homomorphisms by
precomposition, using Mathlib's naturality of `algΓAlgSpecAdjunction`. -/
theorem affineSpecHomOverEquiv_comp (X : Over (Spec (.of K)))
    (A B : Type u) [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    (f : B →ₐ[K] A)
    (h : X ⟶ (algSpec (.of K)).obj (.op (CommAlgCat.of K A))) :
    affineSpecHomOverEquiv K X B
      (h ≫ (algSpec (.of K)).map (CommAlgCat.ofHom f).op) =
      (affineSpecHomOverEquiv K X A h).comp f := by
  apply AlgHom.ext
  intro a
  exact congrArg (fun k : (algΓ (.of K)).obj X ⟶
      Opposite.op (CommAlgCat.of K B) ↦ k.unop.hom a)
    ((algΓAlgSpecAdjunction (.of K)).homEquiv_naturality_right_symm h
      (CommAlgCat.ofHom f).op)

/-- A map to the underlying additive group scheme is specified by one global
section. On affine field-based tests this recovers Milne's *Algebraic Groups*
(2017), item 2.1; the general equivalence uses Mathlib's
`SymmetricAlgebra.lift`. -/
@[expose] def additiveGroupHomOverEquiv (X : Over (Spec (.of K))) :
    (X ⟶ (additiveGroupScheme K).X) ≃
      ((algΓ (.of K)).obj X).unop :=
  ((affineSpecHomOverEquiv K X (additiveGroupCoordinateRing K)).trans
    SymmetricAlgebra.lift.symm).trans
      (LinearMap.ringLmapEquivSelf K K ((algΓ (.of K)).obj X).unop).toEquiv

namespace AffineHomOver

/-- The inverse of the symmetric-algebra lift reads the image of a generator.
This is used for both affine additive-product and vector-group projections. -/
theorem symmetricAlgebra_lift_symm_ι
    (M : Type u) [AddCommMonoid M] [Module K M]
    (A : Type u) [CommRing A] [Algebra K A]
    (h : SymmetricAlgebra K M →ₐ[K] A) (m : M) :
    (SymmetricAlgebra.lift.symm h) m = h (SymmetricAlgebra.ι K M m) := by
  have eq := congrArg (fun f : SymmetricAlgebra K M →ₐ[K] A ↦
    f (SymmetricAlgebra.ι K M m))
      ((SymmetricAlgebra.lift (R := K) (M := M)).apply_symm_apply h)
  simpa only [SymmetricAlgebra.lift_ι_apply] using eq

end AffineHomOver

end AlgebraicGeometry
