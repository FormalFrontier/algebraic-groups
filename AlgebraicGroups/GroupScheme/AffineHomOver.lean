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
-/

public section

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K]

/-- Maps from an arbitrary scheme over `Spec K` to an affine `K`-scheme are
algebra maps into its global sections; the source need not be affine. -/
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

/-- Maps of affine targets act on global-section homomorphisms by precomposition. -/
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

/-- A map to the underlying additive group scheme is specified by one global section. -/
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
