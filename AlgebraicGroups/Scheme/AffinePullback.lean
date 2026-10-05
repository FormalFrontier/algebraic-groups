/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Tensor products from cartesian affine squares

A cartesian square of affine schemes identifies its coordinate ring with the
corresponding tensor-product pushout. This file records the resulting linear
equivalence with an explicit formula for pure tensors.

The proof uses Mathlib's tensor-product pushout, contravariance of `Spec` and
reflection of isomorphisms by affine spectra. The square's projection order
fixes the formula `e (b₀ ⊗ₜ b₁) = p1 b₀ * c b₁`.

## References

* Stacks Project, Lemma 26.17.2 (tag 01JQ), for affine fibre products
  represented by tensor products.
* Mathlib, `Mathlib.Algebra.Category.Ring.Constructions` for
  `CommRingCat.isPushout_tensorProduct`, `Mathlib.AlgebraicGeometry.Pullbacks`
  for `isPullback_SpecMap_of_isPushout`, and
  `Mathlib.AlgebraicGeometry.Morphisms.IsIso` for `isIso_SpecMap_iff`.
-/

public section

open CategoryTheory Limits
open scoped TensorProduct

noncomputable section

namespace AlgebraicGeometry


universe u

variable {A B D : Type u} [CommRing A] [CommRing B] [CommRing D]
  [Algebra A B]

/-- Contravariant affine-spectrum map induced by a ring homomorphism. -/
abbrev specMapRing {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) : Spec (.of S) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom f)

/-- A cartesian square of affine spectra identifies its coordinate ring with
the tensor pushout, as in Stacks Project, Lemma 26.17.2 (tag 01JQ). The
displayed formula fixes the projection orientation: `p1` acts on the first
tensor factor and `c` on the second. -/
lemma exists_tensorLinearEquiv_of_isPullback (c p1 : B →+* D)
    (hbase : c.comp (algebraMap A B) = p1.comp (algebraMap A B))
    (hcart : IsPullback
      (specMapRing c) (specMapRing p1)
      (specMapRing (algebraMap A B)) (specMapRing (algebraMap A B))) :
    letI : Algebra B D := p1.toAlgebra
    ∃ e : B ⊗[A] B ≃ₗ[B] D,
      ∀ b₀ b₁, e (b₀ ⊗ₜ[A] b₁) = p1 b₀ * c b₁ := by
  let _ : Algebra B D := p1.toAlgebra
  let _ : Algebra A D := (p1.comp (algebraMap A B)).toAlgebra
  let _ : IsScalarTower A B D := IsScalarTower.of_algebraMap_eq' rfl
  let cA : B →ₐ[A] D :=
    { c with
      commutes' := fun x ↦ DFunLike.congr_fun hbase x }
  let phi : B ⊗[A] B →ₐ[B] D :=
    Algebra.TensorProduct.lift (Algebra.ofId B D) cA
      (fun _ _ ↦ Commute.all _ _)
  let inl : B →+* B ⊗[A] B :=
    Algebra.TensorProduct.includeLeftRingHom
  let inr : B →+* B ⊗[A] B :=
    Algebra.TensorProduct.includeRight.toRingHom
  have hPush : IsPushout
      (CommRingCat.ofHom (algebraMap A B))
      (CommRingCat.ofHom (algebraMap A B))
      (CommRingCat.ofHom inl) (CommRingCat.ofHom inr) := by
    exact CommRingCat.isPushout_tensorProduct A B B
  let hTensor : IsPullback
      (specMapRing inl) (specMapRing inr)
      (specMapRing (algebraMap A B)) (specMapRing (algebraMap A B)) :=
    AlgebraicGeometry.isPullback_SpecMap_of_isPushout _ _ _ _ hPush
  let eSpec : Spec (.of D) ≅ Spec (.of (B ⊗[A] B)) :=
    hcart.flip.isoIsPullback _ _ hTensor
  have hphi_inl : CommRingCat.ofHom inl ≫
      CommRingCat.ofHom phi.toRingHom = CommRingCat.ofHom p1 := by
    ext x
    change phi (inl x) = p1 x
    simp [phi, inl, RingHom.algebraMap_toAlgebra]
  have hphi_inr : CommRingCat.ofHom inr ≫
      CommRingCat.ofHom phi.toRingHom = CommRingCat.ofHom c := by
    ext x
    change phi (inr x) = c x
    simp [phi, inr, cA]
  have hSpec : specMapRing phi.toRingHom = eSpec.hom := by
    apply hTensor.hom_ext
    · rw [← Spec.map_comp, hphi_inl]
      exact (hcart.flip.isoIsPullback_hom_fst _ _ hTensor).symm
    · rw [← Spec.map_comp, hphi_inr]
      exact (hcart.flip.isoIsPullback_hom_snd _ _ hTensor).symm
  have hSpecIso : IsIso (specMapRing phi.toRingHom) := by
    rw [hSpec]
    infer_instance
  have hphi : Function.Bijective phi :=
    AlgebraicGeometry.isIso_SpecMap_iff.mp hSpecIso
  let e : B ⊗[A] B ≃ₗ[B] D :=
    LinearEquiv.ofBijective phi.toLinearMap hphi
  refine ⟨e, fun b₀ b₁ ↦ ?_⟩
  change phi (b₀ ⊗ₜ[A] b₁) = p1 b₀ * c b₁
  simp [phi, cA, RingHom.algebraMap_toAlgebra]

end AlgebraicGeometry
