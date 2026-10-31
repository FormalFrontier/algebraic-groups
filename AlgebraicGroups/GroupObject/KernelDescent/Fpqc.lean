/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupObject.KernelDescent
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
import AlgebraicGroups.GroupObject.EffectiveEpi
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Descent of monoid homomorphisms along fpqc morphisms

A monoid homomorphism from a group object descends uniquely through an fpqc monoid
homomorphism if it is trivial on the given categorical kernel. The base scheme is arbitrary,
and neither the intermediate monoid nor the target monoid needs a group structure.
This specializes the categorical, arbitrary-monoid-target generalization of Milne's (5.13).

The proof reuses Mathlib's effective-epimorphism, pullback, and morphism-property APIs.
For any supplied Cartesian monoidal structure on the slice, its limiting binary fans
compare its tensor maps with ordinary scheme pullback maps. Flatness and surjectivity
therefore give epimorphicity of these tensor maps without a quasi-compactness assumption.
Quasi-compactness is used only for effectiveness of the given fpqc morphism.

## References

* J. S. Milne, *Algebraic Groups* (2017), (5.13).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj

namespace AlgebraicGeometry

universe u

section TensorHom

variable {S : Scheme.{u}} [c : CartesianMonoidalCategory (Over S)]
variable {G H X Y : Over S}

private lemma tensorHom_flat_surjective (f : G ⟶ H) (g : X ⟶ Y)
    [Flat f.left] [Flat g.left] [Surjective f.left] [Surjective g.left] :
    Flat (f ⊗ₘ g).left ∧ Surjective (f ⊗ₘ g).left := by
  have hGX : IsPullback (fst G X).left (snd G X).left G.hom X.hom :=
    Over.isPullback_of_binaryFan_isLimit
      (BinaryFan.mk (fst G X) (snd G X)) (tensorProductIsBinaryProduct G X)
  have hHY : IsPullback (fst H Y).left (snd H Y).left H.hom Y.hom :=
    Over.isPullback_of_binaryFan_isLimit
      (BinaryFan.mk (fst H Y) (snd H Y)) (tensorProductIsBinaryProduct H Y)
  let m : pullback G.hom X.hom ⟶ pullback H.hom Y.hom :=
    pullback.map G.hom X.hom H.hom Y.hom f.left g.left (𝟙 S)
      ((Category.comp_id _).trans f.w.symm) ((Category.comp_id _).trans g.w.symm)
  have hmFlat : Flat m :=
    MorphismProperty.pullbackMap (P := @Flat)
      (inferInstance : Flat f.left) (inferInstance : Flat g.left) f.w.symm g.w.symm
  let hSurjectiveComp : MorphismProperty.IsStableUnderComposition (@Surjective.{u}) :=
    (inferInstance : MorphismProperty.IsMultiplicative (@Surjective.{u})).toIsStableUnderComposition
  have hmSurjective : Surjective m :=
    (@MorphismProperty.pullbackMap (Scheme.{u}) _ (@Surjective.{u}) _ hSurjectiveComp)
      (inferInstance : Surjective f.left) (inferInstance : Surjective g.left)
      f.w.symm g.w.symm
  have hfst : (f ⊗ₘ g).left ≫ (fst H Y).left = (fst G X).left ≫ f.left := by
    simpa only [Over.comp_left] using
      congrArg (fun k : G ⊗ X ⟶ H => k.left) (tensorHom_fst f g)
  have hsnd : (f ⊗ₘ g).left ≫ (snd H Y).left = (snd G X).left ≫ g.left := by
    simpa only [Over.comp_left] using
      congrArg (fun k : G ⊗ X ⟶ Y => k.left) (tensorHom_snd f g)
  have hm_fst : m ≫ pullback.fst H.hom Y.hom =
      pullback.fst G.hom X.hom ≫ f.left := by
    simp only [m, pullback.map, pullback.lift_fst]
  have hm_snd : m ≫ pullback.snd H.hom Y.hom =
      pullback.snd G.hom X.hom ≫ g.left := by
    simp only [m, pullback.map, pullback.lift_snd]
  have he : (f ⊗ₘ g).left ≫ hHY.isoPullback.hom = hGX.isoPullback.hom ≫ m := by
    apply pullback.hom_ext
    · calc
        ((f ⊗ₘ g).left ≫ hHY.isoPullback.hom) ≫ pullback.fst H.hom Y.hom =
            (f ⊗ₘ g).left ≫ (fst H Y).left := by
              rw [Category.assoc, hHY.isoPullback_hom_fst]
        _ = (fst G X).left ≫ f.left := hfst
        _ = (hGX.isoPullback.hom ≫ pullback.fst G.hom X.hom) ≫ f.left := by
              rw [hGX.isoPullback_hom_fst]
        _ = (hGX.isoPullback.hom ≫ m) ≫ pullback.fst H.hom Y.hom := by
              simp only [Category.assoc, hm_fst]
    · calc
        ((f ⊗ₘ g).left ≫ hHY.isoPullback.hom) ≫ pullback.snd H.hom Y.hom =
            (f ⊗ₘ g).left ≫ (snd H Y).left := by
              rw [Category.assoc, hHY.isoPullback_hom_snd]
        _ = (snd G X).left ≫ g.left := hsnd
        _ = (hGX.isoPullback.hom ≫ pullback.snd G.hom X.hom) ≫ g.left := by
              rw [hGX.isoPullback_hom_snd]
        _ = (hGX.isoPullback.hom ≫ m) ≫ pullback.snd H.hom Y.hom := by
              simp only [Category.assoc, hm_snd]
  let hFlatIso : MorphismProperty.RespectsIso (@Flat.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso (P := @Flat.{u})
  constructor
  · exact (MorphismProperty.cancel_right_of_respectsIso
      (@Flat.{u}) (hP := hFlatIso) (f ⊗ₘ g).left hHY.isoPullback.hom).mp (by
        simpa only [he] using
          (@MorphismProperty.RespectsIso.precomp (Scheme.{u}) _ (@Flat.{u}) hFlatIso)
            hGX.isoPullback.hom m hmFlat)
  · exact (MorphismProperty.cancel_right_of_respectsIso
      (@Surjective.{u}) (f ⊗ₘ g).left hHY.isoPullback.hom).mp (by
        simpa only [he] using
          MorphismProperty.RespectsIso.precomp
            (@Surjective.{u}) hGX.isoPullback.hom m hmSurjective)

private lemma tensorHom_epi (f : G ⟶ H) (g : X ⟶ Y)
    [Flat f.left] [Flat g.left] [Surjective f.left] [Surjective g.left] :
    Epi (f ⊗ₘ g) := by
  obtain ⟨hflat, hsurjective⟩ := tensorHom_flat_surjective f g
  exact @Over.epi_of_epi_left _ _ _ _ _ (f ⊗ₘ g)
    (@Flat.epi_of_flat_of_surjective _ _ (f ⊗ₘ g).left hflat hsurjective)

end TensorHom

/-- An fpqc monoid homomorphism from a group object admits a unique monoid factorization
of any monoid homomorphism trivial on its given categorical kernel.

This is the scheme-theoretic specialization of the categorical, arbitrary-monoid-target
generalization of Milne, *Algebraic Groups* (2017), (5.13). The supplied Cartesian structure
and the monoid structures on `G`, `H`, and `X` are preserved. -/
theorem existsUnique_monoidHom_of_trivial_kernel_of_fpqc
    {S : Scheme.{u}} [c : CartesianMonoidalCategory (Over S)]
    {N G H X : Over S} [GrpObj G] [MonObj H] [MonObj X]
    (q : G ⟶ H) [IsMonHom q]
    [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
    (φ : G ⟶ X) [IsMonHom φ]
    (i : N ⟶ G) (hN : IsPullback i (toUnit N) q η[H])
    (hφ : i ≫ φ = toUnit N ≫ η[X]) :
    ∃! ψ : Mon.mk H ⟶ Mon.mk X, q ≫ ψ.hom = φ := by
  have hq : EffectiveEpi q := Over.effectiveEpi_of_effectiveEpi_left q
  have hqq : Epi (q ⊗ₘ q) := tensorHom_epi q q
  exact @CategoryTheory.GrpObj.existsUnique_monoidHom_of_trivial_kernel
    (Over S) _ c N G H X _ _ _ q _ hq hqq φ _ i hN hφ

end AlgebraicGeometry
