/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.Surjective
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Surjectivity of schematically dominant affine group homomorphisms

A schematically dominant homomorphism of affine group schemes locally of finite type over a
field is surjective on all underlying scheme points. The proof transports the given group
objects and homomorphism to an algebraic closure, applies
`Surjective.of_dominant_affine_group_hom`, and descends surjectivity along the field cover.
The transport and schematic-dominance base change use Mathlib's slice-category and scheme APIs.

## Limitations

This is a schematic-dominance variant of Milne's Corollary 1.69, not the arbitrary-field
statement with only topological dominance. In particular, the proof does not assert that bare
topological dominance is preserved by this scalar extension. Neither the original target nor
its scalar extension is required to be reduced. For a reduced original target, schematic
dominance can instead be obtained from `IsSchemeTheoreticallyDominant.of_isDominant` at use.
Milne's closed-point convention is not used for the conclusion here, which concerns all points.

## References

* J. S. Milne, *Algebraic Groups*, Corollary 1.69.
* `AlgebraicGroups.GroupScheme.Surjective`, the algebraically closed field case.
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj CategoryTheory.Obj

/-- A schematic-dominance variant of Milne, *Algebraic Groups*, Corollary 1.69, over any field:
a schematically dominant homomorphism of affine group schemes locally of finite type is
surjective on all underlying scheme points. The group structures and homomorphism are the given
ones. This uses `Surjective.of_dominant_affine_group_hom` after extension to an algebraic closure;
it does not establish the arbitrary-field assertion from topological dominance alone. -/
theorem Surjective.of_schemeTheoreticallyDominant_affine_group_hom
    {K : Type u} [Field K] {G H : Scheme.{u}}
    (fG : G ⟶ Spec (.of K)) (fH : H ⟶ Spec (.of K))
    [IsAffine G] [IsAffine H]
    [LocallyOfFiniteType fG] [LocallyOfFiniteType fH]
    [GrpObj (Over.mk fG)] [GrpObj (Over.mk fH)]
    (φ : Over.mk fG ⟶ Over.mk fH) [IsMonHom φ]
    [IsSchemeTheoreticallyDominant φ.left] : Surjective φ.left := by
  let L := AlgebraicClosure K
  let β : Spec (.of L) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K L))
  have hβ : Flat β ∧ Surjective β :=
    (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap K L))).2
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  have : Flat β := hβ.1
  have : Surjective β := hβ.2
  let F : Over (Spec (.of K)) ⥤ Over (Spec (.of L)) := Over.pullback β
  let Gbase := F.obj (Over.mk fG)
  let Hbase := F.obj (Over.mk fH)
  let φL : Gbase ⟶ Hbase := F.map φ
  let qG : Gbase.left ⟶ G := pullback.fst fG β
  let qH : Hbase.left ⟶ H := pullback.fst fH β
  have : IsAffineHom φ.left := isAffineHom_of_isAffine (X := G) (Y := H) φ.left
  have : QuasiCompact φ.left := inferInstance
  have hφL : IsMonHom φL := inferInstance
  have : IsAffine Gbase.left := (inferInstance : IsAffine (pullback fG β))
  have : IsAffine Hbase.left := (inferInstance : IsAffine (pullback fH β))
  -- Only the original group structure maps need to be locally of finite type, not β.
  have : LocallyOfFiniteType Gbase.hom :=
    (inferInstance : LocallyOfFiniteType (pullback.snd fG β))
  have : LocallyOfFiniteType Hbase.hom :=
    (inferInstance : LocallyOfFiniteType (pullback.snd fH β))
  have : Flat qH := (inferInstance : Flat (pullback.fst fH β))
  have : Surjective qH := (inferInstance : Surjective (pullback.fst fH β))
  have : IsAffineHom φL.left :=
    isAffineHom_of_isAffine (X := Gbase.left) (Y := Hbase.left) φL.left
  have : QuasiCompact φL.left := inferInstance
  have hcomp : φ.left ≫ fH = fG := Over.w φ
  -- Identify the underlying map of the transported homomorphism, not a replacement map.
  have hmap : φL.left =
      pullback.map fG β fH β φ.left (𝟙 _) (𝟙 _)
        (by simpa only [Category.comp_id] using hcomp.symm)
        (by simp only [Category.comp_id, Category.id_comp]) := by
    rfl
  have hcomm : φL.left ≫ qH = qG ≫ φ.left := by
    rw [hmap]
    exact pullback.lift_fst _ _ _
  have houter : IsPullback (φL.left ≫ Hbase.hom) qG β (φ.left ≫ fH) := by
    have hcompL : φL.left ≫ Hbase.hom = Gbase.hom := Over.w φL
    rw [hcomp, hcompL]
    exact (IsPullback.of_hasPullback fG β).flip
  have hsquare : IsPullback qG φL.left φ.left qH :=
    (IsPullback.of_right houter hcomm (IsPullback.of_hasPullback fH β).flip).flip
  have : IsSchemeTheoreticallyDominant φL.left :=
    IsSchemeTheoreticallyDominant.of_isPullback hsquare
  have : IsDominant φL.left := inferInstance
  let : GrpObj (Over.mk Gbase.hom) := (show GrpObj Gbase from inferInstance)
  let : GrpObj (Over.mk Hbase.hom) := (show GrpObj Hbase from inferInstance)
  have : IsMonHom (show Over.mk Gbase.hom ⟶ Over.mk Hbase.hom from φL) := hφL
  have : Surjective φL.left :=
    Surjective.of_dominant_affine_group_hom Gbase.hom Hbase.hom φL
  have : Surjective (φL.left ≫ qH) := inferInstance
  have : Surjective (qG ≫ φ.left) := by
    rw [← hcomm]
    infer_instance
  exact Surjective.of_comp qG φ.left

end AlgebraicGeometry
