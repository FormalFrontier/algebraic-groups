/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupObject.KernelTorsor
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
# Flat kernel-pair projections over fields

For a homomorphism from a group object to a monoid object over a field, the first
projection of the scheme self-pullback is flat and surjective. This is a statement
about the kernel pair, not a flatness or surjectivity assertion about the homomorphism.
The Cartesian structure and the group and monoid data are the supplied ones.

The proof uses the existing Formal Frontier kernel/torsor formalization and Mathlib's
pullback comparisons and scheme morphism properties. The kernel-multiplication square
is flipped so that its fixed second product coordinate corresponds to the first
kernel-pair projection. No group structure on the kernel is needed.

## References

J. S. Milne, *Algebraic Groups* (2017), (5.8), motivates this kernel-pair result.
Allowing a monoid-object target is a generalization of that motivation.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj

namespace AlgebraicGeometry

/-- The first projection of the scheme self-pullback of a homomorphism from a group
object to a monoid object over a field is flat and surjective.

Only the source is required to be a group object. The conclusion does not assert
flatness or surjectivity of `f.left`. This kernel-pair result is motivated by
J. S. Milne, *Algebraic Groups* (2017), (5.8), with the target generalized to a monoid
object. -/
theorem flat_surjective_pullback_fst_of_monoid_hom_over_field
    (k : Type u) [Field k]
    [c : CartesianMonoidalCategory (Over (Spec (CommRingCat.of k)))]
    (G H : Over (Spec (CommRingCat.of k)))
    [GrpObj G] [MonObj H]
    (f : G ⟶ H) [IsMonHom f] :
    Flat (pullback.fst f.left f.left) ∧
      Surjective (pullback.fst f.left f.left) := by
  classical
  constructor
  · let : Subsingleton (Spec (CommRingCat.of k)) := by
      rw [Spec_carrier]
      infer_instance
    let K := pullback f η[H]
    let i : K ⟶ G := pullback.fst f η[H]
    have hK : IsPullback i (toUnit K) f η[H] := by
      have hunit : pullback.snd f η[H] = toUnit K := toUnit_unique _ _
      simpa only [hunit] using IsPullback.of_hasPullback f η[H]
    have hCore : IsPullback (snd K G) ((i ⊗ₘ 𝟙 G) ≫ μ[G]) f f :=
      (GrpObj.isPullback_kernel_mul i f hK).flip
    have hprod : IsPullback (fst K G).left (snd K G).left K.hom G.hom :=
      Over.isPullback_of_binaryFan_isLimit
        (BinaryFan.mk (fst K G) (snd K G))
        (tensorProductIsBinaryProduct K G)
    let : Flat K.hom := inferInstance
    let : IsOpenImmersion hprod.isoPullback.hom :=
      ((isIso_iff_isOpenImmersion_and_epi_base _).mp (by infer_instance)).1
    have : Flat (snd K G).left := by
      have hcomp : Flat (hprod.isoPullback.hom ≫ pullback.snd K.hom G.hom) :=
        inferInstance
      simpa only [hprod.isoPullback_hom_snd] using hcomp
    let e : (K ⊗ G).left ≅ pullback f.left f.left :=
      ((Over.forget (Spec (CommRingCat.of k))).mapIso hCore.isoPullback) ≪≫
        PreservesPullback.iso (Over.forget (Spec (CommRingCat.of k))) f f
    have hpres :
        (PreservesPullback.iso (Over.forget (Spec (CommRingCat.of k))) f f).hom ≫
            pullback.fst f.left f.left =
          (Over.forget (Spec (CommRingCat.of k))).map (pullback.fst f f) := by
      simpa using PreservesPullback.iso_hom_fst
        (Over.forget (Spec (CommRingCat.of k))) f f
    have he : e.hom ≫ pullback.fst f.left f.left = (snd K G).left := by
      change ((Over.forget (Spec (CommRingCat.of k))).map hCore.isoPullback.hom ≫
        (PreservesPullback.iso (Over.forget (Spec (CommRingCat.of k))) f f).hom) ≫
          pullback.fst f.left f.left = (snd K G).left
      rw [Category.assoc, hpres, ← Functor.map_comp]
      simp
    have heInv : e.inv ≫ (snd K G).left = pullback.fst f.left f.left := by
      rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]
    let : IsOpenImmersion e.inv :=
      ((isIso_iff_isOpenImmersion_and_epi_base _).mp (by infer_instance)).1
    have hcomp : Flat (e.inv ≫ (snd K G).left) := inferInstance
    simpa only [heInv] using hcomp
  · let d : G.left ⟶ pullback f.left f.left :=
      pullback.lift (𝟙 G.left) (𝟙 G.left) (by rfl)
    have hd : d ≫ pullback.fst f.left f.left = 𝟙 G.left :=
      pullback.lift_fst _ _ _
    let : Surjective (d ≫ pullback.fst f.left f.left) := by
      rw [hd]
      infer_instance
    exact Surjective.of_comp d (pullback.fst f.left f.left)

end AlgebraicGeometry
