/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ConstantGroup.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.RingTheory.TensorProduct.Pi

/-!
# The coproduct underlying a finite constant group scheme

We use Tau Ceti's canonical coordinate Hopf algebra and constant group scheme.
Its function-algebra equivalence identifies the underlying scheme with the
finite coproduct of copies of the base. Reducedness also follows from this
function-algebra description.

## References

* James S. Milne, *Algebraic Groups* (2017), item 2.3, p. 40.
* Mathlib's `sigmaSpec`, the spectrum of a finite product.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct
open TauCeti.ConstantGroup
open AlgebraicGeometry
open Functor Monoidal


namespace TauCeti.ConstantGroup

universe u

/-- Evaluation points with the terminal source used for rational group-scheme points. -/
noncomputable def unitPointHom (K Γ : Type u)
    [CommRing K] [Finite Γ] [Group Γ] :
    Γ →* (𝟙_ (Over (Spec (.of K))) ⟶ (groupScheme K Γ).X) := by
  letI := braidedAlgSpec (R := CommRingCat.of K)
  let u : 𝟙_ (Over (Spec (.of K))) ⟶ (Spec (.of K)).asOver (Spec (.of K)) :=
    Functor.LaxMonoidal.ε (algSpec (CommRingCat.of K))
  exact ((yonedaMonObj (groupScheme K Γ).X).map u.op).hom.comp
    ((groupSchemePointMulEquiv K Γ K).toMonoidHom.comp (toPoints K Γ))

/-- Evaluation at the group identity is the unit rational point.

Keeping this formula at the generic group avoids reducing the finite-dual group instance
inside component-group calculations. -/
@[simp] theorem unitPointHom_one (K Γ : Type u)
    [CommRing K] [Finite Γ] [Group Γ] :
    unitPointHom K Γ 1 = η[(groupScheme K Γ).X] := by
  simpa only [CategoryTheory.Hom.one_def, toUnit_unit, Category.id_comp] using
    map_one (unitPointHom K Γ)

/-- The rational evaluation point is spectrum applied to the canonical evaluation map. -/
@[simp] theorem unitPointHom_apply_left (K Γ : Type u)
    [CommRing K] [Finite Γ] [Group Γ] (g : Γ) :
    (unitPointHom K Γ g).left =
      Spec.map (CommRingCat.ofHom (eval K Γ g).toRingHom) := by
  let := braidedAlgSpec (R := CommRingCat.of K)
  simp only [unitPointHom, yonedaMonObj_map]
  change (𝟙 (Spec (.of K))) ≫
    (groupSchemePointMulEquiv K Γ K (toPoints K Γ g)).left = _
  apply (Category.id_comp _).trans
  have h := groupSchemePointMulEquiv_apply_left K Γ K (toPoints K Γ g)
  have heval : (eval K Γ g).toRingHom =
      (eval K Γ g : coordinateRing K Γ →+* K) := by
    ext x
    rfl
  have hc : Spec.map (CommRingCat.ofHom (toPoints K Γ g).ofConv) ≫
      eqToHom (groupScheme_X_left K Γ).symm =
        Spec.map (CommRingCat.ofHom (eval K Γ g).toRingHom) := by
    rw [toPoints_apply, ← heval]
    exact Category.comp_id _
  exact h.trans hc

end TauCeti.ConstantGroup

namespace AlgebraicGeometry

universe u

/-- The scheme underlying the canonical finite constant group is a coproduct of base schemes. -/
noncomputable def finiteConstantSigmaIso (K Γ : Type u)
    [CommRing K] [Fintype Γ] [Group Γ] :
    (∐ fun _ : Γ ↦ Spec (.of K)) ≅ (groupScheme K Γ).X.left :=
  CategoryTheory.asIso (sigmaSpec (fun _ : Γ ↦ .of K)) ≪≫
    Scheme.Spec.mapIso (functionAlgEquiv K Γ).toRingEquiv.toCommRingCatIso.op

/-- The coproduct summand labelled by `g` is the canonical evaluation point. -/
@[reassoc (attr := simp)]
lemma finiteConstantSigmaIso_hom_ι (K Γ : Type u)
    [CommRing K] [Fintype Γ] [Group Γ] (g : Γ) :
    Sigma.ι (fun _ : Γ ↦ Spec (.of K)) g ≫ (finiteConstantSigmaIso K Γ).hom =
      (unitPointHom K Γ g).left := by
  rw [unitPointHom_apply_left]
  have h : Sigma.ι (fun _ : Γ ↦ Spec (.of K)) g ≫
      sigmaSpec (fun _ : Γ ↦ .of K) ≫
        Spec.map (CommRingCat.ofHom
          ((functionAlgEquiv K Γ).toRingEquiv : coordinateRing K Γ →+* (Γ → K))) =
      Spec.map (CommRingCat.ofHom (eval K Γ g).toRingHom) := by
    rw [← Category.assoc, ι_sigmaSpec, ← Spec.map_comp]
    congr 1
    ext f
    change functionAlgEquiv K Γ f g = eval K Γ g f
    rw [eval_apply]
  change Sigma.ι (fun _ : Γ ↦ Spec (.of K)) g ≫
    ((CategoryTheory.asIso (sigmaSpec (fun _ : Γ ↦ .of K))).hom ≫
      (Scheme.Spec.mapIso
        (functionAlgEquiv K Γ).toRingEquiv.toCommRingCatIso.op).hom) = _
  simpa only [CategoryTheory.asIso_hom, Functor.mapIso_hom, Iso.op_hom,
    Scheme.Spec_map, Quiver.Hom.unop_op, RingEquiv.toCommRingCatIso_hom] using h

instance finiteConstantGroupScheme_isReduced (K Γ : Type u)
    [CommRing K] [Finite Γ] [Group Γ] [_root_.IsReduced K] :
    AlgebraicGeometry.IsReduced (groupScheme K Γ).X.left := by
  rw [groupScheme_X_left, affine_isReduced_iff]
  exact isReduced_of_injective (functionAlgEquiv K Γ) (functionAlgEquiv K Γ).injective

end AlgebraicGeometry
