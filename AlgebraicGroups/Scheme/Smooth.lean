/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Geometric reducedness of smooth morphisms

This file lifts reducedness of smooth algebras over domains to schemes and proves that every
smooth morphism of schemes is geometrically reduced.

## Main results

- `AlgebraicGeometry.Smooth.isReduced_of_isDomain`
- `AlgebraicGeometry.Smooth.geometricallyReduced`

## References

- The Stacks Project, [Lemma 10.163.7 (Tag 033B)](https://stacks.math.columbia.edu/tag/033B),
  for reducedness of smooth algebras over reduced bases; base change to a field
  yields geometric reducedness of smooth scheme morphisms.
- Mathlib's `Smooth.smooth_appLE`, `IsReduced.of_openCover`, and
  `smooth_isStableUnderBaseChange` supply the affine-local and base-change steps.
- J. S. Milne, *Algebraic Groups*, Proposition 1.26, for the smooth-to-geometrically-reduced
  implication in the special case of algebraic groups over fields.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- A scheme smooth over the spectrum of an integral domain is reduced. -/
theorem Smooth.isReduced_of_isDomain
    {R : CommRingCat.{u}} [IsDomain R] {X : Scheme.{u}}
    (f : X ⟶ Spec R) [Smooth f] : IsReduced X := by
  refine @IsReduced.of_openCover X X.affineCover (fun i ↦ ?_)
  let g := X.affineCover.f i ≫ f
  have hgSmooth : Smooth g := inferInstance
  let e : (⊤ : (X.affineCover.X i).Opens) ≤ g ⁻¹ᵁ (⊤ : (Spec R).Opens) := by simp
  have hg : (g.appLE ⊤ ⊤ e).hom.Smooth :=
    @Smooth.smooth_appLE _ _ g hgSmooth _ (isAffineOpen_top _) _ (isAffineOpen_top _) e
  let φ : R →+* Γ(X.affineCover.X i, ⊤) :=
    ((Scheme.ΓSpecIso R).inv ≫ g.appLE ⊤ ⊤ e).hom
  have hφ : φ.Smooth := by
    exact (RingHom.Smooth.of_bijective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv)).comp hg
  have hSmooth : @Algebra.Smooth R _ Γ(X.affineCover.X i, ⊤) _ φ.toAlgebra :=
    hφ.toAlgebra
  have hReduced : _root_.IsReduced Γ(X.affineCover.X i, ⊤) :=
    @Algebra.Smooth.isReduced_of_isDomain R Γ(X.affineCover.X i, ⊤)
      _ _ _ φ.toAlgebra hSmooth
  exact @isReduced_of_isAffine_isReduced _ inferInstance hReduced

/-- Every smooth morphism of schemes is geometrically reduced. In particular, this supplies
the smooth-to-geometrically-reduced implication for the algebraic groups in Milne,
*Algebraic Groups*, Proposition 1.26; the theorem applies to arbitrary base schemes. -/
instance (priority := low) Smooth.geometricallyReduced {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Smooth f] : GeometricallyReduced f := by
  constructor
  intro K _ y Z fst snd h
  have hsnd : Smooth snd :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback h inferInstance
  exact @Smooth.isReduced_of_isDomain _ _ _ snd hsnd

end AlgebraicGeometry
