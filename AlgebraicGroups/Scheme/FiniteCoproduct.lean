/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Category.Extensive
public import Mathlib.AlgebraicGeometry.Morphisms.Basic

/-!
# Morphism properties of finite coproducts of schemes

This file shows that a property of scheme morphisms which is Zariski-local on
the target is preserved by maps between finite coproducts.
-/

public section

open CategoryTheory Limits

universe u v

namespace AlgebraicGeometry

/-- A target-local property of scheme morphisms is preserved by a map between
finite coproducts when it holds on every summand. -/
lemma IsZariskiLocalAtTarget.sigmaMap {I : Type v} [Finite I]
    {P : MorphismProperty Scheme.{u}} [IsZariskiLocalAtTarget P]
    {X Y : I → Scheme.{u}} (F : ∀ i, X i ⟶ Y i)
    (hF : ∀ i, P (F i)) : P (Limits.Sigma.map F) := by
  apply IsZariskiLocalAtTarget.of_openCover (sigmaOpenCover Y)
  change ∀ i : I, P ((sigmaOpenCover Y).pullbackHom (Limits.Sigma.map F) i)
  intro i
  change P (pullback.snd (Limits.Sigma.map F) (Sigma.ι Y i))
  rw [← P.cancel_left_of_respectsIso
    (FinitaryExtensive.isPullback_sigmaMap_ι X Y F i).isoPullback.hom]
  simpa using hF i

end AlgebraicGeometry
