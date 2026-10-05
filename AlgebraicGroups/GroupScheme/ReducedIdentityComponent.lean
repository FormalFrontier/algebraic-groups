/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.IdentityComponent
public import AlgebraicGroups.GroupScheme.Reduction

/-!
# Reduced identity components of group schemes

This file records the canonical comparison from the identity component of a
group-scheme reduction to the identity component of the original group scheme.

The main construction first proves a general fact: a monoid-object morphism
from a connected monoid scheme factors through the identity component of its
target.  Applying this to the composite
`(G_red)⁰ ⟶ G_red ⟶ G` gives the comparison `(G_red)⁰ ⟶ G⁰` needed to formulate
the residual quotient `G⁰/(G_red)⁰`.

No quotient, normality, finiteness, or representability statement is asserted
here.

## References

- J. S. Milne, *Algebraic Groups*, Remark 2.39(b) for factorization of a
  connected group through the identity component, and Proposition 1.38 for
  the reduced-group construction under its geometric reducedness condition.
  Proposition 8.37 motivates the reduced identity component as a different
  quotient subgroup; Example 2.35(a) shows why normality of its inclusion
  cannot be inferred.
- The local `GroupScheme.Reduction` supplies the group structure on the
  reduction under explicit base and product reducedness hypotheses;
  `GroupScheme.IdentityComponent` supplies the inherited open component.
  The mathlib community, *Mathlib*, supplies continuous-image arguments,
  open-immersion lifts and reduction homeomorphisms.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open TopologicalSpace

namespace AlgebraicGeometry

universe u

variable {S : Scheme.{u}}

private lemma Scheme.range_isMonHom_subset_identityComponent
    {H G : Over S} [MonObj H] [GrpObj G] (i : H ⟶ G) [IsMonHom i]
    [ConnectedSpace H.left] [LocallyConnectedSpace G.left]
    [Nonempty S] [Subsingleton S] :
    Set.range i.left ⊆ Set.range (Scheme.identityComponent G).ι := by
  let s₀ : S := Classical.choice (inferInstance : Nonempty S)
  let a : H.left := η[H].left s₀
  have hia : i.left a = η[G].left s₀ := by
    change (η[H] ≫ i).left s₀ = η[G].left s₀
    rw [IsMonHom.one_hom]
  rintro _ ⟨x, rfl⟩
  refine ⟨⟨i.left x, ?_⟩, rfl⟩
  change i.left x ∈ connectedComponent (η[G].left s₀)
  rw [← hia]
  exact i.left.continuous.mapsTo_connectedComponent a (by
    rw [PreconnectedSpace.connectedComponent_eq_univ]
    exact Set.mem_univ x)

/-- A monoid-object morphism from a connected monoid scheme factors through the
identity component of its target. This extends the connected-group
factorization in Milne, *Algebraic Groups*, Remark 2.39(b), to monoid
sources over a nonempty one-point base. -/
noncomputable def Scheme.identityComponentLift
    {H G : Over S} [MonObj H] [GrpObj G] (i : H ⟶ G) [IsMonHom i]
    [ConnectedSpace H.left] [LocallyConnectedSpace G.left]
    [Nonempty S] [Subsingleton S] : H ⟶ Scheme.identityComponentOver G :=
  Over.homMk (IsOpenImmersion.lift (Scheme.identityComponent G).ι i.left
    (Scheme.range_isMonHom_subset_identityComponent i)) (by
      rw [show (Scheme.identityComponentOver G).hom =
        (Scheme.identityComponent G).ι ≫ G.hom from rfl,
        ← Category.assoc, IsOpenImmersion.lift_fac]
      exact i.w)

/-- The identity-component lift followed by the canonical inclusion is the
original morphism. -/
@[reassoc]
lemma Scheme.identityComponentLift_comp_ι
    {H G : Over S} [MonObj H] [GrpObj G] (i : H ⟶ G) [IsMonHom i]
    [ConnectedSpace H.left] [LocallyConnectedSpace G.left]
    [Nonempty S] [Subsingleton S] :
    Scheme.identityComponentLift i ≫ Scheme.identityComponentι G = i := by
  ext
  exact IsOpenImmersion.lift_fac _ _ _

instance Scheme.identityComponentLift_mono
    {H G : Over S} [MonObj H] [GrpObj G] (i : H ⟶ G) [IsMonHom i] [Mono i]
    [ConnectedSpace H.left] [LocallyConnectedSpace G.left]
    [Nonempty S] [Subsingleton S] : Mono (Scheme.identityComponentLift i) :=
  mono_of_mono_fac (Scheme.identityComponentLift_comp_ι i)

instance Scheme.identityComponentLift_isClosedImmersion
    {H G : Over S} [MonObj H] [GrpObj G] (i : H ⟶ G) [IsMonHom i]
    [IsClosedImmersion i.left] [ConnectedSpace H.left]
    [LocallyConnectedSpace G.left] [Nonempty S] [Subsingleton S] :
    IsClosedImmersion (Scheme.identityComponentLift i).left := by
  let _ : IsClosedImmersion
      ((Scheme.identityComponentLift i ≫ Scheme.identityComponentι G).left) := by
    rw [Scheme.identityComponentLift_comp_ι]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion
    (Scheme.identityComponentLift i).left (Scheme.identityComponentι G).left

instance Scheme.identityComponentLift_isMonHom
    {H G : Over S} [MonObj H] [GrpObj G] (i : H ⟶ G) [IsMonHom i]
    [ConnectedSpace H.left] [LocallyConnectedSpace G.left]
    [Nonempty S] [Subsingleton S]
    [ConnectedSpace ((Scheme.identityComponentOver G ⊗
      Scheme.identityComponentOver G).left)] :
    IsMonHom (Scheme.identityComponentLift i) where
  one_hom := by
    apply (cancel_mono (Scheme.identityComponentι G)).1
    rw [Category.assoc, Scheme.identityComponentLift_comp_ι,
      IsMonHom.one_hom, IsMonHom.one_hom]
  mul_hom := by
    apply (cancel_mono (Scheme.identityComponentι G)).1
    calc
      (μ[H] ≫ Scheme.identityComponentLift i) ≫ Scheme.identityComponentι G =
          μ[H] ≫ i := by
        rw [Category.assoc, Scheme.identityComponentLift_comp_ι]
      _ = (i ⊗ₘ i) ≫ μ[G] := IsMonHom.mul_hom i
      _ = ((Scheme.identityComponentLift i ≫ Scheme.identityComponentι G) ⊗ₘ
          (Scheme.identityComponentLift i ≫ Scheme.identityComponentι G)) ≫ μ[G] := by
        rw [Scheme.identityComponentLift_comp_ι]
      _ = (Scheme.identityComponentLift i ⊗ₘ Scheme.identityComponentLift i) ≫
          (Scheme.identityComponentι G ⊗ₘ Scheme.identityComponentι G) ≫ μ[G] := by
        rw [tensorHom_comp_tensorHom_assoc]
      _ = (Scheme.identityComponentLift i ⊗ₘ Scheme.identityComponentLift i) ≫
          μ[Scheme.identityComponentOver G] ≫ Scheme.identityComponentι G := by
        rw [IsMonHom.mul_hom]

/-- The reduced identity component `(G_red)⁰`, regarded as an object over the
same base as `G`. -/
noncomputable abbrev Scheme.reducedIdentityComponentOver (G : Over S) [GrpObj G]
    [IsReduced S]
    [IsReduced ((Scheme.reductionOver G ⊗ Scheme.reductionOver G).left)]
    [LocallyConnectedSpace (Scheme.reductionOver G).left]
    [Nonempty S] [Subsingleton S] : Over S :=
  Scheme.identityComponentOver (Scheme.reductionOver G)

/-- The canonical inclusion `(G_red)⁰ ⟶ G`. -/
noncomputable abbrev Scheme.reducedIdentityComponentι (G : Over S) [GrpObj G]
    [IsReduced S]
    [IsReduced ((Scheme.reductionOver G ⊗ Scheme.reductionOver G).left)]
    [LocallyConnectedSpace (Scheme.reductionOver G).left]
    [Nonempty S] [Subsingleton S] :
    Scheme.reducedIdentityComponentOver G ⟶ G :=
  Scheme.identityComponentι (Scheme.reductionOver G) ≫ Scheme.reductionOverι G

/-- The canonical inclusion `(G_red)⁰ ⟶ G` has open underlying range. This is
a statement about the range rather than an open-immersion assertion: the
reduction map itself is generally only a closed immersion, but it is a
homeomorphism on underlying spaces. -/
lemma Scheme.reducedIdentityComponentι_isOpen_range
    (G : Over S) [GrpObj G] [IsReduced S]
    [IsReduced ((Scheme.reductionOver G ⊗ Scheme.reductionOver G).left)]
    [LocallyConnectedSpace (Scheme.reductionOver G).left]
    [Nonempty S] [Subsingleton S] :
    IsOpen (Set.range (Scheme.reducedIdentityComponentι G).left) := by
  change IsOpen (Set.range
    ((Scheme.identityComponentι (Scheme.reductionOver G) ≫
      Scheme.reductionOverι G).left))
  rw [show ⇑((Scheme.identityComponentι (Scheme.reductionOver G) ≫
      Scheme.reductionOverι G).left) =
    (Scheme.reductionι.app G.left) ∘
      (Scheme.identityComponentι (Scheme.reductionOver G)).left from rfl,
    Set.range_comp]
  exact (Scheme.reductionι_isHomeomorph G.left).isOpenMap _
    (IsOpenImmersion.isOpen_range
      (Scheme.identityComponentι (Scheme.reductionOver G)).left)

/-- The canonical comparison `(G_red)⁰ ⟶ G⁰`. This is the inclusion used
when distinguishing the reduced-component quotient of Milne,
*Algebraic Groups*, Proposition 8.37 from the discrete component quotient;
it asserts neither normality nor quotient representability. -/
noncomputable def Scheme.reducedIdentityComponentToIdentityComponent
    (G : Over S) [GrpObj G] [IsReduced S]
    [IsReduced ((Scheme.reductionOver G ⊗ Scheme.reductionOver G).left)]
    [LocallyConnectedSpace (Scheme.reductionOver G).left]
    [LocallyConnectedSpace G.left] [Nonempty S] [Subsingleton S]
    [ConnectedSpace ((Scheme.reducedIdentityComponentOver G ⊗
      Scheme.reducedIdentityComponentOver G).left)] :
    Scheme.reducedIdentityComponentOver G ⟶ Scheme.identityComponentOver G :=
  Scheme.identityComponentLift (Scheme.reducedIdentityComponentι G)

instance Scheme.reducedIdentityComponentToIdentityComponent_mono
    (G : Over S) [GrpObj G] [IsReduced S]
    [IsReduced ((Scheme.reductionOver G ⊗ Scheme.reductionOver G).left)]
    [LocallyConnectedSpace (Scheme.reductionOver G).left]
    [LocallyConnectedSpace G.left] [Nonempty S] [Subsingleton S]
    [ConnectedSpace ((Scheme.reducedIdentityComponentOver G ⊗
      Scheme.reducedIdentityComponentOver G).left)] :
    Mono (Scheme.reducedIdentityComponentToIdentityComponent G) := by
  change Mono (Scheme.identityComponentLift (Scheme.reducedIdentityComponentι G))
  infer_instance

instance Scheme.reducedIdentityComponentToIdentityComponent_isClosedImmersion
    (G : Over S) [GrpObj G] [IsReduced S]
    [IsReduced ((Scheme.reductionOver G ⊗ Scheme.reductionOver G).left)]
    [LocallyConnectedSpace (Scheme.reductionOver G).left]
    [LocallyConnectedSpace G.left] [Nonempty S] [Subsingleton S]
    [ConnectedSpace ((Scheme.reducedIdentityComponentOver G ⊗
      Scheme.reducedIdentityComponentOver G).left)] :
    IsClosedImmersion (Scheme.reducedIdentityComponentToIdentityComponent G).left := by
  change IsClosedImmersion
    (Scheme.identityComponentLift (Scheme.reducedIdentityComponentι G)).left
  let _ : IsClosedImmersion (Scheme.reducedIdentityComponentι G).left := by
    change IsClosedImmersion
      ((Scheme.identityComponentι (Scheme.reductionOver G)).left ≫
        (Scheme.reductionOverι G).left)
    infer_instance
  infer_instance

instance Scheme.reducedIdentityComponentToIdentityComponent_isMonHom
    (G : Over S) [GrpObj G] [IsReduced S]
    [IsReduced ((Scheme.reductionOver G ⊗ Scheme.reductionOver G).left)]
    [LocallyConnectedSpace (Scheme.reductionOver G).left]
    [LocallyConnectedSpace G.left] [Nonempty S] [Subsingleton S]
    [ConnectedSpace ((Scheme.reducedIdentityComponentOver G ⊗
      Scheme.reducedIdentityComponentOver G).left)]
    [ConnectedSpace ((Scheme.identityComponentOver G ⊗
      Scheme.identityComponentOver G).left)] :
    IsMonHom (Scheme.reducedIdentityComponentToIdentityComponent G) := by
  change IsMonHom (Scheme.identityComponentLift (Scheme.reducedIdentityComponentι G))
  infer_instance

/-- The comparison `(G_red)⁰ ⟶ G⁰`, followed by `G⁰ ⟶ G`, is the canonical
inclusion `(G_red)⁰ ⟶ G`. -/
@[reassoc]
lemma Scheme.reducedIdentityComponentToIdentityComponent_comp_ι
    (G : Over S) [GrpObj G] [IsReduced S]
    [IsReduced ((Scheme.reductionOver G ⊗ Scheme.reductionOver G).left)]
    [LocallyConnectedSpace (Scheme.reductionOver G).left]
    [LocallyConnectedSpace G.left] [Nonempty S] [Subsingleton S]
    [ConnectedSpace ((Scheme.reducedIdentityComponentOver G ⊗
      Scheme.reducedIdentityComponentOver G).left)] :
    Scheme.reducedIdentityComponentToIdentityComponent G ≫
      Scheme.identityComponentι G = Scheme.reducedIdentityComponentι G :=
  Scheme.identityComponentLift_comp_ι _

end AlgebraicGeometry
