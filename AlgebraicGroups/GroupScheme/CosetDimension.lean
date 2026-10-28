/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.ClosedPoints
public import AlgebraicGroups.GroupScheme.CosetQuotient
public import AlgebraicGroups.GroupScheme.ReducedIdentityComponent
public import AlgebraicGroups.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Dimension of coset quotient targets

This file gives a dimension-zero criterion for a represented coset quotient,
in the more general setting of a multiplication relation. If `i : H ⟶ G` has
open underlying range and an fppf morphism `G ⟶ Q` has the relation
`(g, h) ↦ (g, g * i(h))` as its self-pullback, then, when `G` and `Q` are
locally of finite type over an algebraically closed field, `Q` has topological
Krull dimension at most zero.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 5.23 (the dimension
  formula for an algebraic coset quotient), Theorem 5.28 / Theorem B.37
  (existence of such quotients over a field), and Proposition 8.37 (the
  reduced-identity-component quotient used in the anti-affine argument).
  The dimension-zero conclusion here is conditional on a supplied quotient;
  its proof translates open ranges and uses Jacobson closed points and fppf
  openness, rather than formalizing the dimension-subtraction proof of 5.23.
* `AlgebraicGroups.GroupScheme.ClosedPoints` supplies the rational/closed-point
  equivalence, `AlgebraicGroups.GroupScheme.ReducedIdentityComponent` the
  open underlying range of `(G_red)⁰ ⟶ G`, and
  `AlgebraicGroups.Topology.KrullDimension` the Jacobson discreteness lemma;
  `AlgebraicGroups.GroupScheme.CosetQuotient` supplies the separately defined
  fppf coset sheaf and its recognition criterion, not a quotient construction.
* Mathlib, `Mathlib.Topology.JacobsonSpace` (closed points in locally closed
  subsets), `Mathlib.Topology.KrullDimension` (dimension of a discrete space),
  and `Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen` (openness of flat
  locally finitely presented morphisms).
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open TopologicalSpace Topology

namespace AlgebraicGeometry

universe u

variable {K : Type u} [Field K] [IsAlgClosed K]
variable {H G Q : Over (Spec (.of K))} [GrpObj H] [GrpObj G]

omit [IsAlgClosed K] [GrpObj H] in
private lemma cosetTranslate_comp
    (i : H ⟶ G) (q : G ⟶ Q)
    (h : IsPullback (fst G H) ((𝟙 G ⊗ₘ i) ≫ μ[G]) q q)
    (a : 𝟙_ (Over (Spec (.of K))) ⟶ G) :
    (i ≫ (TauCeti.leftTranslation a).hom) ≫ q = (toUnit H ≫ a) ≫ q := by
  rw [TauCeti.comp_leftTranslation_hom, CategoryTheory.Hom.mul_def]
  have hmap :
      lift (toUnit H ≫ a) i =
        lift (toUnit H ≫ a) (𝟙 H) ≫ (𝟙 G ⊗ₘ i) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  calc
    (lift (toUnit H ≫ a) i ≫ μ[G]) ≫ q =
        (lift (toUnit H ≫ a) (𝟙 H) ≫ ((𝟙 G ⊗ₘ i) ≫ μ[G])) ≫ q := by
          rw [hmap]
          simp only [Category.assoc]
    _ = lift (toUnit H ≫ a) (𝟙 H) ≫ (fst G H ≫ q) := by
      simp only [Category.assoc]
      rw [← Category.assoc (𝟙 G ⊗ₘ i) μ[G] q, ← h.w]
    _ = (toUnit H ≫ a) ≫ q := by rw [← Category.assoc, lift_fst]

omit [GrpObj H] in
/-- Let `G` be a group scheme over an algebraically closed field and
`i : H ⟶ G` a morphism of schemes over the field with open range. If `G` and
`Q` are locally of finite type and a supplied fppf morphism `q : G ⟶ Q` has
the multiplication relation with maps `fst G H` and `(𝟙 G ⊗ₘ i) ≫ μ[G]` as
its self-pullback, then `Q` has topological Krull dimension at most zero.
No group structure on `H` or homomorphism condition on `i` is required.

Milne's Proposition 5.23 yields the dimension-zero consequence for algebraic
coset quotients by a dimension formula. This proof instead lifts each closed
point to a rational point of `G`, translates the open range of `H`, uses the
openness of the fppf map to make the singleton open, then applies the local
Jacobson discreteness and Mathlib topological-Krull-dimension lemmas. It does
not construct `Q`, assert an open immersion, or prove finiteness. -/
theorem topologicalKrullDim_le_zero_of_isPullback_of_isOpen_range
    (i : H ⟶ G) (q : G ⟶ Q)
    (h : IsPullback (fst G H) ((𝟙 G ⊗ₘ i) ≫ μ[G]) q q)
    [LocallyOfFiniteType G.hom] [LocallyOfFiniteType Q.hom]
    [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left]
    (hi : IsOpen (Set.range i.left)) :
    topologicalKrullDim Q.left ≤ 0 := by
  let _ : Subsingleton (𝟙_ (Over (Spec (.of K)))).left := by
    simpa only [Over.tensorUnit_left] using
      (inferInstance : Subsingleton (Spec (.of K)))
  let _ : JacobsonSpace G.left := LocallyOfFiniteType.jacobsonSpace G.hom
  let _ : JacobsonSpace Q.left := LocallyOfFiniteType.jacobsonSpace Q.hom
  let _ : DiscreteTopology Q.left :=
    JacobsonSpace.discreteTopology_of_isOpen_singleton_closedPoint fun y hy ↦ by
      obtain ⟨x, hx⟩ := q.left.surjective y
      obtain ⟨g, hg, hgclosed⟩ := nonempty_inter_closedPoints
        (X := G.left) (⟨x, hx⟩ : (q.left ⁻¹' ({y} : Set Q.left)).Nonempty)
        (hy.preimage q.left.continuous).isLocallyClosed
      let a : 𝟙_ (Over (Spec (.of K))) ⟶ G :=
        (groupSchemePointEquivClosedPoint G.hom).symm ⟨g, hgclosed⟩
      let t : H ⟶ G := i ≫ (TauCeti.leftTranslation a).hom
      have hag : a.left (IsLocalRing.closedPoint K) = g := by
        exact groupSchemePointEquivClosedPoint_symm_apply_value G.hom ⟨g, hgclosed⟩
      have haq : q.left (a.left (IsLocalRing.closedPoint K)) = y := by
        rw [hag]
        simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hg
      have htq : t ≫ q = (toUnit H ≫ a) ≫ q := by
        exact cosetTranslate_comp i q h a
      have htq_point (z : H.left) : q.left (t.left z) = y := by
        have hz := congrArg (fun f : H ⟶ Q ↦ f.left z) htq
        change q.left (t.left z) =
          q.left (a.left ((toUnit H).left z)) at hz
        rw [hz]
        rw [show (toUnit H).left z = IsLocalRing.closedPoint K from
          Subsingleton.elim _ _]
        exact haq
      have htopen : IsOpen (Set.range t.left) := by
        change IsOpen (Set.range ((i ≫ (TauCeti.leftTranslation a).hom).left))
        rw [show ⇑((i ≫ (TauCeti.leftTranslation a).hom).left) =
          (TauCeti.leftTranslation a).hom.left ∘ i.left from rfl, Set.range_comp]
        exact (((Over.forget (Spec (.of K))).mapIso
          (TauCeti.leftTranslation a)).schemeIsoToHomeo.isOpen_image).mpr hi
      have himage : q.left '' Set.range t.left = {y} := by
        apply Set.Subset.antisymm
        · rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
          exact htq_point z
        · rw [Set.singleton_subset_iff]
          let b : 𝟙_ (Over (Spec (.of K))) ⟶ H :=
            h.lift η[G] η[G] rfl ≫ snd G H
          exact ⟨t.left (b.left (IsLocalRing.closedPoint K)),
            ⟨_, rfl⟩, htq_point _⟩
      rw [← himage]
      exact q.left.isOpenMap _ htopen
  exact topologicalKrullDim_zero_of_discreteTopology Q.left

/-- The group-homomorphism specialization of
`topologicalKrullDim_le_zero_of_isPullback_of_isOpen_range`. -/
@[deprecated topologicalKrullDim_le_zero_of_isPullback_of_isOpen_range
  (since := "2026-10-26")]
theorem topologicalKrullDim_quotient_le_zero_of_isOpen_range
    (i : H ⟶ G) [IsMonHom i] (q : G ⟶ Q)
    (h : IsPullback (fst G H) ((𝟙 G ⊗ₘ i) ≫ μ[G]) q q)
    [LocallyOfFiniteType G.hom] [LocallyOfFiniteType Q.hom]
    [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left]
    (hi : IsOpen (Set.range i.left)) :
    topologicalKrullDim Q.left ≤ 0 :=
  topologicalKrullDim_le_zero_of_isPullback_of_isOpen_range i q h hi

/-- A supplied fppf morphism whose self-pullback is the multiplication
relation parameterized by the underlying reduced identity component `(G_red)⁰`
has topological Krull dimension at most zero when `G` and `Q` are locally of
finite type, the reduction tensor square is reduced and the reduction is
locally connected. This uses the local theorem that `(G_red)⁰ ⟶ G` has open
**underlying range**, not that it is an open immersion.

Milne's Proposition 8.37 uses the existence and finiteness of the quotient by
`(G_red)⁰` in an anti-affine argument. This specialization assumes a target
and the exact multiplication-relation pullback square; it neither proves that
quotient exists nor asserts normality, finiteness, reducedness or a group
structure on `Q`. -/
theorem reducedIdentityComponent_topologicalKrullDim_le_zero_of_isPullback
    (G Q : Over (Spec (.of K))) [GrpObj G]
    [IsReduced ((Scheme.reductionOver G ⊗ Scheme.reductionOver G).left)]
    [LocallyConnectedSpace (Scheme.reductionOver G).left]
    (q : G ⟶ Q)
    (h : IsPullback
      (fst G (Scheme.reducedIdentityComponentOver G))
      ((𝟙 G ⊗ₘ Scheme.reducedIdentityComponentι G) ≫ μ[G]) q q)
    [LocallyOfFiniteType G.hom] [LocallyOfFiniteType Q.hom]
    [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left] :
    topologicalKrullDim Q.left ≤ 0 :=
  topologicalKrullDim_le_zero_of_isPullback_of_isOpen_range
    (Scheme.reducedIdentityComponentι G) q h
    (Scheme.reducedIdentityComponentι_isOpen_range G)

/-- The group-coset specialization of
`reducedIdentityComponent_topologicalKrullDim_le_zero_of_isPullback`, with
connected reduced-component tensor square. -/
@[deprecated reducedIdentityComponent_topologicalKrullDim_le_zero_of_isPullback
  (since := "2026-10-26")]
theorem reducedIdentityComponent_quotient_topologicalKrullDim_le_zero
    (G Q : Over (Spec (.of K))) [GrpObj G]
    [IsReduced ((Scheme.reductionOver G ⊗ Scheme.reductionOver G).left)]
    [LocallyConnectedSpace (Scheme.reductionOver G).left]
    [ConnectedSpace ((Scheme.reducedIdentityComponentOver G ⊗
      Scheme.reducedIdentityComponentOver G).left)]
    (q : G ⟶ Q)
    (h : IsPullback
      (fst G (Scheme.reducedIdentityComponentOver G))
      ((𝟙 G ⊗ₘ Scheme.reducedIdentityComponentι G) ≫ μ[G]) q q)
    [LocallyOfFiniteType G.hom] [LocallyOfFiniteType Q.hom]
    [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left] :
    topologicalKrullDim Q.left ≤ 0 :=
  reducedIdentityComponent_topologicalKrullDim_le_zero_of_isPullback G Q q h

end AlgebraicGeometry
