/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupObject.Coset
public import AlgebraicGroups.GroupScheme.QuotientSheaf
public import Mathlib.CategoryTheory.Sites.Canonical

/-!
# Relative fppf coset quotient sheaves

For an arbitrary morphism `i : H ⟶ G` of group schemes over `S`, this file
sheafifies the type-valued presheaf of pointwise left cosets. Normality is not
required, and the quotient is not given a group structure.

If an fppf morphism `q : G ⟶ Q` has self-pullback presented by the right
action of `H`, then the resulting coset sheaf is represented by `Q`.

## Main definitions

- `AlgebraicGeometry.Scheme.relativeFppfYonedaType`
- `CategoryTheory.IsMonHom.relativeFppfCoset`
- `CategoryTheory.IsMonHom.relativeFppfCosetMk`
- `CategoryTheory.IsMonHom.relativeFppfCosetIso`

## References

* J. S. Milne, *Algebraic Groups* (2017), Definition 5.20 and
  Proposition 5.21 (left cosets and maps out of a quotient), Propositions
  5.24–5.25 (the right-action relation square and faithful flatness), and
  Theorem 5.28 / Theorem B.37 (existence over a field). The last theorem
  constructs a quotient; this module only recognizes an already supplied
  fppf target, over an arbitrary base.
* `AlgebraicGroups.GroupObject.Coset` formalizes the pointwise left-coset
  functor and the injective map to a target with the right-action pullback;
  `AlgebraicGroups.GroupScheme.QuotientSheaf` supplies the relative site and
  the group-valued counterpart for normal morphisms.
* Mathlib, `Mathlib.AlgebraicGeometry.Sites.Fpqc` and
  `Mathlib.CategoryTheory.Sites.Over` (fppf singleton covers on the relative
  site), `Mathlib.CategoryTheory.Sites.Canonical` (`uliftYoneda`),
  `Mathlib.CategoryTheory.Sites.LeftExact` and
  `Mathlib.CategoryTheory.Sites.Sheafification` (type-valued sheafification),
  and `Mathlib.CategoryTheory.Sites.LocallySurjective` and
  `Mathlib.CategoryTheory.Sites.LocallyBijective` (local surjectivity and
  the class inverted by sheafification).
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite MonoidalCategory CartesianMonoidalCategory MonObj

universe u

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}}

/-- The type-valued relative fppf sheaf represented by a scheme over `S`,
lifted to the universe in which relative fppf sheafification exists, using
Mathlib's `GrothendieckTopology.uliftYoneda` for the subcanonical site. -/
noncomputable abbrev relativeFppfYonedaType (Q : Over S) :
    Sheaf (relativeFppfTopology S) (Type (u + 1)) :=
  ((relativeFppfTopology S).uliftYoneda.{u + 1}).obj Q

/-- The morphism of type-valued relative fppf sheaves represented by a
morphism of schemes over `S`. -/
noncomputable abbrev relativeFppfYonedaTypeMap {G Q : Over S} (q : G ⟶ Q) :
    relativeFppfYonedaType G ⟶ relativeFppfYonedaType Q :=
  ((relativeFppfTopology S).uliftYoneda.{u + 1}).map q

end AlgebraicGeometry.Scheme

namespace CategoryTheory.IsMonHom

open AlgebraicGeometry AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} {H G : Over S} [GrpObj H] [GrpObj G]
variable (i : H ⟶ G) [IsMonHom i]

/-- The lifted presheaf of pointwise left cosets of `H` in `G`. -/
noncomputable abbrev relativeFppfCosetPresheaf :
    Functor (Over S)ᵒᵖ (Type (u + 1)) :=
  yonedaCoset i ⋙ CategoryTheory.uliftFunctor.{u + 1, u}

/-- The type-valued relative fppf sheafification of the pointwise left-coset
presheaf from `AlgebraicGroups.GroupObject.Coset`. Its right-action relation
models Milne's Definition 5.20, but no group structure or representing
scheme is asserted here. -/
noncomputable def relativeFppfCoset :
    Sheaf (relativeFppfTopology S) (Type (u + 1)) :=
  (presheafToSheaf (relativeFppfTopology S) (Type (u + 1))).obj
    (relativeFppfCosetPresheaf i)

/-- The pointwise left-coset projection, lifted by one universe. -/
noncomputable abbrev relativeFppfCosetPresheafMk :
    yonedaGrpObj G ⋙ CategoryTheory.forget GrpCat.{u} ⋙
        CategoryTheory.uliftFunctor.{u + 1, u} ⟶
      relativeFppfCosetPresheaf i :=
  Functor.whiskerRight (yonedaCosetMk i)
    CategoryTheory.uliftFunctor.{u + 1, u}

/-- The canonical projection from the functor of points of `G` to the
relative fppf left-coset sheaf. The pointwise coset projection is surjective
before sheafification; this sheaf morphism is locally surjective and epi,
not asserted surjective on every object's sections. -/
noncomputable def relativeFppfCosetMk :
    relativeFppfYonedaType G ⟶ relativeFppfCoset i :=
  ⟨relativeFppfCosetPresheafMk i ≫
    toSheafify (relativeFppfTopology S) (relativeFppfCosetPresheaf i)⟩

lemma relativeFppfCosetPresheafMk_app_surjective (X : (Over S)ᵒᵖ) :
    Function.Surjective ((relativeFppfCosetPresheafMk i).app X) := by
  rintro ⟨x⟩
  obtain ⟨y, rfl⟩ := yonedaCosetMk_app_surjective i X.unop x
  exact ⟨⟨y⟩, rfl⟩

instance relativeFppfCosetMk_isLocallySurjective :
    Sheaf.IsLocallySurjective (relativeFppfCosetMk i) := by
  let _ : Presheaf.IsLocallySurjective (relativeFppfTopology S)
      (relativeFppfCosetPresheafMk i) :=
    Presheaf.isLocallySurjective_of_surjective _ _
      (relativeFppfCosetPresheafMk_app_surjective i)
  let _ : Presheaf.IsLocallySurjective (relativeFppfTopology S)
      (toSheafify (relativeFppfTopology S) (relativeFppfCosetPresheaf i)) :=
    inferInstance
  exact Presheaf.isLocallySurjective_comp (relativeFppfTopology S)
    (relativeFppfCosetPresheafMk i)
    (toSheafify (relativeFppfTopology S) (relativeFppfCosetPresheaf i))

instance relativeFppfCosetMk_epi : Epi (relativeFppfCosetMk i) := by
  exact (Sheaf.isLocallySurjective_iff_epi _).1 inferInstance

variable {i}

/-- A map from the lifted pointwise coset presheaf to an fppf sheaf extends
canonically across sheafification. -/
noncomputable def relativeFppfCosetSheafifyLift
    {F : Sheaf (relativeFppfTopology S) (Type (u + 1))}
    (f : relativeFppfCosetPresheaf i ⟶ F.obj) :
    relativeFppfCoset i ⟶ F :=
  ⟨sheafifyLift (relativeFppfTopology S) f F.property⟩

@[reassoc]
lemma relativeFppfCosetMk_comp_sheafifyLift
    {F : Sheaf (relativeFppfTopology S) (Type (u + 1))}
    (f : relativeFppfCosetPresheaf i ⟶ F.obj) :
    relativeFppfCosetMk i ≫ relativeFppfCosetSheafifyLift f =
      ⟨relativeFppfCosetPresheafMk i ≫ f⟩ := by
  apply Sheaf.hom_ext
  change (relativeFppfCosetPresheafMk i ≫
    toSheafify (relativeFppfTopology S) (relativeFppfCosetPresheaf i)) ≫
      sheafifyLift (relativeFppfTopology S) f F.property =
    relativeFppfCosetPresheafMk i ≫ f
  rw [Category.assoc, toSheafify_sheafifyLift]

variable {Q : Over S} (q : G ⟶ Q)
variable (h : IsPullback (fst G H) ((𝟙 G ⊗ₘ i) ≫ μ[G]) q q)

/-- The map from the lifted pointwise coset presheaf to the lifted functor of
points represented by a candidate quotient `Q`. -/
noncomputable abbrev relativeFppfCosetPresheafMap :
    relativeFppfCosetPresheaf i ⟶ (relativeFppfYonedaType Q).obj :=
  Functor.whiskerRight (yonedaCosetMap i q h)
    CategoryTheory.uliftFunctor.{u + 1, u}

lemma relativeFppfCosetPresheafMap_app_injective (X : (Over S)ᵒᵖ) :
    Function.Injective ((relativeFppfCosetPresheafMap q h).app X) := by
  rintro ⟨x⟩ ⟨y⟩ hxy
  congr 1
  exact yonedaCosetMap_app_injective i q h X.unop (ULift.up.inj hxy)

@[reassoc]
lemma relativeFppfCosetPresheafMk_comp_map :
    relativeFppfCosetPresheafMk i ≫
      relativeFppfCosetPresheafMap q h =
      (relativeFppfYonedaTypeMap q).hom := by
  ext X x
  rcases x with ⟨x⟩
  rfl

omit [GrpObj G] in
/-- An fppf morphism of schemes over `S` is locally surjective on its lifted
relative functor of points. The proof uses Mathlib's fppf singleton-cover and
relative-site sieve APIs; it does not assert objectwise surjectivity. -/
lemma relativeFppfYonedaTypeMap_isLocallySurjective
    [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left] :
    Presheaf.IsLocallySurjective (relativeFppfTopology S)
      (relativeFppfYonedaTypeMap q).hom := by
  constructor
  intro U s
  rcases s with ⟨s⟩
  let R : Sieve Q := Sieve.generate (Presieve.singleton q)
  have hR : R ∈ relativeFppfTopology S Q := by
    rw [GrothendieckTopology.mem_over_iff]
    change Sieve.overEquiv Q (Sieve.generate (Presieve.singleton q)) ∈
      fppfTopology Q.left
    rw [Sieve.overEquiv_generate]
    have heq : Presieve.functorPushforward (Over.forget S)
        (Presieve.singleton q) =
        (Sieve.generate (Presieve.singleton q.left)).arrows := by
      funext Y f
      apply propext
      constructor
      · rintro ⟨Z, g, k, ⟨⟩, rfl⟩
        exact ⟨G.left, k, q.left, ⟨⟩, rfl⟩
      · rintro ⟨Z, k, g, ⟨⟩, hfac⟩
        exact ⟨G, q, k, ⟨⟩, hfac.symm⟩
    rw [heq, Sieve.generate_sieve]
    exact Precoverage.generate_mem_toGrothendieck
      q.left.singleton_mem_fppfPrecoverage
  apply (relativeFppfTopology S).superset_covering _
    ((relativeFppfTopology S).pullback_stable s hR)
  intro V g hg
  rcases hg with ⟨W, a, b, ⟨⟩, hab⟩
  exact ⟨ULift.up a, congrArg ULift.up hab⟩

lemma relativeFppfCosetPresheafMap_isLocallyInjective :
    Presheaf.IsLocallyInjective (relativeFppfTopology S)
      (relativeFppfCosetPresheafMap q h) :=
  Presheaf.isLocallyInjective_of_injective _ _
    (relativeFppfCosetPresheafMap_app_injective q h)

set_option linter.style.haveILetI false in
lemma relativeFppfCosetPresheafMap_isLocallySurjective
    [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left] :
    Presheaf.IsLocallySurjective (relativeFppfTopology S)
      (relativeFppfCosetPresheafMap q h) := by
  have hsurj : Presheaf.IsLocallySurjective (relativeFppfTopology S)
      (relativeFppfYonedaTypeMap q).hom :=
    relativeFppfYonedaTypeMap_isLocallySurjective q
  rw [← relativeFppfCosetPresheafMk_comp_map q h] at hsurj
  letI : Presheaf.IsLocallySurjective (relativeFppfTopology S)
      (relativeFppfCosetPresheafMk i ≫ relativeFppfCosetPresheafMap q h) := hsurj
  exact Presheaf.isLocallySurjective_of_isLocallySurjective _
    (relativeFppfCosetPresheafMk i) (relativeFppfCosetPresheafMap q h)

set_option linter.style.haveILetI false in
lemma relativeFppfCosetPresheafMap_W
    [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left] :
    (relativeFppfTopology S).W (relativeFppfCosetPresheafMap q h) := by
  letI : Presheaf.IsLocallyInjective (relativeFppfTopology S)
      (relativeFppfCosetPresheafMap q h) :=
    relativeFppfCosetPresheafMap_isLocallyInjective q h
  letI : Presheaf.IsLocallySurjective (relativeFppfTopology S)
      (relativeFppfCosetPresheafMap q h) :=
    relativeFppfCosetPresheafMap_isLocallySurjective q h
  exact (relativeFppfTopology S).W_of_isLocallyBijective _

/-- The map from the relative fppf coset sheaf to the sheaf represented by an
already supplied candidate quotient, induced by the right-action pullback. -/
noncomputable def relativeFppfCosetMap :
    relativeFppfCoset i ⟶ relativeFppfYonedaType Q :=
  relativeFppfCosetSheafifyLift (relativeFppfCosetPresheafMap q h)

@[reassoc]
lemma relativeFppfCosetMk_comp_map :
    relativeFppfCosetMk i ≫ relativeFppfCosetMap q h =
      relativeFppfYonedaTypeMap q := by
  rw [relativeFppfCosetMap, relativeFppfCosetMk_comp_sheafifyLift]
  apply Sheaf.hom_ext
  exact relativeFppfCosetPresheafMk_comp_map q h

set_option linter.style.haveILetI false in
/-- If an fppf morphism has self-pullback presented by the right action of
`H`, the induced map from the relative fppf coset sheaf is an isomorphism.
The pullback gives pointwise injectivity and the fppf singleton cover gives
local surjectivity; Mathlib's locally-bijective class `W` is inverted by
sheafification. Milne's Proposition 5.24 gives this relation for a quotient
over a field, but the present theorem assumes rather than builds its target. -/
lemma relativeFppfCosetMap_isIso
    [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left] :
    IsIso (relativeFppfCosetMap q h) := by
  let f := relativeFppfCosetPresheafMap q h
  have hw : (relativeFppfTopology S).W f :=
    relativeFppfCosetPresheafMap_W q h
  letI : IsIso ((presheafToSheaf (relativeFppfTopology S)
      (Type (u + 1))).map f) :=
    ((relativeFppfTopology S).W_iff f).1 hw
  letI : IsIso (sheafifyMap (relativeFppfTopology S) f) := by
    change IsIso ((sheafToPresheaf (relativeFppfTopology S)
      (Type (u + 1))).map
        ((presheafToSheaf (relativeFppfTopology S) (Type (u + 1))).map f))
    infer_instance
  letI : IsIso (sheafifyLift (relativeFppfTopology S) (𝟙 _)
      (relativeFppfYonedaType Q).property) := by
    rw [← isoSheafify_inv]
    infer_instance
  apply (isIso_iff_of_reflects_iso
    (relativeFppfCosetSheafifyLift f)
    (sheafToPresheaf (relativeFppfTopology S) (Type (u + 1)))).1
  change IsIso (sheafifyLift (relativeFppfTopology S) f
    (relativeFppfYonedaType Q).property)
  have hcomp : sheafifyMap (relativeFppfTopology S) f ≫
      sheafifyLift (relativeFppfTopology S) (𝟙 _)
        (relativeFppfYonedaType Q).property =
      sheafifyLift (relativeFppfTopology S) f
        (relativeFppfYonedaType Q).property := by
    simpa only [Category.comp_id] using
      sheafifyMap_sheafifyLift (relativeFppfTopology S) f (𝟙 _)
        (relativeFppfYonedaType Q).property
  exact hcomp ▸ inferInstance

/-- The relative fppf sheaf of left cosets `gH` is represented by a supplied
fppf quotient whose self-pullback is the right `H`-action
`(g, h) ↦ (g, g * i(h))`. Milne's Definition 5.20 and Propositions 5.24–5.25
are field-based antecedents; unlike Theorem 5.28 / Theorem B.37, this does
not construct a quotient of an arbitrary subgroup. Neither normality nor a
group structure on the target is assumed. -/
noncomputable def relativeFppfCosetIso
    [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left] :
    relativeFppfCoset i ≅ relativeFppfYonedaType Q := by
  letI := relativeFppfCosetMap_isIso q h
  exact asIso (relativeFppfCosetMap q h)

end CategoryTheory.IsMonHom
