/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.Gluing
public import AlgebraicGroups.GroupScheme.RepresentationSubmodule
public import AlgebraicGroups.GroupScheme.RepresentationUniverse

/-!
# Finite-dimensional subrepresentations and gluing

The finite-dimensional stages of a natural point representation are the
module-finite bundled subcomodules of its recovered right comodule. Every stage
uses its original subspace subtype, with the point representation of its
specified restricted coaction. The transition and ambient maps have exactly the
ordinary submodule inclusions as their linear maps.

`PointRepresentation.FiniteCompatibleFamily` consists of point intertwiners on
these stages, agreeing under the canonical inclusions. Conversion to the existing
compatible families of colinear maps gives gluing into any target representation.
`homEquivFiniteCompatibleFamily` identifies global point intertwiners with all
such families; its inverse is `glueFinite`. Restriction, reconstruction,
uniqueness, target naturality and source factorization laws concern the original
ambient module, not a replacement union carrier.

The stage index depends only on the specified comodule, not the test level.
Changing test levels transports whole compatible families on those same stages,
retains their underlying maps, and commutes with gluing. The corresponding
stock-lift restriction follows from the value comparison in
`RepresentationUniverse`. All scalar-extension squares are stated for the
canonical evaluation of the same coactions, at independently sized algebras.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 4, §c, Proposition 4.7 and
  Corollary 4.8, for finite-dimensional subrepresentations of rational
  representations of affine groups.
* M. E. Sweedler, *Hopf Algebras*, W. A. Benjamin, 1969, for the coalgebra
  finite-containment theorem reused by the finite-stage system.
* The right-comodule gluing, representation–comodule equivalence, intertwiner,
  invariant-submodule and tester-universe formalizations in this library.
* Mathlib's submodule inclusions, module finiteness, flat tensor maps and
  module direct limits, the last reused through right-comodule gluing.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u a v w z t s r

namespace AlgebraicGeometry.PointRepresentation

variable {K : Type u} [Field K] {C : Type a} [CommRing C] [HopfAlgebra K C]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable {W : Type w} [AddCommGroup W] [Module K W]
variable {U : Type z} [AddCommGroup U] [Module K U]
variable {X : Coalgebra.RightComodule K C V}

/-- The original subspace of a bundled subcomodule, with the point representation
of its specified restricted coaction. -/
abbrev subcomoduleRepresentation (S : X.Subcomodule) :
    PointRepresentation.{u, a, v, t} K C S.toSubmodule :=
  ofRightComodule S.comodule

/-- Reconstruction retains the specified coaction on the same subspace subtype. -/
theorem subcomoduleRepresentation_toRightComodule (S : X.Subcomodule) :
    (subcomoduleRepresentation.{u, a, v, t} S).toRightComodule = S.comodule :=
  toRightComodule_ofRightComodule S.comodule

/-- The stage's recovered coaction is its specified original coaction map. -/
theorem subcomoduleRepresentation_recoveredCoaction (S : X.Subcomodule) :
    (subcomoduleRepresentation.{u, a, v, t} S).recoveredCoaction = S.comodule.coaction :=
  recoveredCoaction_ofRightComodule S.comodule

/-- The canonical stage transition is transported from the existing colinear
inclusion without changing its linear map. -/
def subcomoduleInclusion {S T : X.Subcomodule} (h : S ≤ T) :
    PointHom (subcomoduleRepresentation.{u, a, v, t} S)
      (subcomoduleRepresentation T) :=
  (pointHomEquiv _ _).symm
    { toLinearMap := (Coalgebra.RightComodule.Subcomodule.inclusion h).toLinearMap
      colinear := by
        simpa only [subcomoduleRepresentation_toRightComodule] using
          (Coalgebra.RightComodule.Subcomodule.inclusion h).colinear }

@[simp] theorem subcomoduleInclusion_toLinearMap {S T : X.Subcomodule} (h : S ≤ T) :
    (subcomoduleInclusion.{u, a, v, t} h).toLinearMap = Submodule.inclusion h := rfl

theorem subcomoduleInclusion_apply {S T : X.Subcomodule} (h : S ≤ T)
    (x : S.toSubmodule) :
    (subcomoduleInclusion.{u, a, v, t} h).toLinearMap x = ⟨x, h x.property⟩ := rfl

/-- Inclusion of a stage into itself is the point identity. -/
@[simp] theorem subcomoduleInclusion_refl (S : X.Subcomodule) :
    subcomoduleInclusion.{u, a, v, t} (le_refl S) =
      PointHom.id (subcomoduleRepresentation S) := by
  apply PointHom.ext
  intro x
  rfl

/-- Transitions compose according to the original submodule order. -/
@[simp] theorem subcomoduleInclusion_comp {S T Q : X.Subcomodule}
    (hST : S ≤ T) (hTQ : T ≤ Q) :
    (subcomoduleInclusion.{u, a, v, t} hTQ).comp (subcomoduleInclusion hST) =
      subcomoduleInclusion (hST.trans hTQ) := by
  apply PointHom.ext
  intro x
  rfl

/-- The canonical stage transition intertwines the given in-slice operators. -/
theorem subcomoduleInclusion_operator {S T : X.Subcomodule} (h : S ≤ T)
    (R : CommAlgCat.{max a t, u} K) (g : C →ₐ[K] R)
    (z : R ⊗[K] S.toSubmodule) :
    (Submodule.inclusion h).baseChange R
        (((subcomoduleRepresentation.{u, a, v, t} S).operator R g).val z) =
      ((subcomoduleRepresentation.{u, a, v, t} T).operator R g).val
        ((Submodule.inclusion h).baseChange R z) :=
  (subcomoduleInclusion h).operator_apply R g z

/-- The transition square at every independently sized algebra uses the stock
scalar extension of the original submodule inclusion. -/
theorem subcomoduleInclusion_evaluate {S T : X.Subcomodule} (h : S ≤ T)
    {R : Type r} [CommRing R] [Algebra K R] (g : C →ₐ[K] R)
    (z : R ⊗[K] S.toSubmodule) :
    (Submodule.inclusion h).baseChange R
        ((subcomoduleRepresentation.{u, a, v, t} S).evaluate g z) =
      (subcomoduleRepresentation.{u, a, v, t} T).evaluate g
        ((Submodule.inclusion h).baseChange R z) :=
  (subcomoduleInclusion h).baseChange_evaluate_apply g z

variable (η : PointRepresentation.{u, a, v, t} K C V)
variable (θ : PointRepresentation.{u, a, w, t} K C W)
variable (ξ : PointRepresentation.{u, a, z, t} K C U)

/-- The canonical point intertwiner from a subcomodule stage to the original
representation has precisely the original subtype map as its linear data. -/
def subcomoduleSubtype (S : η.toRightComodule.Subcomodule) :
    PointHom (subcomoduleRepresentation S) η :=
  (pointHomEquiv _ _).symm
    { toLinearMap := S.toSubmodule.subtype
      colinear := by
        rw [subcomoduleRepresentation_toRightComodule]
        exact S.subtype.colinear }

@[simp] theorem subcomoduleSubtype_toLinearMap (S : η.toRightComodule.Subcomodule) :
    (η.subcomoduleSubtype S).toLinearMap = S.toSubmodule.subtype := rfl

@[simp] theorem subcomoduleSubtype_apply (S : η.toRightComodule.Subcomodule)
    (x : S.toSubmodule) : (η.subcomoduleSubtype S).toLinearMap x = (x : V) := rfl

/-- The canonical ambient triangle commutes as point-morphism values. -/
@[simp] theorem subcomoduleSubtype_comp_inclusion {S T : η.toRightComodule.Subcomodule}
    (h : S ≤ T) :
    (η.subcomoduleSubtype T).comp (subcomoduleInclusion h) = η.subcomoduleSubtype S := by
  apply PointHom.ext
  intro x
  rfl

/-- The stage coaction is the uniquely restricted original coaction, as a
specified comodule value on exactly the original subspace subtype. -/
theorem subcomodule_restrictedComodule (S : η.toRightComodule.Subcomodule) :
    η.restrictedComodule S.toSubmodule ((η.isInvariant_iff_isStable _).2 S.isStable) =
      S.comodule := by
  symm
  apply η.restrictedComodule_unique
  exact S.subtype_colinear

/-- A stage presentation agrees with canonical restriction of the original
representation, as a natural-transformation value, not only up to isomorphism. -/
theorem subcomoduleRepresentation_eq_restricted (S : η.toRightComodule.Subcomodule) :
    subcomoduleRepresentation S =
      η.restrictedPointRepresentation S.toSubmodule
        ((η.isInvariant_iff_isStable _).2 S.isStable) := by
  apply η.restrictedPointRepresentation_unique
  exact (η.subcomoduleSubtype S).property

/-- Every stage preserves the original scalar-extension image under all
canonical algebra-valued operators. -/
theorem subcomodule_evaluate_mem (S : η.toRightComodule.Subcomodule)
    {R : Type r} [CommRing R] [Algebra K R] (g : C →ₐ[K] R)
    {z : R ⊗[K] V} (hz : z ∈ S.toSubmodule.baseChange R) :
    η.evaluate g z ∈ S.toSubmodule.baseChange R :=
  S.isStable.evaluate_mem_baseChange g.toLinearMap hz

/-- The ambient inclusion square at every algebra uses the same restricted
coaction and exactly the stock scalar-extended subtype map. -/
theorem subcomoduleSubtype_evaluate (S : η.toRightComodule.Subcomodule)
    {R : Type r} [CommRing R] [Algebra K R] (g : C →ₐ[K] R)
    (z : R ⊗[K] S.toSubmodule) :
    S.toSubmodule.subtype.baseChange R
        ((subcomoduleRepresentation.{u, a, v, t} S).evaluate g z) =
      η.evaluate g (S.toSubmodule.subtype.baseChange R z) :=
  (η.subcomoduleSubtype S).baseChange_evaluate_apply g z

/-- In the original slice the square is also the square of the given components. -/
theorem subcomoduleSubtype_operator (S : η.toRightComodule.Subcomodule)
    (R : CommAlgCat.{max a t, u} K) (g : C →ₐ[K] R)
    (z : R ⊗[K] S.toSubmodule) :
    S.toSubmodule.subtype.baseChange R
        (((subcomoduleRepresentation.{u, a, v, t} S).operator R g).val z) =
      (η.operator R g).val (S.toSubmodule.subtype.baseChange R z) :=
  (η.subcomoduleSubtype S).operator_apply R g z

/-- Over a field every scalar-extended stage inclusion is injective. The reason
is flatness of the coefficient algebra as a vector space, not finiteness. -/
theorem subcomoduleSubtype_baseChange_injective (S : η.toRightComodule.Subcomodule)
    (R : Type r) [CommRing R] [Algebra K R] :
    Function.Injective (S.toSubmodule.subtype.baseChange R) :=
  Module.Flat.lTensor_preserves_injective_linearMap S.toSubmodule.subtype
    Subtype.val_injective

/-- The finite-dimensional stages are the existing module-finite bundled
subcomodules. No replacement subrepresentation carrier is introduced. -/
abbrev finiteStages := η.toRightComodule.finiteSubcomodules

/-- Every invariant finite-dimensional original subspace is a stage, through
the existing uniquely restricted subcomodule construction. -/
def finiteStageOfInvariant (L : Submodule K V) (hL : η.IsInvariant L)
    [FiniteDimensional K L] : η.finiteStages :=
  ⟨η.restrictedSubcomodule L hL, show Module.Finite K L from inferInstance⟩

@[simp] theorem finiteStageOfInvariant_toSubmodule (L : Submodule K V)
    (hL : η.IsInvariant L) [FiniteDimensional K L] :
    (η.finiteStageOfInvariant L hL).val.toSubmodule = L := rfl

/-- This stage has exactly the original restricted point representation value. -/
@[simp] theorem finiteStageOfInvariant_representation (L : Submodule K V)
    (hL : η.IsInvariant L) [FiniteDimensional K L] :
    subcomoduleRepresentation.{u, a, v, t} (η.finiteStageOfInvariant L hL).val =
      η.restrictedPointRepresentation L hL := rfl

/-- Finiteness on a stage is finiteness of its original subspace subtype. -/
theorem finiteStage_finiteDimensional (S : η.finiteStages) :
    FiniteDimensional K S.val.toSubmodule := S.property

/-- The same stages may equivalently be specified by finite generation. -/
theorem finiteStage_fg (S : η.finiteStages) : S.val.toSubmodule.FG :=
  (Coalgebra.RightComodule.mem_finiteSubcomodules_iff_fg S.val).1 S.property

/-- The finite-stage system is nonempty, witnessed by the canonical zero stage. -/
theorem finiteStages_nonempty : η.finiteStages.Nonempty :=
  η.toRightComodule.finiteSubcomodules_nonempty

/-- The canonical zero subcomodule is a finite-dimensional stage. -/
theorem bot_mem_finiteStages : (⊥ : η.toRightComodule.Subcomodule) ∈ η.finiteStages :=
  η.toRightComodule.bot_mem_finiteSubcomodules

/-- Finite stages are closed under the ordinary binary subspace join. -/
theorem sup_mem_finiteStages {S T : η.toRightComodule.Subcomodule}
    (hS : S ∈ η.finiteStages) (hT : T ∈ η.finiteStages) : S ⊔ T ∈ η.finiteStages :=
  Coalgebra.RightComodule.sup_mem_finiteSubcomodules hS hT

/-- Directedness is transported on the same bundled subcomodules and order. -/
theorem directedOn_finiteStages : DirectedOn (· ≤ ·) η.finiteStages :=
  η.toRightComodule.directedOn_finiteSubcomodules

/-- Every finite subset of the original representation lies in a finite stage.
This is the finite-subcomodule theorem, not a new containment construction. -/
theorem finiteStages_contain_finite {s : Set V} (hs : s.Finite) :
    ∃ S : η.finiteStages, s ⊆ (S.val : Set V) :=
  η.toRightComodule.finiteSubcomodules_contain_finite hs

/-- The finite-dimensional subrepresentations cover the original module. -/
theorem finiteStages_cover (x : V) : ∃ S : η.finiteStages, x ∈ S.val :=
  η.toRightComodule.finiteSubcomodules_cover x

/-- A compatible family of point intertwiners on the finite-dimensional
subcomodules of a specified comodule. The index is independent of test level,
so a change of test algebras retains the same subspaces and order. -/
structure FiniteCompatibleFamily (X : Coalgebra.RightComodule K C V)
    (θ : PointRepresentation.{u, a, w, t} K C W) where
  /-- The map from each original stage subtype to the target. -/
  hom (S : X.finiteSubcomodules) : PointHom (subcomoduleRepresentation S.val) θ
  /-- Agreement under exactly the canonical stage inclusions. -/
  compatible (S T : X.finiteSubcomodules) (h : S ≤ T) :
    (hom T).comp (subcomoduleInclusion h) = hom S

namespace FiniteCompatibleFamily

variable {η θ ξ}

/-- Families are determined by their stage maps. -/
@[ext] theorem ext {f g : FiniteCompatibleFamily X θ}
    (h : ∀ S, f.hom S = g.hom S) : f = g := by
  cases f with
  | mk f hf =>
    cases g with
    | mk g hg =>
      have hfg : f = g := funext h
      subst g
      rfl

/-- Convert a point family to the existing compatible colinear family. Its
linear maps are unchanged; the comodule-value inverse identifies each stage. -/
def toComoduleFamily (f : FiniteCompatibleFamily X θ) :
    Coalgebra.RightComodule.Subcomodule.CompatibleFamily X.finiteSubcomodules
      θ.toRightComodule where
  hom S :=
    { toLinearMap := (pointHomEquiv _ _ (f.hom S)).toLinearMap
      colinear := by
        simpa only [subcomoduleRepresentation_toRightComodule] using
          (pointHomEquiv _ _ (f.hom S)).colinear }
  compatible S T h := by
    apply Coalgebra.RightComoduleHom.toLinearMap_injective
    exact congrArg PointHom.toLinearMap (f.compatible S T h)

@[simp] theorem toComoduleFamily_hom_toLinearMap (f : FiniteCompatibleFamily X θ)
    (S : X.finiteSubcomodules) :
    (f.toComoduleFamily.hom S).toLinearMap = (f.hom S).toLinearMap := rfl

/-- Transport an existing compatible colinear family back to point intertwiners
on exactly its original stage subtypes. -/
def ofComoduleFamily
    (f : Coalgebra.RightComodule.Subcomodule.CompatibleFamily X.finiteSubcomodules
      θ.toRightComodule) : FiniteCompatibleFamily X θ where
  hom S := (pointHomEquiv _ _).symm
    { toLinearMap := (f.hom S).toLinearMap
      colinear := by
        simpa only [subcomoduleRepresentation_toRightComodule] using (f.hom S).colinear }
  compatible S T h := by
    apply PointHom.toLinearMap_injective
    exact congrArg Coalgebra.RightComoduleHom.toLinearMap (f.compatible S T h)

@[simp] theorem ofComoduleFamily_hom_toLinearMap
    (f : Coalgebra.RightComodule.Subcomodule.CompatibleFamily X.finiteSubcomodules
      θ.toRightComodule) (S : X.finiteSubcomodules) :
    ((ofComoduleFamily f).hom S).toLinearMap = (f.hom S).toLinearMap := rfl

/-- Conversion in either direction retains the whole point family value. -/
@[simp] theorem ofComoduleFamily_toComoduleFamily (f : FiniteCompatibleFamily X θ) :
    ofComoduleFamily f.toComoduleFamily = f := by
  apply ext
  intro S
  apply PointHom.toLinearMap_injective
  rfl

/-- Conversion in either direction retains the whole colinear family value. -/
@[simp] theorem toComoduleFamily_ofComoduleFamily
    (f : Coalgebra.RightComodule.Subcomodule.CompatibleFamily X.finiteSubcomodules
      θ.toRightComodule) : (ofComoduleFamily f).toComoduleFamily = f := by
  apply Coalgebra.RightComodule.Subcomodule.CompatibleFamily.ext
  intro S
  apply Coalgebra.RightComoduleHom.toLinearMap_injective
  rfl

/-- The constructed family correspondence uses the existing Hom dictionary,
not an additional gluing or compatibility provider. -/
def comoduleFamilyEquiv : FiniteCompatibleFamily X θ ≃
    Coalgebra.RightComodule.Subcomodule.CompatibleFamily X.finiteSubcomodules
      θ.toRightComodule where
  toFun := toComoduleFamily
  invFun := ofComoduleFamily
  left_inv := ofComoduleFamily_toComoduleFamily
  right_inv := toComoduleFamily_ofComoduleFamily

/-- Postcompose every stage map with a point intertwiner. -/
def postcomp (f : FiniteCompatibleFamily X θ) (g : PointHom θ ξ) :
    FiniteCompatibleFamily X ξ where
  hom S := g.comp (f.hom S)
  compatible S T h := by rw [PointHom.comp_assoc, f.compatible S T h]

@[simp] theorem postcomp_hom (f : FiniteCompatibleFamily X θ) (g : PointHom θ ξ)
    (S : X.finiteSubcomodules) : (f.postcomp g).hom S = g.comp (f.hom S) := rfl

@[simp] theorem postcomp_id (f : FiniteCompatibleFamily X θ) :
    f.postcomp (PointHom.id θ) = f := by
  apply ext
  intro S
  exact PointHom.id_comp _

/-- Family postcomposition respects composition. -/
@[simp] theorem postcomp_comp (f : FiniteCompatibleFamily X η)
    (g : PointHom η θ) (h : PointHom θ ξ) :
    (f.postcomp g).postcomp h = f.postcomp (h.comp g) := by
  apply ext
  intro S
  exact (PointHom.comp_assoc h g (f.hom S)).symm

/-- Family conversion commutes with the existing colinear postcomposition. -/
@[simp] theorem toComoduleFamily_postcomp (f : FiniteCompatibleFamily X θ)
    (g : PointHom θ ξ) :
    (f.postcomp g).toComoduleFamily = f.toComoduleFamily.postcomp g.toRightComoduleHom := by
  apply Coalgebra.RightComodule.Subcomodule.CompatibleFamily.ext
  intro S
  apply Coalgebra.RightComoduleHom.toLinearMap_injective
  rfl

end FiniteCompatibleFamily

/-- Restrict a global point intertwiner to all finite-dimensional subrepresentations. -/
def restrictFinite (f : PointHom η θ) : FiniteCompatibleFamily η.toRightComodule θ where
  hom S := f.comp (η.subcomoduleSubtype S.val)
  compatible S T h := by
    rw [PointHom.comp_assoc, subcomoduleSubtype_comp_inclusion]

@[simp] theorem restrictFinite_hom (f : PointHom η θ) (S : η.finiteStages) :
    (restrictFinite η θ f).hom S = f.comp (η.subcomoduleSubtype S.val) := rfl

/-- Restriction is exactly the existing colinear restriction after conversion. -/
@[simp] theorem restrictFinite_toComoduleFamily (f : PointHom η θ) :
    (restrictFinite η θ f).toComoduleFamily =
      Coalgebra.RightComodule.Subcomodule.CompatibleFamily.restrict
        η.toRightComodule.finiteSubcomodules f.toRightComoduleHom := by
  apply Coalgebra.RightComodule.Subcomodule.CompatibleFamily.ext
  intro S
  apply Coalgebra.RightComoduleHom.toLinearMap_injective
  rfl

/-- Glue every compatible point family to the original representation, into any
specified target. The construction is the existing colinear glue followed by
the inverse Hom dictionary, retaining exactly its underlying linear map. -/
def glueFinite (f : FiniteCompatibleFamily η.toRightComodule θ) : PointHom η θ :=
  (pointHomEquiv η θ).symm (Coalgebra.RightComodule.glueFiniteDimensional f.toComoduleFamily)

/-- The underlying map is precisely the existing colinear glued map. -/
@[simp] theorem glueFinite_toLinearMap (f : FiniteCompatibleFamily η.toRightComodule θ) :
    (glueFinite η θ f).toLinearMap =
      (Coalgebra.RightComodule.glueFiniteDimensional f.toComoduleFamily).toLinearMap := rfl

/-- The complete colinear map reads back through the Hom dictionary. -/
@[simp] theorem glueFinite_toRightComoduleHom
    (f : FiniteCompatibleFamily η.toRightComodule θ) :
    (glueFinite η θ f).toRightComoduleHom =
      Coalgebra.RightComodule.glueFiniteDimensional f.toComoduleFamily :=
  PointHom.ofRightComoduleHom_toRightComoduleHom _

/-- Evaluation on any original stage gives its prescribed point map. -/
theorem glueFinite_apply (f : FiniteCompatibleFamily η.toRightComodule θ)
    (S : η.finiteStages) (x : S.val.toSubmodule) :
    (glueFinite η θ f).toLinearMap (x : V) = (f.hom S).toLinearMap x :=
  Coalgebra.RightComodule.glueFiniteDimensional_apply f.toComoduleFamily S x

/-- Evaluate using any stage containing the given ambient element. -/
theorem glueFinite_apply_of_mem (f : FiniteCompatibleFamily η.toRightComodule θ)
    (S : η.finiteStages) (x : V) (hx : x ∈ S.val) :
    (glueFinite η θ f).toLinearMap x = (f.hom S).toLinearMap ⟨x, hx⟩ :=
  glueFinite_apply η θ f S ⟨x, hx⟩

/-- Restriction to each stage is the prescribed bundled point morphism value. -/
@[simp] theorem glueFinite_comp_subtype (f : FiniteCompatibleFamily η.toRightComodule θ)
    (S : η.finiteStages) :
    (glueFinite η θ f).comp (η.subcomoduleSubtype S.val) = f.hom S := by
  apply PointHom.ext
  intro x
  exact glueFinite_apply η θ f S x

/-- Equality of global point morphisms is determined by their covering stages. -/
theorem pointHom_ext_finite {f g : PointHom η θ}
    (h : ∀ S : η.finiteStages,
      f.comp (η.subcomoduleSubtype S.val) = g.comp (η.subcomoduleSubtype S.val)) :
    f = g := by
  apply PointHom.ext
  intro x
  obtain ⟨S, hx⟩ := η.finiteStages_cover x
  exact congrArg (fun k : PointHom (subcomoduleRepresentation S.val) θ ↦
    k.toLinearMap ⟨x, hx⟩) (h S)

/-- The stage restrictions characterize the global glued point morphism. -/
theorem glueFinite_unique (f : FiniteCompatibleFamily η.toRightComodule θ)
    (g : PointHom η θ)
    (hg : ∀ S : η.finiteStages, g.comp (η.subcomoduleSubtype S.val) = f.hom S) :
    g = glueFinite η θ f := by
  apply pointHom_ext_finite η θ
  intro S
  rw [hg S, glueFinite_comp_subtype]

/-- Every compatible family to an arbitrary target has a unique global point
intertwiner. No finite-dimensionality assumption is imposed on the target. -/
theorem existsUnique_glueFinite (f : FiniteCompatibleFamily η.toRightComodule θ) :
    ∃! g : PointHom η θ,
      ∀ S : η.finiteStages, g.comp (η.subcomoduleSubtype S.val) = f.hom S :=
  ⟨glueFinite η θ f, glueFinite_comp_subtype η θ f,
    fun g hg ↦ glueFinite_unique η θ f g hg⟩

/-- Restriction reads back the entire original compatible family value. -/
@[simp] theorem restrict_glueFinite (f : FiniteCompatibleFamily η.toRightComodule θ) :
    restrictFinite η θ (glueFinite η θ f) = f := by
  apply FiniteCompatibleFamily.ext
  exact glueFinite_comp_subtype η θ f

/-- Gluing the restrictions reconstructs the original global point morphism. -/
@[simp] theorem glueFinite_restrict (f : PointHom η θ) :
    glueFinite η θ (restrictFinite η θ f) = f :=
  (glueFinite_unique η θ (restrictFinite η θ f) f (fun _ ↦ rfl)).symm

/-- Global point morphisms are equivalent to all compatible finite-stage point
families, with restriction and gluing as the two constructed inverse functions. -/
def homEquivFiniteCompatibleFamily :
    PointHom η θ ≃ FiniteCompatibleFamily η.toRightComodule θ where
  toFun := restrictFinite η θ
  invFun := glueFinite η θ
  left_inv := glueFinite_restrict η θ
  right_inv := restrict_glueFinite η θ

@[simp] theorem homEquivFiniteCompatibleFamily_apply (f : PointHom η θ) :
    homEquivFiniteCompatibleFamily η θ f = restrictFinite η θ f := rfl

@[simp] theorem homEquivFiniteCompatibleFamily_symm_apply
    (f : FiniteCompatibleFamily η.toRightComodule θ) :
    (homEquivFiniteCompatibleFamily η θ).symm f = glueFinite η θ f := rfl

/-- Restriction commutes with target postcomposition as whole family values. -/
@[simp] theorem restrictFinite_postcomp (f : PointHom η θ) (g : PointHom θ ξ) :
    restrictFinite η ξ (g.comp f) = (restrictFinite η θ f).postcomp g := by
  apply FiniteCompatibleFamily.ext
  intro S
  exact PointHom.comp_assoc g f (η.subcomoduleSubtype S.val)

/-- Gluing commutes with arbitrary target morphisms. -/
@[simp] theorem glueFinite_postcomp (f : FiniteCompatibleFamily η.toRightComodule θ)
    (g : PointHom θ ξ) :
    glueFinite η ξ (f.postcomp g) = g.comp (glueFinite η θ f) := by
  symm
  apply glueFinite_unique η ξ (f.postcomp g)
  intro S
  rw [PointHom.comp_assoc, glueFinite_comp_subtype,
    FiniteCompatibleFamily.postcomp_hom]

/-- The global identity is reconstructed from the canonical stage inclusions.
This exercises the gluing equivalence on the given ambient representation. -/
theorem glueFinite_subtypes :
    glueFinite η η (restrictFinite η η (PointHom.id η)) = PointHom.id η :=
  glueFinite_restrict η η (PointHom.id η)

/-- At every coefficient algebra the glued map intertwines the canonical
operators of the same original coactions on every tensor. -/
theorem glueFinite_evaluate (f : FiniteCompatibleFamily η.toRightComodule θ)
    {R : Type r} [CommRing R] [Algebra K R] (g : C →ₐ[K] R) (z : R ⊗[K] V) :
    (glueFinite η θ f).toLinearMap.baseChange R (η.evaluate g z) =
      θ.evaluate g ((glueFinite η θ f).toLinearMap.baseChange R z) :=
  (glueFinite η θ f).baseChange_evaluate_apply g z

/-- The stage readback is also an equality of scalar-extended linear maps, not
just of their values on vectors over the base field. -/
theorem glueFinite_baseChange_comp_subtype
    (f : FiniteCompatibleFamily η.toRightComodule θ) (S : η.finiteStages)
    (R : Type r) [CommRing R] [Algebra K R] :
    (glueFinite η θ f).toLinearMap.baseChange R ∘ₗ S.val.toSubmodule.subtype.baseChange R =
      (f.hom S).toLinearMap.baseChange R := by
  rw [← LinearMap.baseChange_comp]
  exact congrArg (fun l : S.val.toSubmodule →ₗ[K] W ↦ l.baseChange R)
    (congrArg PointHom.toLinearMap (glueFinite_comp_subtype η θ f S))

/-- Pull back a compatible family along any ambient point morphism. There is
no stage-factorability hypothesis: glue, precompose and restrict. -/
def FiniteCompatibleFamily.pullback (f : FiniteCompatibleFamily θ.toRightComodule ξ)
    (g : PointHom η θ) : FiniteCompatibleFamily η.toRightComodule ξ :=
  restrictFinite η ξ ((glueFinite θ ξ f).comp g)

/-- Unrestricted source-morphism naturality of gluing. -/
@[simp] theorem glueFinite_pullback (f : FiniteCompatibleFamily θ.toRightComodule ξ)
    (g : PointHom η θ) :
    glueFinite η ξ (f.pullback η θ ξ g) = (glueFinite θ ξ f).comp g :=
  glueFinite_restrict η ξ _

/-- Pullback along the identity returns the original family value. -/
@[simp] theorem FiniteCompatibleFamily.pullback_id
    (f : FiniteCompatibleFamily η.toRightComodule θ) :
    f.pullback η η θ (PointHom.id η) = f := by
  simp only [FiniteCompatibleFamily.pullback, PointHom.comp_id, restrict_glueFinite]

/-- Pullback respects composition of arbitrary source morphisms. -/
@[simp] theorem FiniteCompatibleFamily.pullback_comp
    {Q : Type r} [AddCommGroup Q] [Module K Q]
    (ζ : PointRepresentation.{u, a, r, t} K C Q)
    (f : FiniteCompatibleFamily ξ.toRightComodule ζ)
    (g : PointHom η θ) (h : PointHom θ ξ) :
    (f.pullback θ ξ ζ h).pullback η θ ζ g = f.pullback η ξ ζ (h.comp g) := by
  simp only [FiniteCompatibleFamily.pullback, glueFinite_restrict, PointHom.comp_assoc]

/-- Restriction is natural under arbitrary precomposition. -/
@[simp] theorem restrictFinite_precomp (g : PointHom η θ) (h : PointHom θ ξ) :
    (restrictFinite θ ξ h).pullback η θ ξ g = restrictFinite η ξ (h.comp g) := by
  rw [FiniteCompatibleFamily.pullback, glueFinite_restrict]

/-- Source pullback commutes with target postcomposition. -/
theorem FiniteCompatibleFamily.pullback_postcomp
    {Q : Type r} [AddCommGroup Q] [Module K Q]
    (ζ : PointRepresentation.{u, a, r, t} K C Q)
    (f : FiniteCompatibleFamily θ.toRightComodule ξ) (g : PointHom η θ)
    (h : PointHom ξ ζ) :
    (f.pullback η θ ξ g).postcomp h = (f.postcomp h).pullback η θ ζ g := by
  simp only [FiniteCompatibleFamily.pullback, glueFinite_postcomp,
    ← restrictFinite_postcomp, PointHom.comp_assoc]

/-- Every finite source stage has its entire image in some finite target stage.
Only finite generation of its ordinary linear image and the existing
finite-subset containment theorem are used. -/
theorem finiteStage_image_contained (g : PointHom η θ) (S : η.finiteStages) :
    ∃ T : θ.finiteStages,
      S.val.toSubmodule.map g.toLinearMap ≤ T.val.toSubmodule := by
  have hfg := (η.finiteStage_fg S).map g.toLinearMap
  obtain ⟨s, hs, hspan⟩ := Submodule.fg_def.mp hfg
  obtain ⟨T, hsT⟩ := θ.finiteStages_contain_finite hs
  refine ⟨T, ?_⟩
  rw [← hspan]
  exact Submodule.span_le.mpr hsT

/-- The stage map for any supplied finite target stage containing the image.
Its map is the stock codomain restriction of the original linear composite;
colinearity comes from the existing subcomodule factorization theorem. -/
def finiteStageMap (g : PointHom η θ) (S : η.finiteStages) (T : θ.finiteStages)
    (h : S.val.toSubmodule.map g.toLinearMap ≤ T.val.toSubmodule) :
    PointHom (subcomoduleRepresentation.{u, a, v, t} S.val)
      (subcomoduleRepresentation.{u, a, w, t} T.val) :=
  (pointHomEquiv _ _).symm
    { toLinearMap := LinearMap.codRestrict T.val.toSubmodule
        (g.toLinearMap.comp S.val.toSubmodule.subtype)
        (fun x ↦ h ⟨x, x.property, rfl⟩)
      colinear := by
        rw [subcomoduleRepresentation_toRightComodule,
          subcomoduleRepresentation_toRightComodule]
        obtain ⟨l, hl, _⟩ := T.val.existsUnique_factorization S.val.comodule
          (g.toRightComoduleHom.comp S.val.subtype) (fun x ↦ h ⟨x, x.property, rfl⟩)
        have hlinear : l.toLinearMap = LinearMap.codRestrict T.val.toSubmodule
            (g.toLinearMap.comp S.val.toSubmodule.subtype)
            (fun x ↦ h ⟨x, x.property, rfl⟩) := by
          apply LinearMap.ext
          intro x
          apply Subtype.ext
          exact congrArg (fun k : Coalgebra.RightComoduleHom S.val.comodule
            θ.toRightComodule ↦ k x) hl
        rw [← hlinear]
        exact l.colinear }

/-- The factored stage map retains the original ambient value. -/
@[simp] theorem finiteStageMap_apply (g : PointHom η θ) (S : η.finiteStages)
    (T : θ.finiteStages)
    (h : S.val.toSubmodule.map g.toLinearMap ≤ T.val.toSubmodule)
    (x : S.val.toSubmodule) :
    (finiteStageMap η θ g S T h).toLinearMap x =
      ⟨g.toLinearMap x, h ⟨x, x.property, rfl⟩⟩ := rfl

/-- The factorization triangle is an equality of bundled point morphisms. -/
@[simp] theorem subcomoduleSubtype_comp_finiteStageMap (g : PointHom η θ)
    (S : η.finiteStages) (T : θ.finiteStages)
    (h : S.val.toSubmodule.map g.toLinearMap ≤ T.val.toSubmodule) :
    (θ.subcomoduleSubtype T.val).comp (finiteStageMap η θ g S T h) =
      g.comp (η.subcomoduleSubtype S.val) := by
  apply PointHom.ext
  intro x
  rfl

/-- The factorization triangle uniquely determines the stage point map. -/
theorem finiteStageMap_unique (g : PointHom η θ) (S : η.finiteStages)
    (T : θ.finiteStages)
    (h : S.val.toSubmodule.map g.toLinearMap ≤ T.val.toSubmodule)
    (k : PointHom (subcomoduleRepresentation.{u, a, v, t} S.val)
      (subcomoduleRepresentation.{u, a, w, t} T.val))
    (hk : (θ.subcomoduleSubtype T.val).comp k = g.comp (η.subcomoduleSubtype S.val)) :
    k = finiteStageMap η θ g S T h := by
  apply PointHom.ext
  intro x
  apply Subtype.ext
  exact congrArg (fun l : PointHom (subcomoduleRepresentation S.val) θ ↦
    l.toLinearMap x) hk

/-- Each supplied target stage computes the unrestricted pullback on the source
stage. The formula does not depend on choosing target stages globally. -/
theorem FiniteCompatibleFamily.pullback_hom
    (f : FiniteCompatibleFamily θ.toRightComodule ξ) (g : PointHom η θ)
    (S : η.finiteStages) (T : θ.finiteStages)
    (h : S.val.toSubmodule.map g.toLinearMap ≤ T.val.toSubmodule) :
    (f.pullback η θ ξ g).hom S = (f.hom T).comp (finiteStageMap η θ g S T h) := by
  apply PointHom.ext
  intro x
  exact glueFinite_apply θ ξ f T ⟨g.toLinearMap x, h ⟨x, x.property, rfl⟩⟩

/-- The same stage formula holds for any supplied factorization of the source
morphism through a finite target stage, not just its canonical construction. -/
theorem FiniteCompatibleFamily.pullback_hom_of_factorization
    (f : FiniteCompatibleFamily θ.toRightComodule ξ) (g : PointHom η θ)
    (S : η.finiteStages) (T : θ.finiteStages)
    (h : S.val.toSubmodule.map g.toLinearMap ≤ T.val.toSubmodule)
    (k : PointHom (subcomoduleRepresentation.{u, a, v, t} S.val)
      (subcomoduleRepresentation.{u, a, w, t} T.val))
    (hk : (θ.subcomoduleSubtype T.val).comp k = g.comp (η.subcomoduleSubtype S.val)) :
    (f.pullback η θ ξ g).hom S = (f.hom T).comp k := by
  rw [finiteStageMap_unique η θ g S T h k hk]
  exact f.pullback_hom η θ ξ g S T h

/-- Stagewise evaluation of a pullback is independent of every target-stage and
factorization choice, by the unique global extension. -/
theorem FiniteCompatibleFamily.stageMap_independent
    (f : FiniteCompatibleFamily θ.toRightComodule ξ) (g : PointHom η θ)
    (S : η.finiteStages) (T T' : θ.finiteStages)
    (h : S.val.toSubmodule.map g.toLinearMap ≤ T.val.toSubmodule)
    (h' : S.val.toSubmodule.map g.toLinearMap ≤ T'.val.toSubmodule) :
    (f.hom T).comp (finiteStageMap η θ g S T h) =
      (f.hom T').comp (finiteStageMap η θ g S T' h') :=
  (f.pullback_hom η θ ξ g S T h).symm.trans (f.pullback_hom η θ ξ g S T' h')

/-! ## Changing test levels on the same finite stages -/

/-- Changing the presentation of a stage retains its original comodule and
therefore gives its presentation at the new test level. -/
@[simp] theorem changeTestLevel_subcomoduleRepresentation (S : X.Subcomodule) :
    changeTestLevel.{u, a, v, t, s} (subcomoduleRepresentation S) =
      subcomoduleRepresentation.{u, a, v, s} S := by
  apply toRightComodule_injective
  simp only [changeTestLevel_toRightComodule, subcomoduleRepresentation_toRightComodule]

/-- Genuine stock-lift restriction of a stage is its presentation at the
smaller test level, on the same original subtype. -/
@[simp] theorem restrictTestLevel_subcomoduleRepresentation (S : X.Subcomodule) :
    restrictTestLevel.{u, a, v, t, s}
        (subcomoduleRepresentation.{u, a, v, max t s} S) =
      subcomoduleRepresentation.{u, a, v, t} S := by
  rw [restrictTestLevel_eq_changeTestLevel, changeTestLevel_subcomoduleRepresentation]

/-- Universe transport of the canonical transition retains exactly the stock
submodule inclusion as its underlying map. -/
theorem changeTestLevel_subcomoduleInclusion_toLinearMap {S T : X.Subcomodule}
    (h : S ≤ T) :
    (changeTestLevelHom.{u, a, v, v, t, s}
      (subcomoduleRepresentation S) (subcomoduleRepresentation T)
      (subcomoduleInclusion h)).toLinearMap = Submodule.inclusion h := rfl

/-- Universe transport of the ambient stage inclusion retains exactly the
original subtype map, with unchanged scalar extensions. -/
theorem changeTestLevel_subcomoduleSubtype_toLinearMap
    (S : η.toRightComodule.Subcomodule) :
    (changeTestLevelHom.{u, a, v, v, t, s}
      (subcomoduleRepresentation S) η (η.subcomoduleSubtype S)).toLinearMap =
      S.toSubmodule.subtype := rfl

/-- Stage evaluation is independent of the tester presentation at every
independently sized algebra. -/
theorem subcomoduleRepresentation_evaluate_testLevel (S : X.Subcomodule)
    {R : Type r} [CommRing R] [Algebra K R] (g : C →ₐ[K] R) :
    (subcomoduleRepresentation.{u, a, v, t} S).evaluate g =
      (subcomoduleRepresentation.{u, a, v, s} S).evaluate g := by
  change (ofRightComodule.{u, a, v, t} S.comodule).toRightComodule.evaluate g.toLinearMap =
    (ofRightComodule.{u, a, v, s} S.comodule).toRightComodule.evaluate g.toLinearMap
  rw [toRightComodule_ofRightComodule, toRightComodule_ofRightComodule]

namespace FiniteCompatibleFamily

variable {η θ ξ}

private theorem castComoduleFamily_hom_toLinearMap
    {Y Y' : Coalgebra.RightComodule K C W} (h : Y = Y')
    (f : Coalgebra.RightComodule.Subcomodule.CompatibleFamily X.finiteSubcomodules Y)
    (S : X.finiteSubcomodules) :
    ((Eq.mp (congrArg (fun Z : Coalgebra.RightComodule K C W ↦
      Coalgebra.RightComodule.Subcomodule.CompatibleFamily X.finiteSubcomodules Z) h)
        f).hom S).toLinearMap = (f.hom S).toLinearMap := by
  cases h
  rfl

/-- Change the test level of a whole family, on precisely the same finite
subcomodules and subspace subtypes. No reindexing choices are made. -/
def changeTestLevel (f : FiniteCompatibleFamily X θ) :
    FiniteCompatibleFamily X (PointRepresentation.changeTestLevel.{u, a, w, t, s} θ) :=
  ofComoduleFamily
    (Eq.mp (congrArg (fun Y : Coalgebra.RightComodule K C W ↦
      Coalgebra.RightComodule.Subcomodule.CompatibleFamily X.finiteSubcomodules Y)
        (changeTestLevel_toRightComodule θ).symm) f.toComoduleFamily)

/-- All stage maps retain their original linear-map values. -/
@[simp] theorem changeTestLevel_hom_toLinearMap (f : FiniteCompatibleFamily X θ)
    (S : X.finiteSubcomodules) :
    ((changeTestLevel.{u, a, v, w, t, s} f).hom S).toLinearMap =
      (f.hom S).toLinearMap := by
  calc
    _ = ((Eq.mp (congrArg (fun Y : Coalgebra.RightComodule K C W ↦
        Coalgebra.RightComodule.Subcomodule.CompatibleFamily X.finiteSubcomodules Y)
          (changeTestLevel_toRightComodule.{u, a, w, t, s} θ).symm)
            f.toComoduleFamily).hom S).toLinearMap :=
      ofComoduleFamily_hom_toLinearMap.{u, a, v, w, s}
        (X := X) (θ := PointRepresentation.changeTestLevel.{u, a, w, t, s} θ) _ S
    _ = (f.toComoduleFamily.hom S).toLinearMap :=
      castComoduleFamily_hom_toLinearMap.{u, a, v, w}
        (X := X) (Y := θ.toRightComodule)
        (Y' := (PointRepresentation.changeTestLevel.{u, a, w, t, s} θ).toRightComodule)
        (changeTestLevel_toRightComodule.{u, a, w, t, s} θ).symm f.toComoduleFamily S
    _ = _ := toComoduleFamily_hom_toLinearMap.{u, a, v, w, t} (X := X) (θ := θ) f S

/-- Component transport agrees with the existing Hom universe transport on
underlying maps; its source presentation is identified by the stage-value law. -/
theorem changeTestLevel_hom_readback (f : FiniteCompatibleFamily X θ)
    (S : X.finiteSubcomodules) :
    ((changeTestLevel.{u, a, v, w, t, s} f).hom S).toLinearMap =
      (changeTestLevelHom.{u, a, v, w, t, s}
        (subcomoduleRepresentation S.val) θ (f.hom S)).toLinearMap := by
  rw [changeTestLevel_hom_toLinearMap, changeTestLevelHom_toLinearMap]

private theorem heq_of_hom_toLinearMap_eq
    {θ₁ θ₂ : PointRepresentation.{u, a, w, s} K C W} (hθ : θ₁ = θ₂)
    (f : FiniteCompatibleFamily X θ₁) (g : FiniteCompatibleFamily X θ₂)
    (hm : ∀ S, (f.hom S).toLinearMap = (g.hom S).toLinearMap) : HEq f g := by
  subst θ₂
  apply heq_of_eq
  apply ext
  intro S
  exact PointHom.toLinearMap_injective (hm S)

/-- At the same test level the entire family value is unchanged, after the
canonical equality of its target presentation. -/
theorem changeTestLevel_self (f : FiniteCompatibleFamily X θ) :
    HEq (changeTestLevel.{u, a, v, w, t, t} f) f :=
  heq_of_hom_toLinearMap_eq
    (PointRepresentation.changeTestLevel_self.{u, a, w, t} θ) _ _
    (fun S ↦ changeTestLevel_hom_toLinearMap.{u, a, v, w, t, t} f S)

/-- Successive changes agree as family values on the same stage index, after
the canonical target equality. -/
theorem changeTestLevel_trans (f : FiniteCompatibleFamily X θ) :
    HEq (changeTestLevel.{u, a, v, w, s, r}
        (changeTestLevel.{u, a, v, w, t, s} f))
      (changeTestLevel.{u, a, v, w, t, r} f) :=
  heq_of_hom_toLinearMap_eq
    (PointRepresentation.changeTestLevel_trans.{u, a, w, t, s, r} θ) _ _
    (fun _ ↦ by simp only [changeTestLevel_hom_toLinearMap])

/-- A change to another test level and back returns the original whole family. -/
theorem changeTestLevel_inverse (f : FiniteCompatibleFamily X θ) :
    HEq (changeTestLevel.{u, a, v, w, s, t}
        (changeTestLevel.{u, a, v, w, t, s} f)) f :=
  heq_of_hom_toLinearMap_eq
    (PointRepresentation.changeTestLevel_inverse.{u, a, w, t, s} θ) _ _
    (fun _ ↦ by simp only [changeTestLevel_hom_toLinearMap])

/-- Whole-family transport respects target morphisms. -/
theorem changeTestLevel_postcomp (f : FiniteCompatibleFamily X θ) (g : PointHom θ ξ) :
    changeTestLevel.{u, a, v, z, t, s} (f.postcomp g) =
      (changeTestLevel.{u, a, v, w, t, s} f).postcomp
        (changeTestLevelHom.{u, a, w, z, t, s} θ ξ g) := by
  apply ext
  intro S
  apply PointHom.toLinearMap_injective
  simp only [changeTestLevel_hom_toLinearMap, postcomp_hom,
    PointHom.comp_toLinearMap, changeTestLevelHom_toLinearMap]

/-- Glue a fixed-stage family in the canonical presentation of its ambient
comodule. The only gluing operation is the existing colinear glue. -/
def gluePresentation (f : FiniteCompatibleFamily X θ) :
    PointHom (ofRightComodule.{u, a, v, t} X) θ :=
  (pointHomEquiv _ _).symm
    { toLinearMap := (Coalgebra.RightComodule.glueFiniteDimensional
        f.toComoduleFamily).toLinearMap
      colinear := by
        rw [toRightComodule_ofRightComodule]
        exact (Coalgebra.RightComodule.glueFiniteDimensional f.toComoduleFamily).colinear }

@[simp] theorem gluePresentation_apply (f : FiniteCompatibleFamily X θ)
    (S : X.finiteSubcomodules) (x : S.val.toSubmodule) :
    f.gluePresentation.toLinearMap (x : V) = (f.hom S).toLinearMap x :=
  Coalgebra.RightComodule.glueFiniteDimensional_apply f.toComoduleFamily S x

/-- Restrict a morphism in the canonical ambient presentation to the same fixed
stage indices. -/
def restrictPresentation (f : PointHom (ofRightComodule.{u, a, v, t} X) θ) :
    FiniteCompatibleFamily X θ :=
  ofComoduleFamily
    (Coalgebra.RightComodule.Subcomodule.CompatibleFamily.restrict X.finiteSubcomodules
      { toLinearMap := f.toLinearMap
        colinear := by
          simpa only [toRightComodule_ofRightComodule] using f.colinear })

@[simp] theorem restrictPresentation_hom_toLinearMap
    (f : PointHom (ofRightComodule.{u, a, v, t} X) θ) (S : X.finiteSubcomodules) :
    ((restrictPresentation f).hom S).toLinearMap =
      f.toLinearMap.comp S.val.toSubmodule.subtype := rfl

/-- Restriction reads back the whole fixed-stage family after gluing. -/
@[simp] theorem restrictPresentation_glue (f : FiniteCompatibleFamily X θ) :
    restrictPresentation f.gluePresentation = f := by
  apply ext
  intro S
  apply PointHom.ext
  intro x
  exact gluePresentation_apply f S x

/-- Gluing reconstructs every global map in the canonical ambient presentation. -/
@[simp] theorem gluePresentation_restrict
    (f : PointHom (ofRightComodule.{u, a, v, t} X) θ) :
    (restrictPresentation f).gluePresentation = f := by
  apply PointHom.ext
  intro x
  obtain ⟨S, hx⟩ := X.finiteSubcomodules_cover x
  exact gluePresentation_apply (restrictPresentation f) S ⟨x, hx⟩

/-- Changing test levels retains the entire underlying ambient glued map,
proved on the original covering stages. -/
theorem changeTestLevel_gluePresentation_toLinearMap (f : FiniteCompatibleFamily X θ) :
    (changeTestLevel.{u, a, v, w, t, s} f).gluePresentation.toLinearMap =
      f.gluePresentation.toLinearMap := by
  apply LinearMap.ext
  intro x
  obtain ⟨S, hx⟩ := X.finiteSubcomodules_cover x
  exact (gluePresentation_apply (changeTestLevel.{u, a, v, w, t, s} f) S ⟨x, hx⟩).trans
    ((LinearMap.congr_fun
      (changeTestLevel_hom_toLinearMap.{u, a, v, w, t, s} f S) ⟨x, hx⟩).trans
      (gluePresentation_apply f S ⟨x, hx⟩).symm)

/-- Restrict a whole family along the stock algebra-universe lift. Its target
is the genuine stock restriction, and its stage maps retain the same linear data. -/
def restrictTestLevel (θ : PointRepresentation.{u, a, w, max t s} K C W)
    (f : FiniteCompatibleFamily X θ) :
    FiniteCompatibleFamily X (PointRepresentation.restrictTestLevel.{u, a, w, t, s} θ) :=
  ofComoduleFamily
    (Eq.mp (congrArg (fun Y : Coalgebra.RightComodule K C W ↦
      Coalgebra.RightComodule.Subcomodule.CompatibleFamily X.finiteSubcomodules Y)
        (restrictTestLevel_toRightComodule θ).symm) f.toComoduleFamily)

@[simp] theorem restrictTestLevel_hom_toLinearMap
    (θ : PointRepresentation.{u, a, w, max t s} K C W)
    (f : FiniteCompatibleFamily X θ) (S : X.finiteSubcomodules) :
    ((restrictTestLevel.{u, a, v, w, t, s} θ f).hom S).toLinearMap =
      (f.hom S).toLinearMap := by
  calc
    _ = ((Eq.mp (congrArg (fun Y : Coalgebra.RightComodule K C W ↦
        Coalgebra.RightComodule.Subcomodule.CompatibleFamily X.finiteSubcomodules Y)
          (restrictTestLevel_toRightComodule.{u, a, w, t, s} θ).symm)
            f.toComoduleFamily).hom S).toLinearMap :=
      ofComoduleFamily_hom_toLinearMap.{u, a, v, w, t}
        (X := X) (θ := PointRepresentation.restrictTestLevel.{u, a, w, t, s} θ) _ S
    _ = (f.toComoduleFamily.hom S).toLinearMap :=
      castComoduleFamily_hom_toLinearMap.{u, a, v, w}
        (X := X) (Y := θ.toRightComodule)
        (Y' := (PointRepresentation.restrictTestLevel.{u, a, w, t, s} θ).toRightComodule)
        (restrictTestLevel_toRightComodule.{u, a, w, t, s} θ).symm f.toComoduleFamily S
    _ = _ :=
      toComoduleFamily_hom_toLinearMap.{u, a, v, w, max t s} (X := X) (θ := θ) f S

/-- Stock-lift restriction agrees with canonical family transport, as family
values after the proved equality of their target presentations. -/
theorem restrictTestLevel_eq_changeTestLevel
    (θ : PointRepresentation.{u, a, w, max t s} K C W)
    (f : FiniteCompatibleFamily X θ) :
    HEq (restrictTestLevel.{u, a, v, w, t, s} θ f)
      (changeTestLevel.{u, a, v, w, max t s, t} f) :=
  heq_of_hom_toLinearMap_eq
    (PointRepresentation.restrictTestLevel_eq_changeTestLevel.{u, a, w, t, s} θ)
    _ _ (fun _ ↦ by
      simp only [restrictTestLevel_hom_toLinearMap, changeTestLevel_hom_toLinearMap])

/-- Extension to a common maximum followed by genuine stock restriction gives
the same whole family as direct tester change, on the same original stages. -/
theorem restrictTestLevel_commonMax (f : FiniteCompatibleFamily X θ) :
    HEq (restrictTestLevel.{u, a, v, w, s, r}
        (PointRepresentation.changeTestLevel.{u, a, w, t, max s r} θ)
        (changeTestLevel.{u, a, v, w, t, max s r} f))
      (changeTestLevel.{u, a, v, w, t, s} f) :=
  heq_of_hom_toLinearMap_eq
    (PointRepresentation.restrictTestLevel_commonMax.{u, a, w, s, r, t} θ)
    _ _ (fun _ ↦ by
      simp only [restrictTestLevel_hom_toLinearMap, changeTestLevel_hom_toLinearMap])

/-- Genuine stock restriction also retains the whole ambient glued linear map. -/
theorem restrictTestLevel_gluePresentation_toLinearMap
    (θ : PointRepresentation.{u, a, w, max t s} K C W)
    (f : FiniteCompatibleFamily X θ) :
    (restrictTestLevel.{u, a, v, w, t, s} θ f).gluePresentation.toLinearMap =
      f.gluePresentation.toLinearMap := by
  apply LinearMap.ext
  intro x
  obtain ⟨S, hx⟩ := X.finiteSubcomodules_cover x
  exact (gluePresentation_apply (restrictTestLevel.{u, a, v, w, t, s} θ f) S ⟨x, hx⟩).trans
    ((LinearMap.congr_fun
      (restrictTestLevel_hom_toLinearMap.{u, a, v, w, t, s} θ f S) ⟨x, hx⟩).trans
      (gluePresentation_apply f S ⟨x, hx⟩).symm)

/-- Gluing after extension to a common maximum and stock restriction retains
exactly the original ambient linear map. -/
theorem commonMax_gluePresentation_toLinearMap (f : FiniteCompatibleFamily X θ) :
    (restrictTestLevel.{u, a, v, w, s, r}
        (PointRepresentation.changeTestLevel.{u, a, w, t, max s r} θ)
        (changeTestLevel.{u, a, v, w, t, max s r} f)).gluePresentation.toLinearMap =
      f.gluePresentation.toLinearMap :=
  (restrictTestLevel_gluePresentation_toLinearMap _ _).trans
    (changeTestLevel_gluePresentation_toLinearMap f)

end FiniteCompatibleFamily

/-- Transporting an original ambient glued morphism to another tester level
is exactly gluing the transported family on the same original stages. This is
an equality of bundled point morphism values. -/
theorem changeTestLevelHom_glueFinite (f : FiniteCompatibleFamily η.toRightComodule θ) :
    changeTestLevelHom.{u, a, v, w, t, s} η θ (glueFinite η θ f) =
      (FiniteCompatibleFamily.changeTestLevel.{u, a, v, w, t, s} f).gluePresentation := by
  apply PointHom.toLinearMap_injective
  exact (FiniteCompatibleFamily.changeTestLevel_gluePresentation_toLinearMap f).symm

/-- Transporting the restrictions of an original ambient morphism reads back
its restrictions at the new level on the same finite subspaces. -/
theorem changeTestLevel_restrictFinite (f : PointHom η θ) :
    FiniteCompatibleFamily.changeTestLevel.{u, a, v, w, t, s}
        (restrictFinite η θ f) =
      FiniteCompatibleFamily.restrictPresentation
        (changeTestLevelHom.{u, a, v, w, t, s} η θ f) := by
  apply FiniteCompatibleFamily.ext
  intro S
  apply PointHom.toLinearMap_injective
  -- Fix the canonical source and new tester before applying the restriction readback.
  have hrestrict := FiniteCompatibleFamily.restrictPresentation_hom_toLinearMap.{u, a, v, w, s}
    (X := η.toRightComodule)
    (θ := PointRepresentation.changeTestLevel.{u, a, w, t, s} θ)
    (changeTestLevelHom.{u, a, v, w, t, s} η θ f) S
  calc
    _ = f.toLinearMap.comp S.val.toSubmodule.subtype := by
      simp only [FiniteCompatibleFamily.changeTestLevel_hom_toLinearMap,
        restrictFinite_hom, PointHom.comp_toLinearMap, subcomoduleSubtype_toLinearMap]
    _ = (changeTestLevelHom.{u, a, v, w, t, s} η θ f).toLinearMap.comp
        S.val.toSubmodule.subtype :=
      congrArg (fun l : V →ₗ[K] W ↦ l.comp S.val.toSubmodule.subtype)
        (changeTestLevelHom_toLinearMap.{u, a, v, w, t, s} η θ f).symm
    _ = _ := hrestrict.symm

end AlgebraicGeometry.PointRepresentation
