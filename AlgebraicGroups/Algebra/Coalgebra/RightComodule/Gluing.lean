/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.RightComodule
public import Mathlib.Algebra.Colimit.Module
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Gluing colinear maps on covering subcomodules

For a directed covering set `S` of subcomodules of a specified right comodule
`X`, restriction identifies morphisms from `X` to any right comodule `Y` with
compatible families of morphisms from the members of `S` to `Y`.
`Subcomodule.CompatibleFamily.glue` constructs the bundled colinear map, and
`Subcomodule.homEquivCompatibleFamily` gives the two inverse constructions.
Gluing commutes with postcomposition.

The linear construction reuses Mathlib's `Module.DirectLimit.lift`. The
canonical map from that direct limit to the original module is bijective:
injectivity is `Module.DirectLimit.lift_injective`, and surjectivity is the
covering hypothesis. Colinearity is then checked on the covering stages using
the original subtype inclusions and their tensor maps. No new union carrier is
introduced. Flatness is imposed only on the coalgebra, at the boundary where
canonical morphisms between specified subcomodules are available.

The module-finite subcomodules contain zero, are closed under binary joins,
and cover the ambient module when the coalgebra is projective. Consequently
`RightComodule.glueFinite` applies without a projectivity hypothesis on the
ambient module. Over a field, `RightComodule.glueFiniteDimensional` has no
flatness, projectivity, or finite-dimensionality assumptions on the ambient
module or coalgebra.

## References

* Mathlib's module direct limits (Kenny Lau, Chris Hughes, and Jujian Zhang),
  submodule inclusions, and finite-generation API.
* M. E. Sweedler, *Hopf Algebras*, W. A. Benjamin, 1969, for finite-subcomodule
  containment, reused through `RightComodule.exists_fg_subcomodule_of_finite`.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 4(c), Proposition 4.7 and
  Corollary 4.8, for the finite-dimensional filtered-union setting. The gluing
  statement here applies to arbitrary coalgebras and arbitrary directed covers.
-/

@[expose] public section

universe u v w z t

namespace Coalgebra.RightComodule

variable {R : Type u} {C : Type v} {M : Type w} {N : Type z} {P : Type t}
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
variable [AddCommMonoid P] [Module R P]
variable {X : RightComodule R C M} {Y : RightComodule R C N} {Z : RightComodule R C P}

namespace Subcomodule

variable (S : Set X.Subcomodule)

/-- Morphisms on a covering family determine a morphism on the original comodule.
This extensionality statement itself requires neither directedness nor flatness. -/
theorem hom_ext_of_cover (hcover : ∀ m : M, ∃ U : S, m ∈ U.val)
    {f g : RightComoduleHom X Y}
    (h : ∀ U : S, f.comp U.val.subtype = g.comp U.val.subtype) : f = g := by
  apply RightComoduleHom.ext
  intro m
  obtain ⟨U, hm⟩ := hcover m
  exact congrArg (fun k : RightComoduleHom U.val.comodule Y ↦ k ⟨m, hm⟩) (h U)

variable [Module.Flat R C]

/-- A family of colinear maps agreeing under the canonical subcomodule inclusions. -/
structure CompatibleFamily (Y : RightComodule R C N) where
  /-- The colinear map on each member of the family. -/
  hom (U : S) : RightComoduleHom U.val.comodule Y
  /-- Agreement under each canonical inclusion between members of the family. -/
  compatible (U V : S) (h : U ≤ V) :
    (hom V).comp (inclusion h) = hom U

namespace CompatibleFamily

variable {S}

/-- Compatible families are determined by their component morphisms. -/
@[ext] theorem ext {f g : CompatibleFamily S Y}
    (h : ∀ U, f.hom U = g.hom U) : f = g := by
  cases f with
  | mk f hf =>
    cases g with
    | mk g hg =>
      have hfg : f = g := funext h
      subst g
      rfl

/-- Restrict a morphism on the original comodule to every covering stage. -/
def restrict (S : Set X.Subcomodule) (f : RightComoduleHom X Y) :
    CompatibleFamily S Y where
  hom U := f.comp U.val.subtype
  compatible U V h := by
    rw [RightComoduleHom.comp_assoc, subtype_comp_inclusion]

@[simp] theorem restrict_hom (f : RightComoduleHom X Y) (U : S) :
    (restrict S f).hom U = f.comp U.val.subtype := rfl

/-- Postcompose every member of a compatible family with a colinear map. -/
def postcomp (f : CompatibleFamily S Y) (g : RightComoduleHom Y Z) :
    CompatibleFamily S Z where
  hom U := g.comp (f.hom U)
  compatible U V h := by
    rw [RightComoduleHom.comp_assoc, f.compatible U V h]

@[simp] theorem postcomp_hom (f : CompatibleFamily S Y)
    (g : RightComoduleHom Y Z) (U : S) :
    (f.postcomp g).hom U = g.comp (f.hom U) := rfl

@[simp] theorem postcomp_id (f : CompatibleFamily S Y) :
    f.postcomp (RightComoduleHom.id Y) = f := by
  apply ext
  intro U
  exact RightComoduleHom.id_comp _

/-- Postcomposition of compatible families respects composition. -/
@[simp] theorem postcomp_comp {Q : Type*} [AddCommMonoid Q] [Module R Q]
    {T : RightComodule R C Q} (f : CompatibleFamily S Y)
    (g : RightComoduleHom Y Z) (h : RightComoduleHom Z T) :
    (f.postcomp g).postcomp h = f.postcomp (h.comp g) := by
  apply ext
  intro U
  exact (RightComoduleHom.comp_assoc h g (f.hom U)).symm

/-- Restriction commutes with postcomposition. -/
@[simp] theorem restrict_postcomp (f : RightComoduleHom X Y)
    (g : RightComoduleHom Y Z) :
    restrict S (g.comp f) = (restrict S f).postcomp g := by
  apply ext
  intro U
  exact RightComoduleHom.comp_assoc g f U.val.subtype

/-- The transition maps are precisely the underlying stock submodule inclusions. -/
private abbrev transition (U V : S) (h : U ≤ V) :
    U.val.toSubmodule →ₗ[R] V.val.toSubmodule :=
  (inclusion h).toLinearMap

private noncomputable def coverMap [DecidableEq S] :
    Module.DirectLimit (fun U : S ↦ U.val.toSubmodule) (transition (S := S)) →ₗ[R] M :=
  Module.DirectLimit.lift R S (fun U : S ↦ U.val.toSubmodule) (transition (S := S))
    (fun U ↦ U.val.subtype.toLinearMap) (fun _ _ _ _ ↦ rfl)

private theorem coverMap_of [DecidableEq S] (U : S) (m : U.val.toSubmodule) :
    coverMap (S := S)
      (Module.DirectLimit.of R S (fun U : S ↦ U.val.toSubmodule)
        (transition (S := S)) U m) = (m : M) :=
  Module.DirectLimit.lift_of (fun U : S ↦ U.val.subtype.toLinearMap)
    (fun _ _ _ _ ↦ rfl) m

private noncomputable def coverEquiv [DecidableEq S]
    (hS : DirectedOn (· ≤ ·) S) (hcover : ∀ m : M, ∃ U : S, m ∈ U.val) :
    Module.DirectLimit (fun U : S ↦ U.val.toSubmodule) (transition (S := S)) ≃ₗ[R] M := by
  letI : IsDirectedOrder S := hS.isDirectedOrder
  refine LinearEquiv.ofBijective (coverMap (S := S)) ⟨?_, ?_⟩
  · exact Module.DirectLimit.lift_injective _ _ (fun U ↦ U.val.subtype_injective)
  · intro m
    obtain ⟨U, hm⟩ := hcover m
    exact ⟨Module.DirectLimit.of R S (fun U : S ↦ U.val.toSubmodule)
      (transition (S := S)) U ⟨m, hm⟩, coverMap_of U ⟨m, hm⟩⟩

private theorem coverEquiv_of [DecidableEq S]
    (hS : DirectedOn (· ≤ ·) S) (hcover : ∀ m : M, ∃ U : S, m ∈ U.val)
    (U : S) (m : U.val.toSubmodule) :
    coverEquiv hS hcover
      (Module.DirectLimit.of R S (fun U : S ↦ U.val.toSubmodule)
        (transition (S := S)) U m) = (m : M) :=
  coverMap_of U m

private theorem compatible_linear (f : CompatibleFamily S Y) (U V : S)
    (h : U ≤ V) (m : U.val.toSubmodule) :
    (f.hom V).toLinearMap (transition U V h m) = (f.hom U).toLinearMap m :=
  congrArg (fun k : RightComoduleHom U.val.comodule Y ↦ k m) (f.compatible U V h)

private noncomputable def glueLinear (hS : DirectedOn (· ≤ ·) S)
    (hcover : ∀ m : M, ∃ U : S, m ∈ U.val) (f : CompatibleFamily S Y) : M →ₗ[R] N := by
  classical
  exact (Module.DirectLimit.lift R S (fun U : S ↦ U.val.toSubmodule)
    (transition (S := S)) (fun U ↦ (f.hom U).toLinearMap) (compatible_linear f)).comp
      (coverEquiv hS hcover).symm.toLinearMap

private theorem glueLinear_apply (hS : DirectedOn (· ≤ ·) S)
    (hcover : ∀ m : M, ∃ U : S, m ∈ U.val) (f : CompatibleFamily S Y)
    (U : S) (m : U.val.toSubmodule) :
    glueLinear hS hcover f (m : M) = f.hom U m := by
  classical
  have hm : (coverEquiv hS hcover).symm (m : M) =
      Module.DirectLimit.of R S (fun U : S ↦ U.val.toSubmodule)
        (transition (S := S)) U m := by
    apply (coverEquiv hS hcover).injective
    rw [LinearEquiv.apply_symm_apply, coverEquiv_of]
  dsimp only [glueLinear, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [hm]
  exact Module.DirectLimit.lift_of (fun U : S ↦ (f.hom U).toLinearMap)
    (compatible_linear f) m

/-- Glue a compatible family on a directed covering set of subcomodules.
The result is a morphism on the same specified ambient comodule. -/
noncomputable def glue (hS : DirectedOn (· ≤ ·) S)
    (hcover : ∀ m : M, ∃ U : S, m ∈ U.val) (f : CompatibleFamily S Y) :
    RightComoduleHom X Y where
  toLinearMap := private glueLinear hS hcover f
  colinear := by
    apply LinearMap.ext
    intro m
    obtain ⟨U, hm⟩ := hcover m
    let x : U.val.toSubmodule := ⟨m, hm⟩
    have hrest : glueLinear hS hcover f ∘ₗ U.val.subtype.toLinearMap =
        (f.hom U).toLinearMap := by
      apply LinearMap.ext
      intro x
      exact glueLinear_apply hS hcover f U x
    change Y.coaction (glueLinear hS hcover f m) =
      (glueLinear hS hcover f).rTensor C (X.coaction m)
    calc
      Y.coaction (glueLinear hS hcover f m) = Y.coaction (f.hom U x) :=
        congrArg Y.coaction (glueLinear_apply hS hcover f U x)
      _ = (f.hom U).toLinearMap.rTensor C (U.val.comodule.coaction x) :=
        (f.hom U).colinear_apply x
      _ = (glueLinear hS hcover f).rTensor C
          (U.val.subtype.toLinearMap.rTensor C (U.val.comodule.coaction x)) := by
        rw [← LinearMap.rTensor_comp_apply, hrest]
      _ = (glueLinear hS hcover f).rTensor C (X.coaction m) :=
        congrArg ((glueLinear hS hcover f).rTensor C)
          (U.val.subtype.colinear_apply x).symm

/-- Evaluation of the glued map on a member of any covering stage. -/
@[simp] theorem glue_apply (hS : DirectedOn (· ≤ ·) S)
    (hcover : ∀ m : M, ∃ U : S, m ∈ U.val) (f : CompatibleFamily S Y)
    (U : S) (m : U.val.toSubmodule) :
    f.glue hS hcover (m : M) = f.hom U m :=
  glueLinear_apply hS hcover f U m

/-- Evaluate the glued map using any stage containing the given ambient element. -/
theorem glue_apply_of_mem (hS : DirectedOn (· ≤ ·) S)
    (hcover : ∀ m : M, ∃ U : S, m ∈ U.val) (f : CompatibleFamily S Y)
    (U : S) (m : M) (hm : m ∈ U.val) :
    f.glue hS hcover m = f.hom U ⟨m, hm⟩ :=
  glue_apply hS hcover f U ⟨m, hm⟩

/-- The glued map restricts to the prescribed component as a bundled colinear map. -/
@[simp] theorem glue_comp_subtype (hS : DirectedOn (· ≤ ·) S)
    (hcover : ∀ m : M, ∃ U : S, m ∈ U.val) (f : CompatibleFamily S Y) (U : S) :
    (f.glue hS hcover).comp U.val.subtype = f.hom U := by
  apply RightComoduleHom.ext
  intro m
  exact glue_apply hS hcover f U m

/-- Restriction reads back the entire compatible family. -/
@[simp] theorem restrict_glue (hS : DirectedOn (· ≤ ·) S)
    (hcover : ∀ m : M, ∃ U : S, m ∈ U.val) (f : CompatibleFamily S Y) :
    restrict S (f.glue hS hcover) = f := by
  apply ext
  exact glue_comp_subtype hS hcover f

/-- The prescribed restrictions characterize the glued colinear map uniquely. -/
theorem glue_unique (hS : DirectedOn (· ≤ ·) S)
    (hcover : ∀ m : M, ∃ U : S, m ∈ U.val) (f : CompatibleFamily S Y)
    (g : RightComoduleHom X Y)
    (hg : ∀ U : S, g.comp U.val.subtype = f.hom U) : g = f.glue hS hcover := by
  apply hom_ext_of_cover S hcover
  intro U
  rw [hg U, glue_comp_subtype]

/-- A compatible family has exactly one colinear extension to the ambient comodule. -/
theorem existsUnique_glue (hS : DirectedOn (· ≤ ·) S)
    (hcover : ∀ m : M, ∃ U : S, m ∈ U.val) (f : CompatibleFamily S Y) :
    ∃! g : RightComoduleHom X Y, ∀ U : S, g.comp U.val.subtype = f.hom U :=
  ⟨f.glue hS hcover, glue_comp_subtype hS hcover f,
    fun g hg ↦ glue_unique hS hcover f g hg⟩

/-- Gluing the restrictions of a morphism reconstructs that morphism. -/
@[simp] theorem glue_restrict (hS : DirectedOn (· ≤ ·) S)
    (hcover : ∀ m : M, ∃ U : S, m ∈ U.val) (g : RightComoduleHom X Y) :
    (restrict S g).glue hS hcover = g :=
  (glue_unique hS hcover (restrict S g) g (fun _ ↦ rfl)).symm

/-- Gluing is natural in the target comodule. -/
@[simp] theorem glue_postcomp (hS : DirectedOn (· ≤ ·) S)
    (hcover : ∀ m : M, ∃ U : S, m ∈ U.val) (f : CompatibleFamily S Y)
    (g : RightComoduleHom Y Z) :
    (f.postcomp g).glue hS hcover = g.comp (f.glue hS hcover) := by
  symm
  apply glue_unique hS hcover (f.postcomp g)
  intro U
  rw [RightComoduleHom.comp_assoc, glue_comp_subtype, postcomp_hom]

end CompatibleFamily

/-- The universal property of a directed covering family of subcomodules,
with restriction and gluing as mutually inverse data. -/
noncomputable def homEquivCompatibleFamily (hS : DirectedOn (· ≤ ·) S)
    (hcover : ∀ m : M, ∃ U : S, m ∈ U.val) :
    RightComoduleHom X Y ≃ CompatibleFamily S Y where
  toFun := CompatibleFamily.restrict S
  invFun := CompatibleFamily.glue hS hcover
  left_inv := CompatibleFamily.glue_restrict hS hcover
  right_inv := CompatibleFamily.restrict_glue hS hcover

@[simp] theorem homEquivCompatibleFamily_apply (hS : DirectedOn (· ≤ ·) S)
    (hcover : ∀ m : M, ∃ U : S, m ∈ U.val) (f : RightComoduleHom X Y) :
    homEquivCompatibleFamily S hS hcover f = CompatibleFamily.restrict S f := rfl

@[simp] theorem homEquivCompatibleFamily_symm_apply (hS : DirectedOn (· ≤ ·) S)
    (hcover : ∀ m : M, ∃ U : S, m ∈ U.val) (f : CompatibleFamily S Y) :
    (homEquivCompatibleFamily S hS hcover).symm f = f.glue hS hcover := rfl

end Subcomodule

open Subcomodule

/-- The set of subcomodules with module-finite underlying subtype. -/
def finiteSubcomodules (X : RightComodule R C M) : Set X.Subcomodule :=
  {U | Module.Finite R U.toSubmodule}

@[simp] theorem mem_finiteSubcomodules (U : X.Subcomodule) :
    U ∈ X.finiteSubcomodules ↔ Module.Finite R U.toSubmodule := Iff.rfl

/-- Finite generation of the underlying submodule is equivalent to finiteness
of its module subtype, with its canonical scalar structure. -/
theorem mem_finiteSubcomodules_iff_fg (U : X.Subcomodule) :
    U ∈ X.finiteSubcomodules ↔ U.toSubmodule.FG := Module.Finite.iff_fg

/-- The canonical zero subcomodule is module-finite. -/
theorem bot_mem_finiteSubcomodules (X : RightComodule R C M) :
    (⊥ : X.Subcomodule) ∈ X.finiteSubcomodules :=
  Module.Finite.iff_fg.mpr Submodule.fg_bot

/-- The module-finite stage system is nonempty, witnessed by the zero subcomodule. -/
theorem finiteSubcomodules_nonempty (X : RightComodule R C M) :
    X.finiteSubcomodules.Nonempty :=
  ⟨⊥, X.bot_mem_finiteSubcomodules⟩

/-- Binary joins preserve module-finiteness; the join has the induced coaction
on the ordinary submodule join. -/
theorem sup_mem_finiteSubcomodules [Module.Flat R C] {U V : X.Subcomodule}
    (hU : U ∈ X.finiteSubcomodules) (hV : V ∈ X.finiteSubcomodules) :
    U ⊔ V ∈ X.finiteSubcomodules :=
  Module.Finite.iff_fg.mpr
    ((Module.Finite.iff_fg.mp hU).sup (Module.Finite.iff_fg.mp hV))

/-- The module-finite subcomodules form a directed set, using their canonical
binary join. Projectivity is not needed for this closure assertion. -/
theorem directedOn_finiteSubcomodules [Module.Flat R C] (X : RightComodule R C M) :
    DirectedOn (· ≤ ·) X.finiteSubcomodules := by
  intro U hU V hV
  exact ⟨U ⊔ V, sup_mem_finiteSubcomodules hU hV, le_sup_left, le_sup_right⟩

/-- Every finite subset lies in a stage of the module-finite subcomodule system. -/
theorem finiteSubcomodules_contain_finite [Module.Projective R C]
    (X : RightComodule R C M) {s : Set M} (hs : s.Finite) :
    ∃ U : X.finiteSubcomodules, s ⊆ (U.val : Set M) := by
  obtain ⟨U, hsU, hfg⟩ := X.exists_fg_subcomodule_of_finite hs
  exact ⟨⟨U, Module.Finite.iff_fg.mpr hfg⟩, hsU⟩

/-- The module-finite subcomodules cover the original comodule. -/
theorem finiteSubcomodules_cover [Module.Projective R C] (X : RightComodule R C M)
    (m : M) : ∃ U : X.finiteSubcomodules, m ∈ U.val := by
  obtain ⟨U, hU⟩ := X.finiteSubcomodules_contain_finite (Set.finite_singleton m)
  exact ⟨U, hU (Set.mem_singleton m)⟩

section Projective

variable [Module.Projective R C]

/-- Glue any compatible family on all module-finite subcomodules to a colinear
map on the same ambient comodule. Only the coalgebra is assumed projective. -/
noncomputable def glueFinite (f : CompatibleFamily X.finiteSubcomodules Y) :
    RightComoduleHom X Y :=
  f.glue X.directedOn_finiteSubcomodules X.finiteSubcomodules_cover

@[simp] theorem glueFinite_apply (f : CompatibleFamily X.finiteSubcomodules Y)
    (U : X.finiteSubcomodules) (m : U.val.toSubmodule) :
    glueFinite f (m : M) = f.hom U m :=
  f.glue_apply X.directedOn_finiteSubcomodules X.finiteSubcomodules_cover U m

@[simp] theorem glueFinite_comp_subtype (f : CompatibleFamily X.finiteSubcomodules Y)
    (U : X.finiteSubcomodules) :
    (glueFinite f).comp U.val.subtype = f.hom U :=
  f.glue_comp_subtype X.directedOn_finiteSubcomodules X.finiteSubcomodules_cover U

/-- Equality of global colinear maps is determined by their finite-stage restrictions. -/
theorem hom_ext_finite {f g : RightComoduleHom X Y}
    (h : ∀ U : X.finiteSubcomodules, f.comp U.val.subtype = g.comp U.val.subtype) :
    f = g :=
  hom_ext_of_cover X.finiteSubcomodules X.finiteSubcomodules_cover h

/-- The finite-stage restrictions characterize the extension uniquely. -/
theorem glueFinite_unique (f : CompatibleFamily X.finiteSubcomodules Y)
    (g : RightComoduleHom X Y)
    (hg : ∀ U : X.finiteSubcomodules, g.comp U.val.subtype = f.hom U) :
    g = glueFinite f :=
  f.glue_unique X.directedOn_finiteSubcomodules X.finiteSubcomodules_cover g hg

/-- Restriction is an equivalence between global morphisms and compatible
families on module-finite subcomodules. -/
noncomputable def homEquivFiniteCompatibleFamily :
    RightComoduleHom X Y ≃ CompatibleFamily X.finiteSubcomodules Y :=
  homEquivCompatibleFamily X.finiteSubcomodules X.directedOn_finiteSubcomodules
    X.finiteSubcomodules_cover

@[simp] theorem restrict_glueFinite (f : CompatibleFamily X.finiteSubcomodules Y) :
    CompatibleFamily.restrict X.finiteSubcomodules (glueFinite f) = f :=
  f.restrict_glue X.directedOn_finiteSubcomodules X.finiteSubcomodules_cover

@[simp] theorem glueFinite_restrict (g : RightComoduleHom X Y) :
    glueFinite (CompatibleFamily.restrict X.finiteSubcomodules g) = g :=
  CompatibleFamily.glue_restrict X.directedOn_finiteSubcomodules X.finiteSubcomodules_cover g

/-- Finite-stage gluing commutes with every colinear map out of the target. -/
@[simp] theorem glueFinite_postcomp (f : CompatibleFamily X.finiteSubcomodules Y)
    (g : RightComoduleHom Y Z) :
    glueFinite (f.postcomp g) = g.comp (glueFinite f) :=
  f.glue_postcomp X.directedOn_finiteSubcomodules X.finiteSubcomodules_cover g

end Projective

section Field

variable {K : Type u} {D : Type v} {V : Type w} {W : Type z}
variable [Field K] [AddCommGroup D] [Module K D] [Coalgebra K D]
variable [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
variable {A : RightComodule K D V} {B : RightComodule K D W}

/-- Over a field, the module-finite stages are exactly the finite-dimensional
subcomodules, with the canonical module structure on each subtype. -/
theorem mem_finiteSubcomodules_iff_finiteDimensional (U : A.Subcomodule) :
    U ∈ A.finiteSubcomodules ↔ FiniteDimensional K U.toSubmodule := Iff.rfl

/-- Glue any compatible family on finite-dimensional subcomodules of an arbitrary
specified right comodule over a field. All vector spaces are projective, so no
additional flatness or projectivity assumption is needed. -/
noncomputable def glueFiniteDimensional
    (f : CompatibleFamily {U : A.Subcomodule | FiniteDimensional K U.toSubmodule} B) :
    RightComoduleHom A B := glueFinite f

/-- The glued map over a field has the prescribed restriction at every
finite-dimensional subcomodule. -/
@[simp] theorem glueFiniteDimensional_comp_subtype
    (f : CompatibleFamily {U : A.Subcomodule | FiniteDimensional K U.toSubmodule} B)
    (U : {U : A.Subcomodule // FiniteDimensional K U.toSubmodule}) :
    (glueFiniteDimensional f).comp U.val.subtype = f.hom U :=
  glueFinite_comp_subtype f U

/-- Every compatible finite-dimensional family into any target has exactly one
bundled colinear extension to the original, possibly infinite-dimensional comodule. -/
theorem existsUnique_glueFiniteDimensional
    (f : CompatibleFamily {U : A.Subcomodule | FiniteDimensional K U.toSubmodule} B) :
    ∃! g : RightComoduleHom A B,
      ∀ U : {U : A.Subcomodule // FiniteDimensional K U.toSubmodule},
        g.comp U.val.subtype = f.hom U :=
  f.existsUnique_glue A.directedOn_finiteSubcomodules A.finiteSubcomodules_cover

/-- Evaluation of the glued map over a field on a finite-dimensional stage. -/
@[simp] theorem glueFiniteDimensional_apply
    (f : CompatibleFamily {U : A.Subcomodule | FiniteDimensional K U.toSubmodule} B)
    (U : {U : A.Subcomodule // FiniteDimensional K U.toSubmodule})
    (m : U.val.toSubmodule) :
    glueFiniteDimensional f (m : V) = f.hom U m :=
  glueFinite_apply f U m

/-- Restriction reads back the complete finite-dimensional family. -/
@[simp] theorem restrict_glueFiniteDimensional
    (f : CompatibleFamily {U : A.Subcomodule | FiniteDimensional K U.toSubmodule} B) :
    CompatibleFamily.restrict A.finiteSubcomodules (glueFiniteDimensional f) = f :=
  restrict_glueFinite f

/-- Gluing the finite-dimensional restrictions reconstructs any global colinear map. -/
@[simp] theorem glueFiniteDimensional_restrict (g : RightComoduleHom A B) :
    glueFiniteDimensional (CompatibleFamily.restrict A.finiteSubcomodules g) = g :=
  glueFinite_restrict g

/-- Finite-dimensional-stage gluing is natural under colinear postcomposition
into an arbitrary target vector space. -/
@[simp] theorem glueFiniteDimensional_postcomp {Q : Type t}
    [AddCommGroup Q] [Module K Q] {T : RightComodule K D Q}
    (f : CompatibleFamily {U : A.Subcomodule | FiniteDimensional K U.toSubmodule} B)
    (g : RightComoduleHom B T) :
    glueFiniteDimensional (f.postcomp g) = g.comp (glueFiniteDimensional f) :=
  glueFinite_postcomp f g

end Field

end Coalgebra.RightComodule
