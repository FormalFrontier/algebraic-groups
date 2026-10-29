/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.RepresentationEquivalence
public import AlgebraicGroups.GroupScheme.RepresentationIntertwiner

/-!
# Invariant submodules of natural point representations

A submodule is invariant if every component operator preserves the image of its
original scalar-extended inclusion, on every tensor in that image. This condition
is equivalent to `Coalgebra.RightComodule.IsStable` for the same reconstructed
coaction. The converse is detected by the generic point over `ULift C`, followed
by coefficient descent and tensor commutation; no density of base-field points
is used. Stability also gives preservation under the canonical evaluated action
at every independently sized coefficient algebra.

When the coordinate algebra is flat over the base, the existing
`Coalgebra.RightComodule.Subcomodule.ofIsStable` supplies the coaction on the
original submodule subtype. Its natural point representation has the original
subtype inclusion as a bundled point intertwiner. Both the specified subtype
comodule and the point representation are uniquely determined by that inclusion.
The inclusion's scalar extension is always the stock `LinearMap.baseChange`.

## Implementation notes

The invariance criterion needs no flatness. Only construction and uniqueness of
the restricted subtype coaction use flatness of the coordinate algebra, which is
automatic over a field. There is no flatness or projectivity assumption on the
ambient module or the submodule, and no finite-dimensionality assumption.
At a general coefficient algebra the scalar-extended subtype map is not assumed
injective: the invariance predicate concerns its image.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 4, §c, for invariant subspaces
  and the representation-comodule correspondence. The criterion here is stated
  for commutative Hopf algebras over commutative rings.
* The right-comodule image-stability, induced-subtype and uniqueness APIs in
  this library, and Mathlib's tensor-product and scalar-extension APIs.
* M. E. Sweedler, *Hopf Algebras*, W. A. Benjamin, 1969 (bibliographic credit).
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u a v t r

namespace AlgebraicGeometry.PointRepresentation

variable {K : Type u} {C : Type a} [CommRing K] [CommRing C] [HopfAlgebra K C]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable (η : PointRepresentation.{u, a, v, t} K C V)

/-- Every genuine component preserves the image of the original scalar-extended
subtype inclusion, on every element of that image. -/
def IsInvariant (U : Submodule K V) : Prop :=
  ∀ (R : CommAlgCat.{max a t, u} K) (g : C →ₐ[K] R) (z : R ⊗[K] V),
    z ∈ LinearMap.range (U.subtype.baseChange R) →
      (η.operator R g).val z ∈ LinearMap.range (U.subtype.baseChange R)

/-- Invariance tests the original scalar-extension image, not just one-tensors. -/
theorem isInvariant_iff (U : Submodule K V) :
    η.IsInvariant U ↔
      ∀ (R : CommAlgCat.{max a t, u} K) (g : C →ₐ[K] R) (z : R ⊗[K] V),
        z ∈ U.baseChange R → (η.operator R g).val z ∈ U.baseChange R := Iff.rfl

/-- Original-image invariance is exactly image stability for the same recovered
right coaction. The generic algebra has size `max a t`, independently of the
base-ring and module universes. This is the invariant-subspace criterion in
Milne, *Algebraic Groups*, Chapter 4, §c, generalized to commutative base rings. -/
theorem isInvariant_iff_isStable (U : Submodule K V) :
    η.IsInvariant U ↔ η.toRightComodule.IsStable U := by
  constructor
  · intro hU x hx
    let L := ULift.{t} C
    let e : L ≃ₐ[K] C := ULift.algEquiv
    let β : C →ₐ[K] L := e.symm.toAlgHom
    have hz := hU (CommAlgCat.of K L) β (1 ⊗ₜ[K] x)
      (Submodule.tmul_mem_baseChange_of_mem (1 : L) hx)
    change η.genericLinearMap x ∈ U.baseChange L at hz
    have hdown := U.map_mem_baseChange e.toLinearMap hz
    rw [← η.comm_recoveredCoaction x] at hdown
    exact (TensorProduct.comm_mem_baseChange_iff U (η.recoveredCoaction x)).mp hdown
  · intro hU R g z hz
    rw [η.operator_val R g]
    exact hU.evaluate_mem_baseChange g.toLinearMap hz

/-- Invariance gives preservation at any independently sized coefficient
algebra by evaluation of the same recovered coaction. It does not refer to a
component of the natural transformation outside its category of test algebras. -/
theorem IsInvariant.evaluate_mem_baseChange {U : Submodule K V}
    (hU : η.IsInvariant U) {R : Type r} [CommRing R] [Algebra K R]
    (g : C →ₐ[K] R) {z : R ⊗[K] V} (hz : z ∈ U.baseChange R) :
    η.evaluate g z ∈ U.baseChange R :=
  ((η.isInvariant_iff_isStable U).1 hU).evaluate_mem_baseChange g.toLinearMap hz

/-- Invariance under the canonical GL action holds in both directions, using
its antipode-induced inverse. The coefficient algebra may have any size. -/
theorem IsInvariant.pointAction_mem_baseChange_iff {U : Submodule K V}
    (hU : η.IsInvariant U) {R : Type r} [CommRing R] [Algebra K R]
    (g : WithConv (C →ₐ[K] R)) (z : R ⊗[K] V) :
    (η.pointAction g).val z ∈ U.baseChange R ↔ z ∈ U.baseChange R :=
  ((η.isInvariant_iff_isStable U).1 hU).pointAction_mem_baseChange_iff g z

/-- Every available component preserves the original image in both directions. -/
theorem IsInvariant.operator_mem_baseChange_iff {U : Submodule K V}
    (hU : η.IsInvariant U) (R : CommAlgCat.{max a t, u} K)
    (g : C →ₐ[K] R) (z : R ⊗[K] V) :
    (η.operator R g).val z ∈ U.baseChange R ↔ z ∈ U.baseChange R := by
  rw [← η.pointAction_eq_operator R g]
  exact IsInvariant.pointAction_mem_baseChange_iff η hU (WithConv.toConv g) z

/-- The underlying submodule of an existing subcomodule is invariant in the
point representation of its ambient comodule, without any flatness assumption. -/
theorem ofRightComodule_subcomodule_isInvariant (X : Coalgebra.RightComodule K C V)
    (S : X.Subcomodule) : (ofRightComodule.{u, a, v, t} X).IsInvariant S.toSubmodule := by
  apply ((ofRightComodule X).isInvariant_iff_isStable S.toSubmodule).2
  simpa only [toRightComodule_ofRightComodule] using S.isStable

section Flat

variable [Module.Flat K C]

/-- The existing induced subcomodule of an invariant submodule. Its underlying
submodule is the original `U`; its coaction uses the stock closed tensor lift. -/
def restrictedSubcomodule (U : Submodule K V) (hU : η.IsInvariant U) :
    η.toRightComodule.Subcomodule :=
  Coalgebra.RightComodule.Subcomodule.ofIsStable η.toRightComodule U
    ((η.isInvariant_iff_isStable U).1 hU)

@[simp] theorem restrictedSubcomodule_toSubmodule (U : Submodule K V)
    (hU : η.IsInvariant U) : (η.restrictedSubcomodule U hU).toSubmodule = U := rfl

/-- Membership in the induced subcomodule is membership in the original submodule. -/
@[simp] theorem mem_restrictedSubcomodule (U : Submodule K V) (hU : η.IsInvariant U)
    (x : V) : x ∈ η.restrictedSubcomodule U hU ↔ x ∈ U := Iff.rfl

/-- The specified right comodule on exactly the original submodule subtype. -/
def restrictedComodule (U : Submodule K V) (hU : η.IsInvariant U) :
    Coalgebra.RightComodule K C U :=
  (η.restrictedSubcomodule U hU).comodule

/-- The coaction is the existing closed lift, as linear-map data. -/
@[simp] theorem restrictedComodule_coaction (U : Submodule K V) (hU : η.IsInvariant U) :
    (η.restrictedComodule U hU).coaction =
      Coalgebra.RightComodule.Subcomodule.coactionLift η.toRightComodule U
        ((η.isInvariant_iff_isStable U).1 hU) := rfl

/-- The original tensor inclusion reads the restricted coaction back as the
ambient coaction, as an equality of linear maps. -/
theorem subtype_rTensor_comp_restrictedCoaction (U : Submodule K V)
    (hU : η.IsInvariant U) :
    U.subtype.rTensor C ∘ₗ (η.restrictedComodule U hU).coaction =
      η.toRightComodule.coaction ∘ₗ U.subtype :=
  (η.restrictedSubcomodule U hU).subtype_colinear

/-- The restricted coaction is the unique linear-map factorization through the
original tensor inclusion; its characterization is equality of map data. -/
theorem restrictedCoaction_eq_iff (U : Submodule K V) (hU : η.IsInvariant U)
    (f : U →ₗ[K] U ⊗[K] C) :
    f = (η.restrictedComodule U hU).coaction ↔
      U.subtype.rTensor C ∘ₗ f = η.toRightComodule.coaction ∘ₗ U.subtype := by
  constructor
  · rintro rfl
    exact η.subtype_rTensor_comp_restrictedCoaction U hU
  · intro hf
    apply (LinearMap.cancel_left
      (f := U.subtype.rTensor C) (g := f)
      (g' := (η.restrictedComodule U hU).coaction)
      (Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective)).mp
    exact hf.trans (η.subtype_rTensor_comp_restrictedCoaction U hU).symm

/-- Elementwise readback of the restricted coaction under the original inclusion. -/
theorem subtype_rTensor_restrictedCoaction (U : Submodule K V)
    (hU : η.IsInvariant U) (x : U) :
    U.subtype.rTensor C ((η.restrictedComodule U hU).coaction x) =
      η.recoveredCoaction (x : V) :=
  LinearMap.congr_fun (η.subtype_rTensor_comp_restrictedCoaction U hU) x

/-- Uniqueness is the stock uniqueness of a subcomodule with a given underlying
submodule, not a choice of an isomorphic carrier. -/
theorem restrictedSubcomodule_unique (U : Submodule K V) (hU : η.IsInvariant U)
    (S : η.toRightComodule.Subcomodule) (hS : S.toSubmodule = U) :
    S = η.restrictedSubcomodule U hU :=
  Coalgebra.RightComodule.Subcomodule.ext hS

/-- The original inclusion equation uniquely determines the specified comodule
value on `U`. This follows from stock subcomodule uniqueness. -/
theorem restrictedComodule_unique (U : Submodule K V) (hU : η.IsInvariant U)
    (Y : Coalgebra.RightComodule K C U)
    (hY : U.subtype.rTensor C ∘ₗ Y.coaction =
      η.toRightComodule.coaction ∘ₗ U.subtype) :
    Y = η.restrictedComodule U hU := by
  let S : η.toRightComodule.Subcomodule :=
    { toSubmodule := U, comodule := Y, subtype_colinear := hY }
  have hS : S = η.restrictedSubcomodule U hU :=
    η.restrictedSubcomodule_unique U hU S rfl
  have hc : HEq S.comodule (η.restrictedSubcomodule U hU).comodule := by rw [hS]
  exact eq_of_heq hc

/-- The canonical inclusion is the existing ambient subcomodule morphism. -/
def restrictedSubtypeHom (U : Submodule K V) (hU : η.IsInvariant U) :
    Coalgebra.RightComoduleHom (η.restrictedComodule U hU) η.toRightComodule :=
  (η.restrictedSubcomodule U hU).subtype

@[simp] theorem restrictedSubtypeHom_toLinearMap (U : Submodule K V)
    (hU : η.IsInvariant U) :
    (η.restrictedSubtypeHom U hU).toLinearMap = U.subtype := rfl

@[simp] theorem restrictedSubtypeHom_apply (U : Submodule K V)
    (hU : η.IsInvariant U) (x : U) : η.restrictedSubtypeHom U hU x = (x : V) := rfl

/-- The natural point representation on the same subtype, obtained by applying
the constructed forward correspondence to its induced comodule. -/
def restrictedPointRepresentation (U : Submodule K V) (hU : η.IsInvariant U) :
    PointRepresentation.{u, a, v, t} K C U :=
  ofRightComodule (η.restrictedComodule U hU)

/-- Reconstruction returns the same specified subtype-comodule value. -/
@[simp] theorem restrictedPointRepresentation_toRightComodule (U : Submodule K V)
    (hU : η.IsInvariant U) :
    (η.restrictedPointRepresentation U hU).toRightComodule = η.restrictedComodule U hU :=
  toRightComodule_ofRightComodule _

/-- The restricted component is evaluation of the induced coaction. -/
theorem restrictedPointRepresentation_operator_val (U : Submodule K V)
    (hU : η.IsInvariant U) (R : CommAlgCat.{max a t, u} K) (g : C →ₐ[K] R) :
    ((η.restrictedPointRepresentation U hU).operator R g).val =
      (η.restrictedComodule U hU).evaluate g.toLinearMap := rfl

/-- At any independently sized coefficient algebra, the restricted representation
evaluates the same induced coaction. -/
theorem restrictedPointRepresentation_evaluate (U : Submodule K V)
    (hU : η.IsInvariant U) {R : Type r} [CommRing R] [Algebra K R]
    (g : C →ₐ[K] R) :
    (η.restrictedPointRepresentation U hU).evaluate g =
      (η.restrictedComodule U hU).evaluate g.toLinearMap := by
  change (η.restrictedPointRepresentation U hU).toRightComodule.evaluate g.toLinearMap = _
  rw [restrictedPointRepresentation_toRightComodule]

/-- The original subtype inclusion as a point intertwiner. The existing Hom
correspondence and comodule-value inverse transport its colinearity law without
changing its underlying linear map. -/
def restrictedInclusion (U : Submodule K V) (hU : η.IsInvariant U) :
    PointHom (η.restrictedPointRepresentation U hU) η :=
  (pointHomEquiv (η.restrictedPointRepresentation U hU) η).symm
    { toLinearMap := U.subtype
      colinear := by
        rw [restrictedPointRepresentation_toRightComodule]
        exact (η.restrictedSubtypeHom U hU).colinear }

@[simp] theorem restrictedInclusion_toLinearMap (U : Submodule K V)
    (hU : η.IsInvariant U) : (η.restrictedInclusion U hU).toLinearMap = U.subtype := rfl

@[simp] theorem restrictedInclusion_apply (U : Submodule K V)
    (hU : η.IsInvariant U) (x : U) :
    (η.restrictedInclusion U hU).toLinearMap x = (x : V) := rfl

/-- Every component square uses precisely the scalar extension of the original
inclusion, on every tensor of the original subtype. -/
theorem restrictedInclusion_operator_apply (U : Submodule K V) (hU : η.IsInvariant U)
    (R : CommAlgCat.{max a t, u} K) (g : C →ₐ[K] R) (z : R ⊗[K] U) :
    U.subtype.baseChange R (((η.restrictedPointRepresentation U hU).operator R g).val z) =
      (η.operator R g).val (U.subtype.baseChange R z) :=
  (η.restrictedInclusion U hU).operator_apply R g z

/-- The inclusion square holds at every independently sized coefficient algebra,
using canonical evaluation rather than an unavailable component. -/
theorem restrictedInclusion_evaluate_apply (U : Submodule K V) (hU : η.IsInvariant U)
    {R : Type r} [CommRing R] [Algebra K R] (g : C →ₐ[K] R) (z : R ⊗[K] U) :
    U.subtype.baseChange R ((η.restrictedPointRepresentation U hU).evaluate g z) =
      η.evaluate g (U.subtype.baseChange R z) :=
  (η.restrictedInclusion U hU).baseChange_evaluate_apply g z

/-- The point-intertwining condition on the original inclusion uniquely
determines the restricted natural representation, as a natural-transformation
value rather than only up to an isomorphism. -/
theorem restrictedPointRepresentation_unique (U : Submodule K V) (hU : η.IsInvariant U)
    (θ : PointRepresentation.{u, a, v, t} K C U)
    (hθ : IsPointIntertwining θ η U.subtype) :
    θ = η.restrictedPointRepresentation U hU := by
  apply toRightComodule_injective
  rw [restrictedPointRepresentation_toRightComodule]
  apply η.restrictedComodule_unique U hU
  exact ((isPointIntertwining_iff_colinear θ η U.subtype).1 hθ).symm

/-- Exactly one natural representation on the original subtype makes its
original inclusion point-intertwining. -/
theorem existsUnique_restrictedPointRepresentation (U : Submodule K V)
    (hU : η.IsInvariant U) :
    ∃! θ : PointRepresentation.{u, a, v, t} K C U,
      IsPointIntertwining θ η U.subtype :=
  ⟨η.restrictedPointRepresentation U hU, (η.restrictedInclusion U hU).property,
    fun θ hθ ↦ η.restrictedPointRepresentation_unique U hU θ hθ⟩

/-- Applying restriction to an existing subcomodule returns its original
specified coaction value, exercising the criterion on the stock inclusion. -/
theorem restrictedComodule_of_subcomodule (X : Coalgebra.RightComodule K C V)
    (S : X.Subcomodule) :
    (ofRightComodule.{u, a, v, t} X).restrictedComodule S.toSubmodule
        (ofRightComodule_subcomodule_isInvariant X S) = S.comodule := by
  symm
  apply (ofRightComodule X).restrictedComodule_unique
  simpa only [toRightComodule_ofRightComodule] using S.subtype_colinear

end Flat

end AlgebraicGeometry.PointRepresentation
