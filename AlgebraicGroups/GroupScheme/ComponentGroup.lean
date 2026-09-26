/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupObject.Quotient
public import AlgebraicGroups.GroupScheme.ClosedPoints
public import AlgebraicGroups.GroupScheme.IdentityComponent

/-!
# Component groups of finite-type group schemes

For a group scheme over an algebraically closed field, this file compares the
quotient of its rational-point group by the image of the identity component
with the connected components of the underlying scheme. Every component has a
rational point, and the comparison is an equivalence. Consequently this
rational component group is finite for a finite-type group scheme.

The hypotheses needed by the current identity-component API remain explicit.
In particular, the identity component's Cartesian square is assumed connected
when constructing its group structure, and geometric connectedness is assumed
when giving its point image the structure of a normal subgroup. No topological
group structure on the underlying scheme is used.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open TopologicalSpace
open scoped CategoryTheory.MonObj

noncomputable section

namespace AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {G : Scheme.{u}}

/-- The type of `K`-rational points over `Spec K`. It inherits its group
structure when `Over.mk f` is a group object. -/
abbrev groupSchemePoints (f : G ⟶ Spec (.of K)) : Type u :=
  𝟙_ (Over (Spec (.of K))) ⟶ Over.mk f

/-- The underlying point of a group-scheme rational point, evaluated at the
unique closed point of the base spectrum. -/
abbrev groupSchemePointValue (f : G ⟶ Spec (.of K))
    (x : groupSchemePoints f) : G :=
  x.left (IsLocalRing.closedPoint K)

/-- The connected component containing the underlying point of a group-scheme
`K`-point. -/
@[expose] def groupSchemePointComponent
    (f : G ⟶ Spec (.of K)) (x : groupSchemePoints f) :
    ConnectedComponents G :=
  ConnectedComponents.mk (groupSchemePointValue f x)

/-- The component of a rational point is represented by its underlying point
over the unique point of `Spec K`. -/
@[simp]
lemma groupSchemePointComponent_eq_mk (f : G ⟶ Spec (.of K))
    (x : groupSchemePoints f) :
    groupSchemePointComponent f x =
      ConnectedComponents.mk (x.left (IsLocalRing.closedPoint K)) :=
  rfl

private lemma groupSchemePointComponent_mulLeft
    (f : G ⟶ Spec (.of K)) [GrpObj (Over.mk f)] (a x : groupSchemePoints f) :
    groupSchemePointComponent f (a * x) =
      (CategoryTheory.GrpObj.mulLeft a).hom.left.continuous.connectedComponentsMap
        (groupSchemePointComponent f x) := by
  rw [groupSchemePointComponent, groupSchemePointComponent,
    Continuous.connectedComponentsMap_mk]
  apply congrArg ConnectedComponents.mk
  exact (congrArg (groupSchemePointValue f)
    (CategoryTheory.GrpObj.comp_mulLeft_hom a x)).symm

section ClosedPoints

variable [IsAlgClosed K]

/-- Every connected component of a group scheme locally of finite type over an
algebraically closed field contains a rational point. -/
theorem groupSchemePointComponent_surjective
    (f : G ⟶ Spec (.of K)) [GrpObj (Over.mk f)] [LocallyOfFiniteType f] :
    Function.Surjective (groupSchemePointComponent f) := by
  intro c
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  let _ : JacobsonSpace G := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨y, hy, hyClosed⟩ := nonempty_inter_closedPoints
    (isConnected_connectedComponent (x := x)).nonempty
    isClosed_connectedComponent.isLocallyClosed
  let y' : closedPoints G := ⟨y, hyClosed⟩
  let p := (groupSchemePointEquivClosedPoint f).symm y'
  have hp' : groupSchemePointValue f p = y := by
    simp [p, y']
  refine ⟨p, ?_⟩
  rw [groupSchemePointComponent, ConnectedComponents.coe_eq_coe']
  rwa [hp']

end ClosedPoints

section IdentityComponent

variable (f : G ⟶ Spec (.of K)) [GrpObj (Over.mk f)] [LocallyConnectedSpace G]

local instance overMkLocallyConnected : LocallyConnectedSpace (Over.mk f).left :=
  inferInstanceAs (LocallyConnectedSpace G)

private lemma exists_identityComponentPoint_iff (x : groupSchemePoints f) :
    groupSchemePointValue f x ∈ Scheme.identityComponent (Over.mk f) ↔
      ∃ y : groupSchemePoints (Scheme.identityComponentOver (Over.mk f)).hom,
        y ≫ Scheme.identityComponentι (Over.mk f) = x := by
  constructor
  · intro hx
    let i := Scheme.identityComponentι (Over.mk f)
    have hRange : Set.range x.left ⊆ Set.range i.left := by
      rintro _ ⟨s, rfl⟩
      change Spec (.of K) at s
      rw [Subsingleton.elim s (IsLocalRing.closedPoint K)]
      exact ⟨⟨groupSchemePointValue f x, hx⟩, rfl⟩
    let yLeft := IsOpenImmersion.lift i.left x.left hRange
    have hLift : yLeft ≫ i.left = x.left := by
      exact IsOpenImmersion.lift_fac _ _ _
    let y : groupSchemePoints (Scheme.identityComponentOver (Over.mk f)).hom :=
      Over.homMk yLeft (by
        change yLeft ≫ ((Scheme.identityComponent (Over.mk f)).ι ≫ f) = _
        rw [← Category.assoc]
        change (yLeft ≫ i.left) ≫ f = _
        rw [hLift]
        exact x.w)
    refine ⟨y, ?_⟩
    ext
    exact hLift
  · rintro ⟨y, rfl⟩
    exact (y.left (IsLocalRing.closedPoint K)).2

variable [ConnectedSpace ((Scheme.identityComponentOver (Over.mk f) ⊗
  Scheme.identityComponentOver (Over.mk f)).left)]

/-- The subgroup of rational points induced from the identity-component
subgroup scheme. -/
abbrev identityComponentPointSubgroup : Subgroup (groupSchemePoints f) :=
  (IsMonHom.monoidHom (Scheme.identityComponentι (Over.mk f))
    (𝟙_ (Over (Spec (.of K))))).range

private lemma groupSchemePointComponent_one_eq_iff (x : groupSchemePoints f) :
    groupSchemePointComponent f 1 = groupSchemePointComponent f x ↔
      x ∈ identityComponentPointSubgroup f := by
  rw [eq_comm, groupSchemePointComponent, groupSchemePointComponent,
    ConnectedComponents.coe_eq_coe']
  have hOne : groupSchemePointValue f (1 : groupSchemePoints f) =
      (η[Over.mk f]).left (IsLocalRing.closedPoint K) := by
    rfl
  rw [hOne]
  rw [← Scheme.mem_identityComponent_iff (Over.mk f)
    (groupSchemePointValue f x) (IsLocalRing.closedPoint K)]
  rw [exists_identityComponentPoint_iff f]
  rfl

/-- Two rational points lie in the same connected component exactly when their
group quotient lies in the image of the identity component. -/
theorem groupSchemePointComponent_eq_iff (x y : groupSchemePoints f) :
    groupSchemePointComponent f x = groupSchemePointComponent f y ↔
      x⁻¹ * y ∈ identityComponentPointSubgroup f := by
  rw [← groupSchemePointComponent_one_eq_iff f (x⁻¹ * y)]
  constructor
  · intro h
    have h' := congrArg
      (CategoryTheory.GrpObj.mulLeft x⁻¹).hom.left.continuous.connectedComponentsMap h
    rw [← groupSchemePointComponent_mulLeft f,
      ← groupSchemePointComponent_mulLeft f] at h'
    simpa using h'
  · intro h
    have h' := congrArg
      (CategoryTheory.GrpObj.mulLeft x).hom.left.continuous.connectedComponentsMap h
    rw [← groupSchemePointComponent_mulLeft f,
      ← groupSchemePointComponent_mulLeft f] at h'
    simpa using h'

/-- The quotient of the rational-point group by the rational points induced
from the identity-component subgroup scheme. -/
abbrev rationalComponentGroup :=
  groupSchemePoints f ⧸ identityComponentPointSubgroup f

/-- Geometric connectedness of the identity component makes its image on
rational points a normal subgroup. -/
instance identityComponentPointSubgroup_normal
    [GeometricallyConnected (Scheme.identityComponentOver (Over.mk f)).hom] :
    (identityComponentPointSubgroup f).Normal :=
  (IsMonHom.normal_iff_normal_monoidHom.mp
    (inferInstance : IsMonHom.Normal (Scheme.identityComponentι (Over.mk f))))
      (𝟙_ (Over (Spec (.of K))))

private def rationalComponentGroupToConnectedComponents :
    rationalComponentGroup f → ConnectedComponents G :=
  Quotient.map' (groupSchemePointValue f) fun x y hxy ↦ by
    rw [QuotientGroup.leftRel_apply] at hxy
    exact ConnectedComponents.coe_eq_coe.mp
      ((groupSchemePointComponent_eq_iff f x y).2 hxy)

@[simp]
private lemma rationalComponentGroupToConnectedComponents_mk
    (x : groupSchemePoints f) :
    rationalComponentGroupToConnectedComponents f (Quotient.mk'' x) =
      groupSchemePointComponent f x :=
  rfl

private lemma rationalComponentGroupToConnectedComponents_injective :
    Function.Injective (rationalComponentGroupToConnectedComponents f) := by
  intro q₁ q₂
  refine Quotient.ind' (q := q₁) fun x ↦ ?_
  refine Quotient.ind' (q := q₂) fun y hxy ↦ ?_
  rw [QuotientGroup.eq, ← groupSchemePointComponent_eq_iff f]
  simpa only [rationalComponentGroupToConnectedComponents_mk] using hxy

section AlgebraicallyClosed

variable [IsAlgClosed K] [LocallyOfFiniteType f]

/-- Over an algebraically closed field, the rational component group is in
bijection with the connected components of the underlying scheme. -/
def rationalComponentGroupEquivConnectedComponents :
    rationalComponentGroup f ≃ ConnectedComponents G :=
  Equiv.ofBijective (rationalComponentGroupToConnectedComponents f)
    ⟨rationalComponentGroupToConnectedComponents_injective f,
      fun c ↦ by
        obtain ⟨x, hx⟩ := groupSchemePointComponent_surjective f c
        exact ⟨Quotient.mk'' x, by
          simpa only [rationalComponentGroupToConnectedComponents_mk] using hx⟩⟩

/-- The comparison with connected components sends the class of a rational
point to the component containing that point. -/
@[simp]
lemma rationalComponentGroupEquivConnectedComponents_mk
    (x : groupSchemePoints f) :
    rationalComponentGroupEquivConnectedComponents f (Quotient.mk'' x) =
      groupSchemePointComponent f x := by
  change rationalComponentGroupToConnectedComponents f (Quotient.mk'' x) = _
  exact rationalComponentGroupToConnectedComponents_mk f x

/-- The rational component group of a finite-type group scheme over an
algebraically closed field is finite. -/
instance rationalComponentGroupFinite [QuasiCompact f] :
    Finite (rationalComponentGroup f) :=
  letI : CompactSpace G := QuasiCompact.compactSpace_of_compactSpace f
  Finite.of_equiv (ConnectedComponents G)
    (rationalComponentGroupEquivConnectedComponents f).symm

end AlgebraicallyClosed

end IdentityComponent

end AlgebraicGeometry
