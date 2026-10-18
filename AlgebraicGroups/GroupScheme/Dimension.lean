/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Integral

public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.Ideal.Height

public import AlgebraicGroups.GroupObject.BaseChange
public import AlgebraicGroups.GroupScheme.ComponentSchemeMap
public import AlgebraicGroups.GroupScheme.ReducedIdentityComponent
public import AlgebraicGroups.Topology.KrullDimension

/-!
# Dimensions of group schemes

This file relates the Krull dimension of the local ring at the unit of a
group scheme locally of finite type over a field to its topological Krull
dimension. Over an algebraically closed field, it also identifies the
topological Krull dimension of a locally finite-type group scheme with the
dimension of its identity component, and combines this with invariance under
scheme reduction to treat the identity component of the reduction.

## References

- J. S. Milne, *Algebraic Groups*, the dimension discussion following
  Summary 1.36 (printed p. 17), for the common dimension of translated
  connected components. These are topological Krull dimensions; the
  tangent-space statement of Proposition 1.37 is different.
- The local `Topology.KrullDimension` supplies the open-cover supremum
  formula, `GroupScheme.ComponentGroup` the rational representatives,
  `GroupScheme.ComponentSchemeMap` the translation isomorphisms, and
  `Scheme.Reduction` the invariance of topological dimension under reduction.
  The mathlib community, *Mathlib*, supplies topological Krull dimension
  and the dimension invariance of homeomorphisms and embeddings.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open TopologicalSpace

universe v w

/-- Contraction preserves the height of a prime in an integral algebra satisfying going down. -/
private theorem primeSpectrum_height_comap_eq_of_isIntegral_of_hasGoingDown
    {R : Type v} {A : Type w} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.IsIntegral R A] [Algebra.HasGoingDown R A] (q : PrimeSpectrum A) :
    (PrimeSpectrum.comap (algebraMap R A) q).asIdeal.height = q.asIdeal.height := by
  rw [PrimeSpectrum.height_eq_orderHeight, PrimeSpectrum.height_eq_orderHeight]
  have hmono : StrictMono (PrimeSpectrum.comap (algebraMap R A)) := by
    intro P Q hPQ
    apply (PrimeSpectrum.asIdeal_lt_asIdeal _ _).1
    exact Ideal.IsIntegral.under_lt_under (R := R)
      ((PrimeSpectrum.asIdeal_lt_asIdeal P Q).2 hPQ)
  -- Strictness is needed only for comparable primes, not global injectivity.
  refine (Order.height_eq_of_strictMono
    (PrimeSpectrum.comap (algebraMap R A)) hmono ?_ q).symm
  intro Q p hp
  have hp' : p.asIdeal < Q.asIdeal.under R :=
    (PrimeSpectrum.asIdeal_lt_asIdeal _ _).2 hp
  obtain ⟨P, hPQ, hP, hPp⟩ :=
    Ideal.exists_ideal_lt_liesOver_of_lt (p := p.asIdeal)
      (q := Q.asIdeal.under R) Q.asIdeal hp'
  refine ⟨⟨P, hP⟩, (PrimeSpectrum.asIdeal_lt_asIdeal _ _).1 hPQ, ?_⟩
  exact PrimeSpectrum.ext_iff.mpr hPp.over.symm

namespace AlgebraicGeometry

section UnitStalkDimension

universe u

/-- An integral flat morphism preserves the Krull dimension of every stalk. -/
private theorem ringKrullDim_stalk_eq_of_isIntegralHom_of_flat
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f] [Flat f] (x : X) :
    ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (f x)) := by
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := Y) (x := f x) (U := ⊤) (by trivial)
  have hV : IsAffineOpen (f ⁻¹ᵁ U) := hU.preimage f
  have hx : x ∈ f ⁻¹ᵁ U := hxU
  let φ : Γ(Y, U) →+* Γ(X, f ⁻¹ᵁ U) := (f.app U).hom
  let : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := φ.toAlgebra
  have : Algebra.IsIntegral Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := ⟨f.isIntegral_app U hU⟩
  have : Module.Flat Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := by
    change φ.Flat
    simpa only [Scheme.Hom.appLE_eq_app] using f.flat_appLE hU hV le_rfl
  let q : PrimeSpectrum Γ(X, f ⁻¹ᵁ U) := hV.primeIdealOf ⟨x, hx⟩
  let P : PrimeSpectrum Γ(Y, U) := hU.primeIdealOf ⟨f x, hxU⟩
  have hq : PrimeSpectrum.comap φ q = P := by
    simpa only [Scheme.Hom.appLE_eq_app] using
      (IsAffineOpen.comap_primeIdealOf_appLE (f := f) U hU (f ⁻¹ᵁ U) hV le_rfl hx)
  have hheight : P.asIdeal.height = q.asIdeal.height := by
    rw [← hq]
    exact primeSpectrum_height_comap_eq_of_isIntegral_of_hasGoingDown
      (R := Γ(Y, U)) q
  let := Y.presheaf.algebra_section_stalk ⟨f x, hxU⟩
  let := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have : IsLocalization.AtPrime (Y.presheaf.stalk (f x)) P.asIdeal :=
    hU.isLocalization_stalk ⟨f x, hxU⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x) q.asIdeal :=
    hV.isLocalization_stalk ⟨x, hx⟩
  calc
    ringKrullDim (X.presheaf.stalk x) = q.asIdeal.height :=
      IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal _
    _ = P.asIdeal.height := by rw [hheight]
    _ = ringKrullDim (Y.presheaf.stalk (f x)) :=
      (IsLocalization.AtPrime.ringKrullDim_eq_height P.asIdeal _).symm

/-- Left translation identifies the dimensions of the full local rings at the
values of a section and the unit section over any point of the base scheme. -/
theorem ringKrullDim_stalk_groupSchemeSection_eq_unit
    {S G : Scheme.{u}} (f : G ⟶ S) [GrpObj (Over.mk f)]
    (a : 𝟙_ (Over S) ⟶ Over.mk f) (s : S) :
    ringKrullDim (G.presheaf.stalk (a.left s)) =
      ringKrullDim (G.presheaf.stalk (η[Over.mk f].left s)) := by
  let e : G ≅ G := (Over.forget _).mapIso (CategoryTheory.GrpObj.mulLeft a)
  have h : e.hom (η[Over.mk f].left s) = a.left s := by
    change (η[Over.mk f] ≫ (CategoryTheory.GrpObj.mulLeft a).hom).left s = _
    rw [CategoryTheory.GrpObj.unit_comp_mulLeft_hom]
  rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight,
    ← h, coheight_eq_of_isOpenImmersion e.hom]

/-- Left translation identifies the dimensions of the full local rings at a
rational point and at the unit of a group scheme. Neither finite type nor
algebraic closure of the field is needed. -/
theorem ringKrullDim_stalk_groupSchemePoint_eq_unit
    (K : Type u) [Field K] (G : Scheme.{u})
    (f : G ⟶ Spec (.of K)) [GrpObj (Over.mk f)]
    (a : 𝟙_ (Over (Spec (.of K))) ⟶ Over.mk f) :
    ringKrullDim (G.presheaf.stalk (a.left (IsLocalRing.closedPoint K))) =
      ringKrullDim (G.presheaf.stalk
        (η[Over.mk f].left (IsLocalRing.closedPoint K))) := by
  exact ringKrullDim_stalk_groupSchemeSection_eq_unit f a (IsLocalRing.closedPoint K)

/-- The Krull dimension of the local ring at the unit of a group scheme locally
of finite type over a field equals its topological Krull dimension. The field
need not be algebraically closed, and the group scheme need not be connected
or reduced. -/
theorem ringKrullDim_stalk_unit_eq_topologicalKrullDim
    (K : Type u) [Field K] (G : Scheme.{u})
    (f : G ⟶ Spec (.of K)) [GrpObj (Over.mk f)] [LocallyOfFiniteType f] :
    ringKrullDim (G.presheaf.stalk
      (η[Over.mk f].left (IsLocalRing.closedPoint K))) =
      topologicalKrullDim G := by
  apply le_antisymm
  · rw [ringKrullDim_stalk_eq_coheight]
    change (Order.coheight _ : WithBot ℕ∞) ≤
      Order.krullDim (IrreducibleCloseds G)
    rw [Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := G))]
    exact Order.coheight_le_krullDim _
  · let : JacobsonSpace G := LocallyOfFiniteType.jacobsonSpace f
    suffices hclosed : ∀ y : closedPoints G,
        ringKrullDim (G.presheaf.stalk y.1) ≤
          ringKrullDim (G.presheaf.stalk
            (η[Over.mk f].left (IsLocalRing.closedPoint K))) by
      change Order.krullDim (IrreducibleCloseds G) ≤ _
      rw [Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := G)),
        Order.krullDim_eq_iSup_coheight]
      apply iSup_le
      intro x
      obtain ⟨y, hyx, hyclosed⟩ := nonempty_inter_closedPoints
        (Z := closure ({x} : Set G)) ⟨x, subset_closure (by simp)⟩
        isClosed_closure.isLocallyClosed
      have hy : y ≤ x := specializes_iff_mem_closure.mpr hyx
      calc
        (Order.coheight x : WithBot ℕ∞) ≤ Order.coheight y :=
          WithBot.coe_le_coe.mpr (Order.coheight_anti hy)
        _ = ringKrullDim (G.presheaf.stalk y) :=
          (ringKrullDim_stalk_eq_coheight y).symm
        _ ≤ ringKrullDim (G.presheaf.stalk
            (η[Over.mk f].left (IsLocalRing.closedPoint K))) :=
          hclosed ⟨y, hyclosed⟩
    -- A closed point need not be rational over K; translation alone does not apply.
    intro y
    let L : CommRingCat := G.residueField y.1
    let a : Spec L ⟶ G := G.fromSpecResidueField y.1
    let β : Spec L ⟶ Spec (.of K) := a ≫ f
    have : IsClosedImmersion a :=
      isClosed_singleton_iff_isClosedImmersion.mp y.2
    have : IsFinite β :=
      (isFinite_iff_locallyOfFiniteType_of_jacobsonSpace
        (f := β)).2 (by infer_instance)
    let fL : pullback f β ⟶ Spec L := pullback.snd f β
    let : GrpObj (Over.mk fL) := Over.grpObjMkPullbackSnd
    let aL : 𝟙_ (Over (Spec L)) ⟶ Over.mk fL :=
      Over.homMk (pullback.lift a (𝟙 _) (by simp [β])) (by
        change pullback.lift a (𝟙 _) _ ≫ pullback.snd f β = 𝟙 _
        exact pullback.lift_snd _ _ _)
    let s : Spec L := IsLocalRing.closedPoint L
    have haL_fst : aL.left ≫ pullback.fst f β = a := by
      change pullback.lift a (𝟙 _) _ ≫ pullback.fst f β = a
      exact pullback.lift_fst _ _ _
    have ha_point : pullback.fst f β (aL.left s) = y.1 := by
      calc
        pullback.fst f β (aL.left s) = a s := by
          simpa only [Scheme.Hom.comp_apply] using
            congrArg (fun q : Spec L ⟶ G => q s) haL_fst
        _ = y.1 := G.fromSpecResidueField_apply y.1 s
    have hunit_fst : η[Over.mk fL].left ≫ pullback.fst f β =
        β ≫ η[Over.mk f].left := Over.unit_pullback_fst f β
    have hunit_point : pullback.fst f β (η[Over.mk fL].left s) =
        η[Over.mk f].left (IsLocalRing.closedPoint K) := by
      simpa only [Scheme.Hom.comp_apply,
        Subsingleton.elim (β s) (IsLocalRing.closedPoint K)] using
          congrArg (fun q : Spec L ⟶ G => q s) hunit_fst
    apply le_of_eq
    calc
      ringKrullDim (G.presheaf.stalk y.1) =
          ringKrullDim ((pullback f β).presheaf.stalk (aL.left s)) := by
        exact (congrArg (fun z : G => ringKrullDim (G.presheaf.stalk z))
          ha_point).symm.trans
            (ringKrullDim_stalk_eq_of_isIntegralHom_of_flat
              (f := pullback.fst f β) (x := aL.left s)).symm
      _ = ringKrullDim ((pullback f β).presheaf.stalk
          (η[Over.mk fL].left s)) :=
        ringKrullDim_stalk_groupSchemeSection_eq_unit fL aL s
      _ = ringKrullDim (G.presheaf.stalk
          (η[Over.mk f].left (IsLocalRing.closedPoint K))) := by
        exact (ringKrullDim_stalk_eq_of_isIntegralHom_of_flat
          (f := pullback.fst f β) (x := η[Over.mk fL].left s)).trans
            (congrArg (fun z : G => ringKrullDim (G.presheaf.stalk z)) hunit_point)

end UnitStalkDimension

universe u

noncomputable section

variable {K : Type u} [Field K] [IsAlgClosed K] {G : Scheme.{u}}
variable (f : G ⟶ Spec (.of K)) [GrpObj (Over.mk f)] [LocallyConnectedSpace G]

local instance : LocallyConnectedSpace (Over.mk f).left :=
  inferInstanceAs (LocallyConnectedSpace G)

/-- A locally finite-type group scheme over an algebraically closed field and
its identity component have the same topological Krull dimension. This
follows the common-component-dimension discussion in Milne,
*Algebraic Groups*, immediately following Summary 1.36, using translations
and the open-cover formula rather than irreducible-component dimensions. -/
theorem identityComponent_topologicalKrullDim [LocallyOfFiniteType f] :
    topologicalKrullDim (Scheme.identityComponentOver (Over.mk f)).left =
      topologicalKrullDim G := by
  apply le_antisymm
  · exact (Scheme.identityComponentι (Over.mk f)).left.isOpenEmbedding.isInducing
      |>.topologicalKrullDim_le
  · rw [topologicalKrullDim_eq_iSup_of_isOpen_cover
      (fun c : ConnectedComponents G ↦ (G.connectedComponentOpen c : Set G))
      (fun c ↦ (G.connectedComponentOpen c).isOpen) (by
        apply Set.eq_univ_of_forall
        intro x
        exact Set.mem_iUnion_of_mem (ConnectedComponents.mk x)
          ((G.mem_connectedComponentOpen (ConnectedComponents.mk x) x).2 rfl))]
    apply iSup_le
    intro c
    obtain ⟨a, rfl⟩ := groupSchemePointComponent_surjective f c
    let e := (identityComponentIsoConnectedComponent f a).schemeIsoToHomeo
    exact (e.isHomeomorph.topologicalKrullDim_eq e).symm.le

/-- The identity component of the reduction of a locally finite-type group
scheme over an algebraically closed field has the same topological Krull
dimension as the original scheme.  Reducedness of the Cartesian square of the
reduction is the explicit hypothesis needed for its group-scheme structure.
The component-dimension idea is in Milne, *Algebraic Groups*, after Summary
1.36; the final equality uses the local reduction-dimension invariance. -/
theorem reducedIdentityComponent_topologicalKrullDim
    [LocallyOfFiniteType f]
    [IsReduced ((Scheme.reductionOver (Over.mk f) ⊗
      Scheme.reductionOver (Over.mk f)).left)] :
    topologicalKrullDim
        (Scheme.reducedIdentityComponentOver (Over.mk f)).left =
      topologicalKrullDim G := by
  let _ : IsClosedImmersion (Scheme.reductionι.app G) := by
    change IsClosedImmersion G.nilradical.subschemeι
    infer_instance
  let _ : LocallyOfFiniteType (Scheme.reductionOver (Over.mk f)).hom := by
    change LocallyOfFiniteType (Scheme.reductionι.app G ≫ f)
    infer_instance
  let _ : GrpObj (Over.mk (Scheme.reductionOver (Over.mk f)).hom) :=
    inferInstanceAs (GrpObj (Scheme.reductionOver (Over.mk f)))
  let _ : LocallyConnectedSpace (Over.mk
      (Scheme.reductionOver (Over.mk f)).hom).left :=
    inferInstanceAs (LocallyConnectedSpace
      (Scheme.reductionOver (Over.mk f)).left)
  calc
    topologicalKrullDim
        (Scheme.reducedIdentityComponentOver (Over.mk f)).left =
        topologicalKrullDim (Scheme.reductionOver (Over.mk f)).left :=
      identityComponent_topologicalKrullDim
        (Scheme.reductionOver (Over.mk f)).hom
    _ = topologicalKrullDim G := Scheme.reduction_topologicalKrullDim G

end

end AlgebraicGeometry
