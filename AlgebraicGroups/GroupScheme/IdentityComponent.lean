/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Normal
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.Topology.Connected.LocallyConnected

/-!
# Identity components of group schemes over a one-point base

For a group scheme whose base has one underlying point and whose underlying
space is locally connected, this file packages the connected component of the
identity as an open subscheme. The unit and inverse restrict to it. If its
Cartesian square is connected, multiplication restricts as well, yielding a
group scheme whose inclusion is a monoid-object homomorphism. If, in addition,
the component is geometrically connected over the base, the inclusion is
normal.

The connectedness of the Cartesian square is deliberately explicit: no
preservation of connectedness by scheme fibre products is asserted here.
Likewise, geometric connectedness of the component is a separate hypothesis:
connectedness of the component or its Cartesian square is not silently
promoted to geometric connectedness.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open TopologicalSpace

namespace AlgebraicGeometry

universe u

variable {S : Scheme.{u}}

/-- The connected component containing the identity of a group scheme over a
nonempty one-point base, regarded as an open subset. -/
@[expose] noncomputable def Scheme.identityComponent (G : Over S) [GrpObj G]
    [LocallyConnectedSpace G.left] [Nonempty S] [Subsingleton S] : G.left.Opens :=
  ⟨connectedComponent (η[G].left (Classical.choice (inferInstance : Nonempty S))),
    isOpen_connectedComponent⟩

/-- Membership in the identity component can be tested using the image of any
point of the one-point base. -/
lemma Scheme.mem_identityComponent_iff (G : Over S) [GrpObj G]
    [LocallyConnectedSpace G.left] [Nonempty S] [Subsingleton S]
    (x : G.left) (s : S) :
    x ∈ Scheme.identityComponent G ↔ x ∈ connectedComponent (η[G].left s) := by
  change x ∈ connectedComponent
    (η[G].left (Classical.choice (inferInstance : Nonempty S))) ↔ _
  rw [Subsingleton.elim s (Classical.choice (inferInstance : Nonempty S))]

/-- The identity component, equipped with its composite structure morphism to
the base. -/
noncomputable abbrev Scheme.identityComponentOver (G : Over S) [GrpObj G]
    [LocallyConnectedSpace G.left] [Nonempty S] [Subsingleton S] : Over S :=
  Over.mk ((Scheme.identityComponent G).ι ≫ G.hom)

/-- The canonical inclusion of the identity component into the group scheme. -/
noncomputable abbrev Scheme.identityComponentι (G : Over S) [GrpObj G]
    [LocallyConnectedSpace G.left] [Nonempty S] [Subsingleton S] :
    Scheme.identityComponentOver G ⟶ G :=
  Over.homMk (Scheme.identityComponent G).ι

/-- The identity-component inclusion is a monomorphism. -/
instance Scheme.identityComponentι_mono (G : Over S) [GrpObj G]
    [LocallyConnectedSpace G.left] [Nonempty S] [Subsingleton S] :
    Mono (Scheme.identityComponentι G) := by
  let _ : Mono (Scheme.identityComponent G).ι := by infer_instance
  exact Over.mono_of_mono_left _

/-- The underlying morphism of the identity-component inclusion is an open
immersion. -/
instance Scheme.identityComponentι_isOpenImmersion (G : Over S) [GrpObj G]
    [LocallyConnectedSpace G.left] [Nonempty S] [Subsingleton S] :
    IsOpenImmersion (Scheme.identityComponentι G).left := by
  change IsOpenImmersion (Scheme.identityComponent G).ι
  infer_instance

/-- The underlying morphism of the identity-component inclusion is also a
closed immersion. -/
instance Scheme.identityComponentι_isClosedImmersion (G : Over S) [GrpObj G]
    [LocallyConnectedSpace G.left] [Nonempty S] [Subsingleton S] :
    IsClosedImmersion (Scheme.identityComponentι G).left := by
  apply IsClosedImmersion.of_isPreimmersion
  rw [show (Scheme.identityComponentι G).left =
    (Scheme.identityComponent G).ι from rfl, Scheme.Opens.range_ι]
  exact isClosed_connectedComponent

/-- The identity component is connected. -/
instance Scheme.identityComponent_connectedSpace (G : Over S) [GrpObj G]
    [LocallyConnectedSpace G.left] [Nonempty S] [Subsingleton S] :
    ConnectedSpace (Scheme.identityComponentOver G).left := by
  change ConnectedSpace (Scheme.identityComponent G : Set G.left)
  exact isConnected_iff_connectedSpace.mp isConnected_connectedComponent

/-- An identity component of a reduced group scheme is reduced. -/
instance Scheme.identityComponent_isReduced (G : Over S) [GrpObj G]
    [LocallyConnectedSpace G.left] [Nonempty S] [Subsingleton S] [IsReduced G.left] :
    IsReduced (Scheme.identityComponentOver G).left := by
  change IsReduced (Scheme.identityComponent G).toScheme
  infer_instance

private lemma Scheme.range_unit_subset_identityComponent (G : Over S) [GrpObj G]
    [LocallyConnectedSpace G.left] [Nonempty S] [Subsingleton S] :
    Set.range η[G].left ⊆ Set.range (Scheme.identityComponent G).ι := by
  rintro _ ⟨s, rfl⟩
  change S at s
  let s₀ : S := Classical.choice (inferInstance : Nonempty S)
  refine ⟨⟨η[G].left s, ?_⟩, rfl⟩
  change η[G].left s ∈ connectedComponent (η[G].left s₀)
  rw [Subsingleton.elim s s₀]
  exact mem_connectedComponent

/-- The unit section factors through the identity component. -/
noncomputable def Scheme.identityComponentOne (G : Over S) [GrpObj G]
    [LocallyConnectedSpace G.left] [Nonempty S] [Subsingleton S] :
    𝟙_ (Over S) ⟶ Scheme.identityComponentOver G :=
  Over.homMk (IsOpenImmersion.lift (Scheme.identityComponent G).ι η[G].left
    (Scheme.range_unit_subset_identityComponent G)) (by
      rw [show (Scheme.identityComponentOver G).hom =
        (Scheme.identityComponent G).ι ≫ G.hom from rfl,
        IsOpenImmersion.lift_fac_assoc]
      exact η[G].w)

/-- Composing the restricted unit with the inclusion recovers the original
unit. -/
@[reassoc]
lemma Scheme.identityComponentOne_comp_ι (G : Over S) [GrpObj G]
    [LocallyConnectedSpace G.left] [Nonempty S] [Subsingleton S] :
    Scheme.identityComponentOne G ≫ Scheme.identityComponentι G = η[G] := by
  ext
  exact IsOpenImmersion.lift_fac _ _ _

private lemma Scheme.range_mul_subset_identityComponent (G : Over S) [GrpObj G]
    [LocallyConnectedSpace G.left] [Nonempty S] [Subsingleton S]
    [ConnectedSpace ((Scheme.identityComponentOver G ⊗
      Scheme.identityComponentOver G).left)] :
    Set.range (((Scheme.identityComponentι G ⊗ₘ Scheme.identityComponentι G) ≫ μ[G]).left) ⊆
      Set.range (Scheme.identityComponent G).ι := by
  let H := Scheme.identityComponentOver G
  let i : H ⟶ G := Scheme.identityComponentι G
  let one : 𝟙_ (Over S) ⟶ H := Scheme.identityComponentOne G
  let f : H ⊗ H ⟶ G := (i ⊗ₘ i) ≫ μ[G]
  let aMap : 𝟙_ (Over S) ⟶ H ⊗ H := lift one one
  have one_i : one ≫ i = η[G] := Scheme.identityComponentOne_comp_ι G
  have aMap_f : aMap ≫ f = η[G] := by
    dsimp only [aMap, f]
    rw [← Category.assoc, lift_map, one_i]
    simpa using MonObj.lift_comp_one_right (η[G]) (𝟙 (𝟙_ (Over S)))
  let s₀ : S := Classical.choice (inferInstance : Nonempty S)
  let a : (H ⊗ H).left := aMap.left s₀
  have fa : f.left a = η[G].left s₀ := by
    change (aMap ≫ f).left s₀ = η[G].left s₀
    rw [aMap_f]
  rintro _ ⟨x, rfl⟩
  refine ⟨⟨f.left x, ?_⟩, rfl⟩
  change f.left x ∈ connectedComponent (η[G].left s₀)
  rw [← fa]
  exact f.left.continuous.mapsTo_connectedComponent a (by
    rw [PreconnectedSpace.connectedComponent_eq_univ]
    exact Set.mem_univ x)

/-- Multiplication restricts to the identity component when its Cartesian
square is connected. -/
noncomputable def Scheme.identityComponentMul (G : Over S) [GrpObj G]
    [LocallyConnectedSpace G.left] [Nonempty S] [Subsingleton S]
    [ConnectedSpace ((Scheme.identityComponentOver G ⊗
      Scheme.identityComponentOver G).left)] :
    Scheme.identityComponentOver G ⊗ Scheme.identityComponentOver G ⟶
      Scheme.identityComponentOver G :=
  Over.homMk (IsOpenImmersion.lift (Scheme.identityComponent G).ι
    (((Scheme.identityComponentι G ⊗ₘ Scheme.identityComponentι G) ≫ μ[G]).left)
    (Scheme.range_mul_subset_identityComponent G)) (by
      rw [show (Scheme.identityComponentOver G).hom =
        (Scheme.identityComponent G).ι ≫ G.hom from rfl,
        ← Category.assoc, IsOpenImmersion.lift_fac]
      exact ((Scheme.identityComponentι G ⊗ₘ Scheme.identityComponentι G) ≫ μ[G]).w)

/-- Composing the restricted multiplication with the inclusion recovers the
original multiplication on the component square. -/
@[reassoc]
lemma Scheme.identityComponentMul_comp_ι (G : Over S) [GrpObj G]
    [LocallyConnectedSpace G.left] [Nonempty S] [Subsingleton S]
    [ConnectedSpace ((Scheme.identityComponentOver G ⊗
      Scheme.identityComponentOver G).left)] :
    Scheme.identityComponentMul G ≫ Scheme.identityComponentι G =
      (Scheme.identityComponentι G ⊗ₘ Scheme.identityComponentι G) ≫ μ[G] := by
  ext
  exact IsOpenImmersion.lift_fac _ _ _

private lemma Scheme.range_inv_subset_identityComponent (G : Over S) [GrpObj G]
    [LocallyConnectedSpace G.left] [Nonempty S] [Subsingleton S] :
    Set.range ((Scheme.identityComponentι G ≫ ι[G]).left) ⊆
      Set.range (Scheme.identityComponent G).ι := by
  let H := Scheme.identityComponentOver G
  let i : H ⟶ G := Scheme.identityComponentι G
  let one : 𝟙_ (Over S) ⟶ H := Scheme.identityComponentOne G
  let f : H ⟶ G := i ≫ ι[G]
  have one_i : one ≫ i = η[G] := Scheme.identityComponentOne_comp_ι G
  have one_f : one ≫ f = η[G] := by
    dsimp only [f]
    rw [← Category.assoc, one_i, GrpObj.one_inv]
  let s₀ : S := Classical.choice (inferInstance : Nonempty S)
  let a : H.left := one.left s₀
  have fa : f.left a = η[G].left s₀ := by
    change (one ≫ f).left s₀ = η[G].left s₀
    rw [one_f]
  rintro _ ⟨x, rfl⟩
  refine ⟨⟨f.left x, ?_⟩, rfl⟩
  change f.left x ∈ connectedComponent (η[G].left s₀)
  rw [← fa]
  exact f.left.continuous.mapsTo_connectedComponent a (by
    rw [PreconnectedSpace.connectedComponent_eq_univ]
    exact Set.mem_univ x)

/-- Inversion restricts to the identity component. -/
noncomputable def Scheme.identityComponentInv (G : Over S) [GrpObj G]
    [LocallyConnectedSpace G.left] [Nonempty S] [Subsingleton S] :
    Scheme.identityComponentOver G ⟶ Scheme.identityComponentOver G :=
  Over.homMk (IsOpenImmersion.lift (Scheme.identityComponent G).ι
    (Scheme.identityComponentι G ≫ ι[G]).left
    (Scheme.range_inv_subset_identityComponent G)) (by
      rw [show (Scheme.identityComponentOver G).hom =
        (Scheme.identityComponent G).ι ≫ G.hom from rfl,
        ← Category.assoc, IsOpenImmersion.lift_fac]
      exact (Scheme.identityComponentι G ≫ ι[G]).w)

/-- Composing restricted inversion with the inclusion recovers the original
inversion on the identity component. -/
@[reassoc]
lemma Scheme.identityComponentInv_comp_ι (G : Over S) [GrpObj G]
    [LocallyConnectedSpace G.left] [Nonempty S] [Subsingleton S] :
    Scheme.identityComponentInv G ≫ Scheme.identityComponentι G =
      Scheme.identityComponentι G ≫ ι[G] := by
  ext
  exact IsOpenImmersion.lift_fac _ _ _

/-- The identity component is a group scheme when its Cartesian square is
connected. -/
noncomputable instance Scheme.identityComponent_grpObj (G : Over S) [GrpObj G]
    [LocallyConnectedSpace G.left] [Nonempty S] [Subsingleton S]
    [ConnectedSpace ((Scheme.identityComponentOver G ⊗
      Scheme.identityComponentOver G).left)] :
    GrpObj (Scheme.identityComponentOver G) := by
  let i := Scheme.identityComponentι G
  let one := Scheme.identityComponentOne G
  let mul := Scheme.identityComponentMul G
  let inv := Scheme.identityComponentInv G
  have one_i : one ≫ i = η[G] := Scheme.identityComponentOne_comp_ι G
  have mul_i : mul ≫ i = (i ⊗ₘ i) ≫ μ[G] := Scheme.identityComponentMul_comp_ι G
  have inv_i : inv ≫ i = i ≫ ι[G] := Scheme.identityComponentInv_comp_ι G
  letI : MonObj (Scheme.identityComponentOver G) :=
    { one := one
      mul := mul
      one_mul := by
        apply (cancel_mono i).1
        rw [Category.assoc, mul_i, ← tensorHom_id, tensorHom_comp_tensorHom_assoc,
          Category.id_comp, one_i]
        rw [← Category.id_comp η[G], ← Category.comp_id i]
        rw [← tensorHom_comp_tensorHom_assoc (𝟙 (𝟙_ (Over S))) i η[G] (𝟙 G) μ[G]]
        simp
      mul_one := by
        apply (cancel_mono i).1
        rw [Category.assoc, mul_i, ← id_tensorHom, tensorHom_comp_tensorHom_assoc,
          Category.id_comp, one_i]
        rw [← Category.comp_id i, ← Category.id_comp η[G]]
        rw [← tensorHom_comp_tensorHom_assoc i (𝟙 (𝟙_ (Over S))) (𝟙 G) η[G] μ[G]]
        simp
      mul_assoc := by
        apply (cancel_mono i).1
        simp only [Category.assoc, mul_i]
        calc
          mul ▷ Scheme.identityComponentOver G ≫ (i ⊗ₘ i) ≫ μ[G] =
              ((i ⊗ₘ i) ⊗ₘ i) ≫ (μ[G] ▷ G) ≫ μ[G] := by
            rw [← tensorHom_id, tensorHom_comp_tensorHom_assoc, Category.id_comp, mul_i]
            simpa only [Category.comp_id, tensorHom_id, Category.assoc] using
              (tensorHom_comp_tensorHom_assoc (i ⊗ₘ i) i μ[G] (𝟙 G) μ[G]).symm
          _ = ((i ⊗ₘ i) ⊗ₘ i) ≫ (α_ G G G).hom ≫ (G ◁ μ[G]) ≫ μ[G] := by
            rw [MonObj.mul_assoc]
          _ = (α_ (Scheme.identityComponentOver G) (Scheme.identityComponentOver G)
                (Scheme.identityComponentOver G)).hom ≫
              (i ⊗ₘ (i ⊗ₘ i)) ≫ (G ◁ μ[G]) ≫ μ[G] := by
            rw [associator_naturality_assoc]
          _ = (α_ (Scheme.identityComponentOver G) (Scheme.identityComponentOver G)
                (Scheme.identityComponentOver G)).hom ≫
              Scheme.identityComponentOver G ◁ mul ≫ (i ⊗ₘ i) ≫ μ[G] := by
            have hright : Scheme.identityComponentOver G ◁ mul ≫ (i ⊗ₘ i) ≫ μ[G] =
                (i ⊗ₘ (i ⊗ₘ i)) ≫ (G ◁ μ[G]) ≫ μ[G] := by
              rw [← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.id_comp, mul_i]
              simpa only [Category.comp_id, id_tensorHom, Category.assoc] using
                (tensorHom_comp_tensorHom_assoc i (i ⊗ₘ i) (𝟙 G) μ[G] μ[G]).symm
            simp only [hright] }
  exact
    { inv := inv
      left_inv := by
        apply (cancel_mono i).1
        change (lift inv (𝟙 _) ≫ mul) ≫ i = (toUnit _ ≫ one) ≫ i
        rw [Category.assoc, mul_i, ← Category.assoc, lift_map]
        simp [inv_i, one_i]
      right_inv := by
        apply (cancel_mono i).1
        change (lift (𝟙 _) inv ≫ mul) ≫ i = (toUnit _ ≫ one) ≫ i
        rw [Category.assoc, mul_i, ← Category.assoc, lift_map]
        simp [inv_i, one_i] }

/-- The identity-component inclusion is a monoid-object homomorphism. -/
instance Scheme.identityComponentι_isMonHom (G : Over S) [GrpObj G]
    [LocallyConnectedSpace G.left] [Nonempty S] [Subsingleton S]
    [ConnectedSpace ((Scheme.identityComponentOver G ⊗
      Scheme.identityComponentOver G).left)] :
    IsMonHom (Scheme.identityComponentι G) where
  one_hom := Scheme.identityComponentOne_comp_ι G
  mul_hom := Scheme.identityComponentMul_comp_ι G

private lemma Scheme.range_conj_subset_identityComponent (G : Over S) [GrpObj G]
    [LocallyConnectedSpace G.left] [Nonempty S] [Subsingleton S]
    [ConnectedSpace ((Scheme.identityComponentOver G ⊗
      Scheme.identityComponentOver G).left)]
    [GeometricallyConnected (Scheme.identityComponentOver G).hom] :
    Set.range ((G ◁ Scheme.identityComponentι G ≫ GrpObj.conj G).left) ⊆
      Set.range (Scheme.identityComponent G).ι := by
  let H := Scheme.identityComponentOver G
  let i : H ⟶ G := Scheme.identityComponentι G
  let one : 𝟙_ (Over S) ⟶ H := Scheme.identityComponentOne G
  let p : G ⊗ H ⟶ G := fst G H
  let e : G ⟶ G ⊗ H := lift (𝟙 G) (toUnit G ≫ one)
  let f : G ⊗ H ⟶ G := G ◁ i ≫ GrpObj.conj G
  have one_i : one ≫ i = η[G] := Scheme.identityComponentOne_comp_ι G
  have e_f : e ≫ f = toUnit G ≫ η[G] := by
    dsimp only [e, f]
    rw [← id_tensorHom, ← Category.assoc, lift_map]
    simp [one_i, ← Hom.one_def]
  let _ : GeometricallyConnected p.left := by
    change GeometricallyConnected (pullback.fst G.hom H.hom)
    infer_instance
  let s₀ : S := Classical.choice (inferInstance : Nonempty S)
  rintro _ ⟨x, rfl⟩
  let g : G.left := p.left x
  let a : (G ⊗ H).left := e.left g
  have hx : x ∈ p.left ⁻¹' {g} := by
    simp [g]
  have ha : a ∈ p.left ⁻¹' {g} := by
    change p.left (e.left g) = g
    change (e ≫ p).left g = g
    simp [e, p]
  have hxa : x ∈ connectedComponent a :=
    (p.left.isConnected_preimage_singleton g).subset_connectedComponent ha hx
  have hfa : f.left a = η[G].left s₀ := by
    change (e ≫ f).left g = η[G].left s₀
    rw [e_f]
    change η[G].left (G.hom g) = η[G].left s₀
    rw [Subsingleton.elim (G.hom g) s₀]
  refine ⟨⟨f.left x, ?_⟩, rfl⟩
  change f.left x ∈ connectedComponent (η[G].left s₀)
  rw [← hfa]
  exact f.left.continuous.mapsTo_connectedComponent a hxa

/-- Conjugation on the identity component, assuming that the component is
geometrically connected over the base. -/
noncomputable def Scheme.identityComponentConj (G : Over S) [GrpObj G]
    [LocallyConnectedSpace G.left] [Nonempty S] [Subsingleton S]
    [ConnectedSpace ((Scheme.identityComponentOver G ⊗
      Scheme.identityComponentOver G).left)]
    [GeometricallyConnected (Scheme.identityComponentOver G).hom] :
    G ⊗ Scheme.identityComponentOver G ⟶ Scheme.identityComponentOver G :=
  Over.homMk (IsOpenImmersion.lift (Scheme.identityComponent G).ι
    (G ◁ Scheme.identityComponentι G ≫ GrpObj.conj G).left
    (Scheme.range_conj_subset_identityComponent G)) (by
      rw [show (Scheme.identityComponentOver G).hom =
        (Scheme.identityComponent G).ι ≫ G.hom from rfl,
        ← Category.assoc, IsOpenImmersion.lift_fac]
      exact (G ◁ Scheme.identityComponentι G ≫ GrpObj.conj G).w)

/-- Composing restricted conjugation with the identity-component inclusion
recovers ambient conjugation on the component. -/
@[reassoc]
lemma Scheme.identityComponentConj_comp_ι (G : Over S) [GrpObj G]
    [LocallyConnectedSpace G.left] [Nonempty S] [Subsingleton S]
    [ConnectedSpace ((Scheme.identityComponentOver G ⊗
      Scheme.identityComponentOver G).left)]
    [GeometricallyConnected (Scheme.identityComponentOver G).hom] :
    Scheme.identityComponentConj G ≫ Scheme.identityComponentι G =
      G ◁ Scheme.identityComponentι G ≫ GrpObj.conj G := by
  ext
  exact IsOpenImmersion.lift_fac _ _ _

/-- A geometrically connected identity component is a normal subgroup scheme
of the ambient group scheme. -/
instance Scheme.identityComponentι_normal (G : Over S) [GrpObj G]
    [LocallyConnectedSpace G.left] [Nonempty S] [Subsingleton S]
    [ConnectedSpace ((Scheme.identityComponentOver G ⊗
      Scheme.identityComponentOver G).left)]
    [GeometricallyConnected (Scheme.identityComponentOver G).hom] :
    IsMonHom.Normal (Scheme.identityComponentι G) where
  exists_comp_eq_conj := ⟨Scheme.identityComponentConj G,
    Scheme.identityComponentConj_comp_ι G⟩

end AlgebraicGeometry
