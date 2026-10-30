/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupObject.FunctorCategory
public import AlgebraicGroups.GroupScheme.FiniteTypePoints

/-!
# Recovering group schemes from pointwise subgroups

An injective map from a representable locally-finite-type functor of points to
the functor of points of a group scheme induces a group-object structure on the
representing scheme when every component range is a subgroup. The original map,
not merely an abstractly isomorphic replacement, is then a group-object
homomorphism.

The generic constructions work for locally-finite-type schemes and an
injective natural transformation with subgroup ranges on finitely generated
algebras. For a finite-type subscheme these data give the subgroup criterion
of Milne's item 1.5; an immersion is not required by the generic construction.

## Main definitions

- `AlgebraicGeometry.pointwiseSubgroupGrpObj`
- `AlgebraicGeometry.groupOfPointwiseSubgroup`
- `AlgebraicGeometry.pointwiseSubgroupIsMonHom`
- `AlgebraicGeometry.pointwiseSubgroupHom`
- `AlgebraicGeometry.algebraicGroupOfPointwiseSubgroup`
- `AlgebraicGeometry.algebraicPointwiseSubgroupHom`

## References

- James S. Milne, *Algebraic Groups* (2017), items 1.4–1.5 and
  Appendix A.33: recovering the group law and subgroup homomorphism from
  pointwise subgroups by restricted Yoneda full faithfulness.
- `SchemeProperties.FiniteTypePoints`, `lftPointsFullyFaithful` and
  `lftPointsPreservesFiniteLimits`: the separately developed restricted
  functor of points and its finite-limit preservation.
- Mathlib, `Functor.FullyFaithful.grpObj` and
  `Functor.FullyFaithful.isMonHom_preimage`: reflection of the group-object
  structure and its homomorphism through a fully faithful monoidal functor.

The subgroup transport also uses `NatTrans.IsPointwiseSubgroup.grpObj` and
`NatTrans.IsPointwiseSubgroup.isMonHom` from
`AlgebraicGroups.GroupObject.FunctorCategory`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite MonoidalCategory MonObj

universe u

namespace AlgebraicGeometry

variable (K : Type u) [Field K]

/-- The set-valued functor of points of a locally-finite-type scheme, evaluated
on finitely generated algebras. -/
abbrev lftPoints :=
  Presheaf.restrictedULiftYoneda.{0} (finiteAlgSpecOver K)

local instance : Limits.PreservesFiniteLimits (lftPoints K) :=
  lftPointsPreservesFiniteLimits K

/-- The Cartesian monoidal structure on schemes locally of finite type over `K`,
built from their finite products. -/
local instance instCartesianMonoidalCategoryLocallyFiniteTypeOver : CartesianMonoidalCategory
    (locallyFiniteTypeMorphism.Over ⊤ (Spec (.of K))) :=
  .ofHasFiniteProducts

-- Generate the unwrappable legacy name as an ordinary transparent, noninstance alias.
run_cmd do
  let legacy := Lean.mkIdent <| Lean.Name.mkSimple
    ("instCartesianMonoidalCategoryOverSchemeLocallyFiniteTypeMorphism" ++
      "TopMorphismPropertySpecOf_algebraicGroups")
  let replacement := Lean.mkIdent ``instCartesianMonoidalCategoryLocallyFiniteTypeOver
  Lean.Elab.Command.elabCommand (← `(command|
    @[inherit_doc $replacement, deprecated $replacement (since := "2026-10-26"),
      nolint defsWithUnderscore]
    public noncomputable abbrev $legacy := @$replacement))

/-- The monoidal structure on `lftPoints K` induced by preservation of finite products. -/
local instance : (lftPoints K).Monoidal :=
  Functor.Monoidal.ofChosenFiniteProducts _

/-- A pointwise subgroup of the functor of points of a group scheme induces a
group-object structure on its representing locally-finite-type scheme. The
finite-type subscheme case follows Milne, *Algebraic Groups* (2017), item 1.5;
the reflection uses full faithfulness from `SchemeProperties.FiniteTypePoints`. -/
abbrev pointwiseSubgroupGrpObj
    (X : locallyFiniteTypeMorphism.Over ⊤ (Spec (.of K)))
    (G : Grp (locallyFiniteTypeMorphism.Over ⊤ (Spec (.of K))))
    (i : X ⟶ G.X)
    (h : NatTrans.IsPointwiseSubgroup
      (G := Monoidal.GrpFunctorCategory.pointwiseGrp ((lftGroupPoints K).obj G))
      ((lftPoints K).map i)) : GrpObj X := by
  letI : GrpObj ((lftPoints K).obj X) := h.grpObj
  exact (lftPointsFullyFaithful K).grpObj X

/-- The representing scheme equipped with the group law transported from its
pointwise subgroup structure by `pointwiseSubgroupGrpObj`. -/
def groupOfPointwiseSubgroup
    (X : locallyFiniteTypeMorphism.Over ⊤ (Spec (.of K)))
    (G : Grp (locallyFiniteTypeMorphism.Over ⊤ (Spec (.of K))))
    (i : X ⟶ G.X)
    (h : NatTrans.IsPointwiseSubgroup
      (G := Monoidal.GrpFunctorCategory.pointwiseGrp ((lftGroupPoints K).obj G))
      ((lftPoints K).map i)) :
    Grp (locallyFiniteTypeMorphism.Over ⊤ (Spec (.of K))) := by
  letI : GrpObj X := pointwiseSubgroupGrpObj K X G i h
  exact ⟨X⟩

/-- The transported group has exactly the given representing scheme. -/
@[simp] theorem groupOfPointwiseSubgroup_X
    (X : locallyFiniteTypeMorphism.Over ⊤ (Spec (.of K)))
    (G : Grp (locallyFiniteTypeMorphism.Over ⊤ (Spec (.of K))))
    (i : X ⟶ G.X)
    (h : NatTrans.IsPointwiseSubgroup
      (G := Monoidal.GrpFunctorCategory.pointwiseGrp ((lftGroupPoints K).obj G))
      ((lftPoints K).map i)) :
    (groupOfPointwiseSubgroup K X G i h).X = X := rfl

/-- The bundled group stores the same group-object data as the transport. -/
@[simp] theorem groupOfPointwiseSubgroup_grp
    (X : locallyFiniteTypeMorphism.Over ⊤ (Spec (.of K)))
    (G : Grp (locallyFiniteTypeMorphism.Over ⊤ (Spec (.of K))))
    (i : X ⟶ G.X)
    (h : NatTrans.IsPointwiseSubgroup
      (G := Monoidal.GrpFunctorCategory.pointwiseGrp ((lftGroupPoints K).obj G))
      ((lftPoints K).map i)) :
    (groupOfPointwiseSubgroup K X G i h).grp = pointwiseSubgroupGrpObj K X G i h := rfl

/-- For the group structure induced by `pointwiseSubgroupGrpObj`, the original
map to the target group scheme is a group-object homomorphism. For finite-type
subschemes this is the homomorphism assertion in Milne, *Algebraic Groups*
(2017), item 1.5. -/
theorem pointwiseSubgroupIsMonHom
    (X : locallyFiniteTypeMorphism.Over ⊤ (Spec (.of K)))
    (G : Grp (locallyFiniteTypeMorphism.Over ⊤ (Spec (.of K))))
    (i : X ⟶ G.X)
    (h : NatTrans.IsPointwiseSubgroup
      (G := Monoidal.GrpFunctorCategory.pointwiseGrp ((lftGroupPoints K).obj G))
      ((lftPoints K).map i)) :
    @IsMonHom
      (locallyFiniteTypeMorphism.Over ⊤ (Spec (.of K)))
      inferInstance inferInstance
      (groupOfPointwiseSubgroup K X G i h).X G.X
      (groupOfPointwiseSubgroup K X G i h).grp.toMonObj
      G.grp.toMonObj i := by
  let _ : GrpObj X := pointwiseSubgroupGrpObj K X G i h
  have hpOne := by
    letI : GrpObj ((lftPoints K).obj X) := h.grpObj
    letI : GrpObj ((lftPoints K).obj G.X) := ((lftGroupPoints K).obj G).grp
    letI : IsMonHom ((lftPoints K).map i) := h.isMonHom
    exact IsMonHom.one_hom ((lftPoints K).map i)
  have hpMul := by
    letI : GrpObj ((lftPoints K).obj X) := h.grpObj
    letI : GrpObj ((lftPoints K).obj G.X) := ((lftGroupPoints K).obj G).grp
    letI : IsMonHom ((lftPoints K).map i) := h.isMonHom
    exact IsMonHom.mul_hom ((lftPoints K).map i)
  let _ : GrpObj ((lftPoints K).obj X) :=
    Functor.grpObjObj (F := lftPoints K) (G := X)
  let _ : GrpObj ((lftPoints K).obj G.X) :=
    Functor.grpObjObj (F := lftPoints K) (G := G.X)
  let hF := lftPointsFullyFaithful K
  have sourceOne_eq :
      (η : 𝟙_ ((FGAlgCat K)ᵒᵖᵒᵖ ⥤ Type u) ⟶ (lftPoints K).obj X) =
        (letI : GrpObj ((lftPoints K).obj X) := h.grpObj; η) := by
    change Functor.LaxMonoidal.ε (lftPoints K) ≫
      (lftPoints K).map
        (hF.preimage (Functor.OplaxMonoidal.η (lftPoints K) ≫ _)) = _
    rw [hF.map_preimage]
    simp
  have targetOne_eq :
      (η : 𝟙_ ((FGAlgCat K)ᵒᵖᵒᵖ ⥤ Type u) ⟶ (lftPoints K).obj G.X) =
        (letI : GrpObj ((lftPoints K).obj G.X) := ((lftGroupPoints K).obj G).grp;
          η) := rfl
  have sourceMul_eq :
      (μ : (lftPoints K).obj X ⊗ (lftPoints K).obj X ⟶ (lftPoints K).obj X) =
        (letI : GrpObj ((lftPoints K).obj X) := h.grpObj; μ) := by
    change Functor.LaxMonoidal.μ (lftPoints K) X X ≫
      (lftPoints K).map
        (hF.preimage (Functor.OplaxMonoidal.δ (lftPoints K) X X ≫ _)) = _
    rw [hF.map_preimage]
    simp
  have targetMul_eq :
      (μ : (lftPoints K).obj G.X ⊗ (lftPoints K).obj G.X ⟶
        (lftPoints K).obj G.X) =
        (letI : GrpObj ((lftPoints K).obj G.X) := ((lftGroupPoints K).obj G).grp;
          μ) := rfl
  let _ : IsMonHom ((lftPoints K).map i) :=
    { one_hom := by
        rw [sourceOne_eq, targetOne_eq]
        exact hpOne
      mul_hom := by
        rw [sourceMul_eq, targetMul_eq]
        exact hpMul }
  have hpre : IsMonHom (hF.preimage ((lftPoints K).map i)) :=
    hF.isMonHom_preimage (X := X) (Y := G.X) ((lftPoints K).map i)
  rw [hF.preimage_map i] at hpre
  exact hpre

/-- The original map, as a homomorphism from the transported group scheme. -/
def pointwiseSubgroupHom
    (X : locallyFiniteTypeMorphism.Over ⊤ (Spec (.of K)))
    (G : Grp (locallyFiniteTypeMorphism.Over ⊤ (Spec (.of K))))
    (i : X ⟶ G.X)
    (h : NatTrans.IsPointwiseSubgroup
      (G := Monoidal.GrpFunctorCategory.pointwiseGrp ((lftGroupPoints K).obj G))
      ((lftPoints K).map i)) : groupOfPointwiseSubgroup K X G i h ⟶ G :=
  ⟨{ hom := i, isMonHom_hom := pointwiseSubgroupIsMonHom K X G i h }⟩

/-- The bundled homomorphism has exactly the original underlying map. -/
@[simp] theorem pointwiseSubgroupHom_hom_hom
    (X : locallyFiniteTypeMorphism.Over ⊤ (Spec (.of K)))
    (G : Grp (locallyFiniteTypeMorphism.Over ⊤ (Spec (.of K))))
    (i : X ⟶ G.X)
    (h : NatTrans.IsPointwiseSubgroup
      (G := Monoidal.GrpFunctorCategory.pointwiseGrp ((lftGroupPoints K).obj G))
      ((lftPoints K).map i)) : (pointwiseSubgroupHom K X G i h).hom.hom = i := rfl

/-- Restricted points of the bundled homomorphism are the original natural map. -/
@[simp] theorem pointwiseSubgroupHom_points
    (X : locallyFiniteTypeMorphism.Over ⊤ (Spec (.of K)))
    (G : Grp (locallyFiniteTypeMorphism.Over ⊤ (Spec (.of K))))
    (i : X ⟶ G.X)
    (h : NatTrans.IsPointwiseSubgroup
      (G := Monoidal.GrpFunctorCategory.pointwiseGrp ((lftGroupPoints K).obj G))
      ((lftPoints K).map i)) :
    ((lftGroupPoints K).map (pointwiseSubgroupHom K X G i h)).hom.hom =
      (lftPoints K).map i := rfl

/-- On each finitely generated algebra the homomorphism sends a point by `i`. -/
theorem pointwiseSubgroupHom_points_app
    (X : locallyFiniteTypeMorphism.Over ⊤ (Spec (.of K)))
    (G : Grp (locallyFiniteTypeMorphism.Over ⊤ (Spec (.of K))))
    (i : X ⟶ G.X)
    (h : NatTrans.IsPointwiseSubgroup
      (G := Monoidal.GrpFunctorCategory.pointwiseGrp ((lftGroupPoints K).obj G))
      ((lftPoints K).map i))
    (A : (FGAlgCat K)ᵒᵖᵒᵖ) (x : ((lftPoints K).obj X).obj A) :
    (((lftGroupPoints K).map (pointwiseSubgroupHom K X G i h)).hom.hom.app A) x =
      ((lftPoints K).map i).app A x := rfl

/-- A finite-type scheme whose point functor maps injectively onto pointwise
subgroups of a finite-type group scheme becomes a finite-type group scheme on
the same underlying represented object. This is the pointwise subgroup
criterion of Milne, *Algebraic Groups* (2017), item 1.5, without requiring
an immersion in this criterion. -/
abbrev algebraicGroupOfPointwiseSubgroup
    (X : algebraicOver K) (G : algebraicGroupOver K) (i : X.obj ⟶ G.obj.X)
    (h : NatTrans.IsPointwiseSubgroup
      (G := Monoidal.GrpFunctorCategory.pointwiseGrp
        ((lftGroupPoints K).obj G.obj))
      ((lftPoints K).map i)) : algebraicGroupOver K := by
  letI : GrpObj X.obj := pointwiseSubgroupGrpObj K X.obj G.obj i h
  exact ⟨⟨X.obj⟩, X.property⟩

/-- Forgetting the finite-type property gives the same transported group. -/
@[simp] theorem algebraicGroupOfPointwiseSubgroup_obj
    (X : algebraicOver K) (G : algebraicGroupOver K) (i : X.obj ⟶ G.obj.X)
    (h : NatTrans.IsPointwiseSubgroup
      (G := Monoidal.GrpFunctorCategory.pointwiseGrp
        ((lftGroupPoints K).obj G.obj))
      ((lftPoints K).map i)) :
    (algebraicGroupOfPointwiseSubgroup K X G i h).obj =
      groupOfPointwiseSubgroup K X.obj G.obj i h := rfl

/-- The original map as a homomorphism of finite-type group schemes. -/
def algebraicPointwiseSubgroupHom
    (X : algebraicOver K) (G : algebraicGroupOver K) (i : X.obj ⟶ G.obj.X)
    (h : NatTrans.IsPointwiseSubgroup
      (G := Monoidal.GrpFunctorCategory.pointwiseGrp
        ((lftGroupPoints K).obj G.obj))
      ((lftPoints K).map i)) : algebraicGroupOfPointwiseSubgroup K X G i h ⟶ G :=
  ⟨pointwiseSubgroupHom K X.obj G.obj i h⟩

/-- The finite-type homomorphism has the same underlying group homomorphism. -/
@[simp] theorem algebraicPointwiseSubgroupHom_hom
    (X : algebraicOver K) (G : algebraicGroupOver K) (i : X.obj ⟶ G.obj.X)
    (h : NatTrans.IsPointwiseSubgroup
      (G := Monoidal.GrpFunctorCategory.pointwiseGrp
        ((lftGroupPoints K).obj G.obj))
      ((lftPoints K).map i)) :
    (algebraicPointwiseSubgroupHom K X G i h).hom =
      pointwiseSubgroupHom K X.obj G.obj i h := rfl

/-- In the finite-type specialization, the original map to the target group
scheme is the homomorphism for the recovered group structure, as in Milne,
*Algebraic Groups* (2017), item 1.5. -/
theorem algebraicPointwiseSubgroupIsMonHom
    (X : algebraicOver K) (G : algebraicGroupOver K) (i : X.obj ⟶ G.obj.X)
    (h : NatTrans.IsPointwiseSubgroup
      (G := Monoidal.GrpFunctorCategory.pointwiseGrp
        ((lftGroupPoints K).obj G.obj))
      ((lftPoints K).map i)) :
    @IsMonHom
      (locallyFiniteTypeMorphism.Over ⊤ (Spec (.of K)))
      inferInstance inferInstance
      (groupOfPointwiseSubgroup K X.obj G.obj i h).X G.obj.X
      (groupOfPointwiseSubgroup K X.obj G.obj i h).grp.toMonObj
      G.obj.grp.toMonObj i :=
  (algebraicPointwiseSubgroupHom K X G i h).hom.hom.isMonHom_hom

end AlgebraicGeometry
