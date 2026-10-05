/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.FiniteTypePoints
public import AlgebraicGroups.GroupScheme.Separated
public import AlgebraicGroups.Scheme.GeometricallyReduced
public import Mathlib.AlgebraicGeometry.Group.Abelian
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Internal.Types.Basic

/-!
# Commutativity criteria for group schemes

This file shows that commutativity of a finite-type group scheme over a field can be detected on
its points over finitely generated algebras. For geometrically reduced group schemes, points over
one separably closed extension field suffice.

The all-algebra criterion uses finitely generated algebras, not just fields.
The single-field criterion additionally assumes geometric reducedness and
local finite type; it does not apply to arbitrary group schemes.

## Main results

- `AlgebraicGeometry.isCommMonObj_iff_finiteAlg_points_commutative`
- `AlgebraicGeometry.isCommMonObj_iff_isMulCommutative_fieldValuedPoints`

## References

- James S. Milne, *Algebraic Groups* (2017), Proposition 1.25 and
  Corollary 1.17: the all-algebra commutativity criterion and the
  separable-closure argument using schematic density of points of a group
  variety.
- `SchemeProperties.FiniteTypePoints`, `lftPointsFullyFaithful`:
  restricted Yoneda full faithfulness on finitely generated algebras.
- Mathlib, `isCommMonObj_iff_isMulCommutative`: the commutativity criterion
  for a Cartesian group object evaluated on its points.
- `AlgebraicGroups.Scheme.GeometricallyReduced`,
  `GeometricallyReduced.comp_of_flat_of_locallyOfFiniteType`, and
  `AlgebraicGroups.Scheme.JointlySchemeTheoreticallyDominant`,
  `FieldValuedPoints.SchematicallyDense.over_hom_ext`: geometric reducedness
  of the product and equality from schematically dense field-valued points.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite
open scoped CategoryTheory.MonObj MonoidalCategory

universe u

namespace AlgebraicGeometry

variable {K : Type u} [Field K]

noncomputable local instance commutativeLftOverCartesianMonoidal :
    CartesianMonoidalCategory
      (locallyFiniteTypeMorphism.Over ⊤ (Spec (.of K))) :=
  .ofHasFiniteProducts

noncomputable local instance commutativeLftOverBraided :
    BraidedCategory
      (locallyFiniteTypeMorphism.Over ⊤ (Spec (.of K))) :=
  .ofCartesianMonoidalCategory

/-- A group object among schemes locally of finite type over a field is commutative exactly when
its point groups over all finitely generated algebras are commutative. This
extends Milne, *Algebraic Groups* (2017), Proposition 1.25, using the
restricted Yoneda full faithfulness of `SchemeProperties.FiniteTypePoints`. -/
theorem isCommMonObj_iff_finiteAlg_points_commutative
    (G : Grp (locallyFiniteTypeMorphism.Over ⊤ (Spec (.of K)))) :
    IsCommMonObj G.X ↔
      ∀ R : FGAlgCat K,
        IsMulCommutative ((finiteAlgSpecOver K).obj (.op R) ⟶ G.X) := by
  constructor
  · intro h R
    exact (isCommMonObj_iff_isMulCommutative G.X).mp h _
  · intro h
    constructor
    apply (lftPointsFullyFaithful K).map_injective
    ext R x
    simp only [Functor.map_comp]
    cases x with
    | up x =>
      dsimp [Presheaf.restrictedULiftYoneda, uliftYoneda, yoneda, uliftFunctor]
      apply ULift.ext
      dsimp
      rw [MonObj.mul_eq_mul]
      simp only [MonObj.comp_mul, Category.assoc,
        CartesianMonoidalCategory.braiding_hom_fst,
        CartesianMonoidalCategory.braiding_hom_snd]
      exact (h R.unop.unop).is_comm.comm _ _

/-- For a geometrically reduced group scheme locally of finite type over a field, commutativity is
equivalent to commutativity of its points over one separably closed extension
field. This strengthens the implication for group varieties in Milne,
*Algebraic Groups* (2017), Proposition 1.25, via schematic density as in
Corollary 1.17. -/
theorem isCommMonObj_iff_isMulCommutative_fieldValuedPoints
    {L : Type u} [Field L] [Algebra K L] [IsSepClosed L]
    {G : Over (Spec (.of K))} [GrpObj G]
    [LocallyOfFiniteType G.hom] [GeometricallyReduced G.hom] :
    IsCommMonObj G ↔
      IsMulCommutative
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⟶ G) := by
  constructor
  · intro h
    exact (isCommMonObj_iff_isMulCommutative G).mp h _
  · intro h
    constructor
    let _ : IsSeparated G.hom := isSeparated_of_grpObj G
    let _ : LocallyOfFiniteType (G ⊗ G).hom := by
      rw [Over.tensorObj_hom]
      infer_instance
    let _ : GeometricallyReduced (G ⊗ G).hom := by
      rw [Over.tensorObj_hom]
      apply GeometricallyReduced.comp_of_flat_of_locallyOfFiniteType
    apply (FieldValuedPoints.schematicallyDense_of_geometricallyReduced_of_isSepClosed
      (Y := G ⊗ G) (L := L)).over_hom_ext
    intro p
    let q : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⟶ G ⊗ G :=
      Over.homMk p.1 p.2
    change Over.Hom.left (q ≫ ((β_ G G).hom ≫ μ[G])) =
      Over.Hom.left (q ≫ μ[G])
    apply congrArg Over.Hom.left
    rw [← Category.assoc, MonObj.mul_eq_mul]
    simp only [MonObj.comp_mul, Category.assoc,
      CartesianMonoidalCategory.braiding_hom_fst,
      CartesianMonoidalCategory.braiding_hom_snd]
    exact h.is_comm.comm _ _

end AlgebraicGeometry
