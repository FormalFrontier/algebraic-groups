/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.FiniteTypePoints
public import AlgebraicGroups.GroupScheme.FiniteTypePoints
public import SchemeProperties
public import AlgebraicGroups

/-!
# Finite-type points coexistence client

The defining modules and public aggregate roots share one import environment. Generic
finite-type points are provided by Scheme Properties, with group-valued points supplied
by Algebraic Groups.
-/

set_option warningAsError true

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable (K : Type u) [Field K]

private noncomputable def genericPointsFullyFaithful :
    (Presheaf.restrictedULiftYoneda.{0} (finiteAlgSpecOver K)).FullyFaithful :=
  lftPointsFullyFaithful K

private noncomputable def groupPointsFullyFaithful :
    (lftGroupPoints K).FullyFaithful :=
  lftGroupPointsFullyFaithful K

private noncomputable def underlyingPointsIso (X : algebraicOver K)
    (F : (((FGAlgCat K)ᵒᵖ)ᵒᵖ ⥤ Type u))
    (e : (algebraicOverPoints K).obj X ≅ F) :
    (Presheaf.restrictedULiftYoneda.{0} (finiteAlgSpecOver K)).obj X.obj ≅ F := by
  rw [algebraicOverPoints_eq K, Functor.comp_obj, algebraicOverInclusion_obj K X] at e
  exact e

private noncomputable def algebraicPointsIso (X : algebraicOver K)
    (F : (((FGAlgCat K)ᵒᵖ)ᵒᵖ ⥤ Type u))
    (e : (Presheaf.restrictedULiftYoneda.{0} (finiteAlgSpecOver K)).obj X.obj ≅ F) :
    (algebraicOverPoints K).obj X ≅ F := by
  rw [algebraicOverPoints_eq K, Functor.comp_obj, algebraicOverInclusion_obj K X]
  exact e

private theorem underlyingEssImage_of_group
    (F : Grp ((((FGAlgCat K)ᵒᵖ)ᵒᵖ ⥤ Type u)))
    (h : (algebraicGroupPoints K).essImage F) :
    (algebraicOverPoints K).essImage F.X :=
  (algebraicGroupPoints_essImage_iff K).mp h

private theorem groupEssImage_of_underlying
    (F : Grp ((((FGAlgCat K)ᵒᵖ)ᵒᵖ ⥤ Type u)))
    (h : (algebraicOverPoints K).essImage F.X) :
    (algebraicGroupPoints K).essImage F :=
  (algebraicGroupPoints_essImage_iff K).mpr h

end AlgebraicGeometry
