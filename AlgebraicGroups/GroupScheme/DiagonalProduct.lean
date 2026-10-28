/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.Multiplicative
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Scheme
public import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

/-!
# The canonical split torus as a product of multiplicative groups

The existing coordinate-character morphisms are product projections on points
of every test scheme over the base. Their product universal property follows
from the global-sections adjunction and the free-abelian character equivalence.
No affine, reducedness, field, or nontriviality hypothesis is imposed on a test
scheme or the base ring.

## References

* J. S. Milne, *Algebraic Groups* (2017), §12.d.
* Mathlib contributors, the relative Γ-Spec adjunction and product limits.
* Tau Ceti contributors, `SplitTorus.Scheme` and
  `CommHopfAlgCat.schemePointsAlgΓMulEquiv`.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]

/-- Maps from an arbitrary base scheme to the canonical split torus are families
of units in its global-sections algebra. -/
def diagonalGroupHomUnits (X : Over (Spec (.of K))) :
    (X ⟶ (TauCeti.SplitTorus.groupScheme K n).X) ≃*
      (n → ((algΓ (.of K)).obj X).unopˣ) := by
  change (X ⟶ (Spec (.of (MonoidAlgebra K (Multiplicative (n →₀ ℤ))))).asOver
    (Spec (.of K))) ≃* _
  exact (TauCeti.CommHopfAlgCat.schemePointsAlgΓMulEquiv (R := K)
    (MonoidAlgebra K (Multiplicative (n →₀ ℤ))) X).trans
      (TauCeti.SplitTorus.pointsMulEquiv (R := K))

omit [DecidableEq n] in
/-- A coordinate character reads the corresponding global unit on every test scheme. -/
theorem diagonalGroupProjection_globalUnit (j : n) (X : Over (Spec (.of K)))
    (hom : X ⟶ (TauCeti.SplitTorus.groupScheme K n).X) :
    multiplicativeGroupHomUnits K X
      (hom ≫ (TauCeti.SplitTorus.characterGroupSchemeMap
        (R := K) (Finsupp.single j 1)).hom.hom) =
      diagonalGroupHomUnits K n X hom j := by
  let f : ULift.{u} (Multiplicative ℤ) →* Multiplicative (n →₀ ℤ) :=
    TauCeti.DiagonalizableGroup.uliftZPowersMulEquiv _
      (Multiplicative.ofAdd (Finsupp.single j 1))
  let ψ := MonoidAlgebra.mapDomainBialgHom K f
  have hprojection : (TauCeti.SplitTorus.characterGroupSchemeMap
        (R := K) (Finsupp.single j 1)).hom.hom =
      (Spec.map (CommRingCat.ofHom ψ.toAlgHom.toRingHom)).asOver (Spec (.of K)) := by
    rw [TauCeti.SplitTorus.characterGroupSchemeMap_def]
    erw [TauCeti.DiagonalizableGroup.characterGroupSchemeMap_def]
    rfl
  rw [hprojection]
  apply Units.ext
  change _ = (TauCeti.SplitTorus.pointsMulEquiv
    ((TauCeti.CommHopfAlgCat.schemePointsAlgΓMulEquiv (R := K)
      (MonoidAlgebra K (Multiplicative (n →₀ ℤ))) X) hom) j :
        ((algΓ (.of K)).obj X).unop)
  simp only [multiplicativeGroupHomUnits]
  erw [MulEquiv.trans_apply, MulEquiv.trans_apply]
  rw [TauCeti.DiagonalizableGroup.uliftZPowersMulEquiv_symm_apply,
    TauCeti.DiagonalizableGroup.pointsMulEquiv_apply,
    TauCeti.DiagonalizableGroup.charOfPoint_apply_coe,
    TauCeti.SplitTorus.pointsMulEquiv_apply_coe]
  erw [TauCeti.CommHopfAlgCat.schemePointsAlgΓMulEquiv_mapDomain X ψ hom]
  simp only [BialgHom.mapDomain_apply, WithConv.ofConv_toConv, AlgHom.comp_apply,
    ψ]
  congr 1
  erw [MonoidAlgebra.mapDomainBialgHom_single]
  dsimp only [f]
  rw [TauCeti.DiagonalizableGroup.uliftZPowersMulEquiv_apply, toAdd_ofAdd, zpow_one]

/-- The genuine projection fan in group objects over the base. -/
def diagonalGroupProductFan : Limits.Fan (fun _ : n ↦
  TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K) :=
  Limits.Fan.mk (TauCeti.SplitTorus.groupScheme K n) (fun j : n =>
    TauCeti.SplitTorus.characterGroupSchemeMap (R := K) (Finsupp.single j 1))

/-- The underlying cone is universal over all schemes over `Spec K`. -/
def diagonalGroupProductFanForgetIsLimit :
    Limits.IsLimit ((Grp.forget (Over (Spec (.of K)))).mapCone
      (diagonalGroupProductFan K n)) := by
  change Limits.IsLimit (Limits.Fan.mk (TauCeti.SplitTorus.groupScheme K n).X
    (fun j : n ↦ (TauCeti.SplitTorus.characterGroupSchemeMap (R := K) (Finsupp.single j
      1)).hom.hom))
  refine Limits.Fan.IsLimit.mk _ (fun cone ↦
    (diagonalGroupHomUnits K n cone.pt).symm
      (fun j ↦ multiplicativeGroupHomUnits K cone.pt (cone.proj j))) ?_ ?_
  · intro cone j
    apply (multiplicativeGroupHomUnits K cone.pt).injective
    change multiplicativeGroupHomUnits K cone.pt
      ((diagonalGroupHomUnits K n cone.pt).symm
        (fun j ↦ multiplicativeGroupHomUnits K cone.pt (cone.proj j)) ≫
          (TauCeti.SplitTorus.characterGroupSchemeMap (R := K) (Finsupp.single j 1)).hom.hom) =
        multiplicativeGroupHomUnits K cone.pt (cone.proj j)
    rw [diagonalGroupProjection_globalUnit]
    simp
  · intro cone morphism factor
    apply (diagonalGroupHomUnits K n cone.pt).injective
    funext j
    simp only [MulEquiv.apply_symm_apply]
    rw [← diagonalGroupProjection_globalUnit K n j cone.pt morphism]
    have hfac : morphism ≫ (TauCeti.SplitTorus.characterGroupSchemeMap (R := K) (Finsupp.single j
      1)).hom.hom = cone.proj j :=
      factor j
    rw [hfac]

/-- The group-object forgetful functor reflects this product limit. -/
def diagonalGroupProductFanIsLimit : Limits.IsLimit (diagonalGroupProductFan K n) :=
  Limits.isLimitOfReflects (Grp.forget (Over (Spec (.of K))))
    (diagonalGroupProductFanForgetIsLimit K n)

/-- The finite categorical product of multiplicative group schemes over any
commutative base; compare Milne, *Algebraic Groups* (2017), §12.d (p. 234),
for the diagonal product over a field. -/
def diagonalGroupSchemeProductIso :
    TauCeti.SplitTorus.groupScheme K n ≅ (∏ᶜ fun _ : n ↦
      TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K) :=
  (diagonalGroupProductFanIsLimit K n).conePointUniqueUpToIso
    (Limits.productIsProduct fun _ : n ↦ TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K)

omit [DecidableEq n] in
@[simp] theorem diagonalGroupSchemeProductIso_hom_π (j : n) :
    (diagonalGroupSchemeProductIso K n).hom ≫
      Limits.Pi.π (fun _ : n ↦ TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K) j =
        TauCeti.SplitTorus.characterGroupSchemeMap (R := K) (Finsupp.single j 1) :=
  (diagonalGroupProductFanIsLimit K n).conePointUniqueUpToIso_hom_comp
    (Limits.productIsProduct fun _ : n ↦ TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K)
      ⟨j⟩

omit [DecidableEq n] in
@[simp] theorem diagonalGroupSchemeProductIso_inv_projection (j : n) :
    (diagonalGroupSchemeProductIso K n).inv ≫ TauCeti.SplitTorus.characterGroupSchemeMap (R := K)
      (Finsupp.single j 1) =
      Limits.Pi.π (fun _ : n ↦ TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K) j :=
  (diagonalGroupProductFanIsLimit K n).conePointUniqueUpToIso_inv_comp
    (Limits.productIsProduct fun _ : n ↦ TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K)
      ⟨j⟩

/-- The empty diagonal group scheme is terminal over any commutative base. -/
def diagonalGroupSchemeEmptyIsTerminal :
    Limits.IsTerminal (TauCeti.SplitTorus.groupScheme K PEmpty.{u+1}) :=
  (Limits.isLimitEquivIsTerminalOfIsEmpty (Grp (Over (Spec (.of K))))
    (diagonalGroupProductFan K PEmpty.{u+1}))
    (diagonalGroupProductFanIsLimit K PEmpty.{u+1})

/-- The terminality statement specialized to the finite empty index type. -/
def diagonalGroupSchemeFin0IsTerminal (K : Type) [CommRing K] :
    Limits.IsTerminal (TauCeti.SplitTorus.groupScheme K (Fin 0)) :=
  (Limits.isLimitEquivIsTerminalOfIsEmpty (Grp (Over (Spec (.of K))))
    (diagonalGroupProductFan K (Fin 0)))
    (diagonalGroupProductFanIsLimit K (Fin 0))

end AlgebraicGeometry
