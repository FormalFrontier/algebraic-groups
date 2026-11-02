/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.Subcoalgebra.Finsupp
public import AlgebraicGroups.Algebra.Coalgebra.GroupLikeCoordinates
public import AlgebraicGroups.Algebra.Coalgebra.Subcoalgebra.Equiv
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.Order.Hom.Basic

/-!
# Subcoalgebras determined by a group-like basis

For a coalgebra over a field with a given basis of group-like elements,
`Module.Basis.groupLikeSubcoalgebraOrderIso` identifies its subcoalgebras with the
subsets of that basis. The forward subcoalgebra is spanned by the chosen basis vectors;
the inverse records the basis vectors belonging to a subcoalgebra. Membership is
containment of the finite support of the basis coordinates.

The index type may be infinite or empty. In particular, the empty-basis zero coalgebra
is included. A group-like basis is assumed, not asserted to exist for every coalgebra.

The construction transports `Finsupp.supportedSubcoalgebraOrderIso` through the existing
coalgebra equivalences attached to a group-like basis. The restricted coalgebras and
inclusion homomorphisms are those of the existing subcoalgebra and image constructors.

## References

The coordinate equivalences are from
`AlgebraicGroups.Algebra.Coalgebra.GroupLikeCoordinates`; the supported subcoalgebras and
their classification are from `AlgebraicGroups.Algebra.Coalgebra.Subcoalgebra.Finsupp`.
Transport uses `AlgebraicGroups.Algebra.Coalgebra.Subcoalgebra.Equiv`.
-/

@[expose] public section

universe uK uC uI

variable {K : Type uK} {C : Type uC} {I : Type uI}
variable [Field K] [AddCommGroup C] [Module K C] [Coalgebra K C]

namespace Module.Basis

variable (b : Module.Basis I K C) (hb : ∀ i, IsGroupLikeElem K (b i))

private theorem isGroupLikeElem_basisSingleOne (i : I) :
    IsGroupLikeElem K ((Finsupp.basisSingleOne : Module.Basis I K (I →₀ K)) i) := by
  constructor <;> simp [Finsupp.coe_basisSingleOne]

private noncomputable def groupLikeFinsuppCoalgebraEquiv :
    (I →₀ K) ≃ₗc[K] C :=
  ((Finsupp.basisSingleOne : Module.Basis I K (I →₀ K)).groupLikeCoalgebraEquiv
    (isGroupLikeElem_basisSingleOne (K := K))).symm.trans
      (b.groupLikeCoalgebraEquiv hb)

private theorem groupLikeFinsuppCoalgebraEquiv_single (i : I) :
    groupLikeFinsuppCoalgebraEquiv b hb (Finsupp.single i 1) = b i := by
  have h :
      ((Finsupp.basisSingleOne : Module.Basis I K (I →₀ K)).groupLikeCoalgebraEquiv
        (isGroupLikeElem_basisSingleOne (K := K))).symm (Finsupp.single i 1) =
          MonoidAlgebra.single i 1 := by
    simpa only [Finsupp.coe_basisSingleOne] using
      (Finsupp.basisSingleOne : Module.Basis I K (I →₀ K)).groupLikeCoalgebraEquiv_symm_basis
        (isGroupLikeElem_basisSingleOne (K := K)) i
  rw [groupLikeFinsuppCoalgebraEquiv, CoalgEquiv.trans_apply, h,
    groupLikeCoalgebraEquiv_single, one_smul]

/-- Subcoalgebras correspond in order to subsets of a given group-like basis. -/
noncomputable def groupLikeSubcoalgebraOrderIso :
    Set I ≃o Subcoalgebra K C := by
  let e := ((Finsupp.basisSingleOne : Module.Basis I K (I →₀ K)).groupLikeCoalgebraEquiv
    (by intro i; constructor <;> simp [Finsupp.coe_basisSingleOne])).symm.trans
      (b.groupLikeCoalgebraEquiv hb)
  let t : Subcoalgebra K (I →₀ K) ≃o Subcoalgebra K C :=
    { toEquiv := e.subcoalgebraCongr
      map_rel_iff' := by
        intro D D'
        constructor
        · intro h
          have h' := Subcoalgebra.map_mono (f := e.symm.toCoalgHom) h
          apply Subcoalgebra.toSubmodule_le_toSubmodule.mp
          simpa only [← CoalgEquiv.subcoalgebraCongr_symm_apply,
            Equiv.symm_apply_apply] using h'
        · intro h
          exact Subcoalgebra.map_mono (f := e.toCoalgHom) h }
  exact (Finsupp.supportedSubcoalgebraOrderIso K I).trans t

private theorem groupLikeSubcoalgebraOrderIso_apply (s : Set I) :
    b.groupLikeSubcoalgebraOrderIso hb s =
      Subcoalgebra.map (groupLikeFinsuppCoalgebraEquiv b hb).toCoalgHom
        (Finsupp.supportedSubcoalgebra K s) := by
  rfl

/-- The forward subcoalgebra is spanned by the selected basis vectors. -/
theorem groupLikeSubcoalgebraOrderIso_toSubmodule (s : Set I) :
    (b.groupLikeSubcoalgebraOrderIso hb s).toSubmodule =
      Submodule.span K (b '' s) := by
  rw [groupLikeSubcoalgebraOrderIso_apply, Subcoalgebra.map_toSubmodule,
    Finsupp.supportedSubcoalgebra_toSubmodule_eq_span, Submodule.map_span]
  congr 1
  rw [Set.image_image]
  exact congrArg (fun f : I → C => f '' s)
    (funext fun i => groupLikeFinsuppCoalgebraEquiv_single b hb i)

/-- Membership is containment of the finite support of the basis coordinates. -/
@[simp] theorem mem_groupLikeSubcoalgebraOrderIso (s : Set I) (x : C) :
    x ∈ b.groupLikeSubcoalgebraOrderIso hb s ↔
      (↑(b.repr x).support : Set I) ⊆ s := by
  rw [Subcoalgebra.mem_iff, groupLikeSubcoalgebraOrderIso_toSubmodule,
    b.mem_span_image]

/-- A basis vector belongs to a selected subcoalgebra exactly at a selected index. -/
theorem basis_mem_groupLikeSubcoalgebraOrderIso (s : Set I) (i : I) :
    b i ∈ b.groupLikeSubcoalgebraOrderIso hb s ↔ i ∈ s := by
  rw [Subcoalgebra.mem_iff, groupLikeSubcoalgebraOrderIso_toSubmodule,
    b.self_mem_span_image]

/-- The inverse classification records which basis vectors lie in the subcoalgebra. -/
@[simp] theorem groupLikeSubcoalgebraOrderIso_symm_apply (D : Subcoalgebra K C) :
    (b.groupLikeSubcoalgebraOrderIso hb).symm D = {i | b i ∈ D} := by
  ext i
  simpa only [OrderIso.apply_symm_apply, Set.mem_ofPred_eq] using
    (basis_mem_groupLikeSubcoalgebraOrderIso b hb
      ((b.groupLikeSubcoalgebraOrderIso hb).symm D) i).symm

include hb in
/-- Every subcoalgebra is spanned by the basis vectors it contains. -/
theorem subcoalgebra_toSubmodule_eq_span (D : Subcoalgebra K C) :
    D.toSubmodule = Submodule.span K (b '' {i | b i ∈ D}) := by
  have h := groupLikeSubcoalgebraOrderIso_toSubmodule b hb
    ((b.groupLikeSubcoalgebraOrderIso hb).symm D)
  rw [OrderIso.apply_symm_apply] at h
  simpa only [groupLikeSubcoalgebraOrderIso_symm_apply] using h

include hb in
/-- Subcoalgebras are equal exactly when they contain the same vectors of a
fixed group-like basis. -/
theorem subcoalgebra_ext_iff (D D' : Subcoalgebra K C) :
    D = D' ↔ ∀ i, b i ∈ D ↔ b i ∈ D' := by
  constructor
  · rintro rfl i
    rfl
  · intro h
    apply (b.groupLikeSubcoalgebraOrderIso hb).symm.injective
    rw [groupLikeSubcoalgebraOrderIso_symm_apply,
      groupLikeSubcoalgebraOrderIso_symm_apply]
    exact Set.ext h

end Module.Basis

/-- For the unit coordinate basis, the classification agrees with supported
subcoalgebras of finitely supported functions. -/
theorem Finsupp.basisSingleOne_groupLikeSubcoalgebraOrderIso
    (K : Type uK) [Field K] (I : Type uI) :
    (Finsupp.basisSingleOne : Module.Basis I K (I →₀ K)).groupLikeSubcoalgebraOrderIso
      (by intro i; constructor <;> simp [Finsupp.coe_basisSingleOne]) =
        Finsupp.supportedSubcoalgebraOrderIso K I := by
  apply OrderIso.ext
  funext s
  apply Subcoalgebra.toSubmodule_injective
  rw [Module.Basis.groupLikeSubcoalgebraOrderIso_toSubmodule,
    Finsupp.supportedSubcoalgebraOrderIso_apply,
    Finsupp.supportedSubcoalgebra_toSubmodule_eq_span,
    Finsupp.coe_basisSingleOne]
