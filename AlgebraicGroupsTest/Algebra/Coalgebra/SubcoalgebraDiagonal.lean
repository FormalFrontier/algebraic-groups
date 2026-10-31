/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.Subcoalgebra.Finsupp
public import AlgebraicGroups.Algebra.Coalgebra.Equiv
public import AlgebraicGroups.Algebra.Coalgebra.GroupLikeSpan
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.RingTheory.Flat.Basic

/-!
# A finite proper part of the diagonal Finsupp coalgebra

For every field `K`, the coalgebra on `ℕ →₀ K` has a nonzero proper finite-dimensional
subcoalgebra consisting exactly of the functions supported on `{0, 1}`. Its two coordinate
vectors are group-like, while the coordinate vector at `2` is excluded. The ambient module
is not finite-dimensional, as its coordinate basis is indexed by `ℕ`. No infinitude
assumption on the field is needed.

The subcoalgebra is the two-coordinate specialization of
`Finsupp.supportedSubcoalgebra`, whose arbitrary-support construction extends the
construction here using closure of spans of group-like elements. Its characteristic API
gives the carrier, coordinate membership and finiteness. The coalgebra inclusion and
tensor-inclusion injectivity identify the canonical comultiplication on its coordinate
vectors. The canonical comultiplication and counit agree with the finite Finsupp coalgebra
transported along `Finsupp.supportedEquivFinsupp`, without introducing another instance.

The existence theorem records a nonzero proper finite-dimensional subcoalgebra in an
infinite-dimensional ambient module. The specialized alias and verification helpers are
private; the remaining examples compare the canonical structure with transported
structure maps and include the empty-support boundary.

## References

The ambient coalgebra and its single-coordinate formulas use Mathlib's
`Mathlib.RingTheory.Coalgebra.Basic`. The supported submodule and its linear equivalence
use `Mathlib.LinearAlgebra.Finsupp.Supported`; finite generation uses
`Mathlib.RingTheory.Finiteness.Basic`. The infinite-dimensional boundary follows from
`Finsupp.basisSingleOne` and `Module.not_finite_of_infinite_basis` in
`Mathlib.LinearAlgebra.Finsupp.VectorSpace` and `Mathlib.RingTheory.Finiteness.Cardinality`.
The closure argument follows `AlgebraicGroups.Algebra.Coalgebra.GroupLikeSpan`, and the
restriction and inclusion are those of `Subcoalgebra` and `Subcoalgebra.subtype`.
-/

@[expose] public section

noncomputable section

universe u v

open scoped TensorProduct

namespace Coalgebra

variable (K : Type u) [Field K]

private lemma isGroupLikeElem_single_one {ι : Type v} (i : ι) :
    IsGroupLikeElem K (Finsupp.single i (1 : K)) where
  counit_eq_one := by simp
  comul_eq_tmul_self := by simp

/-- The diagonal subcoalgebra supported on the first two coordinates. -/
private abbrev diagonalSubcoalgebra : Subcoalgebra K (ℕ →₀ K) :=
  Finsupp.supportedSubcoalgebra K ({0, 1} : Set ℕ)

@[simp]
private lemma diagonalSubcoalgebra_toSubmodule :
    (diagonalSubcoalgebra K).toSubmodule = Finsupp.supported K K ({0, 1} : Set ℕ) :=
  Finsupp.supportedSubcoalgebra_toSubmodule K ({0, 1} : Set ℕ)

@[simp]
private lemma mem_diagonalSubcoalgebra (x : ℕ →₀ K) :
    x ∈ diagonalSubcoalgebra K ↔ x ∈ Finsupp.supported K K ({0, 1} : Set ℕ) := by
  exact (Finsupp.mem_supportedSubcoalgebra K ({0, 1} : Set ℕ) x).trans
    (Finsupp.mem_supported K x).symm

private lemma diagonalSubcoalgebra_toSubmodule_eq_span :
    (diagonalSubcoalgebra K).toSubmodule =
      Submodule.span K ({Finsupp.single 0 (1 : K), Finsupp.single 1 (1 : K)} :
        Set (ℕ →₀ K)) := by
  simpa only [Set.image_pair] using
    Finsupp.supportedSubcoalgebra_toSubmodule_eq_span K ({0, 1} : Set ℕ)

private lemma single_mem_diagonalSubcoalgebra (i : ℕ) (hi : i ∈ ({0, 1} : Set ℕ)) :
    Finsupp.single i (1 : K) ∈ diagonalSubcoalgebra K :=
  Finsupp.single_mem_supportedSubcoalgebra K ({0, 1} : Set ℕ) 1 hi

private lemma diagonalSubcoalgebra_ne_bot : (diagonalSubcoalgebra K).toSubmodule ≠ ⊥ := by
  intro h
  have hx := (Subcoalgebra.mem_iff (diagonalSubcoalgebra K)).mp
    (single_mem_diagonalSubcoalgebra K 0 (by simp))
  rw [h, Submodule.mem_bot] at hx
  exact (one_ne_zero : (1 : K) ≠ 0)
    (by simpa using congrArg (fun x : ℕ →₀ K => x 0) hx)

private lemma single_two_not_mem_diagonalSubcoalgebra :
    Finsupp.single 2 (1 : K) ∉ diagonalSubcoalgebra K := by
  intro h
  have hs := (mem_diagonalSubcoalgebra K _).mp h
  have h2 := (Finsupp.mem_supported' K _).mp hs 2 (by simp)
  apply (one_ne_zero : (1 : K) ≠ 0)
  simpa only [Finsupp.single_eq_same] using h2

private lemma diagonalSubcoalgebra_ne_top : (diagonalSubcoalgebra K).toSubmodule ≠ ⊤ := by
  intro h
  apply single_two_not_mem_diagonalSubcoalgebra K
  apply (Subcoalgebra.mem_iff (diagonalSubcoalgebra K)).mpr
  rw [h]
  exact Submodule.mem_top

private lemma diagonalSubcoalgebra_fg : (diagonalSubcoalgebra K).toSubmodule.FG :=
  Finsupp.supportedSubcoalgebra_fg K ({0, 1} : Set ℕ) (by simp)

private lemma diagonalSubcoalgebra_finite : Module.Finite K (diagonalSubcoalgebra K) :=
  Finsupp.supportedSubcoalgebra_finite K ({0, 1} : Set ℕ) (by simp)

private lemma not_finite_finsupp_nat : ¬ Module.Finite K (ℕ →₀ K) :=
  Module.not_finite_of_infinite_basis (Finsupp.basisSingleOne (ι := ℕ) (R := K))

/-- Coordinates on the supported subcoalgebra, with values in a two-index Finsupp module. -/
private abbrev diagonalEquiv :
    diagonalSubcoalgebra K ≃ₗ[K] (({0, 1} : Set ℕ) →₀ K) :=
  Finsupp.supportedEquivFinsupp (M := K) (R := K) ({0, 1} : Set ℕ)

/-- A coordinate vector in the supported subcoalgebra. -/
private abbrev diagonalBasisVector (i : ({0, 1} : Set ℕ)) : diagonalSubcoalgebra K :=
  (diagonalEquiv K).symm (Finsupp.single i 1)

@[simp]
private lemma coe_diagonalBasisVector (i : ({0, 1} : Set ℕ)) :
    (diagonalBasisVector K i : ℕ →₀ K) = Finsupp.single (i : ℕ) (1 : K) := by
  exact Finsupp.supportedEquivFinsupp_symm_single (R := K) ({0, 1} : Set ℕ) i (1 : K)

private lemma subtype_diagonalBasisVector (i : ({0, 1} : Set ℕ)) :
    (diagonalSubcoalgebra K).subtype (diagonalBasisVector K i) =
      Finsupp.single (i : ℕ) (1 : K) := by
  rw [Subcoalgebra.subtype_apply, coe_diagonalBasisVector]

private lemma isGroupLikeElem_diagonalBasisVector (i : ({0, 1} : Set ℕ)) :
    IsGroupLikeElem K (diagonalBasisVector K i) where
  counit_eq_one := by
    rw [Subcoalgebra.coalgebra_counit_apply, coe_diagonalBasisVector]
    exact (isGroupLikeElem_single_one K (i : ℕ)).counit_eq_one
  comul_eq_tmul_self := by
    let : Module.Free K (diagonalSubcoalgebra K).toSubmodule :=
      Module.Free.of_divisionRing K (diagonalSubcoalgebra K).toSubmodule
    apply Module.Flat.tensorProduct_mapIncl_injective_of_right
      (diagonalSubcoalgebra K).toSubmodule (diagonalSubcoalgebra K).toSubmodule
    rw [Subcoalgebra.mapIncl_coalgebra_comul, coe_diagonalBasisVector,
      (isGroupLikeElem_single_one K (i : ℕ)).comul_eq_tmul_self]
    simp only [TensorProduct.mapIncl, _root_.TensorProduct.map_tmul, Submodule.subtype_apply,
      coe_diagonalBasisVector]

/-- Transport of the finite Finsupp coalgebra to the supported subtype, kept as explicit data. -/
@[instance_reducible]
private def diagonalCoalgebra : Coalgebra K (diagonalSubcoalgebra K) :=
  (diagonalEquiv K).coalgebra K

private abbrev diagonalComul :
    diagonalSubcoalgebra K →ₗ[K] diagonalSubcoalgebra K ⊗[K] diagonalSubcoalgebra K :=
  @CoalgebraStruct.comul K (diagonalSubcoalgebra K) _ _ _
    (diagonalCoalgebra K).toCoalgebraStruct

private abbrev diagonalCounit : diagonalSubcoalgebra K →ₗ[K] K :=
  @CoalgebraStruct.counit K (diagonalSubcoalgebra K) _ _ _
    (diagonalCoalgebra K).toCoalgebraStruct

private lemma diagonalComul_basisVector (i : ({0, 1} : Set ℕ)) :
    diagonalComul K (diagonalBasisVector K i) =
      diagonalBasisVector K i ⊗ₜ[K] diagonalBasisVector K i := by
  simp only [diagonalComul, LinearEquiv.coalgebra_comul_apply]
  rw [show (diagonalEquiv K) (diagonalBasisVector K i) = Finsupp.single i 1 from
    (diagonalEquiv K).apply_symm_apply _]
  simp only [(isGroupLikeElem_single_one K i).comul_eq_tmul_self, _root_.TensorProduct.map_tmul,
    diagonalBasisVector]
  rfl

private lemma diagonalCounit_basisVector (i : ({0, 1} : Set ℕ)) :
    diagonalCounit K (diagonalBasisVector K i) = 1 := by
  simp only [diagonalCounit, LinearEquiv.coalgebra_counit_apply]
  rw [show (diagonalEquiv K) (diagonalBasisVector K i) = Finsupp.single i 1 from
    (diagonalEquiv K).apply_symm_apply _]
  exact (isGroupLikeElem_single_one K i).counit_eq_one

/-- The diagonal coalgebra on finitely supported functions on `ℕ` has a nonzero proper
finite-dimensional subcoalgebra supported on `{0, 1}`, although its ambient module is
infinite-dimensional. -/
theorem exists_finite_proper_subcoalgebra_finsupp_nat :
    ∃ D : Subcoalgebra K (ℕ →₀ K),
      D.toSubmodule = Finsupp.supported K K ({0, 1} : Set ℕ) ∧
      D.toSubmodule ≠ ⊥ ∧ D.toSubmodule ≠ ⊤ ∧ D.toSubmodule.FG ∧
      Module.Finite K D ∧ ¬ Module.Finite K (ℕ →₀ K) ∧
      Finsupp.single 0 (1 : K) ∈ D ∧ Finsupp.single 1 (1 : K) ∈ D := by
  exact ⟨diagonalSubcoalgebra K, diagonalSubcoalgebra_toSubmodule K,
    diagonalSubcoalgebra_ne_bot K, diagonalSubcoalgebra_ne_top K, diagonalSubcoalgebra_fg K,
    diagonalSubcoalgebra_finite K, not_finite_finsupp_nat K,
    single_mem_diagonalSubcoalgebra K 0 (by simp), single_mem_diagonalSubcoalgebra K 1 (by simp)⟩

-- Empty support gives the zero carrier.
example : (Finsupp.supportedSubcoalgebra K (∅ : Set ℕ)).toSubmodule = ⊥ := by
  rw [Finsupp.supportedSubcoalgebra_toSubmodule_eq_span, Set.image_empty, Submodule.span_empty]

-- The two group-like vectors use the canonical coalgebra and its bundled inclusion.
example (i : ({0, 1} : Set ℕ)) :
    (diagonalSubcoalgebra K).subtype (diagonalBasisVector K i) =
        Finsupp.single (i : ℕ) (1 : K) ∧
      counit (R := K) (diagonalBasisVector K i) = 1 ∧
      comul (R := K) (diagonalBasisVector K i) =
        diagonalBasisVector K i ⊗ₜ[K] diagonalBasisVector K i ∧
      counit (R := K) ((diagonalSubcoalgebra K).subtype (diagonalBasisVector K i)) = 1 ∧
      comul (R := K) ((diagonalSubcoalgebra K).subtype (diagonalBasisVector K i)) =
        _root_.TensorProduct.map (diagonalSubcoalgebra K).subtype.toLinearMap
          (diagonalSubcoalgebra K).subtype.toLinearMap
          (diagonalBasisVector K i ⊗ₜ[K] diagonalBasisVector K i) := by
  have hi := isGroupLikeElem_diagonalBasisVector K i
  refine ⟨subtype_diagonalBasisVector K i, hi.counit_eq_one, hi.comul_eq_tmul_self, ?_, ?_⟩
  · rw [CoalgHomClass.counit_comp_apply, hi.counit_eq_one]
  · rw [← CoalgHomClass.map_comp_comul_apply, hi.comul_eq_tmul_self]
    rfl

-- Agreement on a basis gives agreement of both structure maps on every member.
example :
    diagonalComul K = comul (R := K) (A := diagonalSubcoalgebra K) ∧
      diagonalCounit K = counit (R := K) (A := diagonalSubcoalgebra K) := by
  constructor
  · apply (Module.Basis.ofRepr (diagonalEquiv K)).ext
    intro i
    change diagonalComul K (diagonalBasisVector K i) =
      comul (R := K) (diagonalBasisVector K i)
    rw [diagonalComul_basisVector,
      (isGroupLikeElem_diagonalBasisVector K i).comul_eq_tmul_self]
  · apply (Module.Basis.ofRepr (diagonalEquiv K)).ext
    intro i
    change diagonalCounit K (diagonalBasisVector K i) =
      counit (R := K) (diagonalBasisVector K i)
    rw [diagonalCounit_basisVector,
      (isGroupLikeElem_diagonalBasisVector K i).counit_eq_one]

end Coalgebra
