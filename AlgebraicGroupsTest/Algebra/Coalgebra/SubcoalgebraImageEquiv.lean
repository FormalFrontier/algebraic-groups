/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.Subcoalgebra.Equiv
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
public import Mathlib.RingTheory.Coalgebra.TensorProduct

import AlgebraicGroups.Algebra.Coalgebra.GroupLikeSpan
import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Image isomorphisms in an infinite-dimensional diagonal coalgebra

The diagonal coalgebra on `AddMonoidAlgebra K ℕ` over any field has a finite proper
subcoalgebra supported on `{0, 1}`. Doubling the indices gives an injective but
nonsurjective ambient coalgebra homomorphism, and takes this subcoalgebra to the one
supported on `{0, 2}`. Its restricted image equivalence takes the vector at `1` to
the vector at `2`.

Index collapse to `0` is not injective on the ambient coalgebra, but is injective on
the nonzero singleton-coordinate subcoalgebra. This gives an image equivalence with
only local injectivity. Finally, the tensor left unitor transports the two-coordinate
subcoalgebra to a finite proper subcoalgebra of `K ⊗[K] AddMonoidAlgebra K ℕ`.

## References

The diagonal coalgebra, index maps, coordinate membership, and infinite ambient module
use Mathlib's additive monoid algebra, `mapDomainBialgHom`, `single_mem_span_single`,
and `Module.not_finite_of_infinite_basis`. The span construction uses the public closure
lemma in `AlgebraicGroups.Algebra.Coalgebra.GroupLikeSpan`. Tensor transport uses
Mathlib's `Coalgebra.TensorProduct.lid`.
-/

@[expose] public section

noncomputable section

universe u

open scoped TensorProduct

namespace Coalgebra

variable (K : Type u) [Field K]

/-- The span of the coordinate vectors indexed by `s`, with the inherited coalgebra. -/
private def coordinateSubcoalgebra (s : Set ℕ) :
    Subcoalgebra K (AddMonoidAlgebra K ℕ) :=
  Subcoalgebra.mk'
    (Submodule.span K ((fun n : ℕ ↦ AddMonoidAlgebra.single n (1 : K)) '' s))
    (fun {x} hx ↦ comul_mem_range_mapIncl_span_of_isGroupLikeElem
      (by
        rintro _ ⟨n, _hn, rfl⟩
        exact AddMonoidAlgebra.isGroupLikeElem_single_one n) hx)

private lemma coordinateSubcoalgebra_carrier (s : Set ℕ) :
    (coordinateSubcoalgebra K s).toSubmodule = AddMonoidAlgebra.supported K K s := by
  exact (AddMonoidAlgebra.supported_eq_span_single (R := K) (s := s)).symm

private lemma single_mem_coordinateSubcoalgebra (s : Set ℕ) (n : ℕ) :
    AddMonoidAlgebra.single n (1 : K) ∈ coordinateSubcoalgebra K s ↔ n ∈ s := by
  exact AddMonoidAlgebra.single_mem_span_single

private abbrev doubling : AddMonoidAlgebra K ℕ →ₗc[K] AddMonoidAlgebra K ℕ :=
  (AddMonoidAlgebra.mapDomainBialgHom K (2 • AddMonoidHom.id ℕ)).toCoalgHom

private lemma doubling_single (n : ℕ) (r : K) :
    doubling K (AddMonoidAlgebra.single n r) = AddMonoidAlgebra.single (n + n) r := by
  change AddMonoidAlgebra.mapDomainBialgHom K (2 • AddMonoidHom.id ℕ)
    (AddMonoidAlgebra.single n r) = AddMonoidAlgebra.single (n + n) r
  rw [AddMonoidAlgebra.mapDomainBialgHom_single]
  simp [two_nsmul]

private lemma doubling_injective : Function.Injective (doubling K) := by
  change Function.Injective (AddMonoidAlgebra.mapDomain (R := K)
    (((2 : ℕ) • AddMonoidHom.id ℕ : ℕ →+ ℕ) : ℕ → ℕ))
  apply AddMonoidAlgebra.mapDomain_injective
  intro m n h
  have h' : m + m = n + n := by simpa [two_nsmul] using h
  omega

private lemma doubling_not_surjective : ¬ Function.Surjective (doubling K) := by
  have hodd (x : AddMonoidAlgebra K ℕ) : (doubling K x).coeff 1 = 0 := by
    change (Finsupp.mapDomain
      (((2 : ℕ) • AddMonoidHom.id ℕ : ℕ →+ ℕ) : ℕ → ℕ) x.coeff) 1 = 0
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨n, hn⟩
    have hn' : n + n = 1 := by simpa [two_nsmul] using hn
    omega
  intro h
  obtain ⟨x, hx⟩ := h (AddMonoidAlgebra.single 1 (1 : K))
  have h01 := hodd x
  rw [hx] at h01
  simp at h01

private lemma doubling_map_pair :
    Subcoalgebra.map (doubling K) (coordinateSubcoalgebra K ({0, 1} : Set ℕ)) =
      coordinateSubcoalgebra K ({0, 2} : Set ℕ) := by
  apply Subcoalgebra.toSubmodule_injective
  change Submodule.map (doubling K).toLinearMap
      (Submodule.span K ((fun n : ℕ ↦ AddMonoidAlgebra.single n (1 : K)) '' {0, 1})) =
    Submodule.span K ((fun n : ℕ ↦ AddMonoidAlgebra.single n (1 : K)) '' {0, 2})
  rw [Set.image_pair, Set.image_pair, Submodule.map_span, Set.image_pair]
  simp only [CoalgHom.toLinearMap_eq_coe, CoalgHom.coe_toLinearMap, doubling_single]

/-- Doubling indices identifies the finite proper subcoalgebra supported on `{0, 1}`
with the finite proper image supported on `{0, 2}`. The ambient coalgebra is infinite
dimensional, and the ambient homomorphism is injective but not surjective. The image
equivalence and its inverse are evaluated on the nonzero vector at `1`. -/
theorem doubling_supported_pair_image :
    let f : AddMonoidAlgebra K ℕ →ₗc[K] AddMonoidAlgebra K ℕ :=
      (AddMonoidAlgebra.mapDomainBialgHom K (2 • AddMonoidHom.id ℕ)).toCoalgHom
    Function.Injective f ∧ ¬ Function.Surjective f ∧
      ¬ Module.Finite K (AddMonoidAlgebra K ℕ) ∧
      ∃ D : Subcoalgebra K (AddMonoidAlgebra K ℕ),
        D.toSubmodule = AddMonoidAlgebra.supported K K ({0, 1} : Set ℕ) ∧
        D.toSubmodule ≠ ⊥ ∧ D.toSubmodule ≠ ⊤ ∧ D.toSubmodule.FG ∧
        (Subcoalgebra.map f D).toSubmodule =
          AddMonoidAlgebra.supported K K ({0, 2} : Set ℕ) ∧
        (Subcoalgebra.map f D).toSubmodule ≠ ⊤ ∧
        Module.Finite K D ∧ Module.Finite K (Subcoalgebra.map f D) ∧
        ∃ hf : Set.InjOn f (D : Set (AddMonoidAlgebra K ℕ)),
          ∃ x : D,
            (x : AddMonoidAlgebra K ℕ) = AddMonoidAlgebra.single 1 (1 : K) ∧
            (Subcoalgebra.equivMapOfInjOn f D hf x : AddMonoidAlgebra K ℕ) =
              AddMonoidAlgebra.single 2 (1 : K) ∧
            (Subcoalgebra.equivMapOfInjOn f D hf).symm
              (Subcoalgebra.equivMapOfInjOn f D hf x) = x := by
  let D := coordinateSubcoalgebra K ({0, 1} : Set ℕ)
  have hDfg : D.toSubmodule.FG :=
    Submodule.fg_span ((by simp : ({0, 1} : Set ℕ).Finite).image _)
  have hDbot : D.toSubmodule ≠ ⊥ := by
    intro h
    have hx : AddMonoidAlgebra.single 0 (1 : K) ∈ D.toSubmodule :=
      (single_mem_coordinateSubcoalgebra K _ 0).mpr (by simp)
    rw [h, Submodule.mem_bot] at hx
    exact (AddMonoidAlgebra.isGroupLikeElem_single_one (R := K) (A := K) 0).ne_zero hx
  have hDtop : D.toSubmodule ≠ ⊤ := by
    intro h
    have hx : AddMonoidAlgebra.single 2 (1 : K) ∈ D.toSubmodule := by
      rw [h]
      exact Submodule.mem_top
    have hmem := (single_mem_coordinateSubcoalgebra K ({0, 1} : Set ℕ) 2).mp hx
    simp at hmem
  have hItop : (Subcoalgebra.map (doubling K) D).toSubmodule ≠ ⊤ := by
    rw [doubling_map_pair]
    intro h
    have hx : AddMonoidAlgebra.single 1 (1 : K) ∈
        (coordinateSubcoalgebra K ({0, 2} : Set ℕ)).toSubmodule := by
      rw [h]
      exact Submodule.mem_top
    have hmem := (single_mem_coordinateSubcoalgebra K ({0, 2} : Set ℕ) 1).mp hx
    simp at hmem
  refine ⟨doubling_injective K, doubling_not_surjective K,
    Module.not_finite_of_infinite_basis (AddMonoidAlgebra.basis ℕ K),
    D, coordinateSubcoalgebra_carrier K _, hDbot, hDtop, hDfg, ?_, hItop,
    Module.Finite.iff_fg.mpr hDfg, ?_, (doubling_injective K).injOn, ?_⟩
  · rw [doubling_map_pair, coordinateSubcoalgebra_carrier]
  · exact (Subcoalgebra.finite_map_iff_of_injOn (doubling K) D
      (doubling_injective K).injOn).mpr (Module.Finite.iff_fg.mpr hDfg)
  · let x : D := ⟨AddMonoidAlgebra.single 1 (1 : K),
      (single_mem_coordinateSubcoalgebra K _ 1).mpr (by simp)⟩
    refine ⟨x, rfl, ?_, CoalgEquiv.symm_apply_apply _ x⟩
    rw [Subcoalgebra.coe_equivMapOfInjOn_apply]
    exact doubling_single K 1 1

private abbrev collapse : AddMonoidAlgebra K ℕ →ₗc[K] AddMonoidAlgebra K ℕ :=
  (AddMonoidAlgebra.mapDomainBialgHom K (0 : ℕ →+ ℕ)).toCoalgHom

private lemma collapse_single (n : ℕ) (r : K) :
    collapse K (AddMonoidAlgebra.single n r) = AddMonoidAlgebra.single 0 r := by
  change AddMonoidAlgebra.mapDomainBialgHom K (0 : ℕ →+ ℕ)
    (AddMonoidAlgebra.single n r) = AddMonoidAlgebra.single 0 r
  rw [AddMonoidAlgebra.mapDomainBialgHom_single]
  rfl

private lemma collapse_fix_singleton {x : AddMonoidAlgebra K ℕ}
    (hx : x ∈ coordinateSubcoalgebra K ({0} : Set ℕ)) : collapse K x = x := by
  change x ∈ Submodule.span K
    ((fun n : ℕ ↦ AddMonoidAlgebra.single n (1 : K)) '' ({0} : Set ℕ)) at hx
  rw [Set.image_singleton] at hx
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hx
  rw [map_smul, collapse_single]

private lemma collapse_injOn_singleton :
    Set.InjOn (collapse K) (coordinateSubcoalgebra K ({0} : Set ℕ) :
      Set (AddMonoidAlgebra K ℕ)) := by
  intro x hx y hy hxy
  rwa [collapse_fix_singleton K hx, collapse_fix_singleton K hy] at hxy

/-- Index collapse is not ambiently injective, yet its restriction to the nonzero proper
subcoalgebra supported on `{0}` is the identity. The restricted image equivalence thus
exists and fixes every ambient value; both subcoalgebra subtypes are module-finite. -/
theorem collapse_singleton_image_equiv :
    let f : AddMonoidAlgebra K ℕ →ₗc[K] AddMonoidAlgebra K ℕ :=
      (AddMonoidAlgebra.mapDomainBialgHom K (0 : ℕ →+ ℕ)).toCoalgHom
    ¬ Function.Injective f ∧ ¬ Module.Finite K (AddMonoidAlgebra K ℕ) ∧
      ∃ D : Subcoalgebra K (AddMonoidAlgebra K ℕ),
        D.toSubmodule = AddMonoidAlgebra.supported K K ({0} : Set ℕ) ∧
        D.toSubmodule ≠ ⊥ ∧ D.toSubmodule ≠ ⊤ ∧ D.toSubmodule.FG ∧
        Subcoalgebra.map f D = D ∧ Module.Finite K D ∧
        Module.Finite K (Subcoalgebra.map f D) ∧
        ∃ hf : Set.InjOn f (D : Set (AddMonoidAlgebra K ℕ)),
          ∀ x : D, (Subcoalgebra.equivMapOfInjOn f D hf x : AddMonoidAlgebra K ℕ) =
            (x : AddMonoidAlgebra K ℕ) := by
  let D := coordinateSubcoalgebra K ({0} : Set ℕ)
  have hnotinj : ¬ Function.Injective (collapse K) := by
    intro h
    have heq := h ((collapse_single K 0 1).trans (collapse_single K 1 1).symm)
    have hcoeff := congrArg (fun x : AddMonoidAlgebra K ℕ ↦ x.coeff 0) heq
    simp at hcoeff
  have hDfg : D.toSubmodule.FG :=
    Submodule.fg_span ((Set.finite_singleton (0 : ℕ)).image _)
  have hDbot : D.toSubmodule ≠ ⊥ := by
    intro h
    have hx : AddMonoidAlgebra.single 0 (1 : K) ∈ D.toSubmodule :=
      (single_mem_coordinateSubcoalgebra K _ 0).mpr (by simp)
    rw [h, Submodule.mem_bot] at hx
    exact (AddMonoidAlgebra.isGroupLikeElem_single_one (R := K) (A := K) 0).ne_zero hx
  have hDtop : D.toSubmodule ≠ ⊤ := by
    intro h
    have hx : AddMonoidAlgebra.single 1 (1 : K) ∈ D.toSubmodule := by
      rw [h]
      exact Submodule.mem_top
    have hmem := (single_mem_coordinateSubcoalgebra K ({0} : Set ℕ) 1).mp hx
    simp at hmem
  have hmap : Subcoalgebra.map (collapse K) D = D := by
    apply Subcoalgebra.ext
    intro x
    rw [Subcoalgebra.mem_map]
    constructor
    · rintro ⟨y, hy, hxy⟩
      rw [collapse_fix_singleton K hy] at hxy
      exact hxy ▸ hy
    · intro hx
      exact ⟨x, hx, collapse_fix_singleton K hx⟩
  refine ⟨hnotinj, Module.not_finite_of_infinite_basis (AddMonoidAlgebra.basis ℕ K),
    D, coordinateSubcoalgebra_carrier K _, hDbot, hDtop, hDfg, hmap,
    Module.Finite.iff_fg.mpr hDfg, ?_, collapse_injOn_singleton K, ?_⟩
  · exact (Subcoalgebra.finite_map_iff_of_injOn (collapse K) D
      (collapse_injOn_singleton K)).mpr (Module.Finite.iff_fg.mpr hDfg)
  · intro x
    rw [Subcoalgebra.coe_equivMapOfInjOn_apply]
    exact collapse_fix_singleton K x.property

/-- The tensor left unitor transports a finite nonzero proper subcoalgebra to a finite
nonzero proper subcoalgebra of the tensor product. The vectors `1 ⊗ e₀` and `1 ⊗ e₁`
belong to the transported subcoalgebra, whereas `1 ⊗ e₂` does not. Transport back under
the unitor recovers the two-coordinate subcoalgebra. -/
theorem tensor_lid_supported_pair_transport :
    let e := Coalgebra.TensorProduct.lid K (AddMonoidAlgebra K ℕ)
    ∃ (D : Subcoalgebra K (AddMonoidAlgebra K ℕ))
      (E : Subcoalgebra K (K ⊗[K] AddMonoidAlgebra K ℕ)),
      D.toSubmodule = AddMonoidAlgebra.supported K K ({0, 1} : Set ℕ) ∧
      Module.Finite K D ∧ E = e.symm.subcoalgebraCongr D ∧
      e.subcoalgebraCongr E = D ∧ Module.Finite K E ∧
      E.toSubmodule ≠ ⊥ ∧ E.toSubmodule ≠ ⊤ ∧
      (1 : K) ⊗ₜ[K] AddMonoidAlgebra.single 0 (1 : K) ∈ E ∧
      (1 : K) ⊗ₜ[K] AddMonoidAlgebra.single 1 (1 : K) ∈ E ∧
      (1 : K) ⊗ₜ[K] AddMonoidAlgebra.single 2 (1 : K) ∉ E := by
  let e := Coalgebra.TensorProduct.lid K (AddMonoidAlgebra K ℕ)
  let D := coordinateSubcoalgebra K ({0, 1} : Set ℕ)
  let E := e.subcoalgebraCongr.symm D
  have hDfg : D.toSubmodule.FG :=
    Submodule.fg_span ((by simp : ({0, 1} : Set ℕ).Finite).image _)
  have hfinite : Module.Finite K D := Module.Finite.iff_fg.mpr hDfg
  have hEeq : E = e.symm.subcoalgebraCongr D := by
    change e.subcoalgebraCongr.symm D = e.symm.subcoalgebraCongr D
    rw [CoalgEquiv.subcoalgebraCongr_symm]
  have hback : e.subcoalgebraCongr E = D := e.subcoalgebraCongr.apply_symm_apply D
  have hmem (n : ℕ) :
      (1 : K) ⊗ₜ[K] AddMonoidAlgebra.single n (1 : K) ∈ E ↔ n ∈ ({0, 1} : Set ℕ) := by
    have htransport :
        (1 : K) ⊗ₜ[K] AddMonoidAlgebra.single n (1 : K) ∈ E ↔
          AddMonoidAlgebra.single n (1 : K) ∈ D := by
      have h := CoalgEquiv.mem_subcoalgebraCongr e E
        (AddMonoidAlgebra.single n (1 : K))
      rw [hback, Coalgebra.TensorProduct.lid_symm_apply] at h
      exact h.symm
    exact htransport.trans (single_mem_coordinateSubcoalgebra K _ n)
  have hnonzero : (1 : K) ⊗ₜ[K] AddMonoidAlgebra.single 0 (1 : K) ≠ 0 := by
    intro h
    have h' := congrArg (Coalgebra.TensorProduct.lid K (AddMonoidAlgebra K ℕ)) h
    have hzero : AddMonoidAlgebra.single 0 (1 : K) = 0 := by
      simpa only [Coalgebra.TensorProduct.lid_tmul, one_smul, map_zero] using h'
    exact (AddMonoidAlgebra.isGroupLikeElem_single_one (R := K) (A := K) 0).ne_zero hzero
  refine ⟨D, E, coordinateSubcoalgebra_carrier K _, hfinite, hEeq, hback, ?_, ?_, ?_,
    (hmem 0).mpr (by simp), (hmem 1).mpr (by simp), ?_⟩
  · exact (CoalgEquiv.finite_subcoalgebraCongr_iff e E).mp (by rwa [hback])
  · intro h
    have hx := (hmem 0).mpr (by simp)
    rw [Subcoalgebra.mem_iff, h, Submodule.mem_bot] at hx
    exact hnonzero hx
  · intro h
    have hx : (1 : K) ⊗ₜ[K] AddMonoidAlgebra.single 2 (1 : K) ∈ E.toSubmodule := by
      rw [h]
      exact Submodule.mem_top
    have htwo := (hmem 2).mp hx
    simp at htwo
  · intro hx
    have htwo := (hmem 2).mp hx
    simp at htwo

end Coalgebra
