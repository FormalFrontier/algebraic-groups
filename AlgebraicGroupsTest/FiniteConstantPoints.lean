/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import AlgebraicGroups.GroupScheme.FiniteConstantPoints

/-!
# Finite constant group-scheme point tests

These clients check locally constant points, coefficient naturality, and zero-ring targets.
They also construct weighted linear functionals from finite-support coordinates, with
nonzero two-coordinate and empty-index function-algebra examples.
-/

set_option warningAsError true

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

universe u

variable (K Γ R : Type u)
variable [CommRing K] [CommRing R] [Algebra K R] [Fintype Γ] [Group Γ]

-- The unrestricted theorem has no nontriviality hypothesis and therefore also
-- applies when the target algebra is the zero ring.
private noncomputable def persistentTestFiniteConstantPoints001 [Subsingleton R] :
    LocallyConstant (PrimeSpectrum R) Γ ≃*
      ((Spec (.of R)).asOver (Spec (.of K)) ⟶
        (finiteConstantGroupScheme K Γ).X) :=
  finiteConstantLocallyConstantMulEquivPoints K Γ R

private noncomputable def persistentTestFiniteConstantPoints002 [Nontrivial R]
    (h : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1) :
    Γ ≃* ((Spec (.of R)).asOver (Spec (.of K)) ⟶
      (finiteConstantGroupScheme K Γ).X) :=
  finiteConstantMulEquivPointsOfTrivialIdempotents K Γ R h

private theorem persistentTestFiniteConstantPoints003 (g : Γ) :
    (finiteConstantLocallyConstantMulEquivPoints K Γ K
      (LocallyConstant.const (PrimeSpectrum K) g)).left =
        (finiteConstantGroupSchemePoint K Γ g).left :=
  finiteConstantLocallyConstantMulEquivPoints_const K Γ g

/-- Pulling back a locally constant function agrees with changing coefficients of its point. -/
public theorem finiteConstantGroup_points_naturality {S : Type u} [CommRing S] [Algebra K S]
    (a : R →ₐ[K] S)
    (f : LocallyConstant (PrimeSpectrum R) Γ) :
    finiteConstantLocallyConstantMulEquivPoints K Γ S
        (LocallyConstant.comap
          ⟨PrimeSpectrum.comap a.toRingHom,
            PrimeSpectrum.continuous_comap a.toRingHom⟩ f) =
      (Spec.map (CommRingCat.ofHom a.toRingHom)).asOver (Spec (.of K)) ≫
        finiteConstantLocallyConstantMulEquivPoints K Γ R f :=
  finiteConstantLocallyConstantMulEquivPoints_naturality K Γ R a f

private noncomputable def persistentTestFiniteConstantPoints005 [Unique Γ] :
    FiniteGroupFunctions K Γ ≃ₐ[K] K :=
  FiniteGroupFunctions.uniqueAlgEquiv K Γ

end AlgebraicGeometry

namespace FiniteFunctionModels

universe u v

open AlgebraicGeometry
open AlgebraicGeometry.FiniteGroupFunctions

private noncomputable def weightedCoordinates (K : Type u) (Γ : Type v)
    [CommRing K] [Finite Γ] (w : Γ → K) :
    FiniteGroupFunctions K Γ →ₗ[K] K :=
  (basis K Γ).constr K w

private theorem weightedCoordinates_basis (K : Type u) (Γ : Type v)
    [CommRing K] [Finite Γ] (w : Γ → K) (g : Γ) :
    weightedCoordinates K Γ w (basis K Γ g) = w g := by
  exact (basis K Γ).constr_basis K w g

private theorem weightedCoordinates_apply (K : Type u) (Γ : Type v)
    [CommRing K] [Finite Γ] (w : Γ → K) (f : FiniteGroupFunctions K Γ) :
    weightedCoordinates K Γ w f =
      ((basis K Γ).repr f).sum (fun g c => c * w g) := by
  simpa only [weightedCoordinates, smul_eq_mul] using (basis K Γ).constr_apply K w f

private theorem reconstruct (K : Type u) (Γ : Type v)
    [CommRing K] [Finite Γ] (f : FiniteGroupFunctions K Γ) :
    Finsupp.linearCombination K (basis K Γ) ((basis K Γ).repr f) = f := by
  exact (basis K Γ).linearCombination_repr f

private theorem finite_module (K : Type u) (Γ : Type v)
    [CommRing K] [Finite Γ] : Module.Finite K (FiniteGroupFunctions K Γ) := by
  infer_instance

private def sample : FiniteGroupFunctions ℤ (Fin 2) :=
  fun i => if i = 0 then 3 else -2

private def weights : Fin 2 → ℤ := fun i => if i = 0 then 2 else 5

private theorem delta_diagonal : basis ℤ (Fin 2) 0 0 = 1 := by
  simp [basis_apply]

private theorem delta_offDiagonal : basis ℤ (Fin 2) 0 1 = 0 := by
  simp [basis_apply]

private theorem sample_repr_zero : (basis ℤ (Fin 2)).repr sample 0 = 3 := by
  simp [sample]

private theorem sample_repr_one : (basis ℤ (Fin 2)).repr sample 1 = -2 := by
  simp [sample]

private theorem sample_linearCombination :
    sample = (3 : ℤ) • basis ℤ (Fin 2) 0 + (-2 : ℤ) • basis ℤ (Fin 2) 1 := by
  apply (basis ℤ (Fin 2)).repr.injective
  rw [map_add, map_smul, map_smul, Module.Basis.repr_self, Module.Basis.repr_self]
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp [sample]
  · have hj : j = 0 := Subsingleton.elim _ _
    subst j
    simp [sample]

private theorem weightedCoordinates_sample :
    weightedCoordinates ℤ (Fin 2) weights sample = -4 := by
  rw [sample_linearCombination, map_add, map_smul, map_smul,
    weightedCoordinates_basis, weightedCoordinates_basis]
  decide

private def emptySample : FiniteGroupFunctions ℤ (Fin 0) := fun i => Fin.elim0 i

private theorem emptySample_zero : emptySample = 0 := by
  funext i
  exact Fin.elim0 i

private theorem emptySample_repr : (basis ℤ (Fin 0)).repr emptySample = 0 := by
  rw [emptySample_zero, map_zero]

private theorem weightedCoordinates_empty (w : Fin 0 → ℤ) :
    weightedCoordinates ℤ (Fin 0) w emptySample = 0 := by
  rw [emptySample_zero, map_zero]

end FiniteFunctionModels
