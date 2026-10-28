/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.DirectSum
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.RingTheory.Coalgebra.Basic

/-!
# Direct sums of regular Finsupp comodules

The regular comodule of the Finsupp coalgebra over the natural numbers has
one diagonal comultiplication term for each basis vector. Component maps and
Finsupp evaluation distinguish two inputs in its countable direct sum.
A tensor coordinate separates the same-summand coaction from a pure tensor
with cross terms. The empty direct sum has zero coaction.
-/

@[expose] public section

noncomputable section

open Coalgebra Coalgebra.RightComodule
open scoped DirectSum TensorProduct

namespace RightComoduleDirectSumRegular

/-- The Finsupp coalgebra over the natural numbers. -/
abbrev C := ℕ →₀ ℕ

/-- The countable direct sum of the underlying coalgebra modules. -/
abbrev D := ⨁ _ : ℕ, C

/-- The basis vector at a natural-number index. -/
def basis (k : ℕ) : C := Finsupp.single k 1

/-- The whole regular comodule in every summand. -/
def regularFamily (_ : ℕ) : RightComodule ℕ C C := regular ℕ C

/-- The direct sum of the regular comodules. -/
def sumComodule : RightComodule ℕ C D := directSum regularFamily

/-- The linear inclusion of one coalgebra module into the direct sum. -/
def inclusion (i : ℕ) : C →ₗ[ℕ] D := directSumLof ℕ (fun _ : ℕ => C) i

/-- The zeroth basis vector in the zeroth summand. -/
def a : D := inclusion 0 (basis 0)

/-- The first basis vector in the first summand. -/
def b : D := inclusion 1 (basis 1)

/-- Evaluation at a basis coordinate after projection onto a summand. -/
def coordinate (i k : ℕ) : D →ₗ[ℕ] ℕ :=
  (Finsupp.lapply k : C →ₗ[ℕ] ℕ).comp
    (DirectSum.component ℕ ℕ (fun _ : ℕ => C) i)

private theorem component_inclusion (i : ℕ) (c : C) :
    DirectSum.component ℕ ℕ (fun _ : ℕ => C) i (inclusion i c) = c := by
  simp only [inclusion, directSumLof_eq_lof, DirectSum.component.lof_self]

private theorem component_inclusion_of_ne {i j : ℕ} (h : j ≠ i) (c : C) :
    DirectSum.component ℕ ℕ (fun _ : ℕ => C) i (inclusion j c) = 0 := by
  simp only [inclusion, directSumLof_eq_lof, DirectSum.component.of, h, dite_false]

private theorem coordinate_inclusion (i k : ℕ) (c : C) :
    coordinate i k (inclusion i c) = c k := by
  change (Finsupp.lapply k : C →ₗ[ℕ] ℕ)
    (DirectSum.component ℕ ℕ (fun _ : ℕ => C) i (inclusion i c)) = c k
  simp only [component_inclusion, Finsupp.lapply_apply]

private theorem coordinate_inclusion_of_ne {i j : ℕ} (h : j ≠ i) (k : ℕ) (c : C) :
    coordinate i k (inclusion j c) = 0 := by
  change (Finsupp.lapply k : C →ₗ[ℕ] ℕ)
    (DirectSum.component ℕ ℕ (fun _ : ℕ => C) i (inclusion j c)) = 0
  simp only [component_inclusion_of_ne h, map_zero]

/-- Component evaluation separates the two selected inputs. -/
theorem input_readbacks :
    coordinate 0 0 a = 1 ∧ coordinate 0 0 b = 0 ∧
      coordinate 1 1 a = 0 ∧ coordinate 1 1 b = 1 := by
  simp [a, b, coordinate_inclusion, coordinate_inclusion_of_ne, basis]

/-- The selected inputs are nonzero and distinct. -/
theorem inputs_nonzero_distinct : a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b := by
  obtain ⟨haa, hab, _, hbb⟩ := input_readbacks
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hz : coordinate 0 0 a = 0 := by rw [h, map_zero]
    exact Nat.one_ne_zero (haa.symm.trans hz)
  · intro h
    have hz : coordinate 1 1 b = 0 := by rw [h, map_zero]
    exact Nat.one_ne_zero (hbb.symm.trans hz)
  · intro h
    have heq : coordinate 0 0 a = coordinate 0 0 b :=
      congrArg (fun d : D => coordinate 0 0 d) h
    exact Nat.one_ne_zero (haa.symm.trans (heq.trans hab))

/-- Comultiplication of a basis vector is diagonal. -/
theorem comul_basis (k : ℕ) :
    comul (R := ℕ) (A := C) (basis k) = basis k ⊗ₜ[ℕ] basis k := by
  simp only [basis, Finsupp.comul_single, CommSemiring.comul_apply,
    TensorProduct.map_tmul, Finsupp.lsingle_apply]

/-- The counit of each basis vector is one. -/
theorem counit_basis (k : ℕ) : counit (R := ℕ) (A := C) (basis k) = 1 := by
  simp only [basis, Finsupp.counit_single, CommSemiring.counit_apply]

/-- The direct-sum coaction on an included basis vector. -/
theorem coaction_inclusion_basis (i k : ℕ) :
    sumComodule.coaction (inclusion i (basis k)) =
      inclusion i (basis k) ⊗ₜ[ℕ] basis k := by
  calc
    sumComodule.coaction (inclusion i (basis k)) =
        (inclusion i).rTensor C ((regularFamily i).coaction (basis k)) :=
      directSum_coaction_lof regularFamily i (basis k)
    _ = _ := by
      have hregular : (regularFamily i).coaction (basis k) =
          comul (R := ℕ) (A := C) (basis k) := rfl
      rw [hregular, comul_basis, LinearMap.rTensor_tmul]

/-- The coaction of the two inputs has one term in each of their summands. -/
theorem coaction_add_inputs :
    sumComodule.coaction (a + b) = a ⊗ₜ[ℕ] basis 0 + b ⊗ₜ[ℕ] basis 1 := by
  simp only [a, b, map_add, coaction_inclusion_basis]

/-- Two basis vectors in the same summand still give only diagonal terms. -/
theorem coaction_same_summand (i : ℕ) :
    sumComodule.coaction (inclusion i (basis 0 + basis 1)) =
      inclusion i (basis 0) ⊗ₜ[ℕ] basis 0 +
        inclusion i (basis 1) ⊗ₜ[ℕ] basis 1 := by
  simp only [map_add, coaction_inclusion_basis]

/-- The tensor coordinate with first basis index zero and second basis index one. -/
def crossCoefficient (i : ℕ) : D ⊗[ℕ] C →ₗ[ℕ] ℕ :=
  (TensorProduct.lid ℕ ℕ).toLinearMap.comp
    (TensorProduct.map (coordinate i 0) (Finsupp.lapply 1 : C →ₗ[ℕ] ℕ))

private theorem crossCoefficient_tmul (i : ℕ) (d : D) (c : C) :
    crossCoefficient i (d ⊗ₜ[ℕ] c) = coordinate i 0 d • c 1 := by
  change (TensorProduct.lid ℕ ℕ)
    (TensorProduct.map (coordinate i 0) (Finsupp.lapply 1 : C →ₗ[ℕ] ℕ)
      (d ⊗ₜ[ℕ] c)) = _
  simp only [TensorProduct.map_tmul, TensorProduct.lid_tmul, Finsupp.lapply_apply]

/-- The off-diagonal tensor coordinate of the same-summand coaction vanishes. -/
theorem crossCoefficient_coaction (i : ℕ) :
    crossCoefficient i (sumComodule.coaction (inclusion i (basis 0 + basis 1))) = 0 := by
  calc
    crossCoefficient i (sumComodule.coaction (inclusion i (basis 0 + basis 1))) =
        crossCoefficient i (inclusion i (basis 0) ⊗ₜ[ℕ] basis 0 +
          inclusion i (basis 1) ⊗ₜ[ℕ] basis 1) :=
      congrArg (crossCoefficient i) (coaction_same_summand i)
    _ = 0 := by simp [crossCoefficient_tmul, coordinate_inclusion, basis]

/-- The corresponding coordinate of the pure tensor is one. -/
theorem crossCoefficient_pure (i : ℕ) :
    crossCoefficient i (inclusion i (basis 0 + basis 1) ⊗ₜ[ℕ] (basis 0 + basis 1)) = 1 := by
  calc
    crossCoefficient i (inclusion i (basis 0 + basis 1) ⊗ₜ[ℕ] (basis 0 + basis 1)) =
        coordinate i 0 (inclusion i (basis 0 + basis 1)) • (basis 0 + basis 1) 1 :=
      crossCoefficient_tmul i _ _
    _ = 1 := by simp [coordinate_inclusion, basis]

/-- The same-summand coaction is not the pure tensor with cross terms. -/
theorem coaction_same_summand_ne_pure (i : ℕ) :
    sumComodule.coaction (inclusion i (basis 0 + basis 1)) ≠
      inclusion i (basis 0 + basis 1) ⊗ₜ[ℕ] (basis 0 + basis 1) := by
  intro h
  have heq := congrArg (crossCoefficient i) h
  rw [crossCoefficient_coaction, crossCoefficient_pure] at heq
  exact Nat.zero_ne_one heq

/-- The empty direct sum of the coalgebra modules. -/
abbrev EmptyD := ⨁ _ : Empty, C

/-- The direct sum of the empty family of regular comodules. -/
def emptyComodule : RightComodule ℕ C EmptyD :=
  directSum (fun _ : Empty => regular ℕ C)

/-- Every element of the empty direct sum is zero. -/
theorem empty_eq_zero (d : EmptyD) : d = 0 := by
  apply DirectSum.ext_component ℕ
  intro i
  cases i

/-- The coaction of the empty direct sum is the zero linear map. -/
theorem empty_coaction_eq_zero :
    emptyComodule.coaction = (0 : EmptyD →ₗ[ℕ] EmptyD ⊗[ℕ] C) := by
  apply LinearMap.ext
  intro d
  change emptyComodule.coaction d = (0 : EmptyD ⊗[ℕ] C)
  exact (congrArg (fun x : EmptyD => emptyComodule.coaction x)
    (empty_eq_zero d)).trans emptyComodule.coaction.map_zero

end RightComoduleDirectSumRegular

namespace RightComoduleDirectSumRegular

/-- The identity of the whole regular comodule at every natural-number index. -/
def identityFamily (i : ℕ) : RightComoduleHom (regularFamily i) (regular ℕ C) :=
  RightComoduleHom.id (regular ℕ C)

/-- The morphism extending the everywhere-identity family on the direct sum. -/
def identityDesc : RightComoduleHom sumComodule (regular ℕ C) :=
  RightComoduleHom.desc identityFamily

/-- Restriction along every bundled summand inclusion recovers its identity map. -/
theorem identityDesc_comp_lof (i : ℕ) :
    identityDesc.comp (RightComoduleHom.lof regularFamily i) = identityFamily i := by
  have hinc : (RightComoduleHom.lof regularFamily i).toLinearMap = inclusion i :=
    RightComoduleHom.lof_toLinearMap regularFamily i
  have hmap : identityDesc.toLinearMap ∘ₗ
      (RightComoduleHom.lof regularFamily i).toLinearMap =
        (identityFamily i).toLinearMap :=
    (congrArg (fun f : C →ₗ[ℕ] D => identityDesc.toLinearMap ∘ₗ f) hinc).trans
      (RightComoduleHom.desc_toLinearMap_comp_lof identityFamily i)
  apply RightComoduleHom.ext
  intro c
  exact LinearMap.congr_fun hmap c

/-- The extension returns every element of every regular summand unchanged. -/
theorem identityDesc_inclusion (i : ℕ) (c : C) : identityDesc (inclusion i c) = c := by
  calc
    identityDesc (inclusion i c) = (identityFamily i).toLinearMap c :=
      RightComoduleHom.desc_toLinearMap_lof identityFamily i c
    _ = c := RightComoduleHom.id_apply (regular ℕ C) c

/-- The extension sends the zeroth selected input to the zeroth basis vector. -/
theorem identityDesc_a : identityDesc a = basis 0 :=
  identityDesc_inclusion 0 (basis 0)

/-- The extension sends the first selected input to the first basis vector. -/
theorem identityDesc_b : identityDesc b = basis 1 :=
  identityDesc_inclusion 1 (basis 1)

/-- The sum of the selected inputs maps to the sum of their two basis vectors. -/
theorem identityDesc_add_inputs : identityDesc (a + b) = basis 0 + basis 1 := by
  calc
    identityDesc (a + b) = identityDesc a + identityDesc b :=
      identityDesc.toLinearMap.map_add a b
    _ = basis 0 + basis 1 := by rw [identityDesc_a, identityDesc_b]

/-- Both basis coordinates of the image of the sum are nonzero. -/
theorem identityDesc_add_readbacks :
    (identityDesc (a + b)) 0 = 1 ∧ (identityDesc (a + b)) 1 = 1 := by
  have hcoords : (basis 0 + basis 1) 0 = 1 ∧ (basis 0 + basis 1) 1 = 1 := by
    simp [basis]
  simpa only [identityDesc_add_inputs] using hcoords

/-- The extension intertwines the two coactions. -/
theorem identityDesc_colinear :
    (regular ℕ C).coaction ∘ₗ identityDesc.toLinearMap =
      identityDesc.toLinearMap.rTensor C ∘ₗ sumComodule.coaction :=
  identityDesc.colinear

/-- Colinearity transports the two-term coaction of the selected sum. -/
theorem identityDesc_coaction_add_inputs :
    (regular ℕ C).coaction (identityDesc (a + b)) =
      basis 0 ⊗ₜ[ℕ] basis 0 + basis 1 ⊗ₜ[ℕ] basis 1 := by
  calc
    (regular ℕ C).coaction (identityDesc (a + b)) =
        identityDesc.toLinearMap.rTensor C (sumComodule.coaction (a + b)) :=
      RightComoduleHom.colinear_apply identityDesc (a + b)
    _ = identityDesc.toLinearMap.rTensor C
        (a ⊗ₜ[ℕ] basis 0 + b ⊗ₜ[ℕ] basis 1) :=
      congrArg (identityDesc.toLinearMap.rTensor C) coaction_add_inputs
    _ = basis 0 ⊗ₜ[ℕ] basis 0 + basis 1 ⊗ₜ[ℕ] basis 1 := by
      simp only [map_add, LinearMap.rTensor_tmul, RightComoduleHom.toLinearMap_apply,
        identityDesc_a, identityDesc_b]

end RightComoduleDirectSumRegular

namespace RightComoduleDirectSumRegular

/-- The coproduct equivalence for the empty family, with the whole regular target. -/
def emptyEquiv : RightComoduleHom emptyComodule (regular ℕ C) ≃
    (∀ _ : Empty, RightComoduleHom (regular ℕ C) (regular ℕ C)) :=
  RightComoduleHom.directSumEquiv (fun _ : Empty => regular ℕ C) (regular ℕ C)

/-- Every map from the empty direct sum is recovered from all its restrictions. -/
theorem emptyEquiv_left_inverse (h : RightComoduleHom emptyComodule (regular ℕ C)) :
    emptyEquiv.symm (emptyEquiv h) = h := by
  exact emptyEquiv.symm_apply_apply h

/-- Every empty family is recovered by restricting its extension. -/
theorem emptyEquiv_right_inverse
    (φ : ∀ _ : Empty, RightComoduleHom (regular ℕ C) (regular ℕ C)) :
    emptyEquiv (emptyEquiv.symm φ) = φ := by
  have hinverse : emptyEquiv.symm φ = RightComoduleHom.desc φ :=
    RightComoduleHom.directSumEquiv_symm_apply φ
  calc
    emptyEquiv (emptyEquiv.symm φ) = emptyEquiv (RightComoduleHom.desc φ) :=
      congrArg (fun h : RightComoduleHom emptyComodule (regular ℕ C) => emptyEquiv h)
        hinverse
    _ = (fun i : Empty => (RightComoduleHom.desc φ).comp
        (RightComoduleHom.lof (fun _ : Empty => regular ℕ C) i)) := by
      funext i
      exact RightComoduleHom.directSumEquiv_apply (RightComoduleHom.desc φ) i
    _ = φ := RightComoduleHom.desc_comp_lof_family φ

end RightComoduleDirectSumRegular
