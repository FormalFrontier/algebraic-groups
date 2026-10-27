/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.HopfAlgebra.Hom
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.ZMod.Basic

/-!
# Antipodes over semirings and noncommutative group algebras

The augmentation and the map induced by the trivial group endomorphism are
bialgebra homomorphisms over `ℕ`. Antipode compatibility identifies their values
on arbitrary finite sums, not only on group elements. The group `S₃ × ℤ` gives
an infinite index type and a noncommutative group algebra; the trivial
endomorphism is not injective. The scalar identity also covers the zero ring.

Mathlib's group-algebra Hopf structures and `mapDomainBialgHom` provide the
structures and morphisms used here. Ordinary augmentation is also refined using
comultiplication preservation, recovering the same bundled map and the same
noninjective finite-sum collapse formulas.
-/

@[expose] public section

noncomputable section

namespace HopfAlgebraExamples

universe u

/-- The antipode on the scalar Hopf algebra over `ℕ` fixes every scalar. -/
theorem nat_scalar_antipode (n : ℕ) : HopfAlgebra.antipode ℕ n = n := by
  simp only [CommSemiring.antipode_eq_id, LinearMap.id_apply]

/-- Antipode compatibility for the scalar identity includes the zero ring. -/
theorem zero_scalar_antipode (x : ZMod 1) :
    HopfAlgebra.antipode (ZMod 1) x = x := by
  simp only [CommSemiring.antipode_eq_id, LinearMap.id_apply]

/-- Augmentation of a group algebra over `ℕ` is invariant under the antipode. -/
theorem nat_augmentation_antipode {G : Type u} [Group G] (x : MonoidAlgebra ℕ G) :
    Coalgebra.counit (R := ℕ) (HopfAlgebra.antipode ℕ x) =
      Coalgebra.counit (R := ℕ) x := by
  simpa only [Bialgebra.counitBialgHom_apply, CommSemiring.antipode_eq_id,
    LinearMap.id_apply] using (Bialgebra.counitBialgHom ℕ (MonoidAlgebra ℕ G)).map_antipode x

/-- The direct product of the symmetric group on three letters with the infinite cyclic group. -/
abbrev PermutationLattice := Equiv.Perm (Fin 3) × Multiplicative ℤ

/-- The index group of this group algebra is infinite. -/
theorem permutationLattice_infinite : Infinite PermutationLattice := inferInstance

/-- The group-algebra endomorphism induced by the trivial group endomorphism. -/
def collapse : MonoidAlgebra ℕ PermutationLattice →ₐc[ℕ]
    MonoidAlgebra ℕ PermutationLattice :=
  MonoidAlgebra.mapDomainBialgHom ℕ (1 : PermutationLattice →* PermutationLattice)

/-- Every basis term collapses to the unit group element, with its coefficient unchanged. -/
@[simp]
theorem collapse_single (g : PermutationLattice) (n : ℕ) :
    collapse (MonoidAlgebra.single g n) = MonoidAlgebra.single 1 n := by
  simp [collapse]

/-- On a finite sum, collapse retains the sum of its coefficients. -/
theorem collapse_eq_augmentation (x : MonoidAlgebra ℕ PermutationLattice) :
    collapse x = MonoidAlgebra.single 1 (Coalgebra.counit (R := ℕ) x) := by
  induction x using MonoidAlgebra.induction_linear <;> simp_all

/-- Collapse after inversion of a finite sum equals its augmentation at the unit element. -/
theorem collapse_antipode (x : MonoidAlgebra ℕ PermutationLattice) :
    collapse (HopfAlgebra.antipode ℕ x) =
      MonoidAlgebra.single 1 (Coalgebra.counit (R := ℕ) x) := by
  rw [collapse.map_antipode, collapse_eq_augmentation]
  simp

/-- Collapse is noninjective: a transposition basis term and the unit basis term
have equal images. -/
theorem collapse_not_injective : ¬ Function.Injective collapse := by
  intro h
  have hs : (MonoidAlgebra.single (Equiv.swap (0 : Fin 3) 1, 1) 1 :
      MonoidAlgebra ℕ PermutationLattice) = MonoidAlgebra.single 1 1 :=
    h (by simp)
  have hg := MonoidAlgebra.single_left_injective (by decide : (1 : ℕ) ≠ 0) hs
  have he := congrArg (fun g : PermutationLattice => g.1 (0 : Fin 3)) hg
  simp at he

/-- Two transposition basis terms witness noncommutativity of the group algebra over `ℕ`. -/
theorem permutationLattice_algebra_noncommutative :
    ∃ x y : MonoidAlgebra ℕ PermutationLattice, x * y ≠ y * x := by
  refine ⟨MonoidAlgebra.single (Equiv.swap (0 : Fin 3) 1, 1) 1,
    MonoidAlgebra.single (Equiv.swap (1 : Fin 3) 2, 1) 1, ?_⟩
  intro h
  simp only [MonoidAlgebra.single_mul_single, mul_one] at h
  have hg := MonoidAlgebra.single_left_injective (by decide : (1 : ℕ) ≠ 0) h
  have he := congrArg (fun g : PermutationLattice => g.1 (0 : Fin 3)) hg
  have hn : ((Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2) (0 : Fin 3)) ≠
      ((Equiv.swap (1 : Fin 3) 2 * Equiv.swap (0 : Fin 3) 1) (0 : Fin 3)) := by decide
  exact hn he

/-- Augmentation of a group algebra over `ℕ` preserves comultiplication. -/
theorem nat_augmentation_map_comp_comul {G : Type u} [Group G] :
    (TensorProduct.map
      (Bialgebra.counitAlgHom ℕ (MonoidAlgebra ℕ G)).toLinearMap
      (Bialgebra.counitAlgHom ℕ (MonoidAlgebra ℕ G)).toLinearMap) ∘ₗ
        (Coalgebra.comul (R := ℕ) (A := MonoidAlgebra ℕ G)) =
      (Coalgebra.comul (R := ℕ) (A := ℕ)) ∘ₗ
        (Bialgebra.counitAlgHom ℕ (MonoidAlgebra ℕ G)).toLinearMap := by
  exact CoalgHomClass.map_comp_comul
    (Bialgebra.counitBialgHom ℕ (MonoidAlgebra ℕ G))

/-- Automatic counit preservation for augmentation of the infinite, noncommutative
`ℕ`-group algebra on `S₃ × ℤ`. -/
theorem permutationLattice_augmentation_counit_comp :
    (Coalgebra.counit (R := ℕ) (A := ℕ)) ∘ₗ
        (Bialgebra.counitAlgHom ℕ (MonoidAlgebra ℕ PermutationLattice)).toLinearMap =
      Coalgebra.counit (R := ℕ) (A := MonoidAlgebra ℕ PermutationLattice) := by
  exact AlgHom.counit_comp_of_map_comp_comul
    (Bialgebra.counitAlgHom ℕ (MonoidAlgebra ℕ PermutationLattice))
    (nat_augmentation_map_comp_comul (G := PermutationLattice))

/-- For a nontrivial group, distinct basis terms have the same augmentation `1`. -/
theorem nat_augmentation_noninjective_witness {G : Type u} [Group G] [Nontrivial G] :
    ∃ g : G, g ≠ 1 ∧
      (MonoidAlgebra.single g 1 : MonoidAlgebra ℕ G) ≠ MonoidAlgebra.single 1 1 ∧
      Bialgebra.counitAlgHom ℕ (MonoidAlgebra ℕ G) (MonoidAlgebra.single g 1) = 1 ∧
      Bialgebra.counitAlgHom ℕ (MonoidAlgebra ℕ G) (MonoidAlgebra.single 1 1) = 1 := by
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  refine ⟨g, hg, ?_, ?_, ?_⟩
  · intro h
    exact hg (MonoidAlgebra.single_left_injective (by decide : (1 : ℕ) ≠ 0) h)
  · simp
  · simp

/-- Evaluation at zero on the diagonal bialgebra `ℕ[ℕ]` gives an algebra map
preserving comultiplication but not the counit. -/
theorem nat_addMonoidAlgebra_exists_map_comp_comul_not_counit :
    ∃ f : AddMonoidAlgebra ℕ ℕ →ₐ[ℕ] ℕ,
      ((TensorProduct.map f.toLinearMap f.toLinearMap) ∘ₗ
        (Coalgebra.comul (R := ℕ) (A := AddMonoidAlgebra ℕ ℕ)) =
          (Coalgebra.comul (R := ℕ) (A := ℕ)) ∘ₗ f.toLinearMap) ∧
      ¬ ((Coalgebra.counit (R := ℕ) (A := ℕ)) ∘ₗ f.toLinearMap =
        Coalgebra.counit (R := ℕ) (A := AddMonoidAlgebra ℕ ℕ)) := by
  let f : AddMonoidAlgebra ℕ ℕ →ₐ[ℕ] ℕ :=
    AddMonoidAlgebra.lift ℕ ℕ ℕ (powersHom ℕ 0)
  refine ⟨f, ?_, ?_⟩
  · apply AddMonoidAlgebra.lhom_ext'
    intro n
    apply LinearMap.ext
    intro a
    cases n <;> simp [f, pow_succ]
  · intro h
    have he := LinearMap.congr_fun h (AddMonoidAlgebra.single 1 1)
    have hz : (0 : ℕ) = 1 := by simp [f] at he
    exact Nat.zero_ne_one hz

/-- Augmentation of the infinite noncommutative group algebra, obtained by
refining its ordinary algebra map using comultiplication preservation. -/
def augmentation : MonoidAlgebra ℕ PermutationLattice →ₐc[ℕ] ℕ :=
  (Bialgebra.counitAlgHom ℕ (MonoidAlgebra ℕ PermutationLattice)).toBialgHomOfComul
    nat_augmentation_map_comp_comul

/-- The refined augmentation has exactly the original underlying algebra map. -/
@[simp]
theorem augmentation_toAlgHom :
    augmentation.toAlgHom = Bialgebra.counitAlgHom ℕ (MonoidAlgebra ℕ PermutationLattice) :=
  AlgHom.toBialgHomOfComul_toAlgHom _ _

/-- Refining ordinary augmentation recovers the same bundled counit map. -/
theorem augmentation_eq_counitBialgHom :
    augmentation = Bialgebra.counitBialgHom ℕ (MonoidAlgebra ℕ PermutationLattice) :=
  BialgHom.toAlgHom_toBialgHomOfComul
    (Bialgebra.counitBialgHom ℕ (MonoidAlgebra ℕ PermutationLattice))

/-- Collapse factors through the refined augmentation on every finite sum. -/
theorem collapse_eq_single_augmentation (x : MonoidAlgebra ℕ PermutationLattice) :
    collapse x = MonoidAlgebra.single 1 (augmentation x) := by
  simpa only [augmentation_eq_counitBialgHom, Bialgebra.counitBialgHom_apply] using
    collapse_eq_augmentation x

/-- The same distinct basis terms remain a noninjectivity witness after refinement. -/
theorem augmentation_not_injective : ¬ Function.Injective augmentation := by
  obtain ⟨g, _, hne, hg, h1⟩ :=
    nat_augmentation_noninjective_witness (G := PermutationLattice)
  intro h
  have hval (x : MonoidAlgebra ℕ PermutationLattice) :
      augmentation x = Bialgebra.counitAlgHom ℕ (MonoidAlgebra ℕ PermutationLattice) x :=
    DFunLike.congr_fun augmentation_toAlgHom x
  exact hne (h (by rw [hval, hval, hg, h1]))


end HopfAlgebraExamples
