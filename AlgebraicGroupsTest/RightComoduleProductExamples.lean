/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.Prod
public import AlgebraicGroupsTest.RightComoduleProduct

/-!
# Coordinates of product comodules

The product of the two specified natural-number comodules has the independent
two-weight coaction. Its colinear projections and the tensor left unitor recover
the distinct basis-zero and basis-one weights. The product of two bottom-submodule
scalar comodules gives a zero boundary case.

The examples use the public product and projection equations, Mathlib's tensor
distribution and unitors, and the independent models in `RightComoduleProduct`.
Pairing, coordinate extensionality and the plain Hom equivalence are exercised on
these same specified inputs.
-/

@[expose] public noncomputable section

universe u v w z

open scoped TensorProduct

namespace Coalgebra.RightComodule

section Coordinates

variable {R : Type u} {C : Type v} {M : Type w} {N : Type z}
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- Both colinear coordinates commute with the coaction of a linear combination,
using the canonical scalar action and addition on the product module. -/
theorem prod_coaction_smul_add_coordinates
    (X : RightComodule R C M) (Y : RightComodule R C N) (r : R) (p q : M × N) :
    ((RightComoduleHom.fst X Y).toLinearMap.rTensor C
        ((prod X Y).coaction (r • p + q)),
      (RightComoduleHom.snd X Y).toLinearMap.rTensor C
        ((prod X Y).coaction (r • p + q))) =
      (r • X.coaction p.1 + X.coaction q.1,
        r • Y.coaction p.2 + Y.coaction q.2) := by
  rw [← (RightComoduleHom.fst X Y).colinear_apply (r • p + q),
    ← (RightComoduleHom.snd X Y).colinear_apply (r • p + q)]
  simp

end Coordinates

namespace TwoWeight

/-- The product of the basis-zero and basis-one comodules on `ℕ`. -/
def productComodule : RightComodule ℕ (MonoidAlgebra ℕ ℕ) (ℕ × ℕ) :=
  prod basisZeroComodule basisOneComodule

/-- The first colinear projection of the two-weight product. -/
def productFst : RightComoduleHom productComodule basisZeroComodule :=
  RightComoduleHom.fst basisZeroComodule basisOneComodule

/-- The second colinear projection of the two-weight product. -/
def productSnd : RightComoduleHom productComodule basisOneComodule :=
  RightComoduleHom.snd basisZeroComodule basisOneComodule

/-- The product coaction agrees with the independently formed sum of weighted tensors. -/
theorem productComodule_coaction : productComodule.coaction = weightedCoaction := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  have hw : TensorProduct.prodLeft ℕ ℕ ℕ ℕ (MonoidAlgebra ℕ ℕ)
      (weightedCoaction (x, y)) = (x ⊗ₜ[ℕ] basisZero, y ⊗ₜ[ℕ] basisOne) := by
    simp
  have hp := prodLeft_coaction_prod basisZeroComodule basisOneComodule (x, y)
  simp only [basisZeroComodule_coaction, basisOneComodule_coaction] at hp
  exact (TensorProduct.prodLeft ℕ ℕ ℕ ℕ (MonoidAlgebra ℕ ℕ)).injective
    (hp.trans hw.symm)

/-- The two colinear projections have the canonical coordinate linear maps. -/
theorem product_projection_maps :
    productFst.toLinearMap = LinearMap.fst ℕ ℕ ℕ ∧
      productSnd.toLinearMap = LinearMap.snd ℕ ℕ ℕ := by
  constructor <;> simp only [productFst, productSnd,
    RightComoduleHom.fst_toLinearMap, RightComoduleHom.snd_toLinearMap]

example : productComodule.coaction (1, 0) = (1, 0) ⊗ₜ[ℕ] basisZero := by
  exact (LinearMap.congr_fun productComodule_coaction (1, 0)).trans
    weightedCoaction_one_zero

example : productComodule.coaction (0, 1) = (0, 1) ⊗ₜ[ℕ] basisOne := by
  exact (LinearMap.congr_fun productComodule_coaction (0, 1)).trans
    weightedCoaction_zero_one

/-- The first product projection and left unitor recover the basis-zero weight. -/
@[simp] theorem lid_productFst_coaction_one_zero :
    TensorProduct.lid ℕ (MonoidAlgebra ℕ ℕ)
      (productFst.toLinearMap.rTensor (MonoidAlgebra ℕ ℕ)
        (productComodule.coaction (1, 0))) = basisZero := by
  rw [product_projection_maps.1, productComodule_coaction]
  exact lid_fst_weightedCoaction_one_zero

/-- The second product projection and left unitor recover the basis-one weight. -/
@[simp] theorem lid_productSnd_coaction_zero_one :
    TensorProduct.lid ℕ (MonoidAlgebra ℕ ℕ)
      (productSnd.toLinearMap.rTensor (MonoidAlgebra ℕ ℕ)
        (productComodule.coaction (0, 1))) = basisOne := by
  rw [product_projection_maps.2, productComodule_coaction]
  exact lid_snd_weightedCoaction_zero_one

/-- The two weights recovered from the product coaction are distinct. -/
theorem product_projected_weights_ne :
    TensorProduct.lid ℕ (MonoidAlgebra ℕ ℕ)
        (productFst.toLinearMap.rTensor (MonoidAlgebra ℕ ℕ)
          (productComodule.coaction (1, 0))) ≠
      TensorProduct.lid ℕ (MonoidAlgebra ℕ ℕ)
        (productSnd.toLinearMap.rTensor (MonoidAlgebra ℕ ℕ)
          (productComodule.coaction (0, 1))) := by
  simpa only [lid_productFst_coaction_one_zero, lid_productSnd_coaction_zero_one]
    using basisZero_ne_basisOne

/-- Pair the basis-zero identity with the existing zero colinear map. -/
def basisZeroPair : RightComoduleHom basisZeroComodule productComodule :=
  RightComoduleHom.pair (RightComoduleHom.id basisZeroComodule)
    (0 : RightComoduleHom basisZeroComodule basisOneComodule)

/-- Pair the existing zero colinear map with the basis-one identity. -/
def basisOnePair : RightComoduleHom basisOneComodule productComodule :=
  RightComoduleHom.pair (0 : RightComoduleHom basisOneComodule basisZeroComodule)
    (RightComoduleHom.id basisOneComodule)

@[simp] theorem basisZeroPair_apply (n : ℕ) : basisZeroPair n = (n, 0) := by
  exact (RightComoduleHom.pair_apply (RightComoduleHom.id basisZeroComodule)
    (0 : RightComoduleHom basisZeroComodule basisOneComodule) n).trans
      (Prod.ext (RightComoduleHom.id_apply basisZeroComodule n)
        (RightComoduleHom.zero_apply (X := basisZeroComodule) (Y := basisOneComodule) n))

@[simp] theorem basisOnePair_apply (n : ℕ) : basisOnePair n = (0, n) := by
  exact (RightComoduleHom.pair_apply
    (0 : RightComoduleHom basisOneComodule basisZeroComodule)
    (RightComoduleHom.id basisOneComodule) n).trans
      (Prod.ext
        (RightComoduleHom.zero_apply (X := basisOneComodule) (Y := basisZeroComodule) n)
        (RightComoduleHom.id_apply basisOneComodule n))

/-- The pairings have the identity and zero as their specified coordinates. -/
theorem axisPair_projections :
    productFst.comp basisZeroPair = RightComoduleHom.id basisZeroComodule ∧
      productSnd.comp basisZeroPair = 0 ∧
      productFst.comp basisOnePair = 0 ∧
      productSnd.comp basisOnePair = RightComoduleHom.id basisOneComodule := by
  exact ⟨RightComoduleHom.fst_pair (RightComoduleHom.id basisZeroComodule)
      (0 : RightComoduleHom basisZeroComodule basisOneComodule),
    RightComoduleHom.snd_pair (RightComoduleHom.id basisZeroComodule)
      (0 : RightComoduleHom basisZeroComodule basisOneComodule),
    RightComoduleHom.fst_pair
      (0 : RightComoduleHom basisOneComodule basisZeroComodule)
      (RightComoduleHom.id basisOneComodule),
    RightComoduleHom.snd_pair
      (0 : RightComoduleHom basisOneComodule basisZeroComodule)
      (RightComoduleHom.id basisOneComodule)⟩

/-- The two pairings at one retain their different product coactions. -/
theorem axisPair_coactions :
    productComodule.coaction (basisZeroPair 1) = (1, 0) ⊗ₜ[ℕ] basisZero ∧
      productComodule.coaction (basisOnePair 1) = (0, 1) ⊗ₜ[ℕ] basisOne := by
  constructor
  · exact (congrArg productComodule.coaction (basisZeroPair_apply 1)).trans
      ((LinearMap.congr_fun productComodule_coaction (1, 0)).trans
        weightedCoaction_one_zero)
  · exact (congrArg productComodule.coaction (basisOnePair_apply 1)).trans
      ((LinearMap.congr_fun productComodule_coaction (0, 1)).trans
        weightedCoaction_zero_one)

/-- Tensorized projections of the paired vectors retain both weights. -/
theorem axisPair_tensor_projections :
    (productFst.toLinearMap.rTensor (MonoidAlgebra ℕ ℕ)
        (productComodule.coaction (basisZeroPair 1)),
      productSnd.toLinearMap.rTensor (MonoidAlgebra ℕ ℕ)
        (productComodule.coaction (basisOnePair 1))) =
      (1 ⊗ₜ[ℕ] basisZero, 1 ⊗ₜ[ℕ] basisOne) := by
  apply Prod.ext
  · rw [basisZeroPair_apply, product_projection_maps.1, productComodule_coaction]
    exact fst_weightedCoaction 1 0
  · rw [basisOnePair_apply, product_projection_maps.2, productComodule_coaction]
    exact snd_weightedCoaction 0 1

/-- Applying the left unitor recovers the two weights from the pairings. -/
theorem axisPair_lid_projections :
    (TensorProduct.lid ℕ (MonoidAlgebra ℕ ℕ)
        (productFst.toLinearMap.rTensor (MonoidAlgebra ℕ ℕ)
          (productComodule.coaction (basisZeroPair 1))),
      TensorProduct.lid ℕ (MonoidAlgebra ℕ ℕ)
        (productSnd.toLinearMap.rTensor (MonoidAlgebra ℕ ℕ)
          (productComodule.coaction (basisOnePair 1)))) = (basisZero, basisOne) := by
  simp only [basisZeroPair_apply, basisOnePair_apply, lid_productFst_coaction_one_zero,
    lid_productSnd_coaction_zero_one]

/-- The two pairings recover genuinely different weights. -/
theorem axisPair_projected_weights_ne :
    TensorProduct.lid ℕ (MonoidAlgebra ℕ ℕ)
        (productFst.toLinearMap.rTensor (MonoidAlgebra ℕ ℕ)
          (productComodule.coaction (basisZeroPair 1))) ≠
      TensorProduct.lid ℕ (MonoidAlgebra ℕ ℕ)
        (productSnd.toLinearMap.rTensor (MonoidAlgebra ℕ ℕ)
          (productComodule.coaction (basisOnePair 1))) := by
  simpa only [basisZeroPair_apply, basisOnePair_apply] using product_projected_weights_ne

/-- Coordinate extensionality identifies the pairing of the projections with the identity. -/
theorem pair_product_projections :
    RightComoduleHom.pair productFst productSnd = RightComoduleHom.id productComodule := by
  apply RightComoduleHom.prod_ext
  · exact (RightComoduleHom.fst_pair productFst productSnd).trans
      (RightComoduleHom.comp_id productFst).symm
  · exact (RightComoduleHom.snd_pair productFst productSnd).trans
      (RightComoduleHom.comp_id productSnd).symm

/-- The universal property sends the actual projections to the product identity. -/
theorem prodEquiv_product_projections :
    RightComoduleHom.prodEquiv basisZeroComodule basisOneComodule productComodule
        (productFst, productSnd) = RightComoduleHom.id productComodule := by
  simpa only [RightComoduleHom.prodEquiv_apply] using pair_product_projections

/-- The inverse universal property reads the projections off the actual identity. -/
theorem prodEquiv_symm_product_identity :
    (RightComoduleHom.prodEquiv basisZeroComodule basisOneComodule productComodule).symm
        (RightComoduleHom.id productComodule) = (productFst, productSnd) := by
  exact (RightComoduleHom.prodEquiv_symm_apply basisZeroComodule basisOneComodule
    productComodule (RightComoduleHom.id productComodule)).trans
      (Prod.ext (RightComoduleHom.comp_id productFst) (RightComoduleHom.comp_id productSnd))

/-- The inverse universal property reads the identity and zero off both pairings. -/
theorem prodEquiv_symm_axisPairs :
    (RightComoduleHom.prodEquiv basisZeroComodule basisOneComodule basisZeroComodule).symm
        basisZeroPair = (RightComoduleHom.id basisZeroComodule, 0) ∧
      (RightComoduleHom.prodEquiv basisZeroComodule basisOneComodule basisOneComodule).symm
        basisOnePair = (0, RightComoduleHom.id basisOneComodule) := by
  simp [RightComoduleHom.prodEquiv_symm_apply, basisZeroPair, basisOnePair]

end TwoWeight

/-- The product of two scalar comodules on the bottom submodule of `ℕ`. -/
def zeroProduct :
    RightComodule ℕ ℕ ((⊥ : Submodule ℕ ℕ) × (⊥ : Submodule ℕ ℕ)) :=
  prod zeroBoundary zeroBoundary

/-- The first colinear projection of the bottom-submodule product. -/
def zeroProductFst : RightComoduleHom zeroProduct zeroBoundary :=
  RightComoduleHom.fst zeroBoundary zeroBoundary

/-- The second colinear projection of the bottom-submodule product. -/
def zeroProductSnd : RightComoduleHom zeroProduct zeroBoundary :=
  RightComoduleHom.snd zeroBoundary zeroBoundary

/-- The bottom-submodule product has zero coaction on every vector. -/
@[simp] theorem zeroProduct_coaction
    (p : (⊥ : Submodule ℕ ℕ) × (⊥ : Submodule ℕ ℕ)) :
    zeroProduct.coaction p = 0 := by
  simp only [zeroProduct, coaction_prod_apply, zeroBoundary_coaction]
  exact map_zero (TensorProduct.prodLeft ℕ ℕ
    (⊥ : Submodule ℕ ℕ) (⊥ : Submodule ℕ ℕ) ℕ).symm

/-- Both canonical colinear projections of the zero product take the value zero. -/
theorem zeroProduct_projections
    (p : (⊥ : Submodule ℕ ℕ) × (⊥ : Submodule ℕ ℕ)) :
    zeroProductFst p = 0 ∧ zeroProductSnd p = 0 := by
  exact ⟨(RightComoduleHom.fst_apply zeroBoundary zeroBoundary p).trans
      (zeroBoundary_eq_zero p.1),
    (RightComoduleHom.snd_apply zeroBoundary zeroBoundary p).trans
      (zeroBoundary_eq_zero p.2)⟩

/-- Pairing the bottom-product projections still reconstructs the identity. -/
theorem zeroProduct_pair_projections :
    RightComoduleHom.pair zeroProductFst zeroProductSnd =
      RightComoduleHom.id zeroProduct := by
  exact RightComoduleHom.pair_fst_snd zeroBoundary zeroBoundary

/-- The universal property also sends the bottom projections to their product identity. -/
theorem zeroProduct_prodEquiv_projections :
    RightComoduleHom.prodEquiv zeroBoundary zeroBoundary zeroProduct
        (zeroProductFst, zeroProductSnd) = RightComoduleHom.id zeroProduct := by
  simpa only [RightComoduleHom.prodEquiv_apply] using zeroProduct_pair_projections

/-- The inverse universal property recovers the bottom-product projections. -/
theorem zeroProduct_prodEquiv_symm_identity :
    (RightComoduleHom.prodEquiv zeroBoundary zeroBoundary zeroProduct).symm
        (RightComoduleHom.id zeroProduct) = (zeroProductFst, zeroProductSnd) := by
  exact (RightComoduleHom.prodEquiv_symm_apply zeroBoundary zeroBoundary zeroProduct
    (RightComoduleHom.id zeroProduct)).trans
      (Prod.ext (RightComoduleHom.comp_id zeroProductFst)
        (RightComoduleHom.comp_id zeroProductSnd))

end Coalgebra.RightComodule
