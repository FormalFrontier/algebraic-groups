/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.Surjective
public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra

/-!
# Surjective descent on infinite monoid coalgebras

The first projection induces a surjective, noninjective map
`ℕ[ℕ × ℕ] →ₐc[ℕ] ℕ[ℕ]`. Both monoid index sets are infinite, and the scalars
form a semiring rather than a ring. The map and its section use Mathlib's
`MonoidAlgebra.mapDomainBialgHom`; no quotient or finiteness hypothesis is needed.
-/

@[expose] public section

open Coalgebra TensorProduct

namespace MonoidAlgebra

/-- The first projection on monoid coalgebras is surjective. -/
theorem fst_mapDomainBialgHom_surjective :
    Function.Surjective (mapDomainBialgHom ℕ (MonoidHom.fst ℕ ℕ)) := by
  intro y
  refine ⟨mapDomainBialgHom ℕ (MonoidHom.inl ℕ ℕ) y, ?_⟩
  rw [mapDomainBialgHom_mapDomainBialgHom, MonoidHom.fst_comp_inl,
    mapDomainBialgHom_id, BialgHom.id_apply]

/-- Two distinct group-like basis vectors have the same first projection. -/
theorem fst_mapDomainBialgHom_not_injective :
    ¬ Function.Injective (mapDomainBialgHom ℕ (MonoidHom.fst ℕ ℕ)) := by
  intro h
  have heq : (single (0, 0) 1 : ℕ[ℕ × ℕ]) = single (0, 1) 1 := h (by simp)
  have hcoeff := congrArg (fun x : ℕ[ℕ × ℕ] => x.coeff (0, 0)) heq
  simp at hcoeff

/-- All three coalgebra laws descend along the noninjective first projection. -/
theorem fst_mapDomainBialgHom_coalgebra_laws :
    (TensorProduct.assoc ℕ ℕ[ℕ] ℕ[ℕ] ℕ[ℕ] ∘ₗ
        (comul (R := ℕ) (A := ℕ[ℕ])).rTensor ℕ[ℕ] ∘ₗ comul =
      comul.lTensor ℕ[ℕ] ∘ₗ comul) ∧
    ((counit (R := ℕ) (A := ℕ[ℕ])).rTensor ℕ[ℕ] ∘ₗ comul =
      TensorProduct.mk ℕ _ _ 1) ∧
    ((counit (R := ℕ) (A := ℕ[ℕ])).lTensor ℕ[ℕ] ∘ₗ comul =
      (TensorProduct.mk ℕ _ _).flip 1) := by
  exact ⟨coassoc_of_surjective (mapDomainBialgHom ℕ (MonoidHom.fst ℕ ℕ))
      fst_mapDomainBialgHom_surjective,
    rTensor_counit_comp_comul_of_surjective (mapDomainBialgHom ℕ (MonoidHom.fst ℕ ℕ))
      fst_mapDomainBialgHom_surjective,
    lTensor_counit_comp_comul_of_surjective (mapDomainBialgHom ℕ (MonoidHom.fst ℕ ℕ))
      fst_mapDomainBialgHom_surjective⟩

/-- Cocommutativity descends separately along the first projection. -/
theorem fst_mapDomainBialgHom_isCocomm : IsCocomm ℕ ℕ[ℕ] := by
  exact isCocomm_of_surjective (mapDomainBialgHom ℕ (MonoidHom.fst ℕ ℕ))
    fst_mapDomainBialgHom_surjective

end MonoidAlgebra

/-!
## Why surjectivity is necessary

Map preservation only transports the laws to the range of the map. For the zero
module `Fin 0 → ℕ`, both structure maps are zero and all three coalgebra laws
hold. On the target `ℕ`, take comultiplication zero and counit the identity.
The zero map preserves both maps, but misses `1`; left counitality fails there
since `ℕ ⊗[ℕ] ℕ ≃ₗ[ℕ] ℕ` sends `1 ⊗ₜ 1` to `1`, not zero.

Descent needs no field, flatness, projectivity, finiteness or linear splitting:
it uses only preservation, tensor functoriality and surjectivity. The projection
model above also shows that injectivity, and hence bijectivity, is unnecessary.
-/

namespace Coalgebra

section NonSurjectiveBoundary

@[instance_reducible]
private def boundaryZeroSourceCoalgebra : Coalgebra ℕ (Fin 0 → ℕ) where
  comul := 0
  counit := 0
  coassoc := Subsingleton.elim _ _
  rTensor_counit_comp_comul := Subsingleton.elim _ _
  lTensor_counit_comp_comul := Subsingleton.elim _ _

@[instance_reducible]
private def boundaryWeakNatCoalgebraStruct : CoalgebraStruct ℕ ℕ where
  comul := 0
  counit := LinearMap.id

attribute [local instance] boundaryZeroSourceCoalgebra boundaryWeakNatCoalgebraStruct

private def boundaryZeroHom : (Fin 0 → ℕ) →ₗc[ℕ] ℕ where
  toLinearMap := 0
  counit_comp := Subsingleton.elim _ _
  map_comp_comul := Subsingleton.elim _ _

/-- Preservation without surjectivity need not transport even left counitality. -/
theorem zeroSourceHom_not_surjective_and_counit_failure :
    let f : @CoalgHom ℕ (Fin 0 → ℕ) ℕ _ _ _ _ _
        ({ comul := 0, counit := 0 } : CoalgebraStruct ℕ (Fin 0 → ℕ))
        ({ comul := 0, counit := LinearMap.id } : CoalgebraStruct ℕ ℕ) :=
      @CoalgHom.mk ℕ (Fin 0 → ℕ) ℕ _ _ _ _ _
        ({ comul := 0, counit := 0 } : CoalgebraStruct ℕ (Fin 0 → ℕ))
        ({ comul := 0, counit := LinearMap.id } : CoalgebraStruct ℕ ℕ)
        0 (Subsingleton.elim _ _) (Subsingleton.elim _ _);
    (¬ Function.Surjective f) ∧
      (@CoalgebraStruct.counit ℕ ℕ _ _ _
        ({ comul := 0, counit := LinearMap.id } : CoalgebraStruct ℕ ℕ)).rTensor ℕ ∘ₗ
        (@CoalgebraStruct.comul ℕ ℕ _ _ _
          ({ comul := 0, counit := LinearMap.id } : CoalgebraStruct ℕ ℕ)) ≠
          TensorProduct.mk ℕ _ _ 1 := by
  change (¬ Function.Surjective boundaryZeroHom) ∧
    (counit (R := ℕ) (A := ℕ)).rTensor ℕ ∘ₗ comul ≠ TensorProduct.mk ℕ _ _ 1
  constructor
  · intro h
    obtain ⟨x, hx⟩ := h 1
    simp [boundaryZeroHom] at hx
  · intro h
    have h1 := LinearMap.congr_fun h 1
    let F := (counit (R := ℕ) (A := ℕ)).rTensor ℕ
    have hcomul : (comul (R := ℕ) (A := ℕ)) 1 = 0 := rfl
    have hzero : (F ∘ₗ (comul (R := ℕ) (A := ℕ))) 1 = 0 :=
      (LinearMap.comp_apply F (comul (R := ℕ) (A := ℕ)) 1).trans
        ((congrArg F hcomul).trans F.map_zero)
    have hNat : (0 : ℕ) = 1 := by
      simpa only [map_zero, TensorProduct.mk_apply,
        TensorProduct.lid_tmul, one_smul] using
        congrArg (TensorProduct.lid ℕ ℕ) (hzero.symm.trans h1)
    exact zero_ne_one hNat

end NonSurjectiveBoundary

end Coalgebra

namespace MonoidAlgebra

/-- Surjective descent constructs a cocommutative coalgebra on the infinite projection target. -/
theorem fst_mapDomainBialgHom_ofSurjective_isCocomm :
    @Coalgebra.IsCocomm ℕ ℕ[ℕ] _ _ _
      (Coalgebra.ofSurjective (mapDomainBialgHom ℕ (MonoidHom.fst ℕ ℕ))
        fst_mapDomainBialgHom_surjective) := by
  exact Coalgebra.ofSurjective_isCocomm (mapDomainBialgHom ℕ (MonoidHom.fst ℕ ℕ))
    fst_mapDomainBialgHom_surjective

end MonoidAlgebra

/-!
## Negation changes the selected coalgebra data

For negation on `ℤ`, the source of descent has the scalar coalgebra and the target
has its pullback along negation. These are different structures on the same module:
the pulled-back counit takes `1` to `-1`, whereas the scalar counit takes `1` to `1`.
The canonical equivalence supplies the preserving map without identifying those data.
-/

namespace LinearEquiv

/-- Descent along negation recovers its transported coalgebra, whose counit differs
from the scalar counit. Both coalgebra-data arguments are fixed explicitly. -/
theorem neg_int_coalgebra_transport :
    (@Coalgebra.ofSurjective ℤ ℤ ℤ
      (@CoalgHom ℤ ℤ ℤ _ _ _ _ _ (CommSemiring.toCoalgebra ℤ).toCoalgebraStruct
        ((neg ℤ : ℤ ≃ₗ[ℤ] ℤ).coalgebraStruct ℤ))
      _ _ _ _ _ (CommSemiring.toCoalgebra ℤ)
      ((neg ℤ : ℤ ≃ₗ[ℤ] ℤ).coalgebraStruct ℤ) _ _
      (@CoalgEquiv.toCoalgHom ℤ _ ℤ ℤ _ _ _ _ (CommSemiring.toCoalgebra ℤ).toCoalgebraStruct
        ((neg ℤ : ℤ ≃ₗ[ℤ] ℤ).coalgebraStruct ℤ)
        (@CoalgEquiv.symm ℤ ℤ ℤ _ _ _ _ _ ((neg ℤ : ℤ ≃ₗ[ℤ] ℤ).coalgebraStruct ℤ)
          (CommSemiring.toCoalgebra ℤ).toCoalgebraStruct
          (@toCoalgEquiv ℤ ℤ ℤ _ _ _ _ _ (CommSemiring.toCoalgebra ℤ).toCoalgebraStruct
            (neg ℤ))))
      (neg ℤ : ℤ ≃ₗ[ℤ] ℤ).symm.surjective =
        (neg ℤ : ℤ ≃ₗ[ℤ] ℤ).coalgebra ℤ) ∧
    (@CoalgebraStruct.counit ℤ ℤ _ _ _
      ((neg ℤ : ℤ ≃ₗ[ℤ] ℤ).coalgebraStruct ℤ) 1 = -1) ∧
    (@CoalgebraStruct.counit ℤ ℤ _ _ _
      ((neg ℤ : ℤ ≃ₗ[ℤ] ℤ).coalgebraStruct ℤ) 1 ≠
        @CoalgebraStruct.counit ℤ ℤ _ _ _ (CommSemiring.toCoalgebra ℤ).toCoalgebraStruct 1) := by
  have hε : @CoalgebraStruct.counit ℤ ℤ _ _ _
      ((neg ℤ : ℤ ≃ₗ[ℤ] ℤ).coalgebraStruct ℤ) 1 = -1 := by
    simpa only [LinearEquiv.neg_apply, CommSemiring.counit_apply] using
      (@LinearEquiv.coalgebraStruct_counit_apply ℤ ℤ ℤ _ _ _ _ _
        (CommSemiring.toCoalgebra ℤ).toCoalgebraStruct (neg ℤ) 1)
  refine ⟨Coalgebra.ofSurjective_coalgebra (neg ℤ : ℤ ≃ₗ[ℤ] ℤ), hε, ?_⟩
  rw [hε, CommSemiring.counit_apply]
  decide

end LinearEquiv
