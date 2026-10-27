/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.Quotient

/-!
# Coideal correspondence for a surjective coalgebra homomorphism

For a surjective coalgebra homomorphism, map and comap identify the coideals of
its source containing its linear kernel with the coideals of its target.
The construction uses ordinary submodules and their inherited orders. Both
coalgebra structures are weak: no coalgebra laws, field, flatness or finiteness
hypotheses are imposed. No complete-lattice or intersection assertion is made.

## References

Mathlib's `RingTheory.Coalgebra.Quotient` supplies the coideal predicate and
canonical quotient structures; `RingTheory.Coalgebra.Hom` supplies the generic
morphism class. The underlying map/comap correspondence is the one formalized
by Mathlib's `Submodule.comapMkQRelIso` and `Submodule.orderIsoMapComap`.
-/

@[expose] public section

universe u v w z

namespace Submodule

variable {R : Type u} [CommRing R]
variable {C : Type v} [AddCommGroup C] [Module R C] [CoalgebraStruct R C]
variable {D : Type w} [AddCommGroup D] [Module R D] [CoalgebraStruct R D]
variable {F : Type z} [FunLike F C D] [CoalgHomClass F R C D]

/-- The preimage of a coideal under a surjective coalgebra homomorphism is a coideal. -/
theorem IsCoideal.comap_of_surjective {J : Submodule R D} (hJ : J.IsCoideal)
    (f : F) (hf : Function.Surjective f) : (J.comap (f : C →ₗ[R] D)).IsCoideal := by
  let : J.IsCoideal := hJ
  let g := (Coalgebra.Quotient.mkQCoalgHom J).comp (CoalgHomClass.toCoalgHom f)
  have hg : Function.Surjective g := J.mkQ_surjective.comp hf
  have hker := CoalgHomClass.ker_isCoideal_of_surjective g hg
  have hlinear :
      (CoalgHomClass.toCoalgHom f : C →ₗ[R] D) = (f : C →ₗ[R] D) := by
    apply DFunLike.coe_injective
    simp only [CoalgHom.coe_coe, LinearMap.coe_ofClass]
  simpa only [g, CoalgHom.comp_toLinearMap,
    Coalgebra.Quotient.mkQCoalgHom_toLinearMap, hlinear,
    LinearMap.ker_comp, Submodule.ker_mkQ] using hker

/-- Map and comap give an order isomorphism between source coideals containing the
linear kernel and target coideals of a surjective coalgebra homomorphism. -/
def coidealOrderIsoOfSurjective (f : F) (hf : Function.Surjective f) :
    {I : Submodule R C // I.IsCoideal ∧ (f : C →ₗ[R] D).ker ≤ I} ≃o
      {J : Submodule R D // J.IsCoideal} where
  toFun I := ⟨I.val.map (f : C →ₗ[R] D), by
    exact I.property.1.map f⟩
  invFun J := ⟨J.val.comap (f : C →ₗ[R] D),
    J.property.comap_of_surjective f hf, by
      exact LinearMap.ker_le_comap (f : C →ₗ[R] D)⟩
  left_inv I := Subtype.ext (Submodule.comap_map_eq_self I.property.2)
  right_inv J := Subtype.ext (Submodule.map_comap_eq_of_surjective hf J.val)
  map_rel_iff' := by
    intro I K
    change I.val.map (f : C →ₗ[R] D) ≤ K.val.map (f : C →ₗ[R] D) ↔ I.val ≤ K.val
    rw [Submodule.map_le_iff_le_comap, Submodule.comap_map_eq_self K.property.2]

/-- The forward correspondence has the ordinary submodule image as its value. -/
@[simp]
theorem coidealOrderIsoOfSurjective_apply_val (f : F) (hf : Function.Surjective f)
    (I : {I : Submodule R C // I.IsCoideal ∧ (f : C →ₗ[R] D).ker ≤ I}) :
    (coidealOrderIsoOfSurjective f hf I).val = I.val.map (f : C →ₗ[R] D) :=
  rfl

/-- The inverse correspondence has the ordinary submodule preimage as its value. -/
@[simp]
theorem coidealOrderIsoOfSurjective_symm_apply_val (f : F) (hf : Function.Surjective f)
    (J : {J : Submodule R D // J.IsCoideal}) :
    ((coidealOrderIsoOfSurjective f hf).symm J).val = J.val.comap (f : C →ₗ[R] D) :=
  rfl

end Submodule
