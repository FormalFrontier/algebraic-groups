/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.Hom
public import AlgebraicGroups.Algebra.HopfAlgebra.Subalgebra.Construction
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.Basic

/-!
# Corestriction to a stable subalgebra

A bialgebra homomorphism whose ordinary algebra range lies in a Hopf-stable subalgebra
factors uniquely through its inclusion. The source needs only a semiring, an algebra
structure and a coalgebra structure; no coalgebra laws on the source are used.

The target of every factor is the fixed coalgebra used in the induced Hopf structure.
The underlying algebra homomorphism is `AlgHom.codRestrict`, and coalgebra preservation
follows from `CoalgHom.ofComp`.
-/

@[expose] public section

universe u v w

namespace Subalgebra

variable {K : Type u} {B : Type v} [Field K] [Semiring B] [HopfAlgebra K B]
variable (S : Subalgebra K B)
variable {C : Type w} [Semiring C] [Algebra K C] [CoalgebraStruct K C]

/-- Homomorphisms into the induced coalgebra are determined by their ambient values. -/
@[ext]
theorem bialgHom_ext (h : S.IsHopfSubalgebra)
    {f g : @BialgHom K C S _ _ _ _ _ (inferInstance : CoalgebraStruct K C)
      (S.coalgebraOfComulMem h.comul_mem).toCoalgebraStruct}
    (hfg : ∀ c, (f c : B) = (g c : B)) : f = g :=
  @BialgHom.ext K C S _ _ _ _ _
    (inferInstance : CoalgebraStruct K C)
    (S.coalgebraOfComulMem h.comul_mem).toCoalgebraStruct f g
    (fun c => Subtype.ext (hfg c))

/-- Restrict a bialgebra homomorphism to a Hopf-stable subalgebra containing its range. -/
noncomputable def corestrict (h : S.IsHopfSubalgebra) (f : C →ₐc[K] B)
    (hf : f.toAlgHom.range ≤ S) :
    @BialgHom K C S _ _ _ _ _ (inferInstance : CoalgebraStruct K C)
      (S.coalgebraOfComulMem h.comul_mem).toCoalgebraStruct := by
  letI : CoalgebraStruct K S := (S.coalgebraOfComulMem h.comul_mem).toCoalgebraStruct
  let g : C →ₐ[K] S := f.toAlgHom.codRestrict S (fun c => hf ⟨c, rfl⟩)
  have hg : (S.inclusionBialgHom h).toLinearMap ∘ₗ g.toLinearMap =
      f.toLinearMap := by
    apply LinearMap.ext
    intro c
    change S.inclusionBialgHom h (g c) = f c
    rw [inclusionBialgHom_apply]
    rfl
  have hi : Function.Injective
      (TensorProduct.map (S.inclusionBialgHom h).toLinearMap
        (S.inclusionBialgHom h).toLinearMap) := by
    simp only [CoalgHom.toLinearMap_eq_coe, inclusionBialgHom_toLinearMap]
    have hB : (Module.addCommMonoidToAddCommGroup K (M := B)).toAddCommMonoid =
        (inferInstance : AddCommMonoid B) := rfl
    have hS : (Module.addCommMonoidToAddCommGroup K (M := S)).toAddCommMonoid =
        (inferInstance : AddCommMonoid S) := rfl
    cases hB
    cases hS
    let : AddCommGroup B := Module.addCommMonoidToAddCommGroup K
    let : AddCommGroup S := Module.addCommMonoidToAddCommGroup K
    exact TensorProduct.map_injective_of_flat_flat S.val.toLinearMap S.val.toLinearMap
      Subtype.val_injective Subtype.val_injective
  exact
    { toCoalgHom := CoalgHom.ofComp (S.inclusionBialgHom h).toCoalgHom f.toCoalgHom
        g.toLinearMap hg hi
      map_one' := g.map_one
      map_mul' := g.map_mul }

/-- The algebra homomorphism underlying corestriction is ordinary codomain restriction. -/
@[simp]
theorem corestrict_toAlgHom (h : S.IsHopfSubalgebra) (f : C →ₐc[K] B)
    (hf : f.toAlgHom.range ≤ S) :
    @BialgHom.toAlgHom K C S _ _ _ _ _
      (inferInstance : CoalgebraStruct K C)
      (S.coalgebraOfComulMem h.comul_mem).toCoalgebraStruct
      (S.corestrict h f hf) =
      f.toAlgHom.codRestrict S (fun c => hf ⟨c, rfl⟩) :=
  AlgHom.ext fun _ => rfl

/-- Corestriction preserves the ambient value of the homomorphism. -/
@[simp]
theorem corestrict_apply (h : S.IsHopfSubalgebra) (f : C →ₐc[K] B)
    (hf : f.toAlgHom.range ≤ S) (c : C) : (S.corestrict h f hf c : B) = f c :=
  rfl

/-- Inclusion after corestriction recovers the given homomorphism. -/
@[simp]
theorem inclusionBialgHom_comp_corestrict (h : S.IsHopfSubalgebra) (f : C →ₐc[K] B)
    (hf : f.toAlgHom.range ≤ S) :
    @BialgHom.comp K C S B _ _ _ _ _ _ _
      (inferInstance : CoalgebraStruct K C)
      (S.coalgebraOfComulMem h.comul_mem).toCoalgebraStruct
      (inferInstance : CoalgebraStruct K B)
      (S.inclusionBialgHom h) (S.corestrict h f hf) = f := by
  apply BialgHom.ext
  intro c
  simpa only [BialgHom.coe_comp, Function.comp_apply, inclusionBialgHom_apply] using
    S.corestrict_apply h f hf c

/-- A factor through the fixed inclusion is the corestriction. -/
theorem lift_unique (h : S.IsHopfSubalgebra) (f : C →ₐc[K] B)
    (hf : f.toAlgHom.range ≤ S)
    (g : @BialgHom K C S _ _ _ _ _ (inferInstance : CoalgebraStruct K C)
      (S.coalgebraOfComulMem h.comul_mem).toCoalgebraStruct)
    (hg : @BialgHom.comp K C S B _ _ _ _ _ _ _
      (inferInstance : CoalgebraStruct K C)
      (S.coalgebraOfComulMem h.comul_mem).toCoalgebraStruct
      (inferInstance : CoalgebraStruct K B)
      (S.inclusionBialgHom h) g = f) : g = S.corestrict h f hf := by
  apply S.bialgHom_ext h
  intro c
  simpa only [BialgHom.coe_comp, Function.comp_apply, inclusionBialgHom_apply,
    corestrict_apply] using BialgHom.congr_fun hg c

/-- There is a unique factor through the inclusion into the ambient Hopf algebra. -/
theorem existsUnique_lift (h : S.IsHopfSubalgebra) (f : C →ₐc[K] B)
    (hf : f.toAlgHom.range ≤ S) :
    ∃! g : @BialgHom K C S _ _ _ _ _ (inferInstance : CoalgebraStruct K C)
      (S.coalgebraOfComulMem h.comul_mem).toCoalgebraStruct,
      @BialgHom.comp K C S B _ _ _ _ _ _ _
        (inferInstance : CoalgebraStruct K C)
        (S.coalgebraOfComulMem h.comul_mem).toCoalgebraStruct
        (inferInstance : CoalgebraStruct K B)
        (S.inclusionBialgHom h) g = f :=
  ⟨S.corestrict h f hf, S.inclusionBialgHom_comp_corestrict h f hf,
    fun g hg => S.lift_unique h f hf g hg⟩

end Subalgebra
