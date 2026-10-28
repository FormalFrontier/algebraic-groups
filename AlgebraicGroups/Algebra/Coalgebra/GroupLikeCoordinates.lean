/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import TauCeti.Algebra.Coalgebra.Subcoalgebra.GroupLike
public import AlgebraicGroups.Algebra.Coalgebra.GroupLikeHom
public import AlgebraicGroups.Algebra.Coalgebra.MonoidAlgebra
public import AlgebraicGroups.Algebra.Coalgebra.Subcoalgebra.Hom
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# Coalgebra coordinates for group-like bases

A given basis of group-like elements identifies a coalgebra over a commutative
semiring with the free diagonal coalgebra on the basis index. Coalgebra maps
out of it correspond to arbitrary families of group-like elements in the target.
This correspondence is natural in the target; no multiplication on the index
or classification of all group-like elements is involved.

Over a field, the span of the group-like elements is a subcoalgebra. Canonical
evaluation identifies it, as a coalgebra, with the free diagonal coalgebra indexed
by those group-like elements. The inverse coefficients are the stock linear
coordinates of the linearly independent group-like family. In these coordinates,
ambient comultiplication is diagonal and the counit is the sum of coefficients.

The equivalence is with the span, not necessarily the whole ambient coalgebra.
No finite-dimensionality or nonempty group-like family is required.

## References

Mathlib supplies `linearIndep_groupLikeVal`,
`LinearIndependent.linearCombinationEquiv`, `LinearIndependent.repr` and
`MonoidAlgebra.coeffLinearEquiv`. The subcoalgebra assembles the span-closure
result in `TauCeti.Algebra.Coalgebra.Subcoalgebra.GroupLike` with the constructor
and restricted coalgebra in the subcoalgebra modules.
The equivalences use the existing `MonoidAlgebra.liftGroupLikeCoalgHom` and
`MonoidAlgebra.liftGroupLikeCoalgHomEquiv`. The field-span construction is
identified with the given-basis construction on its canonical span basis.
-/

@[expose] public section

open TauCeti


universe uR uC uD uI uE uK

open scoped MonoidAlgebra TensorProduct

section GroupLikeBasis

variable {R : Type uR} {C : Type uC} {D : Type uD} {I : Type uI}
variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid D] [Module R D] [Coalgebra R D]

namespace Module.Basis

variable (b : Module.Basis I R C) (hb : ∀ i, IsGroupLikeElem R (b i))

private theorem liftGroupLikeCoalgHom_basis_toLinearMap :
    (MonoidAlgebra.liftGroupLikeCoalgHom (fun i => ⟨b i, hb i⟩)).toLinearMap =
      ((MonoidAlgebra.coeffLinearEquiv R).trans b.repr.symm).toLinearMap := by
  apply LinearMap.ext
  intro x
  exact (b.repr_symm_apply ((MonoidAlgebra.coeffLinearEquiv R) x)).symm

/-- Evaluation on a given group-like basis identifies its coalgebra with the
free diagonal coalgebra on the basis index. -/
noncomputable def groupLikeCoalgebraEquiv : R[I] ≃ₗc[R] C :=
  CoalgEquiv.ofBijective
    (f := MonoidAlgebra.liftGroupLikeCoalgHom (fun i => ⟨b i, hb i⟩)) (by
      change Function.Bijective
        (MonoidAlgebra.liftGroupLikeCoalgHom (fun i => ⟨b i, hb i⟩)).toLinearMap
      rw [liftGroupLikeCoalgHom_basis_toLinearMap b hb]
      exact ((MonoidAlgebra.coeffLinearEquiv R).trans b.repr.symm).bijective)

/-- The equivalence uses the canonical coalgebra evaluation map. -/
theorem groupLikeCoalgebraEquiv_toCoalgHom :
    (b.groupLikeCoalgebraEquiv hb).toCoalgHom =
      MonoidAlgebra.liftGroupLikeCoalgHom (fun i => ⟨b i, hb i⟩) := by
  rfl

/-- The linear coordinates use the coefficient equivalence of the monoid-algebra wrapper. -/
theorem groupLikeCoalgebraEquiv_toLinearEquiv :
    (b.groupLikeCoalgebraEquiv hb).toLinearEquiv =
      (MonoidAlgebra.coeffLinearEquiv R).trans b.repr.symm := by
  apply LinearEquiv.toLinearMap_injective
  change (b.groupLikeCoalgebraEquiv hb).toCoalgHom.toLinearMap = _
  rw [groupLikeCoalgebraEquiv_toCoalgHom b hb]
  exact liftGroupLikeCoalgHom_basis_toLinearMap b hb

/-- A monomial evaluates to the corresponding multiple of the basis vector. -/
@[simp]
theorem groupLikeCoalgebraEquiv_single (i : I) (r : R) :
    b.groupLikeCoalgebraEquiv hb (MonoidAlgebra.single i r) = r • b i := by
  change (b.groupLikeCoalgebraEquiv hb).toCoalgHom (MonoidAlgebra.single i r) = _
  rw [groupLikeCoalgebraEquiv_toCoalgHom b hb]
  exact MonoidAlgebra.liftGroupLikeCoalgHom_single _ i r

/-- The inverse coefficients are precisely the given basis coordinates. -/
theorem groupLikeCoalgebraEquiv_symm_coeff (x : C) :
    ((b.groupLikeCoalgebraEquiv hb).symm x).coeff = b.repr x := by
  have h := congrArg (fun e : R[I] ≃ₗ[R] C => e.symm x)
    (b.groupLikeCoalgebraEquiv_toLinearEquiv hb)
  exact congrArg (fun y : R[I] => y.coeff) h

/-- A basis vector has singleton inverse coordinates. -/
@[simp]
theorem groupLikeCoalgebraEquiv_symm_basis (i : I) :
    (b.groupLikeCoalgebraEquiv hb).symm (b i) = MonoidAlgebra.single i 1 := by
  apply EquivLike.injective (b.groupLikeCoalgebraEquiv hb)
  simp only [CoalgEquiv.apply_symm_apply, groupLikeCoalgebraEquiv_single, one_smul]

/-- Coalgebra maps from a coalgebra with a given group-like basis correspond to
arbitrary group-like families in the target. -/
noncomputable def groupLikeCoalgHomEquiv : (C →ₗc[R] D) ≃ (I → GroupLike R D) where
  toFun F := MonoidAlgebra.liftGroupLikeCoalgHomEquiv.symm
    (F.comp (b.groupLikeCoalgebraEquiv hb).toCoalgHom)
  invFun f := (MonoidAlgebra.liftGroupLikeCoalgHom f).comp
    (b.groupLikeCoalgebraEquiv hb).symm.toCoalgHom
  left_inv := by
    intro F
    apply CoalgHom.ext
    intro x
    have h := CoalgHom.congr_fun
      (MonoidAlgebra.liftGroupLikeCoalgHomEquiv.apply_symm_apply
        (F.comp (b.groupLikeCoalgebraEquiv hb).toCoalgHom))
      ((b.groupLikeCoalgebraEquiv hb).symm x)
    simpa only [MonoidAlgebra.liftGroupLikeCoalgHomEquiv_apply, CoalgHom.comp_apply,
      CoalgEquiv.toCoalgHom_eq_ofClass, CoalgEquiv.coe_coalgHomOfClass,
          CoalgEquiv.apply_symm_apply] using h
  right_inv := by
    intro f
    have h : ((MonoidAlgebra.liftGroupLikeCoalgHom f).comp
        (b.groupLikeCoalgebraEquiv hb).symm.toCoalgHom).comp
        (b.groupLikeCoalgebraEquiv hb).toCoalgHom =
        MonoidAlgebra.liftGroupLikeCoalgHom f := by
      apply CoalgHom.ext
      intro x
      simp only [CoalgHom.comp_apply, CoalgEquiv.toCoalgHom_eq_ofClass,
          CoalgEquiv.coe_coalgHomOfClass,
        CoalgEquiv.symm_apply_apply]
    change MonoidAlgebra.liftGroupLikeCoalgHomEquiv.symm
      (((MonoidAlgebra.liftGroupLikeCoalgHom f).comp
        (b.groupLikeCoalgebraEquiv hb).symm.toCoalgHom).comp
        (b.groupLikeCoalgebraEquiv hb).toCoalgHom) = f
    rw [h]
    exact MonoidAlgebra.liftGroupLikeCoalgHomEquiv.symm_apply_apply f

/-- The family associated to a coalgebra map is its value on the chosen basis. -/
@[simp]
theorem groupLikeCoalgHomEquiv_apply (F : C →ₗc[R] D) (i : I) :
    b.groupLikeCoalgHomEquiv hb F i = GroupLike.map F ⟨b i, hb i⟩ := by
  apply GroupLike.val_injective
  change ((MonoidAlgebra.liftGroupLikeCoalgHomEquiv.symm
    (F.comp (b.groupLikeCoalgebraEquiv hb).toCoalgHom)) i).val = _
  rw [MonoidAlgebra.liftGroupLikeCoalgHomEquiv_symm_apply_val]
  simp only [CoalgHom.comp_apply, CoalgEquiv.toCoalgHom_eq_ofClass, CoalgEquiv.coe_coalgHomOfClass,
    groupLikeCoalgebraEquiv_single, one_smul, GroupLike.map_val]

/-- Extension is the existing diagonal-coalgebra lift transported through basis coordinates. -/
theorem groupLikeCoalgHomEquiv_symm_apply (f : I → GroupLike R D) :
    (b.groupLikeCoalgHomEquiv hb).symm f =
      (MonoidAlgebra.liftGroupLikeCoalgHom f).comp
        (b.groupLikeCoalgebraEquiv hb).symm.toCoalgHom := by
  rfl

/-- Extension takes each basis vector to the prescribed group-like value. -/
@[simp]
theorem groupLikeCoalgHomEquiv_symm_apply_basis (f : I → GroupLike R D) (i : I) :
    (b.groupLikeCoalgHomEquiv hb).symm f (b i) = (f i).val := by
  rw [groupLikeCoalgHomEquiv_symm_apply]
  simp only [CoalgHom.comp_apply, CoalgEquiv.toCoalgHom_eq_ofClass, CoalgEquiv.coe_coalgHomOfClass,
    groupLikeCoalgebraEquiv_symm_basis, MonoidAlgebra.liftGroupLikeCoalgHom_single,
    one_smul]

/-- Coalgebra maps agreeing on a basis are equal. -/
theorem coalgHom_ext {F H : C →ₗc[R] D} (h : ∀ i, F (b i) = H (b i)) : F = H := by
  apply CoalgHom.linearMapOfClass_injective
  exact b.ext h

variable {E : Type uE} [AddCommMonoid E] [Module R E] [Coalgebra R E]

/-- Evaluation on the basis commutes with postcomposition of coalgebra maps. -/
theorem groupLikeCoalgHomEquiv_comp (h : D →ₗc[R] E) (F : C →ₗc[R] D) (i : I) :
    b.groupLikeCoalgHomEquiv hb (h.comp F) i =
      GroupLike.map h (b.groupLikeCoalgHomEquiv hb F i) := by
  simp only [groupLikeCoalgHomEquiv_apply, GroupLike.map_comp]

/-- Extending a mapped family is postcomposition of its extension. -/
theorem groupLikeCoalgHomEquiv_symm_map (h : D →ₗc[R] E) (f : I → GroupLike R D) :
    (b.groupLikeCoalgHomEquiv hb).symm (fun i => GroupLike.map h (f i)) =
      h.comp ((b.groupLikeCoalgHomEquiv hb).symm f) := by
  apply b.coalgHom_ext
  intro i
  simp only [groupLikeCoalgHomEquiv_symm_apply_basis, CoalgHom.comp_apply,
    GroupLike.map_val]

end Module.Basis

end GroupLikeBasis

section Field

variable {K : Type uK} {C : Type uC}
variable [Field K] [AddCommGroup C] [Module K C] [Coalgebra K C]

namespace GroupLike

/-- The canonical basis of the span of all group-like elements over a field. -/
noncomputable def spanBasis :
    Module.Basis (GroupLike K C) K
      (Subcoalgebra.groupLikeSetSpan (R := K) (C := C) Set.univ).toSubmodule :=
  Module.Basis.ofRepr ((LinearEquiv.ofEq _ _ (by
    rw [Subcoalgebra.groupLikeSetSpan_toSubmodule, Set.image_univ])).trans
      (linearIndep_groupLikeVal (R := K) (A := C)).linearCombinationEquiv.symm)

/-- The canonical span basis consists of the ambient group-like elements. -/
theorem spanBasis_apply (g : GroupLike K C) :
    spanBasis (K := K) (C := C) g =
      (⟨g.val, Subcoalgebra.groupLike_mem_groupLikeSetSpan (Set.mem_univ g)⟩ :
        (Subcoalgebra.groupLikeSetSpan (R := K) (C := C) Set.univ).toSubmodule) := by
  apply Subtype.val_injective
  change ((linearIndep_groupLikeVal (R := K) (A := C)).linearCombinationEquiv
    (Finsupp.single g 1) : C) = g.val
  rw [LinearIndependent.linearCombinationEquiv_apply_coe,
    Finsupp.linearCombination_single, one_smul]

/-- The span basis is group-like for the restricted field coalgebra structure. -/
theorem isGroupLikeElem_spanBasis (g : GroupLike K C) :
    IsGroupLikeElem K (spanBasis (K := K) (C := C) g) := by
  constructor
  · simpa only [Subcoalgebra.counit_apply, spanBasis_apply] using
      g.isGroupLikeElem_val.counit_eq_one
  · apply Module.Flat.tensorProduct_mapIncl_injective_of_right
      (Subcoalgebra.groupLikeSetSpan (R := K) (C := C) Set.univ).toSubmodule
      (Subcoalgebra.groupLikeSetSpan (R := K) (C := C) Set.univ).toSubmodule
    rw [TensorProduct.mapIncl, Subcoalgebra.comul_apply,
      Subcoalgebra.map_subtype_comulLinearMap, TensorProduct.map_tmul]
    simpa only [spanBasis_apply, Submodule.subtype_apply] using
      g.isGroupLikeElem_val.comul_eq_tmul_self

/-- Canonical evaluation is a coalgebra equivalence from the free diagonal coalgebra
onto the group-like span, with its existing restricted coalgebra structure. -/
noncomputable def spanCoalgebraEquiv :
    K[GroupLike K C] ≃ₗc[K] (Subcoalgebra.groupLikeSetSpan (R := K) (C := C)
      Set.univ).toSubmodule :=
  (spanBasis (K := K) (C := C)).groupLikeCoalgebraEquiv
    (isGroupLikeElem_spanBasis (K := K) (C := C))

/-- The field-span equivalence is the given-basis equivalence on its canonical basis. -/
theorem spanCoalgebraEquiv_eq_groupLikeCoalgebraEquiv :
    spanCoalgebraEquiv (K := K) (C := C) =
      (spanBasis (K := K) (C := C)).groupLikeCoalgebraEquiv
        (isGroupLikeElem_spanBasis (K := K) (C := C)) := by
  rfl

/-- Inclusion after the equivalence is coalgebra evaluation on the identity family. -/
@[simp]
theorem subtype_comp_spanCoalgebraEquiv :
    (Subcoalgebra.groupLikeSetSpan (R := K) (C := C) Set.univ).subtype.comp
        (spanCoalgebraEquiv (K := K) (C := C) :
          K[GroupLike K C] →ₗc[K] (Subcoalgebra.groupLikeSetSpan (R := K) (C := C)
            Set.univ).toSubmodule) =
      MonoidAlgebra.liftGroupLikeCoalgHom
        (id : GroupLike K C → GroupLike K C) := by
  rw [spanCoalgebraEquiv_eq_groupLikeCoalgebraEquiv]
  apply MonoidAlgebra.coalgHom_ext
  intro g
  simp only [CoalgHom.comp_apply, CoalgEquiv.coe_coalgHomOfClass,
    Module.Basis.groupLikeCoalgebraEquiv_single, one_smul, spanBasis_apply,
    Subcoalgebra.subtype_apply, MonoidAlgebra.liftGroupLikeCoalgHom_single, id_eq]

/-- The ambient value of the equivalence is evaluation of the same coefficients. -/
theorem spanCoalgebraEquiv_apply_coe (x : K[GroupLike K C]) :
    (spanCoalgebraEquiv x : C) = MonoidAlgebra.liftGroupLikeCoalgHom
      (id : GroupLike K C → GroupLike K C) x := by
  exact CoalgHom.congr_fun (subtype_comp_spanCoalgebraEquiv (K := K) (C := C)) x

/-- The underlying linear equivalence is the canonical stock linear-combination equivalence. -/
theorem spanCoalgebraEquiv_toLinearEquiv :
    (spanCoalgebraEquiv (K := K) (C := C)).toLinearEquiv =
      (MonoidAlgebra.coeffLinearEquiv K).trans
        (spanBasis (K := K) (C := C)).repr.symm := by
  exact (spanBasis (K := K) (C := C)).groupLikeCoalgebraEquiv_toLinearEquiv
    (isGroupLikeElem_spanBasis (K := K) (C := C))

/-- The equivalence sends a monomial to the corresponding multiple of its group-like element. -/
theorem spanCoalgebraEquiv_single (g : GroupLike K C) (r : K) :
    spanCoalgebraEquiv (MonoidAlgebra.single g r) =
      r • (⟨g.val, Subcoalgebra.groupLike_mem_groupLikeSetSpan (Set.mem_univ g)⟩ :
        (Subcoalgebra.groupLikeSetSpan (R := K) (C := C) Set.univ).toSubmodule) := by
  apply Subtype.val_injective
  simp only [spanCoalgebraEquiv_apply_coe, MonoidAlgebra.liftGroupLikeCoalgHom_single,
    id_eq, Submodule.coe_smul]

/-- Inverse coefficients are exactly the stock coordinates of the independent group-like family. -/
theorem spanCoalgebraEquiv_symm_coeff (x : (Subcoalgebra.groupLikeSetSpan (R := K) (C := C)
  Set.univ).toSubmodule) :
    ((spanCoalgebraEquiv (K := K) (C := C)).symm x).coeff =
      (spanBasis (K := K) (C := C)).repr x := by
  have h := congrArg
    (fun e : K[GroupLike K C] ≃ₗ[K] (Subcoalgebra.groupLikeSetSpan (R := K) (C := C)
      Set.univ).toSubmodule => e.symm x)
    (spanCoalgebraEquiv_toLinearEquiv (K := K) (C := C))
  exact congrArg (fun y : K[GroupLike K C] => y.coeff) h

/-- A group-like generator has singleton inverse coordinates. -/
theorem spanCoalgebraEquiv_symm_groupLike (g : GroupLike K C) :
    (spanCoalgebraEquiv (K := K) (C := C)).symm
        ⟨g.val, Subcoalgebra.groupLike_mem_groupLikeSetSpan (Set.mem_univ g)⟩ =
      MonoidAlgebra.single g 1 := by
  apply EquivLike.injective (spanCoalgebraEquiv (K := K) (C := C))
  simp only [CoalgEquiv.apply_symm_apply, spanCoalgebraEquiv_single, one_smul]

/-- Ambient comultiplication is diagonal in the inverse coalgebra coordinates. -/
theorem comul_eq_sum_spanCoefficients (x : (Subcoalgebra.groupLikeSetSpan (R := K) (C := C)
  Set.univ).toSubmodule) :
    Coalgebra.comul (R := K) (x : C) =
      ((spanCoalgebraEquiv (K := K) (C := C)).symm x).coeff.sum
        (fun g r => r • (g.val ⊗ₜ[K] g.val)) := by
  let f := MonoidAlgebra.liftGroupLikeCoalgHom
    (id : GroupLike K C → GroupLike K C)
  let y := (spanCoalgebraEquiv (K := K) (C := C)).symm x
  calc
    Coalgebra.comul (R := K) (x : C) = Coalgebra.comul (R := K) (f y) := by
      rw [← spanCoalgebraEquiv_apply_coe, CoalgEquiv.apply_symm_apply]
    _ = TensorProduct.map f.toLinearMap f.toLinearMap
        (Coalgebra.comul (R := K) y) :=
      (CoalgHomClass.map_comp_comul_apply f y).symm
    _ = _ := by
      rw [MonoidAlgebra.comul_eq_sum_coeff, map_finsuppSum]
      simp only [map_smul, TensorProduct.map_tmul, f, y, CoalgHom.toLinearMap_eq_ofClass,
        CoalgHom.coe_linearMapOfClass, MonoidAlgebra.liftGroupLikeCoalgHom_single, id_eq, one_smul]

/-- The ambient counit is the sum of the inverse coalgebra coordinates. -/
theorem counit_eq_sum_spanCoefficients (x : (Subcoalgebra.groupLikeSetSpan (R := K) (C := C)
  Set.univ).toSubmodule) :
    Coalgebra.counit (R := K) (x : C) =
      ((spanCoalgebraEquiv (K := K) (C := C)).symm x).coeff.sum (fun _ r => r) := by
  let f := MonoidAlgebra.liftGroupLikeCoalgHom
    (id : GroupLike K C → GroupLike K C)
  let y := (spanCoalgebraEquiv (K := K) (C := C)).symm x
  calc
    Coalgebra.counit (R := K) (x : C) = Coalgebra.counit (R := K) (f y) := by
      rw [← spanCoalgebraEquiv_apply_coe, CoalgEquiv.apply_symm_apply]
    _ = Coalgebra.counit (R := K) y := CoalgHomClass.counit_comp_apply f y
    _ = _ := MonoidAlgebra.counit_eq_sum_coeff y

end GroupLike

end Field
