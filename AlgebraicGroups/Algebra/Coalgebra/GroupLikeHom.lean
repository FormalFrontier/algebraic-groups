/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Coalgebra.GroupLike
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Group-like elements and coalgebra morphisms

For a coalgebra `C` over a commutative semiring `R`, a group-like element determines
an `R`-coalgebra morphism from the canonical scalar coalgebra `R` to `C`.
The morphism sends `r` to `r • g`; its group-like element is recovered by evaluation
at `1`. No multiplication on `C` is required.

The scalar coalgebra has counit `r ↦ r` and comultiplication `r ↦ 1 ⊗ₜ[R] r`.
The normalization `ε g = 1` is essential: the tensor-square equation alone would
not ensure preservation of counit.

Coalgebra morphisms transport group-like elements by their underlying functions.
This transport respects identity and composition, and the scalar-source
correspondence is natural with respect to coalgebra morphisms.

## References

This construction uses Mathlib's `CommSemiring.toCoalgebra` for the scalar coalgebra,
`LinearMap.toSpanSingleton` for scalar multiplication as a linear map,
`IsGroupLikeElem.map` for preservation of group-like elements, and `LinearMap.ext_ring`,
`CoalgHom.ext_of_ring`, and `GroupLike.ext` for extensionality. These providers are in
`Mathlib.RingTheory.Coalgebra.Basic`, `.Hom`, `.GroupLike`,
`Mathlib.LinearAlgebra.Span.Basic`, and `Mathlib.Algebra.Module.LinearMap.Defs`.
The bundled transport uses the group-like carrier and preservation theorem of
Yaël Dillies and Michał Mrugała in `Mathlib.RingTheory.Coalgebra.GroupLike`.
-/

@[expose] public section

universe u v w x

namespace GroupLike

variable {R : Type u} {C : Type v}
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable {D : Type w} {E : Type x}
variable [AddCommMonoid D] [Module R D] [Coalgebra R D]
variable [AddCommMonoid E] [Module R E] [Coalgebra R E]

/-- The image of a group-like element under a coalgebra morphism. -/
def map (f : C →ₗc[R] D) (g : GroupLike R C) : GroupLike R D :=
  ⟨f g.val, IsGroupLikeElem.map f g.isGroupLikeElem_val⟩

/-- The underlying value of a transported group-like element is its image. -/
@[simp]
theorem map_val (f : C →ₗc[R] D) (g : GroupLike R C) :
    (map f g).val = f g.val := rfl

/-- Transport by the identity coalgebra morphism fixes every group-like element. -/
@[simp]
theorem map_id (g : GroupLike R C) : map (CoalgHom.id R C) g = g := by
  apply GroupLike.ext
  rfl

/-- Transport by a composite coalgebra morphism agrees with successive transport. -/
@[simp]
theorem map_comp (f : C →ₗc[R] D) (h : D →ₗc[R] E) (g : GroupLike R C) :
    map (h.comp f) g = map h (map f g) := by
  apply GroupLike.ext
  rfl

/-- Group-like elements of an `R`-coalgebra correspond to coalgebra morphisms from
its canonical scalar coalgebra, by scalar multiplication and evaluation at `1`. -/
noncomputable def coalgHomEquiv : GroupLike R C ≃ (R →ₗc[R] C) where
  toFun g :=
    { LinearMap.toSpanSingleton R C g.val with
      counit_comp := by
        apply LinearMap.ext_ring
        simpa only [LinearMap.comp_apply, LinearMap.toSpanSingleton_apply, one_smul,
          CommSemiring.counit_apply] using g.isGroupLikeElem_val.counit_eq_one
      map_comp_comul := by
        apply LinearMap.ext_ring
        simpa only [LinearMap.comp_apply, CommSemiring.comul_apply, TensorProduct.map_tmul,
          LinearMap.toSpanSingleton_apply, one_smul]
          using g.isGroupLikeElem_val.comul_eq_tmul_self.symm }
  invFun f := ⟨f 1, IsGroupLikeElem.map f (isGroupLikeElem_self.mpr rfl)⟩
  left_inv g := by
    apply GroupLike.ext
    exact one_smul R g.val
  right_inv f := by
    apply CoalgHom.ext_of_ring
    exact one_smul R (f 1)

/-- The coalgebra morphism corresponding to `g` sends `r` to `r • g.val`. -/
@[simp]
theorem coalgHomEquiv_apply (g : GroupLike R C) (r : R) :
    coalgHomEquiv g r = r • g.val := rfl

/-- The group-like element corresponding to a scalar-source coalgebra morphism
has underlying value equal to its image of `1`. -/
@[simp]
theorem coalgHomEquiv_symm_val (f : R →ₗc[R] C) :
    ((coalgHomEquiv (R := R) (C := C)).symm f).val = f 1 := rfl

/-- The scalar-source coalgebra morphism of a transported group-like element is
obtained by postcomposition. -/
@[simp]
theorem coalgHomEquiv_map (f : C →ₗc[R] D) (g : GroupLike R C) :
    coalgHomEquiv (map f g) = f.comp (coalgHomEquiv g) := by
  apply CoalgHom.ext_of_ring
  simp

end GroupLike
