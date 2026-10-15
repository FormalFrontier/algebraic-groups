/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra

/-!
# Coalgebra maps from the free diagonal coalgebra

For any type `G` and commutative semiring `R`, the canonical coalgebra on
`MonoidAlgebra R G` has group-like generators `single g 1`. A function from `G` to
the group-like elements of an `R`-coalgebra extends uniquely to a coalgebra map.
Neither a multiplication on `G` nor a multiplication on the target is required.
The correspondence is an equivalence of types, not a linear equivalence.

The counit and comultiplication are finite sums in the canonical coefficients.
Evaluation on the identity family of group-like elements agrees with the
coalgebra map underlying Mathlib's bialgebra evaluation when a bialgebra is given.

## References

The construction uses Mathlib's `MonoidAlgebra.coeffLinearEquiv`,
`Finsupp.linearCombination`, arbitrary-index monoid-algebra coalgebra and
`IsGroupLikeElem.map`. The compatibility theorem refers to Mathlib's
`MonoidAlgebra.liftGroupLikeBialgHom`; no multiplicative structure is used in the
coalgebra-only extension.
-/

@[expose] public section

universe uR uC uG

open scoped TensorProduct

namespace MonoidAlgebra

variable {R : Type uR} {C : Type uC} {G : Type uG}

section Ext

variable [CommSemiring R] [AddCommMonoid C] [Module R C] [CoalgebraStruct R C]

/-- Coalgebra maps from the free diagonal coalgebra are determined on `single g 1`. -/
@[ext]
theorem coalgHom_ext {F H : R[G] →ₗc[R] C}
    (h : ∀ g, F (single g 1) = H (single g 1)) : F = H := by
  apply CoalgHom.coe_linearMap_injective
  exact lhom_ext' fun g => LinearMap.ext_ring (h g)

end Ext

section Coalgebra

variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]

/-- Extend a family of group-like elements by linear combination in the canonical
coefficients of the free diagonal coalgebra. -/
noncomputable def liftGroupLikeCoalgHom (f : G → GroupLike R C) : R[G] →ₗc[R] C where
  toLinearMap := (Finsupp.linearCombination R (fun g => (f g).val)).comp
    (coeffLinearEquiv R).toLinearMap
  counit_comp := by
    apply lhom_ext'
    intro g
    apply LinearMap.ext_ring
    simp
  map_comp_comul := by
    apply lhom_ext'
    intro g
    apply LinearMap.ext_ring
    simp

/-- The linear map underlying the extension is the stock linear-combination map. -/
theorem liftGroupLikeCoalgHom_toLinearMap (f : G → GroupLike R C) :
    (liftGroupLikeCoalgHom f).toLinearMap =
      (Finsupp.linearCombination R (fun g => (f g).val)).comp
        (coeffLinearEquiv R).toLinearMap := rfl

/-- The extension sends a monomial with any coefficient to the corresponding scalar multiple. -/
@[simp]
theorem liftGroupLikeCoalgHom_single (f : G → GroupLike R C) (g : G) (r : R) :
    liftGroupLikeCoalgHom f (single g r) = r • (f g).val :=
  Finsupp.linearCombination_single R r g

/-- Any coalgebra map extending the given family is its canonical extension. -/
theorem liftGroupLikeCoalgHom_unique (f : G → GroupLike R C) (F : R[G] →ₗc[R] C)
    (h : ∀ g, F (single g 1) = (f g).val) : F = liftGroupLikeCoalgHom f := by
  exact coalgHom_ext fun g => by simpa using h g

/-- Families of group-like elements correspond to coalgebra maps from the free
diagonal coalgebra on their indexing type. -/
noncomputable def liftGroupLikeCoalgHomEquiv :
    (G → GroupLike R C) ≃ (R[G] →ₗc[R] C) where
  toFun := liftGroupLikeCoalgHom
  invFun F g := ⟨F (single g 1), IsGroupLikeElem.map F
    (isGroupLikeElem_single_one (R := R) (A := R) g)⟩
  left_inv := by
    intro f
    funext g
    apply GroupLike.val_injective
    simp only [liftGroupLikeCoalgHom_single, one_smul]
  right_inv := by
    intro F
    apply coalgHom_ext
    intro g
    simp only [liftGroupLikeCoalgHom_single, one_smul]

/-- The universal correspondence extends a family by the canonical coalgebra map. -/
@[simp]
theorem liftGroupLikeCoalgHomEquiv_apply (f : G → GroupLike R C) :
    liftGroupLikeCoalgHomEquiv f = liftGroupLikeCoalgHom f := rfl

/-- The inverse universal correspondence evaluates at the group-like generators. -/
@[simp]
theorem liftGroupLikeCoalgHomEquiv_symm_apply_val (F : R[G] →ₗc[R] C) (g : G) :
    ((liftGroupLikeCoalgHomEquiv.symm F) g).val = F (single g 1) := rfl

/-- The image of the extension is exactly the linear span of its group-like generators. -/
theorem range_liftGroupLikeCoalgHom (f : G → GroupLike R C) :
    LinearMap.range (liftGroupLikeCoalgHom f).toLinearMap =
      Submodule.span R (Set.range (fun g => (f g).val)) := by
  rw [liftGroupLikeCoalgHom_toLinearMap, LinearMap.range_comp, LinearEquiv.range,
    Submodule.map_top, Finsupp.range_linearCombination]

/-- An empty indexing type gives the zero source, without requiring a target group-like element. -/
theorem liftGroupLikeCoalgHom_apply_of_isEmpty [IsEmpty G] (f : G → GroupLike R C)
    (x : R[G]) : liftGroupLikeCoalgHom f x = 0 := by
  have hx : x = 0 := by
    ext g
    exact isEmptyElim g
  simp [hx]

end Coalgebra

section Diagonal

variable [CommSemiring R]

/-- The counit of the canonical diagonal coalgebra is the sum of its coefficients. -/
theorem counit_eq_sum_coeff (x : R[G]) :
    Coalgebra.counit (R := R) x = x.coeff.sum (fun _ r => r) := by
  simpa only [map_finsuppSum, counit_single, CommSemiring.counit_apply] using
    congrArg (Coalgebra.counit (R := R)) x.sum_coeff_single.symm

/-- Comultiplication of the canonical diagonal coalgebra is diagonal in its generators. -/
theorem comul_eq_sum_coeff (x : R[G]) :
    Coalgebra.comul (R := R) x = x.coeff.sum
      (fun g r => r • ((single g 1 : R[G]) ⊗ₜ[R] (single g 1 : R[G]))) := by
  calc
    Coalgebra.comul (R := R) x =
        Coalgebra.comul (R := R) (x.coeff.sum single : R[G]) :=
      congrArg (Coalgebra.comul (R := R)) x.sum_coeff_single.symm
    _ = x.coeff.sum (fun g r => Coalgebra.comul (R := R) (single g r : R[G])) :=
      map_finsuppSum ..
    _ = _ := by
      apply Finsupp.sum_congr
      intro g _
      rw [show (single g (x.coeff g) : R[G]) = x.coeff g • single g 1 by
          simp only [smul_single, smul_eq_mul, mul_one],
        map_smul, (isGroupLikeElem_single_one (R := R) (A := R) g).comul_eq_tmul_self]

end Diagonal

section Bialgebra

variable [CommSemiring R] [Semiring C] [Bialgebra R C]

/-- Coalgebra evaluation on all group-like elements agrees with bialgebra evaluation. -/
theorem liftGroupLikeCoalgHom_id_eq_liftGroupLikeBialgHom :
    liftGroupLikeCoalgHom (id : GroupLike R C → GroupLike R C) =
      (liftGroupLikeBialgHom (R := R) (A := C)).toCoalgHom := by
  apply coalgHom_ext
  intro g
  simp [BialgHom.toCoalgHom_apply, liftGroupLikeBialgHom]

end Bialgebra

end MonoidAlgebra
