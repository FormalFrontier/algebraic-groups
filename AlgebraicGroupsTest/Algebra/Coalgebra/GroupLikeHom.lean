/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.GroupLikeHom
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.Ring.PUnit
public import Mathlib.Data.ULift

/-!
# Scalar-source coalgebra morphisms on concrete coalgebras

These examples use `GroupLike.coalgHomEquiv` on diagonal Finsupp coalgebras,
the product coalgebra over `ℕ`, the zero coalgebra, and a scalar semiring with
zero divisors. Lifted labels allow the diagonal target to lie in a higher
universe than its scalars.

The product coalgebra over `ℕ` is distinct from the scalar-self coalgebra over
`ℕ × ℕ`: its coordinate points give nonunital maps into the product algebra,
whereas the scalar-self coalgebra has only the normalized point `1`.

## References

The constructions use Mathlib's scalar, Finsupp, and product coalgebras and
coordinate-inclusion identities in `Mathlib.RingTheory.Coalgebra.Basic`, its
bundled morphisms in `Mathlib.RingTheory.Coalgebra.Hom`, and its normalized
group-like predicate in `Mathlib.RingTheory.Coalgebra.GroupLike`. The algebra
comparison and trivial scalar semiring use `Mathlib.Algebra.Algebra.Prod` and
`Mathlib.Algebra.Ring.PUnit`; lifted labels use `Mathlib.Data.ULift`.
-/

@[expose] public section

open Coalgebra

universe u v

noncomputable section

private def coordinateNatPoint {ι : Type v} (i : ι) : GroupLike ℕ (ι →₀ ℕ) where
  val := Finsupp.single i 1
  isGroupLikeElem_val := {
    counit_eq_one := by simp
    comul_eq_tmul_self := by simp }

private theorem coordinateNatPoint_image {ι : Type v} (i : ι) (n : ℕ) :
    GroupLike.coalgHomEquiv (coordinateNatPoint i) n = Finsupp.single i n := by
  rw [GroupLike.coalgHomEquiv_apply]
  exact Finsupp.smul_single_one i n

private theorem coordinateNatPoint_ne {ι : Type v} {i j : ι} (hij : i ≠ j) :
    coordinateNatPoint i ≠ coordinateNatPoint j := by
  classical
  intro h
  have hc := congrArg (fun g : GroupLike ℕ (ι →₀ ℕ) => g.val i) h
  simp [coordinateNatPoint, hij] at hc

private theorem coordinateNatPoint_images_ne {ι : Type v} {i j : ι} (hij : i ≠ j) :
    GroupLike.coalgHomEquiv (coordinateNatPoint i) ≠
      GroupLike.coalgHomEquiv (coordinateNatPoint j) := by
  intro h
  exact coordinateNatPoint_ne hij
    ((GroupLike.coalgHomEquiv (R := ℕ) (C := ι →₀ ℕ)).injective h)

-- Bundle the coordinate inclusion independently of the equivalence.
private def coordinateNatHom {ι : Type v} (i : ι) : ℕ →ₗc[ℕ] (ι →₀ ℕ) where
  toLinearMap := Finsupp.lsingle i
  counit_comp := Finsupp.counit_comp_lsingle (R := ℕ) (ι := ι) (A := ℕ) i
  map_comp_comul := (Finsupp.comul_comp_lsingle (R := ℕ) (ι := ι) (A := ℕ) i).symm

private theorem coordinateNatHom_apply {ι : Type v} (i : ι) (n : ℕ) :
    coordinateNatHom i n = Finsupp.single i n := rfl

private theorem coordinateNatHom_inverse {ι : Type v} (i : ι) :
    (GroupLike.coalgHomEquiv (R := ℕ) (C := ι →₀ ℕ)).symm (coordinateNatHom i) =
      coordinateNatPoint i := by
  apply GroupLike.val_injective
  rw [GroupLike.coalgHomEquiv_symm_val]
  rfl

/-- The two coordinate points of the diagonal coalgebra on `Fin 2 →₀ ℕ` give
distinct scalar-source morphisms. Their values are coordinate vectors, and
evaluation at `2` has coefficient `2`, not `1`. -/
theorem Finsupp.exists_distinct_coalgHomEquiv_nat_fin_two :
    ∃ g₀ g₁ : GroupLike ℕ (Fin 2 →₀ ℕ),
      g₀.val = Finsupp.single 0 1 ∧
      g₁.val = Finsupp.single 1 1 ∧
      (∀ n, GroupLike.coalgHomEquiv g₀ n = Finsupp.single 0 n) ∧
      (∀ n, GroupLike.coalgHomEquiv g₁ n = Finsupp.single 1 n) ∧
      (GroupLike.coalgHomEquiv g₀ 2) 0 = 2 ∧
      (GroupLike.coalgHomEquiv g₀ 2) 1 = 0 ∧
      GroupLike.coalgHomEquiv g₀ ≠ GroupLike.coalgHomEquiv g₁ := by
  refine ⟨coordinateNatPoint 0, coordinateNatPoint 1, rfl, rfl,
    coordinateNatPoint_image 0, coordinateNatPoint_image 1, ?_, ?_, ?_⟩
  · rw [coordinateNatPoint_image]
    simp
  · rw [coordinateNatPoint_image]
    simp
  · exact coordinateNatPoint_images_ne (by simp)

/-- The inverse equivalence recovers the coordinate point from an independently
bundled coordinate inclusion. Its forward image at `1` is group-like, while
its forward image at `2` is not normalized by the counit. -/
theorem Finsupp.exists_coalgHomEquiv_inverse_single_nat_fin_two (i : Fin 2) :
    ∃ f : ℕ →ₗc[ℕ] (Fin 2 →₀ ℕ),
      (∀ n, f n = Finsupp.single i n) ∧
      ((GroupLike.coalgHomEquiv (R := ℕ) (C := Fin 2 →₀ ℕ)).symm f).val =
        Finsupp.single i 1 ∧
      IsGroupLikeElem ℕ
        (GroupLike.coalgHomEquiv
          ((GroupLike.coalgHomEquiv (R := ℕ) (C := Fin 2 →₀ ℕ)).symm f) 1) ∧
      ¬ IsGroupLikeElem ℕ
        (GroupLike.coalgHomEquiv
          ((GroupLike.coalgHomEquiv (R := ℕ) (C := Fin 2 →₀ ℕ)).symm f) 2) := by
  refine ⟨coordinateNatHom i, coordinateNatHom_apply i, ?_, ?_, ?_⟩
  · rw [GroupLike.coalgHomEquiv_symm_val]
    rfl
  · rw [coordinateNatHom_inverse, coordinateNatPoint_image]
    exact (coordinateNatPoint i).isGroupLikeElem_val
  · intro h
    have hc := h.counit_eq_one
    rw [coordinateNatHom_inverse, coordinateNatPoint_image] at hc
    simp at hc

/-- The diagonal coordinate examples also work when their labels are lifted
into an independently chosen universe. Both the forward morphisms and the
inverse of the coordinate inclusion use the lifted target. -/
theorem Finsupp.exists_distinct_coalgHomEquiv_nat_ulift_fin_two :
    ∃ g₀ g₁ : GroupLike ℕ (ULift.{v} (Fin 2) →₀ ℕ),
      (∀ n, GroupLike.coalgHomEquiv g₀ n =
        Finsupp.single (ULift.up (0 : Fin 2)) n) ∧
      (∀ n, GroupLike.coalgHomEquiv g₁ n =
        Finsupp.single (ULift.up (1 : Fin 2)) n) ∧
      GroupLike.coalgHomEquiv g₀ ≠ GroupLike.coalgHomEquiv g₁ ∧
      ∃ f : ℕ →ₗc[ℕ] (ULift.{v} (Fin 2) →₀ ℕ),
        (∀ n, f n = Finsupp.single (ULift.up (0 : Fin 2)) n) ∧
        ((GroupLike.coalgHomEquiv (R := ℕ)
          (C := ULift.{v} (Fin 2) →₀ ℕ)).symm f).val =
            Finsupp.single (ULift.up (0 : Fin 2)) 1 := by
  refine ⟨coordinateNatPoint (ULift.up (0 : Fin 2)),
    coordinateNatPoint (ULift.up (1 : Fin 2)),
    coordinateNatPoint_image _, coordinateNatPoint_image _, ?_,
    coordinateNatHom (ULift.up (0 : Fin 2)), coordinateNatHom_apply _, ?_⟩
  · exact coordinateNatPoint_images_ne (by simp)
  · rw [GroupLike.coalgHomEquiv_symm_val]
    rfl

private def natLeftHom : ℕ →ₗc[ℕ] (ℕ × ℕ) where
  toLinearMap := LinearMap.inl ℕ ℕ ℕ
  counit_comp := Prod.counit_comp_inl (R := ℕ) (A := ℕ) (B := ℕ)
  map_comp_comul := (Prod.comul_comp_inl (R := ℕ) (A := ℕ) (B := ℕ)).symm

private def natRightHom : ℕ →ₗc[ℕ] (ℕ × ℕ) where
  toLinearMap := LinearMap.inr ℕ ℕ ℕ
  counit_comp := Prod.counit_comp_inr (R := ℕ) (A := ℕ) (B := ℕ)
  map_comp_comul := (Prod.comul_comp_inr (R := ℕ) (A := ℕ) (B := ℕ)).symm

private def natLeftPoint : GroupLike ℕ (ℕ × ℕ) where
  val := (1, 0)
  isGroupLikeElem_val :=
    (show IsGroupLikeElem ℕ (1 : ℕ) from by simp).map natLeftHom

private def natRightPoint : GroupLike ℕ (ℕ × ℕ) where
  val := (0, 1)
  isGroupLikeElem_val :=
    (show IsGroupLikeElem ℕ (1 : ℕ) from by simp).map natRightHom

private theorem natLeftPoint_image (n : ℕ) :
    GroupLike.coalgHomEquiv natLeftPoint n = (n, 0) := by
  rw [GroupLike.coalgHomEquiv_apply]
  simp [natLeftPoint, smul_eq_mul]

private theorem natRightPoint_image (n : ℕ) :
    GroupLike.coalgHomEquiv natRightPoint n = (0, n) := by
  rw [GroupLike.coalgHomEquiv_apply]
  simp [natRightPoint, smul_eq_mul]

private theorem natLeftPoint_not_unital :
    GroupLike.coalgHomEquiv natLeftPoint 1 ≠ (1 : ℕ × ℕ) := by
  intro h
  rw [natLeftPoint_image] at h
  have hc := congrArg Prod.snd h
  simp at hc

private theorem natRightPoint_not_unital :
    GroupLike.coalgHomEquiv natRightPoint 1 ≠ (1 : ℕ × ℕ) := by
  intro h
  rw [natRightPoint_image] at h
  have hc := congrArg Prod.fst h
  simp at hc

private theorem natLeftPoint_not_algebraHom :
    ¬ ∃ ψ : ℕ →ₐ[ℕ] (ℕ × ℕ), ∀ n, ψ n = GroupLike.coalgHomEquiv natLeftPoint n := by
  rintro ⟨ψ, hψ⟩
  apply natLeftPoint_not_unital
  rw [← hψ 1, map_one]

private theorem natRightPoint_not_algebraHom :
    ¬ ∃ ψ : ℕ →ₐ[ℕ] (ℕ × ℕ), ∀ n, ψ n = GroupLike.coalgHomEquiv natRightPoint n := by
  rintro ⟨ψ, hψ⟩
  apply natRightPoint_not_unital
  rw [← hψ 1, map_one]

/-- For the product coalgebra over `ℕ`, the points `(1, 0)` and `(0, 1)` give
the two coordinate inclusions under the equivalence. Neither morphism is
unital for the product algebra, so neither is an algebra homomorphism. -/
theorem Prod.exists_coalgHomEquiv_nat_coordinate_inclusions :
    ∃ g₀ g₁ : GroupLike ℕ (ℕ × ℕ),
      g₀.val = (1, 0) ∧ g₁.val = (0, 1) ∧
      (∀ n, GroupLike.coalgHomEquiv g₀ n = (n, 0)) ∧
      (∀ n, GroupLike.coalgHomEquiv g₁ n = (0, n)) ∧
      GroupLike.coalgHomEquiv g₀ 1 ≠ (1 : ℕ × ℕ) ∧
      GroupLike.coalgHomEquiv g₁ 1 ≠ (1 : ℕ × ℕ) ∧
      (¬ ∃ ψ : ℕ →ₐ[ℕ] (ℕ × ℕ), ∀ n, ψ n = GroupLike.coalgHomEquiv g₀ n) ∧
      (¬ ∃ ψ : ℕ →ₐ[ℕ] (ℕ × ℕ), ∀ n, ψ n = GroupLike.coalgHomEquiv g₁ n) := by
  exact ⟨natLeftPoint, natRightPoint, rfl, rfl, natLeftPoint_image,
    natRightPoint_image, natLeftPoint_not_unital, natRightPoint_not_unital,
    natLeftPoint_not_algebraHom, natRightPoint_not_algebraHom⟩

/-- The zero Finsupp coalgebra over nontrivial scalars has no group-like point.
The inverse equivalence therefore rules out scalar-source coalgebra morphisms. -/
theorem Finsupp.not_nonempty_groupLike_and_coalgHom_empty
    (R : Type u) [CommSemiring R] [Nontrivial R] :
    ¬ Nonempty (GroupLike R (Empty →₀ R)) ∧ ¬ Nonempty (R →ₗc[R] (Empty →₀ R)) := by
  have hpoint : ¬ Nonempty (GroupLike R (Empty →₀ R)) := by
    rintro ⟨g⟩
    exact g.isGroupLikeElem_val.ne_zero (Subsingleton.elim _ _)
  refine ⟨hpoint, ?_⟩
  rintro ⟨f⟩
  exact hpoint ⟨(GroupLike.coalgHomEquiv (R := R) (C := Empty →₀ R)).symm f⟩

private def punitZeroPoint : GroupLike PUnit (Empty →₀ PUnit) where
  val := 0
  isGroupLikeElem_val := {
    counit_eq_one := Subsingleton.elim _ _
    comul_eq_tmul_self := by simp }

/-- Over the trivial scalar semiring `PUnit`, the zero coalgebra instead has
a group-like point. Its corresponding morphism is zero and returns to the
same point under the inverse equivalence. -/
theorem Finsupp.exists_coalgHomEquiv_zero_punit :
    ∃ g : GroupLike PUnit (Empty →₀ PUnit),
      g.val = 0 ∧
      (∀ r, GroupLike.coalgHomEquiv g r = 0) ∧
      ((GroupLike.coalgHomEquiv (R := PUnit) (C := Empty →₀ PUnit)).symm
        (GroupLike.coalgHomEquiv g)).val = 0 ∧
      (GroupLike.coalgHomEquiv (R := PUnit) (C := Empty →₀ PUnit)).symm
        (GroupLike.coalgHomEquiv g) = g := by
  refine ⟨punitZeroPoint, rfl, ?_, ?_, ?_⟩
  · intro r
    rw [GroupLike.coalgHomEquiv_apply]
    simp [punitZeroPoint]
  · rw [GroupLike.coalgHomEquiv_symm_val, GroupLike.coalgHomEquiv_apply]
    simp [punitZeroPoint]
  · exact (GroupLike.coalgHomEquiv (R := PUnit)
      (C := Empty →₀ PUnit)).symm_apply_apply punitZeroPoint

private def productScalarPoint : GroupLike (ℕ × ℕ) (ℕ × ℕ) where
  val := 1
  isGroupLikeElem_val := by simp

/-- The semiring `ℕ × ℕ` has zero divisors, but the equivalence for its
scalar-self coalgebra still sends the normalized point `1` to the identity.
Its inverse evaluates that identity at `1`, and every group-like point in
this scalar-self coalgebra has value `1`. -/
theorem GroupLike.exists_coalgHomEquiv_id_product_nat :
    (∃ a b : ℕ × ℕ, a ≠ 0 ∧ b ≠ 0 ∧ a * b = 0) ∧
      (∃ g : GroupLike (ℕ × ℕ) (ℕ × ℕ),
        g.val = 1 ∧
        GroupLike.coalgHomEquiv g = CoalgHom.id (ℕ × ℕ) (ℕ × ℕ) ∧
        (∀ r, GroupLike.coalgHomEquiv g r = r) ∧
        ((GroupLike.coalgHomEquiv (R := ℕ × ℕ) (C := ℕ × ℕ)).symm
          (CoalgHom.id (ℕ × ℕ) (ℕ × ℕ))).val = 1) ∧
      (∀ g : GroupLike (ℕ × ℕ) (ℕ × ℕ), g.val = 1) := by
  refine ⟨⟨(1, 0), (0, 1), by simp, by simp, by simp⟩,
    ⟨productScalarPoint, rfl, ?_, ?_, ?_⟩, ?_⟩
  · apply CoalgHom.ext_of_ring
    rw [GroupLike.coalgHomEquiv_apply]
    simp [productScalarPoint]
  · intro r
    rw [GroupLike.coalgHomEquiv_apply]
    simp [productScalarPoint, smul_eq_mul]
  · rw [GroupLike.coalgHomEquiv_symm_val]
    rfl
  · intro g
    exact isGroupLikeElem_self.mp g.isGroupLikeElem_val
