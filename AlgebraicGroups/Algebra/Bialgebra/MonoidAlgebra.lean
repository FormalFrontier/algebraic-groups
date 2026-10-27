/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Bialgebra.GroupLike
public import AlgebraicGroups.Algebra.Coalgebra.MonoidAlgebra
public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra

/-!
# Bialgebra maps from monoid algebras

A bialgebra map from `R[M]` determines a monoid homomorphism from `M` to the
group-like elements of its target. Conversely, a group-like-valued monoid map
extends by Mathlib's group-like evaluation after the induced map on monoid algebras.
These maps form an equivalence over an arbitrary commutative semiring, with
algebra and coalgebra agreement, evaluation, uniqueness and naturality laws.
The target semiring need not be commutative or a Hopf algebra.

## References

The algebra universal property is Mathlib's `MonoidAlgebra.lift`. The monoid-algebra
bialgebra, normalized group-like generators and evaluation map are due to
Amelia Livingston, Yaël Dillies and Michał Mrugała in
`Mathlib.RingTheory.Bialgebra.MonoidAlgebra`. The group-like carrier and monoid
structure are provided by Mathlib's coalgebra and bialgebra group-like modules.
The coalgebra extension and transport are those of
`AlgebraicGroups.Algebra.Coalgebra.MonoidAlgebra` and
`AlgebraicGroups.Algebra.Bialgebra.GroupLike`.
-/

@[expose] public section

universe uR uM uN uH uA uB

namespace MonoidAlgebra

variable {R : Type uR} {M : Type uM} {N : Type uN} {H : Type uH}
variable {A : Type uA} {B : Type uB}

section Bialgebra

variable [CommSemiring R] [Monoid M] [Semiring A] [Bialgebra R A]

/-- Extract the group-like-valued monoid homomorphism of a bialgebra map from a
monoid algebra, using the inverse of the algebra universal property. -/
noncomputable def groupLikeHomOfBialgHom (F : R[M] →ₐc[R] A) : M →* GroupLike R A where
  toFun m :=
    { val := (lift R A M).symm F.toAlgHom m
      isGroupLikeElem_val := by
        rw [lift_symm_apply]
        exact (isGroupLikeElem_single_one (R := R) (A := R) m).map F.toCoalgHom }
  map_one' := by
    apply GroupLike.val_injective
    exact ((lift R A M).symm F.toAlgHom).map_one
  map_mul' m n := by
    apply GroupLike.val_injective
    exact ((lift R A M).symm F.toAlgHom).map_mul m n

/-- Extraction evaluates a bialgebra map on the normalized monoid generators. -/
@[simp]
theorem groupLikeHomOfBialgHom_apply_val (F : R[M] →ₐc[R] A) (m : M) :
    ((groupLikeHomOfBialgHom F) m).val = F (single m 1) := by
  exact lift_symm_apply F.toAlgHom m

/-- Forgetting group-likeness in the extracted map gives the inverse algebra
universal property exactly. -/
theorem valMonoidHom_comp_groupLikeHomOfBialgHom (F : R[M] →ₐc[R] A) :
    (GroupLike.valMonoidHom R A).comp (groupLikeHomOfBialgHom F) =
      (lift R A M).symm F.toAlgHom := by
  rfl

/-- Extraction is a left inverse of group-like evaluation after the induced map
on monoid algebras. -/
theorem groupLikeHomOfBialgHom_leftInverse :
    Function.LeftInverse (groupLikeHomOfBialgHom (R := R) (M := M) (A := A))
      (fun f : M →* GroupLike R A =>
        (liftGroupLikeBialgHom (R := R) (A := A)).comp (mapDomainBialgHom R f)) := by
  intro f
  apply MonoidHom.ext
  intro m
  apply GroupLike.val_injective
  rw [groupLikeHomOfBialgHom_apply_val]
  change (liftGroupLikeBialgHom (R := R) (A := A))
    (mapDomainBialgHom R f (single m 1)) = (f m).val
  rw [mapDomainBialgHom_single]
  change (liftGroupLikeBialgHom (R := R) (A := A)).toCoalgHom
    (single (f m) 1) = (f m).val
  rw [← liftGroupLikeCoalgHom_id_eq_liftGroupLikeBialgHom]
  simp only [liftGroupLikeCoalgHom_single, id_eq, one_smul]

/-- Extraction is a right inverse of group-like evaluation after the induced map
on monoid algebras. -/
theorem groupLikeHomOfBialgHom_rightInverse :
    Function.RightInverse (groupLikeHomOfBialgHom (R := R) (M := M) (A := A))
      (fun f : M →* GroupLike R A =>
        (liftGroupLikeBialgHom (R := R) (A := A)).comp (mapDomainBialgHom R f)) := by
  intro F
  exact BialgHom.coe_coalgHom_injective <|
    show
      ((liftGroupLikeBialgHom (R := R) (A := A)).comp
        (mapDomainBialgHom R (groupLikeHomOfBialgHom F))).toCoalgHom =
        F.toCoalgHom from by
      have hforward :
          ((liftGroupLikeBialgHom (R := R) (A := A)).comp
            (mapDomainBialgHom R (groupLikeHomOfBialgHom F))).toCoalgHom =
          liftGroupLikeCoalgHom (fun m => groupLikeHomOfBialgHom F m) := by
        apply coalgHom_ext
        intro m
        change (liftGroupLikeBialgHom (R := R) (A := A)).toCoalgHom
          (mapDomainBialgHom R (groupLikeHomOfBialgHom F) (single m 1)) =
            liftGroupLikeCoalgHom (fun m => groupLikeHomOfBialgHom F m) (single m 1)
        rw [mapDomainBialgHom_single,
          ← liftGroupLikeCoalgHom_id_eq_liftGroupLikeBialgHom]
        simp only [liftGroupLikeCoalgHom_single, id_eq]
      have hfamily : (fun m => groupLikeHomOfBialgHom F m) =
          (liftGroupLikeCoalgHomEquiv (R := R) (C := A) (G := M)).symm F.toCoalgHom := by
        funext m
        apply GroupLike.val_injective
        simp only [groupLikeHomOfBialgHom_apply_val,
          liftGroupLikeCoalgHomEquiv_symm_apply_val, BialgHom.toCoalgHom_apply]
      rw [hforward, hfamily]
      exact (liftGroupLikeCoalgHomEquiv (R := R) (C := A) (G := M)).apply_symm_apply
        F.toCoalgHom

/-- Monoid maps to group-like elements correspond to bialgebra maps from a monoid algebra. -/
noncomputable def liftGroupLikeBialgHomEquiv :
    (M →* GroupLike R A) ≃ (R[M] →ₐc[R] A) where
  toFun f := (liftGroupLikeBialgHom (R := R) (A := A)).comp (mapDomainBialgHom R f)
  invFun := groupLikeHomOfBialgHom
  left_inv := groupLikeHomOfBialgHom_leftInverse
  right_inv := groupLikeHomOfBialgHom_rightInverse

/-- The universal correspondence extends a monoid map by group-like evaluation. -/
@[simp]
theorem liftGroupLikeBialgHomEquiv_apply (f : M →* GroupLike R A) :
    liftGroupLikeBialgHomEquiv f =
      (liftGroupLikeBialgHom (R := R) (A := A)).comp (mapDomainBialgHom R f) := rfl

/-- The inverse universal correspondence extracts the group-like-valued monoid map. -/
@[simp]
theorem liftGroupLikeBialgHomEquiv_symm_apply (F : R[M] →ₐc[R] A) :
    liftGroupLikeBialgHomEquiv.symm F = groupLikeHomOfBialgHom F := rfl

/-- Group-like evaluation extends the underlying value map by the algebra
universal property. -/
theorem liftGroupLikeBialgHom_mapDomain_toAlgHom (f : M →* GroupLike R A) :
    ((liftGroupLikeBialgHom (R := R) (A := A)).comp
      (mapDomainBialgHom R f)).toAlgHom =
        lift R A M ((GroupLike.valMonoidHom R A).comp f) := by
  apply (lift R A M).symm.injective
  rw [Equiv.symm_apply_apply, ← valMonoidHom_comp_groupLikeHomOfBialgHom,
    groupLikeHomOfBialgHom_leftInverse]

/-- Group-like evaluation agrees with the coalgebra extension of the same family. -/
theorem liftGroupLikeBialgHom_mapDomain_toCoalgHom (f : M →* GroupLike R A) :
    ((liftGroupLikeBialgHom (R := R) (A := A)).comp
      (mapDomainBialgHom R f)).toCoalgHom = liftGroupLikeCoalgHom (fun m => f m) := by
  apply liftGroupLikeCoalgHom_unique (fun m => f m)
  intro m
  have h := congrArg (fun g : M →* GroupLike R A => (g m).val)
    (groupLikeHomOfBialgHom_leftInverse f)
  simpa only [groupLikeHomOfBialgHom_apply_val, BialgHom.toCoalgHom_apply] using h

/-- Group-like evaluation sends each monomial to the corresponding scalar multiple. -/
theorem liftGroupLikeBialgHom_mapDomain_single (f : M →* GroupLike R A) (m : M) (r : R) :
    ((liftGroupLikeBialgHom (R := R) (A := A)).comp (mapDomainBialgHom R f)) (single m r) =
      r • (f m).val := by
  change ((liftGroupLikeBialgHom (R := R) (A := A)).comp
    (mapDomainBialgHom R f)).toCoalgHom (single m r) = r • (f m).val
  rw [liftGroupLikeBialgHom_mapDomain_toCoalgHom, liftGroupLikeCoalgHom_single]

/-- A bialgebra map is the extension of a group-like-valued monoid map exactly
when their values on normalized generators agree. -/
theorem liftGroupLikeBialgHom_mapDomain_eq_iff (f : M →* GroupLike R A)
    (F : R[M] →ₐc[R] A) :
    (liftGroupLikeBialgHom (R := R) (A := A)).comp (mapDomainBialgHom R f) = F ↔
      ∀ m, F (single m 1) = (f m).val := by
  constructor
  · intro h m
    rw [← h, liftGroupLikeBialgHom_mapDomain_single, one_smul]
  · intro h
    exact BialgHom.coe_coalgHom_injective <|
      show
        ((liftGroupLikeBialgHom (R := R) (A := A)).comp
          (mapDomainBialgHom R f)).toCoalgHom = F.toCoalgHom from
        (liftGroupLikeBialgHom_mapDomain_toCoalgHom f).trans
          (liftGroupLikeCoalgHom_unique (fun m => f m) F.toCoalgHom h).symm

/-- Extending a group-like-valued monoid map commutes with precomposition on its
source monoid. -/
theorem liftGroupLikeBialgHom_mapDomain_comp [Monoid N] (f : M →* GroupLike R A)
    (α : N →* M) :
    (liftGroupLikeBialgHom (R := R) (A := A)).comp (mapDomainBialgHom R (f.comp α)) =
      ((liftGroupLikeBialgHom (R := R) (A := A)).comp (mapDomainBialgHom R f)).comp
        (mapDomainBialgHom R α) := by
  apply (liftGroupLikeBialgHom_mapDomain_eq_iff (f.comp α) _).2
  intro n
  change ((liftGroupLikeBialgHom (R := R) (A := A)).comp
    (mapDomainBialgHom R f)) (mapDomainBialgHom R α (single n 1)) = (f (α n)).val
  rw [mapDomainBialgHom_single, liftGroupLikeBialgHom_mapDomain_single, one_smul]

/-- Extending a group-like-valued monoid map commutes with transport by a
bialgebra morphism of its target. -/
theorem liftGroupLikeBialgHom_mapDomain_groupLikeMap [Semiring B] [Bialgebra R B]
    (f : M →* GroupLike R A) (h : A →ₐc[R] B) :
    (liftGroupLikeBialgHom (R := R) (A := B)).comp
        (mapDomainBialgHom R (h.groupLikeMap.comp f)) =
      h.comp ((liftGroupLikeBialgHom (R := R) (A := A)).comp (mapDomainBialgHom R f)) := by
  apply (liftGroupLikeBialgHom_mapDomain_eq_iff (h.groupLikeMap.comp f) _).2
  intro m
  change h (((liftGroupLikeBialgHom (R := R) (A := A)).comp
    (mapDomainBialgHom R f)) (single m 1)) = (h.groupLikeMap (f m)).val
  rw [liftGroupLikeBialgHom_mapDomain_single, one_smul, BialgHom.groupLikeMap_val]

end Bialgebra

/-- Extension of the normalized generators in a monoid algebra recovers the
induced bialgebra map for any monoid homomorphism. -/
theorem liftGroupLikeBialgHom_mapDomain_groupLikeHomOfBialgHom_id
    [CommSemiring R] [Monoid M] [Monoid H] (f : M →* H) :
    (liftGroupLikeBialgHom (R := R) (A := R[H])).comp
        (mapDomainBialgHom R ((groupLikeHomOfBialgHom (BialgHom.id R R[H])).comp f)) =
      mapDomainBialgHom R f := by
  apply (liftGroupLikeBialgHom_mapDomain_eq_iff
    ((groupLikeHomOfBialgHom (BialgHom.id R R[H])).comp f) _).2
  intro m
  change mapDomainBialgHom R f (single m 1) =
    (groupLikeHomOfBialgHom (BialgHom.id R R[H]) (f m)).val
  rw [mapDomainBialgHom_single, groupLikeHomOfBialgHom_apply_val, BialgHom.coe_id]
  rfl

end MonoidAlgebra
