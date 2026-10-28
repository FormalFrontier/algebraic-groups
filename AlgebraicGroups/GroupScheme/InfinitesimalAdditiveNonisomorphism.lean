/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.MonoidAlgebraPrimitive
public import AlgebraicGroups.GroupScheme.AdditivePowerQuotient
public import AlgebraicGroups.GroupScheme.InfinitesimalAdditive
public import AlgebraicGroups.GroupScheme.RootsOfUnity

@[expose] public section

/-!
# Infinitesimal additive groups are not roots-of-unity groups

Over a field of characteristic `p`, the characteristic-power quotient of the
additive group has a nonzero primitive coordinate when `m > 0`. The roots-of-unity
coordinate Hopf algebra of order `p ^ m` has no nonzero primitive elements:
it is an additive monoid algebra, and primitivity includes both zero counit and
the comultiplication equation. Fully faithful affine Hopf `Spec` transports any
group-scheme isomorphism to a bialgebra equivalence, contradicting this obstruction.

This is an obstruction to an isomorphism **of group schemes**, not to an
isomorphism of their underlying schemes. The positive-exponent hypothesis is
essential: at `m = 0`, the infinitesimal coordinate itself vanishes.

Milne's *Algebraic Groups*, item 2.5, asserts non-isomorphism without the
necessary `m > 0` restriction. The proof here rules out *every* group-scheme
isomorphism by transporting primitive elements through affine Hopf `Spec`;
the tensor-diagonal argument for the absence of nonzero primitive elements
in a monoid algebra is provided by `AlgebraicGroups.Algebra.MonoidAlgebraPrimitive`.
Failure of the particular coordinate translation to preserve comultiplication
alone would not establish this theorem.

## References

- James S. Milne, *Algebraic Groups* (2017), item 2.5, p. 40 (the
  group-nonisomorphism assertion, corrected here at `m = 0`).
- `AlgebraicGroups.Algebra.MonoidAlgebraPrimitive` (the general
  diagonal-coefficient argument for primitive elements).
- Mathlib, `Mathlib.RingTheory.Bialgebra.Primitive`,
  `Mathlib.RingTheory.Coalgebra.Primitive`, and
  `Mathlib.AlgebraicGeometry.Group.Affine` (the primitive-element predicate,
  preservation under coalgebra equivalences and fully faithful affine Hopf `Spec`).
-/

set_option warningAsError true

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

/-- In positive characteristic, no group-scheme isomorphism identifies the
characteristic-power infinitesimal additive group with roots of unity of the
same order. This is the corrected `0 < m` form of the assertion in Milne's
*Algebraic Groups*, item 2.5: at `m = 0` the groups are isomorphic. The proof
compares primitive elements, rather than only checking one coordinate translation. -/
theorem infinitesimalAdditiveGroupScheme_not_iso_rootsOfUnity
    (K : Type u) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (m : ℕ) (hm : 0 < m) :
    ¬ Nonempty (infinitesimalAdditiveGroupScheme K p m ≅
      (TauCeti.RootsOfUnityGroup.groupScheme K (p ^ m))) := by
  intro ⟨iso⟩
  have hN : 1 < p ^ m := Nat.one_lt_pow (Nat.ne_of_gt hm) (Fact.out : p.Prime).one_lt
  have hcoord : infinitesimalAdditiveCoordinate K p m ≠ 0 :=
    additivePowerCoordinate_ne_zero K (p ^ m) hN
  have hprim : Bialgebra.IsPrimitiveElem K
      (infinitesimalAdditiveCoordinate K p m) := by
    constructor
    · exact infinitesimalAdditiveCoordinate_counit K p m
    · simpa only [add_comm] using infinitesimalAdditiveCoordinate_comul K p m
  let isoHopf : (hopfSpec (.of K)).obj
      (.op (.of K (infinitesimalAdditiveCoordinateRing K p m))) ≅
      (hopfSpec (.of K)).obj (.op (.of K ((MonoidAlgebra K
        (TauCeti.RootsOfUnityGroup.characterGroup.{u} (p ^ m)))))) := iso
  let equiv : infinitesimalAdditiveCoordinateRing K p m ≃ₐc[K]
      (MonoidAlgebra K (TauCeti.RootsOfUnityGroup.characterGroup.{u} (p ^ m))) :=
    CommHopfAlgCat.ofIso
      (((hopfSpec.fullyFaithful (R := .of K)).preimageIso isoHopf).unop.symm)
  have he : Bialgebra.IsPrimitiveElem K
      (equiv (infinitesimalAdditiveCoordinate K p m)) := by
    simpa only [map_one] using
      (Coalgebra.isSkewPrimitiveElem_map_equiv (R := K)
        (g := (1 : infinitesimalAdditiveCoordinateRing K p m)) (h := 1)
        (a := infinitesimalAdditiveCoordinate K p m) equiv).2 hprim
  apply hcoord
  apply (EquivLike.injective equiv)
  exact ((MonoidAlgebra.isPrimitiveElem_iff_eq_zero _).mp he).trans (map_zero equiv).symm

end AlgebraicGeometry
