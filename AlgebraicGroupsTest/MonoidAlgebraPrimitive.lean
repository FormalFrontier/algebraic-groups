/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.MonoidAlgebraPrimitive
public import AlgebraicGroups.GroupScheme.RootsOfUnity

/-!
# Primitive elements in monoid-algebra examples

This module applies `MonoidAlgebra.isPrimitiveElem_iff_eq_zero` to a
comultiplication-only condition, transports it to additive monoid algebras,
and specializes it to roots-of-unity coordinate rings. The additive transfer
is proved here using Mathlib's bialgebra equivalence and preservation of
skew-primitive elements, rather than by simply specializing the multiplicative
theorem. Primitivity includes a zero counit. Additive cancellation is needed
to recover that condition from comultiplication alone, but not for the full
primitive-vanishing or additive-transfer results.

The finite cyclic diagonal-coefficient argument in Formal Frontier's
*Alpha-power versus roots of unity: scheme isomorphism, not group isomorphism*
underlies the general monoid-algebra theorem used here. Milne's roots-of-unity
coordinates and comparison with infinitesimal additive groups provide the
published setting, not a general monoid-algebra primitive-vanishing theorem.

## References

- James S. Milne, *Algebraic Groups* (2017), §2a, items 2.4–2.5
  (roots-of-unity coordinates and the infinitesimal-additive comparison).
- Formal Frontier, *Alpha-power versus roots of unity: scheme isomorphism, not
  group isomorphism*, § “No group-scheme isomorphism for positive exponent”
  (finite cyclic diagonal-coefficient argument).
- Darij Grinberg and Victor Reiner, *Hopf algebras in combinatorics* (2020),
  Proposition 1.4.17 (cited by Mathlib for the primitive counit consequence).
- Mathlib, `Mathlib.RingTheory.Bialgebra.Primitive` and
  `Mathlib.RingTheory.Coalgebra.Primitive` (cancellation and skew-primitive
  transport), and `Mathlib.RingTheory.Bialgebra.MonoidAlgebra` (the
  additive-to-multiplicative bialgebra equivalence).
- `AlgebraicGroups.Algebra.MonoidAlgebraPrimitive` and
  `AlgebraicGroups.GroupScheme.RootsOfUnity` (the general primitive theorem
  and roots-of-unity coordinate-ring definition).
-/

public section

set_option warningAsError true

open scoped TensorProduct

variable {K M : Type*} [CommSemiring K] [Monoid M]

private theorem persistentTestMonoidAlgebraPrimitive001 (x : MonoidAlgebra K M) : Bialgebra.IsPrimitiveElem K x ↔ x = 0 :=
  MonoidAlgebra.isPrimitiveElem_iff_eq_zero x

private theorem persistentTestMonoidAlgebraPrimitive002 (x : MonoidAlgebra ℕ ℕ) : Bialgebra.IsPrimitiveElem ℕ x ↔ x = 0 :=
  MonoidAlgebra.isPrimitiveElem_iff_eq_zero x

private theorem persistentTestMonoidAlgebraPrimitive003 (x : MonoidAlgebra (ZMod 2) PUnit) : Bialgebra.IsPrimitiveElem (ZMod 2) x ↔
    x = 0 := MonoidAlgebra.isPrimitiveElem_iff_eq_zero x

private theorem persistentTestMonoidAlgebraPrimitive004 (x : MonoidAlgebra (ZMod 1) (Equiv.Perm (Fin 3))) :
    Bialgebra.IsPrimitiveElem (ZMod 1) x ↔ x = 0 :=
  MonoidAlgebra.isPrimitiveElem_iff_eq_zero x

private theorem persistentTestMonoidAlgebraPrimitive005 (x : MonoidAlgebra ℕ (Equiv.Perm (Fin 3))) :
    Bialgebra.IsPrimitiveElem ℕ x ↔ x = 0 :=
  MonoidAlgebra.isPrimitiveElem_iff_eq_zero x

/-- Over a commutative ring, the comultiplication identity alone forces a
monoid-algebra element to vanish. Mathlib's
`Bialgebra.isPrimitiveElem_iff_comul_eq_tmul_add_tmul` recovers the zero counit
using additive cancellation; `MonoidAlgebra.isPrimitiveElem_iff_eq_zero` then
gives the conclusion. Mathlib cites Grinberg–Reiner, *Hopf algebras in
combinatorics*, Proposition 1.4.17 for the counit step. Without cancellation,
the comultiplication identity alone need not force vanishing. -/
theorem monoidAlgebraPrimitive_ring_bridge {R G : Type*} [CommRing R] [Monoid G]
    (x : MonoidAlgebra R G) :
    Coalgebra.comul (R := R) x = 1 ⊗ₜ[R] x + x ⊗ₜ[R] 1 ↔ x = 0 := by
  rw [← Bialgebra.isPrimitiveElem_iff_comul_eq_tmul_add_tmul]
  exact MonoidAlgebra.isPrimitiveElem_iff_eq_zero x

/-- An additive monoid algebra over a commutative semiring has no nonzero
primitive elements. The proof transports primitivity through Mathlib's
`AddMonoidAlgebra.toMultiplicativeBialgEquiv` using
`Coalgebra.isSkewPrimitiveElem_map_equiv`, applies
`MonoidAlgebra.isPrimitiveElem_iff_eq_zero`, and transfers vanishing back by
injectivity. Neither additive cancellation nor a finiteness assumption on the
index monoid is required. -/
theorem additiveMonoidAlgebraPrimitive_iff_zero {R G : Type*} [CommSemiring R]
    [AddMonoid G] (x : AddMonoidAlgebra R G) :
    Bialgebra.IsPrimitiveElem R x ↔ x = 0 := by
  let e := AddMonoidAlgebra.toMultiplicativeBialgEquiv R R G
  constructor
  · intro hx
    have he : Bialgebra.IsPrimitiveElem R (e x) := by
      simpa only [map_one] using
        (Coalgebra.isSkewPrimitiveElem_map_equiv (R := R)
          (g := (1 : AddMonoidAlgebra R G)) (h := 1) (a := x) e).2 hx
    apply (EquivLike.injective e)
    exact ((MonoidAlgebra.isPrimitiveElem_iff_eq_zero (e x)).1 he).trans (map_zero e).symm
  · rintro rfl
    exact Coalgebra.IsSkewPrimitiveElem.zero

/-- The roots-of-unity coordinate ring `R[ZMod n]` has no nonzero primitive
elements, by `additiveMonoidAlgebraPrimitive_iff_zero` and the coordinate-ring
definition. Milne, *Algebraic Groups* (2017), §2a, item 2.4 supplies the
cyclic coordinate setting and comultiplication law, not this general vanishing
statement. The result also covers `n = 0` and the zero ring; it uses the
canonical bialgebra structure rather than an algebra-only quotient
presentation. -/
theorem rootsOfUnityCoordinateRing_primitive_iff_zero (R : Type*) [CommRing R]
    (n : ℕ) (x : AlgebraicGeometry.rootsOfUnityCoordinateRing R n) :
    Bialgebra.IsPrimitiveElem R x ↔ x = 0 :=
  additiveMonoidAlgebraPrimitive_iff_zero x

private theorem persistentTestMonoidAlgebraPrimitive006 (x : AlgebraicGeometry.rootsOfUnityCoordinateRing (ZMod 1) 1) :
    Bialgebra.IsPrimitiveElem (ZMod 1) x ↔ x = 0 :=
  rootsOfUnityCoordinateRing_primitive_iff_zero (ZMod 1) 1 x

private theorem persistentTestMonoidAlgebraPrimitive007 (R : Type*) [CommRing R] (x : AlgebraicGeometry.rootsOfUnityCoordinateRing R 1) :
    Bialgebra.IsPrimitiveElem R x ↔ x = 0 :=
  rootsOfUnityCoordinateRing_primitive_iff_zero R 1 x

#print axioms MonoidAlgebra.isPrimitiveElem_iff_eq_zero
#print axioms Bialgebra.isPrimitiveElem_iff_comul_eq_tmul_add_tmul
#print axioms Coalgebra.isSkewPrimitiveElem_map_equiv
#print axioms monoidAlgebraPrimitive_ring_bridge
#print axioms additiveMonoidAlgebraPrimitive_iff_zero
#print axioms rootsOfUnityCoordinateRing_primitive_iff_zero
