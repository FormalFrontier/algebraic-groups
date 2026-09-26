/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.MonoidAlgebraPrimitive
public import AlgebraicGroups.GroupScheme.RootsOfUnity

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

/-- With additive cancellation, the existing bialgebra iff recovers the
comultiplication-only convention from full primitivity. -/
theorem monoidAlgebraPrimitive_ring_bridge {R G : Type*} [CommRing R] [Monoid G]
    (x : MonoidAlgebra R G) :
    Coalgebra.comul (R := R) x = 1 ⊗ₜ[R] x + x ⊗ₜ[R] 1 ↔ x = 0 := by
  rw [← Bialgebra.isPrimitiveElem_iff_comul_eq_tmul_add_tmul]
  exact MonoidAlgebra.isPrimitiveElem_iff_eq_zero x

/-- The canonical bialgebra equivalence transports both counit and comultiplication. -/
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

/-- The roots-of-unity coordinate ring is the additive monoid algebra of `ZMod n`. -/
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
