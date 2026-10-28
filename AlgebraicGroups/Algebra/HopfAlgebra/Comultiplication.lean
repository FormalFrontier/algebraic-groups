/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Coalgebra.Primitive
public import TauCeti.Algebra.HopfAlgebra.Antipode

/-!
# The antipode reverses comultiplication

For a Hopf algebra over a commutative semiring, comultiplication after the
antipode is the flipped comultiplication followed by the tensor of antipodes.
The algebra need not be commutative, and the coalgebra need not be cocommutative.
Consequently, the antipode sends `(g, h)`-skew-primitive elements to
`(S h, S g)`-skew-primitive elements, without assumptions on the endpoints.

* The square of the antipode preserves comultiplication:
  `HopfAlgebra.comul_comp_antipode_comp_antipode` and
  `HopfAlgebra.comul_antipode_antipode`.

The anti-comultiplication law is supplied by Tau Ceti. The square and skew-primitive
conclusions below use that canonical law directly.

## References

* Robert Hawkins, Mathlib, `RingTheory/Coalgebra/Primitive`: the skew-primitive
  predicate and its characteristic equations.
* Kim Morrison, Mathlib, `CategoryTheory/Monoidal/Hopf_`: the corresponding
  identity for braided Hopf objects and the convolution inverse-uniqueness proof.
* Yaël Dillies, Michał Mrugała and Yunzhou Xie, Mathlib,
  `RingTheory/HopfAlgebra/Convolution`: the concrete right convolution inverse
  of comultiplication.
* Ali Ramsey and Eric Wieser, Mathlib, `RingTheory/Coalgebra/Basic`: the
  coassociativity and counit API.
* Kenny Lau and Mario Carneiro, Mathlib, `LinearAlgebra/TensorProduct`:
  the tensor universal property, associators and permutations.
-/

@[expose] public section

universe u v

open TensorProduct WithConv
open scoped RingTheory.LinearMap

namespace HopfAlgebra

variable {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [HopfAlgebra R A]

local notation "Δ" => Coalgebra.comul (R := R) (A := A)
local notation "S" => antipode R (A := A)

/-- The square of the antipode preserves comultiplication, with no commutativity
or cocommutativity assumption. -/
theorem comul_comp_antipode_comp_antipode :
    Δ ∘ₗ (S ∘ₗ S) = map (S ∘ₗ S) (S ∘ₗ S) ∘ₗ Δ := by
  ext x
  simp only [LinearMap.comp_apply, TauCeti.HopfAlgebra.antipode_comul_antidistrib_apply,
    ← map_comm, comm_comm, map_map]

/-- Comultiplication of the square of the antipode is the tensor of its square
applied to comultiplication. -/
theorem comul_antipode_antipode (x : A) :
    Δ (S (S x)) = map (S ∘ₗ S) (S ∘ₗ S) (Δ x) :=
  LinearMap.congr_fun comul_comp_antipode_comp_antipode x

end HopfAlgebra

namespace Coalgebra.IsSkewPrimitiveElem

variable {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [HopfAlgebra R A]
  {g h a : A}

/-- The antipode reverses the endpoints of a skew-primitive element.
No group-like or unit hypotheses on the endpoints are required. -/
lemma antipode (ha : IsSkewPrimitiveElem R g h a) :
    IsSkewPrimitiveElem R (HopfAlgebra.antipode R h) (HopfAlgebra.antipode R g)
      (HopfAlgebra.antipode R a) where
  counit_eq_zero := by rw [HopfAlgebra.counit_antipode, ha.counit_eq_zero]
  comul_eq_tmul_add_tmul := by
    rw [TauCeti.HopfAlgebra.antipode_comul_antidistrib_apply, ha.comul_eq_tmul_add_tmul]
    simp only [map_add, _root_.TensorProduct.comm_tmul, _root_.TensorProduct.map_tmul,
      add_comm]

end Coalgebra.IsSkewPrimitiveElem
