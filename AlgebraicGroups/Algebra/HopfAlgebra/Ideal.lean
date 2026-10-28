/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.Quotient
public import AlgebraicGroups.Algebra.HopfAlgebra.Hom
public import Mathlib.RingTheory.HopfAlgebra.Quotient

/-!
# Hopf-ideal properties of kernels and inverse images

For full Hopf algebras and a bundled bialgebra homomorphism, inverse images
preserve `Ideal.IsHopfIdeal` whenever the scalar-restricted ordinary ideal
preimage is a coideal. The corresponding kernel theorem assumes precisely the
coideality of the scalar-restricted ordinary ring kernel. Over a field, both
coideality conditions follow without additional hypotheses.

The source and target rings need not be commutative. The kernel theorems allow
a semiring target. The property `Ideal.IsHopfIdeal` consists of restricted
coideality and antipode stability; it does not imply two-sidedness. A quotient
ring or quotient Hopf algebra requires the separate two-sidedness condition.

## References

* J. S. Milne, *Algebraic Groups*, Proposition 3.11, for kernels as Hopf ideals.
* Mathlib, `Mathlib.RingTheory.HopfAlgebra.Quotient`, for `Ideal.IsHopfIdeal`.
* `AlgebraicGroups.Algebra.HopfAlgebra.Hom`, for compatibility of bialgebra
  homomorphisms with antipodes.
* `AlgebraicGroups.Algebra.Coalgebra.Quotient`, for field kernel coideality,
  and Mathlib, `Mathlib.RingTheory.Coalgebra.Quotient`, for the linear
  coalgebra quotient used for inverse images.
-/

@[expose] public section

universe u v w

/-- The inverse image of an ideal with the Hopf-ideal property has that property
if its scalar-restricted ordinary ideal preimage is a coideal. This does not
assert two-sidedness of either ideal. -/
theorem Ideal.IsHopfIdeal.comap_of_isCoideal
    {R : Type u} {A : Type v} {B : Type w}
    [CommRing R] [Ring A] [Ring B]
    [HopfAlgebra R A] [HopfAlgebra R B]
    {J : Ideal B} (hJ : Ideal.IsHopfIdeal R J) (f : A →ₐc[R] B)
    (hco : ((J.comap f.toAlgHom.toRingHom).restrictScalars R).IsCoideal) :
    Ideal.IsHopfIdeal R (J.comap f.toAlgHom.toRingHom) := by
  refine
    { toIsCoideal := hco
      antipode_mem := ?_ }
  intro x hx
  change f (HopfAlgebra.antipode R x) ∈ J
  rw [BialgHomClass.map_antipode f]
  exact hJ.antipode_mem (Ideal.mem_comap.mp hx)

/-- The ordinary ring kernel of a bialgebra homomorphism between full Hopf
algebras has the Hopf-ideal property if its scalar restriction is a coideal.
The target need only be a semiring. -/
theorem BialgHom.ker_isHopfIdeal_of_isCoideal
    {R : Type u} {A : Type v} {B : Type w}
    [CommRing R] [Ring A] [Semiring B]
    [HopfAlgebra R A] [HopfAlgebra R B]
    (f : A →ₐc[R] B)
    (hco : ((RingHom.ker f.toAlgHom.toRingHom).restrictScalars R).IsCoideal) :
    Ideal.IsHopfIdeal R (RingHom.ker f.toAlgHom.toRingHom) := by
  refine
    { toIsCoideal := hco
      antipode_mem := ?_ }
  intro x hx
  have hfx : f x = 0 := RingHom.mem_ker.mp hx
  change f (HopfAlgebra.antipode R x) = 0
  rw [BialgHomClass.map_antipode f, hfx, map_zero]

/-- Over a field, inverse images along bialgebra homomorphisms between full
Hopf algebras preserve the Hopf-ideal property. No coideality, surjectivity or
two-sidedness hypothesis is needed beyond the target ideal's Hopf-ideal
property. -/
theorem Ideal.IsHopfIdeal.comap
    {k : Type u} {A : Type v} {B : Type w}
    [Field k] [Ring A] [Ring B]
    [HopfAlgebra k A] [HopfAlgebra k B]
    {J : Ideal B} (hJ : Ideal.IsHopfIdeal k J) (f : A →ₐc[k] B) :
    Ideal.IsHopfIdeal k (J.comap f.toAlgHom.toRingHom) := by
  let : (J.restrictScalars k).IsCoideal := hJ.toIsCoideal
  let q := Coalgebra.Quotient.mkQCoalgHom (J.restrictScalars k)
  let g := q.comp f.toCoalgHom
  have hker : LinearMap.ker g.toLinearMap =
      (J.comap f.toAlgHom.toRingHom).restrictScalars k := by
    ext x
    change Submodule.Quotient.mk (p := J.restrictScalars k) (f x) = 0 ↔
      x ∈ (J.comap f.toAlgHom.toRingHom).restrictScalars k
    simp only [Submodule.Quotient.mk_eq_zero, Submodule.restrictScalars_mem, Ideal.mem_comap,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, BialgHom.coe_toAlgHom]
  apply hJ.comap_of_isCoideal f
  rw [← hker]
  exact CoalgHomClass.ker_isCoideal g

/-- Over a field, the ordinary ring kernel of a bialgebra homomorphism between
full Hopf algebras has the Hopf-ideal property, without an additional coideality
or surjectivity hypothesis. The target need only be a semiring. This generalizes
Milne, *Algebraic Groups*, Proposition 3.11, taking a full bundled bialgebra
homomorphism as input and allowing noncommutative source rings. -/
theorem BialgHom.ker_isHopfIdeal
    {k : Type u} {A : Type v} {B : Type w}
    [Field k] [Ring A] [Semiring B]
    [HopfAlgebra k A] [HopfAlgebra k B]
    (f : A →ₐc[k] B) :
    Ideal.IsHopfIdeal k (RingHom.ker f.toAlgHom.toRingHom) := by
  let : AddCommGroup B := Module.addCommMonoidToAddCommGroup k
  have hker : LinearMap.ker f.toLinearMap =
      (RingHom.ker f.toAlgHom.toRingHom).restrictScalars k := by
    ext x
    simp only [LinearMap.mem_ker, Submodule.restrictScalars_mem, RingHom.mem_ker,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, BialgHom.coe_toAlgHom]
    rfl
  apply f.ker_isHopfIdeal_of_isCoideal
  rw [← hker]
  exact CoalgHomClass.ker_isCoideal f.toCoalgHom
