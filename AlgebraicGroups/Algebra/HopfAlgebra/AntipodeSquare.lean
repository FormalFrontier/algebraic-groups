/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.HopfAlgebra.Antipode
public import AlgebraicGroups.Algebra.HopfAlgebra.Comultiplication
public import AlgebraicGroups.Algebra.HopfAlgebra.Hom

/-!
# The square of the antipode as a bialgebra endomorphism

The square of the antipode of a Hopf algebra over a commutative semiring
preserves multiplication, the unit, comultiplication and the counit. Its
underlying linear map is the composite of the antipode with itself.

Bialgebra homomorphisms between Hopf algebras intertwine these endomorphisms.
For a commutative Hopf algebra the antipode-square endomorphism is the identity;
no such identity is asserted for a general noncommutative Hopf algebra.
Neither cocommutativity nor finiteness is assumed.

## References

* Mathlib, `RingTheory/HopfAlgebra/Basic` and `Convolution`: the antipode's
  unit, counit and anti-multiplication laws.
* Mathlib, `RingTheory/Bialgebra/Hom` and `Coalgebra/Hom`: bundled
  homomorphisms and their composition and extensionality API.
* `AlgebraicGroups.Algebra.HopfAlgebra.Comultiplication`: preservation of
  comultiplication by the square of the antipode.
* `AlgebraicGroups.Algebra.HopfAlgebra.Antipode` and `Hom`: commutative
  involutivity and compatibility of bialgebra homomorphisms with antipodes.
-/

@[expose] public section

universe u v w

namespace HopfAlgebra

/-- The square of the antipode as a bialgebra endomorphism. -/
def antipodeSquareBialgHom (R : Type u) (A : Type v)
    [CommSemiring R] [Semiring A] [HopfAlgebra R A] : A →ₐc[R] A where
  toLinearMap := (antipode R (A := A)).comp (antipode R (A := A))
  counit_comp := by
    rw [← LinearMap.comp_assoc, counit_comp_antipode, counit_comp_antipode]
  map_comp_comul := (comul_comp_antipode_comp_antipode (R := R) (A := A)).symm
  map_one' := by
    change antipode R (antipode R (1 : A)) = 1
    rw [antipode_one, antipode_one]
  map_mul' := by
    intro x y
    change antipode R (antipode R (x * y)) =
      antipode R (antipode R x) * antipode R (antipode R y)
    rw [antipode_mul_antidistrib, antipode_mul_antidistrib]

/-- Evaluation of the antipode-square endomorphism is two antipode applications. -/
@[simp]
theorem antipodeSquareBialgHom_apply (R : Type u) (A : Type v)
    [CommSemiring R] [Semiring A] [HopfAlgebra R A] (x : A) :
    antipodeSquareBialgHom R A x = antipode R (antipode R x) :=
  rfl

/-- The linear projection of the antipode-square endomorphism is `S.comp S`. -/
theorem antipodeSquareBialgHom_toLinearMap (R : Type u) (A : Type v)
    [CommSemiring R] [Semiring A] [HopfAlgebra R A] :
    (antipodeSquareBialgHom R A).toLinearMap =
      (antipode R (A := A)).comp (antipode R (A := A)) :=
  rfl

/-- In a commutative Hopf algebra the generic antipode-square map is the identity. -/
@[simp]
theorem antipodeSquareBialgHom_eq_id (R : Type u) (A : Type v)
    [CommSemiring R] [CommSemiring A] [HopfAlgebra R A] :
    antipodeSquareBialgHom R A = BialgHom.id R A := by
  apply BialgHom.ext
  intro x
  simpa only [antipodeSquareBialgHom_apply, BialgHom.coe_id, id_eq] using
    (antipode_antipode (R := R) x)

end HopfAlgebra

namespace BialgHom

/-- A bialgebra map intertwines the antipode-square endomorphisms. -/
theorem comp_antipodeSquareBialgHom {R : Type u} {A : Type v} {B : Type w}
    [CommSemiring R] [Semiring A] [Semiring B]
    [HopfAlgebra R A] [HopfAlgebra R B] (f : A →ₐc[R] B) :
    f.comp (HopfAlgebra.antipodeSquareBialgHom R A) =
      (HopfAlgebra.antipodeSquareBialgHom R B).comp f := by
  apply BialgHom.ext
  intro x
  simp only [coe_comp, Function.comp_apply, HopfAlgebra.antipodeSquareBialgHom_apply,
    map_antipode]

end BialgHom
