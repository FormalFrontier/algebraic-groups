/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Yunzhou Xie. All rights reserved.
Modifications by Formal Frontier Agents.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Yunzhou Xie, Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.HopfAlgebra.Convolution
public import Mathlib.Algebra.Group.Ext

/-!
# Convolution groups of algebra-valued points

Algebra maps from a Hopf algebra to a commutative algebra form a group under
Mathlib's convolution multiplication. The coefficient algebra needs no
coalgebra structure. Even the source need not be commutative: its antipode is
antimultiplicative, and an algebra map into a commutative target turns this
into multiplicativity.

`AlgHom.convolutionGroup` is a named group structure, not an instance. It
extends the existing convolution monoid on the same `WithConv` carrier.
`AlgHom.convolutionGroup_eq_convGroup` identifies the entire structure with
Mathlib's `AlgHom.convGroup` when the latter applies, including division and
integer powers. Postcomposition uses the existing convolution multiplication.

## References

* Yaël Dillies, Michał Mrugała and Yunzhou Xie, Mathlib,
  `RingTheory/HopfAlgebra/Convolution`: the antipode identities and the original
  `AlgHom.convInv` and `AlgHom.convGroup` constructions generalized here.
* Yaël Dillies and Michał Mrugała, Mathlib,
  `RingTheory/Bialgebra/Convolution`: the convolution monoid and compatibility
  of its multiplication with postcomposition.
* Mathlib, `Algebra/Group/Ext`: equality of group structures with the same
  multiplication, including all their operation data.
-/

@[expose] public section

noncomputable section

open WithConv

universe u a r s t

namespace AlgHom

section Postcomposition

variable {K : Type u} {A : Type a} {R : Type r} {S : Type s} {T : Type t}
  [CommSemiring K] [Semiring A] [Bialgebra K A]
  [CommSemiring R] [Algebra K R] [CommSemiring S] [Algebra K S]
  [CommSemiring T] [Algebra K T]

/-- Postcomposition of convolution algebra maps by a coefficient algebra map.
No coalgebra structure or coalgebra compatibility on the coefficient map is needed. -/
def convolutionPostcomp (q : R →ₐ[K] S) :
    WithConv (A →ₐ[K] R) →* WithConv (A →ₐ[K] S) where
  toFun f := toConv (q.comp f.ofConv)
  map_one' := by
    apply ofConv_injective
    ext x
    simp
  map_mul' f g := ofConv_injective (comp_convMul_distrib q f g)

/-- The coordinate algebra map of a postcomposed point. -/
@[simp] theorem convolutionPostcomp_ofConv (q : R →ₐ[K] S)
    (f : WithConv (A →ₐ[K] R)) :
    (convolutionPostcomp q f).ofConv = q.comp f.ofConv := rfl

/-- Evaluation of a postcomposed point. -/
@[simp] theorem convolutionPostcomp_apply (q : R →ₐ[K] S)
    (f : WithConv (A →ₐ[K] R)) (x : A) :
    convolutionPostcomp q f x = q (f x) := rfl

/-- Postcomposition by the identity is the identity monoid homomorphism. -/
@[simp] theorem convolutionPostcomp_id :
    convolutionPostcomp (A := A) (AlgHom.id K R) = MonoidHom.id _ := by
  ext f x
  rfl

/-- Postcomposition respects composition of coefficient algebra maps. -/
@[simp] theorem convolutionPostcomp_comp (q : R →ₐ[K] S) (p : S →ₐ[K] T) :
    convolutionPostcomp (A := A) (p.comp q) =
      (convolutionPostcomp p).comp (convolutionPostcomp q) := by
  ext f x
  rfl

end Postcomposition

section Hopf

variable {K : Type u} {A : Type a} {R : Type r} {S : Type s}
  [CommSemiring K] [Semiring A] [HopfAlgebra K A]
  [CommSemiring R] [Algebra K R] [CommSemiring S] [Algebra K S]

/-- The convolution inverse of an algebra-valued point: precomposition with
its source's antipode. Commutativity of the coefficient algebra suffices even
when the source Hopf algebra is not commutative. -/
def convolutionInverse (f : WithConv (A →ₐ[K] R)) : WithConv (A →ₐ[K] R) :=
  toConv <| AlgHom.ofLinearMap
    (f.ofConv.toLinearMap.comp (HopfAlgebra.antipode K))
    (by simp)
    (fun x y ↦ by
      change f.ofConv (HopfAlgebra.antipode K (x * y)) =
        f.ofConv (HopfAlgebra.antipode K x) * f.ofConv (HopfAlgebra.antipode K y)
      rw [HopfAlgebra.antipode_mul_antidistrib, map_mul, mul_comm])

/-- Evaluation of the convolution inverse. -/
@[simp] theorem convolutionInverse_apply (f : WithConv (A →ₐ[K] R)) (x : A) :
    convolutionInverse f x = f (HopfAlgebra.antipode K x) := rfl

/-- On linear maps the convolution inverse is precomposition with the antipode. -/
@[simp] theorem toLinearMap_convolutionInverse (f : WithConv (A →ₐ[K] R)) :
    (convolutionInverse f).ofConv.toLinearMap =
      f.ofConv.toLinearMap.comp (HopfAlgebra.antipode K) := rfl

/-- The source antipode gives a left inverse in the existing convolution monoid. -/
@[simp] theorem convolutionInverse_mul (f : WithConv (A →ₐ[K] R)) :
    convolutionInverse f * f = 1 := by
  apply ofConv_injective
  apply AlgHom.toLinearMap_injective
  apply toConv_injective
  rw [toLinearMap_convMul, toLinearMap_convOne]
  apply ofConv_injective
  calc
    (toConv (convolutionInverse f).ofConv.toLinearMap *
        toConv f.ofConv.toLinearMap : WithConv (A →ₗ[K] R)).ofConv =
        f.ofConv.toLinearMap.comp
          (toConv (HopfAlgebra.antipode K) * toConv LinearMap.id :
            WithConv (A →ₗ[K] A)).ofConv := by
      rw [LinearMap.algHom_comp_convMul_distrib]
      rfl
    _ = f.ofConv.toLinearMap.comp (1 : WithConv (A →ₗ[K] A)).ofConv := by
      rw [LinearMap.antipode_mul_id]
    _ = (1 : WithConv (A →ₗ[K] R)).ofConv := by
      ext x
      simp

/-- The convolution group of algebra-valued points, extending Mathlib's
existing convolution monoid without a coalgebra structure on the target.
This is a value, deliberately not a global instance. -/
@[instance_reducible]
def convolutionGroup (K : Type u) (A : Type a) (R : Type r)
    [CommSemiring K] [Semiring A] [HopfAlgebra K A]
    [CommSemiring R] [Algebra K R] : Group (WithConv (A →ₐ[K] R)) where
  toMonoid := inferInstanceAs (Monoid (WithConv (A →ₐ[K] R)))
  inv := convolutionInverse
  inv_mul_cancel := convolutionInverse_mul

/-- Forgetting the inverse recovers precisely the existing convolution monoid. -/
@[simp] theorem convolutionGroup_toMonoid :
    (convolutionGroup K A R).toMonoid =
      inferInstanceAs (Monoid (WithConv (A →ₐ[K] R))) := rfl

/-- The unit of the named group is the existing convolution unit. -/
@[simp] theorem convolutionGroup_one :
    (convolutionGroup K A R).one = (1 : WithConv (A →ₐ[K] R)) := rfl

/-- The multiplication of the named group is the existing convolution product. -/
@[simp] theorem convolutionGroup_mul (f g : WithConv (A →ₐ[K] R)) :
    (convolutionGroup K A R).mul f g = f * g := rfl

/-- Natural powers in the named group are the existing convolution powers. -/
@[simp] theorem convolutionGroup_npow (f : WithConv (A →ₐ[K] R)) (n : ℕ) :
    (convolutionGroup K A R).npow n f = f ^ n := rfl

/-- The inverse operation of the named group is antipode precomposition. -/
@[simp] theorem convolutionGroup_inv (f : WithConv (A →ₐ[K] R)) :
    (convolutionGroup K A R).inv f = convolutionInverse f := rfl

/-- The source antipode is also a right inverse in the existing convolution monoid. -/
@[simp] theorem mul_convolutionInverse (f : WithConv (A →ₐ[K] R)) :
    f * convolutionInverse f = 1 := by
  let := convolutionGroup K A R
  exact mul_inv_cancel f

/-- The convolution inverse fixes the counit point. -/
@[simp] theorem convolutionInverse_one :
    convolutionInverse (1 : WithConv (A →ₐ[K] R)) = 1 := by
  let := convolutionGroup K A R
  exact (inv_one : (1 : WithConv (A →ₐ[K] R))⁻¹ = 1)

/-- Taking the convolution inverse twice fixes a point. -/
@[simp] theorem convolutionInverse_inverse (f : WithConv (A →ₐ[K] R)) :
    convolutionInverse (convolutionInverse f) = f := by
  let := convolutionGroup K A R
  exact inv_inv f

/-- The convolution inverse reverses products. -/
theorem convolutionInverse_mul_rev (f g : WithConv (A →ₐ[K] R)) :
    convolutionInverse (f * g) = convolutionInverse g * convolutionInverse f := by
  let := convolutionGroup K A R
  exact mul_inv_rev f g

/-- Postcomposition commutes with the antipode inverse, for every coefficient
algebra map, without a coalgebra condition. -/
@[simp] theorem convolutionPostcomp_inverse (q : R →ₐ[K] S)
    (f : WithConv (A →ₐ[K] R)) :
    convolutionPostcomp q (convolutionInverse f) =
      convolutionInverse (convolutionPostcomp q f) := by
  apply ofConv_injective
  ext x
  rfl

end Hopf

section CommutativeSource

variable {K : Type u} {A : Type a} {R : Type r}
  [CommSemiring K] [CommSemiring A] [HopfAlgebra K A]
  [CommSemiring R] [Algebra K R]

/-- For a commutative source, the inverse is composition of algebra maps with
Mathlib's bundled antipode. -/
@[simp] theorem convolutionInverse_ofConv (f : WithConv (A →ₐ[K] R)) :
    (convolutionInverse f).ofConv =
      f.ofConv.comp (HopfAlgebra.antipodeAlgHom K A) := by
  ext x
  rfl

end CommutativeSource

section Compatibility

variable (K : Type u) (A : Type a) (R : Type r)
  [CommSemiring K] [CommSemiring A] [HopfAlgebra K A]
  [CommSemiring R] [Bialgebra K R]

/-- Under the canonical algebra of a target bialgebra, the entire generalized
group value equals Mathlib's original `AlgHom.convGroup`. Equality is of group
structures, so includes inverse, division and all integer-power data. -/
theorem convolutionGroup_eq_convGroup :
    convolutionGroup K A R = (AlgHom.convGroup : Group (WithConv (A →ₐ[K] R))) :=
  Group.ext rfl

/-- The generalized inverse agrees with Mathlib's original convolution inverse. -/
@[simp] theorem convolutionInverse_eq_inv (f : WithConv (A →ₐ[K] R)) :
    convolutionInverse f = f⁻¹ := by
  change (convolutionGroup K A R).inv f = _
  rw [convolutionGroup_eq_convGroup]

/-- Division agrees with the division data of Mathlib's original group. -/
theorem convolutionGroup_div_eq (f g : WithConv (A →ₐ[K] R)) :
    (convolutionGroup K A R).div f g = f / g := by
  rw [convolutionGroup_eq_convGroup]
  rfl

/-- Integer powers agree with the integer-power data of Mathlib's original group. -/
theorem convolutionGroup_zpow_eq (f : WithConv (A →ₐ[K] R)) (n : ℤ) :
    (convolutionGroup K A R).zpow n f = f ^ n := by
  rw [convolutionGroup_eq_convGroup]
  rfl

/-- The comparison with the original convolution group is the identity on its
unchanged carrier and multiplication; `convolutionGroup_eq_convGroup` identifies
the full group structures. -/
def convolutionGroupEquiv : WithConv (A →ₐ[K] R) ≃* WithConv (A →ₐ[K] R) :=
  MulEquiv.refl _

/-- The comparison does not change a point. -/
@[simp] theorem convolutionGroupEquiv_apply (f : WithConv (A →ₐ[K] R)) :
    convolutionGroupEquiv K A R f = f := rfl

variable {K A R} {S : Type s} [CommSemiring S] [Bialgebra K S]

/-- The identity comparison commutes with postcomposition by every algebra map,
not just bialgebra maps. -/
theorem convolutionGroupEquiv_postcomp (q : R →ₐ[K] S) (f : WithConv (A →ₐ[K] R)) :
    convolutionGroupEquiv K A S (convolutionPostcomp q f) =
      convolutionPostcomp q (convolutionGroupEquiv K A R f) := rfl

end Compatibility

end AlgHom
