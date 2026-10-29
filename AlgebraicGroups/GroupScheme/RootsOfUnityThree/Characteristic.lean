/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.InfinitesimalAdditiveTranslation
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Reduced
public import Mathlib.Algebra.TrivSqZeroExt.Basic

/-!
# Cube roots of unity in characteristic three

In characteristic three the coordinate generator of μ₃ minus one is a nonzero
nilpotent, even though every point over a field extension is the identity.
The element `1 + TrivSqZeroExt.inr 1` gives a nonidentity point over the
square-zero extension. Its coordinate homomorphism evaluates the generator
at this element and evaluates polynomial classes by substitution.

The coordinate assertions use the prime-power translation from μ₃ to the
infinitesimal additive coordinate algebra. This is an algebra comparison,
not an assertion of compatibility with the group laws.

## References

- James S. Milne, *Algebraic Groups* (2017), Example 1.6 (the
  characteristic-three case of μ₃).
- `AlgebraicGroups.GroupScheme.InfinitesimalAdditiveTranslation` and
  `AlgebraicGroups.GroupScheme.AdditivePowerQuotient` (coordinate translation
  and nonvanishing).
- Mathlib, `Mathlib.Algebra.CharP.Reduced` and
  `Mathlib.Algebra.TrivSqZeroExt.Basic` (reduced-ring roots and the
  square-zero extension).
-/

@[expose] public section

noncomputable section

open CategoryTheory Polynomial
open scoped CategoryTheory.MonObj

universe u v

namespace AlgebraicGeometry.RootsOfUnityThree

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

section Coordinates

variable (k : Type u) [Field k] [CharP k 3]

/-- The coordinate generator of μ₃ minus one is nonzero in characteristic three. -/
theorem coordinate_sub_one_ne_zero :
    rootsOfUnityCoordinateGenerator k 3 - 1 ≠ 0 := by
  have hT : infinitesimalAdditiveCoordinate k 3 1 ≠ 0 := by
    change additivePowerCoordinate k (3 ^ 1) ≠ 0
    exact additivePowerCoordinate_ne_zero k (3 ^ 1) (by decide)
  have htranslation :
      (infinitesimalAdditiveTranslationAlgEquiv k 3 1).symm
        (infinitesimalAdditiveCoordinate k 3 1) =
          rootsOfUnityCoordinateGenerator k 3 - 1 := by
    convert infinitesimalAdditiveTranslationAlgEquiv_symm_coordinate k 3 1 using 1
  intro hzero
  apply hT
  apply (infinitesimalAdditiveTranslationAlgEquiv k 3 1).symm.injective
  simpa only [map_zero] using htranslation.trans hzero

/-- The coordinate generator of μ₃ minus one has cube zero in characteristic three. -/
theorem coordinate_sub_one_cube :
    (rootsOfUnityCoordinateGenerator k 3 - 1) ^ 3 = 0 := by
  have h := congrArg (infinitesimalAdditiveTranslationAlgEquiv k 3 1).symm
    (infinitesimalAdditiveCoordinate_pow k 3 1)
  have ht := infinitesimalAdditiveTranslationAlgEquiv_symm_coordinate k 3 1
  rw [map_pow, map_zero, ht] at h
  convert h using 1

/-- In the polynomial presentation of μ₃, the distinguished root minus one is nonzero. -/
theorem root_sub_one_ne_zero :
    AdjoinRoot.root (rootsOfUnityPolynomial k 3) - 1 ≠ 0 := by
  intro hzero
  apply coordinate_sub_one_ne_zero k
  have h := congrArg (rootsOfUnityCoordinateAlgEquiv k 3).symm hzero
  simpa only [map_sub, map_one, map_zero,
    rootsOfUnityCoordinateAlgEquiv_symm_root] using h

/-- In the polynomial presentation of μ₃, the distinguished root minus one has cube zero. -/
theorem root_sub_one_cube :
    (AdjoinRoot.root (rootsOfUnityPolynomial k 3) - 1) ^ 3 = 0 := by
  have h := congrArg (rootsOfUnityCoordinateAlgEquiv k 3) (coordinate_sub_one_cube k)
  simpa only [map_pow, map_sub, map_one, map_zero,
    rootsOfUnityCoordinateAlgEquiv_generator] using h

end Coordinates

section ReducedRings

variable (R : Type v) [CommRing R] [_root_.IsReduced R] [CharP R 3]

private theorem cube_eq_one_iff (a : R) : a ^ 3 = 1 ↔ a = 1 := by
  simpa only [pow_one, mul_one] using
    (ExpChar.pow_prime_pow_mul_eq_one_iff (R := R) 3 1 1 a)

/-- The group of cube roots of unity in a reduced ring of characteristic three is trivial. -/
theorem root_eq_one (ζ : rootsOfUnity 3 R) : ζ = 1 := by
  apply rootsOfUnity.coe_injective
  change ((ζ : Rˣ) : R) = 1
  exact (cube_eq_one_iff R _).mp
    ((mem_rootsOfUnity' 3 (ζ : Rˣ)).mp ζ.property)

end ReducedRings

section FieldExtensions

variable (k : Type u) (F : Type v) [Field k] [CharP k 3] [Field F] [Algebra k F]

include k in
/-- Every cube root of one over any field extension of a characteristic-three field is one. -/
theorem fieldExtension_cube_eq_one_iff (a : F) : a ^ 3 = 1 ↔ a = 1 := by
  let _ : CharP F 3 :=
    charP_of_injective_algebraMap (algebraMap k F).injective 3
  exact cube_eq_one_iff F a

include k in
/-- Every cube root of unity over a field extension of a characteristic-three field
is the identity. -/
theorem fieldExtension_root_eq_one (ζ : rootsOfUnity 3 F) : ζ = 1 := by
  apply rootsOfUnity.coe_injective
  change ((ζ : Fˣ) : F) = 1
  exact (fieldExtension_cube_eq_one_iff k F _).mp
    ((mem_rootsOfUnity' 3 (ζ : Fˣ)).mp ζ.property)

/-- Coordinate homomorphisms of μ₃ to a field extension are unique, in independent universes. -/
theorem fieldExtension_algHom_eq
    (φ ψ : rootsOfUnityCoordinateRing k 3 →ₐ[k] F) : φ = ψ := by
  let e : rootsOfUnity 3 F ≃ (rootsOfUnityCoordinateRing k 3 →ₐ[k] F) :=
    (rootsOfUnityMulEquivAlgHom k F 3).toEquiv.trans (WithConv.equiv _)
  apply e.symm.injective
  exact (fieldExtension_root_eq_one k F (e.symm φ)).trans
    (fieldExtension_root_eq_one k F (e.symm ψ)).symm

end FieldExtensions

/-- Every represented μ₃-point over a field extension is the identity.
The affine scheme objects are taken in a common universe. -/
theorem fieldExtension_point_eq_one
    (k F : Type u) [Field k] [CharP k 3] [Field F] [Algebra k F]
    (x : (Spec (.of F)).asOver (Spec (.of k)) ⟶ rootsOfUnityScheme k 3) : x = 1 := by
  apply (rootsOfUnityMulEquivPoints k F 3).symm.injective
  rw [map_one]
  exact fieldExtension_root_eq_one k F _

section SquareZero

variable (k : Type u) [CommRing k]

/-- The element `1 + inr 1` differs from one over a nontrivial base ring. -/
theorem one_add_inr_one_ne_one [Nontrivial k] :
    (1 + TrivSqZeroExt.inr (1 : k) : TrivSqZeroExt k k) ≠ 1 := by
  intro h
  have hs := congrArg TrivSqZeroExt.snd h
  exact (one_ne_zero : (1 : k) ≠ 0) (by
    simpa only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_one,
      TrivSqZeroExt.snd_inr, zero_add] using hs)

/-- The element `1 + inr 1` is a cube root of one in characteristic three. -/
theorem one_add_inr_one_cube [CharP k 3] :
    (1 + TrivSqZeroExt.inr (1 : k) : TrivSqZeroExt k k) ^ 3 = 1 := by
  let _ : CharP (TrivSqZeroExt k k) 3 :=
    charP_of_injective_algebraMap (R := k) (A := TrivSqZeroExt k k)
      TrivSqZeroExt.inl_injective 3
  have hε : (TrivSqZeroExt.inr (1 : k) : TrivSqZeroExt k k) ^ 3 = 0 := by
    rw [pow_succ, pow_two, TrivSqZeroExt.inr_mul_inr, zero_mul]
  rw [add_pow_char, one_pow, hε, add_zero]

variable [CharP k 3]

/-- The cube root of unity `1 + inr 1` in the square-zero extension. -/
def squareZeroRoot : rootsOfUnity 3 (TrivSqZeroExt k k) :=
  rootsOfUnity.mkOfPowEq (1 + TrivSqZeroExt.inr (1 : k)) (one_add_inr_one_cube k)

/-- The μ₃-point over the square-zero extension corresponding to `1 + inr 1`. -/
def squareZeroPoint :
    (Spec (.of (TrivSqZeroExt k k))).asOver (Spec (.of k)) ⟶ rootsOfUnityScheme k 3 :=
  rootsOfUnityMulEquivPoints k (TrivSqZeroExt k k) 3 (squareZeroRoot k)

/-- The underlying ring element of the square-zero cube root is `1 + inr 1`. -/
@[simp]
theorem squareZeroRoot_coe :
    ((squareZeroRoot k : (TrivSqZeroExt k k)ˣ) : TrivSqZeroExt k k) =
      1 + TrivSqZeroExt.inr (1 : k) :=
  rfl

/-- The square-zero cube root is nonidentity when the base ring is nontrivial. -/
theorem squareZeroRoot_ne_one [Nontrivial k] : squareZeroRoot k ≠ 1 := by
  intro h
  apply one_add_inr_one_ne_one k
  have hv := congrArg
    (fun ζ : rootsOfUnity 3 (TrivSqZeroExt k k) ↦ ((ζ : (TrivSqZeroExt k k)ˣ) :
      TrivSqZeroExt k k)) h
  simpa only [squareZeroRoot_coe, Subgroup.coe_one, Units.val_one] using hv

/-- The square-zero μ₃-point is nonidentity when the base ring is nontrivial. -/
theorem squareZeroPoint_ne_one [Nontrivial k] : squareZeroPoint k ≠ 1 := by
  intro h
  apply squareZeroRoot_ne_one k
  apply (rootsOfUnityMulEquivPoints k (TrivSqZeroExt k k) 3).injective
  simpa only [squareZeroPoint, map_one] using h

/-- The square-zero point sends the coordinate generator to `1 + inr 1`. -/
theorem squareZeroPoint_generator :
    (rootsOfUnityMulEquivAlgHom k (TrivSqZeroExt k k) 3 (squareZeroRoot k)).ofConv
      (rootsOfUnityCoordinateGenerator k 3) = 1 + TrivSqZeroExt.inr (1 : k) := by
  rw [rootsOfUnityMulEquivAlgHom_apply, rootsOfUnityMulEquivAlgHom_generator,
    squareZeroRoot_coe]

/-- The square-zero point is the spectrum map of its coordinate homomorphism. -/
@[simp]
theorem squareZeroPoint_left :
    (squareZeroPoint k).left =
      Spec.map (CommRingCat.ofHom
        (rootsOfUnityMulEquivAlgHom k (TrivSqZeroExt k k) 3
          (squareZeroRoot k)).ofConv.toRingHom) :=
  rfl

/-- The inverse point equivalence recovers the square-zero cube root. -/
@[simp]
theorem squareZeroPoint_root :
    (rootsOfUnityMulEquivPoints k (TrivSqZeroExt k k) 3).symm (squareZeroPoint k) =
      squareZeroRoot k :=
  (rootsOfUnityMulEquivPoints k (TrivSqZeroExt k k) 3).symm_apply_apply _

/-- The square-zero point agrees with the component of the representing isomorphism. -/
theorem squareZeroPoint_eq_pointsIso :
    squareZeroPoint k =
      (ConcreteCategory.hom ((rootsOfUnityPointsIso k 3).hom.app
          (CommAlgCat.of k (TrivSqZeroExt k k))) :
        rootsOfUnity 3 (TrivSqZeroExt k k) →*
          ((Spec (.of (TrivSqZeroExt k k))).asOver (Spec (.of k)) ⟶
            rootsOfUnityScheme k 3)) (squareZeroRoot k) :=
  rfl

/-- Polynomial classes evaluated at the square-zero point are evaluated at `1 + inr 1`. -/
theorem squareZeroPoint_eval (p : k[X]) :
    (rootsOfUnityMulEquivAlgHom k (TrivSqZeroExt k k) 3 (squareZeroRoot k)).ofConv
      ((rootsOfUnityCoordinateAlgEquiv k 3).symm
        (AdjoinRoot.mk (rootsOfUnityPolynomial k 3) p)) =
      aeval (1 + TrivSqZeroExt.inr (1 : k) : TrivSqZeroExt k k) p := by
  let ψ : AdjoinRoot (rootsOfUnityPolynomial k 3) →ₐ[k] TrivSqZeroExt k k :=
    (rootsOfUnityMulEquivAlgHom k (TrivSqZeroExt k k) 3 (squareZeroRoot k)).ofConv.comp
      (rootsOfUnityCoordinateAlgEquiv k 3).symm.toAlgHom
  change ψ (AdjoinRoot.mk (rootsOfUnityPolynomial k 3) p) = _
  rw [← AdjoinRoot.aeval_eq, ← Polynomial.aeval_algHom_apply]
  have hψ : ψ (AdjoinRoot.root (rootsOfUnityPolynomial k 3)) =
      1 + TrivSqZeroExt.inr (1 : k) := by
    change (rootsOfUnityMulEquivAlgHom k (TrivSqZeroExt k k) 3
      (squareZeroRoot k)).ofConv
        ((rootsOfUnityCoordinateAlgEquiv k 3).symm
          (AdjoinRoot.root (rootsOfUnityPolynomial k 3))) = _
    rw [rootsOfUnityCoordinateAlgEquiv_symm_root]
    exact squareZeroPoint_generator k
  rw [hψ]

end SquareZero

end AlgebraicGeometry.RootsOfUnityThree
