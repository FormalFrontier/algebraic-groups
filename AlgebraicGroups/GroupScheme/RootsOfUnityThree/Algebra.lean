/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.RootsOfUnity
public import AlgebraicGroups.GroupScheme.RootsOfUnityThree.Quadratic
public import Mathlib.RingTheory.Polynomial.Quotient
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Tactic.LinearCombination

/-!
# Coordinate algebra decompositions for the third roots of unity

Over a commutative ring in which 3 is invertible, the coordinate algebra of μ₃
is the product of the base and the quotient by `X² + X + 1`. If this quadratic
has a chosen root ζ in the base, the latter factor splits as well. The three
factors are ordered as `1, ζ, ζ²` and associated as `R × (R × R)`.

These are algebra decompositions, not decompositions as group objects. Over
fields they give the coordinate algebra calculations in Milne's *Algebraic
Groups*, Example 1.6. The constructions use the Chinese remainder theorem
and the existing coordinate presentation of the roots-of-unity group scheme.
-/

@[expose] public section

noncomputable section

open Polynomial

namespace AlgebraicGeometry.RootsOfUnityThree

universe u v

section CommRing

variable (R : Type u) [CommRing R]

local notation "q₃" => (X ^ 2 + X + 1 : R[X])
local notation "P₃" => AdjoinRoot (rootsOfUnityPolynomial R 3)
local notation "Q₃" => AdjoinRoot q₃

private lemma twoFactor_coprime (h3 : IsUnit (3 : R)) :
    IsCoprime (Ideal.span ({X - C (1 : R)} : Set R[X]))
      (Ideal.span ({q₃} : Set R[X])) := by
  apply Ideal.isCoprime_iff_sup_eq.mpr
  apply (Ideal.sup_eq_top_iff_isCoprime _ _).mpr
  refine ⟨-C (↑h3.unit⁻¹ : R) * (X + C 2), C (↑h3.unit⁻¹ : R), ?_⟩
  calc
    -C (↑h3.unit⁻¹ : R) * (X + C 2) * (X - C 1) +
        C (↑h3.unit⁻¹ : R) * q₃ = C (↑h3.unit⁻¹ : R) * C 3 := by
      simp only [map_ofNat, map_one]
      ring
    _ = 1 := by rw [← map_mul, h3.val_inv_mul, map_one]

private lemma twoFactor_ideal :
    Ideal.span ({rootsOfUnityPolynomial R 3} : Set R[X]) =
      Ideal.span ({X - C (1 : R)} : Set R[X]) * Ideal.span ({q₃} : Set R[X]) := by
  rw [Ideal.span_singleton_mul_span_singleton]
  apply congrArg (fun p : R[X] => Ideal.span ({p} : Set R[X]))
  simp only [rootsOfUnityPolynomial, map_one]
  ring

/-- The two-factor decomposition of `R[T]/(T³-1)` when 3 is a unit. -/
def twoFactorAlgEquiv (h3 : IsUnit (3 : R)) : P₃ ≃ₐ[R] R × Q₃ :=
  (Ideal.quotientEquivAlgOfEq R (by exact twoFactor_ideal R)).trans <|
    ({ Ideal.quotientMulEquivQuotientProd
        (Ideal.span ({X - C (1 : R)} : Set R[X]))
        (Ideal.span ({q₃} : Set R[X])) (by exact twoFactor_coprime R h3) with
      commutes' := fun r => by apply Prod.ext <;> rfl } :
      (R[X] ⧸ (Ideal.span ({X - C (1 : R)} : Set R[X]) *
        Ideal.span ({q₃} : Set R[X]))) ≃ₐ[R]
        AdjoinRoot (X - C (1 : R)) × Q₃).trans
      (AlgEquiv.prodCongr (Polynomial.quotientSpanXSubCAlgEquiv (1 : R))
        (AlgEquiv.refl : Q₃ ≃ₐ[R] Q₃))

@[simp]
lemma twoFactorAlgEquiv_mk (h3 : IsUnit (3 : R)) (p : R[X]) :
    twoFactorAlgEquiv R h3 (AdjoinRoot.mk _ p) =
      (p.eval 1, AdjoinRoot.mk q₃ p) := by
  apply Prod.ext <;> rfl

@[simp]
lemma twoFactorAlgEquiv_root (h3 : IsUnit (3 : R)) :
    twoFactorAlgEquiv R h3 (AdjoinRoot.root _) = (1, AdjoinRoot.root q₃) := by
  simpa only [AdjoinRoot.root, eval_X] using twoFactorAlgEquiv_mk R h3 X

@[simp]
lemma twoFactorAlgEquiv_algebraMap (h3 : IsUnit (3 : R)) (r : R) :
    twoFactorAlgEquiv R h3 (AdjoinRoot.of _ r) = (r, AdjoinRoot.of q₃ r) :=
  (twoFactorAlgEquiv R h3).commutes r

/-- Evaluation at the identity root of the cubic polynomial. -/
def evalOne : P₃ →ₐ[R] R :=
  AdjoinRoot.liftAlgHom _ (AlgHom.id R R) 1 (by simp [rootsOfUnityPolynomial])

@[simp]
lemma evalOne_mk (p : R[X]) : evalOne R (AdjoinRoot.mk _ p) = p.eval 1 := rfl

/-- The quotient map from the cubic quotient to its quadratic factor. -/
def quotientToQuadratic : P₃ →ₐ[R] Q₃ :=
  AdjoinRoot.algHomOfDvd R _ _ ⟨X - 1, by
    simp only [rootsOfUnityPolynomial]
    ring⟩

@[simp]
lemma quotientToQuadratic_mk (p : R[X]) :
    quotientToQuadratic R (AdjoinRoot.mk _ p) = AdjoinRoot.mk q₃ p := by
  rw [← AdjoinRoot.aeval_eq p, ← Polynomial.aeval_algHom_apply]
  simp only [quotientToQuadratic, AdjoinRoot.algHomOfDvd_root, AdjoinRoot.aeval_eq]

lemma twoFactorAlgEquiv_fst (h3 : IsUnit (3 : R)) :
    (AlgHom.fst R R Q₃).comp (twoFactorAlgEquiv R h3).toAlgHom = evalOne R := by
  ext
  simp [evalOne]

lemma twoFactorAlgEquiv_snd (h3 : IsUnit (3 : R)) :
    (AlgHom.snd R R Q₃).comp (twoFactorAlgEquiv R h3).toAlgHom =
      quotientToQuadratic R := by
  ext
  simp [quotientToQuadratic]

@[simp]
lemma twoFactorAlgEquiv_symm_mk (h3 : IsUnit (3 : R)) (p : R[X]) :
    (twoFactorAlgEquiv R h3).symm (p.eval 1, AdjoinRoot.mk q₃ p) = AdjoinRoot.mk _ p := by
  apply (twoFactorAlgEquiv R h3).injective
  simp

@[simp]
lemma twoFactorAlgEquiv_symm_root (h3 : IsUnit (3 : R)) :
    (twoFactorAlgEquiv R h3).symm (1, AdjoinRoot.root q₃) = AdjoinRoot.root _ := by
  apply (twoFactorAlgEquiv R h3).injective
  simp

@[simp]
lemma twoFactorAlgEquiv_symm_algebraMap (h3 : IsUnit (3 : R)) (r : R) :
    (twoFactorAlgEquiv R h3).symm (r, AdjoinRoot.of q₃ r) = AdjoinRoot.of _ r :=
  (twoFactorAlgEquiv R h3).symm.commutes r

/-- The two-factor decomposition of the existing coordinate algebra of μ₃. -/
def coordinateTwoFactorAlgEquiv (h3 : IsUnit (3 : R)) :
    rootsOfUnityCoordinateRing R 3 ≃ₐ[R] R × Q₃ :=
  (rootsOfUnityCoordinateAlgEquiv R 3).trans (twoFactorAlgEquiv R h3)

@[simp]
lemma coordinateTwoFactorAlgEquiv_mk (h3 : IsUnit (3 : R)) (p : R[X]) :
    coordinateTwoFactorAlgEquiv R h3
      ((rootsOfUnityCoordinateAlgEquiv R 3).symm (AdjoinRoot.mk _ p)) =
      (p.eval 1, AdjoinRoot.mk q₃ p) := by
  simp [coordinateTwoFactorAlgEquiv]

@[simp]
lemma coordinateTwoFactorAlgEquiv_generator (h3 : IsUnit (3 : R)) :
    coordinateTwoFactorAlgEquiv R h3 (rootsOfUnityCoordinateGenerator R 3) =
      (1, AdjoinRoot.root q₃) := by
  simp [coordinateTwoFactorAlgEquiv]

@[simp]
lemma coordinateTwoFactorAlgEquiv_algebraMap (h3 : IsUnit (3 : R)) (r : R) :
    coordinateTwoFactorAlgEquiv R h3 (AddMonoidAlgebra.single 0 r) =
      (r, AdjoinRoot.of q₃ r) :=
  (coordinateTwoFactorAlgEquiv R h3).commutes r

lemma coordinateTwoFactorAlgEquiv_fst (h3 : IsUnit (3 : R)) :
    (AlgHom.fst R R Q₃).comp (coordinateTwoFactorAlgEquiv R h3).toAlgHom =
      (evalOne R).comp (rootsOfUnityCoordinateAlgEquiv R 3).toAlgHom := by
  apply DFunLike.ext
  intro x
  exact DFunLike.congr_fun (twoFactorAlgEquiv_fst R h3)
    (rootsOfUnityCoordinateAlgEquiv R 3 x)

lemma coordinateTwoFactorAlgEquiv_snd (h3 : IsUnit (3 : R)) :
    (AlgHom.snd R R Q₃).comp (coordinateTwoFactorAlgEquiv R h3).toAlgHom =
      (quotientToQuadratic R).comp (rootsOfUnityCoordinateAlgEquiv R 3).toAlgHom := by
  apply DFunLike.ext
  intro x
  exact DFunLike.congr_fun (twoFactorAlgEquiv_snd R h3)
    (rootsOfUnityCoordinateAlgEquiv R 3 x)

@[simp]
lemma coordinateTwoFactorAlgEquiv_symm_mk (h3 : IsUnit (3 : R)) (p : R[X]) :
    (coordinateTwoFactorAlgEquiv R h3).symm (p.eval 1, AdjoinRoot.mk q₃ p) =
      (rootsOfUnityCoordinateAlgEquiv R 3).symm (AdjoinRoot.mk _ p) := by
  apply (coordinateTwoFactorAlgEquiv R h3).injective
  simp

@[simp]
lemma coordinateTwoFactorAlgEquiv_symm_generator (h3 : IsUnit (3 : R)) :
    (coordinateTwoFactorAlgEquiv R h3).symm (1, AdjoinRoot.root q₃) =
      rootsOfUnityCoordinateGenerator R 3 := by
  apply (coordinateTwoFactorAlgEquiv R h3).injective
  simp

@[simp]
lemma coordinateTwoFactorAlgEquiv_symm_algebraMap (h3 : IsUnit (3 : R)) (r : R) :
    (coordinateTwoFactorAlgEquiv R h3).symm (r, AdjoinRoot.of q₃ r) =
      AddMonoidAlgebra.single 0 r :=
  (coordinateTwoFactorAlgEquiv R h3).symm.commutes r

/-- A root of the quadratic factor is a cube root of one, over any base ring. -/
lemma quadraticRoot_cube (ζ : R) (hq : (q₃).eval ζ = 0) : ζ ^ 3 = 1 := by
  have h : ζ ^ 2 + ζ + 1 = 0 := by simpa using hq
  linear_combination (ζ - 1) * h

lemma quadraticRoot_sq_cube (ζ : R) (hq : (q₃).eval ζ = 0) : (ζ ^ 2) ^ 3 = 1 := by
  calc
    (ζ ^ 2) ^ 3 = (ζ ^ 3) ^ 2 := by ring
    _ = 1 := by rw [quadraticRoot_cube R ζ hq, one_pow]

lemma quadraticRoot_difference_mul (ζ : R) (hq : (q₃).eval ζ = 0) :
    (ζ - 1) * (ζ ^ 2 - 1) = 3 := by
  have h : ζ ^ 2 + ζ + 1 = 0 := by simpa using hq
  have hc := quadraticRoot_cube R ζ hq
  linear_combination hc - h

lemma isUnit_zeta_sub_one (h3 : IsUnit (3 : R)) (ζ : R) (hq : (q₃).eval ζ = 0) :
    IsUnit (ζ - 1) := by
  apply isUnit_of_mul_isUnit_left (y := ζ ^ 2 - 1)
  rwa [quadraticRoot_difference_mul R ζ hq]

lemma isUnit_zeta_sq_sub_one (h3 : IsUnit (3 : R)) (ζ : R) (hq : (q₃).eval ζ = 0) :
    IsUnit (ζ ^ 2 - 1) := by
  apply isUnit_of_mul_isUnit_right (x := ζ - 1)
  rwa [quadraticRoot_difference_mul R ζ hq]

lemma isUnit_zeta_sq_sub_zeta (h3 : IsUnit (3 : R)) (ζ : R) (hq : (q₃).eval ζ = 0) :
    IsUnit (ζ ^ 2 - ζ) := by
  have hζ : IsUnit ζ := .of_pow_eq_one (quadraticRoot_cube R ζ hq) (by decide : 3 ≠ 0)
  convert hζ.mul (isUnit_zeta_sub_one R h3 ζ hq) using 1; ring

lemma isUnit_one_sub_zeta (h3 : IsUnit (3 : R)) (ζ : R) (hq : (q₃).eval ζ = 0) :
    IsUnit (1 - ζ) := by
  simpa only [neg_sub] using (isUnit_zeta_sub_one R h3 ζ hq).neg

lemma isUnit_one_sub_zeta_sq (h3 : IsUnit (3 : R)) (ζ : R) (hq : (q₃).eval ζ = 0) :
    IsUnit (1 - ζ ^ 2) := by
  simpa only [neg_sub] using (isUnit_zeta_sq_sub_one R h3 ζ hq).neg

lemma isUnit_zeta_sub_zeta_sq (h3 : IsUnit (3 : R)) (ζ : R) (hq : (q₃).eval ζ = 0) :
    IsUnit (ζ - ζ ^ 2) := by
  simpa only [neg_sub] using (isUnit_zeta_sq_sub_zeta R h3 ζ hq).neg

private lemma quadratic_split_ideal (ζ : R) (hq : (q₃).eval ζ = 0) :
    Ideal.span ({q₃} : Set R[X]) =
      Ideal.span ({X - C ζ} : Set R[X]) * Ideal.span ({X - C (ζ ^ 2)} : Set R[X]) := by
  rw [Ideal.span_singleton_mul_span_singleton]
  apply congrArg (fun p : R[X] => Ideal.span ({p} : Set R[X]))
  have h : C ζ ^ 2 + C ζ + 1 = (0 : R[X]) := by
    simpa using congrArg (C : R →+* R[X]) (show ζ ^ 2 + ζ + 1 = 0 by simpa using hq)
  have hc : C ζ ^ 3 = (1 : R[X]) := by
    simpa using congrArg (C : R →+* R[X]) (quadraticRoot_cube R ζ hq)
  simp only [map_pow]
  linear_combination X * h - hc

private lemma quadratic_split_coprime (h3 : IsUnit (3 : R)) (ζ : R)
    (hq : (q₃).eval ζ = 0) :
    IsCoprime (Ideal.span ({X - C ζ} : Set R[X]))
      (Ideal.span ({X - C (ζ ^ 2)} : Set R[X])) := by
  apply Ideal.isCoprime_iff_sup_eq.mpr
  apply (Ideal.sup_eq_top_iff_isCoprime _ _).mpr
  exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub (isUnit_zeta_sub_zeta_sq R h3 ζ hq)

/-- The quadratic quotient split at a specified quadratic root, ordered `ζ, ζ²`. -/
def quadraticSplitAlgEquiv (h3 : IsUnit (3 : R)) (ζ : R)
    (hq : (q₃).eval ζ = 0) : Q₃ ≃ₐ[R] R × R :=
  (Ideal.quotientEquivAlgOfEq R (by exact quadratic_split_ideal R ζ hq)).trans <|
    ({ Ideal.quotientMulEquivQuotientProd
        (Ideal.span ({X - C ζ} : Set R[X]))
        (Ideal.span ({X - C (ζ ^ 2)} : Set R[X]))
        (by exact quadratic_split_coprime R h3 ζ hq) with
      commutes' := fun r => by apply Prod.ext <;> rfl } :
      (R[X] ⧸ (Ideal.span ({X - C ζ} : Set R[X]) *
        Ideal.span ({X - C (ζ ^ 2)} : Set R[X]))) ≃ₐ[R]
        AdjoinRoot (X - C ζ) × AdjoinRoot (X - C (ζ ^ 2))).trans
      (AlgEquiv.prodCongr (Polynomial.quotientSpanXSubCAlgEquiv ζ)
        (Polynomial.quotientSpanXSubCAlgEquiv (ζ ^ 2)))

@[simp]
lemma quadraticSplitAlgEquiv_mk (h3 : IsUnit (3 : R)) (ζ : R)
    (hq : (q₃).eval ζ = 0) (p : R[X]) :
    quadraticSplitAlgEquiv R h3 ζ hq (AdjoinRoot.mk q₃ p) =
      (p.eval ζ, p.eval (ζ ^ 2)) := by
  apply Prod.ext <;> rfl

/-- The ordered three-factor decomposition at a chosen root of `X²+X+1`.
No nontriviality or field hypothesis is needed. -/
def splitAlgEquivOfQuadraticRoot (h3 : IsUnit (3 : R)) (ζ : R) (hq : (q₃).eval ζ = 0) :
    P₃ ≃ₐ[R] R × (R × R) :=
  (twoFactorAlgEquiv R h3).trans
    (AlgEquiv.prodCongr (AlgEquiv.refl : R ≃ₐ[R] R) (quadraticSplitAlgEquiv R h3 ζ hq))

@[simp]
lemma splitAlgEquivOfQuadraticRoot_mk (h3 : IsUnit (3 : R)) (ζ : R)
    (hq : (q₃).eval ζ = 0) (p : R[X]) :
    splitAlgEquivOfQuadraticRoot R h3 ζ hq (AdjoinRoot.mk _ p) =
      (p.eval 1, (p.eval ζ, p.eval (ζ ^ 2))) := by
  simp [splitAlgEquivOfQuadraticRoot, quadraticSplitAlgEquiv_mk]

@[simp]
lemma splitAlgEquivOfQuadraticRoot_root (h3 : IsUnit (3 : R)) (ζ : R)
    (hq : (q₃).eval ζ = 0) :
    splitAlgEquivOfQuadraticRoot R h3 ζ hq (AdjoinRoot.root _) = (1, (ζ, ζ ^ 2)) := by
  simpa only [AdjoinRoot.root, eval_X] using splitAlgEquivOfQuadraticRoot_mk R h3 ζ hq X

@[simp]
lemma splitAlgEquivOfQuadraticRoot_algebraMap (h3 : IsUnit (3 : R)) (ζ : R)
    (hq : (q₃).eval ζ = 0) (r : R) :
    splitAlgEquivOfQuadraticRoot R h3 ζ hq (AdjoinRoot.of _ r) = (r, (r, r)) :=
  (splitAlgEquivOfQuadraticRoot R h3 ζ hq).commutes r

/-- Evaluation at a cube root, as a homomorphism from the cubic quotient. -/
def evalCubeRoot (a : R) (ha : a ^ 3 = 1) : P₃ →ₐ[R] R :=
  AdjoinRoot.liftAlgHom _ (AlgHom.id R R) a
    (by simpa [rootsOfUnityPolynomial] using sub_eq_zero.mpr ha)

@[simp]
lemma evalCubeRoot_mk (a : R) (ha : a ^ 3 = 1) (p : R[X]) :
    evalCubeRoot R a ha (AdjoinRoot.mk _ p) = p.eval a := rfl

lemma splitAlgEquivOfQuadraticRoot_fst (h3 : IsUnit (3 : R)) (ζ : R)
    (hq : (q₃).eval ζ = 0) :
    (AlgHom.fst R R (R × R)).comp (splitAlgEquivOfQuadraticRoot R h3 ζ hq).toAlgHom =
      evalOne R := by
  ext
  simp [evalOne]

lemma splitAlgEquivOfQuadraticRoot_snd_fst (h3 : IsUnit (3 : R)) (ζ : R)
    (hq : (q₃).eval ζ = 0) :
    ((AlgHom.fst R R R).comp (AlgHom.snd R R (R × R))).comp
      (splitAlgEquivOfQuadraticRoot R h3 ζ hq).toAlgHom =
        evalCubeRoot R ζ (quadraticRoot_cube R ζ hq) := by
  ext
  simp [evalCubeRoot]

lemma splitAlgEquivOfQuadraticRoot_snd_snd (h3 : IsUnit (3 : R)) (ζ : R)
    (hq : (q₃).eval ζ = 0) :
    ((AlgHom.snd R R R).comp (AlgHom.snd R R (R × R))).comp
      (splitAlgEquivOfQuadraticRoot R h3 ζ hq).toAlgHom =
        evalCubeRoot R (ζ ^ 2) (quadraticRoot_sq_cube R ζ hq) := by
  ext
  simp [evalCubeRoot]

/-- The Lagrange polynomial for the ordered root 1, using an inverse unit. -/
def lagrangeZeroPolynomial (h3 : IsUnit (3 : R)) (ζ : R) (hq : (q₃).eval ζ = 0) : R[X] :=
  C (↑((isUnit_one_sub_zeta R h3 ζ hq).mul
    (isUnit_one_sub_zeta_sq R h3 ζ hq)).unit⁻¹ : R) * (X - C ζ) * (X - C (ζ ^ 2))

/-- The Lagrange polynomial for the ordered root ζ, using an inverse unit. -/
def lagrangeOnePolynomial (h3 : IsUnit (3 : R)) (ζ : R) (hq : (q₃).eval ζ = 0) : R[X] :=
  C (↑((isUnit_zeta_sub_one R h3 ζ hq).mul
    (isUnit_zeta_sub_zeta_sq R h3 ζ hq)).unit⁻¹ : R) * (X - 1) * (X - C (ζ ^ 2))

/-- The Lagrange polynomial for the ordered root ζ², using an inverse unit. -/
def lagrangeTwoPolynomial (h3 : IsUnit (3 : R)) (ζ : R) (hq : (q₃).eval ζ = 0) : R[X] :=
  C (↑((isUnit_zeta_sq_sub_one R h3 ζ hq).mul
    (isUnit_zeta_sq_sub_zeta R h3 ζ hq)).unit⁻¹ : R) * (X - 1) * (X - C ζ)

@[simp]
lemma lagrangeZeroPolynomial_eval (h3 : IsUnit (3 : R)) (ζ : R) (hq : (q₃).eval ζ = 0) :
    (lagrangeZeroPolynomial R h3 ζ hq).eval 1 = 1 ∧
      (lagrangeZeroPolynomial R h3 ζ hq).eval ζ = 0 ∧
      (lagrangeZeroPolynomial R h3 ζ hq).eval (ζ ^ 2) = 0 := by
  simp [lagrangeZeroPolynomial, mul_assoc]

@[simp]
lemma lagrangeOnePolynomial_eval (h3 : IsUnit (3 : R)) (ζ : R) (hq : (q₃).eval ζ = 0) :
    (lagrangeOnePolynomial R h3 ζ hq).eval 1 = 0 ∧
      (lagrangeOnePolynomial R h3 ζ hq).eval ζ = 1 ∧
      (lagrangeOnePolynomial R h3 ζ hq).eval (ζ ^ 2) = 0 := by
  simp [lagrangeOnePolynomial, mul_assoc]

@[simp]
lemma lagrangeTwoPolynomial_eval (h3 : IsUnit (3 : R)) (ζ : R) (hq : (q₃).eval ζ = 0) :
    (lagrangeTwoPolynomial R h3 ζ hq).eval 1 = 0 ∧
      (lagrangeTwoPolynomial R h3 ζ hq).eval ζ = 0 ∧
      (lagrangeTwoPolynomial R h3 ζ hq).eval (ζ ^ 2) = 1 := by
  simp [lagrangeTwoPolynomial, mul_assoc]

lemma splitAlgEquivOfQuadraticRoot_lagrangeZero (h3 : IsUnit (3 : R)) (ζ : R)
    (hq : (q₃).eval ζ = 0) :
    splitAlgEquivOfQuadraticRoot R h3 ζ hq
      (AdjoinRoot.mk _ (lagrangeZeroPolynomial R h3 ζ hq)) = (1, (0, 0)) := by
  rw [splitAlgEquivOfQuadraticRoot_mk]
  obtain ⟨h0, h1, h2⟩ := lagrangeZeroPolynomial_eval R h3 ζ hq
  rw [h0, h1, h2]

lemma splitAlgEquivOfQuadraticRoot_lagrangeOne (h3 : IsUnit (3 : R)) (ζ : R)
    (hq : (q₃).eval ζ = 0) :
    splitAlgEquivOfQuadraticRoot R h3 ζ hq
      (AdjoinRoot.mk _ (lagrangeOnePolynomial R h3 ζ hq)) = (0, (1, 0)) := by
  rw [splitAlgEquivOfQuadraticRoot_mk]
  obtain ⟨h0, h1, h2⟩ := lagrangeOnePolynomial_eval R h3 ζ hq
  rw [h0, h1, h2]

lemma splitAlgEquivOfQuadraticRoot_lagrangeTwo (h3 : IsUnit (3 : R)) (ζ : R)
    (hq : (q₃).eval ζ = 0) :
    splitAlgEquivOfQuadraticRoot R h3 ζ hq
      (AdjoinRoot.mk _ (lagrangeTwoPolynomial R h3 ζ hq)) = (0, (0, 1)) := by
  rw [splitAlgEquivOfQuadraticRoot_mk]
  obtain ⟨h0, h1, h2⟩ := lagrangeTwoPolynomial_eval R h3 ζ hq
  rw [h0, h1, h2]

@[simp]
lemma splitAlgEquivOfQuadraticRoot_symm_idempotentZero (h3 : IsUnit (3 : R)) (ζ : R)
    (hq : (q₃).eval ζ = 0) :
    (splitAlgEquivOfQuadraticRoot R h3 ζ hq).symm (1, (0, 0)) =
      AdjoinRoot.mk _ (lagrangeZeroPolynomial R h3 ζ hq) := by
  apply (splitAlgEquivOfQuadraticRoot R h3 ζ hq).injective
  simp

@[simp]
lemma splitAlgEquivOfQuadraticRoot_symm_idempotentOne (h3 : IsUnit (3 : R)) (ζ : R)
    (hq : (q₃).eval ζ = 0) :
    (splitAlgEquivOfQuadraticRoot R h3 ζ hq).symm (0, (1, 0)) =
      AdjoinRoot.mk _ (lagrangeOnePolynomial R h3 ζ hq) := by
  apply (splitAlgEquivOfQuadraticRoot R h3 ζ hq).injective
  simp

@[simp]
lemma splitAlgEquivOfQuadraticRoot_symm_idempotentTwo (h3 : IsUnit (3 : R)) (ζ : R)
    (hq : (q₃).eval ζ = 0) :
    (splitAlgEquivOfQuadraticRoot R h3 ζ hq).symm (0, (0, 1)) =
      AdjoinRoot.mk _ (lagrangeTwoPolynomial R h3 ζ hq) := by
  apply (splitAlgEquivOfQuadraticRoot R h3 ζ hq).injective
  simp

/-- The inverse of the ordered evaluation map is unit-valued Lagrange interpolation. -/
lemma splitAlgEquivOfQuadraticRoot_symm_apply (h3 : IsUnit (3 : R)) (ζ : R)
    (hq : (q₃).eval ζ = 0) (a b c : R) :
    (splitAlgEquivOfQuadraticRoot R h3 ζ hq).symm (a, (b, c)) =
      algebraMap R P₃ a * AdjoinRoot.mk _ (lagrangeZeroPolynomial R h3 ζ hq) +
      algebraMap R P₃ b * AdjoinRoot.mk _ (lagrangeOnePolynomial R h3 ζ hq) +
      algebraMap R P₃ c * AdjoinRoot.mk _ (lagrangeTwoPolynomial R h3 ζ hq) := by
  apply (splitAlgEquivOfQuadraticRoot R h3 ζ hq).injective
  simp only [AlgEquiv.apply_symm_apply, map_add, map_mul,
    splitAlgEquivOfQuadraticRoot_lagrangeZero,
    splitAlgEquivOfQuadraticRoot_lagrangeOne, splitAlgEquivOfQuadraticRoot_lagrangeTwo]
  ext <;> simp

@[simp]
lemma splitAlgEquivOfQuadraticRoot_symm_mk (h3 : IsUnit (3 : R)) (ζ : R)
    (hq : (q₃).eval ζ = 0) (p : R[X]) :
    (splitAlgEquivOfQuadraticRoot R h3 ζ hq).symm
      (p.eval 1, (p.eval ζ, p.eval (ζ ^ 2))) = AdjoinRoot.mk _ p := by
  apply (splitAlgEquivOfQuadraticRoot R h3 ζ hq).injective
  simp

@[simp]
lemma splitAlgEquivOfQuadraticRoot_symm_root (h3 : IsUnit (3 : R)) (ζ : R)
    (hq : (q₃).eval ζ = 0) :
    (splitAlgEquivOfQuadraticRoot R h3 ζ hq).symm (1, (ζ, ζ ^ 2)) = AdjoinRoot.root _ := by
  apply (splitAlgEquivOfQuadraticRoot R h3 ζ hq).injective
  simp

@[simp]
lemma splitAlgEquivOfQuadraticRoot_symm_algebraMap (h3 : IsUnit (3 : R)) (ζ : R)
    (hq : (q₃).eval ζ = 0) (r : R) :
    (splitAlgEquivOfQuadraticRoot R h3 ζ hq).symm (r, (r, r)) = algebraMap R P₃ r :=
  (splitAlgEquivOfQuadraticRoot R h3 ζ hq).symm.commutes r

/-- The ordered split decomposition of the existing coordinate algebra of μ₃. -/
def coordinateSplitAlgEquivOfQuadraticRoot (h3 : IsUnit (3 : R)) (ζ : R)
    (hq : (q₃).eval ζ = 0) : rootsOfUnityCoordinateRing R 3 ≃ₐ[R] R × (R × R) :=
  (rootsOfUnityCoordinateAlgEquiv R 3).trans (splitAlgEquivOfQuadraticRoot R h3 ζ hq)

@[simp]
lemma coordinateSplitAlgEquivOfQuadraticRoot_mk (h3 : IsUnit (3 : R)) (ζ : R)
    (hq : (q₃).eval ζ = 0) (p : R[X]) :
    coordinateSplitAlgEquivOfQuadraticRoot R h3 ζ hq
      ((rootsOfUnityCoordinateAlgEquiv R 3).symm (AdjoinRoot.mk _ p)) =
      (p.eval 1, (p.eval ζ, p.eval (ζ ^ 2))) := by
  simp [coordinateSplitAlgEquivOfQuadraticRoot]

@[simp]
lemma coordinateSplitAlgEquivOfQuadraticRoot_generator (h3 : IsUnit (3 : R)) (ζ : R)
    (hq : (q₃).eval ζ = 0) :
    coordinateSplitAlgEquivOfQuadraticRoot R h3 ζ hq (rootsOfUnityCoordinateGenerator R 3) =
      (1, (ζ, ζ ^ 2)) := by
  simp [coordinateSplitAlgEquivOfQuadraticRoot]

@[simp]
lemma coordinateSplitAlgEquivOfQuadraticRoot_algebraMap (h3 : IsUnit (3 : R)) (ζ : R)
    (hq : (q₃).eval ζ = 0) (r : R) :
    coordinateSplitAlgEquivOfQuadraticRoot R h3 ζ hq
      (AddMonoidAlgebra.single 0 r) = (r, (r, r)) :=
  (coordinateSplitAlgEquivOfQuadraticRoot R h3 ζ hq).commutes r

lemma coordinateSplitAlgEquivOfQuadraticRoot_fst (h3 : IsUnit (3 : R)) (ζ : R)
    (hq : (q₃).eval ζ = 0) :
    (AlgHom.fst R R (R × R)).comp
      (coordinateSplitAlgEquivOfQuadraticRoot R h3 ζ hq).toAlgHom =
        (evalOne R).comp (rootsOfUnityCoordinateAlgEquiv R 3).toAlgHom := by
  apply DFunLike.ext
  intro x
  exact DFunLike.congr_fun (splitAlgEquivOfQuadraticRoot_fst R h3 ζ hq)
    (rootsOfUnityCoordinateAlgEquiv R 3 x)

lemma coordinateSplitAlgEquivOfQuadraticRoot_snd_fst (h3 : IsUnit (3 : R)) (ζ : R)
    (hq : (q₃).eval ζ = 0) :
    ((AlgHom.fst R R R).comp (AlgHom.snd R R (R × R))).comp
      (coordinateSplitAlgEquivOfQuadraticRoot R h3 ζ hq).toAlgHom =
        (evalCubeRoot R ζ (quadraticRoot_cube R ζ hq)).comp
          (rootsOfUnityCoordinateAlgEquiv R 3).toAlgHom := by
  apply DFunLike.ext
  intro x
  exact DFunLike.congr_fun (splitAlgEquivOfQuadraticRoot_snd_fst R h3 ζ hq)
    (rootsOfUnityCoordinateAlgEquiv R 3 x)

lemma coordinateSplitAlgEquivOfQuadraticRoot_snd_snd (h3 : IsUnit (3 : R)) (ζ : R)
    (hq : (q₃).eval ζ = 0) :
    ((AlgHom.snd R R R).comp (AlgHom.snd R R (R × R))).comp
      (coordinateSplitAlgEquivOfQuadraticRoot R h3 ζ hq).toAlgHom =
        (evalCubeRoot R (ζ ^ 2) (quadraticRoot_sq_cube R ζ hq)).comp
            (rootsOfUnityCoordinateAlgEquiv R 3).toAlgHom := by
  apply DFunLike.ext
  intro x
  exact DFunLike.congr_fun (splitAlgEquivOfQuadraticRoot_snd_snd R h3 ζ hq)
    (rootsOfUnityCoordinateAlgEquiv R 3 x)

@[simp]
lemma coordinateSplitAlgEquivOfQuadraticRoot_symm_mk (h3 : IsUnit (3 : R)) (ζ : R)
    (hq : (q₃).eval ζ = 0) (p : R[X]) :
    (coordinateSplitAlgEquivOfQuadraticRoot R h3 ζ hq).symm
      (p.eval 1, (p.eval ζ, p.eval (ζ ^ 2))) =
        (rootsOfUnityCoordinateAlgEquiv R 3).symm (AdjoinRoot.mk _ p) := by
  apply (coordinateSplitAlgEquivOfQuadraticRoot R h3 ζ hq).injective
  simp

@[simp]
lemma coordinateSplitAlgEquivOfQuadraticRoot_symm_generator (h3 : IsUnit (3 : R)) (ζ : R)
    (hq : (q₃).eval ζ = 0) :
    (coordinateSplitAlgEquivOfQuadraticRoot R h3 ζ hq).symm (1, (ζ, ζ ^ 2)) =
      rootsOfUnityCoordinateGenerator R 3 := by
  apply (coordinateSplitAlgEquivOfQuadraticRoot R h3 ζ hq).injective
  simp

@[simp]
lemma coordinateSplitAlgEquivOfQuadraticRoot_symm_algebraMap (h3 : IsUnit (3 : R)) (ζ : R)
    (hq : (q₃).eval ζ = 0) (r : R) :
    (coordinateSplitAlgEquivOfQuadraticRoot R h3 ζ hq).symm (r, (r, r)) =
      algebraMap R (rootsOfUnityCoordinateRing R 3) r :=
  (coordinateSplitAlgEquivOfQuadraticRoot R h3 ζ hq).symm.commutes r

lemma coordinateSplitAlgEquivOfQuadraticRoot_symm_apply (h3 : IsUnit (3 : R)) (ζ : R)
    (hq : (q₃).eval ζ = 0) (a b c : R) :
    (coordinateSplitAlgEquivOfQuadraticRoot R h3 ζ hq).symm (a, (b, c)) =
      (rootsOfUnityCoordinateAlgEquiv R 3).symm
        (algebraMap R P₃ a * AdjoinRoot.mk _ (lagrangeZeroPolynomial R h3 ζ hq) +
        algebraMap R P₃ b * AdjoinRoot.mk _ (lagrangeOnePolynomial R h3 ζ hq) +
        algebraMap R P₃ c * AdjoinRoot.mk _ (lagrangeTwoPolynomial R h3 ζ hq)) := by
  exact congrArg (rootsOfUnityCoordinateAlgEquiv R 3).symm
    (splitAlgEquivOfQuadraticRoot_symm_apply R h3 ζ hq a b c)

end CommRing

section Field

variable (k : Type u) [Field k]

/-- Over a field, a primitive cube root is a root of the quadratic factor. -/
lemma primitiveRoot_quadratic_eval (ζ : k) (hζ : IsPrimitiveRoot ζ 3) :
    (X ^ 2 + X + 1 : k[X]).eval ζ = 0 := by
  have h : (ζ - 1) * (ζ ^ 2 + ζ + 1) = 0 := by
    calc
      _ = ζ ^ 3 - 1 := by ring
      _ = 0 := sub_eq_zero.mpr hζ.pow_eq_one
  have hq := (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr (hζ.ne_one (by decide)))
  simpa using hq

/-- A primitive cube root in a field forces 3 to be invertible. -/
lemma primitiveRoot_three_isUnit (ζ : k) (hζ : IsPrimitiveRoot ζ 3) : IsUnit (3 : k) := by
  rw [← quadraticRoot_difference_mul k ζ (primitiveRoot_quadratic_eval k ζ hζ)]
  exact (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (hζ.ne_one (by decide)))).mul
    (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr
      (hζ.pow_ne_one_of_pos_of_lt (by decide : 2 ≠ 0) (by decide : 2 < 3))))

/-- The ordered split cubic quotient over a field with a primitive cube root.
There is no independent characteristic hypothesis. -/
def splitAlgEquiv (ζ : k) (hζ : IsPrimitiveRoot ζ 3) :
    AdjoinRoot (rootsOfUnityPolynomial k 3) ≃ₐ[k] k × (k × k) :=
  splitAlgEquivOfQuadraticRoot k (primitiveRoot_three_isUnit k ζ hζ) ζ
    (primitiveRoot_quadratic_eval k ζ hζ)

@[simp]
lemma splitAlgEquiv_mk (ζ : k) (hζ : IsPrimitiveRoot ζ 3) (p : k[X]) :
    splitAlgEquiv k ζ hζ (AdjoinRoot.mk _ p) =
      (p.eval 1, (p.eval ζ, p.eval (ζ ^ 2))) := by
  simp [splitAlgEquiv]

@[simp]
lemma splitAlgEquiv_root (ζ : k) (hζ : IsPrimitiveRoot ζ 3) :
    splitAlgEquiv k ζ hζ (AdjoinRoot.root _) = (1, (ζ, ζ ^ 2)) := by
  simp [splitAlgEquiv]

@[simp]
lemma splitAlgEquiv_algebraMap (ζ : k) (hζ : IsPrimitiveRoot ζ 3) (a : k) :
    splitAlgEquiv k ζ hζ (AdjoinRoot.of _ a) = (a, (a, a)) :=
  (splitAlgEquiv k ζ hζ).commutes a

lemma splitAlgEquiv_fst (ζ : k) (hζ : IsPrimitiveRoot ζ 3) :
    (AlgHom.fst k k (k × k)).comp (splitAlgEquiv k ζ hζ).toAlgHom = evalOne k :=
  splitAlgEquivOfQuadraticRoot_fst k (primitiveRoot_three_isUnit k ζ hζ) ζ
    (primitiveRoot_quadratic_eval k ζ hζ)

lemma splitAlgEquiv_snd_fst (ζ : k) (hζ : IsPrimitiveRoot ζ 3) :
    ((AlgHom.fst k k k).comp (AlgHom.snd k k (k × k))).comp
      (splitAlgEquiv k ζ hζ).toAlgHom = evalCubeRoot k ζ hζ.pow_eq_one :=
  splitAlgEquivOfQuadraticRoot_snd_fst k (primitiveRoot_three_isUnit k ζ hζ) ζ
    (primitiveRoot_quadratic_eval k ζ hζ)

lemma splitAlgEquiv_snd_snd (ζ : k) (hζ : IsPrimitiveRoot ζ 3) :
    ((AlgHom.snd k k k).comp (AlgHom.snd k k (k × k))).comp
      (splitAlgEquiv k ζ hζ).toAlgHom =
        evalCubeRoot k (ζ ^ 2)
          (quadraticRoot_sq_cube k ζ (primitiveRoot_quadratic_eval k ζ hζ)) :=
  splitAlgEquivOfQuadraticRoot_snd_snd k (primitiveRoot_three_isUnit k ζ hζ) ζ
    (primitiveRoot_quadratic_eval k ζ hζ)

@[simp]
lemma splitAlgEquiv_symm_root (ζ : k) (hζ : IsPrimitiveRoot ζ 3) :
    (splitAlgEquiv k ζ hζ).symm (1, (ζ, ζ ^ 2)) = AdjoinRoot.root _ := by
  apply (splitAlgEquiv k ζ hζ).injective
  simp

@[simp]
lemma splitAlgEquiv_symm_algebraMap (ζ : k) (hζ : IsPrimitiveRoot ζ 3) (a : k) :
    (splitAlgEquiv k ζ hζ).symm (a, (a, a)) = algebraMap k _ a :=
  (splitAlgEquiv k ζ hζ).symm.commutes a

lemma splitAlgEquiv_symm_apply (ζ : k) (hζ : IsPrimitiveRoot ζ 3) (a b c : k) :
    (splitAlgEquiv k ζ hζ).symm (a, (b, c)) =
      algebraMap k _ a * AdjoinRoot.mk _ (lagrangeZeroPolynomial k
        (primitiveRoot_three_isUnit k ζ hζ) ζ (primitiveRoot_quadratic_eval k ζ hζ)) +
      algebraMap k _ b * AdjoinRoot.mk _ (lagrangeOnePolynomial k
        (primitiveRoot_three_isUnit k ζ hζ) ζ (primitiveRoot_quadratic_eval k ζ hζ)) +
      algebraMap k _ c * AdjoinRoot.mk _ (lagrangeTwoPolynomial k
        (primitiveRoot_three_isUnit k ζ hζ) ζ (primitiveRoot_quadratic_eval k ζ hζ)) :=
  splitAlgEquivOfQuadraticRoot_symm_apply k (primitiveRoot_three_isUnit k ζ hζ) ζ
    (primitiveRoot_quadratic_eval k ζ hζ) a b c

/-- The ordered split coordinate algebra over a field with a primitive cube root. -/
def coordinateSplitAlgEquiv (ζ : k) (hζ : IsPrimitiveRoot ζ 3) :
    rootsOfUnityCoordinateRing k 3 ≃ₐ[k] k × (k × k) :=
  coordinateSplitAlgEquivOfQuadraticRoot k (primitiveRoot_three_isUnit k ζ hζ) ζ
    (primitiveRoot_quadratic_eval k ζ hζ)

@[simp]
lemma coordinateSplitAlgEquiv_mk (ζ : k) (hζ : IsPrimitiveRoot ζ 3) (p : k[X]) :
    coordinateSplitAlgEquiv k ζ hζ
      ((rootsOfUnityCoordinateAlgEquiv k 3).symm (AdjoinRoot.mk _ p)) =
      (p.eval 1, (p.eval ζ, p.eval (ζ ^ 2))) := by
  simp [coordinateSplitAlgEquiv]

@[simp]
lemma coordinateSplitAlgEquiv_generator (ζ : k) (hζ : IsPrimitiveRoot ζ 3) :
    coordinateSplitAlgEquiv k ζ hζ (rootsOfUnityCoordinateGenerator k 3) =
      (1, (ζ, ζ ^ 2)) := by
  simp [coordinateSplitAlgEquiv]

@[simp]
lemma coordinateSplitAlgEquiv_algebraMap (ζ : k) (hζ : IsPrimitiveRoot ζ 3) (a : k) :
    coordinateSplitAlgEquiv k ζ hζ (AddMonoidAlgebra.single 0 a) = (a, (a, a)) :=
  (coordinateSplitAlgEquiv k ζ hζ).commutes a

lemma coordinateSplitAlgEquiv_fst (ζ : k) (hζ : IsPrimitiveRoot ζ 3) :
    (AlgHom.fst k k (k × k)).comp (coordinateSplitAlgEquiv k ζ hζ).toAlgHom =
      (evalOne k).comp (rootsOfUnityCoordinateAlgEquiv k 3).toAlgHom :=
  coordinateSplitAlgEquivOfQuadraticRoot_fst k (primitiveRoot_three_isUnit k ζ hζ) ζ
    (primitiveRoot_quadratic_eval k ζ hζ)

lemma coordinateSplitAlgEquiv_snd_fst (ζ : k) (hζ : IsPrimitiveRoot ζ 3) :
    ((AlgHom.fst k k k).comp (AlgHom.snd k k (k × k))).comp
      (coordinateSplitAlgEquiv k ζ hζ).toAlgHom =
        (evalCubeRoot k ζ hζ.pow_eq_one).comp (rootsOfUnityCoordinateAlgEquiv k 3).toAlgHom :=
  coordinateSplitAlgEquivOfQuadraticRoot_snd_fst k (primitiveRoot_three_isUnit k ζ hζ) ζ
    (primitiveRoot_quadratic_eval k ζ hζ)

lemma coordinateSplitAlgEquiv_snd_snd (ζ : k) (hζ : IsPrimitiveRoot ζ 3) :
    ((AlgHom.snd k k k).comp (AlgHom.snd k k (k × k))).comp
      (coordinateSplitAlgEquiv k ζ hζ).toAlgHom =
        (evalCubeRoot k (ζ ^ 2)
          (quadraticRoot_sq_cube k ζ (primitiveRoot_quadratic_eval k ζ hζ))).comp
            (rootsOfUnityCoordinateAlgEquiv k 3).toAlgHom :=
  coordinateSplitAlgEquivOfQuadraticRoot_snd_snd k (primitiveRoot_three_isUnit k ζ hζ) ζ
    (primitiveRoot_quadratic_eval k ζ hζ)

@[simp]
lemma coordinateSplitAlgEquiv_symm_generator (ζ : k) (hζ : IsPrimitiveRoot ζ 3) :
    (coordinateSplitAlgEquiv k ζ hζ).symm (1, (ζ, ζ ^ 2)) =
      rootsOfUnityCoordinateGenerator k 3 := by
  apply (coordinateSplitAlgEquiv k ζ hζ).injective
  simp

@[simp]
lemma coordinateSplitAlgEquiv_symm_algebraMap (ζ : k) (hζ : IsPrimitiveRoot ζ 3) (a : k) :
    (coordinateSplitAlgEquiv k ζ hζ).symm (a, (a, a)) =
      algebraMap k (rootsOfUnityCoordinateRing k 3) a :=
  (coordinateSplitAlgEquiv k ζ hζ).symm.commutes a

/-- An algebraically closed field with `3 ≠ 0` contains a primitive cube root. -/
lemma exists_primitiveCubeRoot [IsAlgClosed k] (h3 : (3 : k) ≠ 0) :
    ∃ ζ : k, IsPrimitiveRoot ζ 3 := by
  let _ : NeZero (3 : k) := ⟨h3⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot k 3

/-- A chosen primitive cube root for the algebraically closed field specialization. -/
def algebraicallyClosedCubeRoot [IsAlgClosed k] (h3 : (3 : k) ≠ 0) : k :=
  Classical.choose (exists_primitiveCubeRoot k h3)

lemma algebraicallyClosedCubeRoot_isPrimitive [IsAlgClosed k] (h3 : (3 : k) ≠ 0) :
    IsPrimitiveRoot (algebraicallyClosedCubeRoot k h3) 3 :=
  Classical.choose_spec (exists_primitiveCubeRoot k h3)

/-- The cubic quotient over an algebraically closed field of characteristic not three. -/
def splitAlgEquivOfIsAlgClosed [IsAlgClosed k] (h3 : (3 : k) ≠ 0) :
    AdjoinRoot (rootsOfUnityPolynomial k 3) ≃ₐ[k] k × (k × k) :=
  splitAlgEquiv k (algebraicallyClosedCubeRoot k h3)
    (algebraicallyClosedCubeRoot_isPrimitive k h3)

@[simp]
lemma splitAlgEquivOfIsAlgClosed_mk [IsAlgClosed k] (h3 : (3 : k) ≠ 0) (p : k[X]) :
    splitAlgEquivOfIsAlgClosed k h3 (AdjoinRoot.mk _ p) =
      (p.eval 1, (p.eval (algebraicallyClosedCubeRoot k h3),
        p.eval (algebraicallyClosedCubeRoot k h3 ^ 2))) := by
  simp [splitAlgEquivOfIsAlgClosed]

@[simp]
lemma splitAlgEquivOfIsAlgClosed_root [IsAlgClosed k] (h3 : (3 : k) ≠ 0) :
    splitAlgEquivOfIsAlgClosed k h3 (AdjoinRoot.root _) =
      (1, (algebraicallyClosedCubeRoot k h3, algebraicallyClosedCubeRoot k h3 ^ 2)) := by
  simp [splitAlgEquivOfIsAlgClosed]

@[simp]
lemma splitAlgEquivOfIsAlgClosed_algebraMap [IsAlgClosed k] (h3 : (3 : k) ≠ 0) (a : k) :
    splitAlgEquivOfIsAlgClosed k h3 (AdjoinRoot.of _ a) = (a, (a, a)) :=
  (splitAlgEquivOfIsAlgClosed k h3).commutes a

/-- The split coordinate algebra over an algebraically closed field of characteristic not three.
The evaluations retain the chosen primitive cube root. -/
def coordinateSplitAlgEquivOfIsAlgClosed [IsAlgClosed k] (h3 : (3 : k) ≠ 0) :
    rootsOfUnityCoordinateRing k 3 ≃ₐ[k] k × (k × k) :=
  coordinateSplitAlgEquiv k (algebraicallyClosedCubeRoot k h3)
    (algebraicallyClosedCubeRoot_isPrimitive k h3)

@[simp]
lemma coordinateSplitAlgEquivOfIsAlgClosed_mk [IsAlgClosed k] (h3 : (3 : k) ≠ 0) (p : k[X]) :
    coordinateSplitAlgEquivOfIsAlgClosed k h3
      ((rootsOfUnityCoordinateAlgEquiv k 3).symm (AdjoinRoot.mk _ p)) =
      (p.eval 1, (p.eval (algebraicallyClosedCubeRoot k h3),
        p.eval (algebraicallyClosedCubeRoot k h3 ^ 2))) := by
  simp [coordinateSplitAlgEquivOfIsAlgClosed]

@[simp]
lemma coordinateSplitAlgEquivOfIsAlgClosed_generator [IsAlgClosed k] (h3 : (3 : k) ≠ 0) :
    coordinateSplitAlgEquivOfIsAlgClosed k h3 (rootsOfUnityCoordinateGenerator k 3) =
      (1, (algebraicallyClosedCubeRoot k h3, algebraicallyClosedCubeRoot k h3 ^ 2)) := by
  simp [coordinateSplitAlgEquivOfIsAlgClosed]

@[simp]
lemma coordinateSplitAlgEquivOfIsAlgClosed_algebraMap [IsAlgClosed k] (h3 : (3 : k) ≠ 0) (a : k) :
    coordinateSplitAlgEquivOfIsAlgClosed k h3 (AddMonoidAlgebra.single 0 a) = (a, (a, a)) :=
  (coordinateSplitAlgEquivOfIsAlgClosed k h3).commutes a

section AdjoinAlgebra

variable (L : Type v) [CommRing L] [IsDomain L] [Algebra k L]

private lemma chosenRoot_three_isUnit (ζ : L) (hζ : IsPrimitiveRoot ζ 3) :
    IsUnit (3 : k) := by
  let _ : NeZero (3 : L) := hζ.neZero'
  apply isUnit_iff_ne_zero.mpr
  intro h
  apply NeZero.ne (3 : L)
  simpa only [map_ofNat, map_zero] using congrArg (algebraMap k L) h

/-- The coordinate decomposition with exactly the subalgebra generated by the
chosen primitive root as its second factor. -/
def coordinateAdjoinAlgEquiv (hnosplit : ¬ ∃ a : k, IsPrimitiveRoot a 3)
    (ζ : L) (hζ : IsPrimitiveRoot ζ 3) :
    rootsOfUnityCoordinateRing k 3 ≃ₐ[k] k × Algebra.adjoin k ({ζ} : Set L) :=
  (coordinateTwoFactorAlgEquiv k (by exact chosenRoot_three_isUnit k L ζ hζ)).trans
    (AlgEquiv.prodCongr (AlgEquiv.refl : k ≃ₐ[k] k)
      (quadraticAlgEquivAdjoin hnosplit ζ hζ))

/-- The chosen-subalgebra component evaluates at precisely the chosen root. -/
lemma coordinateAdjoinAlgEquiv_generator (hnosplit : ¬ ∃ a : k, IsPrimitiveRoot a 3)
    (ζ : L) (hζ : IsPrimitiveRoot ζ 3) :
    coordinateAdjoinAlgEquiv k L hnosplit ζ hζ (rootsOfUnityCoordinateGenerator k 3) =
      (1, ⟨ζ, Algebra.self_mem_adjoin_singleton k ζ⟩) := by
  simp [coordinateAdjoinAlgEquiv, AlgEquiv.prodCongr_apply]

lemma coordinateAdjoinAlgEquiv_algebraMap (hnosplit : ¬ ∃ a : k, IsPrimitiveRoot a 3)
    (ζ : L) (hζ : IsPrimitiveRoot ζ 3) (a : k) :
    coordinateAdjoinAlgEquiv k L hnosplit ζ hζ
      (algebraMap k (rootsOfUnityCoordinateRing k 3) a) =
      (a, algebraMap k (Algebra.adjoin k ({ζ} : Set L)) a) :=
  (coordinateAdjoinAlgEquiv k L hnosplit ζ hζ).commutes a

/-- Polynomial classes evaluate in the generated subalgebra. -/
lemma coordinateAdjoinAlgEquiv_mk (hnosplit : ¬ ∃ a : k, IsPrimitiveRoot a 3)
    (ζ : L) (hζ : IsPrimitiveRoot ζ 3) (p : k[X]) :
    coordinateAdjoinAlgEquiv k L hnosplit ζ hζ
      ((rootsOfUnityCoordinateAlgEquiv k 3).symm (AdjoinRoot.mk _ p)) =
      (p.eval 1, aeval (⟨ζ, Algebra.self_mem_adjoin_singleton k ζ⟩ :
        Algebra.adjoin k ({ζ} : Set L)) p) := by
  simp [coordinateAdjoinAlgEquiv, AlgEquiv.prodCongr_apply]

/-- First projection after the chosen-coordinate equivalence is evaluation
at one after the coordinate presentation. -/
lemma coordinateAdjoinAlgEquiv_fst (hnosplit : ¬ ∃ a : k, IsPrimitiveRoot a 3)
    (ζ : L) (hζ : IsPrimitiveRoot ζ 3) :
    (AlgHom.fst k k (Algebra.adjoin k ({ζ} : Set L))).comp
      (coordinateAdjoinAlgEquiv k L hnosplit ζ hζ).toAlgHom =
        (evalOne k).comp (rootsOfUnityCoordinateAlgEquiv k 3).toAlgHom := by
  apply AlgHom.ext
  intro x
  change (coordinateTwoFactorAlgEquiv k (chosenRoot_three_isUnit k L ζ hζ) x).1 = _
  exact DFunLike.congr_fun
    (coordinateTwoFactorAlgEquiv_fst k (chosenRoot_three_isUnit k L ζ hζ)) x

/-- Second projection is the quadratic-adjoin comparison after the
quadratic quotient map, as an equality of algebra homomorphisms. -/
lemma coordinateAdjoinAlgEquiv_snd (hnosplit : ¬ ∃ a : k, IsPrimitiveRoot a 3)
    (ζ : L) (hζ : IsPrimitiveRoot ζ 3) :
    (AlgHom.snd k k (Algebra.adjoin k ({ζ} : Set L))).comp
      (coordinateAdjoinAlgEquiv k L hnosplit ζ hζ).toAlgHom =
        (quadraticAlgEquivAdjoin hnosplit ζ hζ).toAlgHom.comp
          ((quotientToQuadratic k).comp (rootsOfUnityCoordinateAlgEquiv k 3).toAlgHom) := by
  apply AlgHom.ext
  intro x
  change quadraticAlgEquivAdjoin hnosplit ζ hζ
    (coordinateTwoFactorAlgEquiv k (chosenRoot_three_isUnit k L ζ hζ) x).2 = _
  exact congrArg (quadraticAlgEquivAdjoin hnosplit ζ hζ)
    (DFunLike.congr_fun
      (coordinateTwoFactorAlgEquiv_snd k (chosenRoot_three_isUnit k L ζ hζ)) x)

/-- Including the chosen component into the extension recovers evaluation. -/
lemma coordinateAdjoinAlgEquiv_inclusion_comp (hnosplit : ¬ ∃ a : k, IsPrimitiveRoot a 3)
    (ζ : L) (hζ : IsPrimitiveRoot ζ 3) :
    (Algebra.adjoin k ({ζ} : Set L)).val.comp
      ((AlgHom.snd k k (Algebra.adjoin k ({ζ} : Set L))).comp
        (coordinateAdjoinAlgEquiv k L hnosplit ζ hζ).toAlgHom) =
      (quadraticEval ζ hζ).comp
        ((quotientToQuadratic k).comp (rootsOfUnityCoordinateAlgEquiv k 3).toAlgHom) := by
  rw [coordinateAdjoinAlgEquiv_snd]
  ext x
  exact DFunLike.congr_fun (quadraticAlgEquivAdjoin_inclusion_comp hnosplit hζ) _

/-- The cubic polynomial presentation with the chosen-root subalgebra
as its second factor. This uses the coordinate presentation. -/
def adjoinAlgEquiv (hnosplit : ¬ ∃ a : k, IsPrimitiveRoot a 3)
    (ζ : L) (hζ : IsPrimitiveRoot ζ 3) :
    AdjoinRoot (rootsOfUnityPolynomial k 3) ≃ₐ[k] k × Algebra.adjoin k ({ζ} : Set L) :=
  (rootsOfUnityCoordinateAlgEquiv k 3).symm.trans
    (coordinateAdjoinAlgEquiv k L hnosplit ζ hζ)

@[simp]
lemma adjoinAlgEquiv_mk (hnosplit : ¬ ∃ a : k, IsPrimitiveRoot a 3)
    (ζ : L) (hζ : IsPrimitiveRoot ζ 3) (p : k[X]) :
    adjoinAlgEquiv k L hnosplit ζ hζ (AdjoinRoot.mk _ p) =
      (p.eval 1, aeval (⟨ζ, Algebra.self_mem_adjoin_singleton k ζ⟩ :
        Algebra.adjoin k ({ζ} : Set L)) p) :=
  coordinateAdjoinAlgEquiv_mk k L hnosplit ζ hζ p

@[simp]
lemma adjoinAlgEquiv_root (hnosplit : ¬ ∃ a : k, IsPrimitiveRoot a 3)
    (ζ : L) (hζ : IsPrimitiveRoot ζ 3) :
    adjoinAlgEquiv k L hnosplit ζ hζ (AdjoinRoot.root _) =
      (1, ⟨ζ, Algebra.self_mem_adjoin_singleton k ζ⟩) := by
  simpa only [AdjoinRoot.root, eval_X, aeval_X] using
    adjoinAlgEquiv_mk k L hnosplit ζ hζ X

@[simp]
lemma adjoinAlgEquiv_algebraMap (hnosplit : ¬ ∃ a : k, IsPrimitiveRoot a 3)
    (ζ : L) (hζ : IsPrimitiveRoot ζ 3) (a : k) :
    adjoinAlgEquiv k L hnosplit ζ hζ (AdjoinRoot.of _ a) =
      (a, algebraMap k (Algebra.adjoin k ({ζ} : Set L)) a) :=
  (adjoinAlgEquiv k L hnosplit ζ hζ).commutes a

end AdjoinAlgebra

end Field

end AlgebraicGeometry.RootsOfUnityThree
