/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.ArtinSchreierTwistedLine

set_option warningAsError true

noncomputable section

open ArtinSchreierTwistedLine
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

private theorem testEquation (R : Type*) [CommRing R] (p : ℕ) (t : R) :
    equation R p t =
      MvPolynomial.X 0 ^ p - MvPolynomial.X 0 - MvPolynomial.C t * MvPolynomial.X 1 ^ p := rfl

private theorem testEquationIdeal (R : Type*) [CommRing R] (p : ℕ) (t : R) :
    equationIdeal R p t = Ideal.span {equation R p t} := rfl

private theorem testX (R : Type*) [CommRing R] (p : ℕ) (t : R) :
    x R p t = Ideal.Quotient.mk _ (MvPolynomial.X 1) := rfl

private theorem testY (R : Type*) [CommRing R] (p : ℕ) (t : R) :
    y R p t = Ideal.Quotient.mk _ (MvPolynomial.X 0) := rfl

private theorem testSatisfiesEquation (R A : Type*) [CommRing R] [Ring A] [Algebra R A]
    (p : ℕ) (t : R) (x' y' : A) :
    SatisfiesEquation R p t x' y' ↔
      y' ^ p - y' - algebraMap R A t * x' ^ p = 0 := Iff.rfl

private def testLift (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
    (p : ℕ) (t : R) (x' y' : A) (h : SatisfiesEquation R p t x' y') :
    CoordinateRing R p t →ₐ[R] A := lift R p t x' y' h

private theorem testLiftComp (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
    (p : ℕ) (t : R) (x' y' : A) (h : SatisfiesEquation R p t x' y') :
    (lift R p t x' y' h).comp (Ideal.Quotient.mkₐ R (equationIdeal R p t)) =
      (MvPolynomial.aeval (fun i ↦ Fin.cases y' (fun _ ↦ x') i) :
        MvPolynomial (Fin 2) R →ₐ[R] A) := by
  unfold lift
  apply Ideal.Quotient.liftₐ_comp

private theorem testLiftX (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
    (p : ℕ) (t : R) (x' y' : A) (h : SatisfiesEquation R p t x' y') :
    lift R p t x' y' h (x R p t) = x' := by
  change ((lift R p t x' y' h).comp (Ideal.Quotient.mkₐ R (equationIdeal R p t)))
    (MvPolynomial.X 1) = x'
  rw [testLiftComp]
  simp only [MvPolynomial.aeval_X]
  rfl

private theorem testLiftY (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
    (p : ℕ) (t : R) (x' y' : A) (h : SatisfiesEquation R p t x' y') :
    lift R p t x' y' h (y R p t) = y' := by
  change ((lift R p t x' y' h).comp (Ideal.Quotient.mkₐ R (equationIdeal R p t)))
    (MvPolynomial.X 0) = y'
  rw [testLiftComp]
  simp only [MvPolynomial.aeval_X, Fin.cases_zero]

private theorem testDefiningEquation (R : Type*) [CommRing R] (p : ℕ) (t : R) :
    y R p t ^ p - y R p t =
      algebraMap R (CoordinateRing R p t) t * x R p t ^ p :=
  y_pow_sub_y_eq R p t

private def testComul (R : Type*) [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]
    (t : R) : CoordinateRing R p t →ₐ[R]
      CoordinateRing R p t ⊗[R] CoordinateRing R p t := comul R t

private theorem testComulX (R : Type*) [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]
    (t : R) : comul R t (x R p t) =
      Algebra.TensorProduct.includeLeft (R := R) (S := R) (x R p t) +
        Algebra.TensorProduct.includeRight (R := R) (x R p t) := by
  simp only [comul, testLiftX]

private theorem testComulY (R : Type*) [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]
    (t : R) : comul R t (y R p t) =
      Algebra.TensorProduct.includeLeft (R := R) (S := R) (y R p t) +
        Algebra.TensorProduct.includeRight (R := R) (y R p t) := by
  simp only [comul, testLiftY]

private def testCounit (R : Type*) [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]
    (t : R) : CoordinateRing R p t →ₐ[R] R := counit R t

private theorem testCounitX (R : Type*) [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]
    (t : R) : counit R t (x R p t) = 0 := by
  simp only [counit, testLiftX]

private theorem testCounitY (R : Type*) [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]
    (t : R) : counit R t (y R p t) = 0 := by
  simp only [counit, testLiftY]

private def testAntipode (R : Type*) [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]
    (t : R) : CoordinateRing R p t →ₐ[R] CoordinateRing R p t := antipode R t

private theorem testAntipodeX (R : Type*) [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]
    (t : R) : antipode R t (x R p t) = -x R p t := by
  simp only [antipode, testLiftX]

private theorem testAntipodeY (R : Type*) [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]
    (t : R) : antipode R t (y R p t) = -y R p t := by
  simp only [antipode, testLiftY]

private theorem testBialgebra (R : Type*) [CommRing R] {p : ℕ} [Fact p.Prime]
    [CharP R p] (t : R) : Nonempty (Bialgebra R (CoordinateRing R p t)) :=
  ⟨inferInstance⟩

private theorem testHopfAlgebra (R : Type*) [CommRing R] {p : ℕ} [Fact p.Prime]
    [CharP R p] (t : R) : Nonempty (HopfAlgebra R (CoordinateRing R p t)) :=
  ⟨inferInstance⟩

private def testGroupScheme (R : Type*) [CommRing R] {p : ℕ} [Fact p.Prime]
    [CharP R p] (t : R) : Grp (Over (Spec (.of R))) := groupScheme R t

private theorem testW (R L : Type*) [CommRing R] [CommRing L] [Algebra R L]
    (p : ℕ) (t : R) (u : Lˣ) :
    W R L p t u = (1 : L) ⊗ₜ[R] y R p t - (u : L) ⊗ₜ[R] x R p t := rfl

private def testNormalForm (R L : Type*) [CommRing R] [CommRing L] [Algebra R L]
    {p : ℕ} [Fact p.Prime] [CharP L p] (t : R) (u : Lˣ)
    (hu : (u : L) ^ p = algebraMap R L t) :
    L ⊗[R] CoordinateRing R p t ≃ₐ[L] Polynomial L :=
  baseChangeNormalForm R L t u hu

private theorem testNormalFormX (R L : Type*) [CommRing R] [CommRing L] [Algebra R L]
    {p : ℕ} [Fact p.Prime] [CharP L p] (t : R) (u : Lˣ)
    (hu : (u : L) ^ p = algebraMap R L t) :
    baseChangeNormalForm R L t u hu ((1 : L) ⊗ₜ[R] x R p t) =
      Polynomial.C ((u⁻¹ : Lˣ) : L) * (Polynomial.X ^ p - Polynomial.X) := by
  simp

private theorem testNormalFormY (R L : Type*) [CommRing R] [CommRing L] [Algebra R L]
    {p : ℕ} [Fact p.Prime] [CharP L p] (t : R) (u : Lˣ)
    (hu : (u : L) ^ p = algebraMap R L t) :
    baseChangeNormalForm R L t u hu ((1 : L) ⊗ₜ[R] y R p t) = Polynomial.X ^ p := by
  simp

private theorem testNormalFormW (R L : Type*) [CommRing R] [CommRing L] [Algebra R L]
    {p : ℕ} [Fact p.Prime] [CharP L p] (t : R) (u : Lˣ)
    (hu : (u : L) ^ p = algebraMap R L t) :
    baseChangeNormalForm R L t u hu (W R L p t u) = Polynomial.X := by
  simp

private theorem testNormalFormInverseX (R L : Type*) [CommRing R] [CommRing L]
    [Algebra R L] {p : ℕ} [Fact p.Prime] [CharP L p] (t : R) (u : Lˣ)
    (hu : (u : L) ^ p = algebraMap R L t) :
    (baseChangeNormalForm R L t u hu).symm Polynomial.X = W R L p t u := by
  simp

private theorem testNormalFormRoundtrip (R L : Type*) [CommRing R] [CommRing L]
    [Algebra R L] {p : ℕ} [Fact p.Prime] [CharP L p] (t : R) (u : Lˣ)
    (hu : (u : L) ^ p = algebraMap R L t) :
    (baseChangeNormalForm R L t u hu).symm
        (baseChangeNormalForm R L t u hu ((1 : L) ⊗ₜ[R] x R p t)) =
      (1 : L) ⊗ₜ[R] x R p t := by
  exact (baseChangeNormalForm R L t u hu).symm_apply_apply _

private theorem testStandardSmooth (R : Type*) [CommRing R] {p : ℕ} [CharP R p]
    (t : R) : Algebra.IsStandardSmooth R (CoordinateRing R p t) :=
  coordinateRing_isStandardSmooth R t

private theorem testSmooth (R : Type*) [CommRing R] {p : ℕ} [CharP R p]
    (t : R) : Algebra.Smooth R (CoordinateRing R p t) :=
  coordinateRing_smooth R t

private theorem testSchemeSmooth (R : Type*) [CommRing R] {p : ℕ} [CharP R p]
    (t : R) : Smooth (scheme R p t).hom := scheme_smooth R t

private theorem testBaseChangeConnected (R L : Type*) [CommRing R] [CommRing L]
    [Algebra R L] [IsDomain L] {p : ℕ} [Fact p.Prime] [CharP L p]
    (t : R) (u : Lˣ) (hu : (u : L) ^ p = algebraMap R L t) :
    ConnectedSpace (Spec (.of (L ⊗[R] CoordinateRing R p t))) :=
  baseChangeSpec_connectedSpace R L t u hu

private theorem testDomain (K : Type*) [Field K] {p : ℕ} (hp : p.Prime)
    [CharP K p] {t : K} (ht : t ≠ 0) :
    IsDomain (CoordinateRing K p t) := coordinateRing_isDomain_of_ne_zero K hp ht

private theorem testConnected (K : Type*) [Field K] {p : ℕ} (hp : p.Prime)
    [CharP K p] {t : K} (ht : t ≠ 0) :
    ConnectedSpace (scheme K p t).left := scheme_connectedSpace_of_ne_zero K hp ht

private theorem testDisconnected (K : Type*) [Field K] {p : ℕ} (hp : p.Prime)
    [CharP K p] : ¬ ConnectedSpace (scheme K p 0).left :=
  not_scheme_connectedSpace_zero K hp
