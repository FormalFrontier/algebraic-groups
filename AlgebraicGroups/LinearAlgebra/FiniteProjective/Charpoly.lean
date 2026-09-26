/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.LinearAlgebra.FiniteProjective.Fredholm
public import AlgebraicGroups.RingTheory.Equalizer
public import Mathlib.RingTheory.LocalProperties.Exactness
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Characteristic polynomials of finite projective modules

For a finite projective module of constant local rank, this file defines its
characteristic polynomial by reflecting the presentation-independent Fredholm
polynomial.  Scalar-base-change and intertwining formulas follow from the
Fredholm construction.  Comparison with the ordinary characteristic
polynomial after localization gives monicity and Cayley--Hamilton.

No fixed-degree exterior-power base-change construction is used here.
-/

public section

noncomputable section

open Polynomial
open scoped TensorProduct

namespace Module.FiniteProjective

universe uR uS uM uN uL

variable (R : Type uR) (M : Type uM)
  [CommRing R] [AddCommGroup M] [Module R M]

/-- The characteristic polynomial obtained by reflecting the canonical
Fredholm polynomial at the prescribed constant rank. -/
noncomputable def finiteProjectiveCharpoly [Module.Finite R M]
    [Module.Projective R M] (n : ℕ) (f : Module.End R M) : R[X] :=
  (FreePresentation.fredholm (R := R) (M := M)
    (freePresentation R M) f).reflect n

section BaseChange

variable {R : Type uR} {S : Type uS} {M : Type uM}
  [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M]
  [Module.Finite R M] [Module.Projective R M]

/-- The finite-projective characteristic polynomial commutes with arbitrary
scalar extension. -/
lemma finiteProjectiveCharpoly_baseChange (n : ℕ) (f : Module.End R M) :
    (finiteProjectiveCharpoly R M n f).map (algebraMap R S) =
      finiteProjectiveCharpoly S (TensorProduct R S M) n
        (f.baseChange S) := by
  unfold finiteProjectiveCharpoly
  rw [← reflect_map]
  congr 1
  rw [FreePresentation.fredholm_baseChange]
  exact FreePresentation.fredholm_eq (R := S) (M := TensorProduct R S M)
    (FreePresentation.baseChange (R := R) (M := M)
      (freePresentation R M) S)
    (freePresentation S (TensorProduct R S M)) (f.baseChange S)

/-- Coefficients of the finite-projective characteristic polynomial commute
with arbitrary scalar extension. -/
lemma finiteProjectiveCharpoly_coeff_baseChange (n k : ℕ)
    (f : Module.End R M) :
    algebraMap R S ((finiteProjectiveCharpoly R M n f).coeff k) =
      (finiteProjectiveCharpoly S (TensorProduct R S M) n
        (f.baseChange S)).coeff k := by
  rw [← coeff_map, finiteProjectiveCharpoly_baseChange]

end BaseChange

section Equivariance

variable {R : Type uR} {S : Type uS}
  {M : Type uM} {N : Type uN}
  [CommRing R] [CommRing S]
  [AddCommGroup M] [Module R M]
  [AddCommGroup N]

/-- The finite-projective characteristic polynomial is invariant under an
intertwining linear equivalence. -/
lemma finiteProjectiveCharpoly_eq_of_equiv_intertwine
    [Module R N]
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    (n : ℕ) (e : M ≃ₗ[R] N) (f : Module.End R M) (g : Module.End R N)
    (h : e.toLinearMap ∘ₗ f = g ∘ₗ e.toLinearMap) :
    finiteProjectiveCharpoly R M n f =
      finiteProjectiveCharpoly R N n g := by
  unfold finiteProjectiveCharpoly
  congr 1
  exact FreePresentation.fredholm_eq_of_equiv_intertwine
    (R := R) (M := M) (N := N)
    (freePresentation R M) (freePresentation R N) e f g h

/-- Extension of scalars along a ring equivalence followed by the equivalence
itself recovers the original module. -/
noncomputable def ringEquivTensorLid [Module S N] (e : R ≃+* S) :
    letI : Algebra R S := e.toRingHom.toAlgebra
    letI : Module R N := Module.compHom N e.toRingHom
    S ⊗[R] N ≃ₗ[S] N := by
  let _ : Algebra R S := e.toRingHom.toAlgebra
  let _ : Module R N := Module.compHom N e.toRingHom
  let _ : IsScalarTower R S N := ⟨fun r s x ↦ by
    change (e r * s) • x = e r • s • x
    rw [mul_smul]⟩
  let _ : Algebra S R := e.symm.toRingHom.toAlgebra
  let _ : IsScalarTower S R N := ⟨fun s r x ↦ by
    change e (e.symm s * r) • x = s • e r • x
    rw [map_mul, e.apply_symm_apply, mul_smul]⟩
  let _ : IsScalarTower S R S := ⟨fun s r z ↦ by
    change e (e.symm s * r) * z = s * (e r * z)
    rw [map_mul, e.apply_symm_apply, mul_assoc]⟩
  let _ : TensorProduct.CompatibleSMul R S S N :=
    TensorProduct.CompatibleSMul.of_algebraMap_surjective S N e.surjective
  let _ : TensorProduct.CompatibleSMul S R S N :=
    TensorProduct.CompatibleSMul.of_algebraMap_surjective S N e.symm.surjective
  exact TensorProduct.lidOfCompatibleSMul R S N

attribute [local instance] RingHomInvPair.of_ringEquiv

/-- The finite-projective characteristic polynomial is natural under an
intertwining semilinear equivalence over a ring equivalence. -/
lemma finiteProjectiveCharpoly_map_ringEquiv_of_intertwine
    [Module S N]
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite S N] [Module.Projective S N]
    (n : ℕ) (e : R ≃+* S)
    (q : M ≃ₛₗ[RingHomClass.toRingHom e] N)
    (f : Module.End R M) (g : Module.End S N)
    (h : ∀ x, q.toLinearMap (f x) = g (q.toLinearMap x)) :
    (finiteProjectiveCharpoly R M n f).map e.toRingHom =
      finiteProjectiveCharpoly S N n g := by
  let _ : Algebra R S := e.toRingHom.toAlgebra
  let _ : Module R N := Module.compHom N e.toRingHom
  let _ : IsScalarTower R S N := ⟨fun r s x ↦ by
    change (e r * s) • x = e r • s • x
    rw [mul_smul]⟩
  let qR : M ≃ₗ[R] N :=
    { q with
      map_smul' := fun r x ↦ by
        change q.toLinearMap (r • x) = e r • q.toLinearMap x
        exact q.toLinearMap.map_smulₛₗ r x }
  let qS : TensorProduct R S M ≃ₗ[S] N :=
    (qR.baseChange R S M N).trans (ringEquivTensorLid e)
  have hqS : qS.toLinearMap ∘ₗ f.baseChange S =
      g ∘ₗ qS.toLinearMap := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp_all
    | tmul s x =>
      change s • q.toLinearMap (f x) = g (s • q.toLinearMap x)
      rw [h, g.map_smul]
  change (finiteProjectiveCharpoly R M n f).map (algebraMap R S) = _
  rw [finiteProjectiveCharpoly_baseChange]
  exact finiteProjectiveCharpoly_eq_of_equiv_intertwine n qS
    (f.baseChange S) g hqS

end Equivariance

section FreeComparison

variable {R : Type uR} {M : Type uM}
  [CommRing R] [AddCommGroup M] [Module R M]

/-- The split presentation associated to a finite basis. -/
@[expose] noncomputable def FreePresentation.ofBasis {n : ℕ}
    (b : Module.Basis (Fin n) R M) : FreePresentation R M where
  n := n
  proj := b.equivFun.symm.toLinearMap
  incl := b.equivFun.toLinearMap
  proj_comp_incl := by simp

/-- With a finite basis, the finite-projective characteristic polynomial is
the ordinary characteristic polynomial. -/
lemma finiteProjectiveCharpoly_eq_charpoly
    [Module.Finite R M] [Module.Projective R M]
    {n : ℕ} (b : Module.Basis (Fin n) R M)
    [Module.Free R M] (f : Module.End R M) :
    finiteProjectiveCharpoly R M n f = f.charpoly := by
  by_cases hR : Nontrivial R
  · let _ : Nontrivial R := hR
    unfold finiteProjectiveCharpoly
    rw [FreePresentation.fredholm_eq (R := R) (M := M)
      (freePresentation R M) (FreePresentation.ofBasis (R := R) (M := M) b) f]
    unfold FreePresentation.fredholm
    have hmatrix : LinearMap.toMatrix'
        ((FreePresentation.ofBasis (R := R) (M := M) b).incl.comp
      (f.comp (FreePresentation.ofBasis (R := R) (M := M) b).proj)) =
        LinearMap.toMatrix b b f := by
      dsimp only [FreePresentation.ofBasis]
      rfl
    rw [hmatrix]
    change (Matrix.charpolyRev (LinearMap.toMatrix b b f)).reflect n =
      f.charpoly
    rw [← Matrix.reverse_charpoly]
    unfold Polynomial.reverse
    rw [Matrix.charpoly_natDegree_eq_dim]
    simp only [Fintype.card_fin]
    rw [reflect_reflect]
    exact f.charpoly_toMatrix b
  · let _ : Subsingleton R := not_nontrivial_iff_subsingleton.mp hR
    exact Subsingleton.elim _ _

end FreeComparison

section LocalGlobal

variable {R : Type uR} {M : Type uM} {n : ℕ}
  [CommRing R] [AddCommGroup M] [Module R M]

/-- Equality of scalars can be checked after localization at every maximal
ideal. -/
lemma eq_of_algebraMap_localization_maximal_eq (a b : R)
    (h : ∀ (J : Ideal R) [J.IsMaximal],
      algebraMap R (Localization J.primeCompl) a =
        algebraMap R (Localization J.primeCompl) b) :
    a = b := by
  apply MaximalSpectrum.toPiLocalization_injective R
  funext J
  let _ : J.1.IsMaximal := J.2
  exact h J.1

/-- The universal localized-module map on the tensor-product model is the
ordinary base change of a linear map. -/
lemma localizedMap_tensorProduct_eq_baseChange (T : Submonoid R)
    (g : Module.End R M) :
    IsLocalizedModule.mapExtendScalars T
        (TensorProduct.mk R (Localization T) M 1)
        (TensorProduct.mk R (Localization T) M 1)
        (Localization T) g =
      g.baseChange (Localization T) := by
  apply LinearMap.restrictScalars_injective R
  apply IsLocalizedModule.linearMap_ext T
    (TensorProduct.mk R (Localization T) M 1)
    (TensorProduct.mk R (Localization T) M 1)
  ext x
  change (IsLocalizedModule.map T
      (TensorProduct.mk R (Localization T) M 1)
      (TensorProduct.mk R (Localization T) M 1) g)
        ((TensorProduct.mk R (Localization T) M 1) x) =
    (TensorProduct.mk R (Localization T) M 1) (g x)
  rw [IsLocalizedModule.map_apply]

/-- Polynomial evaluation in an endomorphism commutes with arbitrary scalar
extension. -/
lemma aeval_end_baseChange (S : Type uS) [CommRing S] [Algebra R S]
    (g : Module.End R M) (p : R[X]) :
    (aeval g p).baseChange S =
      aeval (g.baseChange S) (p.map (algebraMap R S)) := by
  change (Module.End.baseChangeHom R S M) (aeval g p) =
    aeval ((Module.End.baseChangeHom R S M) g)
      (p.map (algebraMap R S))
  exact Polynomial.map_aeval_eq_aeval_map
    (φ := algebraMap R S)
    (ψ := (Module.End.baseChangeHom R S M).toRingHom)
    (by ext r x; simp) p g

variable [Module.Finite R M] [Module.Projective R M]

/-- After localization at a maximal ideal where the projective module has
rank `n`, the finite-projective polynomial is the ordinary characteristic
polynomial. -/
lemma finiteProjectiveCharpoly_map_localization_eq_charpoly
    (f : Module.End R M) (J : Ideal R) [J.IsMaximal]
    (hrank : Module.finrank (Localization J.primeCompl)
      (LocalizedModule J.primeCompl M) = n) :
    let _ : Module.Free (Localization J.primeCompl)
        (TensorProduct R (Localization J.primeCompl) M) :=
      Module.free_of_flat_of_isLocalRing
    (finiteProjectiveCharpoly R M n f).map
        (algebraMap R (Localization J.primeCompl)) =
      (f.baseChange (Localization J.primeCompl)).charpoly := by
  let _ : Module.Free (Localization J.primeCompl)
      (TensorProduct R (Localization J.primeCompl) M) :=
    Module.free_of_flat_of_isLocalRing
  have htensorRank : Module.finrank (Localization J.primeCompl)
      (TensorProduct R (Localization J.primeCompl) M) = n := by
    rw [← (LocalizedModule.equivTensorProduct J.primeCompl M).finrank_eq]
    exact hrank
  let b := Module.finBasisOfFinrankEq (Localization J.primeCompl)
    (TensorProduct R (Localization J.primeCompl) M) htensorRank
  rw [finiteProjectiveCharpoly_baseChange]
  exact finiteProjectiveCharpoly_eq_charpoly b
    (f.baseChange (Localization J.primeCompl))

/-- For constant maximal-local rank `n`, the finite-projective
characteristic polynomial is monic of degree `n`. -/
lemma finiteProjectiveCharpoly_monic_of_local_finrank
    (f : Module.End R M)
    (hrank : ∀ (J : Ideal R) [J.IsMaximal],
      Module.finrank (Localization J.primeCompl)
        (LocalizedModule J.primeCompl M) = n) :
    (finiteProjectiveCharpoly R M n f).Monic := by
  let p := finiteProjectiveCharpoly R M n f
  have hcoeff : p.coeff n = 1 := by
    apply eq_of_algebraMap_localization_maximal_eq
    intro J hJ
    let _ : Module.Free (Localization J.primeCompl)
        (TensorProduct R (Localization J.primeCompl) M) :=
      Module.free_of_flat_of_isLocalRing
    have htensorRank : Module.finrank (Localization J.primeCompl)
        (TensorProduct R (Localization J.primeCompl) M) = n := by
      rw [← (LocalizedModule.equivTensorProduct J.primeCompl M).finrank_eq]
      exact hrank J
    rw [← coeff_map]
    rw [finiteProjectiveCharpoly_map_localization_eq_charpoly f J (hrank J)]
    simpa [LinearMap.charpoly_natDegree, htensorRank] using
      (LinearMap.charpoly_monic
        (f.baseChange (Localization J.primeCompl))).coeff_natDegree
  have hdegree : p.natDegree ≤ n := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    apply eq_of_algebraMap_localization_maximal_eq
    intro J hJ
    let _ : Module.Free (Localization J.primeCompl)
        (TensorProduct R (Localization J.primeCompl) M) :=
      Module.free_of_flat_of_isLocalRing
    have htensorRank : Module.finrank (Localization J.primeCompl)
        (TensorProduct R (Localization J.primeCompl) M) = n := by
      rw [← (LocalizedModule.equivTensorProduct J.primeCompl M).finrank_eq]
      exact hrank J
    rw [← coeff_map]
    rw [finiteProjectiveCharpoly_map_localization_eq_charpoly f J (hrank J)]
    rw [map_zero]
    apply coeff_eq_zero_of_natDegree_lt
    simpa [LinearMap.charpoly_natDegree, htensorRank] using hk
  exact monic_of_natDegree_le_of_coeff_eq_one n hdegree hcoeff

/-- Cayley--Hamilton for a finite projective module of constant maximal-local
rank. -/
lemma finiteProjectiveCharpoly_aeval_eq_zero_of_local_finrank
    (f : Module.End R M)
    (hrank : ∀ (J : Ideal R) [J.IsMaximal],
      Module.finrank (Localization J.primeCompl)
        (LocalizedModule J.primeCompl M) = n) :
    aeval f (finiteProjectiveCharpoly R M n f) = 0 := by
  let p := finiteProjectiveCharpoly R M n f
  apply LinearMap.ext
  intro x
  apply Module.eq_zero_of_localization_maximal
    (fun (J : Ideal R) [J.IsMaximal] ↦
      TensorProduct R (Localization J.primeCompl) M)
    (fun (J : Ideal R) [J.IsMaximal] ↦
      (TensorProduct.mk R (Localization J.primeCompl) M) 1)
  intro J hJ
  let _ : Module.Free (Localization J.primeCompl)
      (TensorProduct R (Localization J.primeCompl) M) :=
    Module.free_of_flat_of_isLocalRing
  have hbase : (aeval f p).baseChange (Localization J.primeCompl) = 0 := by
    rw [aeval_end_baseChange]
    rw [finiteProjectiveCharpoly_map_localization_eq_charpoly
      f J (hrank J)]
    exact LinearMap.aeval_self_charpoly
      (f.baseChange (Localization J.primeCompl))
  have hx := LinearMap.congr_fun hbase
    ((1 : Localization J.primeCompl) ⊗ₜ[R] x)
  simpa using hx

end LocalGlobal

section EqualizerIntegrality

variable {C : Type uL} {A : Type uR} {B : Type uM}
  [CommRing C] [CommRing A] [CommRing B]
  [Algebra C A] [Algebra C B] [Algebra A B] [IsScalarTower C A B]
  [Module.Finite A B] [Module.Projective A B]

/-- Invariant coefficients of the canonical finite-projective characteristic
polynomial give integrality over the equalizer. -/
lemma isIntegral_equalizer_of_finiteProjectiveCharpoly_coeff_invariant
    (s t : A →ₐ[C] B) (hs : IsScalarTower.toAlgHom C A B = s)
    (ht : Function.Injective t) (n : ℕ)
    (hrank : ∀ (J : Ideal A) [J.IsMaximal],
      Module.finrank (Localization J.primeCompl)
        (LocalizedModule J.primeCompl B) = n)
    (x : A)
    (hcoeff : ∀ k,
      s ((finiteProjectiveCharpoly A B n
        (Algebra.lmul A B (t x))).coeff k) =
      t ((finiteProjectiveCharpoly A B n
        (Algebra.lmul A B (t x))).coeff k)) :
    IsIntegral (AlgHom.equalizer s t) x := by
  let f : Module.End A B := Algebra.lmul A B (t x)
  let p : A[X] := finiteProjectiveCharpoly A B n f
  have hp_lifts : p ∈ Polynomial.lifts
      (algebraMap (AlgHom.equalizer s t) A) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro k
    refine ⟨⟨p.coeff k, ?_⟩, rfl⟩
    simpa [p, f] using hcoeff k
  obtain ⟨q, hqmap, -, hqmonic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hp_lifts
      (finiteProjectiveCharpoly_monic_of_local_finrank f hrank)
  refine ⟨q, hqmonic, ?_⟩
  apply ht
  have hbase : s.toRingHom.comp (algebraMap (AlgHom.equalizer s t) A) =
      algebraMap (AlgHom.equalizer s t) B := by
    ext c
    change s c.1 = algebraMap A B c.1
    exact (DFunLike.congr_fun hs c.1).symm
  have hqB : q.map (algebraMap (AlgHom.equalizer s t) B) =
      p.map s.toRingHom := by
    calc
      q.map (algebraMap (AlgHom.equalizer s t) B) =
          q.map (s.toRingHom.comp
            (algebraMap (AlgHom.equalizer s t) A)) := by rw [hbase]
      _ = (q.map (algebraMap (AlgHom.equalizer s t) A)).map
          s.toRingHom := by rw [Polynomial.map_map]
      _ = p.map s.toRingHom := by rw [hqmap]
  have htbase : (algebraMap B B).comp
      (algebraMap (AlgHom.equalizer s t) B) =
      t.toRingHom.comp (algebraMap (AlgHom.equalizer s t) A) := by
    ext c
    have hc : t c.1 = algebraMap A B c.1 := by
      calc
        t c.1 = s c.1 := c.2.symm
        _ = IsScalarTower.toAlgHom C A B c.1 :=
          (DFunLike.congr_fun hs c.1).symm
        _ = algebraMap A B c.1 := rfl
    change t c.1 = algebraMap (AlgHom.equalizer s t) B c at hc
    exact hc.symm
  have hsRing : s.toRingHom = algebraMap A B := by
    ext a
    exact (DFunLike.congr_fun hs a).symm
  calc
    t (Polynomial.aeval x q) =
        Polynomial.aeval (t x)
          (q.map (algebraMap (AlgHom.equalizer s t) B)) :=
      Polynomial.map_aeval_eq_aeval_map htbase q x
    _ = Polynomial.aeval (t x) (p.map s.toRingHom) := by rw [hqB]
    _ = 0 := by
      rw [hsRing]
      rw [Polynomial.aeval_map_algebraMap]
      have hCH := finiteProjectiveCharpoly_aeval_eq_zero_of_local_finrank
        f hrank
      apply Algebra.lmul_injective (R := A)
      simpa [← aeval_algHom_apply, f, p] using hCH
    _ = t 0 := (map_zero t).symm

end EqualizerIntegrality

end Module.FiniteProjective
