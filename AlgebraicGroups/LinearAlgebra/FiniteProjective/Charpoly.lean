/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import TauCeti.LinearAlgebra.Charpoly.Projective
public import AlgebraicGroups.RingTheory.Equalizer
public import Mathlib.RingTheory.LocalProperties.Exactness
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Characteristic polynomials of finite projective modules

For a finite projective module and a supplied natural number `n`, this file
uses the reflection of Tau Ceti’s canonical reversed characteristic
polynomial at `n`. At constant maximal-local rank `n`, comparison with the ordinary
characteristic polynomial after localization gives monicity and
Cayley--Hamilton. The polynomial itself does not supply a global basis.

No fixed-degree exterior-power base-change construction is used here.

## References

* Mathlib, `Mathlib.LinearAlgebra.Charpoly.Basic` (finite-free
  characteristic polynomial and Cayley--Hamilton),
  `Mathlib.LinearAlgebra.Charpoly.BaseChange`, and
  `Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff` (the reverse form) provide
  the free-module comparison. `Mathlib.RingTheory.LocalRing.Module`
  (`Module.free_of_flat_of_isLocalRing`) and
  `Mathlib.RingTheory.Spectrum.Prime.FreeLocus` supply the local freeness
  needed after localization; maximal-local detection proves the resulting
  coefficient and endomorphism equalities.
* The Stacks Project, Lemmas 39.23.2 and 39.23.4
  ([tags 03BH](https://stacks.math.columbia.edu/tag/03BH) and
  [03BJ](https://stacks.math.columbia.edu/tag/03BJ)), use invariant norm
  polynomials and Cayley--Hamilton to establish integrality for affine
  finite-locally-free groupoid relations. The conditional equalizer lemma
  below isolates their coefficient-invariance and integrality step, rather
  than proving the groupoid invariance assertion.
-/

public section

noncomputable section

open Polynomial
open scoped TensorProduct

namespace Module.FiniteProjective

universe uR uS uM uL

section FreeComparison

variable {R : Type uR} {M : Type uM}
  [CommRing R] [AddCommGroup M] [Module R M]

/-- With a finite basis, the reflected projective reversed characteristic polynomial is
 the ordinary characteristic polynomial. -/
lemma projectiveCharpolyRev_reflect_eq_charpoly
    [Module.Finite R M] [Module.Projective R M]
    {n : ℕ} (b : Module.Basis (Fin n) R M)
    [Module.Free R M] (f : Module.End R M) :
    (LinearMap.projectiveCharpolyRev f).reflect n = f.charpoly := by
  rcases subsingleton_or_nontrivial R with _ | _
  · exact Subsingleton.elim _ _
  rw [LinearMap.projectiveCharpolyRev_eq_charpolyRev b, ← Matrix.reverse_charpoly]
  unfold Polynomial.reverse
  rw [Matrix.charpoly_natDegree_eq_dim]
  simp only [Fintype.card_fin]
  rw [reflect_reflect]
  exact f.charpoly_toMatrix b

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
lemma projectiveCharpolyRev_reflect_map_localization_eq_charpoly
    (f : Module.End R M) (J : Ideal R) [J.IsMaximal]
    (hrank : Module.finrank (Localization J.primeCompl)
      (LocalizedModule J.primeCompl M) = n) :
    let _ : Module.Free (Localization J.primeCompl)
        (TensorProduct R (Localization J.primeCompl) M) :=
      Module.free_of_flat_of_isLocalRing
    ((LinearMap.projectiveCharpolyRev f).reflect n).map
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
  rw [← reflect_map, ← LinearMap.projectiveCharpolyRev_baseChange]
  exact projectiveCharpolyRev_reflect_eq_charpoly b
    (f.baseChange (Localization J.primeCompl))

/-- For constant maximal-local rank `n`, the finite-projective
characteristic polynomial is monic. This uses Mathlib's finite-free
characteristic-polynomial monicity after localization at maximal ideals. -/
lemma projectiveCharpolyRev_reflect_monic_of_local_finrank
    (f : Module.End R M)
    (hrank : ∀ (J : Ideal R) [J.IsMaximal],
      Module.finrank (Localization J.primeCompl)
        (LocalizedModule J.primeCompl M) = n) :
    ((LinearMap.projectiveCharpolyRev f).reflect n).Monic := by
  let p := (LinearMap.projectiveCharpolyRev f).reflect n
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
    rw [projectiveCharpolyRev_reflect_map_localization_eq_charpoly f J (hrank J)]
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
    rw [projectiveCharpolyRev_reflect_map_localization_eq_charpoly f J (hrank J)]
    rw [map_zero]
    apply coeff_eq_zero_of_natDegree_lt
    simpa [LinearMap.charpoly_natDegree, htensorRank] using hk
  exact monic_of_natDegree_le_of_coeff_eq_one n hdegree hcoeff

/-- Cayley--Hamilton for a finite projective module of constant maximal-local
rank, obtained from Mathlib's `LinearMap.aeval_self_charpoly` after
localization. -/
lemma projectiveCharpolyRev_reflect_aeval_eq_zero_of_local_finrank
    (f : Module.End R M)
    (hrank : ∀ (J : Ideal R) [J.IsMaximal],
      Module.finrank (Localization J.primeCompl)
        (LocalizedModule J.primeCompl M) = n) :
    aeval f ((LinearMap.projectiveCharpolyRev f).reflect n) = 0 := by
  let p := (LinearMap.projectiveCharpolyRev f).reflect n
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
    rw [projectiveCharpolyRev_reflect_map_localization_eq_charpoly
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

/-- Invariant coefficients of the finite-projective characteristic polynomial
give integrality over the equalizer. Compare the norm-polynomial argument in
Stacks Project, Lemma 39.23.4 (tag 03BJ), using Lemma 39.23.2 (tag 03BH):
the invariance of coefficients is assumed here, not deduced from a groupoid. -/
lemma isIntegral_equalizer_of_projectiveCharpolyRev_reflect_coeff_invariant
    (s t : A →ₐ[C] B) (hs : IsScalarTower.toAlgHom C A B = s)
    (ht : Function.Injective t) (n : ℕ)
    (hrank : ∀ (J : Ideal A) [J.IsMaximal],
      Module.finrank (Localization J.primeCompl)
        (LocalizedModule J.primeCompl B) = n)
    (x : A)
    (hcoeff : ∀ k,
      s (((LinearMap.projectiveCharpolyRev (Algebra.lmul A B (t x))).reflect n).coeff k) =
      t (((LinearMap.projectiveCharpolyRev (Algebra.lmul A B (t x))).reflect n).coeff k)) :
    IsIntegral (AlgHom.equalizer s t) x := by
  let f : Module.End A B := Algebra.lmul A B (t x)
  let p : A[X] := (LinearMap.projectiveCharpolyRev f).reflect n
  have hp_lifts : p ∈ Polynomial.lifts
      (algebraMap (AlgHom.equalizer s t) A) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro k
    refine ⟨⟨p.coeff k, ?_⟩, rfl⟩
    simpa [p, f] using hcoeff k
  obtain ⟨q, hqmap, -, hqmonic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hp_lifts
      (projectiveCharpolyRev_reflect_monic_of_local_finrank f hrank)
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
      have hCH := projectiveCharpolyRev_reflect_aeval_eq_zero_of_local_finrank
        f hrank
      apply Algebra.lmul_injective (R := A)
      simpa [← aeval_algHom_apply, f, p] using hCH
    _ = t 0 := (map_zero t).symm

end EqualizerIntegrality

end Module.FiniteProjective
