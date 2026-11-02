/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Bialgebra.RelativeFrobenius
public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.SymmetricAlgebra
public import AlgebraicGroups.Algebra.SymmetricAlgebra
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.MvPolynomial.Expand
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Frobenius linearization of symmetric-algebra generators

The generator-power function on a module is Frobenius-semilinear. Its linearization
has source the coefficient-first Frobenius base extension, with the original module
action on the right factor and the ordinary new coefficient action on the left.
Its image is the submodule spanned by powers of generators in the original symmetric
algebra, rather than the span of powers of arbitrary algebra elements.

The linearization is the composite of the base change of the generator map and the
relative Frobenius of the symmetric algebra. In particular, it does not require an
inverse to coefficient Frobenius. For a projective semimodule it is injective and
identifies the base extension canonically with the generator-power submodule. This
submodule is projective when the original module is projective, and free when it is
free. Finite generation of the original module implies finite generation of that submodule.
Over a field, the pure-power submodule has the same `Module.finrank` as the original
module, without a finite-dimensionality assumption.

## References

Mathlib supplies scalar extension, the primitive bialgebra on a symmetric algebra,
base-changed bases and coefficient-preserving polynomial expansion.
-/

@[expose] public noncomputable section

universe u v w

open scoped TensorProduct

namespace SymmetricAlgebra

variable (K : Type u) (V : Type v)
variable [CommSemiring K] [AddCommMonoid V] [Module K V]
variable (p r : ℕ) [ExpChar K p]

/-- The linearization of the Frobenius-semilinear generator-power map. Its
coefficient action is the new action on the base extension. -/
def frobeniusLinearMap :
    Algebra.FrobeniusTwist.twistObject K V p r →ₗ[K] SymmetricAlgebra K V :=
  let baseChange :
      ∀ (R S : Type u) (M : Type v) (N : Type (max u v))
        [CommSemiring R] [CommSemiring S] [Algebra R S]
        [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N],
        (M →ₗ[R] N) → (S ⊗[R] M →ₗ[S] S ⊗[R] N) :=
    fun R S M N _ _ _ _ _ _ _ f => f.baseChange S
  (Bialgebra.relativeFrobenius K (SymmetricAlgebra K V) p r).toAlgHom.toLinearMap.comp
    (@baseChange K K V (SymmetricAlgebra K V)
      _ _ (Algebra.FrobeniusTwist.coefficientAlgebra K p r)
      _ _ ‹Module K V› (inferInstance : Module K (SymmetricAlgebra K V)) (ι K V))

/-- The Frobenius linearization retains the new coefficient. -/
@[simp] theorem frobeniusLinearMap_tmul (c : K) (v : V) :
    frobeniusLinearMap K V p r (Algebra.FrobeniusTwist.tmul K V p r c v) =
      c • (ι K V v) ^ (p ^ r) := by
  change Bialgebra.relativeFrobenius K (SymmetricAlgebra K V) p r
      (Algebra.FrobeniusTwist.tmul K (SymmetricAlgebra K V) p r c (ι K V v)) = _
  rw [Bialgebra.relativeFrobenius_tmul, Algebra.smul_def]

/-- The image is the original span of generator powers. -/
theorem range_frobeniusLinearMap :
    LinearMap.range (frobeniusLinearMap K V p r) =
      purePowerSubmodule K V (p ^ r) := by
  have hmem (x : Algebra.FrobeniusTwist.twistObject K V p r) :
      frobeniusLinearMap K V p r x ∈ purePowerSubmodule K V (p ^ r) := by
    refine Algebra.FrobeniusTwist.inductionOn K V p r x ?_ ?_
    · intro c v
      rw [frobeniusLinearMap_tmul]
      exact (purePowerSubmodule K V (p ^ r)).smul_mem c
        (ι_pow_mem_purePowerSubmodule K V (p ^ r) v)
    · intro x y hx hy
      rw [map_add]
      exact (purePowerSubmodule K V (p ^ r)).add_mem hx hy
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact hmem x
  · apply (purePowerSubmodule_le_iff K V (p ^ r) _).2
    intro v
    exact ⟨Algebra.FrobeniusTwist.tmul K V p r 1 v, by
      rw [frobeniusLinearMap_tmul, one_smul]⟩

/-- A linear map out of the base extension is determined by its values on
unit-coefficient generator tensors. -/
theorem frobeniusLinearMap_unique
    (f : Algebra.FrobeniusTwist.twistObject K V p r →ₗ[K] SymmetricAlgebra K V)
    (hf : ∀ v : V, f (Algebra.FrobeniusTwist.tmul K V p r 1 v) =
      (ι K V v) ^ (p ^ r)) : f = frobeniusLinearMap K V p r := by
  apply LinearMap.toAddMonoidHom_injective
  apply Algebra.FrobeniusTwist.ext K V p r
  intro c v
  change f (Algebra.FrobeniusTwist.tmul K V p r c v) =
    frobeniusLinearMap K V p r (Algebra.FrobeniusTwist.tmul K V p r c v)
  have ht : Algebra.FrobeniusTwist.tmul K V p r c v =
      c • Algebra.FrobeniusTwist.tmul K V p r 1 v := by
    rw [Algebra.FrobeniusTwist.smul_tmul, mul_one]
  rw [ht, map_smul, map_smul, hf, frobeniusLinearMap_tmul, one_smul]

/-- The Frobenius linearization commutes with linear maps of the original modules
and their coefficient-first scalar extensions. -/
theorem frobeniusLinearMap_comp_baseChange {W : Type w}
    [AddCommMonoid W] [Module K W] (f : V →ₗ[K] W) :
    let baseChange :
        ∀ (R S : Type u) (M : Type v) (N : Type w)
          [CommSemiring R] [CommSemiring S] [Algebra R S]
          [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N],
          (M →ₗ[R] N) → (S ⊗[R] M →ₗ[S] S ⊗[R] N) :=
      fun R S M N _ _ _ _ _ _ _ g => g.baseChange S
    (frobeniusLinearMap K W p r).comp
        (@baseChange K K V W _ _ (Algebra.FrobeniusTwist.coefficientAlgebra K p r)
          _ _ ‹Module K V› ‹Module K W› f) =
      (map f).toLinearMap.comp (frobeniusLinearMap K V p r) := by
  apply LinearMap.toAddMonoidHom_injective
  apply Algebra.FrobeniusTwist.ext K V p r
  intro c v
  change frobeniusLinearMap K W p r (Algebra.FrobeniusTwist.tmul K W p r c (f v)) =
    map f (frobeniusLinearMap K V p r (Algebra.FrobeniusTwist.tmul K V p r c v))
  rw [frobeniusLinearMap_tmul, frobeniusLinearMap_tmul, map_smul, map_pow, map_ι]

private theorem frobeniusLinearMap_injective_of_basis {I : Type w}
    (b : Module.Basis I K V) :
    Function.Injective (frobeniusLinearMap K V p r) := by
  let bτ := Algebra.FrobeniusTwist.basis K V p r b
  have hbτ (i : I) :
      bτ i = Algebra.FrobeniusTwist.tmul K V p r 1 (b i) :=
    Algebra.FrobeniusTwist.basis_apply K V p r b i
  -- Expansion fixes coefficients. Its injectivity needs only p^r > 0.
  have hpow : LinearIndependent K
      (fun i : I => (MvPolynomial.X i : MvPolynomial I K) ^ (p ^ r)) := by
    have h := (MvPolynomial.linearIndependent_X I K).map_injOn
      (MvPolynomial.expand (p ^ r) (R := K) (σ := I)).toLinearMap
      (MvPolynomial.expand_injective (R := K) (σ := I)
        (expChar_pow_pos K p r)).injOn
    simpa only [Function.comp_def, AlgHom.toLinearMap_apply, MvPolynomial.expand_X] using h
  let Φ : Algebra.FrobeniusTwist.twistObject K V p r →ₗ[K] MvPolynomial I K :=
    (equivMvPolynomial b).toLinearMap.comp (frobeniusLinearMap K V p r)
  have hΦ : Φ = bτ.constr K
      (fun i : I => (MvPolynomial.X i : MvPolynomial I K) ^ (p ^ r)) := by
    apply bτ.ext
    intro i
    change equivMvPolynomial b (frobeniusLinearMap K V p r (bτ i)) =
      (bτ.constr K
        (fun j : I => (MvPolynomial.X j : MvPolynomial I K) ^ (p ^ r))) (bτ i)
    rw [Module.Basis.constr_basis, hbτ, frobeniusLinearMap_tmul,
      one_smul, map_pow, equivMvPolynomial_ι_apply]
  -- Compare two elements: a zero-kernel criterion would require cancellation.
  intro x y hxy
  have hΦxy : Φ x = Φ y := congrArg (equivMvPolynomial b) hxy
  apply bτ.injective_constr_of_linearIndependent (R₂ := K) hpow
  simpa only [hΦ] using hΦxy

private theorem frobeniusLinearMap_injective_of_free [Module.Free K V] :
    Function.Injective (frobeniusLinearMap K V p r) :=
  frobeniusLinearMap_injective_of_basis K V p r (Module.Free.chooseBasis K V)

/-- The Frobenius linearization is injective for a projective semimodule. -/
theorem frobeniusLinearMap_injective [Module.Projective K V] :
    Function.Injective (frobeniusLinearMap K V p r) := by
  obtain ⟨s, hs⟩ := (inferInstance : Module.Projective K V).out
  let π : (V →₀ K) →ₗ[K] V := Finsupp.linearCombination K id
  let sτ := Algebra.FrobeniusTwist.map K V p r s
  let πτ := Algebra.FrobeniusTwist.map K (V →₀ K) p r π
  have hπs : π.comp s = (LinearMap.id : V →ₗ[K] V) := by
    apply LinearMap.ext
    exact hs
  have hsplit : πτ.comp sτ = LinearMap.id := by
    change (Algebra.FrobeniusTwist.map K (V →₀ K) p r π).comp
      (Algebra.FrobeniusTwist.map K V p r s) = LinearMap.id
    rw [← Algebra.FrobeniusTwist.map_comp, hπs, Algebra.FrobeniusTwist.map_id]
  have hnat : (frobeniusLinearMap K (V →₀ K) p r).comp sτ =
      (map s).toLinearMap.comp (frobeniusLinearMap K V p r) :=
    frobeniusLinearMap_comp_baseChange K V p r s
  intro x y hxy
  have hsxy : sτ x = sτ y := by
    apply frobeniusLinearMap_injective_of_free K (V →₀ K) p r
    calc
      frobeniusLinearMap K (V →₀ K) p r (sτ x) =
          map s (frobeniusLinearMap K V p r x) := LinearMap.congr_fun hnat x
      _ = map s (frobeniusLinearMap K V p r y) := congrArg (map s) hxy
      _ = frobeniusLinearMap K (V →₀ K) p r (sτ y) :=
        (LinearMap.congr_fun hnat y).symm
  calc
    x = πτ (sτ x) := (LinearMap.congr_fun hsplit x).symm
    _ = πτ (sτ y) := congrArg πτ hsxy
    _ = y := LinearMap.congr_fun hsplit y

/-- Frobenius base extension identifies canonically with the original
pure-power submodule of the symmetric algebra of a projective semimodule. -/
def frobeniusEquivPurePowerSubmodule [Module.Projective K V] :
    Algebra.FrobeniusTwist.twistObject K V p r ≃ₗ[K]
      purePowerSubmodule K V (p ^ r) :=
  LinearEquiv.ofBijective
    ((frobeniusLinearMap K V p r).codRestrict
      (purePowerSubmodule K V (p ^ r))
      (fun x => (range_frobeniusLinearMap K V p r).le ⟨x, rfl⟩))
    ⟨fun x y h => frobeniusLinearMap_injective K V p r (congrArg Subtype.val h),
      fun y => by
        have hy : (y : SymmetricAlgebra K V) ∈
            LinearMap.range (frobeniusLinearMap K V p r) :=
          (range_frobeniusLinearMap K V p r).ge y.property
        obtain ⟨x, hx⟩ := hy
        exact ⟨x, Subtype.ext hx⟩⟩

/-- The canonical equivalence sends a tensor to the corresponding generator power. -/
@[simp] theorem coe_frobeniusEquivPurePowerSubmodule_tmul [Module.Projective K V]
    (c : K) (v : V) :
    (frobeniusEquivPurePowerSubmodule K V p r
      (Algebra.FrobeniusTwist.tmul K V p r c v) : SymmetricAlgebra K V) =
      c • (ι K V v) ^ (p ^ r) := by
  change frobeniusLinearMap K V p r (Algebra.FrobeniusTwist.tmul K V p r c v) = _
  exact frobeniusLinearMap_tmul K V p r c v

/-- The generator-power span of a projective semimodule is projective. -/
theorem moduleProjective_purePowerSubmodule [Module.Projective K V] :
    Module.Projective K (purePowerSubmodule K V (p ^ r)) := by
  let projectiveTwist :
      Module.Projective K (Algebra.FrobeniusTwist.twistObject K V p r) :=
    Algebra.FrobeniusTwist.moduleProjective K V p r
  exact Module.Projective.of_equiv' (frobeniusEquivPurePowerSubmodule K V p r)

/-- The generator-power span of a free semimodule is free. -/
theorem moduleFree_purePowerSubmodule [Module.Free K V] :
    Module.Free K (purePowerSubmodule K V (p ^ r)) := by
  let projective : Module.Projective K V := Module.Projective.of_free
  let freeTwist : Module.Free K (Algebra.FrobeniusTwist.twistObject K V p r) :=
    Algebra.FrobeniusTwist.moduleFree K V p r
  exact Module.Free.of_equiv' freeTwist (frobeniusEquivPurePowerSubmodule K V p r)

/-- Finite generation of the original module gives finite generation of its
Frobenius pure-power span. -/
theorem moduleFinite_purePowerSubmodule [Module.Finite K V] :
    Module.Finite K (purePowerSubmodule K V (p ^ r)) := by
  let finiteTwist : Module.Finite K (Algebra.FrobeniusTwist.twistObject K V p r) :=
    Algebra.FrobeniusTwist.moduleFinite K V p r
  rw [← range_frobeniusLinearMap K V p r]
  exact Module.Finite.range (frobeniusLinearMap K V p r)

end SymmetricAlgebra

namespace SymmetricAlgebra

section Field

variable (K : Type u) (V : Type v)
variable [Field K] [AddCommMonoid V] [Module K V]
variable (p r : ℕ) [ExpChar K p]

/-- For a vector space, Frobenius base extension is its original symmetric
pure-power span, without a choice of basis in the interface. -/
noncomputable def frobeniusEquivPurePowerSubmoduleOfField :
    Algebra.FrobeniusTwist.twistObject K V p r ≃ₗ[K]
      purePowerSubmodule K V (p ^ r) :=
  let free : Module.Free K V :=
    @Module.Free.of_divisionRing K V (inferInstance : DivisionRing K)
      (@Module.addCommMonoidToAddCommGroup K V
        (inferInstance : Ring K) ‹AddCommMonoid V› ‹Module K V›)
      ‹Module K V›
  frobeniusEquivPurePowerSubmodule K V p r

/-- The field comparison retains the coefficient and powers the original generator. -/
@[simp] theorem coe_frobeniusEquivPurePowerSubmoduleOfField_tmul (c : K) (v : V) :
    (frobeniusEquivPurePowerSubmoduleOfField K V p r
      (Algebra.FrobeniusTwist.tmul K V p r c v) : SymmetricAlgebra K V) =
      c • (ι K V v) ^ (p ^ r) := by
  let free : Module.Free K V :=
    @Module.Free.of_divisionRing K V (inferInstance : DivisionRing K)
      (@Module.addCommMonoidToAddCommGroup K V
        (inferInstance : Ring K) ‹AddCommMonoid V› ‹Module K V›)
      ‹Module K V›
  exact coe_frobeniusEquivPurePowerSubmodule_tmul K V p r c v

/-- The dimension of the Frobenius pure-power span equals that of the vector space. -/
theorem finrank_purePowerSubmodule :
    Module.finrank K (purePowerSubmodule K V (p ^ r)) = Module.finrank K V := by
  let free : Module.Free K V :=
    @Module.Free.of_divisionRing K V (inferInstance : DivisionRing K)
      (@Module.addCommMonoidToAddCommGroup K V
        (inferInstance : Ring K) ‹AddCommMonoid V› ‹Module K V›)
      ‹Module K V›
  let b := Module.Free.chooseBasis K V
  -- The same basis index is retained. This is base extension to the new
  -- coefficient field, not restriction along the old Frobenius action.
  let bF := Algebra.FrobeniusTwist.basis K V p r b
  calc
    Module.finrank K (purePowerSubmodule K V (p ^ r)) =
        Module.finrank K (Algebra.FrobeniusTwist.twistObject K V p r) :=
      (frobeniusEquivPurePowerSubmoduleOfField K V p r).finrank_eq.symm
    _ = Nat.card (Module.Free.ChooseBasisIndex K V) :=
      Module.finrank_eq_nat_card_basis bF
    _ = Module.finrank K V := (Module.finrank_eq_nat_card_basis b).symm

end Field

end SymmetricAlgebra
