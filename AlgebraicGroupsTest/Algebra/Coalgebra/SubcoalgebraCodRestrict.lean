/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroupsTest.Algebra.Coalgebra.SubcoalgebraDiagonal

/-!
# Codomain restriction from comultiplication and counit data

The diagonal coalgebra on `ℕ →₀ K` has a nonzero proper finite-dimensional subcoalgebra
`D` supported on `{0, 1}`. On the module `D × K`, comultiplication and counit can instead
ignore the second coordinate. Projection onto `D` preserves both maps, and its composite
with the inclusion has range exactly `D`, although it has the nonzero kernel vector
`(0, 1)`. The left counit identity fails at this vector.

The characteristic laws of codomain restriction, uniqueness of factorization, and
precomposition are considered for sources carrying only comultiplication and counit.
The ambient coalgebra and its subcoalgebra retain their full canonical structures.

## Implementation notes

A type synonym distinguishes the projected structure maps from the usual product
coalgebra. It inherits only the additive monoid and module instances; no coalgebra
laws are supplied for these structure maps. The same underlying module admits the
different, usual product coalgebra, but the specified projected comultiplication and
counit fail the left counit law. The finite proper subcoalgebra is chosen from
`Coalgebra.exists_finite_proper_subcoalgebra_finsupp_nat`.

## References

The proper finite-dimensional part is provided by
`AlgebraicGroupsTest.Algebra.Coalgebra.SubcoalgebraDiagonal`. Preservation-only bundled
maps use `Mathlib.RingTheory.Coalgebra.Hom`, and restriction and factorization use
`AlgebraicGroups.Algebra.Coalgebra.Subcoalgebra.Hom`.
-/

@[expose] public section

noncomputable section

universe u v w w₁

open scoped TensorProduct

namespace Coalgebra

variable (K : Type u) [Field K]

/-- A nonzero proper finite-dimensional part of the diagonal coalgebra. -/
private def supportedPart : Subcoalgebra K (ℕ →₀ K) :=
  (exists_finite_proper_subcoalgebra_finsupp_nat K).choose

private lemma supportedPart_spec :
    (supportedPart K).toSubmodule = Finsupp.supported K K ({0, 1} : Set ℕ) ∧
      (supportedPart K).toSubmodule ≠ ⊥ ∧ (supportedPart K).toSubmodule ≠ ⊤ ∧
      (supportedPart K).toSubmodule.FG ∧ Module.Finite K (supportedPart K) ∧
      ¬ Module.Finite K (ℕ →₀ K) ∧
      Finsupp.single 0 (1 : K) ∈ supportedPart K ∧
      Finsupp.single 1 (1 : K) ∈ supportedPart K :=
  (exists_finite_proper_subcoalgebra_finsupp_nat K).choose_spec

/-- The module on which the second coordinate is ignored by the structure maps. -/
private def projectedSource (D : Subcoalgebra K (ℕ →₀ K)) : Type u := D × K

private instance projectedSourceAddCommMonoid (D : Subcoalgebra K (ℕ →₀ K)) :
    AddCommMonoid (projectedSource K D) :=
  inferInstanceAs (AddCommMonoid (D × K))

private instance projectedSourceModule (D : Subcoalgebra K (ℕ →₀ K)) :
    Module K (projectedSource K D) :=
  inferInstanceAs (Module K (D × K))

private def firstProjection (D : Subcoalgebra K (ℕ →₀ K)) :
    projectedSource K D →ₗ[K] D :=
  LinearMap.fst K D K

private def firstInclusion (D : Subcoalgebra K (ℕ →₀ K)) :
    D →ₗ[K] projectedSource K D :=
  LinearMap.inl K D K

private lemma firstProjection_comp_firstInclusion (D : Subcoalgebra K (ℕ →₀ K)) :
    firstProjection K D ∘ₗ firstInclusion K D = LinearMap.id :=
  rfl

private instance projectedSourceCoalgebraStruct (D : Subcoalgebra K (ℕ →₀ K)) :
    CoalgebraStruct K (projectedSource K D) where
  comul := _root_.TensorProduct.map (firstInclusion K D) (firstInclusion K D) ∘ₗ
    comul (R := K) (A := D) ∘ₗ firstProjection K D
  counit := counit (R := K) (A := D) ∘ₗ firstProjection K D

/-- Projection preserves the specified comultiplication and counit. -/
private def firstProjectionHom (D : Subcoalgebra K (ℕ →₀ K)) :
    projectedSource K D →ₗc[K] D where
  toLinearMap := firstProjection K D
  counit_comp := rfl
  map_comp_comul := by
    apply LinearMap.ext
    intro x
    change _root_.TensorProduct.map (firstProjection K D) (firstProjection K D)
        (_root_.TensorProduct.map (firstInclusion K D) (firstInclusion K D)
          (comul (R := K) (A := D) (firstProjection K D x))) =
      comul (R := K) (A := D) (firstProjection K D x)
    rw [TensorProduct.map_map, firstProjection_comp_firstInclusion,
      TensorProduct.map_id, LinearMap.id_apply]

private def firstInclusionHom (D : Subcoalgebra K (ℕ →₀ K)) :
    D →ₗc[K] projectedSource K D where
  toLinearMap := firstInclusion K D
  counit_comp := rfl
  map_comp_comul := rfl

/-- A nonidentity endomorphism that erases the second coordinate. -/
private def eraseSecond (D : Subcoalgebra K (ℕ →₀ K)) :
    projectedSource K D →ₗc[K] projectedSource K D :=
  (firstInclusionHom K D).comp (firstProjectionHom K D)

/-- Projection into the ambient infinite-dimensional diagonal coalgebra. -/
private def ambientProjection (D : Subcoalgebra K (ℕ →₀ K)) :
    projectedSource K D →ₗc[K] (ℕ →₀ K) :=
  D.subtype.comp (firstProjectionHom K D)

private lemma ambientProjection_mem (D : Subcoalgebra K (ℕ →₀ K))
    (x : projectedSource K D) : ambientProjection K D x ∈ D :=
  Subcoalgebra.coe_mem (firstProjectionHom K D x)

private lemma ambientProjection_range (D : Subcoalgebra K (ℕ →₀ K)) :
    LinearMap.range (ambientProjection K D).toLinearMap = D.toSubmodule := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    exact (Subcoalgebra.mem_iff D).mp (ambientProjection_mem K D x)
  · intro y hy
    exact ⟨(⟨y, (Subcoalgebra.mem_iff D).mpr hy⟩, 0), rfl⟩

private lemma ambientProjection_ne_zero :
    (ambientProjection K (supportedPart K)).toLinearMap ≠ 0 := by
  intro h
  apply (supportedPart_spec K).2.1
  rw [← ambientProjection_range K (supportedPart K), h, LinearMap.range_zero]

private lemma ambientProjection_range_ne_top :
    LinearMap.range (ambientProjection K (supportedPart K)).toLinearMap ≠ ⊤ := by
  rw [ambientProjection_range]
  exact (supportedPart_spec K).2.2.1

private lemma firstProjectionHom_ne_zero :
    (firstProjectionHom K (supportedPart K)).toLinearMap ≠ 0 := by
  intro h
  apply ambientProjection_ne_zero K
  change (supportedPart K).subtype.toLinearMap ∘ₗ
    (firstProjectionHom K (supportedPart K)).toLinearMap = 0
  rw [h, LinearMap.comp_zero]

private def kernelVector (D : Subcoalgebra K (ℕ →₀ K)) : projectedSource K D :=
  (0, 1)

private lemma kernelVector_ne_zero (D : Subcoalgebra K (ℕ →₀ K)) :
    kernelVector K D ≠ 0 := by
  intro h
  exact (one_ne_zero : (1 : K) ≠ 0)
    (congrArg (fun x : projectedSource K D => (x : D × K).2) h)

private lemma ambientProjection_kernelVector (D : Subcoalgebra K (ℕ →₀ K)) :
    ambientProjection K D (kernelVector K D) = 0 :=
  rfl

private lemma ambientProjection_not_injective (D : Subcoalgebra K (ℕ →₀ K)) :
    ¬ Function.Injective (ambientProjection K D) := by
  intro h
  exact kernelVector_ne_zero K D (h (by rfl))

private lemma firstProjectionHom_not_injective (D : Subcoalgebra K (ℕ →₀ K)) :
    ¬ Function.Injective (firstProjectionHom K D) := by
  intro h
  exact kernelVector_ne_zero K D (h (by rfl))

private lemma ambientProjection_comp_eraseSecond (D : Subcoalgebra K (ℕ →₀ K)) :
    (ambientProjection K D).comp (eraseSecond K D) = ambientProjection K D :=
  CoalgHom.ext fun _ => rfl

private lemma eraseSecond_ne_id (D : Subcoalgebra K (ℕ →₀ K)) :
    eraseSecond K D ≠ CoalgHom.id K (projectedSource K D) := by
  intro h
  have hx := CoalgHom.congr_fun h (kernelVector K D)
  exact kernelVector_ne_zero K D hx.symm

/-- The left counit identity fails on the nonzero vector in the projection kernel. -/
private lemma projectedSource_left_counit_failure (D : Subcoalgebra K (ℕ →₀ K)) :
    (counit (R := K) (A := projectedSource K D)).rTensor (projectedSource K D)
        (comul (R := K) (A := projectedSource K D) (kernelVector K D)) ≠
      (1 : K) ⊗ₜ[K] kernelVector K D := by
  have hc : comul (R := K) (A := projectedSource K D) (kernelVector K D) = 0 := by
    change _root_.TensorProduct.map (firstInclusion K D) (firstInclusion K D)
      (comul (R := K) (A := D) 0) = 0
    rw [map_zero, map_zero]
  intro h
  rw [hc, map_zero] at h
  have hx : (0 : projectedSource K D) = kernelVector K D := by
    simpa only [map_zero, _root_.TensorProduct.lid_tmul, one_smul] using
      congrArg (_root_.TensorProduct.lid K (projectedSource K D)) h
  exact kernelVector_ne_zero K D hx.symm

end Coalgebra

namespace Subcoalgebra

variable {K : Type u} {C : Type v} {A : Type w}
variable [Field K] [AddCommGroup C] [Module K C] [Coalgebra K C]
variable [AddCommMonoid A] [Module K A] [CoalgebraStruct K A]

/-- Underlying linear maps, values, and recovery by inclusion for codomain restriction. -/
private def restrictionContract (f : A →ₗc[K] C) (D : Subcoalgebra K C)
    (h : ∀ x, f x ∈ D) : Prop :=
  (f.codRestrict D h).toLinearMap = f.toLinearMap.codRestrict D.toSubmodule h ∧
    (∀ x, f.codRestrict D h x = ⟨f x, h x⟩) ∧
    (∀ x, (f.codRestrict D h x : C) = f x) ∧
    D.subtype.comp (f.codRestrict D h) = f

private lemma restrictionClient (f : A →ₗc[K] C) (D : Subcoalgebra K C)
    (h : ∀ x, f x ∈ D) : restrictionContract f D h :=
  ⟨CoalgHom.codRestrict_toLinearMap f D h, CoalgHom.codRestrict_apply f D h,
    CoalgHom.coe_codRestrict f D h, CoalgHom.subtype_comp_codRestrict f D h⟩

-- The laws of `coalgHom_ext`, `subtype_comp_injective`, and `subtype_comp_inj`.
/-- Ambient values determine a map into a subcoalgebra, as does its composite inclusion. -/
private def extensionalityContract (D : Subcoalgebra K C) : Prop :=
  (∀ f g : A →ₗc[K] D, (∀ x, (f x : C) = (g x : C)) → f = g) ∧
    Function.Injective (fun f : A →ₗc[K] D => D.subtype.comp f) ∧
    (∀ f g : A →ₗc[K] D, D.subtype.comp f = D.subtype.comp g ↔ f = g)

private lemma extensionalityClient (D : Subcoalgebra K C) :
    extensionalityContract (A := A) D :=
  ⟨fun _ _ h => coalgHom_ext h, subtype_comp_injective D,
    fun f g => subtype_comp_inj D (f := f) (g := g)⟩

-- The laws of `CoalgHom.codRestrict_subtype_comp` and `CoalgHom.codRestrict_unique`.
/-- Restriction recovers a map into a subcoalgebra and identifies any factorization. -/
private def factorizationContract (f : A →ₗc[K] C) (D : Subcoalgebra K C)
    (h : ∀ x, f x ∈ D) : Prop :=
  (∀ g : A →ₗc[K] D,
      (D.subtype.comp g).codRestrict D (fun x => Subcoalgebra.coe_mem (g x)) = g) ∧
    (∀ g : A →ₗc[K] D, D.subtype.comp g = f → g = f.codRestrict D h)

private lemma factorizationClient (f : A →ₗc[K] C) (D : Subcoalgebra K C)
    (h : ∀ x, f x ∈ D) : factorizationContract f D h :=
  ⟨CoalgHom.codRestrict_subtype_comp D,
    fun g hg => CoalgHom.codRestrict_unique f D h g hg⟩

-- The law of `CoalgHom.existsUnique_subtype_comp_iff`.
/-- Unique factorization through inclusion is equivalent to membership of all values. -/
private def uniqueFactorizationContract (f : A →ₗc[K] C) (D : Subcoalgebra K C) : Prop :=
  (∃! g : A →ₗc[K] D, D.subtype.comp g = f) ↔ ∀ x, f x ∈ D

private lemma uniqueFactorizationClient (f : A →ₗc[K] C) (D : Subcoalgebra K C) :
    uniqueFactorizationContract f D :=
  CoalgHom.existsUnique_subtype_comp_iff f D

-- The law of `CoalgHom.codRestrict_inj`.
/-- Restriction detects equality of homomorphisms whose values lie in the subcoalgebra. -/
private def restrictionInjectivityContract (D : Subcoalgebra K C)
    (f g : A →ₗc[K] C) (hf : ∀ x, f x ∈ D) (hg : ∀ x, g x ∈ D) : Prop :=
  f.codRestrict D hf = g.codRestrict D hg ↔ f = g

private lemma restrictionInjectivityClient (D : Subcoalgebra K C)
    (f g : A →ₗc[K] C) (hf : ∀ x, f x ∈ D) (hg : ∀ x, g x ∈ D) :
    restrictionInjectivityContract D f g hf hg :=
  CoalgHom.codRestrict_inj D hf hg

variable {B : Type w₁} [AddCommMonoid B] [Module K B] [CoalgebraStruct K B]

-- The law of `CoalgHom.codRestrict_comp`.
/-- Codomain restriction commutes with precomposition between structure-only sources. -/
private def precompositionContract (f : B →ₗc[K] C) (g : A →ₗc[K] B)
    (D : Subcoalgebra K C) (h : ∀ y, f y ∈ D) : Prop :=
  (f.comp g).codRestrict D (fun x => h (g x)) = (f.codRestrict D h).comp g

private lemma precompositionClient (f : B →ₗc[K] C) (g : A →ₗc[K] B)
    (D : Subcoalgebra K C) (h : ∀ y, f y ∈ D) : precompositionContract f g D h :=
  CoalgHom.codRestrict_comp f g D h

end Subcoalgebra

namespace CoalgebraTest

variable {K : Type u} {C : Type v} {F : Type w}
variable [Field K] [AddCommGroup C] [Module K C] [Coalgebra K C]
variable [AddCommGroup F] [Module K F] [Coalgebra K F]

/-- For a source with coalgebra laws, restriction recovers maps into a subcoalgebra,
unique factorization is equivalent to membership of all values, and restricting the
inclusion gives the identity. -/
theorem codRestrict_full_source_specialization (f : F →ₗc[K] C) (D : Subcoalgebra K C) :
    (∀ g : F →ₗc[K] D,
      (D.subtype.comp g).codRestrict D (fun x => Subcoalgebra.coe_mem (g x)) = g) ∧
    ((∃! g : F →ₗc[K] D, D.subtype.comp g = f) ↔ ∀ x, f x ∈ D) ∧
    D.subtype.codRestrict D (fun x => Subcoalgebra.coe_mem x) = CoalgHom.id K D :=
  ⟨CoalgHom.codRestrict_subtype_comp D, CoalgHom.existsUnique_subtype_comp_iff f D,
    CoalgHom.codRestrict_subtype D⟩

end CoalgebraTest

namespace Coalgebra

variable (K : Type u) [Field K]

/-- Restriction of the nonzero noninjective projection, including nonidentity precomposition. -/
private def projectedRestrictionContract : Prop :=
  let D := supportedPart K
  let f := ambientProjection K D
  let h := ambientProjection_mem K D
  Subcoalgebra.restrictionContract f D h ∧
    Subcoalgebra.extensionalityContract (A := projectedSource K D) D ∧
    Subcoalgebra.factorizationContract f D h ∧
    Subcoalgebra.uniqueFactorizationContract f D ∧
    f.codRestrict D h = firstProjectionHom K D ∧
    (f.codRestrict D h).toLinearMap ≠ 0 ∧
    ¬ Function.Injective (f.codRestrict D h) ∧
    f.codRestrict D h (kernelVector K D) = 0 ∧
    (∃! g : projectedSource K D →ₗc[K] D, D.subtype.comp g = f) ∧
    Subcoalgebra.restrictionInjectivityContract D f (f.comp (eraseSecond K D)) h
      (fun x => h (eraseSecond K D x)) ∧
    Subcoalgebra.precompositionContract f (eraseSecond K D) D h

private lemma projectedRestrictionClient : projectedRestrictionContract K := by
  let D := supportedPart K
  let f := ambientProjection K D
  let h := ambientProjection_mem K D
  have hr : f.codRestrict D h = firstProjectionHom K D :=
    CoalgHom.codRestrict_subtype_comp D (firstProjectionHom K D)
  refine ⟨Subcoalgebra.restrictionClient f D h,
    Subcoalgebra.extensionalityClient (A := projectedSource K D) D,
    Subcoalgebra.factorizationClient f D h, Subcoalgebra.uniqueFactorizationClient f D,
    hr, ?_, ?_, ?_, (CoalgHom.existsUnique_subtype_comp_iff f D).mpr h,
    Subcoalgebra.restrictionInjectivityClient D f (f.comp (eraseSecond K D)) h
      (fun x => h (eraseSecond K D x)),
    CoalgHom.codRestrict_comp f (eraseSecond K D) D h⟩
  · rw [hr]
    exact firstProjectionHom_ne_zero K
  · rw [hr]
    exact firstProjectionHom_not_injective K D
  · rw [hr]
    rfl

end Coalgebra
