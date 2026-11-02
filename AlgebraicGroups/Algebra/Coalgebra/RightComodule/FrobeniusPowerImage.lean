/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Bialgebra.RelativeFrobenius
public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.SymmetricAlgebra
public import AlgebraicGroups.Algebra.HopfAlgebra.Range
public import AlgebraicGroups.RingTheory.Flat.Field

/-!
# Pure-power coactions over the image of relative Frobenius

Let `K` be a field of prime characteristic `p`, let `A` be a commutative Hopf
`K`-algebra, and let `η` be a specified right coaction on a `K`-module `V`.
The submodule `SymmetricAlgebra.purePowerSubmodule K V (p ^ r)` carries the
induced coaction from `η.symmetricAlgebra`. Its coefficients lie in the
`K`-linear span of the `p ^ r`th powers in `A`, which is the algebra range of
`Bialgebra.relativeFrobenius K A p r`.

Restricting coefficients to this range gives a right comodule on the same
pure-power submodule. Inclusion of the range recovers the induced coaction,
and this equation determines the restricted coaction uniquely. The coefficient
coalgebra is the full coalgebra parent of `BialgHom.rangeHopfAlgebra`
on the ordinary algebra-range subtype. The finite-sum generator formula uses
`BialgHom.hopfRangeRestrict`, and inclusion uses `BialgHom.hopfRangeInclusion`.

## Implementation notes

The coefficient-first Frobenius tensor uses the original Frobenius-balanced
coefficient algebra. Its public ring structure retains the tensor-product semiring
at that algebra. The module `V` needs only an additive commutative
monoid structure and a `K`-module structure; no basis or finiteness assumption
is imposed. Flatness needed for the induced subtype coaction follows from the
field hypothesis.

## References

* Mathlib's tensor-product ring structures and iterated Frobenius.
* The Hopf-image, specified-comodule and coefficient-span APIs in
  `AlgebraicGroups.Algebra.HopfAlgebra.Range`,
  `AlgebraicGroups.Algebra.Coalgebra.RightComodule`, and
  `AlgebraicGroups.Algebra.Coalgebra.ComoduleCoefficients`.
* M. E. Sweedler, *Hopf Algebras* (1969), for right comodules and the
  coefficient method.
-/

@[expose] public noncomputable section

universe u a v w

open scoped TensorProduct BigOperators

namespace Coalgebra.RightComodule

variable {K : Type u} {A : Type a} {V : Type v}
variable [Field K] [CommSemiring A] [HopfAlgebra K A]
variable [AddCommMonoid V] [Module K V]
variable (p r : ℕ) (hp : p.Prime) (hchar : (p : K) = 0)

local notation "Eχ" =>
  @ExpChar.prime K (inferInstance : AddMonoidWithOne K) p hp
    (Iff.mpr (CharP.charP_iff_prime_eq_zero (R := K) hp) hchar)

local notation "Tφ" =>
  @Algebra.FrobeniusTwist.twistObject K A
    (inferInstance : CommSemiring K) (inferInstance : Semiring A)
    (inferInstance : Algebra K A) p r Eχ

local notation "Rτ" =>
  @Algebra.FrobeniusTwist.instRing K A
    (inferInstance : CommRing K) (inferInstance : Semiring A)
    (inferInstance : Algebra K A) p r Eχ

local notation "Hτ" =>
  @Algebra.FrobeniusTwist.instHopfAlgebra K A
    (inferInstance : CommSemiring K) (inferInstance : Semiring A)
    p r Eχ (inferInstance : HopfAlgebra K A)

local notation "Φ" =>
  @Bialgebra.relativeFrobenius K A
    (inferInstance : CommSemiring K) (inferInstance : CommSemiring A)
    (inferInstance : Bialgebra K A) p r Eχ

local notation "Bφ" => AlgHom.range (BialgHom.toAlgHom Φ)
local notation "Wq" => SymmetricAlgebra.purePowerSubmodule K V (p ^ r)

local notation "Hφ" =>
  @BialgHom.rangeHopfAlgebra K Tφ A
    (inferInstance : Field K) Rτ (inferInstance : Semiring A)
    Hτ (inferInstance : HopfAlgebra K A) Φ

local notation "jφ" =>
  @BialgHom.hopfRangeInclusion K Tφ A
    (inferInstance : Field K) Rτ (inferInstance : Semiring A)
    Hτ (inferInstance : HopfAlgebra K A) Φ

local notation "rφ" =>
  @BialgHom.hopfRangeRestrict K Tφ A
    (inferInstance : Field K) Rτ (inferInstance : Semiring A)
    Hτ (inferInstance : HopfAlgebra K A) Φ

private theorem purePower_coefficientSpan_le_range (η : RightComodule K A V) :
    (@purePowerSubcomodule K A V
      (inferInstance : CommSemiring K) (inferInstance : CommSemiring A)
      (inferInstance : Bialgebra K A)
      (inferInstance : AddCommMonoid V) (inferInstance : Module K V)
      (Module.Flat.of_field K A) η p r hp hchar).comodule.coefficientSpan ≤
        LinearMap.range (Φ).toLinearMap := by
  let : Module.Flat K A := Module.Flat.of_field K A
  let : ExpChar K p := Eχ
  change _ ≤ (Φ).toAlgHom.range.toSubmodule
  rw [Bialgebra.relativeFrobenius_range_eq_span_pow K A p r]
  exact η.coefficientSpan_purePowerSubcomodule_le_span_pow p r hp hchar

private theorem purePower_range_tensor_injective :
    Function.Injective ((jφ).toLinearMap.lTensor Wq) := by
  let : Module.Flat K Wq := Module.Flat.of_field K Wq
  rw [BialgHom.hopfRangeInclusion_toLinearMap]
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := Wq)
    (Φ).toAlgHom.range.val.toLinearMap Subtype.val_injective

/-- The pure-power submodule as a right comodule over the algebra range of
relative Frobenius, with its restricted range coalgebra. -/
noncomputable def purePowerRelativeFrobeniusComodule
    (η : RightComodule K A V) :
    @RightComodule K Bφ Wq
      (inferInstance : CommSemiring K)
      (inferInstance : AddCommMonoid Bφ) (inferInstance : Module K Bφ)
      (Hφ).toBialgebra.toCoalgebra
      (inferInstance : AddCommMonoid Wq) (inferInstance : Module K Wq) := by
  letI : AddCommGroup A := Module.addCommMonoidToAddCommGroup K
  letI : Module.Flat K A := Module.Flat.of_field K A
  let X : RightComodule K A Wq :=
    (η.purePowerSubcomodule p r hp hchar).comodule
  have hcoeff : X.coefficientSpan ≤ (Φ).toCoalgHom.range.toSubmodule := by
    rw [CoalgHom.range_toSubmodule]
    exact private_decl% (@purePower_coefficientSpan_le_range K A V
      (inferInstance : Field K) (inferInstance : CommSemiring A)
      (inferInstance : HopfAlgebra K A)
      (inferInstance : AddCommMonoid V) (inferInstance : Module K V) p r hp hchar η)
  exact X.restrictCoalgebra (Φ).toCoalgHom.range
    ((X.coaction_mem_range_iff_coefficientSpan_le _).2 hcoeff)

/-- Inclusion of the image coefficients recovers the induced pure-power coaction. -/
theorem purePowerRelativeFrobeniusComodule_coaction
    (η : RightComodule K A V) :
    (jφ).toLinearMap.lTensor Wq ∘ₗ
        (purePowerRelativeFrobeniusComodule
          (p := p) (r := r) (hp := hp) (hchar := hchar) η).coaction =
      (@purePowerSubcomodule K A V
        (inferInstance : CommSemiring K) (inferInstance : CommSemiring A)
        (inferInstance : Bialgebra K A)
        (inferInstance : AddCommMonoid V) (inferInstance : Module K V)
        (Module.Flat.of_field K A) η p r hp hchar).comodule.coaction := by
  let : AddCommGroup A := Module.addCommMonoidToAddCommGroup K
  let : Module.Flat K A := Module.Flat.of_field K A
  rw [BialgHom.hopfRangeInclusion_toLinearMap]
  exact subtype_lTensor_comp_restrictCoalgebra_coaction
    (η.purePowerSubcomodule p r hp hchar).comodule (Φ).toCoalgHom.range _

/-- Changing the image coefficients back recovers the specified induced comodule. -/
theorem purePowerRelativeFrobeniusComodule_mapCoalgebra
    (η : RightComodule K A V) :
    (purePowerRelativeFrobeniusComodule
      (p := p) (r := r) (hp := hp) (hchar := hchar) η).mapCoalgebra
        (jφ).toCoalgHom =
      (@purePowerSubcomodule K A V
        (inferInstance : CommSemiring K) (inferInstance : CommSemiring A)
        (inferInstance : Bialgebra K A)
        (inferInstance : AddCommMonoid V) (inferInstance : Module K V)
        (Module.Flat.of_field K A) η p r hp hchar).comodule := by
  apply RightComodule.ext
  rw [mapCoalgebra_coaction]
  exact purePowerRelativeFrobeniusComodule_coaction p r hp hchar η

/-- The inclusion equation uniquely determines the image coaction on the
pure-power submodule. -/
theorem existsUnique_purePowerRelativeFrobeniusComodule
    (η : RightComodule K A V) :
    ∃! β : @RightComodule K Bφ Wq
        (inferInstance : CommSemiring K)
        (inferInstance : AddCommMonoid Bφ) (inferInstance : Module K Bφ)
        (Hφ).toBialgebra.toCoalgebra
        (inferInstance : AddCommMonoid Wq) (inferInstance : Module K Wq),
      (jφ).toLinearMap.lTensor Wq ∘ₗ β.coaction =
        (@purePowerSubcomodule K A V
          (inferInstance : CommSemiring K) (inferInstance : CommSemiring A)
          (inferInstance : Bialgebra K A)
          (inferInstance : AddCommMonoid V) (inferInstance : Module K V)
          (Module.Flat.of_field K A) η p r hp hchar).comodule.coaction := by
  refine ⟨purePowerRelativeFrobeniusComodule p r hp hchar η,
    purePowerRelativeFrobeniusComodule_coaction p r hp hchar η, ?_⟩
  intro β hβ
  apply RightComodule.ext
  apply LinearMap.ext
  intro x
  apply purePower_range_tensor_injective p r hp hchar
  exact (LinearMap.congr_fun hβ x).trans
    (LinearMap.congr_fun (purePowerRelativeFrobeniusComodule_coaction p r hp hchar η) x).symm

local notation "powGen" => fun z : V ↦
  (Subtype.mk ((SymmetricAlgebra.ι K V z) ^ (p ^ r))
    (SymmetricAlgebra.ι_pow_mem_purePowerSubmodule K V (p ^ r) z) : Wq)

/-- Every finite expression for the original coaction gives the generator formula
with coefficients corestricted by relative Frobenius. Their ambient values are the
`p ^ r`th powers of the original coefficients. -/
theorem purePowerRelativeFrobeniusComodule_coaction_ι_pow_eq_sum
    (η : RightComodule K A V)
    {I : Type w} (s : Finset I) (vs : I → V) (coeff : I → A) (v : V)
    (hη : η.coaction v = ∑ i ∈ s, vs i ⊗ₜ[K] coeff i) :
    (purePowerRelativeFrobeniusComodule p r hp hchar η).coaction (powGen v) =
      ∑ i ∈ s, powGen (vs i) ⊗ₜ[K]
        rφ (@Algebra.FrobeniusTwist.tmul K A
          (inferInstance : CommSemiring K) (inferInstance : Semiring A)
          (inferInstance : Algebra K A) p r Eχ 1 (coeff i)) := by
  let : Module.Flat K A := Module.Flat.of_field K A
  let : ExpChar K p := Eχ
  apply purePower_range_tensor_injective p r hp hchar
  have hcoaction := LinearMap.congr_fun
    (purePowerRelativeFrobeniusComodule_coaction p r hp hchar η) (powGen v)
  simp only [LinearMap.comp_apply] at hcoaction
  rw [hcoaction]
  have hW : Function.Injective ((Wq).subtype.rTensor A) :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := A)
      (Wq).subtype Subtype.val_injective
  apply hW
  calc
    (Wq).subtype.rTensor A
        ((η.purePowerSubcomodule p r hp hchar).comodule.coaction (powGen v)) =
        η.symmetricAlgebraCoaction ((SymmetricAlgebra.ι K V v) ^ (p ^ r)) :=
      η.purePowerSubcomodule_coaction p r hp hchar (powGen v)
    _ = ∑ i ∈ s, ((SymmetricAlgebra.ι K V (vs i)) ^ (p ^ r)) ⊗ₜ[K]
        ((coeff i) ^ (p ^ r)) :=
      η.symmetricAlgebraCoaction_ι_pow_eq_sum p r hp hchar s vs coeff v hη
    _ = _ := by
      simp only [map_sum, LinearMap.lTensor_tmul, LinearMap.rTensor_tmul,
        BialgHom.hopfRangeInclusion_toLinearMap, AlgHom.toLinearMap_apply,
        Subalgebra.val_apply, BialgHom.hopfRangeRestrict_apply,
        AlgHom.coe_codRestrict, BialgHom.coe_toAlgHom, Bialgebra.relativeFrobenius_tmul,
        map_one, one_mul, Submodule.subtype_apply]

/-- A weight vector gives a weight vector in the original power span, with its
coefficient sent through the full relative-Frobenius range corestriction. -/
theorem purePowerRelativeFrobeniusComodule_coaction_ι_pow_of_coaction_eq
    (η : RightComodule K A V) (v : V) (a : A)
    (hη : η.coaction v = v ⊗ₜ[K] a) :
    (purePowerRelativeFrobeniusComodule p r hp hchar η).coaction (powGen v) =
      powGen v ⊗ₜ[K] rφ (@Algebra.FrobeniusTwist.tmul K A
        (inferInstance : CommSemiring K) (inferInstance : Semiring A)
        (inferInstance : Algebra K A) p r Eχ 1 a) := by
  classical
  simpa only [Finset.sum_singleton] using
    purePowerRelativeFrobeniusComodule_coaction_ι_pow_eq_sum p r hp hchar η
      {()} (fun _ : Unit ↦ v) (fun _ : Unit ↦ a) v
      (by simpa only [Finset.sum_singleton] using hη)

end Coalgebra.RightComodule
