/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.ComoduleCoefficients
public import AlgebraicGroups.Algebra.Coalgebra.RightComodule
public import AlgebraicGroups.Algebra.SymmetricAlgebra.PowerSpan
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Finite
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.RingTheory.Bialgebra.Basic

/-!
# Symmetric-algebra coactions and pure-power submodules

A specified right coaction of a commutative bialgebra extends to the symmetric
algebra by its universal property. The extension is an algebra homomorphism and
its underlying linear map is a specified right comodule. Colinear linear maps
induce algebra homomorphisms and morphisms of these specified comodules.

`SymmetricAlgebra.purePowerSubmodule K V n` is the original submodule spanned by
the `n`th powers of the generators, for every natural number `n`. It is independent
of any coaction or characteristic. If `p` is prime and `(p : K) = 0`, the submodule
for `n = p ^ r` is image-stable. Only the induced subtype coaction uses flatness
of the coacting bialgebra, through `RightComodule.Subcomodule.ofIsStable`.
The all-dual coefficients of this induced coaction lie in the linear span of
prime-power values in the coacting bialgebra.

## Implementation notes

No basis, antipode or finiteness assumption is needed for the coaction extension.
The power submodule need not be the whole homogeneous symmetric component. The field
nonvanishing and finite-dimensionality statements concern this original submodule,
not the whole symmetric algebra. These constructions do not include a relative
Frobenius image or a character-descent construction.

## References

* Mathlib's symmetric-algebra universal property, bialgebras and tensor products.
* M. E. Sweedler, *Hopf Algebras* (1969), for the right-comodule convention.
-/

@[expose] public section

universe u a v w z

open scoped TensorProduct BigOperators

namespace SymmetricAlgebra

section Field

variable {K : Type u} {V : Type v}
variable [Field K] [AddCommGroup V] [Module K V]

/-- A nonzero vector has nonzero powers in the symmetric algebra. Evaluation at
a linear functional taking the vector to `1` detects these powers. -/
theorem ι_pow_ne_zero {v : V} (hv : v ≠ 0) (n : ℕ) :
    (ι K V v) ^ n ≠ 0 := by
  obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_eq_one K hv
  intro h
  have h' : (1 : K) = 0 := by
    simpa only [map_pow, lift_ι_apply, hℓ, one_pow, map_zero] using
      congrArg (lift ℓ) h
  exact one_ne_zero h'

/-- A nonzero vector gives a nonzero original power submodule. -/
theorem purePowerSubmodule_ne_bot {v : V} (hv : v ≠ 0) (n : ℕ) :
    purePowerSubmodule K V n ≠ ⊥ := by
  intro h
  apply ι_pow_ne_zero (K := K) hv n
  have hmem := ι_pow_mem_purePowerSubmodule K V n v
  simpa only [h, Submodule.mem_bot] using hmem

/-- Finite-dimensionality of the original module implies finite-dimensionality
of each pure-power submodule, not of the whole symmetric algebra. -/
theorem finiteDimensional_purePowerSubmodule [FiniteDimensional K V] (n : ℕ) :
    FiniteDimensional K (purePowerSubmodule K V n) := by
  let f : PiTensorProduct K (fun _ : Fin n ↦ V) →ₗ[K] SymmetricAlgebra K V :=
    PiTensorProduct.lift
      ((MultilinearMap.mkPiAlgebraFin K n (SymmetricAlgebra K V)).compLinearMap
        (fun _ ↦ ι K V))
  apply Submodule.finiteDimensional_of_le (S₂ := LinearMap.range f)
  rw [purePowerSubmodule_eq_span]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨v, rfl⟩
  refine ⟨PiTensorProduct.tprod K (fun _ : Fin n ↦ v), ?_⟩
  simpa only [f, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply] using
    (MultilinearMap.mkPiAlgebraFin_apply_const (R := K) (n := n) (ι K V v))

end Field

end SymmetricAlgebra

namespace Coalgebra.RightComodule

variable {K : Type u} {A : Type a} {V : Type v}
variable [CommSemiring K] [CommSemiring A] [Bialgebra K A]
variable [AddCommMonoid V] [Module K V]

/-- The algebra coaction extending the given linear coaction on generators. -/
def symmetricAlgebraCoaction (η : RightComodule K A V) :
    SymmetricAlgebra K V →ₐ[K] SymmetricAlgebra K V ⊗[K] A :=
  SymmetricAlgebra.lift ((SymmetricAlgebra.ι K V).rTensor A ∘ₗ η.coaction)

/-- The extended algebra coaction agrees with the given coaction on generators. -/
@[simp] theorem symmetricAlgebraCoaction_ι (η : RightComodule K A V) (v : V) :
    η.symmetricAlgebraCoaction (SymmetricAlgebra.ι K V v) =
      (SymmetricAlgebra.ι K V).rTensor A (η.coaction v) :=
  SymmetricAlgebra.lift_ι_apply _ v

/-- The generator equation determines the algebra map uniquely. No coaction-law
hypothesis is needed for this uniqueness assertion. -/
theorem symmetricAlgebraCoaction_unique (η : RightComodule K A V)
    (δ : SymmetricAlgebra K V →ₐ[K] SymmetricAlgebra K V ⊗[K] A)
    (hδ : ∀ v : V, δ (SymmetricAlgebra.ι K V v) =
      (SymmetricAlgebra.ι K V).rTensor A (η.coaction v)) :
    δ = η.symmetricAlgebraCoaction := by
  apply SymmetricAlgebra.algHom_ext
  apply LinearMap.ext
  intro v
  exact (hδ v).trans (η.symmetricAlgebraCoaction_ι v).symm

-- Prove the laws among algebra homomorphisms first, so agreement on the
-- original linear generators suffices. The supplied comodule laws are used only
-- after the canonical tensor maps have transported the generator equation.
private theorem symmetricAlgebraCoaction_coassoc_algHom (η : RightComodule K A V) :
    (Algebra.TensorProduct.assoc K K K (SymmetricAlgebra K V) A A).toAlgHom.comp
        ((Algebra.TensorProduct.map η.symmetricAlgebraCoaction (AlgHom.id K A)).comp
          η.symmetricAlgebraCoaction) =
      (Algebra.TensorProduct.map (AlgHom.id K (SymmetricAlgebra K V))
        (Bialgebra.comulAlgHom K A)).comp η.symmetricAlgebraCoaction := by
  let S := SymmetricAlgebra K V
  let i : V →ₗ[K] S := SymmetricAlgebra.ι K V
  let d : S →ₐ[K] S ⊗[K] A := η.symmetricAlgebraCoaction
  have hi : d.toLinearMap ∘ₗ i = i.rTensor A ∘ₗ η.coaction :=
    LinearMap.ext (η.symmetricAlgebraCoaction_ι)
  have ht : d.toLinearMap.rTensor A ∘ₗ i.rTensor A =
      (i.rTensor A).rTensor A ∘ₗ η.coaction.rTensor A := by
    simpa only [LinearMap.rTensor_comp] using
      congrArg (fun l : V →ₗ[K] S ⊗[K] A ↦ l.rTensor A) hi
  have ha : (_root_.TensorProduct.assoc K S A A).toLinearMap ∘ₗ
        (i.rTensor A).rTensor A =
      i.rTensor (A ⊗[K] A) ∘ₗ (_root_.TensorProduct.assoc K V A A).toLinearMap := by
    simpa only [LinearMap.rTensor_def, TensorProduct.map_id] using
      (TensorProduct.map_map_comp_assoc_eq i
        (LinearMap.id : A →ₗ[K] A) (LinearMap.id : A →ₗ[K] A)).symm
  have hc : (comul (R := K) (A := A)).lTensor S ∘ₗ i.rTensor A =
      i.rTensor (A ⊗[K] A) ∘ₗ (comul (R := K) (A := A)).lTensor V := by
    rw [LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
  apply SymmetricAlgebra.algHom_ext
  apply LinearMap.ext
  intro v
  change _root_.TensorProduct.assoc K S A A
      (d.toLinearMap.rTensor A (d (i v))) =
    (comul (R := K) (A := A)).lTensor S (d (i v))
  rw [show d (i v) = i.rTensor A (η.coaction v) from η.symmetricAlgebraCoaction_ι v]
  calc
    _root_.TensorProduct.assoc K S A A
        (d.toLinearMap.rTensor A (i.rTensor A (η.coaction v))) =
        _root_.TensorProduct.assoc K S A A
          ((i.rTensor A).rTensor A (η.coaction.rTensor A (η.coaction v))) :=
      congrArg (_root_.TensorProduct.assoc K S A A) (LinearMap.congr_fun ht (η.coaction v))
    _ = i.rTensor (A ⊗[K] A)
        (_root_.TensorProduct.assoc K V A A (η.coaction.rTensor A (η.coaction v))) :=
      LinearMap.congr_fun ha (η.coaction.rTensor A (η.coaction v))
    _ = i.rTensor (A ⊗[K] A)
        ((comul (R := K) (A := A)).lTensor V (η.coaction v)) :=
      congrArg (i.rTensor (A ⊗[K] A)) (η.coassoc_apply v)
    _ = (comul (R := K) (A := A)).lTensor S (i.rTensor A (η.coaction v)) :=
      (LinearMap.congr_fun hc (η.coaction v)).symm

private theorem symmetricAlgebraCoaction_counit_algHom (η : RightComodule K A V) :
    (Algebra.TensorProduct.map (AlgHom.id K (SymmetricAlgebra K V))
        (Bialgebra.counitAlgHom K A)).comp η.symmetricAlgebraCoaction =
      (Algebra.TensorProduct.rid K K (SymmetricAlgebra K V)).symm.toAlgHom := by
  let S := SymmetricAlgebra K V
  let i : V →ₗ[K] S := SymmetricAlgebra.ι K V
  let d : S →ₐ[K] S ⊗[K] A := η.symmetricAlgebraCoaction
  have hc : (counit (R := K) (A := A)).lTensor S ∘ₗ i.rTensor A =
      i.rTensor K ∘ₗ (counit (R := K) (A := A)).lTensor V := by
    rw [LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
  apply SymmetricAlgebra.algHom_ext
  apply LinearMap.ext
  intro v
  change (counit (R := K) (A := A)).lTensor S (d (i v)) = i v ⊗ₜ[K] 1
  rw [show d (i v) = i.rTensor A (η.coaction v) from η.symmetricAlgebraCoaction_ι v]
  calc
    (counit (R := K) (A := A)).lTensor S (i.rTensor A (η.coaction v)) =
        i.rTensor K ((counit (R := K) (A := A)).lTensor V (η.coaction v)) :=
      LinearMap.congr_fun hc (η.coaction v)
    _ = i v ⊗ₜ[K] 1 := by
      simpa only [LinearMap.rTensor_tmul] using
        congrArg (i.rTensor K) (η.counit_coaction v)

/-- The specified right comodule on the symmetric algebra extending the given coaction. -/
def symmetricAlgebra (η : RightComodule K A V) :
    RightComodule K A (SymmetricAlgebra K V) where
  coaction := η.symmetricAlgebraCoaction.toLinearMap
  coassoc := by
    exact congrArg
      (fun h : SymmetricAlgebra K V →ₐ[K]
        SymmetricAlgebra K V ⊗[K] (A ⊗[K] A) ↦ h.toLinearMap)
      (symmetricAlgebraCoaction_coassoc_algHom η)
  counit_comp := by
    exact congrArg
      (fun h : SymmetricAlgebra K V →ₐ[K] SymmetricAlgebra K V ⊗[K] K ↦ h.toLinearMap)
      (symmetricAlgebraCoaction_counit_algHom η)

/-- Forgetting the algebra structure recovers the extended linear coaction. -/
@[simp] theorem symmetricAlgebra_coaction (η : RightComodule K A V) :
    η.symmetricAlgebra.coaction = η.symmetricAlgebraCoaction.toLinearMap := rfl

/-- The specified comodule has the characteristic generator equation. -/
theorem symmetricAlgebra_coaction_ι (η : RightComodule K A V) (v : V) :
    η.symmetricAlgebra.coaction (SymmetricAlgebra.ι K V v) =
      (SymmetricAlgebra.ι K V).rTensor A (η.coaction v) :=
  η.symmetricAlgebraCoaction_ι v

/-- Powers of a weight vector retain the value-wise powered coefficient.
This equation holds for every exponent and needs no characteristic assumption. -/
theorem symmetricAlgebraCoaction_ι_pow_of_coaction_eq
    (η : RightComodule K A V) (v : V) (a : A)
    (hη : η.coaction v = v ⊗ₜ[K] a) (n : ℕ) :
    η.symmetricAlgebraCoaction ((SymmetricAlgebra.ι K V v) ^ n) =
      ((SymmetricAlgebra.ι K V v) ^ n) ⊗ₜ[K] (a ^ n) := by
  rw [map_pow, symmetricAlgebraCoaction_ι, hη,
    LinearMap.rTensor_tmul, Algebra.TensorProduct.tmul_pow]

/-- Every finite tensor expression for the given coaction gives the same
prime-power formula for the extended algebra coaction. -/
theorem symmetricAlgebraCoaction_ι_pow_eq_sum (η : RightComodule K A V)
    (p r : ℕ) (hp : p.Prime) (hchar : (p : K) = 0)
    {I : Type w} (s : Finset I) (vs : I → V) (coeff : I → A) (v : V)
    (hη : η.coaction v = ∑ i ∈ s, vs i ⊗ₜ[K] coeff i) :
    η.symmetricAlgebraCoaction ((SymmetricAlgebra.ι K V v) ^ (p ^ r)) =
      ∑ i ∈ s, ((SymmetricAlgebra.ι K V (vs i)) ^ (p ^ r)) ⊗ₜ[K]
        ((coeff i) ^ (p ^ r)) := by
  rcases subsingleton_or_nontrivial (SymmetricAlgebra K V ⊗[K] A) with hT | hT
  · let _ := hT
    exact Subsingleton.elim _ _
  · let _ := hT
    have hcharT : (p : SymmetricAlgebra K V ⊗[K] A) = 0 := by
      simpa only [map_natCast, map_zero] using
        congrArg (algebraMap K (SymmetricAlgebra K V ⊗[K] A)) hchar
    let _ : CharP (SymmetricAlgebra K V ⊗[K] A) p :=
      (CharP.charP_iff_prime_eq_zero hp).2 hcharT
    let _ : ExpChar (SymmetricAlgebra K V ⊗[K] A) p := ExpChar.prime hp
    calc
      η.symmetricAlgebraCoaction ((SymmetricAlgebra.ι K V v) ^ (p ^ r)) =
          ((SymmetricAlgebra.ι K V).rTensor A (η.coaction v)) ^ (p ^ r) := by
        rw [map_pow, symmetricAlgebraCoaction_ι]
      _ = (∑ i ∈ s, SymmetricAlgebra.ι K V (vs i) ⊗ₜ[K] coeff i) ^ (p ^ r) := by
        simp only [hη, map_sum, LinearMap.rTensor_tmul]
      _ = ∑ i ∈ s, (SymmetricAlgebra.ι K V (vs i) ⊗ₜ[K] coeff i) ^ (p ^ r) :=
        sum_pow_char_pow p r s _
      _ = _ := by simp only [Algebra.TensorProduct.tmul_pow]

/-- The original prime-power submodule is image-stable for every one of its
members. Flatness is not required for this image-stability assertion. -/
theorem isStable_purePowerSubmodule (η : RightComodule K A V)
    (p r : ℕ) (hp : p.Prime) (hchar : (p : K) = 0) :
    η.symmetricAlgebra.IsStable (SymmetricAlgebra.purePowerSubmodule K V (p ^ r)) := by
  classical
  let U := SymmetricAlgebra.purePowerSubmodule K V (p ^ r)
  let E : Submodule K (SymmetricAlgebra K V ⊗[K] A) :=
    LinearMap.range (U.subtype.rTensor A)
  have hgen (v : V) :
      η.symmetricAlgebraCoaction ((SymmetricAlgebra.ι K V v) ^ (p ^ r)) ∈ E := by
    obtain ⟨s, hη⟩ := _root_.TensorProduct.exists_finset (η.coaction v)
    rw [η.symmetricAlgebraCoaction_ι_pow_eq_sum p r hp hchar s Prod.fst Prod.snd v hη]
    refine E.sum_mem fun i _ ↦ ?_
    refine ⟨(⟨(SymmetricAlgebra.ι K V i.1) ^ (p ^ r),
      SymmetricAlgebra.ι_pow_mem_purePowerSubmodule K V (p ^ r) i.1⟩ : U)
        ⊗ₜ[K] (i.2 ^ (p ^ r)), ?_⟩
    rfl
  have hle : U ≤ E.comap η.symmetricAlgebra.coaction := by
    apply (SymmetricAlgebra.purePowerSubmodule_le_iff K V (p ^ r)
      (E.comap η.symmetricAlgebra.coaction)).2
    intro v
    simpa only [Submodule.mem_comap, symmetricAlgebra_coaction, AlgHom.toLinearMap_apply]
      using hgen v
  exact (η.symmetricAlgebra.isStable_iff U).2 fun w hw ↦ hle hw

section Flat

variable [Module.Flat K A]

/-- The induced coaction on the exact original prime-power submodule.
Flatness is used only by the existing subtype restriction construction. -/
noncomputable def purePowerSubcomodule (η : RightComodule K A V)
    (p r : ℕ) (hp : p.Prime) (hchar : (p : K) = 0) : η.symmetricAlgebra.Subcomodule :=
  Subcomodule.ofIsStable η.symmetricAlgebra
    (SymmetricAlgebra.purePowerSubmodule K V (p ^ r))
    (η.isStable_purePowerSubmodule p r hp hchar)

/-- The induced subcomodule retains the original power submodule. -/
@[simp] theorem purePowerSubcomodule_toSubmodule (η : RightComodule K A V)
    (p r : ℕ) (hp : p.Prime) (hchar : (p : K) = 0) :
    (η.purePowerSubcomodule p r hp hchar).toSubmodule =
      SymmetricAlgebra.purePowerSubmodule K V (p ^ r) := rfl

/-- Inclusion of the induced subtype coaction is the extended ambient coaction. -/
theorem purePowerSubcomodule_coaction (η : RightComodule K A V)
    (p r : ℕ) (hp : p.Prime) (hchar : (p : K) = 0)
    (w : SymmetricAlgebra.purePowerSubmodule K V (p ^ r)) :
    (SymmetricAlgebra.purePowerSubmodule K V (p ^ r)).subtype.rTensor A
        ((η.purePowerSubcomodule p r hp hchar).comodule.coaction w) =
      η.symmetricAlgebraCoaction (w : SymmetricAlgebra K V) := by
  exact LinearMap.congr_fun
    (η.purePowerSubcomodule p r hp hchar).subtype_colinear w

/-- The coefficients of the pure-power subcomodule lie in the linear span of
prime-power values in the coefficient algebra. -/
theorem coefficientSpan_purePowerSubcomodule_le_span_pow
    (η : RightComodule K A V) (p r : ℕ)
    (hp : p.Prime) (hchar : (p : K) = 0) :
    (η.purePowerSubcomodule p r hp hchar).comodule.coefficientSpan ≤
      Submodule.span K (Set.range fun a : A ↦ a ^ (p ^ r)) := by
  classical
  let W := SymmetricAlgebra.purePowerSubmodule K V (p ^ r)
  let X : RightComodule K A W := (η.purePowerSubcomodule p r hp hchar).comodule
  let N : Submodule K A :=
    Submodule.span K (Set.range fun a : A ↦ a ^ (p ^ r))
  let w (v : V) : W :=
    ⟨(SymmetricAlgebra.ι K V v) ^ (p ^ r),
      SymmetricAlgebra.ι_pow_mem_purePowerSubmodule K V (p ^ r) v⟩
  have hinj : Function.Injective (W.subtype.rTensor A) :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := A)
      W.subtype Subtype.val_injective
  have hgen (ell : W →ₗ[K] K) (v : V) : X.coefficient ell (w v) ∈ N := by
    obtain ⟨s, hη⟩ := _root_.TensorProduct.exists_finset (η.coaction v)
    have hco : X.coaction (w v) =
        ∑ i ∈ s, w i.1 ⊗ₜ[K] (i.2 ^ (p ^ r)) := by
      apply hinj
      calc
        W.subtype.rTensor A (X.coaction (w v)) =
            η.symmetricAlgebraCoaction ((SymmetricAlgebra.ι K V v) ^ (p ^ r)) :=
          η.purePowerSubcomodule_coaction p r hp hchar (w v)
        _ = ∑ i ∈ s,
            ((SymmetricAlgebra.ι K V i.1) ^ (p ^ r)) ⊗ₜ[K]
              (i.2 ^ (p ^ r)) :=
          η.symmetricAlgebraCoaction_ι_pow_eq_sum p r hp hchar s Prod.fst Prod.snd v hη
        _ = W.subtype.rTensor A
            (∑ i ∈ s, w i.1 ⊗ₜ[K]
              (i.2 ^ (p ^ r))) := by
          simp only [map_sum, LinearMap.rTensor_tmul, Submodule.subtype_apply, w]
    rw [coefficient_eq, hco]
    simp only [map_sum, LinearMap.rTensor_tmul, _root_.TensorProduct.lid_tmul]
    exact N.sum_mem fun i _ ↦ N.smul_mem _ (Submodule.subset_span
      ⟨i.2, rfl⟩)
  apply (X.coefficientSpan_le_iff N).2
  intro ell x
  let f : W →ₗ[K] A := (X.coefficientHom ell).toLinearMap
  -- The ambient image of this linear coefficient preimage is a submodule.
  -- Containing every original power generator therefore contains their span.
  let E : Submodule K (SymmetricAlgebra K V) := (N.comap f).map W.subtype
  have hle : W ≤ E := by
    apply (SymmetricAlgebra.purePowerSubmodule_le_iff K V (p ^ r) E).2
    intro v
    exact ⟨w v, hgen ell v, rfl⟩
  obtain ⟨y, hy, hyx⟩ := hle x.property
  have hxy : y = x := Subtype.ext hyx
  change f x ∈ N
  rw [← hxy]
  exact hy

end Flat

end Coalgebra.RightComodule

namespace Coalgebra.RightComoduleHom

variable {K : Type u} {A : Type a} {V : Type v} {W : Type w} {U : Type z}
variable [CommSemiring K] [CommSemiring A] [Bialgebra K A]
variable [AddCommMonoid V] [Module K V] [AddCommMonoid W] [Module K W]
variable [AddCommMonoid U] [Module K U]
variable {η : RightComodule K A V} {θ : RightComodule K A W} {κ : RightComodule K A U}

private theorem symmetricAlgebra_colinear_algHom (f : RightComoduleHom η θ) :
    θ.symmetricAlgebraCoaction.comp (SymmetricAlgebra.map f.toLinearMap) =
      (Algebra.TensorProduct.map (SymmetricAlgebra.map f.toLinearMap)
        (AlgHom.id K A)).comp η.symmetricAlgebraCoaction := by
  have hi : (SymmetricAlgebra.map f.toLinearMap).toLinearMap ∘ₗ
        SymmetricAlgebra.ι K V =
      SymmetricAlgebra.ι K W ∘ₗ f.toLinearMap :=
    LinearMap.ext (SymmetricAlgebra.map_ι f.toLinearMap)
  have ht : (SymmetricAlgebra.map f.toLinearMap).toLinearMap.rTensor A ∘ₗ
        (SymmetricAlgebra.ι K V).rTensor A =
      (SymmetricAlgebra.ι K W).rTensor A ∘ₗ f.toLinearMap.rTensor A := by
    simpa only [LinearMap.rTensor_comp] using
      congrArg (fun l : V →ₗ[K] SymmetricAlgebra K W ↦ l.rTensor A) hi
  apply SymmetricAlgebra.algHom_ext
  apply LinearMap.ext
  intro v
  change θ.symmetricAlgebraCoaction
      (SymmetricAlgebra.map f.toLinearMap (SymmetricAlgebra.ι K V v)) =
    (SymmetricAlgebra.map f.toLinearMap).toLinearMap.rTensor A
      (η.symmetricAlgebraCoaction (SymmetricAlgebra.ι K V v))
  rw [SymmetricAlgebra.map_ι, θ.symmetricAlgebraCoaction_ι,
    η.symmetricAlgebraCoaction_ι]
  exact (congrArg ((SymmetricAlgebra.ι K W).rTensor A) (f.colinear_apply v)).trans
    (LinearMap.congr_fun ht (η.coaction v)).symm

/-- The induced algebra map, bundled in the existing right-comodule morphism model. -/
def symmetricAlgebra (f : RightComoduleHom η θ) :
    RightComoduleHom η.symmetricAlgebra θ.symmetricAlgebra where
  toLinearMap := (SymmetricAlgebra.map f.toLinearMap).toLinearMap
  colinear := by
    exact congrArg
      (fun h : SymmetricAlgebra K V →ₐ[K] SymmetricAlgebra K W ⊗[K] A ↦ h.toLinearMap)
      (symmetricAlgebra_colinear_algHom f)

/-- Forgetting colinearity gives the linear map of the induced algebra homomorphism. -/
@[simp] theorem symmetricAlgebra_toLinearMap (f : RightComoduleHom η θ) :
    f.symmetricAlgebra.toLinearMap = (SymmetricAlgebra.map f.toLinearMap).toLinearMap := rfl

/-- The bundled colinear map retains the generator equation. -/
@[simp] theorem symmetricAlgebra_ι (f : RightComoduleHom η θ) (v : V) :
    f.symmetricAlgebra (SymmetricAlgebra.ι K V v) = SymmetricAlgebra.ι K W (f v) :=
  SymmetricAlgebra.map_ι f.toLinearMap v

/-- The induced colinear maps preserve identities. -/
@[simp] theorem symmetricAlgebra_id (η : RightComodule K A V) :
    (id η).symmetricAlgebra = id η.symmetricAlgebra := by
  apply toLinearMap_injective
  exact congrArg AlgHom.toLinearMap (SymmetricAlgebra.map_id (K := K) (V := V))

/-- The induced colinear maps preserve composition. -/
@[simp] theorem symmetricAlgebra_comp (g : RightComoduleHom θ κ)
    (f : RightComoduleHom η θ) :
    (g.comp f).symmetricAlgebra = g.symmetricAlgebra.comp f.symmetricAlgebra := by
  apply toLinearMap_injective
  exact congrArg AlgHom.toLinearMap (SymmetricAlgebra.map_comp g.toLinearMap f.toLinearMap)

end Coalgebra.RightComoduleHom
