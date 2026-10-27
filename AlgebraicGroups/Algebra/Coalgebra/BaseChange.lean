/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.CounitRange
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Coalgebra.Quotient
public import Mathlib.RingTheory.Coalgebra.TensorProduct

/-!
# The counit ideal and coideals under extension of scalars

For commutative semirings `R` and `S` with an `R`-algebra structure on `S`, the
canonical `S`-coalgebra on `S ⊗[R] C` has counit ideal equal to the extension of
the counit ideal of `C`. Neither flatness of `S` nor projectivity, freeness or
finite generation of `C` is required. The additive structure of `C` need only
be a commutative monoid, and the three types may lie in independent universes.

## References

Mathlib supplies the scalar-extension coalgebra and its counit formula, the
range of a tensored linear map, submodule scalar extension as a span, and
ideal extension. The proof combines these APIs rather than imposing an
injectivity condition on tensor products.

## Coideal scalar extension

Over commutative rings, extension of scalars preserves coideals, and faithfully
flat scalar extension reflects them. Only `CoalgebraStruct` on the source is
required; there are no coalgebra-law, field, finiteness or source/quotient-flatness
hypotheses. The scalar rings and the module retain independent universes.

The canonical tensor coalgebra data and `Submodule.baseChange` image carrier
already exist over commutative semirings. The ring/group boundary here comes
from Mathlib's quotient-based `Submodule.IsCoideal` predicate on both sides.
The proof compares the two quotient comultiplications using Mathlib's S-linear
`AlgebraTensorModule.tensorQuotientEquiv` and `distribBaseChange`. Reflection
uses `Module.FaithfullyFlat.one_tmul_eq_zero_iff`, on the scalar ring for the
counit and on the quotient tensor product for comultiplication.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

open scoped TensorProduct

namespace Coalgebra

variable (R : Type u) (S : Type v) (C : Type w)
variable [CommSemiring R] [CommSemiring S] [Algebra R S]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]

/-- The counit ideal of the canonical scalar-extension coalgebra is the extension
of the original counit ideal. This holds without flatness or freeness assumptions. -/
theorem counit_range_baseChange :
    (LinearMap.range (counit (R := S) (A := S ⊗[R] C)) : Ideal S) =
      Ideal.map (algebraMap R S) (LinearMap.range (counit (R := R) (A := C))) := by
  have hε : counit (R := S) (A := S ⊗[R] C) =
      (TensorProduct.AlgebraTensorModule.rid R S S).toLinearMap ∘ₗ
        (counit (R := R) (A := C)).baseChange S := by
    ext s
    simp [Algebra.smul_def]
  have hrange : LinearMap.range ((counit (R := R) (A := C)).baseChange S) =
      (LinearMap.range (counit (R := R) (A := C))).baseChange S := by
    apply Submodule.restrictScalars_injective R
    rw [← LinearMap.range_restrictScalars]
    change LinearMap.range ((counit (R := R) (A := C)).lTensor S) =
      LinearMap.range ((LinearMap.range (counit (R := R) (A := C))).subtype.lTensor S)
    exact LinearMap.lTensor_range S
  rw [hε, LinearMap.range_comp, hrange, Submodule.baseChange_eq_span,
    Submodule.map_span, Submodule.map_coe, Set.image_image, Ideal.submodule_span_eq]
  congr 1
  ext s
  simp [TensorProduct.AlgebraTensorModule.rid_tmul, Algebra.smul_def]

end Coalgebra

namespace Coalgebra

section WeakBaseChange

variable (R : Type u) (S : Type v) (C : Type w)
variable [CommSemiring R] [CommSemiring S] [Algebra R S]
variable [AddCommMonoid C] [Module R C] [CoalgebraStruct R C]

/-- The canonical scalar-extension comultiplication is the base change of the
source comultiplication, followed by the stock tensor-distribution equivalence.
Only the structure maps, not the coalgebra identities, are required. -/
theorem comul_baseChange :
    comul (R := S) (A := S ⊗[R] C) =
      (TensorProduct.AlgebraTensorModule.distribBaseChange R S C C).toLinearMap ∘ₗ
        (comul (R := R) (A := C)).baseChange S := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro s c
  simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearEquiv.coe_coe,
    TensorProduct.comul_tmul, CommSemiring.comul_apply]
  generalize comul (R := R) c = t
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
    rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
      TensorProduct.AlgebraTensorModule.distribBaseChange_tmul,
      TensorProduct.tmul_eq_smul_one_tmul s y, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add x y hx hy =>
    simp only [TensorProduct.tmul_add, map_add, hx, hy]

end WeakBaseChange

end Coalgebra

namespace Submodule.IsCoideal

section Weak

variable {R : Type u} {S : Type v} {C : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup C] [Module R C] [CoalgebraStruct R C]

-- The quotient comparison below is Mathlib's existing S-linear equivalence.
-- Its range is definitionally I.baseChange S: both maps are map id I.subtype.
-- No injectivity of S ⊗[R] I → S ⊗[R] C is asserted or needed.
private theorem map_mkQ_comul_baseChange_eq_zero_iff
    (I : Submodule R C) (s : S) (c : C) :
    TensorProduct.map (I.baseChange S).mkQ (I.baseChange S).mkQ
        (Coalgebra.comul (R := S) (s ⊗ₜ[R] c)) = 0 ↔
      s ⊗ₜ[R] (TensorProduct.map I.mkQ I.mkQ (Coalgebra.comul (R := R) c)) = 0 := by
  let e : S ⊗[R] (C ⧸ I) ≃ₗ[S] (S ⊗[R] C) ⧸ I.baseChange S :=
    TensorProduct.AlgebraTensorModule.tensorQuotientEquiv S R S I
  have he (a : S) (x : C) :
      e.symm ((I.baseChange S).mkQ (a ⊗ₜ[R] x)) = a ⊗ₜ[R] I.mkQ x :=
    TensorProduct.AlgebraTensorModule.tensorQuotientEquiv_symm_apply_mk_tmul S R S I a x
  let E := TensorProduct.congr e.symm e.symm ≪≫ₗ
    (TensorProduct.AlgebraTensorModule.distribBaseChange R S (C ⧸ I) (C ⧸ I)).symm
  have hE :
      E (TensorProduct.map (I.baseChange S).mkQ (I.baseChange S).mkQ
        (Coalgebra.comul (R := S) (s ⊗ₜ[R] c))) =
      s ⊗ₜ[R] (TensorProduct.map I.mkQ I.mkQ (Coalgebra.comul (R := R) c)) := by
    rw [Coalgebra.comul_baseChange R S C]
    simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul]
    generalize Coalgebra.comul (R := R) c = t
    induction t using TensorProduct.inductionOn with
    | tmul x y =>
      simp only [E, LinearEquiv.trans_apply, LinearEquiv.coe_coe,
        TensorProduct.AlgebraTensorModule.distribBaseChange_tmul,
        TensorProduct.map_tmul, TensorProduct.congr_tmul, he,
        TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul, mul_one]
    | add x y hx hy =>
      simp only [TensorProduct.tmul_add, map_add, hx, hy]
  constructor
  · intro h
    rw [h, map_zero] at hE
    exact hE.symm
  · intro h
    apply E.injective
    rw [hE, h, map_zero]

/-- Extension of scalars preserves a coideal for an arbitrary algebra of
commutative rings, with the canonical tensor coalgebra data and image submodule.
No coalgebra laws or flatness are assumed. -/
theorem baseChange {I : Submodule R C} (hI : I.IsCoideal) :
    (I.baseChange S).IsCoideal := by
  constructor
  · intro x hx
    obtain ⟨t, rfl⟩ := hx
    induction t using TensorProduct.inductionOn with
    | tmul s i =>
      change Coalgebra.counit (R := S) (s ⊗ₜ[R] (i : C)) = 0
      rw [TensorProduct.counit_tmul, hI.counit_eq_zero i.property, zero_smul]
    | add x y hx hy =>
      simp only [map_add, hx, hy, add_zero]
  · intro x hx
    obtain ⟨t, rfl⟩ := hx
    induction t using TensorProduct.inductionOn with
    | tmul s i =>
      change TensorProduct.map (I.baseChange S).mkQ (I.baseChange S).mkQ
        (Coalgebra.comul (R := S) (s ⊗ₜ[R] (i : C))) = 0
      apply (map_mkQ_comul_baseChange_eq_zero_iff I s (i : C)).mpr
      rw [hI.map_mkQ_comul_eq_zero i.property, TensorProduct.tmul_zero]
    | add x y hx hy =>
      simp only [map_add, hx, hy, add_zero]

/-- Faithfully flat scalar extension reflects a coideal. Faithful flatness is
imposed only on the scalar extension, not on the source module, the coideal or
its quotient. No coalgebra laws are required. -/
theorem of_baseChange [Module.FaithfullyFlat R S] {I : Submodule R C}
    (hI : (I.baseChange S).IsCoideal) : I.IsCoideal := by
  constructor
  · intro x hx
    have hε := hI.counit_eq_zero
      (Submodule.tmul_mem_baseChange_of_mem (1 : S) hx)
    apply (Module.FaithfullyFlat.one_tmul_eq_zero_iff R R
      (A := S) (Coalgebra.counit (R := R) x)).mp
    apply (TensorProduct.AlgebraTensorModule.rid R S S).injective
    simpa only [TensorProduct.AlgebraTensorModule.rid_tmul, map_zero,
      TensorProduct.counit_tmul, CommSemiring.counit_apply] using hε
  · intro x hx
    apply (Module.FaithfullyFlat.one_tmul_eq_zero_iff R ((C ⧸ I) ⊗[R] (C ⧸ I))
      (A := S) (TensorProduct.map I.mkQ I.mkQ (Coalgebra.comul (R := R) x))).mp
    exact (map_mkQ_comul_baseChange_eq_zero_iff I (1 : S) x).mp
      (hI.map_mkQ_comul_eq_zero
        (Submodule.tmul_mem_baseChange_of_mem (1 : S) hx))

end Weak

end Submodule.IsCoideal
