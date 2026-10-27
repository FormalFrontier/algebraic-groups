/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.BaseChange
public import AlgebraicGroups.Algebra.Coalgebra.Quotient
public import Mathlib.Algebra.Polynomial.Basis
public import Mathlib.RingTheory.Coalgebra.MonoidAlgebra

/-!
# A polynomial scalar extension of the rational augmentation coideal

There is one model: the stock diagonal coalgebra `AddMonoidAlgebra ℚ ℤ`,
extended from `ℚ` to `ℚ[X]`. Its augmentation submodule is exactly the kernel
of the coerced canonical counit coalgebra homomorphism. Both this submodule
and its stock base change are nonzero and proper. The extended nonzero witness
is `X ⊗ (e₀ - e₁)`, detected as `X` by an ordinary base-changed coefficient map.
Thus the extension is genuinely polynomial, the scalar ring is not a field,
and the coalgebra has infinitely many coordinate indices.

The model exercises both coideal preservation and faithfully flat reflection.
Its data, freeness, faithful flatness and coefficient detection use stock
constructions. The nonzero/proper carrier arguments are independent of the
coideal implications; exclusion of the unit tensor uses preservation.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped TensorProduct

namespace CoalgebraTest.CoidealBaseChange

/- The public model surface consists of the stock aliases and coefficient detector
used by the named conjunction below. The augmentation and coefficient-zero maps
remain private proof supports; exposed public bodies use their stock expressions. -/

/-- The polynomial scalar ring for the rational scalar extension. -/
public abbrev S := Polynomial ℚ

/-- The rational additive monoid algebra on the infinite index set `ℤ`, with its
stock diagonal coalgebra structure. -/
public abbrev C := AddMonoidAlgebra ℚ ℤ

private abbrev augmentation : C →ₗ[ℚ] ℚ :=
  (Coalgebra.counitCoalgHom ℚ C : C →ₗ[ℚ] ℚ)

/-- The rational augmentation submodule, the kernel of the canonical counit. -/
public abbrev I : Submodule ℚ C :=
  LinearMap.ker (Coalgebra.counitCoalgHom ℚ C : C →ₗ[ℚ] ℚ)

/-- The stock scalar-extension image of the augmentation submodule over `S`. -/
public abbrev J : Submodule S (S ⊗[ℚ] C) := I.baseChange S

/-- The stock single with rational coefficient `1` at the integer index `n`. -/
public abbrev e (n : ℤ) : C := AddMonoidAlgebra.single n 1

/-- The difference of the singles at `0` and `1`, a nonzero augmentation witness. -/
public abbrev k : C := e 0 - e 1

private def coefficientZero : C →ₗ[ℚ] ℚ :=
  (Finsupp.lapply (0 : ℤ)).comp (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

/-- The `S`-linear detector obtained by base-changing the rational coefficient at
`0` and applying the stock right-unit tensor equivalence. -/
public def detect : S ⊗[ℚ] C →ₗ[S] S :=
  (TensorProduct.AlgebraTensorModule.rid ℚ S S).toLinearMap.comp
    (((Finsupp.lapply (0 : ℤ)).comp
      (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap).baseChange S)

/-- On a pure tensor, the detector multiplies its scalar by the coefficient at `0`. -/
theorem detect_tmul (s : S) (c : C) :
    detect (s ⊗ₜ[ℚ] c) =
      ((Finsupp.lapply (0 : ℤ)).comp
        (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap) c • s := by
  simp only [detect, LinearMap.comp_apply, LinearMap.baseChange_tmul,
    LinearEquiv.coe_coe, TensorProduct.AlgebraTensorModule.rid_tmul]

/-- One faithful polynomial augmentation model, including an actual `X`-tensor
witness, nonzero/proper carriers, and clients of preservation and reflection. -/
theorem rational_polynomial_augmentation :
    Module.FaithfullyFlat ℚ S ∧
      I.IsCoideal ∧ k ∈ I ∧ k ≠ 0 ∧ I ≠ ⊥ ∧ I ≠ ⊤ ∧
      (Polynomial.X : S) ⊗ₜ[ℚ] k ∈ J ∧
      detect ((Polynomial.X : S) ⊗ₜ[ℚ] k) = Polynomial.X ∧
      (Polynomial.X : S) ⊗ₜ[ℚ] k ≠ 0 ∧ J ≠ ⊥ ∧ J ≠ ⊤ ∧
      Coalgebra.counit (R := S) ((1 : S) ⊗ₜ[ℚ] e 0) = 1 ∧
      (1 : S) ⊗ₜ[ℚ] e 0 ∉ J ∧ J.IsCoideal := by
  let : Module.Free ℚ S := Module.Free.of_basis (Polynomial.basisMonomials ℚ)
  have hFF : Module.FaithfullyFlat ℚ S := inferInstance
  let : Module.FaithfullyFlat ℚ S := hFF
  have hI : I.IsCoideal :=
    CoalgHomClass.ker_isCoideal (Coalgebra.counitCoalgHom ℚ C)
  have h₀ : augmentation (e 0) = (1 : ℚ) := by
    change Coalgebra.counitCoalgHom ℚ C
      (AddMonoidAlgebra.single (0 : ℤ) (1 : ℚ)) = 1
    rw [Coalgebra.counitCoalgHom_apply, AddMonoidAlgebra.counit_single,
      CommSemiring.counit_apply]
  have h₁ : augmentation (e 1) = (1 : ℚ) := by
    change Coalgebra.counitCoalgHom ℚ C
      (AddMonoidAlgebra.single (1 : ℤ) (1 : ℚ)) = 1
    rw [Coalgebra.counitCoalgHom_apply, AddMonoidAlgebra.counit_single,
      CommSemiring.counit_apply]
  have hkI : k ∈ I := by
    change augmentation (e 0 - e 1) = 0
    rw [map_sub, h₀, h₁, sub_self]
  have hc : coefficientZero k = (1 : ℚ) := by
    simp [coefficientZero, k, e]
  have hk : k ≠ 0 := by
    intro h
    have hzero : (1 : ℚ) = 0 := by
      simpa only [hc, map_zero] using congrArg coefficientZero h
    exact (one_ne_zero : (1 : ℚ) ≠ 0) hzero
  have hIbot : I ≠ ⊥ := by
    intro h
    exact hk ((Submodule.mem_bot ℚ).mp (h ▸ hkI))
  have hItop : I ≠ ⊤ := by
    intro h
    have hout : e 0 ∈ I := h.symm ▸ Submodule.mem_top
    have hzero : augmentation (e 0) = 0 := hout
    exact (one_ne_zero : (1 : ℚ) ≠ 0) (h₀.symm.trans hzero)
  have hXmem : (Polynomial.X : S) ⊗ₜ[ℚ] k ∈ J :=
    Submodule.tmul_mem_baseChange_of_mem _ hkI
  have hdetect : detect ((Polynomial.X : S) ⊗ₜ[ℚ] k) = Polynomial.X := by
    rw [detect_tmul]
    change coefficientZero k • (Polynomial.X : S) = Polynomial.X
    rw [hc, one_smul]
  have hX : (Polynomial.X : S) ⊗ₜ[ℚ] k ≠ 0 := by
    intro h
    apply (Polynomial.X_ne_zero : (Polynomial.X : S) ≠ 0)
    simpa only [hdetect, map_zero] using congrArg detect h
  have hJbot : J ≠ ⊥ := by
    intro h
    exact hX ((Submodule.mem_bot S).mp (h ▸ hXmem))
  have hJtop : J ≠ ⊤ := by
    intro h
    apply hItop
    apply (Submodule.baseChange_inj (A := S)).mp
    change I.baseChange S = ⊤ at h
    simpa only [Submodule.baseChange_top] using h
  have hJ : J.IsCoideal := Submodule.IsCoideal.baseChange (S := S) hI
  have hIreflected : I.IsCoideal := Submodule.IsCoideal.of_baseChange (S := S) hJ
  have hε : Coalgebra.counit (R := S) ((1 : S) ⊗ₜ[ℚ] e 0) = 1 := by
    rw [TensorProduct.counit_tmul]
    change Coalgebra.counit (R := ℚ)
      (AddMonoidAlgebra.single (0 : ℤ) (1 : ℚ)) •
        Coalgebra.counit (R := S) (1 : S) = 1
    rw [AddMonoidAlgebra.counit_single, CommSemiring.counit_apply,
      CommSemiring.counit_apply, one_smul]
  have houtJ : (1 : S) ⊗ₜ[ℚ] e 0 ∉ J := by
    intro hx
    exact (one_ne_zero : (1 : S) ≠ 0) (hε.symm.trans (hJ.counit_eq_zero hx))
  exact ⟨hFF, hIreflected, hkI, hk, hIbot, hItop, hXmem, hdetect, hX, hJbot,
    hJtop, hε, houtJ, hJ⟩

end CoalgebraTest.CoidealBaseChange
