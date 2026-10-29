/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.Transport
public import AlgebraicGroups.GroupScheme.Additive
public import Mathlib.Algebra.Polynomial.Basis
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.RingTheory.Polynomial.DegreeLT

/-!
# The polynomial regular comodule of the additive group

The regular comodule of `additiveGroupCoordinateRing K` is transported to
`Polynomial K` using `additiveGroupCoordinateAlgEquiv K`. Only the comodule
carrier changes: the coacting coalgebra remains the rank-one symmetric algebra,
with its existing comultiplication. The polynomial generator has coaction
`X ⊗ 1 + 1 ⊗ t`, where `t` is `additiveGroupCoordinate K`.

The submodules `Polynomial.degreeLT K (n + 1)` are stable, giving an increasing,
directed covering family of module-finite subcomodules over any commutative ring.
Their monomial bases give finrank `n + 1` over every nontrivial commutative ring,
and finite-dimensional stages over a field. Over a nontrivial base the ambient
module is not module-finite, and every stage is proper and nonzero.

## Implementation notes

This construction neither installs a coalgebra structure on `Polynomial K` nor
asserts a polynomial Hopf-algebra equivalence or a comparison with global sections
of the additive group scheme. The associated point-action convention is
`f(x) ↦ f(xg)`, hence translation `f(x + g)` for the additive group.

## References

- J. S. Milne, *Algebraic Groups* (2017), item 2.1 (primitive additive coordinate)
  and Chapter 4(c), Proposition 4.7/Corollary 4.8 (finite-dimensional subrepresentations).
- Mathlib, `Polynomial.degreeLT.basis` (Anne Baanen and Kenny Lau),
  `Polynomial.basisMonomials` (Jz Pan), and the binomial theorem `add_pow`.
- The fixed-coalgebra carrier transport and additive-coordinate APIs in this library.
-/

@[expose] public noncomputable section

open Coalgebra TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K]

/-- The additive group's regular right comodule on the polynomial carrier,
with its original symmetric-algebra coacting coalgebra. -/
def additiveGroupPolynomialComodule :
    RightComodule K (additiveGroupCoordinateRing K) (Polynomial K) :=
  (RightComodule.regular K (additiveGroupCoordinateRing K)).transport
    (additiveGroupCoordinateAlgEquiv K).toLinearEquiv

/-- Read back the transported regular coaction without changing the coalgebra factor. -/
theorem additiveGroupPolynomialComodule_coaction_apply (f : Polynomial K) :
    (additiveGroupPolynomialComodule K).coaction f =
      (additiveGroupCoordinateAlgEquiv K).toLinearMap.rTensor
        (additiveGroupCoordinateRing K)
        (comul ((additiveGroupCoordinateAlgEquiv K).symm f)) :=
  RightComodule.transport_coaction_apply _ _ f

/-- The polynomial regular coaction, bundled with its algebra-homomorphism structure. -/
def additiveGroupPolynomialCoaction :
    Polynomial K →ₐ[K] Polynomial K ⊗[K] additiveGroupCoordinateRing K :=
  (Algebra.TensorProduct.map (additiveGroupCoordinateAlgEquiv K).toAlgHom
    (AlgHom.id K (additiveGroupCoordinateRing K))).comp
      ((Bialgebra.comulAlgHom K (additiveGroupCoordinateRing K)).comp
        (additiveGroupCoordinateAlgEquiv K).symm.toAlgHom)

/-- The algebra map is the coaction of the transported regular comodule. -/
@[simp]
theorem additiveGroupPolynomialCoaction_apply (f : Polynomial K) :
    additiveGroupPolynomialCoaction K f =
      (additiveGroupPolynomialComodule K).coaction f := by
  have hmap :
      (Algebra.TensorProduct.map (additiveGroupCoordinateAlgEquiv K).toAlgHom
        (AlgHom.id K (additiveGroupCoordinateRing K))).toLinearMap =
      (additiveGroupCoordinateAlgEquiv K).toLinearMap.rTensor
        (additiveGroupCoordinateRing K) := by
    ext a b
    simp
  rw [additiveGroupPolynomialComodule_coaction_apply]
  change (Algebra.TensorProduct.map (additiveGroupCoordinateAlgEquiv K).toAlgHom
    (AlgHom.id K (additiveGroupCoordinateRing K))).toLinearMap _ = _
  rw [hmap]
  rfl

/-- The polynomial generator has the additive group's primitive coaction. -/
@[simp]
theorem additiveGroupPolynomialComodule_coaction_X :
    (additiveGroupPolynomialComodule K).coaction Polynomial.X =
      Polynomial.X ⊗ₜ[K] (1 : additiveGroupCoordinateRing K) +
        (1 : Polynomial K) ⊗ₜ[K] additiveGroupCoordinate K := by
  have hx : (additiveGroupCoordinateAlgEquiv K).symm Polynomial.X =
      additiveGroupCoordinate K := by
    apply (additiveGroupCoordinateAlgEquiv K).injective
    simp
  rw [additiveGroupPolynomialComodule_coaction_apply, hx,
    additiveGroupCoordinate_comul]
  simp

/-- The regular coaction is multiplicative on the polynomial carrier. -/
theorem additiveGroupPolynomialComodule_coaction_mul (f g : Polynomial K) :
    (additiveGroupPolynomialComodule K).coaction (f * g) =
      (additiveGroupPolynomialComodule K).coaction f *
        (additiveGroupPolynomialComodule K).coaction g := by
  simpa only [additiveGroupPolynomialCoaction_apply] using
    map_mul (additiveGroupPolynomialCoaction K) f g

/-- The binomial formula for the additive group's regular coaction on monomials. -/
theorem additiveGroupPolynomialComodule_coaction_X_pow (m : ℕ) :
    (additiveGroupPolynomialComodule K).coaction (Polynomial.X ^ m) =
      ∑ i ∈ Finset.range (m + 1), (m.choose i : K) •
        ((Polynomial.X ^ i) ⊗ₜ[K] (additiveGroupCoordinate K ^ (m - i))) := by
  rw [← additiveGroupPolynomialCoaction_apply, map_pow,
    additiveGroupPolynomialCoaction_apply, additiveGroupPolynomialComodule_coaction_X,
    add_pow]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [← nsmul_eq_mul', ← Nat.cast_smul_eq_nsmul K]
  simp only [Algebra.TensorProduct.tmul_pow, one_pow,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- Polynomials of degree at most `n` are stable for the polynomial regular coaction. -/
theorem additiveGroupPolynomialComodule_degreeLT_isStable (n : ℕ) :
    (additiveGroupPolynomialComodule K).IsStable (Polynomial.degreeLT K (n + 1)) := by
  classical
  intro f hf
  have hsum : f = ∑ j : Fin (n + 1),
      (Polynomial.degreeLT.basis K (n + 1)).repr ⟨f, hf⟩ j •
        (Polynomial.X ^ (j : ℕ)) := by
    simpa only [Submodule.coe_sum, Submodule.coe_smul, Polynomial.degreeLT.basis_val]
      using congrArg (fun p : Polynomial.degreeLT K (n + 1) ↦ (p : Polynomial K))
        ((Polynomial.degreeLT.basis K (n + 1)).sum_repr ⟨f, hf⟩).symm
  rw [hsum, map_sum]
  refine Submodule.sum_mem _ fun j hj ↦ ?_
  rw [map_smul]
  refine Submodule.smul_mem _ _ ?_
  rw [additiveGroupPolynomialComodule_coaction_X_pow]
  refine Submodule.sum_mem _ fun i hi ↦ Submodule.smul_mem _ _ ?_
  have hin : i < n + 1 :=
    (Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans_lt j.is_lt
  have hmem : Polynomial.X ^ i ∈ Polynomial.degreeLT K (n + 1) :=
    Polynomial.mem_degreeLT.mpr
      ((Polynomial.degree_X_pow_le i).trans_lt (WithBot.coe_lt_coe.mpr hin))
  exact ⟨(⟨Polynomial.X ^ i, hmem⟩ : Polynomial.degreeLT K (n + 1)) ⊗ₜ[K]
    (additiveGroupCoordinate K ^ ((j : ℕ) - i)), rfl⟩

/-- The degree-at-most-`n` subcomodule of the additive group's polynomial regular comodule. -/
def additiveGroupDegreeSubcomodule (n : ℕ) :
    (additiveGroupPolynomialComodule K).Subcomodule :=
  RightComodule.Subcomodule.ofIsStable _ (Polynomial.degreeLT K (n + 1))
    (additiveGroupPolynomialComodule_degreeLT_isStable K n)

/-- The degree subcomodule has exactly the usual polynomial degree submodule. -/
@[simp]
theorem additiveGroupDegreeSubcomodule_toSubmodule (n : ℕ) :
    (additiveGroupDegreeSubcomodule K n).toSubmodule = Polynomial.degreeLT K (n + 1) :=
  rfl

/-- Membership in a degree subcomodule is the polynomial degree bound. -/
@[simp]
theorem mem_additiveGroupDegreeSubcomodule (n : ℕ) (f : Polynomial K) :
    f ∈ additiveGroupDegreeSubcomodule K n ↔ f.degree < n + 1 :=
  Polynomial.mem_degreeLT

/-- The degree-stage coaction is the induced lift on the polynomial degree submodule. -/
@[simp]
theorem additiveGroupDegreeSubcomodule_coaction (n : ℕ) :
    ((additiveGroupDegreeSubcomodule K n).comodule.coaction :
      Polynomial.degreeLT K (n + 1) →ₗ[K]
        Polynomial.degreeLT K (n + 1) ⊗[K] additiveGroupCoordinateRing K) =
      RightComodule.Subcomodule.coactionLift (additiveGroupPolynomialComodule K)
        (Polynomial.degreeLT K (n + 1))
        (additiveGroupPolynomialComodule_degreeLT_isStable K n) :=
  RightComodule.Subcomodule.ofIsStable_coaction _ _ _

/-- The degree-stage coaction maps to the polynomial coaction under tensor inclusion. -/
theorem additiveGroupDegreeSubcomodule_coaction_apply (n : ℕ)
    (f : (additiveGroupDegreeSubcomodule K n).toSubmodule) :
    (additiveGroupDegreeSubcomodule K n).toSubmodule.subtype.rTensor
        (additiveGroupCoordinateRing K)
        ((additiveGroupDegreeSubcomodule K n).comodule.coaction f) =
      (additiveGroupPolynomialComodule K).coaction (f : Polynomial K) :=
  LinearMap.congr_fun (additiveGroupDegreeSubcomodule K n).subtype_colinear f

/-- The monomial basis of the degree subcomodule's subtype. -/
def additiveGroupDegreeSubcomoduleBasis (n : ℕ) :
    Module.Basis (Fin (n + 1)) K (additiveGroupDegreeSubcomodule K n).toSubmodule :=
  Polynomial.degreeLT.basis K (n + 1)

/-- The degree-stage basis is the monomial basis of the polynomial degree submodule. -/
@[simp]
theorem additiveGroupDegreeSubcomoduleBasis_eq_degreeLT_basis (n : ℕ) :
    (additiveGroupDegreeSubcomoduleBasis K n :
      Module.Basis (Fin (n + 1)) K (Polynomial.degreeLT K (n + 1))) =
        Polynomial.degreeLT.basis K (n + 1) := rfl

/-- The stage basis consists of the monomials through degree `n`. -/
theorem additiveGroupDegreeSubcomoduleBasis_val (n : ℕ) (i : Fin (n + 1)) :
    (additiveGroupDegreeSubcomoduleBasis K n i : Polynomial K) = Polynomial.X ^ (i : ℕ) :=
  Polynomial.degreeLT.basis_val i

instance additiveGroupDegreeSubcomodule_finite (n : ℕ) :
    Module.Finite K (additiveGroupDegreeSubcomodule K n).toSubmodule :=
  Module.Finite.of_basis (additiveGroupDegreeSubcomoduleBasis K n)

/-- The degree subcomodules form an increasing family. -/
theorem additiveGroupDegreeSubcomodule_monotone :
    Monotone (additiveGroupDegreeSubcomodule K) :=
  fun _ _ h ↦ Polynomial.degreeLT_mono (Nat.add_le_add_right h 1)

/-- Two degree subcomodules lie in a common degree subcomodule. -/
theorem additiveGroupDegreeSubcomodule_directed :
    Directed (· ≤ ·) (additiveGroupDegreeSubcomodule K) :=
  (additiveGroupDegreeSubcomodule_monotone K).directed_le

/-- Every polynomial belongs to its degree stage. -/
theorem mem_additiveGroupDegreeSubcomodule_natDegree (f : Polynomial K) :
    f ∈ additiveGroupDegreeSubcomodule K f.natDegree := by
  rw [mem_additiveGroupDegreeSubcomodule]
  exact (Polynomial.degree_le_natDegree).trans_lt (by exact_mod_cast Nat.lt_succ_self f.natDegree)

/-- The degree subcomodules exhaust the polynomial carrier. -/
theorem additiveGroupDegreeSubcomodule_iUnion :
    (⋃ n, (additiveGroupDegreeSubcomodule K n : Set (Polynomial K))) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro f
  exact Set.mem_iUnion.mpr ⟨f.natDegree, mem_additiveGroupDegreeSubcomodule_natDegree K f⟩

/-- Each degree stage contains the nonzero constant polynomial over a nontrivial base. -/
theorem additiveGroupDegreeSubcomodule_ne_bot [Nontrivial K] (n : ℕ) :
    additiveGroupDegreeSubcomodule K n ≠ ⊥ := by
  intro h
  have hmem : (1 : Polynomial K) ∈ additiveGroupDegreeSubcomodule K n := by
    rw [mem_additiveGroupDegreeSubcomodule, Polynomial.degree_one]
    exact_mod_cast Nat.zero_lt_succ n
  rw [h] at hmem
  exact one_ne_zero (show (1 : Polynomial K) = 0 from hmem)

/-- Each degree stage is a proper submodule over a nontrivial base. -/
theorem additiveGroupDegreeSubcomodule_toSubmodule_ne_top [Nontrivial K] (n : ℕ) :
    (additiveGroupDegreeSubcomodule K n).toSubmodule ≠ ⊤ := by
  intro h
  have hmem : (Polynomial.X ^ (n + 1) : Polynomial K) ∈
      (additiveGroupDegreeSubcomodule K n).toSubmodule := by rw [h]; trivial
  have hlt := (mem_additiveGroupDegreeSubcomodule K n _).mp hmem
  simp at hlt

/-- The polynomial regular comodule is not module-finite over a nontrivial base. -/
theorem additiveGroupPolynomialComodule_not_finite [Nontrivial K] :
    ¬ Module.Finite K (Polynomial K) := by
  intro h
  let := h
  exact Module.Finite.not_linearIndependent_of_infinite (Polynomial.basisMonomials K)
    (Polynomial.basisMonomials K).linearIndependent

/-- Over a nontrivial commutative ring, the degree-at-most-`n` stage has finrank `n + 1`. -/
theorem additiveGroupDegreeSubcomodule_finrank [Nontrivial K] (n : ℕ) :
    Module.finrank K (additiveGroupDegreeSubcomodule K n).toSubmodule = n + 1 := by
  simpa using Module.finrank_eq_card_basis (additiveGroupDegreeSubcomoduleBasis K n)

/-- Over a field, each degree stage is finite-dimensional. -/
theorem additiveGroupDegreeSubcomodule_finiteDimensional (K : Type u) [Field K] (n : ℕ) :
    FiniteDimensional K (additiveGroupDegreeSubcomodule K n).toSubmodule :=
  additiveGroupDegreeSubcomodule_finite K n

end AlgebraicGeometry
