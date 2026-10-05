/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.Unitriangular
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.GroupTheory.Exponent

/-!
# Prime-power exponents of upper-unitriangular matrix groups

The exponent bound and its sharpness concern the native group
`Matrix.UnitriangularGroup (Fin n) R`, over a commutative ring.
The bound uses Cayley–Hamilton for strictly upper-triangular matrices and a
commuting prime-power identity; sharpness uses a consecutive superdiagonal
shift. Neither conclusion is a group-scheme exponent statement.

## References

- Mathlib contributors, `Mathlib.LinearAlgebra.Matrix.Charpoly.Basic`
  (triangular characteristic polynomial and Cayley–Hamilton),
  `Mathlib.Algebra.CharP.Lemmas` (commuting prime-power identity) and
  `Mathlib.GroupTheory.Exponent` (uniform exponent divisibility).
-/

@[expose] public section

noncomputable section

namespace Matrix

/-- A strictly upper-triangular matrix over a commutative ring vanishes at the
power given by the number of its indices, including for an empty index type.
The proof applies Cayley–Hamilton as formalized by Mathlib's
`Matrix.aeval_self_charpoly` to its triangular characteristic polynomial. -/
theorem pow_card_eq_zero_of_upperTriangular_diag_zero
    {ι R : Type*} [Fintype ι] [LinearOrder ι] [CommRing R]
    (N : Matrix ι ι R) (hupper : N.IsUpperTriangular)
    (hdiag : ∀ i, N i i = 0) : N ^ Fintype.card ι = 0 := by
  classical
  have hpoly : N.charpoly = Polynomial.X ^ Fintype.card ι := by
    rw [N.charpoly_of_isUpperTriangular hupper]
    simp [hdiag]
  simpa [hpoly] using N.aeval_self_charpoly

namespace UnitriangularGroup

/-- The consecutive superdiagonal shift, used for the sharpness witness. -/
private def shift (n : ℕ) (R : Type) [CommRing R] :
    Matrix (Fin n) (Fin n) R := fun i j =>
  if j.val = i.val + 1 then 1 else 0

private theorem shift_pow_apply (n : ℕ) (R : Type) [CommRing R]
    (k : ℕ) (i j : Fin n) :
    (shift n R ^ k) i j = if j.val = i.val + k then 1 else 0 := by
  classical
  induction k generalizing i j with
  | zero =>
    simp only [pow_zero, Matrix.one_apply, Nat.add_zero]
    by_cases hij : i = j
    · subst j
      simp
    · have hval : j.val ≠ i.val := by
        intro heq
        exact hij (Fin.ext heq.symm)
      simp [hij, hval]
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply]
    simp only [shift, ih]
    by_cases hnext : i.val + 1 < n
    · let next : Fin n := ⟨i.val + 1, hnext⟩
      rw [Finset.sum_eq_single next]
      · simp only [next, ↓reduceIte, one_mul]
        have heq : i.val + 1 + k = i.val + (k + 1) := by omega
        rw [heq]
      · intro u _ hne
        have hval : u.val ≠ i.val + 1 := by
          intro heq
          exact hne (Fin.ext heq)
        simp [hval]
      · simp
    · have hval : ∀ u : Fin n, u.val ≠ i.val + 1 := by
        intro u heq
        omega
      have htarget : j.val ≠ i.val + (k + 1) := by omega
      simp [hval, htarget]

private theorem shift_pow_mul_natCast_apply (n : ℕ) (R : Type) [CommRing R]
    (k c : ℕ) (i j : Fin n) :
    ((shift n R ^ k) * (c : Matrix (Fin n) (Fin n) R)) i j =
      (shift n R ^ k) i j * (c : R) := by
  classical
  rw [Matrix.mul_apply]
  simp [Matrix.natCast_apply]

/-- A characteristic-`p` native upper-unitriangular matrix has prime-power order
bounded by the first power of `p` at least its dimension. The proof combines
Cayley–Hamilton with Mathlib's `Commute.add_pow_prime_pow_eq'`. -/
theorem pow_prime_pow_eq_one {n p t : ℕ} {R : Type} [CommRing R]
    (hp : Nat.Prime p) (hchar : (p : R) = 0) (hn : n ≤ p ^ t)
    (g : Matrix.UnitriangularGroup (Fin n) R) : g ^ (p ^ t) = 1 := by
  classical
  let A : Matrix (Fin n) (Fin n) R := g.1
  let N : Matrix (Fin n) (Fin n) R := A - 1
  have hupper : A.IsUpperTriangular := g.2.1
  have hdiag : ∀ i, A i i = 1 := g.2.2
  have hNupper : N.IsUpperTriangular := hupper.sub Matrix.blockTriangular_one
  have hNdiag : ∀ i, N i i = 0 := by
    intro i
    simp [N, Matrix.sub_apply, hdiag]
  have hNzero : N ^ n = 0 := by
    simpa using Matrix.pow_card_eq_zero_of_upperTriangular_diag_zero N hNupper hNdiag
  have hNpow : N ^ (p ^ t) = 0 := pow_eq_zero_of_le hn hNzero
  have hpMatrix : (p : Matrix (Fin n) (Fin n) R) = 0 := by
    ext i j
    simp [Matrix.natCast_apply, hchar]
  have hsum : (1 + N) ^ (p ^ t) = (1 : Matrix (Fin n) (Fin n) R) + N ^ (p ^ t) := by
    simpa [hpMatrix] using ((Commute.one_left N).add_pow_prime_pow_eq' hp t)
  have hA : A = 1 + N := by dsimp [N]; abel
  apply Subtype.ext
  apply Units.ext
  change A ^ (p ^ t) = (1 : Matrix (Fin n) (Fin n) R)
  rw [hA, hsum, hNpow, add_zero]

/-- For any positive length shorter than the dimension, some native
upper-unitriangular matrix has a nontrivial power of that length. -/
theorem exists_pow_ne_one_of_pos_lt {n : ℕ} {R : Type} [CommRing R] [Nontrivial R]
    {q : ℕ} (hq : 0 < q) (hqn : q < n) :
    ∃ g : Matrix.UnitriangularGroup (Fin n) R, g ^ q ≠ 1 := by
  classical
  let J := shift n R
  let U : Matrix (Fin n) (Fin n) R := 1 + J
  have hJupper : J.IsUpperTriangular := by
    intro i j hji
    simp only [id_eq] at hji
    have hne : j.val ≠ i.val + 1 := by omega
    simp [J, shift, hne]
  have hJdiag (i : Fin n) : J i i = 0 := by
    have hne : i.val ≠ i.val + 1 := by omega
    simp [J, shift]
  have hUupper : U.IsUpperTriangular := Matrix.blockTriangular_one.add hJupper
  have hUdiag (i : Fin n) : U i i = 1 := by
    simp [U, Matrix.add_apply, hJdiag]
  have hdet : IsUnit U.det := by
    rw [Matrix.det_of_isUpperTriangular hUupper]
    simp [hUdiag]
  let g : Matrix.UnitriangularGroup (Fin n) R :=
    ⟨Matrix.GeneralLinearGroup.mk'' U hdet, by
      exact ⟨hUupper, hUdiag⟩⟩
  let first : Fin n := ⟨0, by omega⟩
  let last : Fin n := ⟨q, hqn⟩
  have hterm (k : ℕ) :
      ((J ^ k * 1 ^ (q - k) * (↑(q.choose k) : Matrix (Fin n) (Fin n) R))
        first last) = if q = k then (q.choose k : R) else 0 := by
    simp only [one_pow, mul_one]
    rw [shift_pow_mul_natCast_apply]
    simp [shift_pow_apply, first, last]
  have hUentry : (U ^ q) first last = 1 := by
    have hcomm : Commute J (1 : Matrix (Fin n) (Fin n) R) := Commute.one_right J
    have hswap : U = J + 1 := by dsimp [U]; exact add_comm 1 J
    rw [hswap, hcomm.add_pow q, Matrix.sum_apply]
    simp only [hterm]
    simp [Finset.sum_ite_eq, Finset.mem_range]
  refine ⟨g, ?_⟩
  intro hg
  have hmatrix : (g.1 : Matrix (Fin n) (Fin n) R) = U := by simp [g]
  have hpower : ((g.1 : Matrix (Fin n) (Fin n) R) ^ q) first last =
      (1 : Matrix (Fin n) (Fin n) R) first last := by
    have heq := congrArg (fun x : Matrix.UnitriangularGroup (Fin n) R =>
      ((x.1 : Matrix (Fin n) (Fin n) R) first last)) hg
    simpa only [Subgroup.coe_pow, Subgroup.coe_one, Units.val_pow_eq_pow_val,
      Matrix.GeneralLinearGroup.coe_one] using heq
  rw [hmatrix] at hpower
  have hne : first ≠ last := by
    intro heq
    have hval := congrArg Fin.val heq
    dsimp [first, last] at hval
    omega
  have hzero : (1 : Matrix (Fin n) (Fin n) R) first last = 0 := by
    simp [hne]
  exact one_ne_zero (hUentry.symm.trans (hpower.trans hzero))

/-- The prime-power uniform exponent bound is sharp over nontrivial
commutative coefficient rings. The consecutive-superdiagonal shift gives a
witness to nontriviality below the dimension threshold. -/
theorem forall_pow_prime_pow_eq_one_iff {n p t : ℕ} {R : Type}
    [CommRing R] [Nontrivial R] (hp : Nat.Prime p) (hchar : (p : R) = 0) :
    (∀ g : Matrix.UnitriangularGroup (Fin n) R, g ^ (p ^ t) = 1) ↔ n ≤ p ^ t := by
  constructor
  · intro hall
    by_contra hn
    obtain ⟨g, hg⟩ := exists_pow_ne_one_of_pos_lt (n := n) (R := R) (q := p ^ t)
      (pow_pos hp.pos t) (Nat.lt_of_not_ge hn)
    exact hg (hall g)
  · intro hn g
    exact pow_prime_pow_eq_one hp hchar hn g

/-- The native group's exponent divides the prime power precisely above the
dimension threshold (with exponent `1` for the trivial group). This uses
Mathlib's `Monoid.exponent_dvd_iff_forall_pow_eq_one`. -/
theorem exponent_dvd_prime_pow_iff {n p t : ℕ} {R : Type}
    [CommRing R] [Nontrivial R] (hp : Nat.Prime p) (hchar : (p : R) = 0) :
    (Monoid.exponent (Matrix.UnitriangularGroup (Fin n) R) ∣ p ^ t) ↔ n ≤ p ^ t := by
  exact (Monoid.exponent_dvd_iff_forall_pow_eq_one).trans
    (forall_pow_prime_pow_eq_one_iff hp hchar)

end UnitriangularGroup

end Matrix
