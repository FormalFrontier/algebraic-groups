/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.HopfAlgebra.FiniteType
public import CoherentModules.RingTheory.Flat.FiniteWindows

/-!
# Faithful flatness from finite-type Hopf inclusions

A uniform faithful-flatness theorem for injective maps between finite-type commutative
Hopf algebras implies faithful flatness of every Hopf-subalgebra inclusion. Compatible
Hopf windows identify the maps in the finite-subring criterion with restrictions of
the inclusion.

The finite-type faithful-flatness theorem is an input, not a result of this module.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§3.31–3.35, for the Hopf-subalgebra and
  finite-generation background.
-/

@[expose] public section

universe u v

/-- A uniform faithful-flatness theorem for injective full bialgebra maps between
finite-type commutative Hopf algebras implies faithful flatness of a Hopf-subalgebra
inclusion. The source and target in the uniform hypothesis are both finite type;
no finite-type assumption is made on the ambient algebra or the given subalgebra. -/
theorem Subalgebra.faithfullyFlat_val_of_finiteType_inclusions
    {K : Type u} {H : Type v}
    [Field K] [CommRing H] [HopfAlgebra K H]
    (S : Subalgebra K H) (hS : S.IsHopfSubalgebra)
    (hfinite :
      ∀ (A B : Type v) [CommRing A] [HopfAlgebra K A]
          [CommRing B] [HopfAlgebra K B],
        Algebra.FiniteType K A → Algebra.FiniteType K B →
        ∀ r : @BialgHom K A B _ _ _ _ _
            (inferInstance : CoalgebraStruct K A)
            (inferInstance : CoalgebraStruct K B),
          Function.Injective r →
          (r.toAlgHom : A →+* B).FaithfullyFlat) :
    (S.val : S →+* H).FaithfullyFlat := by
  classical
  let _ : HopfAlgebra K S := S.hopfAlgebra hS
  apply RingHom.FaithfullyFlat.of_finite_subring_windows (S.val : S →+* H)
  intro e
  obtain ⟨A, hA, hAfin, he, htarget⟩ :=
    BialgHom.exists_compatible_finiteType_hopf_windows_of_commutative
      (S.inclusionBialgHom hS) (↑e : Set S) e.finite_toSet
  intro t
  obtain ⟨B, hB, hBfin, ht, hmap, r, hsquare, -⟩ :=
    htarget (↑t : Set H) t.finite_toSet
  let _ : HopfAlgebra K A := A.hopfAlgebra hA
  let _ : HopfAlgebra K B := B.hopfAlgebra hB
  have hvalue (a : A) : (r a : H) = ((a : S) : H) := by
    exact congrArg
      (fun q : @BialgHom K A H _ _ _ _ _
        (A.coalgebraOfComulMem hA.comul_mem).toCoalgebraStruct
        (inferInstance : CoalgebraStruct K H) => q a) hsquare
  have hinj : Function.Injective r := by
    intro a a' haa'
    apply Subtype.ext
    apply Subtype.ext
    exact (hvalue a).symm.trans
      ((congrArg (fun b : B => (b : H)) haa').trans (hvalue a'))
  have hmem : ∀ a ∈ A.toSubring, (S.val : S →+* H) a ∈ B.toSubring := by
    intro a ha
    exact hmap ⟨a, ha, rfl⟩
  have hrestriction :
      (S.val : S →+* H).restrict A.toSubring B.toSubring hmem =
        (r.toAlgHom : A →+* B) := by
    apply RingHom.ext
    intro a
    apply Subtype.ext
    simpa using (hvalue a).symm
  refine ⟨A.toSubring, B.toSubring, he, ht, hmem, ?_⟩
  rw [hrestriction]
  exact hfinite A B hAfin hBfin r hinj
