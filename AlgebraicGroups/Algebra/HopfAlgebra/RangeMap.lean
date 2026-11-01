/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import AlgebraicGroups.Algebra.HopfAlgebra.Range
public import AlgebraicGroups.Algebra.Bialgebra.RangeMap

/-!
# Postcomposition of Hopf quotient factorizations

The Hopf algebra on an ordinary algebra range and its weak range coalgebra have
identical counit and comultiplication. The identity algebra equivalence therefore
gives a bialgebra equivalence between these two coalgebra structures.

Postcomposition commutes with the first-isomorphism equivalences on the ordinary
ideal quotients. The map between the quotients is the quotient lift of the
projection to the quotient by the kernel of the composite.
-/

@[expose] public section

universe u v w z

namespace BialgHom

variable {K : Type u} {A : Type v} {B : Type w}
variable [Field K] [Ring A] [Semiring B]
variable [HopfAlgebra K A] [HopfAlgebra K B]

attribute [local instance] BialgHom.rangeCoalgebraStruct
attribute [local instance] BialgHom.rangeCompCoalgebraStruct

variable {C : Type z} [Semiring C] [HopfAlgebra K C]

/-- Postcomposition commutes with the first-isomorphism equivalences on the
ordinary ideal quotients, after identifying the Hopf and weak range coalgebras. -/
theorem quotientKerEquivRange_rangeMap (f : A →ₐc[K] B) (g : B →ₐc[K] C) :
    @BialgHom.comp K
      (A ⧸ RingHom.ker (f.toAlgHom : A →+* B))
      (A ⧸ RingHom.ker ((g.comp f).toAlgHom : A →+* C))
      (g.comp f).toAlgHom.range _ _ _ _
      (Ideal.Quotient.algebra K) (Ideal.Quotient.algebra K)
      (Subalgebra.algebra (g.comp f).toAlgHom.range)
      (@Bialgebra.Quotient.instQuotientIdeal K A _ _ _
        (RingHom.ker (f.toAlgHom : A →+* B)) _
        (ker_restrictScalars_isCoideal f)).toCoalgebra.toCoalgebraStruct
      (@Bialgebra.Quotient.instQuotientIdeal K A _ _ _
        (RingHom.ker ((g.comp f).toAlgHom : A →+* C)) _
        (ker_restrictScalars_isCoideal (g.comp f))).toCoalgebra.toCoalgebraStruct
      (rangeCoalgebraStruct (g.comp f))
      (@BialgHom.comp K
        (A ⧸ RingHom.ker ((g.comp f).toAlgHom : A →+* C))
        (g.comp f).toAlgHom.range (g.comp f).toAlgHom.range _ _ _ _
        (Ideal.Quotient.algebra K) (Subalgebra.algebra (g.comp f).toAlgHom.range)
        (Subalgebra.algebra (g.comp f).toAlgHom.range)
        (@Bialgebra.Quotient.instQuotientIdeal K A _ _ _
          (RingHom.ker ((g.comp f).toAlgHom : A →+* C)) _
          (ker_restrictScalars_isCoideal (g.comp f))).toCoalgebra.toCoalgebraStruct
        (rangeHopfAlgebra (g.comp f)).toBialgebra.toCoalgebra.toCoalgebraStruct
        (rangeCoalgebraStruct (g.comp f))
        (@BialgEquiv.toBialgHom K (g.comp f).toAlgHom.range (g.comp f).toAlgHom.range _ _ _
          (Subalgebra.algebra (g.comp f).toAlgHom.range)
          (Subalgebra.algebra (g.comp f).toAlgHom.range)
          (rangeHopfAlgebra (g.comp f)).toBialgebra.toCoalgebra.toCoalgebraStruct
          (rangeCoalgebraStruct (g.comp f)) (rangeHopfBialgEquiv (g.comp f)))
        (@BialgEquiv.toBialgHom K
          (A ⧸ RingHom.ker ((g.comp f).toAlgHom : A →+* C))
          (g.comp f).toAlgHom.range _ _ _
          (Ideal.Quotient.algebra K) (Subalgebra.algebra (g.comp f).toAlgHom.range)
          (@Bialgebra.Quotient.instQuotientIdeal K A _ _ _
            (RingHom.ker ((g.comp f).toAlgHom : A →+* C)) _
            (ker_restrictScalars_isCoideal (g.comp f))).toCoalgebra.toCoalgebraStruct
          (rangeHopfAlgebra (g.comp f)).toBialgebra.toCoalgebra.toCoalgebraStruct
          (quotientKerEquivRange (g.comp f))))
      (@Bialgebra.Quotient.mapBialgHom K A _ _ _
        (RingHom.ker (f.toAlgHom : A →+* B))
        (RingHom.ker ((g.comp f).toAlgHom : A →+* C)) _ _
        (ker_restrictScalars_isCoideal f) (ker_restrictScalars_isCoideal (g.comp f))
        (by
          change RingHom.ker (f.toAlgHom : A →+* B) ≤
            (RingHom.ker (g.toAlgHom : B →+* C)).comap (f.toAlgHom : A →+* B)
          exact Ideal.ker_le_comap (f.toAlgHom : A →+* B))) =
      @BialgHom.comp K
        (A ⧸ RingHom.ker (f.toAlgHom : A →+* B))
        f.toAlgHom.range (g.comp f).toAlgHom.range _ _ _ _
        (Ideal.Quotient.algebra K) (Subalgebra.algebra f.toAlgHom.range)
        (Subalgebra.algebra (g.comp f).toAlgHom.range)
        (@Bialgebra.Quotient.instQuotientIdeal K A _ _ _
          (RingHom.ker (f.toAlgHom : A →+* B)) _
          (ker_restrictScalars_isCoideal f)).toCoalgebra.toCoalgebraStruct
        (rangeCoalgebraStruct f) (rangeCoalgebraStruct (g.comp f))
        (rangeMap f g)
        (@BialgHom.comp K
          (A ⧸ RingHom.ker (f.toAlgHom : A →+* B))
          f.toAlgHom.range f.toAlgHom.range _ _ _ _
          (Ideal.Quotient.algebra K) (Subalgebra.algebra f.toAlgHom.range)
          (Subalgebra.algebra f.toAlgHom.range)
          (@Bialgebra.Quotient.instQuotientIdeal K A _ _ _
            (RingHom.ker (f.toAlgHom : A →+* B)) _
            (ker_restrictScalars_isCoideal f)).toCoalgebra.toCoalgebraStruct
          (rangeHopfAlgebra f).toBialgebra.toCoalgebra.toCoalgebraStruct
          (rangeCoalgebraStruct f)
          (@BialgEquiv.toBialgHom K f.toAlgHom.range f.toAlgHom.range _ _ _
            (Subalgebra.algebra f.toAlgHom.range) (Subalgebra.algebra f.toAlgHom.range)
            (rangeHopfAlgebra f).toBialgebra.toCoalgebra.toCoalgebraStruct
            (rangeCoalgebraStruct f) (rangeHopfBialgEquiv f))
          (@BialgEquiv.toBialgHom K
            (A ⧸ RingHom.ker (f.toAlgHom : A →+* B)) f.toAlgHom.range _ _ _
            (Ideal.Quotient.algebra K) (Subalgebra.algebra f.toAlgHom.range)
            (@Bialgebra.Quotient.instQuotientIdeal K A _ _ _
              (RingHom.ker (f.toAlgHom : A →+* B)) _
              (ker_restrictScalars_isCoideal f)).toCoalgebra.toCoalgebraStruct
            (rangeHopfAlgebra f).toBialgebra.toCoalgebra.toCoalgebraStruct
            (quotientKerEquivRange f))) := by
  let : CoalgebraStruct K (A ⧸ RingHom.ker (f.toAlgHom : A →+* B)) :=
    (@Bialgebra.Quotient.instQuotientIdeal K A _ _ _
      (RingHom.ker (f.toAlgHom : A →+* B)) _
      (ker_restrictScalars_isCoideal f)).toCoalgebra.toCoalgebraStruct
  apply BialgHom.ext
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  change rangeHopfBialgEquiv (g.comp f)
        (quotientKerEquivRange (g.comp f)
          ((@Bialgebra.Quotient.mapBialgHom K A _ _ _
            (RingHom.ker (f.toAlgHom : A →+* B))
            (RingHom.ker ((g.comp f).toAlgHom : A →+* C)) _ _
            (ker_restrictScalars_isCoideal f) (ker_restrictScalars_isCoideal (g.comp f))
            (by
              change RingHom.ker (f.toAlgHom : A →+* B) ≤
                (RingHom.ker (g.toAlgHom : B →+* C)).comap (f.toAlgHom : A →+* B)
              exact Ideal.ker_le_comap (f.toAlgHom : A →+* B)))
            (Ideal.Quotient.mk _ a))) =
      (rangeMap f g).toFun (rangeHopfBialgEquiv f
        (quotientKerEquivRange f (Ideal.Quotient.mk _ a)))
  rw [Bialgebra.Quotient.mapBialgHom_mk, quotientKerEquivRange_mk, quotientKerEquivRange_mk,
    rangeHopfBialgEquiv_apply, rangeHopfBialgEquiv_apply, rangeMap_rangeRestrict]

end BialgHom
