/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Bialgebra.Quotient

/-!
# Counit and comultiplication compatibility of algebra quotient lifts

Let `I` be a two-sided ideal of a bialgebra `A` over a commutative ring `R`,
with `I.restrictScalars R` a coideal. For a bialgebra morphism `f : A →ₐc[R] B`
vanishing on `I`, the preservation conditions for `Ideal.Quotient.liftₐ` are
equalities of algebra morphisms: composing with the target counit gives the
quotient counit, and applying the tensor square of the lift to the quotient
comultiplication gives the target comultiplication after the lift.

The quotient carries Mathlib's bialgebra structure on the ordinary ideal
quotient. The source is a ring, the target is only a semiring, and the scalar,
source and target universes are independent. All algebra, module and coalgebra
data are inherited from the bialgebras and the ideal quotient.

## Scope

These equalities are preservation components for the algebraic factor map,
not the full quotient universal property. They allow a commutative-ring base
and bialgebras without commutativity or an antipode, and assume that the input
morphism preserves the counit. By contrast, Milne's Proposition 3.12 concerns
commutative Hopf quotients over a field. Its algebra-and-comultiplication
morphism convention obtains counit and antipode preservation separately from
Proposition 3.4. Neither this convention bridge nor uniqueness of quotient
Hopf algebra structures is asserted here.

## References

- J. S. Milne, *Algebraic Groups* (2017), Proposition 3.12, for the factor-map
  part of commutative Hopf quotient factorization over a field.
- Mathlib's `Mathlib.RingTheory.Bialgebra.Quotient` for the quotient bialgebra
  and its canonical projection, `Mathlib.RingTheory.Ideal.Quotient.Operations`
  for the algebra lift, and `Mathlib.RingTheory.Bialgebra.Hom` for the counit
  and comultiplication preservation conditions of a bialgebra morphism.
-/

@[expose] public section

universe uR uA uB

namespace Bialgebra.Quotient

/-- Composing the ordinary algebra quotient lift with the target counit gives
exactly the counit of the quotient bialgebra. -/
theorem counitAlgHom_comp_liftₐ :
    ∀ {R : Type uR} {A : Type uA} {B : Type uB}
      [CommRing R] [Ring A] [Semiring B] [Bialgebra R A] [Bialgebra R B]
      (I : Ideal A) [I.IsTwoSided] [(I.restrictScalars R).IsCoideal]
      (f : A →ₐc[R] B)
      (hf : I ≤ RingHom.ker ((f : A →ₐ[R] B).toRingHom)),
    (Bialgebra.counitAlgHom R B).comp
        (Ideal.Quotient.liftₐ I (f : A →ₐ[R] B)
          (fun a ha => RingHom.mem_ker.mp (hf ha))) =
      Bialgebra.counitAlgHom R (A ⧸ I) := by
  intro R A B _ _ _ _ _ I _ _ f hf
  have hmk :
      (mkBialgHom (R := R) I : A →ₐ[R] A ⧸ I) = Ideal.Quotient.mkₐ R I := by
    apply AlgHom.ext
    intro a
    simpa only [BialgHom.coe_toAlgHom, Ideal.Quotient.mkₐ_eq_mk] using
      mkBialgHom_apply (R := R) I a
  apply Ideal.Quotient.algHom_ext R
  simpa only [AlgHom.comp_assoc, Ideal.Quotient.liftₐ_comp, hmk] using
    (BialgHom.counitAlgHom_comp f).trans
      (BialgHom.counitAlgHom_comp (mkBialgHom (R := R) I)).symm

/-- The tensor square of the ordinary algebra quotient lift intertwines the
quotient comultiplication with the target comultiplication. -/
theorem map_liftₐ_comp_comulAlgHom :
    ∀ {R : Type uR} {A : Type uA} {B : Type uB}
      [CommRing R] [Ring A] [Semiring B] [Bialgebra R A] [Bialgebra R B]
      (I : Ideal A) [I.IsTwoSided] [(I.restrictScalars R).IsCoideal]
      (f : A →ₐc[R] B)
      (hf : I ≤ RingHom.ker ((f : A →ₐ[R] B).toRingHom)),
    (Algebra.TensorProduct.map
        (Ideal.Quotient.liftₐ I (f : A →ₐ[R] B)
          (fun a ha => RingHom.mem_ker.mp (hf ha)))
        (Ideal.Quotient.liftₐ I (f : A →ₐ[R] B)
          (fun a ha => RingHom.mem_ker.mp (hf ha)))).comp
        (Bialgebra.comulAlgHom R (A ⧸ I)) =
      (Bialgebra.comulAlgHom R B).comp
        (Ideal.Quotient.liftₐ I (f : A →ₐ[R] B)
          (fun a ha => RingHom.mem_ker.mp (hf ha))) := by
  intro R A B _ _ _ _ _ I _ _ f hf
  -- Keep the vanishing witness opaque to rewriting at implicit transparency.
  have hI : ∀ a : A, a ∈ I → (f : A →ₐ[R] B) a = 0 := by
    intro a ha
    exact RingHom.mem_ker.mp (hf ha)
  change
    (Algebra.TensorProduct.map
        (Ideal.Quotient.liftₐ I (f : A →ₐ[R] B) hI)
        (Ideal.Quotient.liftₐ I (f : A →ₐ[R] B) hI)).comp
        (Bialgebra.comulAlgHom R (A ⧸ I)) =
      (Bialgebra.comulAlgHom R B).comp
        (Ideal.Quotient.liftₐ I (f : A →ₐ[R] B) hI)
  have hmk :
      (mkBialgHom (R := R) I : A →ₐ[R] A ⧸ I) = Ideal.Quotient.mkₐ R I := by
    apply AlgHom.ext
    intro a
    simpa only [BialgHom.coe_toAlgHom, Ideal.Quotient.mkₐ_eq_mk] using
      mkBialgHom_apply (R := R) I a
  have hcomul :
      (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)).comp
          (Bialgebra.comulAlgHom R A) =
        (Bialgebra.comulAlgHom R (A ⧸ I)).comp (Ideal.Quotient.mkₐ R I) := by
    simpa only [hmk] using
      BialgHom.map_comp_comulAlgHom (mkBialgHom (R := R) I)
  apply Ideal.Quotient.algHom_ext R
  rw [AlgHom.comp_assoc, ← hcomul, ← AlgHom.comp_assoc,
    ← Algebra.TensorProduct.map_comp]
  simpa only [AlgHom.comp_assoc, Ideal.Quotient.liftₐ_comp] using
    BialgHom.map_comp_comulAlgHom f

end Bialgebra.Quotient
