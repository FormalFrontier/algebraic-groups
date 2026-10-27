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

The canonical `liftBialgHom` bundles this algebra lift using these two
preservation equalities. Its representative and composition formulas,
extensionality, and unique factorization API concern this fixed quotient
bialgebra structure.

## Scope

The factorization starts with a full bialgebra morphism, including counit
preservation. It allows a commutative-ring base and bialgebras without
commutativity or an antipode. By contrast, Milne's Proposition 3.12 concerns
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
          (fun _ ha => RingHom.mem_ker.mp (hf ha))) =
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
          (fun _ ha => RingHom.mem_ker.mp (hf ha)))
        (Ideal.Quotient.liftₐ I (f : A →ₐ[R] B)
          (fun _ ha => RingHom.mem_ker.mp (hf ha)))).comp
        (Bialgebra.comulAlgHom R (A ⧸ I)) =
      (Bialgebra.comulAlgHom R B).comp
        (Ideal.Quotient.liftₐ I (f : A →ₐ[R] B)
          (fun _ ha => RingHom.mem_ker.mp (hf ha))) := by
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


namespace Bialgebra.Quotient

/-- The bialgebra morphism induced by a full bialgebra morphism vanishing on a
scalar-restricted coideal that is a two-sided ideal. The quotient has its
canonical bialgebra structure, and the underlying algebra map is the ordinary
ideal quotient lift. -/
noncomputable def liftBialgHom
    {R : Type uR} {A : Type uA} {B : Type uB}
    [CommRing R] [Ring A] [Semiring B] [Bialgebra R A] [Bialgebra R B]
    (I : Ideal A) [I.IsTwoSided] [(I.restrictScalars R).IsCoideal]
    (f : A →ₐc[R] B) (hf : I ≤ RingHom.ker f.toAlgHom.toRingHom) :
    (A ⧸ I) →ₐc[R] B :=
  BialgHom.ofAlgHom
    (Ideal.Quotient.liftₐ I f.toAlgHom (fun _a ha => RingHom.mem_ker.mp (hf ha)))
    (Bialgebra.Quotient.counitAlgHom_comp_liftₐ I f hf)
    (Bialgebra.Quotient.map_liftₐ_comp_comulAlgHom I f hf)

/-- The underlying algebra morphism of the induced bialgebra morphism is the
ordinary algebra quotient lift. -/
@[simp]
theorem liftBialgHom_toAlgHom :
    ∀ {R : Type uR} {A : Type uA} {B : Type uB}
      [CommRing R] [Ring A] [Semiring B] [Bialgebra R A] [Bialgebra R B]
      (I : Ideal A) [I.IsTwoSided] [(I.restrictScalars R).IsCoideal]
      (f : A →ₐc[R] B) (hf : I ≤ RingHom.ker f.toAlgHom.toRingHom),
    (liftBialgHom I f hf).toAlgHom =
      Ideal.Quotient.liftₐ I f.toAlgHom (fun _a ha => RingHom.mem_ker.mp (hf ha)) := by
  intro R A B _ _ _ _ _ I _ _ f hf
  apply AlgHom.ext
  intro x
  simp only [BialgHom.coe_toAlgHom, liftBialgHom, BialgHom.ofAlgHom_apply]

/-- The induced bialgebra morphism sends the class of each representative to
its image under the original morphism. -/
@[simp]
theorem liftBialgHom_mk :
    ∀ {R : Type uR} {A : Type uA} {B : Type uB}
      [CommRing R] [Ring A] [Semiring B] [Bialgebra R A] [Bialgebra R B]
      (I : Ideal A) [I.IsTwoSided] [(I.restrictScalars R).IsCoideal]
      (f : A →ₐc[R] B) (hf : I ≤ RingHom.ker f.toAlgHom.toRingHom) (a : A),
    liftBialgHom I f hf (Ideal.Quotient.mk I a) = f a := by
  intro R A B _ _ _ _ _ I _ _ f hf a
  have h := congrArg
    (fun g : (A ⧸ I) →ₐ[R] B => g.comp (Ideal.Quotient.mkₐ R I))
    (liftBialgHom_toAlgHom I f hf)
  have hcomp := h.trans
    (Ideal.Quotient.liftₐ_comp (R₁ := R) I f.toAlgHom
      (fun a ha => RingHom.mem_ker.mp (hf ha)))
  simpa only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
    BialgHom.coe_toAlgHom] using AlgHom.congr_fun hcomp a

/-- The induced bialgebra morphism factors the original morphism through the
canonical quotient projection. -/
@[simp]
theorem liftBialgHom_comp_mkBialgHom :
    ∀ {R : Type uR} {A : Type uA} {B : Type uB}
      [CommRing R] [Ring A] [Semiring B] [Bialgebra R A] [Bialgebra R B]
      (I : Ideal A) [I.IsTwoSided] [(I.restrictScalars R).IsCoideal]
      (f : A →ₐc[R] B) (hf : I ≤ RingHom.ker f.toAlgHom.toRingHom),
    (liftBialgHom I f hf).comp (mkBialgHom (R := R) I) = f := by
  intro R A B _ _ _ _ _ I _ _ f hf
  apply BialgHom.ext
  intro a
  simpa only [BialgHom.coe_comp, Function.comp_apply, mkBialgHom_apply] using
    liftBialgHom_mk I f hf a

/-- Bialgebra morphisms from the canonical quotient agree if their composites
with the quotient projection agree. -/
theorem hom_ext :
    ∀ {R : Type uR} {A : Type uA} {B : Type uB}
      [CommRing R] [Ring A] [Semiring B] [Bialgebra R A] [Bialgebra R B]
      (I : Ideal A) [I.IsTwoSided] [(I.restrictScalars R).IsCoideal]
      (g h : (A ⧸ I) →ₐc[R] B),
    g.comp (mkBialgHom (R := R) I) = h.comp (mkBialgHom (R := R) I) → g = h := by
  intro R A B _ _ _ _ _ I _ _ g h hcomp
  have hmk :
      (mkBialgHom (R := R) I : A →ₐ[R] A ⧸ I) = Ideal.Quotient.mkₐ R I := by
    apply AlgHom.ext
    intro a
    simpa only [BialgHom.coe_toAlgHom, Ideal.Quotient.mkₐ_eq_mk] using
      mkBialgHom_apply (R := R) I a
  apply BialgHom.coe_toAlgHom_injective
  apply Ideal.Quotient.algHom_ext R
  simpa only [BialgHom.comp_toAlgHom, hmk] using
    congrArg BialgHom.toAlgHom hcomp

/-- Every factor through the canonical quotient projection equals the induced
bialgebra morphism. -/
theorem liftBialgHom_unique :
    ∀ {R : Type uR} {A : Type uA} {B : Type uB}
      [CommRing R] [Ring A] [Semiring B] [Bialgebra R A] [Bialgebra R B]
      (I : Ideal A) [I.IsTwoSided] [(I.restrictScalars R).IsCoideal]
      (f : A →ₐc[R] B) (hf : I ≤ RingHom.ker f.toAlgHom.toRingHom)
      (g : (A ⧸ I) →ₐc[R] B),
    g.comp (mkBialgHom (R := R) I) = f → g = liftBialgHom I f hf := by
  intro R A B _ _ _ _ _ I _ _ f hf g hg
  apply hom_ext I
  exact hg.trans (liftBialgHom_comp_mkBialgHom I f hf).symm

/-- A full bialgebra morphism vanishing on the ideal factors uniquely through
the fixed canonical quotient bialgebra and its projection. This asserts
uniqueness of the factor morphism, not of bialgebra structures on the quotient. -/
theorem existsUnique_liftBialgHom
    {R : Type uR} {A : Type uA} {B : Type uB}
    [CommRing R] [Ring A] [Semiring B] [Bialgebra R A] [Bialgebra R B]
    (I : Ideal A) [I.IsTwoSided] [(I.restrictScalars R).IsCoideal]
    (f : A →ₐc[R] B) (hf : I ≤ RingHom.ker f.toAlgHom.toRingHom) :
    ∃! g : (A ⧸ I) →ₐc[R] B, g.comp (mkBialgHom (R := R) I) = f := by
  refine ⟨liftBialgHom I f hf, liftBialgHom_comp_mkBialgHom I f hf, ?_⟩
  intro g hg
  exact liftBialgHom_unique I f hf g hg

end Bialgebra.Quotient
