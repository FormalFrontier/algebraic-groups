/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AlgebraicGroups.Algebra.MatrixEndBaseChange
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Ordinary-import regressions for source-order tensor base change

These named private clients exercise the existing public reductions and
evaluation formulas without exporting mathematical declarations.
-/

set_option warningAsError true

noncomputable section

open TensorProduct
open scoped TensorProduct

namespace AlgebraicGeometry

universe u

variable (K V R S T : Type u) [CommRing K] [AddCommGroup V] [Module K V]
  [CommRing R] [Algebra K R] [CommRing S] [Algebra K S]
  [CommRing T] [Algebra K T]

private theorem testTensorSwap (v : V) (r : R) :
    sourceOrderTensorEquiv K V R (v ⊗ₜ[K] r) = r ⊗ₜ[K] v := rfl

private theorem testWrapperProjection (x : SourceOrderedTensor K V R) :
    (sourceOrderedEquiv K V R) x = x.tensor := rfl

private theorem testWrapperConstruction (x : V ⊗[K] R) :
    (sourceOrderedEquiv K V R).symm x = ⟨x⟩ := rfl

private theorem testAddReduction (x y : V ⊗[K] R) :
    ((⟨x⟩ : SourceOrderedTensor K V R) + ⟨y⟩).tensor = x + y := rfl

private theorem testTransportedAdd (x y : SourceOrderedTensor K V R) :
    sourceOrderedCanonicalAddEquiv K V R (x + y) =
      sourceOrderedCanonicalAddEquiv K V R x + sourceOrderedCanonicalAddEquiv K V R y :=
  (sourceOrderedCanonicalAddEquiv K V R).map_add x y

private theorem testTransportedScalar (x : SourceOrderedTensor K V R) (r : R) :
    sourceOrderedCanonicalLinearEquiv K V R (r • x) =
      r • sourceOrderedCanonicalLinearEquiv K V R x :=
  (sourceOrderedCanonicalLinearEquiv K V R).map_smul r x

private theorem testPureTensor (v : V) (r : R) :
    (sourceOrderedTmul K V R v r).tensor = v ⊗ₜ[K] r := rfl

private theorem testAddEquivReduction (x : V ⊗[K] R) :
    sourceOrderedCanonicalAddEquiv K V R ⟨x⟩ = (TensorProduct.comm K V R) x := rfl

private theorem testPureLinear (v : V) (r : R) :
    sourceOrderedCanonicalLinearEquiv K V R (sourceOrderedTmul K V R v r) =
      r ⊗ₜ[K] v := rfl

private theorem testEndConjugation (f : Module.End R (SourceOrderedTensor K V R))
    (x : SourceOrderedTensor K V R) :
    sourceOrderedEndEquiv K V R f (sourceOrderedCanonicalLinearEquiv K V R x) =
      sourceOrderedCanonicalLinearEquiv K V R (f x) :=
  sourceOrderedEndEquiv_apply K V R f x

private theorem testEndConjugationReduction
    (f : Module.End R (SourceOrderedTensor K V R)) :
    sourceOrderedEndEquiv K V R f = (sourceOrderedCanonicalLinearEquiv K V R).conj f := rfl

private theorem testEndBaseChangeReduction (g : R →ₐ[K] S)
    (f : Module.End R (SourceOrderTensor K V R)) :
    endBaseChange K V R S g f =
      letI : Algebra R S := g.toRingHom.toAlgebra
      (AlgebraTensorModule.cancelBaseChange K R S S V).toLinearMap.comp
        ((f.baseChange S).comp
          (AlgebraTensorModule.cancelBaseChange K R S S V).symm.toLinearMap) := rfl

private theorem testAddHomReduction (g : R →ₐ[K] S)
    (f : Module.End R (SourceOrderTensor K V R)) :
    endBaseChangeAddHom K V R S g f = endBaseChange K V R S g f := rfl

private theorem testNamedEvaluation (g : R →ₐ[K] S)
    (f : Module.End R (SourceOrderTensor K V R)) (s : S) (v : V) :
    endBaseChange K V R S g f (s ⊗ₜ[K] v) =
      s • (g.toLinearMap.rTensor V) (f (1 ⊗ₜ[K] v)) :=
  endBaseChange_tmul K V R S g f s v

private theorem testTensorSums (g : R →ₐ[K] S)
    (f : Module.End R (SourceOrderTensor K V R)) (s t : S) (v w : V) :
    endBaseChange K V R S g f (s ⊗ₜ[K] v + t ⊗ₜ[K] w) =
      s • (g.toLinearMap.rTensor V) (f (1 ⊗ₜ[K] v)) +
        t • (g.toLinearMap.rTensor V) (f (1 ⊗ₜ[K] w)) := by
  rw [map_add, endBaseChange_tmul, endBaseChange_tmul]

private theorem testIdentity (f : Module.End R (SourceOrderTensor K V R)) :
    endBaseChange K V R R (AlgHom.id K R) f = f :=
  endBaseChange_id K V R f

private theorem testComposition (g : R →ₐ[K] S) (h : S →ₐ[K] T)
    (f : Module.End R (SourceOrderTensor K V R)) :
    endBaseChange K V S T h (endBaseChange K V R S g f) =
      endBaseChange K V R T (h.comp g) f :=
  endBaseChange_comp K V R S T g h f

private theorem testAdditive (g : R →ₐ[K] S)
    (f h : Module.End R (SourceOrderTensor K V R)) :
    endBaseChange K V R S g (f + h) =
      endBaseChange K V R S g f + endBaseChange K V R S g h :=
  (endBaseChangeAddHom K V R S g).map_add f h

private theorem testPolynomialEvaluation (f : Module.End (Polynomial (ZMod 2))
    (SourceOrderTensor (ZMod 2) (Fin 1 → ZMod 2) (Polynomial (ZMod 2))))
    (s : ZMod 2) (v : Fin 1 → ZMod 2) :
    endBaseChange (ZMod 2) (Fin 1 → ZMod 2) (Polynomial (ZMod 2))
      (ZMod 2) (Polynomial.aeval (1 : ZMod 2)) f (s ⊗ₜ[ZMod 2] v) =
        s • ((Polynomial.aeval (1 : ZMod 2)).toLinearMap.rTensor (Fin 1 → ZMod 2))
          (f (1 ⊗ₜ[ZMod 2] v)) :=
  endBaseChange_tmul (ZMod 2) (Fin 1 → ZMod 2)
    (Polynomial (ZMod 2)) (ZMod 2) (Polynomial.aeval (1 : ZMod 2)) f s v

local instance zeroRingAlgebra : Algebra (ZMod 2) (ZMod 1) :=
  (ZMod.castHom (show 1 ∣ 2 by decide) (ZMod 1)).toAlgebra

private theorem testEmptyModule (f : Module.End (ZMod 2)
    (SourceOrderTensor (ZMod 2) (Fin 0 → ZMod 2) (ZMod 2)))
    (s : ZMod 1) (v : Fin 0 → ZMod 2) :
    endBaseChange (ZMod 2) (Fin 0 → ZMod 2) (ZMod 2) (ZMod 1)
      (Algebra.ofId (ZMod 2) (ZMod 1)) f (s ⊗ₜ[ZMod 2] v) =
        s • ((Algebra.ofId (ZMod 2) (ZMod 1)).toLinearMap.rTensor (Fin 0 → ZMod 2))
          (f (1 ⊗ₜ[ZMod 2] v)) :=
  endBaseChange_tmul (ZMod 2) (Fin 0 → ZMod 2) (ZMod 2) (ZMod 1)
    (Algebra.ofId (ZMod 2) (ZMod 1)) f s v

private theorem testZeroRing (f : Module.End (ZMod 1)
    (SourceOrderTensor (ZMod 1) (Fin 0 → ZMod 1) (ZMod 1))) :
    endBaseChange (ZMod 1) (Fin 0 → ZMod 1) (ZMod 1) (ZMod 1)
      (AlgHom.id (ZMod 1) (ZMod 1)) f = f :=
  endBaseChange_id (ZMod 1) (Fin 0 → ZMod 1) (ZMod 1) f

end AlgebraicGeometry

#lint
