/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.RingTheory.Coalgebra.Basic
import AlgebraicGroups.Algebra.Coalgebra.Subcoalgebra.Equiv

@[expose] public section

universe u v w w₁

section

example {K : Type*} [Field K] :
    (1 : K) ∉ (CoalgEquiv.refl K K).subcoalgebraCongr
      (⊥ : Subcoalgebra K K) := by
  simp

variable {K : Type*} {C : Type*} {C' : Type*} {C'' : Type*}
variable [Field K] [AddCommGroup C] [Module K C] [Coalgebra K C]
variable [AddCommGroup C'] [Module K C'] [Coalgebra K C']
variable [AddCommGroup C''] [Module K C''] [Coalgebra K C'']

example (e : C ≃ₗc[K] C') (e' : C' ≃ₗc[K] C'')
    (D : Subcoalgebra K C) (E : Subcoalgebra K C'') :
    (e'.subcoalgebraCongr (e.subcoalgebraCongr D) : Set C'') \
        (E : Set C'') =
      {z : C'' | e.symm (e'.symm z) ∈ D ∧ z ∉ E} := by
  ext z
  simp

example (f : C →ₗc[K] C') (D : Subcoalgebra K C)
    (hf : Set.InjOn f (D : Set C)) (q : C' →ₗc[K] C'') :
    q.comp ((Subcoalgebra.map f D).subtype.comp
        (Subcoalgebra.equivMapOfInjOn f D hf).toCoalgHom) =
      (q.comp f).comp D.subtype := by
  rw [Subcoalgebra.subtype_comp_equivMapOfInjOn f D hf]
  exact (CoalgHom.comp_assoc q f D.subtype).symm

example (f : C →ₗc[K] C') (D : Subcoalgebra K C)
    (hf : Set.InjOn f (D : Set C)) (q : C' →ₗc[K] C'')
    (y : Subcoalgebra.map f D) :
    (q.comp (f.comp D.subtype))
        ((Subcoalgebra.equivMapOfInjOn f D hf).symm y) =
      q (y : C') := by
  have h :
      ((Subcoalgebra.map f D).subtype.comp
        (Subcoalgebra.equivMapOfInjOn f D hf).toCoalgHom)
        ((Subcoalgebra.equivMapOfInjOn f D hf).symm y) = (y : C') := by
    simp
  have heval :=
    congrArg
      (fun g : D →ₗc[K] C' ↦
        g ((Subcoalgebra.equivMapOfInjOn f D hf).symm y))
      (Subcoalgebra.subtype_comp_equivMapOfInjOn f D hf)
  have h' :
      (f.comp D.subtype) ((Subcoalgebra.equivMapOfInjOn f D hf).symm y) =
        (y : C') :=
    heval.symm.trans h
  simpa only [CoalgHom.comp_apply] using congrArg q h'

end
