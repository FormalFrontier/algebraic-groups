/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# Bialgebra transport along an algebra equivalence

An algebra equivalence pulls a bialgebra structure back to its domain without
changing the algebra or module on that domain. The coalgebra is the existing
`LinearEquiv.coalgebra` pullback; only its compatibility with multiplication
and the unit needs to be supplied.

As an application, an injective algebra homomorphism from a bialgebra gives its
ordinary subalgebra range a bialgebra structure. No coalgebra on the ambient
algebra is required. This construction alone makes no assertion about the
inclusion preserving coalgebra maps supplied separately on the ambient algebra.
-/

@[expose] public section

open scoped TensorProduct

universe u v w x

namespace AlgEquiv

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommSemiring R] [Semiring A] [Semiring B]
variable [Algebra R A] [Bialgebra R B]

variable (R) in
/-- Pull a bialgebra structure back along an algebra equivalence, retaining the
algebra and module already given on its domain. -/
@[instance_reducible]
noncomputable def bialgebra (e : A ≃ₐ[R] B) : Bialgebra R A := by
  letI : Coalgebra R A := e.toLinearEquiv.coalgebra R
  let ε : A →ₐ[R] R := (Bialgebra.counitAlgHom R B).comp e.toAlgHom
  let Δ : A →ₐ[R] A ⊗[R] A :=
    (Algebra.TensorProduct.map e.symm.toAlgHom e.symm.toAlgHom).comp
      ((Bialgebra.comulAlgHom R B).comp e.toAlgHom)
  exact Bialgebra.mk' R A (map_one ε) (fun {a b} => map_mul ε a b)
    (map_one Δ) (fun {a b} => map_mul Δ a b)

/-- The coalgebra of the transported bialgebra is the linear-equivalence pullback. -/
@[simp]
theorem bialgebra_toCoalgebra (e : A ≃ₐ[R] B) :
    (e.bialgebra R).toCoalgebra = e.toLinearEquiv.coalgebra R := rfl

/-- Transport retains the given algebra structure on the domain. -/
@[simp]
theorem bialgebra_toAlgebra (e : A ≃ₐ[R] B) :
    (e.bialgebra R).toAlgebra = (inferInstance : Algebra R A) := rfl

/-- Comultiplication for the transported bialgebra. -/
theorem bialgebra_comul (e : A ≃ₐ[R] B) :
    (e.bialgebra R).comul =
      TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap ∘ₗ
        (Coalgebra.comul : B →ₗ[R] B ⊗[R] B) ∘ₗ e.toLinearMap := rfl

/-- Counit for the transported bialgebra. -/
theorem bialgebra_counit (e : A ≃ₐ[R] B) :
    (e.bialgebra R).counit =
      (Coalgebra.counit : B →ₗ[R] R) ∘ₗ e.toLinearMap := rfl

/-- The pointwise comultiplication formula for transport. -/
@[simp]
theorem bialgebra_comul_apply (e : A ≃ₐ[R] B) (a : A) :
    (e.bialgebra R).comul a =
      TensorProduct.map e.symm.toLinearMap e.symm.toLinearMap
        (Coalgebra.comul (e a)) := rfl

/-- The pointwise counit formula for transport. -/
@[simp]
theorem bialgebra_counit_apply (e : A ≃ₐ[R] B) (a : A) :
    (e.bialgebra R).counit a = Coalgebra.counit (e a) := rfl

/-- The algebra equivalence intertwines the transported comultiplication. -/
theorem map_bialgebra_comul (e : A ≃ₐ[R] B) (a : A) :
    TensorProduct.map e.toLinearMap e.toLinearMap ((e.bialgebra R).comul a) =
      Coalgebra.comul (e a) := by
  simp [bialgebra_comul_apply, TensorProduct.map_map]

end AlgEquiv

/-- Transport along the identity algebra equivalence recovers the given bialgebra. -/
@[simp]
theorem AlgEquiv.bialgebra_refl {R : Type u} {A : Type v}
    [CommSemiring R] [Semiring A] [b : Bialgebra R A] :
    (AlgEquiv.refl : A ≃ₐ[R] A).bialgebra R = (inferInstance : Bialgebra R A) := by
  cases b
  simp [AlgEquiv.bialgebra, Bialgebra.mk', LinearEquiv.coalgebra,
    LinearEquiv.coalgebraStruct]

/-- Pullback along a composite algebra equivalence agrees with successive pullback. -/
theorem AlgEquiv.bialgebra_trans {R : Type u} {A : Type v} {B : Type w} {C : Type x}
    [CommSemiring R] [Semiring A] [Semiring B] [Semiring C]
    [Algebra R A] [Algebra R B] [Bialgebra R C]
    (e : A ≃ₐ[R] B) (f : B ≃ₐ[R] C) :
    (e.trans f).bialgebra R =
      @AlgEquiv.bialgebra R A B _ _ _ _ (f.bialgebra R) e := by
  have ext_bialgebra (b₁ b₂ : Bialgebra R A)
      (hA : b₁.toAlgebra = b₂.toAlgebra)
      (hΔ : HEq b₁.comul b₂.comul) (hε : HEq b₁.counit b₂.counit) : b₁ = b₂ := by
    cases b₁ with
    | @mk a₁ c₁ _ _ _ _ =>
      cases b₂ with
      | @mk a₂ c₂ _ _ _ _ =>
        cases hA
        cases c₁ with
        | @mk s₁ _ _ _ =>
          cases c₂ with
          | @mk s₂ _ _ _ =>
            cases s₁
            cases s₂
            cases hΔ
            cases hε
            rfl
  refine ext_bialgebra _ _ ?_ ?_ ?_
  · rfl
  · apply heq_of_eq
    ext a
    simp [AlgEquiv.bialgebra_comul_apply, TensorProduct.map_map]
    rfl
  · apply heq_of_eq
    ext a
    simp [AlgEquiv.bialgebra_counit_apply]

namespace AlgHom

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommSemiring R] [Semiring A] [Semiring B]
variable [Bialgebra R A] [Algebra R B]

/-- The ordinary algebra range of an injective algebra homomorphism from a
bialgebra is a bialgebra, with its inherited algebra and module structures.
No coalgebra structure on the ambient algebra is needed. -/
@[instance_reducible]
noncomputable def rangeBialgebraOfInjective (f : A →ₐ[R] B)
    (hf : Function.Injective f) : Bialgebra R f.range :=
  (AlgEquiv.ofInjective f hf).symm.bialgebra R

/-- The range construction retains the inherited subalgebra algebra structure. -/
@[simp]
theorem rangeBialgebraOfInjective_toAlgebra (f : A →ₐ[R] B)
    (hf : Function.Injective f) :
    (f.rangeBialgebraOfInjective hf).toAlgebra =
      (inferInstance : Algebra R f.range) := rfl

/-- Under the range equivalence, comultiplication is that of the original source. -/
theorem rangeBialgebraOfInjective_comul (f : A →ₐ[R] B)
    (hf : Function.Injective f) (a : A) :
    (f.rangeBialgebraOfInjective hf).comul (AlgEquiv.ofInjective f hf a) =
      TensorProduct.map (AlgEquiv.ofInjective f hf).toLinearMap
        (AlgEquiv.ofInjective f hf).toLinearMap (Coalgebra.comul a) := by
  simp

/-- Under the range equivalence, the counit is that of the original source. -/
theorem rangeBialgebraOfInjective_counit (f : A →ₐ[R] B)
    (hf : Function.Injective f) (a : A) :
    (f.rangeBialgebraOfInjective hf).counit (AlgEquiv.ofInjective f hf a) =
      Coalgebra.counit a := by
  simp

end AlgHom
