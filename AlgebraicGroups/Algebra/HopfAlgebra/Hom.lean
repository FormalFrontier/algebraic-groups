/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.HopfAlgebra.Convolution
import Mathlib.RingTheory.HopfAlgebra.Quotient

/-!
# Bialgebra homomorphisms between Hopf algebras

A bialgebra homomorphism between Hopf algebras commutes with their antipodes.
The base is a commutative semiring; the two Hopf algebras need not be commutative
or have additive inverses. The proof compares a left and a right inverse in
Mathlib's convolution monoid of linear maps, using its compatibility lemmas for
composition with the convolution product and unit. The quotient construction
`HopfAlgebra.ofSurjective` assumes antipode compatibility rather than proving it.

A unital algebra map from a Hopf algebra to a bialgebra that preserves
comultiplication refines canonically to a bialgebra homomorphism, without
changing its underlying algebra map. Counit preservation follows automatically;
no counit premise or Hopf structure on the target is required. This uses
Mathlib's `BialgHom.ofAlgHom` after the counit-compatibility theorem below.

## References

* J. S. Milne, *Algebraic Groups* (2017), §3.4: automatic compatibility
  of algebra homomorphisms with the counit.
* Yaël Dillies, Michał Mrugała and Yunzhou Xie, Mathlib,
  `Mathlib.RingTheory.Coalgebra.Convolution` and
  `Mathlib.RingTheory.HopfAlgebra.Convolution`: convolution of linear maps,
  compatibility with algebra and coalgebra maps, and the antipode identities.
* Kenny Lau, Yury Kudryashov and Amelia Livingston, Mathlib,
  `Mathlib.RingTheory.Bialgebra.Hom`: bundled bialgebra homomorphisms and
  `BialgHom.ofAlgHom`.
* Robert Hawkins, Mathlib, `Mathlib.RingTheory.HopfAlgebra.Quotient`:
  `LinearMap.convOne_comp_coalgHom` and `LinearMap.algHom_comp_convOne`,
  compatibility of the convolution unit with coalgebra and algebra maps.
-/

@[expose] public section

universe u v w

open WithConv

namespace BialgHom

variable {R : Type u} {A : Type v} {B : Type w}
  [CommSemiring R] [Semiring A] [Semiring B]
  [HopfAlgebra R A] [HopfAlgebra R B]

/-- A bialgebra homomorphism between Hopf algebras commutes with the antipodes.
This follows from uniqueness of convolution inverses, using Mathlib's linear-map
convolution identities. -/
@[simp]
theorem map_antipode (f : A →ₐc[R] B) (x : A) :
    f (HopfAlgebra.antipode R x) = HopfAlgebra.antipode R (f x) := by
  have hleft : toConv ((HopfAlgebra.antipode R).comp f.toLinearMap) *
      toConv f.toLinearMap = (1 : WithConv (A →ₗ[R] B)) := by
    apply ofConv_injective
    calc
      (toConv ((HopfAlgebra.antipode R).comp f.toLinearMap) *
          toConv f.toLinearMap : WithConv (A →ₗ[R] B)).ofConv =
          (toConv (HopfAlgebra.antipode R) *
            toConv LinearMap.id : WithConv (B →ₗ[R] B)).ofConv.comp
              f.toCoalgHom.toLinearMap := by
        rw [LinearMap.convMul_comp_coalgHom_distrib]
        rfl
      _ = (1 : WithConv (B →ₗ[R] B)).ofConv.comp f.toLinearMap := by
        rw [LinearMap.antipode_mul_id]
      _ = (1 : WithConv (A →ₗ[R] B)).ofConv := by
        exact LinearMap.convOne_comp_coalgHom f.toCoalgHom
  have hright : toConv f.toLinearMap *
      toConv (f.toLinearMap.comp (HopfAlgebra.antipode R)) =
        (1 : WithConv (A →ₗ[R] B)) := by
    apply ofConv_injective
    calc
      (toConv f.toLinearMap *
          toConv (f.toLinearMap.comp (HopfAlgebra.antipode R)) :
            WithConv (A →ₗ[R] B)).ofConv =
          (f : A →ₐ[R] B).toLinearMap.comp
            (toConv LinearMap.id * toConv (HopfAlgebra.antipode R) :
              WithConv (A →ₗ[R] A)).ofConv := by
        rw [LinearMap.algHom_comp_convMul_distrib]
        rfl
      _ = f.toLinearMap.comp (1 : WithConv (A →ₗ[R] A)).ofConv := by
        rw [LinearMap.id_mul_antipode]
        rfl
      _ = (1 : WithConv (A →ₗ[R] B)).ofConv := by
        exact LinearMap.algHom_comp_convOne (f : A →ₐ[R] B)
  have heq := toConv_injective (left_inv_eq_right_inv hleft hright)
  exact (LinearMap.congr_fun heq x).symm

end BialgHom

namespace AlgHom

variable {R : Type u} {A : Type v} {B : Type w}
  [CommSemiring R] [Semiring A] [Semiring B]
  [HopfAlgebra R A] [Bialgebra R B]

/-- A unital algebra map from a Hopf algebra to a bialgebra that preserves
comultiplication also preserves the counit.

This generalizes the counit-compatibility part of Milne, *Algebraic Groups*
(2017), §3.4, stated for commutative Hopf algebras over a commutative ring:
the base here may be a commutative semiring, neither algebra need be commutative,
and the target need only be a bialgebra. -/
theorem counit_comp_of_map_comp_comul (f : A →ₐ[R] B)
    (hΔ : (TensorProduct.map f.toLinearMap f.toLinearMap) ∘ₗ
      (Coalgebra.comul (R := R) (A := A)) =
        (Coalgebra.comul (R := R) (A := B)) ∘ₗ f.toLinearMap) :
    (Coalgebra.counit (R := R) (A := B)) ∘ₗ f.toLinearMap =
      Coalgebra.counit (R := R) (A := A) := by
  let φ : A →ₐ[R] R := (Bialgebra.counitAlgHom R B).comp f
  let p : WithConv (A →ₗ[R] R) := toConv φ.toLinearMap
  have hε : toConv (Coalgebra.counit (R := R) (A := B)) =
      (1 : WithConv (B →ₗ[R] R)) := by
    ext b
    simp [LinearMap.convOne_def]
  have hcomp :
      TensorProduct.map φ.toLinearMap φ.toLinearMap ∘ₗ
          Coalgebra.comul (R := R) (A := A) =
        TensorProduct.map (Coalgebra.counit (R := R) (A := B))
          (Coalgebra.counit (R := R) (A := B)) ∘ₗ
            Coalgebra.comul (R := R) (A := B) ∘ₗ f.toLinearMap := by
    change TensorProduct.map
        ((Coalgebra.counit (R := R) (A := B)) ∘ₗ f.toLinearMap)
        ((Coalgebra.counit (R := R) (A := B)) ∘ₗ f.toLinearMap) ∘ₗ
          Coalgebra.comul (R := R) (A := A) = _
    rw [TensorProduct.map_comp, LinearMap.comp_assoc, hΔ]
  have hidem : p * p = p := by
    apply ofConv_injective
    change LinearMap.mul' R R ∘ₗ
        (TensorProduct.map φ.toLinearMap φ.toLinearMap ∘ₗ
          Coalgebra.comul (R := R) (A := A)) = φ.toLinearMap
    rw [hcomp]
    change (toConv (Coalgebra.counit (R := R) (A := B)) *
        toConv (Coalgebra.counit (R := R) (A := B)) :
          WithConv (B →ₗ[R] R)).ofConv ∘ₗ f.toLinearMap = φ.toLinearMap
    simp only [hε, one_mul]; ext a; simp [φ, LinearMap.convOne_def]
  have hleft : toConv (φ.toLinearMap.comp (HopfAlgebra.antipode R)) * p =
      (1 : WithConv (A →ₗ[R] R)) := by
    apply ofConv_injective
    calc
      _ = φ.toLinearMap.comp
          (toConv (HopfAlgebra.antipode R) * toConv LinearMap.id :
            WithConv (A →ₗ[R] A)).ofConv := by
        rw [LinearMap.algHom_comp_convMul_distrib]; rfl
      _ = φ.toLinearMap.comp (1 : WithConv (A →ₗ[R] A)).ofConv := by
        rw [LinearMap.antipode_mul_id]
      _ = (1 : WithConv (A →ₗ[R] R)).ofConv :=
        LinearMap.algHom_comp_convOne φ
  have hp : p = 1 := by
    calc
      p = 1 * p := (one_mul p).symm
      _ = (toConv (φ.toLinearMap.comp (HopfAlgebra.antipode R)) * p) * p := by
        rw [hleft]
      _ = toConv (φ.toLinearMap.comp (HopfAlgebra.antipode R)) * (p * p) :=
        mul_assoc _ _ _
      _ = toConv (φ.toLinearMap.comp (HopfAlgebra.antipode R)) * p := by
        rw [hidem]
      _ = 1 := hleft
  apply LinearMap.ext
  intro a
  have ha := LinearMap.congr_fun (congrArg WithConv.ofConv hp) a
  simpa [p, φ, LinearMap.convOne_def] using ha

end AlgHom

namespace AlgHom

variable {R : Type u} {A : Type v} {B : Type w}
  [CommSemiring R] [Semiring A] [Semiring B]
  [HopfAlgebra R A] [Bialgebra R B]


/-- Refine a comultiplication-preserving algebra map from a Hopf algebra to a
bialgebra homomorphism with the same underlying algebra map. Counit preservation
is automatic, so the target need only be a bialgebra. -/
def toBialgHomOfComul (f : A →ₐ[R] B)
    (hf : (TensorProduct.map f.toLinearMap f.toLinearMap) ∘ₗ
      (Coalgebra.comul (R := R) (A := A)) =
        (Coalgebra.comul (R := R) (A := B)) ∘ₗ f.toLinearMap) :
    A →ₐc[R] B :=
  BialgHom.ofAlgHom f
    (AlgHom.toLinearMap_injective (by
      simpa only [AlgHom.comp_toLinearMap, Bialgebra.toLinearMap_counitAlgHom] using
        f.counit_comp_of_map_comp_comul hf))
    (AlgHom.toLinearMap_injective (by
      simpa only [AlgHom.comp_toLinearMap, Bialgebra.toLinearMap_comulAlgHom,
        Algebra.TensorProduct.toLinearMap_map, TensorProduct.AlgebraTensorModule.map_eq] using hf))

variable (f : A →ₐ[R] B)
  (hf : (TensorProduct.map f.toLinearMap f.toLinearMap) ∘ₗ
    (Coalgebra.comul (R := R) (A := A)) =
      (Coalgebra.comul (R := R) (A := B)) ∘ₗ f.toLinearMap)

/-- Refinement preserves the underlying algebra map. -/
@[simp]
theorem toBialgHomOfComul_toAlgHom : (f.toBialgHomOfComul hf).toAlgHom = f := rfl

/-- Refinement preserves the underlying linear map. -/
@[simp]
theorem toBialgHomOfComul_toLinearMap :
    ((f.toBialgHomOfComul hf).toCoalgHom : A →ₗ[R] B) = f.toLinearMap := rfl

/-- Refinement preserves evaluation. -/
@[simp]
theorem toBialgHomOfComul_apply (a : A) : f.toBialgHomOfComul hf a = f a := rfl

end AlgHom

namespace BialgHom

variable {R : Type u} {A : Type v} {B : Type w}
  [CommSemiring R] [Semiring A] [Semiring B]
  [HopfAlgebra R A] [Bialgebra R B]

/-- Forgetting a bialgebra homomorphism and refining it again recovers the same
bundled morphism. -/
@[simp]
theorem toAlgHom_toBialgHomOfComul (F : A →ₐc[R] B) :
    F.toAlgHom.toBialgHomOfComul (CoalgHomClass.map_comp_comul F) = F := by
  exact BialgHom.ext fun _ => rfl

end BialgHom
