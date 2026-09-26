/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.Vector
public import Mathlib.Algebra.Field.ZMod

/-!
# Private vector-group regression clients

Named private declarations persist the original ordinary-import examples in
the compiled test without adding a public mathematical API.
-/

public section

set_option warningAsError true

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct

namespace AlgebraicGeometry

universe u v

section Generic

variable (K : Type u) [CommRing K] (M : Type v) [AddCommMonoid M] [Module K M]
  (R : Type u) [CommRing R] [Algebra K R]

private def testLinearMapConvolutionEquiv : Multiplicative (M →ₗ[K] R) ≃*
    WithConv (SymmetricAlgebra K M →ₐ[K] R) :=
  SymmetricAlgebra.linearMapMulEquivAlgHom K M R

private theorem testConvolutionAdds (f g : M →ₗ[K] R) :
    SymmetricAlgebra.linearMapMulEquivAlgHom K M R (.ofAdd (f + g)) =
      SymmetricAlgebra.linearMapMulEquivAlgHom K M R (.ofAdd f) *
        SymmetricAlgebra.linearMapMulEquivAlgHom K M R (.ofAdd g) :=
  (SymmetricAlgebra.linearMapMulEquivAlgHom K M R).map_mul (.ofAdd f) (.ofAdd g)

private theorem testConvolutionZero : SymmetricAlgebra.linearMapMulEquivAlgHom K M R (.ofAdd 0) = 1 :=
  SymmetricAlgebra.linearMapMulEquivAlgHom_zero K M R

private theorem testConvolutionLeftInverse (f : M →ₗ[K] R) :
    SymmetricAlgebra.linearMapMulEquivAlgHom K M R (.ofAdd (-f)) *
      SymmetricAlgebra.linearMapMulEquivAlgHom K M R (.ofAdd f) = 1 :=
  SymmetricAlgebra.linearMapMulEquivAlgHom_neg_mul K M R f

private theorem testConvolutionRightInverse (f : M →ₗ[K] R) :
    SymmetricAlgebra.linearMapMulEquivAlgHom K M R (.ofAdd f) *
      SymmetricAlgebra.linearMapMulEquivAlgHom K M R (.ofAdd (-f)) = 1 :=
  SymmetricAlgebra.linearMapMulEquivAlgHom_mul_neg K M R f

private theorem testConvolutionGenerator (f : M →ₗ[K] R) (m : M) :
    (SymmetricAlgebra.linearMapMulEquivAlgHom K M R (.ofAdd f)).ofConv
      (SymmetricAlgebra.ι K M m) = f m := by simp

private theorem testConvolutionNaturality {S : Type u} [CommRing S] [Algebra K S]
    (h : R →ₐ[K] S) (f : M →ₗ[K] R) :
    (SymmetricAlgebra.linearMapMulEquivAlgHom K M S (.ofAdd
      (h.toLinearMap.comp f))).ofConv =
        h.comp (SymmetricAlgebra.linearMapMulEquivAlgHom K M R (.ofAdd f)).ofConv :=
  SymmetricAlgebra.linearMapMulEquivAlgHom_naturality K M R h f

end Generic

variable (K : Type u) [Field K] (V : Type u) [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  (R : Type u) [CommRing R] [Algebra K R]

private theorem testCoordinateFiniteType : Algebra.FiniteType K (vectorGroupCoordinateRing K V) := inferInstance

private theorem testSchemeLocallyFiniteType : LocallyOfFiniteType (vectorGroupUnderlyingScheme K V).hom := inferInstance

omit [FiniteDimensional K V] in
private theorem testSchemeQuasiCompact [FiniteDimensional K V] :
    QuasiCompact (vectorGroupUnderlyingScheme K V).hom := inferInstance

private def testVectorScheme : Grp (Over (Spec (.of K))) := vectorGroupScheme K V

private def testPointsIso : vectorGroupFunctor K V ≅ vectorGroupPointsFunctor K V :=
  vectorGroupPointsIso K V

omit [FiniteDimensional K V] in
private theorem testFunctorMap [FiniteDimensional K V]
    (R : Type u) [CommRing R] [Algebra K R]
    {S : Type u} [CommRing S] [Algebra K S]
    (f : R →ₐ[K] S) (x : V ⊗[K] R) :
    (vectorGroupFunctor K V).map (CommAlgCat.ofHom f) (.ofAdd x) =
      .ofAdd (TensorProduct.map (LinearMap.id : V →ₗ[K] V) f.toLinearMap x) :=
  rfl

private def testTensorDualEquiv : (V ⊗[K] R) ≃ₗ[K] (Module.Dual K V →ₗ[K] R) :=
  vectorGroupTensorDualEquiv K V R

private theorem testTensorSumEvaluation (v w : V) (r s : R) (φ : Module.Dual K V) :
    vectorGroupTensorDualEquiv K V R (v ⊗ₜ[K] r + w ⊗ₜ[K] s) φ =
      (φ v) • r + (φ w) • s := by simp

private theorem testTensorNaturality {S : Type u} [CommRing S] [Algebra K S]
    (f : R →ₐ[K] S) (x : V ⊗[K] R) (φ : Module.Dual K V) :
    vectorGroupTensorDualEquiv K V S
      (TensorProduct.map (LinearMap.id : V →ₗ[K] V) f.toLinearMap x) φ =
      f (vectorGroupTensorDualEquiv K V R x φ) :=
  vectorGroupTensorDualEquiv_naturality K V R S f x φ

private theorem testTensorLinearMap (W : Type u) [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (f : V →ₗ[K] W) (x : V ⊗[K] R) (φ : Module.Dual K W) :
    vectorGroupTensorDualEquiv K W R
      (TensorProduct.map f (LinearMap.id : R →ₗ[K] R) x) φ =
      vectorGroupTensorDualEquiv K V R x (φ.comp f) :=
  vectorGroupTensorDualEquiv_linearMap K V W f R x φ

omit [FiniteDimensional K V] in
private theorem testCoordinatePullback [FiniteDimensional K V]
    (W : Type u) [AddCommGroup W] [Module K W]
    (f : V →ₗ[K] W) (φ : Module.Dual K W) :
    vectorGroupCoordinateMap K V W f (SymmetricAlgebra.ι K _ φ) =
      SymmetricAlgebra.ι K _ (φ.comp f) := by simp

private theorem testPointsLinearMap (W : Type u) [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (f : V →ₗ[K] W) (x : V ⊗[K] R) :
    (vectorGroupMulEquivAlgHom K W R (.ofAdd
      (TensorProduct.map f (LinearMap.id : R →ₗ[K] R) x))).ofConv =
      (vectorGroupMulEquivAlgHom K V R (.ofAdd x)).ofConv.comp
        (vectorGroupCoordinateMap K V W f) :=
  vectorGroupMulEquivAlgHom_linearMap K V R W f x

private theorem testTensorConvolutionAdds (x y : V ⊗[K] R) :
    vectorGroupMulEquivAlgHom K V R (.ofAdd (x + y)) =
      vectorGroupMulEquivAlgHom K V R (.ofAdd x) *
        vectorGroupMulEquivAlgHom K V R (.ofAdd y) :=
  (vectorGroupMulEquivAlgHom K V R).map_mul (.ofAdd x) (.ofAdd y)

private theorem testTensorGenerator (v : V) (r : R) (φ : Module.Dual K V) :
    (vectorGroupMulEquivAlgHom K V R (.ofAdd (v ⊗ₜ[K] r))).ofConv
      (SymmetricAlgebra.ι K _ φ) = (φ v) • r := by simp

private theorem testTensorConvolutionNaturality {S : Type u} [CommRing S] [Algebra K S]
    (f : R →ₐ[K] S) (x : V ⊗[K] R) :
    (vectorGroupMulEquivAlgHom K V S (.ofAdd
      (TensorProduct.map (LinearMap.id : V →ₗ[K] V) f.toLinearMap x))).ofConv =
      f.comp (vectorGroupMulEquivAlgHom K V R (.ofAdd x)).ofConv :=
  vectorGroupMulEquivAlgHom_naturality K V R f x

private def testRepresentedPoints : Multiplicative (V ⊗[K] R) ≃*
    ((Spec (.of R)).asOver (Spec (.of K)) ⟶ (vectorGroupScheme K V).X) :=
  vectorGroupMulEquivPoints K V R

private theorem testRepresentedPointsSpecMap (x : V ⊗[K] R) :
    (vectorGroupMulEquivPoints K V R (.ofAdd x)).left =
      Spec.map (CommRingCat.ofHom
        (vectorGroupMulEquivAlgHom K V R (.ofAdd x)).ofConv.toRingHom) :=
  vectorGroupMulEquivPoints_apply_left K V R x

section FiniteField

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- A concrete algebra structure on the zero ring for finite-field clients. -/
local instance zeroRingAlgebra : Algebra (ZMod 2) (ZMod 1) :=
  (ZMod.castHom (show 1 ∣ 2 by decide) (ZMod 1)).toAlgebra

private def testZeroRingPoints : Multiplicative ((Fin 1 → ZMod 2) ⊗[ZMod 2] ZMod 1) ≃*
    ((Spec (.of (ZMod 1))).asOver (Spec (.of (ZMod 2))) ⟶
      (vectorGroupScheme (ZMod 2) (Fin 1 → ZMod 2)).X) :=
  vectorGroupMulEquivPoints (ZMod 2) (Fin 1 → ZMod 2) (ZMod 1)

private def testZeroRingNaturality : vectorGroupFunctor (ZMod 2) (Fin 1 → ZMod 2) ≅
    vectorGroupPointsFunctor (ZMod 2) (Fin 1 → ZMod 2) :=
  vectorGroupPointsIso (ZMod 2) (Fin 1 → ZMod 2)

private theorem testFiniteFieldGenerator (v : Fin 1 → ZMod 2)
    (φ : Module.Dual (ZMod 2) (Fin 1 → ZMod 2)) :
    (vectorGroupMulEquivAlgHom (ZMod 2) (Fin 1 → ZMod 2) (ZMod 2)
      (.ofAdd (v ⊗ₜ[ZMod 2] 1))).ofConv
        (SymmetricAlgebra.ι (ZMod 2) _ φ) = φ v := by simp

private theorem testZeroRingBaseChange (x : (Fin 1 → ZMod 2) ⊗[ZMod 2] ZMod 2) :
    (vectorGroupMulEquivAlgHom (ZMod 2) (Fin 1 → ZMod 2) (ZMod 1)
      (.ofAdd (TensorProduct.map
        (LinearMap.id : (Fin 1 → ZMod 2) →ₗ[ZMod 2] (Fin 1 → ZMod 2))
        (Algebra.ofId (ZMod 2) (ZMod 1)).toLinearMap x))).ofConv =
        (Algebra.ofId (ZMod 2) (ZMod 1)).comp
          (vectorGroupMulEquivAlgHom (ZMod 2) (Fin 1 → ZMod 2)
            (ZMod 2) (.ofAdd x)).ofConv :=
  vectorGroupMulEquivAlgHom_naturality (ZMod 2) (Fin 1 → ZMod 2)
    (ZMod 2) (Algebra.ofId (ZMod 2) (ZMod 1)) x

end FiniteField

private theorem testZeroDimensionSubsingleton : Subsingleton (Multiplicative ((Fin 0 → K) ⊗[K] R)) :=
  inferInstance

private theorem testZeroDimensionIdentity (x : Multiplicative ((Fin 0 → K) ⊗[K] R)) : x = 1 :=
  Subsingleton.elim x 1

private theorem testZeroDimensionEvaluation (x : (Fin 0 → K) ⊗[K] R)
    (φ : Module.Dual K (Fin 0 → K)) :
    vectorGroupTensorDualEquiv K (Fin 0 → K) R x φ = 0 := by
  have : x = 0 := Subsingleton.elim x 0
  subst x
  simp

private theorem testZeroDimensionFiniteType : Algebra.FiniteType K (vectorGroupCoordinateRing K (Fin 0 → K)) :=
  inferInstance

private def testZeroDimensionIso : vectorGroupFunctor K (Fin 0 → K) ≅
    vectorGroupPointsFunctor K (Fin 0 → K) :=
  vectorGroupPointsIso K (Fin 0 → K)

private def testZeroDimensionPoints : Multiplicative ((Fin 0 → K) ⊗[K] R) ≃*
    ((Spec (.of R)).asOver (Spec (.of K)) ⟶
      (vectorGroupScheme K (Fin 0 → K)).X) :=
  vectorGroupMulEquivPoints K (Fin 0 → K) R

end AlgebraicGeometry

namespace NativeVectorReductionTests

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct

universe u v

variable (K : Type u) [CommRing K] (M : Type v) [AddCommMonoid M] [Module K M]
  (R : Type u) [CommRing R] [Algebra K R]

private theorem testLinearMapForward (f : M →ₗ[K] R) :
    SymmetricAlgebra.linearMapMulEquivAlgHom K M R (.ofAdd f) =
      WithConv.toConv (SymmetricAlgebra.lift f) := rfl

private theorem testLinearMapInverse (g : SymmetricAlgebra K M →ₐ[K] R) :
    (SymmetricAlgebra.linearMapMulEquivAlgHom K M R).symm (WithConv.toConv g) =
      .ofAdd (SymmetricAlgebra.lift.symm g) := rfl

variable (F : Type u) [Field F] (V : Type u) [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] (S : Type u) [CommRing S] [Algebra F S]

private theorem testTensorForward (x : V ⊗[F] S) :
    vectorGroupTensorDualEquiv F V S x =
      (IsBaseChange.linearMapRightBaseChangeEquiv (Module.Dual F V)
        (IsBaseChange.linearMap F S)).restrictScalars F
        (((Module.evalEquiv F V).baseChange F S).restrictScalars F
          ((TensorProduct.comm F V S) x)) := rfl

private theorem testTensorInverse (h : Module.Dual F V →ₗ[F] S) :
    (vectorGroupTensorDualEquiv F V S).symm h =
      (TensorProduct.comm F V S).symm
        ((((Module.evalEquiv F V).baseChange F S).restrictScalars F).symm
          (((IsBaseChange.linearMapRightBaseChangeEquiv (Module.Dual F V)
            (IsBaseChange.linearMap F S)).restrictScalars F).symm h)) := rfl

omit [FiniteDimensional F V] in
private theorem testCoordinatePullbackData
    (W : Type u) [AddCommGroup W] [Module F W] (f : V →ₗ[F] W) :
    vectorGroupCoordinateMap F V W f =
      SymmetricAlgebra.lift
        ((SymmetricAlgebra.ι F (Module.Dual F V)).comp f.dualMap) := rfl

omit [FiniteDimensional F V] in
private theorem testFunctorObject (A : CommAlgCat F) :
    (vectorGroupFunctor F V).obj A = GrpCat.of (Multiplicative (V ⊗[F] A)) := rfl

private theorem testConvolutionData :
    vectorGroupMulEquivAlgHom F V S =
      (vectorGroupTensorDualEquiv F V S).toAddEquiv.toMultiplicative.trans
        (SymmetricAlgebra.linearMapMulEquivAlgHom F (Module.Dual F V) S) := rfl

private theorem testRepresentedPointsData :
    vectorGroupMulEquivPoints F V S =
      (vectorGroupMulEquivAlgHom F V S).trans
        (Spec.mapMulEquiv (R := F) (S := vectorGroupCoordinateRing F V) (T := S)) := rfl

private theorem testIsoComponent (A : CommAlgCat F) :
    (vectorGroupPointsIso F V).hom.app A =
      (vectorGroupMulEquivPoints F V A).toGrpIso.hom := rfl

end NativeVectorReductionTests
