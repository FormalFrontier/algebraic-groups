/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.VectorProduct
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.StdBasis

/-!
# Vector-group product regression clients

Named private declarations persist the original ordinary-import examples without
adding public mathematical APIs.
-/

public section

set_option warningAsError true

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct

namespace AlgebraicGeometry

universe u

variable (K : Type u) [Field K]
  (V : Type u) [AddCommGroup V] [Module K V]
  (W : Type u) [AddCommGroup W] [Module K W]

private def testSchemeMap (f : V →ₗ[K] W) : vectorGroupScheme K V ⟶ vectorGroupScheme K W :=
  vectorGroupSchemeMap K V W f

private def testSchemeFunctor : ModuleCat.{u} K ⥤ Grp (Over (Spec (.of K))) :=
  vectorGroupSchemeFunctor K

private theorem testSchemeFunctorMap (f : V →ₗ[K] W) :
    (vectorGroupSchemeFunctor K).map (ModuleCat.ofHom f) =
      vectorGroupSchemeMap K V W f := rfl

private theorem testCoordinateBialgHom (f : V →ₗ[K] W) (φ : Module.Dual K W) :
    vectorGroupCoordinateBialgHom K V W f (SymmetricAlgebra.ι K _ φ) =
      SymmetricAlgebra.ι K _ (φ.comp f) := by simp

private theorem testSchemeMapLeft (f : V →ₗ[K] W) :
    (vectorGroupSchemeMap K V W f).hom.hom.left =
      Spec.map (CommRingCat.ofHom
        (vectorGroupCoordinateMap K V W f).toRingHom) :=
  vectorGroupSchemeMap_left K V W f

private theorem testSchemeMapId : vectorGroupSchemeMap K V V LinearMap.id = 𝟙 _ := by simp

private theorem testSchemeMapComp (U : Type u) [AddCommGroup U] [Module K U]
    (f : V →ₗ[K] W) (g : W →ₗ[K] U) :
    vectorGroupSchemeMap K V U (g.comp f) =
      vectorGroupSchemeMap K V W f ≫ vectorGroupSchemeMap K W U g := by simp

variable {i j : Type u} [Finite i] [Finite j]
  (b : Module.Basis i K V) (c : Module.Basis j K W)

private def testProductIso : vectorGroupScheme K V ≅ (∏ᶜ fun _ : i ↦ additiveGroupScheme K) :=
  vectorGroupSchemeProductIso K V b

private def testUnderlyingIsLimit : Limits.IsLimit ((Grp.forget (Over (Spec (.of K)))).mapCone
    (vectorGroupBasisFan K V b)) :=
  vectorGroupBasisFan_forget_isLimit K V b

private def testHomOverEquiv (X : Over (Spec (.of K))) :
    (X ⟶ (vectorGroupScheme K V).X) ≃
      (Module.Dual K V →ₗ[K] ((algΓ (.of K)).obj X).unop) :=
  vectorGroupHomOverEquiv K V X

private theorem testAffineSpecHomForward (X : Over (Spec (.of K)))
    (A : Type u) [CommRing A] [Algebra K A]
    (h : X ⟶ (algSpec (.of K)).obj (.op (CommAlgCat.of K A))) :
    affineSpecHomOverEquiv K X A h =
      (((algΓAlgSpecAdjunction (.of K)).homEquiv X
        (.op (CommAlgCat.of K A))).symm h).unop.hom := rfl

private theorem testAffineSpecHomInverse (X : Over (Spec (.of K)))
    (A : Type u) [CommRing A] [Algebra K A]
    (h : A →ₐ[K] ((algΓ (.of K)).obj X).unop) :
    (affineSpecHomOverEquiv K X A).symm h =
      (algΓAlgSpecAdjunction (.of K)).homEquiv X
        (.op (CommAlgCat.of K A)) (CommAlgCat.ofHom h).op := rfl

private theorem testVectorHomForward (X : Over (Spec (.of K)))
    (h : X ⟶ (vectorGroupScheme K V).X) :
    vectorGroupHomOverEquiv K V X h =
      SymmetricAlgebra.lift.symm
        (affineSpecHomOverEquiv K X (vectorGroupCoordinateRing K V) h) := rfl

private theorem testAdditiveHomForward (X : Over (Spec (.of K)))
    (h : X ⟶ (additiveGroupScheme K).X) :
    additiveGroupHomOverEquiv K X h =
      (LinearMap.ringLmapEquivSelf K K ((algΓ (.of K)).obj X).unop)
        (SymmetricAlgebra.lift.symm
          (affineSpecHomOverEquiv K X (additiveGroupCoordinateRing K) h)) := rfl

section UnderlyingFanLift

open Classical

private theorem testUnderlyingFanLift
    (s : Limits.Fan (fun _ : i ↦ (additiveGroupScheme K).X)) :
    (vectorGroupBasisFan_forget_isLimit K V b).lift s =
      (vectorGroupHomOverEquiv K V s.pt).symm
        (b.dualBasis.constr K (fun j ↦ additiveGroupHomOverEquiv K s.pt (s.proj j))) := by
  classical
  rfl

end UnderlyingFanLift

private theorem testProductIsoHomProjection (k : i) :
    (vectorGroupSchemeProductIso K V b).hom ≫
      Limits.Pi.π (fun _ : i ↦ additiveGroupScheme K) k =
      vectorGroupProjection K V b k := by simp

private theorem testProductIsoInvProjection (k : i) :
    (vectorGroupSchemeProductIso K V b).inv ≫ vectorGroupProjection K V b k =
      Limits.Pi.π (fun _ : i ↦ additiveGroupScheme K) k := by simp

omit b [Finite i] in
/-- Retain the original regression's finite-index hypothesis, even for a single coordinate. -/
@[nolint unusedArguments]
private theorem testProjectionGlobalCoordinate [Finite i] (b : Module.Basis i K V)
    (X : Over (Spec (.of K)))
    (h : X ⟶ (vectorGroupScheme K V).X)
    (k : i) :
    additiveGroupHomOverEquiv K X (h ≫ (vectorGroupProjection K V b k).hom.hom) =
      (vectorGroupHomOverEquiv K V X h) (b.coord k) :=
  vectorGroupProjection_globalCoordinate K V b k X h

omit b c [Finite i] [Finite j] in
/-- The original regression includes both finite-index hypotheses as well as its chosen basis. -/
@[nolint unusedArguments]
private theorem testCoordinateMapBasis [Finite i] [Finite j]
    (b : Module.Basis i K V) (c : Module.Basis j K W) [Fintype i]
    (f : V →ₗ[K] W) (k : j) :
    vectorGroupCoordinateMap K V W f (SymmetricAlgebra.ι K _ (c.coord k)) =
      ∑ s : i, (c.coord k (f (b s))) •
        SymmetricAlgebra.ι K _ (b.coord s) :=
  vectorGroupCoordinateMap_basis K V W b c f k

omit b c [Finite i] [Finite j] in
/-- Preserve the original finite-index context while checking the scheme-map coordinate. -/
@[nolint unusedArguments]
private theorem testSchemeMapProjectionCoordinate [Finite i] [Finite j]
    (b : Module.Basis i K V) (c : Module.Basis j K W) [Fintype i]
    (f : V →ₗ[K] W) (k : j) :
    ((vectorGroupCoordinateBialgHom K V W f).comp
      (vectorGroupProjectionBialgHom K W c k)) (additiveGroupCoordinate K) =
      ∑ s : i, (c.coord k (f (b s))) •
        (vectorGroupProjectionBialgHom K V b s) (additiveGroupCoordinate K) :=
  vectorGroupSchemeMap_projection_coordinate K V W b c f k

private theorem testBasisMapSquare (f : V →ₗ[K] W) :
    (vectorGroupSchemeProductIso K V b).hom ≫ vectorGroupBasisMap K V W b c f =
      vectorGroupSchemeMap K V W f ≫ (vectorGroupSchemeProductIso K W c).hom := by simp

private theorem testBasisMapProjection (f : V →ₗ[K] W) (k : j) :
    vectorGroupBasisMap K V W b c f ≫
        Limits.Pi.π (fun _ : j ↦ additiveGroupScheme K) k =
      (vectorGroupSchemeProductIso K V b).inv ≫
        vectorGroupSchemeMap K V W f ≫ vectorGroupProjection K W c k :=
  vectorGroupBasisMap_projection K V W b c f k

private theorem testChangeBasisRoundTrip (d : Module.Basis i K V) :
    vectorGroupBasisMap K V V b d LinearMap.id ≫
      vectorGroupBasisMap K V V d b LinearMap.id = 𝟙 _ := by
  rw [vectorGroupBasisMap_changeBasis_comp K V b d b]
  exact vectorGroupBasisMap_id K V b

section FiniteDimensional

variable [FiniteDimensional K V] [FiniteDimensional K W]
  (R : Type u) [CommRing R] [Algebra K R]

private theorem testSchemeMapPoints (f : V →ₗ[K] W) (x : V ⊗[K] R) :
    vectorGroupMulEquivPoints K V R (.ofAdd x) ≫
      (vectorGroupSchemeMap K V W f).hom.hom =
      vectorGroupMulEquivPoints K W R (.ofAdd
        (TensorProduct.map f (LinearMap.id : R →ₗ[K] R) x)) :=
  vectorGroupSchemeMap_points K V W R f x

omit b c [Finite i] [Finite j] [FiniteDimensional K V] [FiniteDimensional K W]
    R [CommRing R] [Algebra K R] in
/-- Preserve the original finite-index and finite-dimensional regression context. -/
@[nolint unusedArguments]
private theorem testTensorDualBasis [Finite i] [Finite j]
    (b : Module.Basis i K V) (c : Module.Basis j K W)
    [FiniteDimensional K V] [FiniteDimensional K W]
    (R : Type u) [CommRing R] [Algebra K R] [Fintype i]
    (f : V →ₗ[K] W) (x : V ⊗[K] R) (k : j) :
    vectorGroupTensorDualEquiv K W R
        (TensorProduct.map f (LinearMap.id : R →ₗ[K] R) x) (c.coord k) =
      ∑ s : i, (c.coord k (f (b s))) •
        vectorGroupTensorDualEquiv K V R x (b.coord s) :=
  vectorGroupTensorDualEquiv_basis K V W b c f R x k

omit b c [Finite i] [Finite j] [FiniteDimensional K V] [FiniteDimensional K W]
    R [CommRing R] [Algebra K R] in
/-- Preserve the original finite-index and finite-dimensional regression context. -/
@[nolint unusedArguments]
private theorem testMulEquivAlgHomBasis [Finite i] [Finite j]
    (b : Module.Basis i K V) (c : Module.Basis j K W)
    [FiniteDimensional K V] [FiniteDimensional K W]
    (R : Type u) [CommRing R] [Algebra K R] [Fintype i]
    (f : V →ₗ[K] W) (x : V ⊗[K] R) (k : j) :
    (vectorGroupMulEquivAlgHom K W R (.ofAdd
      (TensorProduct.map f (LinearMap.id : R →ₗ[K] R) x))).ofConv
        (SymmetricAlgebra.ι K _ (c.coord k)) =
      ∑ s : i, (algebraMap K R (c.coord k (f (b s)))) *
        (vectorGroupMulEquivAlgHom K V R (.ofAdd x)).ofConv
          (SymmetricAlgebra.ι K _ (b.coord s)) :=
  vectorGroupMulEquivAlgHom_basis K V W b c f R x k

omit b [Finite i] [FiniteDimensional K V] R [CommRing R] [Algebra K R] in
/-- Retain the original finite-index hypothesis in the pure-tensor coordinate regression. -/
@[nolint unusedArguments]
private theorem testCoordinatePureTensor [Finite i] (b : Module.Basis i K V)
    [FiniteDimensional K V] (R : Type u) [CommRing R] [Algebra K R]
    (v : V) (r : R) (k : i) :
    vectorGroupTensorDualEquiv K V R (v ⊗ₜ[K] r) (b.coord k) =
      (b.coord k v) • r := by simp

private theorem testTensorNaturality (S : Type u) [CommRing S] [Algebra K S]
    (f : V →ₗ[K] W) (g : R →ₐ[K] S) (x : V ⊗[K] R) :
    TensorProduct.map (LinearMap.id : W →ₗ[K] W) g.toLinearMap
        (TensorProduct.map f (LinearMap.id : R →ₗ[K] R) x) =
      TensorProduct.map f (LinearMap.id : S →ₗ[K] S)
        (TensorProduct.map (LinearMap.id : V →ₗ[K] V) g.toLinearMap x) :=
  vectorGroupSchemeMap_tensor_naturality K V W R S f g x

end FiniteDimensional

section Concrete

variable (k : Type) [Field k]

private def testFinZeroProductIso : vectorGroupScheme k (Fin 0 → k) ≅
    (∏ᶜ fun _ : Fin 0 ↦ additiveGroupScheme k) :=
  vectorGroupSchemeProductIso k _ (Pi.basisFun k (Fin 0))

private def testFinOneProductIso : vectorGroupScheme k (Fin 1 → k) ≅
    (∏ᶜ fun _ : Fin 1 ↦ additiveGroupScheme k) :=
  vectorGroupSchemeProductIso k _ (Pi.basisFun k (Fin 1))

private def testFinTwoProductIso : vectorGroupScheme k (Fin 2 → k) ≅
    (∏ᶜ fun _ : Fin 2 ↦ additiveGroupScheme k) :=
  vectorGroupSchemeProductIso k _ (Pi.basisFun k (Fin 2))

private def testFinZeroTerminalIso : vectorGroupScheme k (Fin 0 → k) ≅
    ⊤_ (Grp (Over (Spec (.of k)))) :=
  vectorGroupSchemeZeroIso k _

private def testFinZeroUnderlyingIso : (vectorGroupScheme k (Fin 0 → k)).X ≅
    Over.mk (𝟙 (Spec (.of k))) :=
  vectorGroupUnderlyingZeroIso k _

end Concrete

section FiniteField

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- The zero ring is a `ZMod 2` algebra for the degenerate target regressions. -/
local instance zeroRingAlgebra : Algebra (ZMod 2) (ZMod 1) :=
  (ZMod.castHom (show 1 ∣ 2 by decide) (ZMod 1)).toAlgebra

private theorem testZeroAlgebraPoints (x : (Fin 2 → ZMod 2) ⊗[ZMod 2] ZMod 1) :
    vectorGroupMulEquivPoints (ZMod 2) (Fin 2 → ZMod 2) (ZMod 1) (.ofAdd x) ≫
      (vectorGroupSchemeMap (ZMod 2) _ _
        (LinearMap.id : (Fin 2 → ZMod 2) →ₗ[ZMod 2] (Fin 2 → ZMod 2))).hom.hom =
        vectorGroupMulEquivPoints (ZMod 2) _ (ZMod 1) (.ofAdd
          (TensorProduct.map LinearMap.id (LinearMap.id : ZMod 1 →ₗ[ZMod 2] ZMod 1) x)) :=
  vectorGroupSchemeMap_points (ZMod 2) _ _ (ZMod 1) _ x

private def testFiniteFieldProductIso : vectorGroupScheme (ZMod 2) (Fin 2 → ZMod 2) ≅
    (∏ᶜ fun _ : Fin 2 ↦ additiveGroupScheme (ZMod 2)) :=
  vectorGroupSchemeProductIso (ZMod 2) _ (Pi.basisFun (ZMod 2) (Fin 2))

private theorem testFiniteFieldCoordinateMap
    (f : (Fin 2 → ZMod 2) →ₗ[ZMod 2] (Fin 2 → ZMod 2)) (j : Fin 2) :
    vectorGroupCoordinateMap (ZMod 2) _ _ f
        (SymmetricAlgebra.ι (ZMod 2) _ ((Pi.basisFun (ZMod 2) (Fin 2)).coord j)) =
      ∑ s : Fin 2,
        (((Pi.basisFun (ZMod 2) (Fin 2)).coord j) (f ((Pi.basisFun (ZMod 2) (Fin 2)) s))) •
          SymmetricAlgebra.ι (ZMod 2) _ ((Pi.basisFun (ZMod 2) (Fin 2)).coord s) :=
  vectorGroupCoordinateMap_basis (ZMod 2) _ _
    (Pi.basisFun (ZMod 2) (Fin 2)) (Pi.basisFun (ZMod 2) (Fin 2)) f j

private theorem testPolynomialEvaluation
    (x : (Fin 1 → ZMod 2) ⊗[ZMod 2] Polynomial (ZMod 2)) :
    TensorProduct.map (LinearMap.id : (Fin 1 → ZMod 2) →ₗ[ZMod 2] _)
      (Polynomial.aeval (0 : ZMod 2)).toLinearMap
      (TensorProduct.map LinearMap.id
        (LinearMap.id : Polynomial (ZMod 2) →ₗ[ZMod 2] _) x) =
      TensorProduct.map LinearMap.id (LinearMap.id : ZMod 2 →ₗ[ZMod 2] _)
        (TensorProduct.map LinearMap.id
          (Polynomial.aeval (0 : ZMod 2)).toLinearMap x) :=
  vectorGroupSchemeMap_tensor_naturality (ZMod 2) _ _
    (Polynomial (ZMod 2)) (ZMod 2) LinearMap.id (Polynomial.aeval 0) x

end FiniteField

end AlgebraicGeometry
