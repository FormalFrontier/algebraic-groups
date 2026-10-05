/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.SymmetricAlgebraPoints
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom

/-!
# Vector group schemes

For a finite-dimensional vector space `V` over a field `K`, the symmetric algebra
on its dual represents the additive group functor `R ↦ V ⊗[K] R`.
The tensor–dual equivalence is canonical; finite dimensionality is used for
its inverse and for finite type of the coordinate ring.

Milne's item 2.6 gives the finite-dimensional field-base vector group,
its dual symmetric-algebra coordinates and representation on all test
algebras. This implementation uses Mathlib's double-dual evaluation,
finite-free base change and symmetric-algebra/convolution interfaces;
the coordinate map itself needs no finite-dimensionality.

## References

- J. S. Milne, *Algebraic Groups* (2017), item 2.6 (vector group and
  dual symmetric coordinates).
- Mathlib, `Mathlib.LinearAlgebra.Dual.Defs` (`Module.evalEquiv`),
  `Mathlib.RingTheory.TensorProduct.IsBaseChangeHom` (linear-map base change),
  `Mathlib.LinearAlgebra.SymmetricAlgebra.Basis` (polynomial coordinates),
  and `Mathlib.AlgebraicGeometry.Group.Affine` (affine group points).
-/

public section

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [Field K] (V : Type u) [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- The canonical, source-order tensor/evaluation equivalence. Its
finite-dimensional field-base identification is in Milne, *Algebraic Groups*
(2017), item 2.6; the inverse uses Mathlib's `Module.evalEquiv` and
`IsBaseChange.linearMapRightBaseChangeEquiv`. -/
@[expose] def vectorGroupTensorDualEquiv (R : Type u) [CommRing R] [Algebra K R] :
    (V ⊗[K] R) ≃ₗ[K] (Module.Dual K V →ₗ[K] R) :=
  let first : (V ⊗[K] R) ≃ₗ[K] (R ⊗[K] V) := TensorProduct.comm K V R
  let second : (R ⊗[K] V) ≃ₗ[K] (R ⊗[K] Module.Dual K (Module.Dual K V)) :=
    ((Module.evalEquiv K V).baseChange K R).restrictScalars K
  let third : (R ⊗[K] Module.Dual K (Module.Dual K V)) ≃ₗ[K]
      (Module.Dual K V →ₗ[K] R) :=
    (IsBaseChange.linearMapRightBaseChangeEquiv (Module.Dual K V)
      (IsBaseChange.linearMap K R)).restrictScalars K
  (first.trans second).trans third

@[simp]
theorem vectorGroupTensorDualEquiv_tmul (R : Type u) [CommRing R] [Algebra K R]
    (v : V) (r : R) (φ : Module.Dual K V) :
    vectorGroupTensorDualEquiv K V R (v ⊗ₜ[K] r) φ = (φ v) • r := by
  simp [vectorGroupTensorDualEquiv, IsBaseChange.linearMapRightBaseChangeEquiv,
    IsBaseChange.linearMapRightBaseChangeHom, Algebra.smul_def, mul_comm]

/-- Evaluation commutes with extension of scalars along every algebra map. -/
theorem vectorGroupTensorDualEquiv_naturality (R S : Type u) [CommRing R] [Algebra K R]
    [CommRing S] [Algebra K S] (f : R →ₐ[K] S) (x : V ⊗[K] R)
    (φ : Module.Dual K V) :
    vectorGroupTensorDualEquiv K V S
      (TensorProduct.map (LinearMap.id : V →ₗ[K] V) f.toLinearMap x) φ =
      f (vectorGroupTensorDualEquiv K V R x φ) := by
  induction x using TensorProduct.inductionOn with
  | tmul v r => simp [map_smul]
  | add x y hx hy => simp [hx, hy]

/-- Evaluation is covariant in vectors and contravariant in linear coordinates. -/
theorem vectorGroupTensorDualEquiv_linearMap
    (W : Type u) [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (f : V →ₗ[K] W) (R : Type u) [CommRing R] [Algebra K R]
    (x : V ⊗[K] R) (φ : Module.Dual K W) :
    vectorGroupTensorDualEquiv K W R
      (TensorProduct.map f (LinearMap.id : R →ₗ[K] R) x) φ =
      vectorGroupTensorDualEquiv K V R x (φ.comp f) := by
  induction x using TensorProduct.inductionOn with
  | tmul v r => simp
  | add x y hx hy => simp [hx, hy]

/-- The symmetric coordinate algebra on the linear dual. -/
abbrev vectorGroupCoordinateRing : Type u := SymmetricAlgebra K (Module.Dual K V)

/-- A linear map induces the pullback of polynomial coordinates. -/
@[expose] def vectorGroupCoordinateMap
    (W : Type u) [AddCommGroup W] [Module K W]
    (f : V →ₗ[K] W) :
    vectorGroupCoordinateRing K W →ₐ[K] vectorGroupCoordinateRing K V :=
  SymmetricAlgebra.lift ((SymmetricAlgebra.ι K (Module.Dual K V)).comp f.dualMap)

omit [FiniteDimensional K V] in
@[simp]
theorem vectorGroupCoordinateMap_ι
    (W : Type u) [AddCommGroup W] [Module K W]
    (f : V →ₗ[K] W) (φ : Module.Dual K W) :
    vectorGroupCoordinateMap K V W f (SymmetricAlgebra.ι K _ φ) =
      SymmetricAlgebra.ι K _ (φ.comp f) := by
  simp only [vectorGroupCoordinateMap, SymmetricAlgebra.lift_ι_apply,
    LinearMap.comp_apply]
  congr 1

instance vectorGroupCoordinateRing_finiteType :
    Algebra.FiniteType K (vectorGroupCoordinateRing K V) := by
  let basis := Module.Free.chooseBasis K (Module.Dual K V)
  exact Algebra.FiniteType.equiv
    (inferInstance : Algebra.FiniteType K
      (MvPolynomial (Module.Free.ChooseBasisIndex K (Module.Dual K V)) K))
    (SymmetricAlgebra.equivMvPolynomial basis).symm

/-- The affine scheme represented by the dual symmetric algebra, over `Spec K`. -/
abbrev vectorGroupUnderlyingScheme : Over (Spec (.of K)) :=
  (Spec (.of (vectorGroupCoordinateRing K V))).asOver (Spec (.of K))

instance vectorGroupUnderlyingScheme_locallyOfFiniteType :
    LocallyOfFiniteType (vectorGroupUnderlyingScheme K V).hom := by
  let _ : Algebra.FiniteType K (vectorGroupCoordinateRing K V) :=
    vectorGroupCoordinateRing_finiteType K V
  change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
    (algebraMap K (vectorGroupCoordinateRing K V))))
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  simpa [RingHom.finiteType_algebraMap]

instance vectorGroupUnderlyingScheme_quasiCompact :
    QuasiCompact (vectorGroupUnderlyingScheme K V).hom := by
  change QuasiCompact (Spec.map (CommRingCat.ofHom
    (algebraMap K (vectorGroupCoordinateRing K V))))
  infer_instance

/-- The affine vector group scheme; its Hopf structure comes from the primitive
generators of the symmetric algebra. -/
abbrev vectorGroupScheme : Grp (Over (Spec (.of K))) :=
  ⟨vectorGroupUnderlyingScheme K V⟩

/-- The additive tensor-group functor, with `Multiplicative` only tagging the
additive operation as the group operation of `GrpCat`. -/
@[expose] def vectorGroupFunctor : CommAlgCat K ⥤ GrpCat where
  obj R := GrpCat.of (Multiplicative (V ⊗[K] R))
  map f := GrpCat.ofHom (AddMonoidHom.toMultiplicative
    (TensorProduct.map (LinearMap.id : V →ₗ[K] V) f.hom.toLinearMap).toAddMonoidHom)
  map_id R := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    change TensorProduct.map (LinearMap.id : V →ₗ[K] V)
      (𝟙 R : R ⟶ R).hom.toLinearMap x.toAdd = x.toAdd
    change TensorProduct.map (LinearMap.id : V →ₗ[K] V)
      (LinearMap.id : R →ₗ[K] R) x.toAdd = x.toAdd
    exact congrArg (fun h : (V ⊗[K] R) →ₗ[K] (V ⊗[K] R) ↦ h x.toAdd)
      (TensorProduct.map_id (M := V) (N := R))
  map_comp f g := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    change TensorProduct.map (LinearMap.id : V →ₗ[K] V)
      (f ≫ g).hom.toLinearMap x.toAdd =
        TensorProduct.map (LinearMap.id : V →ₗ[K] V) g.hom.toLinearMap
          (TensorProduct.map (LinearMap.id : V →ₗ[K] V) f.hom.toLinearMap x.toAdd)
    simpa only [CommAlgCat.hom_comp, AlgHom.comp_toLinearMap, LinearMap.id_comp] using
      (TensorProduct.map_map (LinearMap.id : V →ₗ[K] V) g.hom.toLinearMap
        (LinearMap.id : V →ₗ[K] V) f.hom.toLinearMap x.toAdd).symm

/-- Group-valued affine points of the vector group scheme. -/
abbrev vectorGroupPointsFunctor : CommAlgCat K ⥤ GrpCat :=
  (algSpec (.of K)).rightOp ⋙ yonedaGrp.obj (vectorGroupScheme K V)

variable (R : Type u) [CommRing R] [Algebra K R]

/-- Tensor-valued points are the convolution group of algebra maps out of the
dual symmetric algebra. -/
@[expose] def vectorGroupMulEquivAlgHom :
    Multiplicative (V ⊗[K] R) ≃*
      WithConv (vectorGroupCoordinateRing K V →ₐ[K] R) :=
  (vectorGroupTensorDualEquiv K V R).toAddEquiv.toMultiplicative.trans
    (SymmetricAlgebra.linearMapMulEquivAlgHom K (Module.Dual K V) R)

@[simp]
theorem vectorGroupMulEquivAlgHom_ι (x : V ⊗[K] R)
    (φ : Module.Dual K V) :
    (vectorGroupMulEquivAlgHom K V R (.ofAdd x)).ofConv
      (SymmetricAlgebra.ι K _ φ) = vectorGroupTensorDualEquiv K V R x φ := by
  simp [vectorGroupMulEquivAlgHom]

theorem vectorGroupMulEquivAlgHom_tmul (v : V) (r : R)
    (φ : Module.Dual K V) :
    (vectorGroupMulEquivAlgHom K V R (.ofAdd (v ⊗ₜ[K] r))).ofConv
      (SymmetricAlgebra.ι K _ φ) = (φ v) • r := by
  simp

/-- Pullback of coordinates agrees with the covariant tensor map. -/
theorem vectorGroupMulEquivAlgHom_linearMap
    (W : Type u) [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (f : V →ₗ[K] W) (x : V ⊗[K] R) :
    (vectorGroupMulEquivAlgHom K W R (.ofAdd
      (TensorProduct.map f (LinearMap.id : R →ₗ[K] R) x))).ofConv =
      (vectorGroupMulEquivAlgHom K V R (.ofAdd x)).ofConv.comp
        (vectorGroupCoordinateMap K V W f) := by
  apply SymmetricAlgebra.algHom_ext
  ext φ
  change (vectorGroupMulEquivAlgHom K W R (.ofAdd
      (TensorProduct.map f (LinearMap.id : R →ₗ[K] R) x))).ofConv
        (SymmetricAlgebra.ι K _ φ) =
      ((vectorGroupMulEquivAlgHom K V R (.ofAdd x)).ofConv.comp
        (vectorGroupCoordinateMap K V W f)) (SymmetricAlgebra.ι K _ φ)
  rw [AlgHom.comp_apply, vectorGroupCoordinateMap_ι,
    vectorGroupMulEquivAlgHom_ι, vectorGroupMulEquivAlgHom_ι]
  exact vectorGroupTensorDualEquiv_linearMap K V W f R x φ

/-- The tensor/convolution equivalence is natural in the test algebra. -/
theorem vectorGroupMulEquivAlgHom_naturality
    {S : Type u} [CommRing S] [Algebra K S]
    (f : R →ₐ[K] S) (x : V ⊗[K] R) :
    (vectorGroupMulEquivAlgHom K V S (.ofAdd
      (TensorProduct.map (LinearMap.id : V →ₗ[K] V) f.toLinearMap x))).ofConv =
      f.comp (vectorGroupMulEquivAlgHom K V R (.ofAdd x)).ofConv := by
  apply SymmetricAlgebra.algHom_ext
  ext φ
  change (vectorGroupMulEquivAlgHom K V S (.ofAdd
      (TensorProduct.map (LinearMap.id : V →ₗ[K] V) f.toLinearMap x))).ofConv
        (SymmetricAlgebra.ι K _ φ) =
      (f.comp (vectorGroupMulEquivAlgHom K V R (.ofAdd x)).ofConv)
        (SymmetricAlgebra.ι K _ φ)
  rw [AlgHom.comp_apply, vectorGroupMulEquivAlgHom_ι,
    vectorGroupMulEquivAlgHom_ι]
  exact vectorGroupTensorDualEquiv_naturality K V R S f x φ

/-- Points of the affine scheme as morphisms over `Spec K`. -/
@[expose] def vectorGroupMulEquivPoints :
    Multiplicative (V ⊗[K] R) ≃*
      ((Spec (.of R)).asOver (Spec (.of K)) ⟶ (vectorGroupScheme K V).X) :=
  (vectorGroupMulEquivAlgHom K V R).trans
    (Spec.mapMulEquiv (R := K) (S := vectorGroupCoordinateRing K V) (T := R))

@[simp]
theorem vectorGroupMulEquivPoints_apply_left (x : V ⊗[K] R) :
    (vectorGroupMulEquivPoints K V R (.ofAdd x)).left =
      Spec.map (CommRingCat.ofHom
        (vectorGroupMulEquivAlgHom K V R (.ofAdd x)).ofConv.toRingHom) :=
  rfl

/-- The vector group scheme represents the group-valued tensor functor on
commutative test algebras, as in Milne, *Algebraic Groups* (2017), item 2.6.
The statement includes zero test algebras and naturality for every algebra map. -/
@[expose] def vectorGroupPointsIso :
    vectorGroupFunctor K V ≅ vectorGroupPointsFunctor K V :=
  NatIso.ofComponents
    (fun R ↦ (vectorGroupMulEquivPoints K V R).toGrpIso)
    (fun {R S} f ↦ by
      ext x
      apply Over.OverMorphism.ext
      change
        (vectorGroupMulEquivPoints K V S (.ofAdd
          (TensorProduct.map (LinearMap.id : V →ₗ[K] V) f.hom.toLinearMap x.toAdd))).left =
            ((algSpec (.of K)).map f.op).left ≫
              (vectorGroupMulEquivPoints K V R x).left
      rw [vectorGroupMulEquivPoints_apply_left]
      change
        Spec.map (CommRingCat.ofHom
          (vectorGroupMulEquivAlgHom K V S (.ofAdd
            (TensorProduct.map (LinearMap.id : V →ₗ[K] V)
              f.hom.toLinearMap x.toAdd))).ofConv.toRingHom) =
          Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫
            Spec.map (CommRingCat.ofHom
              (vectorGroupMulEquivAlgHom K V R x).ofConv.toRingHom)
      rw [← Spec.map_comp]
      congr 1
      exact congrArg (fun h : vectorGroupCoordinateRing K V →ₐ[K] S ↦
          CommRingCat.ofHom h.toRingHom)
        (vectorGroupMulEquivAlgHom_naturality K V R f.hom x.toAdd))

end AlgebraicGeometry
