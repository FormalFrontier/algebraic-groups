/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.Multiplicative
public import AlgebraicGroups.GroupScheme.UnitriangularGeometry
public import AlgebraicGroups.GroupScheme.DiagonalProduct
public import AlgebraicGroups.GroupScheme.UpperTriangularSplitKernel
public import AlgebraicGroups.GroupObject.SplitKernelProduct
public import AlgebraicGroups.Scheme.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
public import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
public import Mathlib.RingTheory.Smooth.StandardSmooth
public import Mathlib.Algebra.MvPolynomial.Equiv

/-! # Geometry of finite diagonal and upper-triangular group schemes

The native multiplicative, finite diagonal, and finite upper-triangular group schemes
are smooth with geometrically integral fibers over every commutative base.
-/

@[expose] public section

set_option warningAsError true
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory
open scoped TensorProduct Polynomial CategoryTheory.MonoidalCategory

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K]

private instance multiplicativeGroupCoordinateRing_standardSmooth :
    Algebra.IsStandardSmooth K (multiplicativeGroupCoordinateRing K) := by
  letI : Algebra.IsStandardSmooth K K[X] :=
    Algebra.IsStandardSmooth.of_algEquiv (MvPolynomial.uniqueAlgEquiv K PUnit.{1})
  letI : Algebra.IsStandardSmooth K[X] (LaurentPolynomial K) :=
    Algebra.IsStandardSmooth.localization_away (Polynomial.X : K[X])
  letI : IsScalarTower K K[X] (LaurentPolynomial K) :=
    .of_algebraMap_eq' (by ext; simp [LaurentPolynomial.algebraMap_apply,
      LaurentPolynomial.algebraMap_eq_toLaurent, Polynomial.toLaurent_C])
  exact Algebra.IsStandardSmooth.trans K K[X] (LaurentPolynomial K)

/-- The genuine Laurent-polynomial structure map is smooth, even over the zero ring. -/
instance multiplicativeGroupUnderlyingScheme_smooth :
    Smooth (multiplicativeGroupUnderlyingScheme K).hom := by
  change Smooth (Spec.map (CommRingCat.ofHom
    (algebraMap K (multiplicativeGroupCoordinateRing K))))
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  change (algebraMap K (multiplicativeGroupCoordinateRing K)).Smooth
  exact RingHom.smooth_algebraMap.mpr inferInstance

private theorem multiplicativeGroupTensor_isDomain
    (F : Type u) [Field F] [Algebra K F] :
    IsDomain (F ⊗[K] multiplicativeGroupCoordinateRing K) := by
  change IsDomain (F ⊗[K] AddMonoidAlgebra K ℤ)
  exact (AddMonoidAlgebra.scalarTensorEquiv (M := ℤ) K F).injective.isDomain
    (AddMonoidAlgebra.scalarTensorEquiv (M := ℤ) K F).toRingHom

/-- Every geometric fiber of the native multiplicative group is integral. -/
instance multiplicativeGroupUnderlyingScheme_geometricallyIntegral :
    GeometricallyIntegral (multiplicativeGroupUnderlyingScheme K).hom := by
  letI : ObjectProperty.IsClosedUnderIsomorphisms (C := Scheme) IsIntegral :=
    ⟨fun iso integral ↦ by letI := integral; exact IsIntegral.of_isIso iso.hom⟩
  refine ⟨(geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms
    (P := IsIntegral)).2 ?_⟩
  intro F _ _
  change IsIntegral (pullback
    (Spec.map (CommRingCat.ofHom (algebraMap K (multiplicativeGroupCoordinateRing K))))
    (Spec.map (CommRingCat.ofHom (algebraMap K F))))
  haveI : IsDomain (F ⊗[K] multiplicativeGroupCoordinateRing K) :=
    multiplicativeGroupTensor_isDomain K F
  haveI : IsDomain (multiplicativeGroupCoordinateRing K ⊗[K] F) :=
    (Algebra.TensorProduct.comm K (multiplicativeGroupCoordinateRing K) F).injective.isDomain
      (Algebra.TensorProduct.comm K (multiplicativeGroupCoordinateRing K) F).toRingHom
  exact IsIntegral.of_isIso
    (pullbackSpecIso K (multiplicativeGroupCoordinateRing K) F).inv

private theorem product_smooth {S : Scheme.{u}} (X Y : Over S)
    [Smooth X.hom] [Smooth Y.hom] : Smooth (X ⊗ Y).hom := by
  rw [Over.tensorObj_hom]
  infer_instance

private theorem product_geometricallyIntegral {S : Scheme.{u}} (X Y : Over S)
    [Smooth X.hom] [Smooth Y.hom]
    [GeometricallyIntegral X.hom] [GeometricallyIntegral Y.hom] :
    GeometricallyIntegral (X ⊗ Y).hom := by
  haveI : Smooth (X ⊗ Y).hom := product_smooth X Y
  rw [Over.tensorObj_hom]
  haveI : UniversallyOpen X.hom := inferInstance
  haveI : UniversallyOpen Y.hom := inferInstance
  haveI : GeometricallyIrreducible (pullback.fst X.hom Y.hom ≫ X.hom) :=
    GeometricallyIrreducible.comp _ _
  exact GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible _

private theorem smooth_of_iso {S : Scheme.{u}} {X Y : Over S}
    (iso : X ≅ Y) [Smooth Y.hom] : Smooth X.hom := by
  haveI : IsIso iso.hom := inferInstance
  haveI : IsIso iso.hom.left := by
    change IsIso ((Over.forget S).map iso.hom)
    infer_instance
  letI : MorphismProperty.RespectsIso (@Smooth) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have h : Smooth (iso.hom.left ≫ Y.hom) :=
    (MorphismProperty.cancel_left_of_respectsIso
      (P := @Smooth) iso.hom.left _).mpr (by infer_instance)
  exact iso.hom.w ▸ h

private theorem geometricallyIntegral_of_iso {S : Scheme.{u}} {X Y : Over S}
    (iso : X ≅ Y) [GeometricallyIntegral Y.hom] : GeometricallyIntegral X.hom := by
  haveI : IsIso iso.hom := inferInstance
  haveI : IsIso iso.hom.left := by
    change IsIso ((Over.forget S).map iso.hom)
    infer_instance
  letI : MorphismProperty.RespectsIso (@GeometricallyIntegral) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have h : GeometricallyIntegral (iso.hom.left ≫ Y.hom) :=
    (MorphismProperty.cancel_left_of_respectsIso
      (P := @GeometricallyIntegral) iso.hom.left _).mpr (by infer_instance)
  exact iso.hom.w ▸ h

private def optionProductFan {S : Scheme.{u}} {index : Type u} [Fintype index]
    (family : Option index → Over S) : Fan family :=
  Fan.mk (family none ⊗ ∏ᶜ (fun i : index => family (some i)))
    (fun | none => fst _ _
         | some i => snd _ _ ≫ Pi.π _ i)

private def optionProductFan_isLimit {S : Scheme.{u}} {index : Type u} [Fintype index]
    (family : Option index → Over S) : IsLimit (optionProductFan family) := by
  classical
  refine Fan.IsLimit.mk _ (fun cone =>
    lift (cone.proj none) (Pi.lift fun i => cone.proj (some i))) ?_ ?_
  · intro cone i
    cases i with
    | none => simp [optionProductFan]
    | some i => simp [optionProductFan]
  · intro cone morphism factor
    apply hom_ext
    · simpa [optionProductFan] using factor none
    · apply Pi.hom_ext
      intro i
      have hi := factor (some i)
      change morphism ≫ (snd _ _ ≫ Pi.π _ i) = cone.proj (some i) at hi
      simpa only [lift_snd, Pi.lift_π] using
        (Category.assoc morphism (snd _ _) (Pi.π _ i)).trans hi

private def optionProductIso {S : Scheme.{u}} {index : Type u} [Fintype index]
    (family : Option index → Over S) :
    (∏ᶜ family) ≅ family none ⊗ ∏ᶜ (fun i : index => family (some i)) :=
  (productIsProduct family).conePointUniqueUpToIso (optionProductFan_isLimit family)

private theorem identity_geometricallyIntegral :
    GeometricallyIntegral (𝟙 (Spec (.of K))) := by
  letI : ObjectProperty.IsClosedUnderIsomorphisms (C := Scheme) IsIntegral :=
    ⟨fun iso integral ↦ by letI := integral; exact IsIntegral.of_isIso iso.hom⟩
  refine ⟨(geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms
    (P := IsIntegral)).2 ?_⟩
  intro F _ _
  haveI : IsIso (pullback.snd (𝟙 (Spec (.of K)))
      (Spec.map (CommRingCat.ofHom (algebraMap K F)))) := inferInstance
  exact IsIntegral.of_isIso
    (inv (pullback.snd (𝟙 (Spec (.of K)))
      (Spec.map (CommRingCat.ofHom (algebraMap K F)))))

private theorem finiteMultiplicativeProductGeometry (index : Type u) [Fintype index] :
    Smooth (∏ᶜ fun _ : index => multiplicativeGroupUnderlyingScheme K).hom ∧
      GeometricallyIntegral
        (∏ᶜ fun _ : index => multiplicativeGroupUnderlyingScheme K).hom := by
  classical
  refine Fintype.induction_empty_option
    (P := fun (index : Type u) [Fintype index] =>
      Smooth (∏ᶜ fun _ : index => multiplicativeGroupUnderlyingScheme K).hom ∧
      GeometricallyIntegral
        (∏ᶜ fun _ : index => multiplicativeGroupUnderlyingScheme K).hom)
    ?_ ?_ ?_ index
  · intro source target _ equivalence ih
    letI : Fintype source := Fintype.ofEquiv target equivalence.symm
    let iso : (∏ᶜ fun _ : source => multiplicativeGroupUnderlyingScheme K) ≅
        (∏ᶜ fun _ : target => multiplicativeGroupUnderlyingScheme K) :=
      Pi.reindex equivalence (fun _ : target => multiplicativeGroupUnderlyingScheme K)
    letI : Smooth (∏ᶜ fun _ : source => multiplicativeGroupUnderlyingScheme K).hom := ih.1
    letI : GeometricallyIntegral
        (∏ᶜ fun _ : source => multiplicativeGroupUnderlyingScheme K).hom := ih.2
    exact ⟨smooth_of_iso iso.symm, geometricallyIntegral_of_iso iso.symm⟩
  ·
    let terminal : IsTerminal (∏ᶜ fun _ : PEmpty.{u+1} =>
        multiplicativeGroupUnderlyingScheme K) :=
      (isLimitEquivIsTerminalOfIsEmpty (Over (Spec (.of K)))
        (Fan.mk (∏ᶜ fun _ : PEmpty.{u+1} => multiplicativeGroupUnderlyingScheme K)
          (Pi.π fun _ : PEmpty.{u+1} => multiplicativeGroupUnderlyingScheme K)))
        (productIsProduct fun _ : PEmpty.{u+1} => multiplicativeGroupUnderlyingScheme K)
    let baseTerminal : IsTerminal (Over.mk (𝟙 (Spec (.of K)))) :=
      IsTerminal.ofUniqueHom (fun Y => Over.homMk Y.hom)
        (fun Y morphism => Over.OverMorphism.ext (by simpa using morphism.w))
    let iso := terminal.uniqueUpToIso baseTerminal
    haveI : Smooth (Over.mk (𝟙 (Spec (.of K)))).hom := by
      change Smooth (𝟙 (Spec (.of K)))
      infer_instance
    haveI : GeometricallyIntegral (Over.mk (𝟙 (Spec (.of K)))).hom :=
      identity_geometricallyIntegral K
    exact ⟨smooth_of_iso iso, geometricallyIntegral_of_iso iso⟩
  · intro smaller _ ih
    let iso := optionProductIso
      (fun _ : Option smaller => multiplicativeGroupUnderlyingScheme K)
    haveI : Smooth (∏ᶜ fun _ : smaller => multiplicativeGroupUnderlyingScheme K).hom := ih.1
    haveI : GeometricallyIntegral
        (∏ᶜ fun _ : smaller => multiplicativeGroupUnderlyingScheme K).hom := ih.2
    haveI : Smooth (multiplicativeGroupUnderlyingScheme K ⊗
        (∏ᶜ fun _ : smaller => multiplicativeGroupUnderlyingScheme K)).hom :=
      product_smooth _ _
    haveI : GeometricallyIntegral (multiplicativeGroupUnderlyingScheme K ⊗
        (∏ᶜ fun _ : smaller => multiplicativeGroupUnderlyingScheme K)).hom :=
      product_geometricallyIntegral _ _
    exact ⟨smooth_of_iso iso, geometricallyIntegral_of_iso iso⟩

private def diagonalUnderlyingProductIso (index : Type u) [Fintype index]
    [DecidableEq index] :
    diagonalGroupUnderlyingScheme K index ≅
      (∏ᶜ fun _ : index => multiplicativeGroupUnderlyingScheme K) :=
  (diagonalGroupProductFan_forget_isLimit K index).conePointUniqueUpToIso
    (productIsProduct fun _ : index => multiplicativeGroupUnderlyingScheme K)

/-- The native finite diagonal structure morphism is smooth over every commutative base. -/
instance diagonalGroupUnderlyingScheme_smooth (index : Type u) [Fintype index]
    [DecidableEq index] : Smooth (diagonalGroupUnderlyingScheme K index).hom := by
  haveI : Smooth (∏ᶜ fun _ : index => multiplicativeGroupUnderlyingScheme K).hom :=
    (finiteMultiplicativeProductGeometry K index).1
  exact smooth_of_iso (diagonalUnderlyingProductIso K index)

/-- Every geometric fiber of the native finite diagonal group is integral. -/
instance diagonalGroupUnderlyingScheme_geometricallyIntegral (index : Type u)
    [Fintype index] [DecidableEq index] :
    GeometricallyIntegral (diagonalGroupUnderlyingScheme K index).hom := by
  haveI : GeometricallyIntegral
      (∏ᶜ fun _ : index => multiplicativeGroupUnderlyingScheme K).hom :=
    (finiteMultiplicativeProductGeometry K index).2
  exact geometricallyIntegral_of_iso (diagonalUnderlyingProductIso K index)

private def upperTriangularSplitIso
    (n : Type u) [Fintype n] [LinearOrder n] :
    unitriangularGroupUnderlyingScheme K n ⊗ diagonalGroupUnderlyingScheme K n ≅
      upperTriangularGroupUnderlyingScheme K n := by
  classical
  apply CategoryTheory.splitKernelProductIso
    (unitriangularToUpperTriangular K n).hom.hom
    (upperTriangularDiagonalProjection K n).hom.hom
    (upperTriangularDiagonalSection K n).hom.hom
    (upperTriangularDiagonalSquare_isPullback_over K n)
  exact congrArg (fun morphism => morphism.hom.hom)
    (upperTriangularDiagonal_section K n)

/-- The actual structure morphism of the finite upper-triangular group is smooth. -/
instance upperTriangularGroupUnderlyingScheme_smooth
    (n : Type u) [Fintype n] [LinearOrder n] :
    Smooth (upperTriangularGroupUnderlyingScheme K n).hom := by
  haveI : Smooth (unitriangularGroupUnderlyingScheme K n ⊗
      diagonalGroupUnderlyingScheme K n).hom := product_smooth _ _
  exact smooth_of_iso (upperTriangularSplitIso K n).symm

/-- Every geometric fiber of the native finite upper-triangular group is integral. -/
instance upperTriangularGroupUnderlyingScheme_geometricallyIntegral
    (n : Type u) [Fintype n] [LinearOrder n] :
    GeometricallyIntegral (upperTriangularGroupUnderlyingScheme K n).hom := by
  haveI : GeometricallyIntegral (unitriangularGroupUnderlyingScheme K n ⊗
      diagonalGroupUnderlyingScheme K n).hom := product_geometricallyIntegral _ _
  exact geometricallyIntegral_of_iso (upperTriangularSplitIso K n).symm

private theorem integral_of_relative [IsDomain K] (X : Over (Spec (.of K)))
    [Smooth X.hom] [GeometricallyIntegral X.hom] : IsIntegral X.left := by
  haveI : IsReduced X.left := Smooth.isReduced_of_isDomain X.hom
  haveI : IrreducibleSpace X.left :=
    GeometricallyIrreducible.irreducibleSpace (f := X.hom) X.hom.isOpenMap
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- The native multiplicative group is integral over an integral domain. -/
instance multiplicativeGroupUnderlyingScheme_isIntegral [IsDomain K] :
    IsIntegral (multiplicativeGroupUnderlyingScheme K).left :=
  integral_of_relative K _

/-- The finite diagonal group is integral over an integral domain. -/
instance diagonalGroupUnderlyingScheme_isIntegral [IsDomain K]
    (index : Type u) [Fintype index] [DecidableEq index] :
    IsIntegral (diagonalGroupUnderlyingScheme K index).left :=
  integral_of_relative K _

/-- The finite upper-triangular group is integral over an integral domain. -/
instance upperTriangularGroupUnderlyingScheme_isIntegral [IsDomain K]
    (index : Type u) [Fintype index] [LinearOrder index] :
    IsIntegral (upperTriangularGroupUnderlyingScheme K index).left :=
  integral_of_relative K _

end AlgebraicGeometry
