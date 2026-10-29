/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.RepresentationReconstruction
public import AlgebraicGroups.Algebra.Coalgebra.Evaluation.Action

/-!
# Natural point representations and right comodules

A specified right coaction gives a natural point representation by the existing
`Coalgebra.RightComodule.pointAction`. Its component at a lifted point is the
corresponding general linear operator on the scalar extension. Naturality uses
coefficient evaluation and the general linear base-change formula.

`AlgebraicGeometry.PointRepresentation.rightComoduleEquiv` identifies these
natural transformations with specified right-comodule values. Recovery of a
coaction after evaluation is proved at the lifted generic point, cancelling the
coordinate lift and the tensor commutation. The other inverse follows from the
component evaluation formula. No finiteness or flatness is required.

The equivalence also gives canonical point actions over independently sized
coefficient algebras, by evaluating the recovered coaction. Such an action is not
a component of the original natural transformation unless the coefficient algebra
belongs to its category of test algebras.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 4, §c, for the correspondence
  between representations and comodules over the coordinate Hopf algebra.
* The right-comodule evaluation, convolution action and generic-point
  reconstruction formalizations in this library, using right coactions and left
  point actions.
* Mathlib's `GrpCat.uliftFunctor`, `MulEquiv.ulift`, tensor-product and general
  linear group formalizations, and the general linear base-change functor in
  this library.
* M. E. Sweedler, *Hopf Algebras*, W. A. Benjamin, 1969 (bibliographic credit).
-/

@[expose] public section

noncomputable section

open CategoryTheory WithConv
open scoped TensorProduct

universe u a v t r s

namespace Coalgebra.RightComodule

variable {K : Type u} [CommRing K] {A : Type a} [Semiring A] [HopfAlgebra K A]
  {V : Type v} [AddCommGroup V] [Module K V]
  {R : Type r} [CommRing R] [Algebra K R]
  {S : Type s} [CommRing S] [Algebra K S]

/-- The point action commutes with the general linear functor's coefficient
base change, for arbitrary modules and independently sized coefficient algebras. -/
theorem pointAction_baseChange (X : RightComodule K A V) (q : R →ₐ[K] S)
    (g : WithConv (A →ₐ[K] R)) :
    AlgebraicGeometry.generalLinearModuleBaseChange K V R S q (X.pointAction g) =
      X.pointAction (AlgHom.convolutionPostcomp q g) := by
  apply Units.ext
  apply TensorProduct.AlgebraTensorModule.ext
  intro z x
  rw [AlgebraicGeometry.generalLinearModuleBaseChange_tmul]
  simp only [pointAction_val, AlgHom.convolutionPostcomp_ofConv, AlgHom.comp_toLinearMap]
  rw [LinearMap.rTensor_def, X.evaluate_one_tmul, X.evaluate_tmul,
    TensorProduct.map_map, LinearMap.id_comp]

end Coalgebra.RightComodule

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (A : Type a) [CommRing A] [HopfAlgebra K A]
  (V : Type v) [AddCommGroup V] [Module K V]

namespace PointRepresentation

variable {K A V}

/-- The natural point representation of a specified right comodule. Components
use the existing point action, preceded by the stock group universe-lift bridge. -/
def ofRightComodule (X : Coalgebra.RightComodule K A V) :
    PointRepresentation.{u, a, v, t} K A V where
  app R := GrpCat.ofHom ((X.pointAction (A := R)).comp
    (MulEquiv.ulift : ULift.{v} ((pointGroupFunctor K A).obj R) ≃*
      (pointGroupFunctor K A).obj R).toMonoidHom)
  naturality {R S} q := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    rintro ⟨g⟩
    change X.pointAction (AlgHom.convolutionPostcomp q.hom g) =
      generalLinearModuleBaseChange K V R S q.hom (X.pointAction g)
    exact (X.pointAction_baseChange q.hom g).symm

/-- The component automorphism is the existing point-action automorphism. -/
@[simp] theorem ofRightComodule_operator (X : Coalgebra.RightComodule K A V)
    (R : CommAlgCat.{max a t, u} K) (g : A →ₐ[K] R) :
    (ofRightComodule X).operator R g = X.pointAction (toConv g) := rfl

/-- Forgetting a component gives evaluation of the original coaction. -/
theorem ofRightComodule_operator_val (X : Coalgebra.RightComodule K A V)
    (R : CommAlgCat.{max a t, u} K) (g : A →ₐ[K] R) :
    ((ofRightComodule X).operator R g).val = X.evaluate g.toLinearMap := rfl

/-- Characteristic one-tensor formula for the forward construction. -/
theorem ofRightComodule_operator_one_tmul (X : Coalgebra.RightComodule K A V)
    (R : CommAlgCat.{max a t, u} K) (g : A →ₐ[K] R) (x : V) :
    ((ofRightComodule X).operator R g).val (1 ⊗ₜ[K] x) =
      TensorProduct.map g.toLinearMap (LinearMap.id : V →ₗ[K] V)
        (TensorProduct.comm K V A (X.coaction x)) :=
  X.evaluate_one_tmul g.toLinearMap x

/-- Characteristic formula on all pure tensors for the forward construction. -/
theorem ofRightComodule_operator_tmul (X : Coalgebra.RightComodule K A V)
    (R : CommAlgCat.{max a t, u} K) (g : A →ₐ[K] R) (z : R) (x : V) :
    ((ofRightComodule X).operator R g).val (z ⊗ₜ[K] x) =
      z • TensorProduct.map g.toLinearMap (LinearMap.id : V →ₗ[K] V)
        (TensorProduct.comm K V A (X.coaction x)) := rfl

/-- At the lifted generic point the forward representation reads back the
original coaction, with the coordinate factor lifted and commuted to the left. -/
theorem genericLinearMap_ofRightComodule (X : Coalgebra.RightComodule K A V) (x : V) :
    (ofRightComodule.{u, a, v, t} X).genericLinearMap x =
      TensorProduct.map
        (ULift.algEquiv (R := K) : ULift.{t} A ≃ₐ[K] A).symm.toLinearMap
        (LinearMap.id : V →ₗ[K] V) (TensorProduct.comm K V A (X.coaction x)) :=
  X.evaluate_one_tmul _ x

/-- Recovering the coaction after the forward construction returns its original
linear-map data, not merely its two comodule laws. -/
@[simp] theorem recoveredCoaction_ofRightComodule (X : Coalgebra.RightComodule K A V) :
    (ofRightComodule.{u, a, v, t} X).recoveredCoaction = X.coaction := by
  let e : ULift.{t} A ≃ₐ[K] A := ULift.algEquiv
  have he : (TensorProduct.map e.toLinearMap (LinearMap.id : V →ₗ[K] V)).comp
      (TensorProduct.map e.symm.toLinearMap (LinearMap.id : V →ₗ[K] V)) =
        LinearMap.id := by
    apply TensorProduct.ext'
    intro y x
    simp
  apply LinearMap.ext
  intro x
  apply (TensorProduct.comm K V A).injective
  rw [comm_recoveredCoaction, genericLinearMap_ofRightComodule]
  exact LinearMap.congr_fun he (TensorProduct.comm K V A (X.coaction x))

/-- Reconstruction after evaluation returns the same specified right-comodule
value, by equality of its coaction data. -/
@[simp] theorem toRightComodule_ofRightComodule (X : Coalgebra.RightComodule K A V) :
    (ofRightComodule.{u, a, v, t} X).toRightComodule = X :=
  Coalgebra.RightComodule.ext (recoveredCoaction_ofRightComodule X)

/-- Evaluation of a reconstructed right comodule returns the original natural
transformation, by the component operator readback. -/
@[simp] theorem ofRightComodule_toRightComodule
    (η : PointRepresentation.{u, a, v, t} K A V) :
    ofRightComodule η.toRightComodule = η := by
  apply PointRepresentation.ext
  intro R g
  apply Units.ext
  rw [ofRightComodule_operator_val]
  exact (η.operator_val R g).symm

variable (K A V) in
/-- Natural representations of the point functor are equivalent to specified
right comodules on the same module. This extends the representation-comodule
correspondence of Milne, *Algebraic Groups*, Chapter 4, §c, to commutative Hopf
algebras over arbitrary commutative base rings. -/
def rightComoduleEquiv :
    PointRepresentation.{u, a, v, t} K A V ≃ Coalgebra.RightComodule K A V where
  toFun := toRightComodule
  invFun := ofRightComodule
  left_inv := ofRightComodule_toRightComodule
  right_inv := toRightComodule_ofRightComodule

/-- The forward map of the equivalence is generic-point reconstruction. -/
@[simp] theorem rightComoduleEquiv_apply (η : PointRepresentation.{u, a, v, t} K A V) :
    rightComoduleEquiv K A V η = η.toRightComodule := rfl

/-- The inverse map of the equivalence is the natural point action. -/
@[simp] theorem rightComoduleEquiv_symm_apply (X : Coalgebra.RightComodule K A V) :
    (rightComoduleEquiv.{u, a, v, t} K A V).symm X = ofRightComodule X := rfl

/-- The equivalence retains the recovered coaction as its coaction data. -/
theorem rightComoduleEquiv_coaction
    (η : PointRepresentation.{u, a, v, t} K A V) :
    (rightComoduleEquiv K A V η).coaction = η.recoveredCoaction := rfl

/-- Recovering the coaction of the inverse image returns the original coaction. -/
theorem rightComoduleEquiv_symm_recoveredCoaction
    (X : Coalgebra.RightComodule K A V) :
    ((rightComoduleEquiv.{u, a, v, t} K A V).symm X).recoveredCoaction = X.coaction :=
  recoveredCoaction_ofRightComodule X

/-- Components of a representation evaluate the comodule given by the equivalence. -/
theorem rightComoduleEquiv_operator_val
    (η : PointRepresentation.{u, a, v, t} K A V)
    (R : CommAlgCat.{max a t, u} K) (g : A →ₐ[K] R) :
    (η.operator R g).val = (rightComoduleEquiv K A V η).evaluate g.toLinearMap :=
  η.operator_val R g

/-- Components of the inverse image are the original comodule's point action. -/
theorem rightComoduleEquiv_symm_operator (X : Coalgebra.RightComodule K A V)
    (R : CommAlgCat.{max a t, u} K) (g : A →ₐ[K] R) :
    ((rightComoduleEquiv K A V).symm X).operator R g = X.pointAction (toConv g) := rfl

/-- The inverse image has the same evaluation at every independently sized
coefficient algebra, not only at objects of its category of test algebras. -/
theorem rightComoduleEquiv_symm_evaluate (X : Coalgebra.RightComodule K A V)
    {R : Type r} [CommRing R] [Algebra K R] (g : A →ₐ[K] R) :
    ((rightComoduleEquiv.{u, a, v, t} K A V).symm X).evaluate g =
      X.evaluate g.toLinearMap := by
  change (ofRightComodule.{u, a, v, t} X).toRightComodule.evaluate g.toLinearMap = _
  rw [toRightComodule_ofRightComodule]

/-- The canonical action at any coefficient algebra is the point action of the
same recovered right comodule. It does not require an out-of-category component. -/
def pointAction (η : PointRepresentation.{u, a, v, t} K A V)
    {R : Type r} [CommRing R] [Algebra K R] :
    WithConv (A →ₐ[K] R) →* LinearMap.GeneralLinearGroup R (R ⊗[K] V) :=
  (rightComoduleEquiv K A V η).pointAction

/-- The canonical action's endomorphism is evaluation of the recovered coaction. -/
@[simp] theorem pointAction_val (η : PointRepresentation.{u, a, v, t} K A V)
    {R : Type r} [CommRing R] [Algebra K R] (g : WithConv (A →ₐ[K] R)) :
    (η.pointAction g).val = η.evaluate g.ofConv := rfl

/-- The inverse canonical operator evaluates precomposition by the antipode. -/
theorem pointAction_inv_val (η : PointRepresentation.{u, a, v, t} K A V)
    {R : Type r} [CommRing R] [Algebra K R] (g : WithConv (A →ₐ[K] R)) :
    (η.pointAction g).inv = η.evaluate (AlgHom.convolutionInverse g).ofConv := rfl

/-- The underlying map of the inverse canonical action evaluates the source antipode. -/
@[simp] theorem pointAction_coe_inv (η : PointRepresentation.{u, a, v, t} K A V)
    {R : Type r} [CommRing R] [Algebra K R] (g : WithConv (A →ₐ[K] R)) :
    (↑(η.pointAction g)⁻¹ : Module.End R (R ⊗[K] V)) =
      η.evaluate (AlgHom.convolutionInverse g).ofConv := by
  simpa only [Units.inv_eq_val_inv] using η.pointAction_inv_val g

/-- The canonical action agrees with each available component as a group unit. -/
theorem pointAction_eq_operator (η : PointRepresentation.{u, a, v, t} K A V)
    (R : CommAlgCat.{max a t, u} K) (g : A →ₐ[K] R) :
    η.pointAction (toConv g) = η.operator R g := by
  apply Units.ext
  rw [pointAction_val]
  exact (η.operator_val_eq_evaluate R g).symm

/-- Starting with a right comodule, the canonical action of its representation
is the original point-action homomorphism, at every coefficient algebra. -/
@[simp] theorem pointAction_ofRightComodule (X : Coalgebra.RightComodule K A V)
    {R : Type r} [CommRing R] [Algebra K R] :
    (ofRightComodule.{u, a, v, t} X).pointAction (R := R) = X.pointAction := by
  change (ofRightComodule.{u, a, v, t} X).toRightComodule.pointAction = X.pointAction
  rw [toRightComodule_ofRightComodule]

/-- Canonical actions are natural under every independently sized coefficient
algebra map, using the existing general linear base-change homomorphism. -/
theorem pointAction_baseChange (η : PointRepresentation.{u, a, v, t} K A V)
    {R : Type r} [CommRing R] [Algebra K R]
    {S : Type s} [CommRing S] [Algebra K S]
    (q : R →ₐ[K] S) (g : WithConv (A →ₐ[K] R)) :
    generalLinearModuleBaseChange K V R S q (η.pointAction g) =
      η.pointAction (AlgHom.convolutionPostcomp q g) :=
  η.toRightComodule.pointAction_baseChange q g

/-- The every-algebra-map naturality square evaluated at an arbitrary tensor.
The tensor comparison is only `K`-linear. -/
theorem pointAction_naturality_apply (η : PointRepresentation.{u, a, v, t} K A V)
    {R : Type r} [CommRing R] [Algebra K R]
    {S : Type s} [CommRing S] [Algebra K S]
    (q : R →ₐ[K] S) (g : A →ₐ[K] R) (z : R ⊗[K] V) :
    TensorProduct.map q.toLinearMap (LinearMap.id : V →ₗ[K] V)
        ((η.pointAction (toConv g)).val z) =
      (η.pointAction (toConv (q.comp g))).val
        (TensorProduct.map q.toLinearMap (LinearMap.id : V →ₗ[K] V) z) :=
  LinearMap.congr_fun (η.evaluate_naturality q g) z

/-- On a one-tensor the canonical action evaluates the same recovered coaction. -/
theorem pointAction_one_tmul (η : PointRepresentation.{u, a, v, t} K A V)
    {R : Type r} [CommRing R] [Algebra K R] (g : A →ₐ[K] R) (x : V) :
    (η.pointAction (toConv g)).val (1 ⊗ₜ[K] x) =
      TensorProduct.map g.toLinearMap (LinearMap.id : V →ₗ[K] V)
        (TensorProduct.comm K V A ((rightComoduleEquiv K A V η).coaction x)) :=
  η.evaluate_one_tmul g x

/-- The representation of the existing scalar comodule is trivial at every
component, for an arbitrary module over the base ring. -/
theorem ofRightComodule_scalar_operator
    (R : CommAlgCat.{max u t, u} K) (g : K →ₐ[K] R) :
    (ofRightComodule (Coalgebra.RightComodule.scalar K V)).operator R g = 1 := by
  apply Units.ext
  rw [ofRightComodule_operator_val, Coalgebra.RightComodule.scalar_evaluate]
  simp [Module.End.one_eq_id]

end PointRepresentation

end AlgebraicGeometry
