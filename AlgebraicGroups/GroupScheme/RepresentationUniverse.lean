/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.RepresentationEquivalence
public import AlgebraicGroups.GroupScheme.RepresentationIntertwiner

/-!
# Changing the universe of test algebras

Natural point representations in different categories of test algebras describe
the same specified right coaction. `PointRepresentation.changeTestLevel` gives
the canonical change of presentation. `PointRepresentation.restrictTestLevel`
is constructed separately: it uses the component at the stock algebra universe
lift, lifts the point, and applies the existing general linear base-change
homomorphism along the coefficient equivalence down. Its agreement with the
canonical change is a theorem, not its definition.

Coefficient tensor comparisons are `K`-linear equivalences. With respect to the
coefficient rings they obey the displayed semilinear scalar rule; they are not
asserted to be linear over two different coefficient rings. Double lifts are
compared with a single lift by an algebra equivalence and its tensor map.
Identity, composition, inverse and common-maximum equations compare the
representation values themselves, retaining the recovered coaction and the
underlying linear maps of intertwiners. No finiteness of the module is needed.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 4, §c, for the
  representation–comodule correspondence in the coordinate Hopf algebra setting.
* Mathlib's `CommAlgCat.uliftFunctor`, `GrpCat.uliftFunctor`, `ULift.algEquiv`,
  `MulEquiv.ulift` and tensor-product congruences.
* The general linear base-change, right-comodule evaluation, reconstruction,
  equivalence and point-intertwiner APIs in this library.
* M. E. Sweedler, *Hopf Algebras*, W. A. Benjamin, 1969 (bibliographic credit).
-/

@[expose] public section

noncomputable section

open CategoryTheory WithConv
open scoped TensorProduct

universe u a v w x t s r p q

namespace AlgebraicGeometry

section Coefficients

variable {K : Type u} [CommRing K] {V : Type v} [AddCommGroup V] [Module K V]
variable {R : Type r} [CommRing R] [Algebra K R]
variable {S : Type s} [CommRing S] [Algebra K S]
variable {T : Type t} [CommRing T] [Algebra K T]

/-- Coefficient transport on tensors, using the stock tensor congruence.
This equivalence is linear over the base ring. -/
def coefficientTensorEquiv (e : R ≃ₐ[K] S) : R ⊗[K] V ≃ₗ[K] S ⊗[K] V :=
  TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl K V)

/-- The tensor equivalence has the stock coefficient tensor map as its data. -/
@[simp] theorem coefficientTensorEquiv_toLinearMap (e : R ≃ₐ[K] S) :
    (coefficientTensorEquiv (V := V) e).toLinearMap =
      TensorProduct.map e.toLinearMap (LinearMap.id : V →ₗ[K] V) := rfl

@[simp] theorem coefficientTensorEquiv_tmul (e : R ≃ₐ[K] S) (z : R) (v : V) :
    coefficientTensorEquiv (V := V) e (z ⊗ₜ[K] v) = e z ⊗ₜ[K] v := rfl

@[simp] theorem coefficientTensorEquiv_symm_tmul (e : R ≃ₐ[K] S) (z : S) (v : V) :
    (coefficientTensorEquiv (V := V) e).symm (z ⊗ₜ[K] v) =
      e.symm z ⊗ₜ[K] v := rfl

/-- The inverse tensor transport uses the inverse coefficient equivalence. -/
@[simp] theorem coefficientTensorEquiv_symm (e : R ≃ₐ[K] S) :
    (coefficientTensorEquiv (V := V) e).symm = coefficientTensorEquiv e.symm := rfl

/-- On one-tensors the coefficient equivalence fixes the unit coefficient. -/
theorem coefficientTensorEquiv_one_tmul (e : R ≃ₐ[K] S) (v : V) :
    coefficientTensorEquiv e (1 ⊗ₜ[K] v) = 1 ⊗ₜ[K] v := by
  rw [coefficientTensorEquiv_tmul, map_one]

theorem coefficientTensorEquiv_symm_one_tmul (e : R ≃ₐ[K] S) (v : V) :
    (coefficientTensorEquiv e).symm (1 ⊗ₜ[K] v) = 1 ⊗ₜ[K] v := by
  rw [coefficientTensorEquiv_symm, coefficientTensorEquiv_one_tmul]

/-- Tensor change of coefficients is semilinear along the coefficient map. -/
theorem tensorCoefficientMap_smul (f : R →ₐ[K] S) (c : R) (z : R ⊗[K] V) :
    TensorProduct.map f.toLinearMap (LinearMap.id : V →ₗ[K] V) (c • z) =
      f c • TensorProduct.map f.toLinearMap (LinearMap.id : V →ₗ[K] V) z := by
  induction z using TensorProduct.inductionOn with
  | tmul z v =>
    simp only [TensorProduct.smul_tmul', smul_eq_mul, TensorProduct.map_tmul,
      AlgHom.toLinearMap_apply, LinearMap.id_apply, map_mul]
  | add z z' hz hz' =>
    simp only [smul_add, map_add, hz, hz']

/-- The coefficient scalar rule is semilinear along `e`, rather than
linearity over an unidentified coefficient ring. -/
theorem coefficientTensorEquiv_smul (e : R ≃ₐ[K] S) (c : R) (z : R ⊗[K] V) :
    coefficientTensorEquiv e (c • z) = e c • coefficientTensorEquiv e z :=
  tensorCoefficientMap_smul e.toAlgHom c z

/-- The scalar rule for the inverse coefficient transport. -/
theorem coefficientTensorEquiv_symm_smul (e : R ≃ₐ[K] S) (c : S)
    (z : S ⊗[K] V) :
    (coefficientTensorEquiv e).symm (c • z) =
      e.symm c • (coefficientTensorEquiv e).symm z :=
  coefficientTensorEquiv_smul e.symm c z

/-- Tensor transport respects successive coefficient equivalences. -/
theorem coefficientTensorEquiv_trans (e : R ≃ₐ[K] S) (f : S ≃ₐ[K] T) :
    coefficientTensorEquiv (V := V) (e.trans f) =
      (coefficientTensorEquiv e).trans (coefficientTensorEquiv f) := by
  apply LinearEquiv.toLinearMap_injective
  apply TensorProduct.ext'
  intro z v
  rfl

/-- The identity coefficient equivalence induces the identity tensor map. -/
@[simp] theorem coefficientTensorEquiv_refl :
    coefficientTensorEquiv (V := V) (AlgEquiv.refl : R ≃ₐ[K] R) =
      LinearEquiv.refl K (R ⊗[K] V) := by
  apply LinearEquiv.toLinearMap_injective
  apply TensorProduct.ext'
  intro z v
  rfl

/-- The existing general linear coefficient map intertwines an operator with
its base change on arbitrary tensors, without injectivity of the algebra map. -/
theorem generalLinearModuleBaseChange_naturality_apply (f : R →ₐ[K] S)
    (F : LinearMap.GeneralLinearGroup R (R ⊗[K] V)) (z : R ⊗[K] V) :
    TensorProduct.map f.toLinearMap (LinearMap.id : V →ₗ[K] V) (F.val z) =
      (generalLinearModuleBaseChange K V R S f F).val
        (TensorProduct.map f.toLinearMap (LinearMap.id : V →ₗ[K] V) z) := by
  induction z using TensorProduct.inductionOn with
  | tmul c v =>
    calc
      _ = TensorProduct.map f.toLinearMap (LinearMap.id : V →ₗ[K] V)
          (F.val (c • (1 ⊗ₜ[K] v))) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      _ = f c • TensorProduct.map f.toLinearMap (LinearMap.id : V →ₗ[K] V)
          (F.val (1 ⊗ₜ[K] v)) := by
        rw [map_smul, tensorCoefficientMap_smul]
      _ = _ := by
        rw [TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
          LinearMap.id_apply, generalLinearModuleBaseChange_tmul]
        rfl
  | add z z' hz hz' =>
    simp only [map_add, hz, hz']

/-- General linear base change along a coefficient equivalence is conjugation
by its base-linear tensor comparison. The resulting endomorphism is linear
over the target coefficient ring because it is the existing base-change map. -/
theorem generalLinearModuleBaseChange_equiv_apply (e : R ≃ₐ[K] S)
    (F : LinearMap.GeneralLinearGroup R (R ⊗[K] V)) (z : S ⊗[K] V) :
    (generalLinearModuleBaseChange K V R S e.toAlgHom F).val z =
      coefficientTensorEquiv e (F.val ((coefficientTensorEquiv e).symm z)) := by
  have h := generalLinearModuleBaseChange_naturality_apply e.toAlgHom F
    ((coefficientTensorEquiv e).symm z)
  change coefficientTensorEquiv e (F.val ((coefficientTensorEquiv e).symm z)) =
    (generalLinearModuleBaseChange K V R S e.toAlgHom F).val
      (coefficientTensorEquiv e ((coefficientTensorEquiv e).symm z)) at h
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- Base change along an equivalence and along its inverse are inverse on
general linear group values. -/
theorem generalLinearModuleBaseChange_equiv_symm (e : R ≃ₐ[K] S)
    (F : LinearMap.GeneralLinearGroup R (R ⊗[K] V)) :
    generalLinearModuleBaseChange K V S R e.symm.toAlgHom
        (generalLinearModuleBaseChange K V R S e.toAlgHom F) = F := by
  rw [generalLinearModuleBaseChange_comp]
  have he : e.symm.toAlgHom.comp e.toAlgHom = AlgHom.id K R := by
    ext z
    exact e.symm_apply_apply z
  rw [he, generalLinearModuleBaseChange_id]

/-- The double universe lift is compared with the single maximum lift by
stock algebra equivalences; their carriers are not identified. -/
def iteratedLiftAlgEquiv : ULift.{q} (ULift.{p} R) ≃ₐ[K] ULift.{max p q} R :=
  ((ULift.algEquiv (R := K) : ULift.{q} (ULift.{p} R) ≃ₐ[K] ULift.{p} R).trans
    (ULift.algEquiv (R := K) : ULift.{p} R ≃ₐ[K] R)).trans
      (ULift.algEquiv (R := K) : ULift.{max p q} R ≃ₐ[K] R).symm

@[simp] theorem iteratedLiftAlgEquiv_apply (z : ULift.{q} (ULift.{p} R)) :
    iteratedLiftAlgEquiv (K := K) z = ULift.up z.down.down := rfl

/-- The two tensor down-maps compose through the double-to-single comparison. -/
theorem iteratedLift_tensor_down (z : ULift.{q} (ULift.{p} R) ⊗[K] V) :
    coefficientTensorEquiv (ULift.algEquiv (R := K) : ULift.{p} R ≃ₐ[K] R)
        (coefficientTensorEquiv
          (ULift.algEquiv (R := K) : ULift.{q} (ULift.{p} R) ≃ₐ[K] ULift.{p} R) z) =
      coefficientTensorEquiv
        (ULift.algEquiv (R := K) : ULift.{max p q} R ≃ₐ[K] R)
        (coefficientTensorEquiv (iteratedLiftAlgEquiv (K := K)) z) := by
  have h : (coefficientTensorEquiv (K := K) (V := V)
        (ULift.algEquiv (R := K) : ULift.{p} R ≃ₐ[K] R)).toLinearMap.comp
      (coefficientTensorEquiv (K := K) (V := V)
        (ULift.algEquiv (R := K) : ULift.{q} (ULift.{p} R) ≃ₐ[K] ULift.{p} R)).toLinearMap =
      (coefficientTensorEquiv (K := K) (V := V)
        (ULift.algEquiv (R := K) : ULift.{max p q} R ≃ₐ[K] R)).toLinearMap.comp
        (coefficientTensorEquiv (K := K) (V := V)
          (iteratedLiftAlgEquiv (K := K) :
            ULift.{q} (ULift.{p} R) ≃ₐ[K] ULift.{max p q} R)).toLinearMap := by
    apply TensorProduct.ext'
    intro c v
    rfl
  exact LinearMap.congr_fun h z

/-- Successive general linear coefficient changes agree with the single lift
comparison followed by descent. The operator belongs to the scalar-extension
automorphism functor, with coefficient multiplication on the first tensor factor. -/
theorem iteratedLift_generalLinear_down
    (F : (generalLinearModuleFunctor K V).obj
      (CommAlgCat.of K (ULift.{q} (ULift.{p} R)))) :
    generalLinearModuleBaseChange K V (ULift.{p} R) R ULift.algEquiv.toAlgHom
        (generalLinearModuleBaseChange K V (ULift.{q} (ULift.{p} R))
          (ULift.{p} R) ULift.algEquiv.toAlgHom F) =
      generalLinearModuleBaseChange K V (ULift.{max p q} R) R ULift.algEquiv.toAlgHom
        (generalLinearModuleBaseChange K V (ULift.{q} (ULift.{p} R))
          (ULift.{max p q} R) (iteratedLiftAlgEquiv (K := K)).toAlgHom F) := by
  let R₂ : CommAlgCat.{max q (max p r), u} K :=
    CommAlgCat.of K (ULift.{q} (ULift.{p} R))
  let R₁ : CommAlgCat.{max p r, u} K := CommAlgCat.of K (ULift.{p} R)
  let Rₘ : CommAlgCat.{max (max p q) r, u} K :=
    CommAlgCat.of K (ULift.{max p q} R)
  let e₂ : R₂ ≃ₐ[K] R₁ := ULift.algEquiv
  let e₁ : R₁ ≃ₐ[K] R := ULift.algEquiv
  let eₘ : Rₘ ≃ₐ[K] R := ULift.algEquiv
  let e : R₂ ≃ₐ[K] Rₘ := iteratedLiftAlgEquiv (K := K)
  have he : e₁.toAlgHom.comp e₂.toAlgHom = eₘ.toAlgHom.comp e.toAlgHom := by
    ext c
    rfl
  exact (generalLinearModuleBaseChange_comp K V R₂ R₁ R
      e₂.toAlgHom e₁.toAlgHom F).trans
    ((congrArg (fun f : R₂ →ₐ[K] R ↦ generalLinearModuleBaseChange K V R₂ R f F) he).trans
      (generalLinearModuleBaseChange_comp K V R₂ Rₘ R
        e.toAlgHom eₘ.toAlgHom F).symm)

end Coefficients

namespace PointRepresentation

variable {K : Type u} [CommRing K] {A : Type a} [CommRing A] [HopfAlgebra K A]
variable {V : Type v} [AddCommGroup V] [Module K V]

/-- Present the same recovered right comodule in another category of test
algebras. This is the inverse dictionary at the new test level. -/
def changeTestLevel (η : PointRepresentation.{u, a, v, t} K A V) :
    PointRepresentation.{u, a, v, s} K A V :=
  (rightComoduleEquiv.{u, a, v, s} K A V).symm (rightComoduleEquiv K A V η)

/-- Changing test levels retains the specified right-comodule value. -/
@[simp] theorem changeTestLevel_toRightComodule
    (η : PointRepresentation.{u, a, v, t} K A V) :
    (changeTestLevel.{u, a, v, t, s} η).toRightComodule = η.toRightComodule :=
  toRightComodule_ofRightComodule η.toRightComodule

/-- In particular the underlying coaction map is unchanged. -/
@[simp] theorem changeTestLevel_recoveredCoaction
    (η : PointRepresentation.{u, a, v, t} K A V) :
    (changeTestLevel.{u, a, v, t, s} η).recoveredCoaction = η.recoveredCoaction :=
  recoveredCoaction_ofRightComodule η.toRightComodule

/-- At the original test level the presentation is the original NatTrans value. -/
@[simp] theorem changeTestLevel_self (η : PointRepresentation.{u, a, v, t} K A V) :
    changeTestLevel.{u, a, v, t, t} η = η := ofRightComodule_toRightComodule η

/-- Successive changes of tester universe compose as equalities of values. -/
@[simp] theorem changeTestLevel_trans (η : PointRepresentation.{u, a, v, t} K A V) :
    changeTestLevel.{u, a, v, s, r} (changeTestLevel.{u, a, v, t, s} η) =
      changeTestLevel.{u, a, v, t, r} η := by
  apply toRightComodule_injective
  simp only [changeTestLevel_toRightComodule]

/-- Changing to another level and back returns the original value. -/
theorem changeTestLevel_inverse (η : PointRepresentation.{u, a, v, t} K A V) :
    changeTestLevel.{u, a, v, s, t} (changeTestLevel.{u, a, v, t, s} η) = η := by
  rw [changeTestLevel_trans, changeTestLevel_self]

/-- The constructed change of presentation is an equivalence. -/
def testLevelEquiv : PointRepresentation.{u, a, v, t} K A V ≃
    PointRepresentation.{u, a, v, s} K A V where
  toFun := changeTestLevel
  invFun := changeTestLevel
  left_inv := changeTestLevel_inverse
  right_inv := changeTestLevel_inverse

@[simp] theorem testLevelEquiv_apply (η : PointRepresentation.{u, a, v, t} K A V) :
    testLevelEquiv.{u, a, v, t, s} η = changeTestLevel η := rfl

@[simp] theorem testLevelEquiv_symm_apply (η : PointRepresentation.{u, a, v, s} K A V) :
    (testLevelEquiv.{u, a, v, t, s}).symm η = changeTestLevel η := rfl

/-- Every component of the new presentation evaluates the original coaction. -/
theorem changeTestLevel_operator (η : PointRepresentation.{u, a, v, t} K A V)
    (R : CommAlgCat.{max a s, u} K) (g : A →ₐ[K] R) :
    (changeTestLevel.{u, a, v, t, s} η).operator R g = η.pointAction (toConv g) := rfl

/-- Evaluation over any independently sized algebra is unchanged, whether or
not it is an object of either category of test algebras. -/
@[simp] theorem changeTestLevel_evaluate (η : PointRepresentation.{u, a, v, t} K A V)
    {R : Type r} [CommRing R] [Algebra K R] (g : A →ₐ[K] R) :
    (changeTestLevel.{u, a, v, t, s} η).evaluate g = η.evaluate g := by
  change (changeTestLevel η).toRightComodule.evaluate g.toLinearMap = _
  rw [changeTestLevel_toRightComodule]
  rfl

/-- The entire canonical point-action homomorphism is unchanged. -/
@[simp] theorem changeTestLevel_pointAction
    (η : PointRepresentation.{u, a, v, t} K A V)
    {R : Type r} [CommRing R] [Algebra K R] :
    (changeTestLevel.{u, a, v, t, s} η).pointAction (R := R) = η.pointAction := by
  change (changeTestLevel η).toRightComodule.pointAction = _
  rw [changeTestLevel_toRightComodule]
  rfl

/-- Coefficient tensor transport intertwines the canonical point actions.
Both sides evaluate the same recovered right coaction. -/
theorem pointAction_coefficientEquiv (η : PointRepresentation.{u, a, v, t} K A V)
    {R : Type r} [CommRing R] [Algebra K R]
    {S : Type s} [CommRing S] [Algebra K S] (e : R ≃ₐ[K] S)
    (g : A →ₐ[K] R) (z : R ⊗[K] V) :
    coefficientTensorEquiv e ((η.pointAction (toConv g)).val z) =
      (η.pointAction (toConv (e.toAlgHom.comp g))).val (coefficientTensorEquiv e z) :=
  η.pointAction_naturality_apply e.toAlgHom g z

/-- The stock lift and its inverse tensor map give the external action
conjugation formula without an out-of-category component. -/
theorem evaluate_lift_down (η : PointRepresentation.{u, a, v, t} K A V)
    {R : Type r} [CommRing R] [Algebra K R] (g : A →ₐ[K] R)
    (z : ULift.{p} R ⊗[K] V) :
    coefficientTensorEquiv (ULift.algEquiv (R := K) : ULift.{p} R ≃ₐ[K] R)
        (η.evaluate ((ULift.algEquiv (R := K)).symm.toAlgHom.comp g) z) =
      η.evaluate g
        (coefficientTensorEquiv (ULift.algEquiv (R := K) : ULift.{p} R ≃ₐ[K] R) z) := by
  have h := η.pointAction_coefficientEquiv
    (ULift.algEquiv (R := K) : ULift.{p} R ≃ₐ[K] R)
    ((ULift.algEquiv (R := K)).symm.toAlgHom.comp g) z
  have hg : (ULift.algEquiv (R := K) : ULift.{p} R ≃ₐ[K] R).toAlgHom.comp
      ((ULift.algEquiv (R := K)).symm.toAlgHom.comp g) = g := by
    ext c
    rfl
  simpa only [pointAction_val, hg] using h

/-- The stock lift of a coefficient morphism commutes with the down maps. -/
theorem uliftFunctor_map_down {R S : CommAlgCat.{r, u} K} (f : R ⟶ S) :
    (ULift.algEquiv (R := K) : ULift.{s} S ≃ₐ[K] S).toAlgHom.comp
        (((CommAlgCat.uliftFunctor.{s, r, u} K).map f).hom) =
      f.hom.comp (ULift.algEquiv (R := K) : ULift.{s} R ≃ₐ[K] R).toAlgHom := by
  ext c
  rfl

private def restrictionComponent (ξ : PointRepresentation.{u, a, v, max t s} K A V)
    (R : CommAlgCat.{max a t, u} K) :
    ((pointGroupFunctor K A ⋙ GrpCat.uliftFunctor.{v, max a t}).obj R) ⟶
      (generalLinearModuleFunctor K V).obj R :=
  GrpCat.ofHom
    ((generalLinearModuleBaseChange K V
      ((CommAlgCat.uliftFunctor.{s, max a t, u} K).obj R) R
      (ULift.algEquiv (R := K) :
        ((CommAlgCat.uliftFunctor.{s, max a t, u} K).obj R) ≃ₐ[K] R).toAlgHom).comp
      ((ξ.app ((CommAlgCat.uliftFunctor.{s, max a t, u} K).obj R)).hom.comp
        (MulEquiv.ulift.symm.toMonoidHom.comp
          ((AlgHom.convolutionPostcomp
            (ULift.algEquiv (R := K) :
              ((CommAlgCat.uliftFunctor.{s, max a t, u} K).obj R) ≃ₐ[K] R).symm.toAlgHom).comp
              MulEquiv.ulift.toMonoidHom))))

private theorem restrictionComponent_apply
    (ξ : PointRepresentation.{u, a, v, max t s} K A V)
    (R : CommAlgCat.{max a t, u} K) (g : A →ₐ[K] R) :
    (restrictionComponent.{u, a, v, t, s} ξ R).hom (ULift.up (toConv g)) =
      generalLinearModuleBaseChange K V
        ((CommAlgCat.uliftFunctor.{s, max a t, u} K).obj R) R
        (ULift.algEquiv (R := K) :
          ((CommAlgCat.uliftFunctor.{s, max a t, u} K).obj R) ≃ₐ[K] R).toAlgHom
        (ξ.operator ((CommAlgCat.uliftFunctor.{s, max a t, u} K).obj R)
          ((ULift.algEquiv (R := K) :
            ((CommAlgCat.uliftFunctor.{s, max a t, u} K).obj R) ≃ₐ[K] R).symm.toAlgHom.comp g)) :=
  rfl

private theorem restrictionComponent_eq_pointAction
    (ξ : PointRepresentation.{u, a, v, max t s} K A V)
    (R : CommAlgCat.{max a t, u} K) (g : A →ₐ[K] R) :
    (restrictionComponent.{u, a, v, t, s} ξ R).hom (ULift.up (toConv g)) =
      ξ.pointAction (toConv g) := by
  let L : CommAlgCat.{max s (max a t), u} K :=
    (CommAlgCat.uliftFunctor.{s, max a t, u} K).obj R
  let e : L ≃ₐ[K] R := ULift.algEquiv
  let gL : A →ₐ[K] L := e.symm.toAlgHom.comp g
  have hg : e.toAlgHom.comp gL = g := by
    ext c
    exact e.apply_symm_apply (g c)
  have hp : AlgHom.convolutionPostcomp e.toAlgHom (toConv gL) = toConv g := by
    apply ofConv_injective
    exact hg
  exact (restrictionComponent_apply.{u, a, v, t, s} ξ R g).trans
    ((congrArg (generalLinearModuleBaseChange K V L R e.toAlgHom)
      (ξ.pointAction_eq_operator L gL).symm).trans
      ((ξ.pointAction_baseChange (R := L) (S := R) e.toAlgHom (toConv gL)).trans
        (congrArg (ξ.pointAction (R := R)) hp)))

/-- Restrict a representation from the maximum level using the stock
coefficient-lift functor. Components use the given representation at the
lifted algebra, not a reconstructed replacement. -/
def restrictTestLevel (ξ : PointRepresentation.{u, a, v, max t s} K A V) :
    PointRepresentation.{u, a, v, t} K A V where
  app := private restrictionComponent.{u, a, v, t, s} ξ
  naturality {R S} f := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    rintro ⟨g⟩
    change (restrictionComponent.{u, a, v, t, s} ξ S).hom
        (ULift.up (toConv (f.hom.comp g.ofConv))) =
      generalLinearModuleBaseChange K V R S f.hom
        ((restrictionComponent.{u, a, v, t, s} ξ R).hom (ULift.up (toConv g.ofConv)))
    rw [restrictionComponent_eq_pointAction.{u, a, v, t, s},
      restrictionComponent_eq_pointAction.{u, a, v, t, s}]
    exact (ξ.pointAction_baseChange f.hom g).symm

/-- The restriction's component is the existing coefficient group homomorphism
applied to the original component at the genuinely lifted coefficient algebra. -/
theorem restrictTestLevel_operator
    (ξ : PointRepresentation.{u, a, v, max t s} K A V)
    (R : CommAlgCat.{max a t, u} K) (g : A →ₐ[K] R) :
    (restrictTestLevel.{u, a, v, t, s} ξ).operator R g =
      generalLinearModuleBaseChange K V
        ((CommAlgCat.uliftFunctor.{s, max a t, u} K).obj R) R
        (ULift.algEquiv (R := K) :
          ((CommAlgCat.uliftFunctor.{s, max a t, u} K).obj R) ≃ₐ[K] R).toAlgHom
        (ξ.operator ((CommAlgCat.uliftFunctor.{s, max a t, u} K).obj R)
          ((ULift.algEquiv (R := K) :
            ((CommAlgCat.uliftFunctor.{s, max a t, u} K).obj R) ≃ₐ[K] R).symm.toAlgHom.comp g)) :=
  restrictionComponent_apply.{u, a, v, t, s} ξ R g

/-- The characteristic restriction formula is conjugation by `e_R ⊗ id`.
The comparison itself is only base-linear, with its semilinear scalar rule. -/
theorem restrictTestLevel_operator_apply
    (ξ : PointRepresentation.{u, a, v, max t s} K A V)
    (R : CommAlgCat.{max a t, u} K) (g : A →ₐ[K] R) (z : R ⊗[K] V) :
    ((restrictTestLevel.{u, a, v, t, s} ξ).operator R g).val z =
      coefficientTensorEquiv (ULift.algEquiv (R := K) :
        ((CommAlgCat.uliftFunctor.{s, max a t, u} K).obj R) ≃ₐ[K] R)
        ((ξ.operator ((CommAlgCat.uliftFunctor.{s, max a t, u} K).obj R)
          ((ULift.algEquiv (R := K) :
            ((CommAlgCat.uliftFunctor.{s, max a t, u} K).obj R) ≃ₐ[K] R).symm.toAlgHom.comp g)).val
          ((coefficientTensorEquiv
            (ULift.algEquiv (R := K) :
              ((CommAlgCat.uliftFunctor.{s, max a t, u} K).obj R) ≃ₐ[K] R)).symm z)) := by
  rw [restrictTestLevel_operator]
  exact generalLinearModuleBaseChange_equiv_apply _ _ z

/-- The restriction's pure-tensor formula evaluates the original larger
representation's recovered coaction, with no change of that coaction data. -/
theorem restrictTestLevel_operator_tmul
    (ξ : PointRepresentation.{u, a, v, max t s} K A V)
    (R : CommAlgCat.{max a t, u} K) (g : A →ₐ[K] R) (c : R) (v : V) :
    ((restrictTestLevel.{u, a, v, t, s} ξ).operator R g).val (c ⊗ₜ[K] v) =
      c • TensorProduct.map g.toLinearMap (LinearMap.id : V →ₗ[K] V)
        (TensorProduct.comm K V A (ξ.recoveredCoaction v)) := by
  have h : (restrictTestLevel.{u, a, v, t, s} ξ).operator R g =
      ξ.pointAction (toConv g) :=
    restrictionComponent_eq_pointAction.{u, a, v, t, s} ξ R g
  rw [h, pointAction_val]
  exact ξ.evaluate_tmul g c v

/-- Stock-lift restriction agrees with the canonical change of
presentation, as an equality of natural-transformation values. -/
theorem restrictTestLevel_eq_changeTestLevel
    (ξ : PointRepresentation.{u, a, v, max t s} K A V) :
    restrictTestLevel.{u, a, v, t, s} ξ = changeTestLevel ξ := by
  apply PointRepresentation.ext
  intro R g
  exact restrictionComponent_eq_pointAction.{u, a, v, t, s} ξ R g

/-- Restriction retains the original specified comodule value. -/
@[simp] theorem restrictTestLevel_toRightComodule
    (ξ : PointRepresentation.{u, a, v, max t s} K A V) :
    (restrictTestLevel.{u, a, v, t, s} ξ).toRightComodule = ξ.toRightComodule := by
  rw [restrictTestLevel_eq_changeTestLevel, changeTestLevel_toRightComodule]

/-- Restriction retains the coaction map as data. -/
@[simp] theorem restrictTestLevel_recoveredCoaction
    (ξ : PointRepresentation.{u, a, v, max t s} K A V) :
    (restrictTestLevel.{u, a, v, t, s} ξ).recoveredCoaction = ξ.recoveredCoaction := by
  rw [restrictTestLevel_eq_changeTestLevel, changeTestLevel_recoveredCoaction]

/-- Restriction retains every canonical arbitrary-algebra operator. -/
@[simp] theorem restrictTestLevel_evaluate
    (ξ : PointRepresentation.{u, a, v, max t s} K A V)
    {R : Type r} [CommRing R] [Algebra K R] (g : A →ₐ[K] R) :
    (restrictTestLevel.{u, a, v, t, s} ξ).evaluate g = ξ.evaluate g := by
  rw [restrictTestLevel_eq_changeTestLevel, changeTestLevel_evaluate]

/-- The canonical action homomorphism also reads back through restriction,
including independently sized coefficient algebras. -/
@[simp] theorem restrictTestLevel_pointAction
    (ξ : PointRepresentation.{u, a, v, max t s} K A V)
    {R : Type r} [CommRing R] [Algebra K R] :
    (restrictTestLevel.{u, a, v, t, s} ξ).pointAction (R := R) = ξ.pointAction := by
  rw [restrictTestLevel_eq_changeTestLevel, changeTestLevel_pointAction]

/-- Restriction at the same level, still using a coefficient lift, is identity. -/
@[simp] theorem restrictTestLevel_self (η : PointRepresentation.{u, a, v, t} K A V) :
    restrictTestLevel.{u, a, v, t, t} η = η := by
  rw [restrictTestLevel_eq_changeTestLevel, changeTestLevel_self]

/-- Restriction after extension to the common maximum returns the original. -/
@[simp] theorem restrictTestLevel_changeTestLevel
    (η : PointRepresentation.{u, a, v, t} K A V) :
    restrictTestLevel.{u, a, v, t, s}
        (changeTestLevel.{u, a, v, t, max t s} η) = η := by
  rw [restrictTestLevel_eq_changeTestLevel, changeTestLevel_inverse]

/-- Extension after stock-lift restriction returns the original larger value. -/
@[simp] theorem changeTestLevel_restrictTestLevel
    (ξ : PointRepresentation.{u, a, v, max t s} K A V) :
    changeTestLevel.{u, a, v, t, max t s}
        (restrictTestLevel.{u, a, v, t, s} ξ) = ξ := by
  rw [restrictTestLevel_eq_changeTestLevel, changeTestLevel_inverse]

/-- Extending through a common maximum and restricting gives the same
presentation as direct canonical change, including unequal starting levels. -/
theorem restrictTestLevel_commonMax
    (η : PointRepresentation.{u, a, v, r} K A V) :
    restrictTestLevel.{u, a, v, t, s}
        (changeTestLevel.{u, a, v, r, max t s} η) =
      changeTestLevel.{u, a, v, r, t} η := by
  rw [restrictTestLevel_eq_changeTestLevel, changeTestLevel_trans]

/-- Two restrictions along coefficient lifts agree with the single
maximum restriction, as values, not merely up to an unspecified isomorphism. -/
theorem restrictTestLevel_trans
    (ξ : PointRepresentation.{u, a, v, max (max t s) r} K A V) :
    restrictTestLevel.{u, a, v, t, s}
        (restrictTestLevel.{u, a, v, max t s, r} ξ) =
      restrictTestLevel.{u, a, v, t, max s r} ξ := by
  simp only [restrictTestLevel_eq_changeTestLevel, changeTestLevel_trans]

/-- Iterating common-maximum extension and descent is independent of the
intermediate maximum, as an equality of representation values. -/
theorem restrictTestLevel_iteratedCommonMax
    (η : PointRepresentation.{u, a, v, p} K A V) :
    restrictTestLevel.{u, a, v, t, s}
        (restrictTestLevel.{u, a, v, max t s, r}
          (changeTestLevel.{u, a, v, p, max (max t s) r} η)) =
      changeTestLevel.{u, a, v, p, t} η := by
  simp only [restrictTestLevel_eq_changeTestLevel, changeTestLevel_trans]

/-- Postcomposition with the double-to-single algebra equivalence sends the
doubly lifted point to the single lifted point. -/
theorem iteratedLift_point {R : Type r} [CommRing R] [Algebra K R]
    (g : A →ₐ[K] R) :
    (iteratedLiftAlgEquiv (K := K) :
        ULift.{q} (ULift.{p} R) ≃ₐ[K] ULift.{max p q} R).toAlgHom.comp
      ((ULift.algEquiv (R := K) :
          ULift.{q} (ULift.{p} R) ≃ₐ[K] ULift.{p} R).symm.toAlgHom.comp
        ((ULift.algEquiv (R := K) : ULift.{p} R ≃ₐ[K] R).symm.toAlgHom.comp g)) =
      (ULift.algEquiv (R := K) : ULift.{max p q} R ≃ₐ[K] R).symm.toAlgHom.comp g := by
  ext c
  rfl

/-- Naturality of the given larger representation compares its components
at the double and single lifts through the specified algebra equivalence. -/
theorem iteratedLift_operator
    (ξ : PointRepresentation.{u, a, v, max (max t p) q} K A V)
    (R : CommAlgCat.{max a t, u} K) (g : A →ₐ[K] R) :
    generalLinearModuleBaseChange K V (ULift.{q} (ULift.{p} R))
        (ULift.{max p q} R) (iteratedLiftAlgEquiv (K := K)).toAlgHom
        (ξ.operator (CommAlgCat.of K (ULift.{q} (ULift.{p} R)))
          ((ULift.algEquiv (R := K) :
              ULift.{q} (ULift.{p} R) ≃ₐ[K] ULift.{p} R).symm.toAlgHom.comp
            ((ULift.algEquiv (R := K) : ULift.{p} R ≃ₐ[K] R).symm.toAlgHom.comp g))) =
      ξ.operator (CommAlgCat.of K (ULift.{max p q} R))
        ((ULift.algEquiv (R := K) : ULift.{max p q} R ≃ₐ[K] R).symm.toAlgHom.comp g) := by
  have h := ξ.operator_baseChange
    (R := CommAlgCat.of K (ULift.{q} (ULift.{p} R)))
    (S := CommAlgCat.of K (ULift.{max p q} R))
    (iteratedLiftAlgEquiv (K := K)).toAlgHom
    ((ULift.algEquiv (R := K) :
        ULift.{q} (ULift.{p} R) ≃ₐ[K] ULift.{p} R).symm.toAlgHom.comp
      ((ULift.algEquiv (R := K) : ULift.{p} R ≃ₐ[K] R).symm.toAlgHom.comp g))
  simpa only [iteratedLift_point] using h

/-- Descending the given double-lift component in two steps is the same general
linear group value as descending its single-lift component in one step. -/
theorem iteratedLift_operator_down
    (ξ : PointRepresentation.{u, a, v, max (max t p) q} K A V)
    (R : CommAlgCat.{max a t, u} K) (g : A →ₐ[K] R) :
    generalLinearModuleBaseChange K V (ULift.{p} R) R ULift.algEquiv.toAlgHom
        (generalLinearModuleBaseChange K V (ULift.{q} (ULift.{p} R))
          (ULift.{p} R) ULift.algEquiv.toAlgHom
          (ξ.operator (CommAlgCat.of K (ULift.{q} (ULift.{p} R)))
            ((ULift.algEquiv (R := K) :
                ULift.{q} (ULift.{p} R) ≃ₐ[K] ULift.{p} R).symm.toAlgHom.comp
              ((ULift.algEquiv (R := K) : ULift.{p} R ≃ₐ[K] R).symm.toAlgHom.comp g)))) =
      generalLinearModuleBaseChange K V (ULift.{max p q} R) R ULift.algEquiv.toAlgHom
        (ξ.operator (CommAlgCat.of K (ULift.{max p q} R))
          ((ULift.algEquiv (R := K) : ULift.{max p q} R ≃ₐ[K] R).symm.toAlgHom.comp g)) := by
  let L₂ : CommAlgCat.{max q (max p (max a t)), u} K :=
    CommAlgCat.of K (ULift.{q} (ULift.{p} R))
  let Lₘ : CommAlgCat.{max (max p q) (max a t), u} K :=
    CommAlgCat.of K (ULift.{max p q} R)
  let e₁ : ULift.{p} R ≃ₐ[K] R := ULift.algEquiv
  let e₂ : L₂ ≃ₐ[K] ULift.{p} R := ULift.algEquiv
  let eₘ : Lₘ ≃ₐ[K] R := ULift.algEquiv
  let g₂ : A →ₐ[K] L₂ := e₂.symm.toAlgHom.comp (e₁.symm.toAlgHom.comp g)
  exact (iteratedLift_generalLinear_down.{u, v, max a t, p, q}
      (K := K) (V := V) (R := R)
      (ξ.operator.{u, a, v, max (max t p) q} L₂ g₂)).trans
    (congrArg (generalLinearModuleBaseChange K V Lₘ R eₘ.toAlgHom)
      (iteratedLift_operator.{u, a, v, t, p, q} ξ R g))

/-- The tensor comparison between iterated and single lifts intertwines the
operators for their respective lifted points. -/
theorem iteratedLift_evaluate (η : PointRepresentation.{u, a, v, t} K A V)
    {R : Type r} [CommRing R] [Algebra K R] (g : A →ₐ[K] R)
    (z : ULift.{q} (ULift.{p} R) ⊗[K] V) :
    coefficientTensorEquiv (iteratedLiftAlgEquiv (K := K) :
        ULift.{q} (ULift.{p} R) ≃ₐ[K] ULift.{max p q} R)
      (η.evaluate
        ((ULift.algEquiv (R := K) :
            ULift.{q} (ULift.{p} R) ≃ₐ[K] ULift.{p} R).symm.toAlgHom.comp
          ((ULift.algEquiv (R := K) : ULift.{p} R ≃ₐ[K] R).symm.toAlgHom.comp g)) z) =
      η.evaluate
        ((ULift.algEquiv (R := K) : ULift.{max p q} R ≃ₐ[K] R).symm.toAlgHom.comp g)
        (coefficientTensorEquiv (iteratedLiftAlgEquiv (K := K)) z) := by
  have h := η.pointAction_coefficientEquiv
    (iteratedLiftAlgEquiv (K := K) :
      ULift.{q} (ULift.{p} R) ≃ₐ[K] ULift.{max p q} R)
    ((ULift.algEquiv (R := K) :
        ULift.{q} (ULift.{p} R) ≃ₐ[K] ULift.{p} R).symm.toAlgHom.comp
      ((ULift.algEquiv (R := K) : ULift.{p} R ≃ₐ[K] R).symm.toAlgHom.comp g)) z
  simpa only [pointAction_val, iteratedLift_point] using h

/-- Every algebra map can be compared at a common maximum using separately
lifted coefficient algebras and then descended. This is a universe-polymorphic
theorem for each pair of coefficient universes, not a binder over universes. -/
theorem commonMax_naturality (η : PointRepresentation.{u, a, v, t} K A V)
    {R : Type r} [CommRing R] [Algebra K R]
    {S : Type s} [CommRing S] [Algebra K S] (f : R →ₐ[K] S)
    (g : A →ₐ[K] R) (z : R ⊗[K] V) :
    TensorProduct.map f.toLinearMap (LinearMap.id : V →ₗ[K] V) (η.evaluate g z) =
      η.evaluate (f.comp g)
        (TensorProduct.map f.toLinearMap (LinearMap.id : V →ₗ[K] V) z) := by
  let R' : CommAlgCat.{max a (max t (max r s)), u} K :=
    CommAlgCat.of K (ULift.{max a (max t (max r s))} R)
  let S' : CommAlgCat.{max a (max t (max r s)), u} K :=
    CommAlgCat.of K (ULift.{max a (max t (max r s))} S)
  let eR : R' ≃ₐ[K] R := ULift.algEquiv
  let eS : S' ≃ₐ[K] S := ULift.algEquiv
  let f' : R' →ₐ[K] S' := eS.symm.toAlgHom.comp (f.comp eR.toAlgHom)
  let g' : A →ₐ[K] R' := eR.symm.toAlgHom.comp g
  let η' := changeTestLevel.{u, a, v, t, max a (max t (max r s))} η
  let dR := coefficientTensorEquiv (V := V) eR
  let dS := coefficientTensorEquiv (V := V) eS
  let z' := dR.symm z
  have hsquare (y : R' ⊗[K] V) :
      dS (TensorProduct.map f'.toLinearMap (LinearMap.id : V →ₗ[K] V) y) =
        TensorProduct.map f.toLinearMap (LinearMap.id : V →ₗ[K] V) (dR y) := by
    have h : dS.toLinearMap.comp
          (TensorProduct.map f'.toLinearMap (LinearMap.id : V →ₗ[K] V)) =
        (TensorProduct.map f.toLinearMap (LinearMap.id : V →ₗ[K] V)).comp
          dR.toLinearMap := by
      apply TensorProduct.ext'
      intro c v
      rfl
    exact LinearMap.congr_fun h y
  have hg : f'.comp g' = eS.symm.toAlgHom.comp (f.comp g) := by
    ext c
    rfl
  have hbig : TensorProduct.map f'.toLinearMap (LinearMap.id : V →ₗ[K] V)
        ((η'.operator R' g').val z') =
      (η'.operator S' (f'.comp g')).val
        (TensorProduct.map f'.toLinearMap (LinearMap.id : V →ₗ[K] V) z') := by
    have h := generalLinearModuleBaseChange_naturality_apply f' (η'.operator R' g') z'
    rw [η'.operator_baseChange] at h
    exact h
  have hR (y : R' ⊗[K] V) :
      dR ((η'.operator R' g').val y) = η.evaluate g (dR y) := by
    rw [operator_val_eq_evaluate, changeTestLevel_evaluate]
    exact η.evaluate_lift_down g y
  have hS (y : S' ⊗[K] V) :
      dS ((η'.operator S' (eS.symm.toAlgHom.comp (f.comp g))).val y) =
        η.evaluate (f.comp g) (dS y) := by
    rw [operator_val_eq_evaluate, changeTestLevel_evaluate]
    exact η.evaluate_lift_down (f.comp g) y
  calc
    _ = TensorProduct.map f.toLinearMap (LinearMap.id : V →ₗ[K] V)
        (dR ((η'.operator R' g').val z')) := by
      rw [hR, LinearEquiv.apply_symm_apply]
    _ = dS (TensorProduct.map f'.toLinearMap (LinearMap.id : V →ₗ[K] V)
        ((η'.operator R' g').val z')) := (hsquare _).symm
    _ = dS ((η'.operator S' (f'.comp g')).val
        (TensorProduct.map f'.toLinearMap (LinearMap.id : V →ₗ[K] V) z')) :=
      congrArg dS hbig
    _ = η.evaluate (f.comp g)
        (dS (TensorProduct.map f'.toLinearMap (LinearMap.id : V →ₗ[K] V) z')) := by
      rw [hg, hS]
    _ = _ := by rw [hsquare, LinearEquiv.apply_symm_apply]

section Intertwiners

variable {W : Type w} [AddCommGroup W] [Module K W]
variable {U : Type x} [AddCommGroup U] [Module K U]
variable (η : PointRepresentation.{u, a, v, t} K A V)
variable (θ : PointRepresentation.{u, a, w, t} K A W)
variable (ξ : PointRepresentation.{u, a, x, t} K A U)

/-- Change the test level of an intertwiner through the existing Hom dictionary,
retaining its original base-linear map. -/
def changeTestLevelHom (f : PointHom η θ) :
    PointHom (changeTestLevel.{u, a, v, t, s} η)
      (changeTestLevel.{u, a, w, t, s} θ) :=
  (pointHomEquiv _ _).symm
    { toLinearMap := (pointHomEquiv η θ f).toLinearMap
      colinear := by
        simpa only [changeTestLevel_toRightComodule] using
          (pointHomEquiv η θ f).colinear }

@[simp] theorem changeTestLevelHom_toLinearMap (f : PointHom η θ) :
    (changeTestLevelHom.{u, a, v, w, t, s} η θ f).toLinearMap = f.toLinearMap := rfl

/-- Changing the tester universe is also an equivalence on the existing
modules of point intertwiners. Both directions retain the same linear map. -/
def testLevelHomEquiv : PointHom η θ ≃ₗ[K]
    PointHom (changeTestLevel.{u, a, v, t, s} η)
      (changeTestLevel.{u, a, w, t, s} θ) where
  toFun := changeTestLevelHom η θ
  invFun f := (pointHomEquiv η θ).symm
    { toLinearMap := (pointHomEquiv _ _ f).toLinearMap
      colinear := by
        simpa only [changeTestLevel_toRightComodule] using
          (pointHomEquiv _ _ f).colinear }
  left_inv f := by
    apply PointHom.toLinearMap_injective
    rfl
  right_inv f := by
    apply PointHom.toLinearMap_injective
    rfl
  map_add' f h := by
    apply PointHom.toLinearMap_injective
    rfl
  map_smul' c f := by
    apply PointHom.toLinearMap_injective
    rfl

@[simp] theorem testLevelHomEquiv_apply_toLinearMap (f : PointHom η θ) :
    (testLevelHomEquiv.{u, a, v, w, t, s} η θ f).toLinearMap = f.toLinearMap := rfl

@[simp] theorem testLevelHomEquiv_symm_apply_toLinearMap
    (f : PointHom (changeTestLevel.{u, a, v, t, s} η)
      (changeTestLevel.{u, a, w, t, s} θ)) :
    ((testLevelHomEquiv.{u, a, v, w, t, s} η θ).symm f).toLinearMap =
      f.toLinearMap := rfl

/-- The identity intertwiner retains the identity map after changing levels. -/
@[simp] theorem changeTestLevelHom_id :
    changeTestLevelHom.{u, a, v, v, t, s} η η (PointHom.id η) =
      PointHom.id (changeTestLevel η) := by
  apply PointHom.toLinearMap_injective
  rfl

/-- Changing levels respects composition of the same underlying linear maps. -/
@[simp] theorem changeTestLevelHom_comp (h : PointHom θ ξ) (f : PointHom η θ) :
    changeTestLevelHom.{u, a, v, x, t, s} η ξ (h.comp f) =
      (changeTestLevelHom.{u, a, w, x, t, s} θ ξ h).comp
        (changeTestLevelHom.{u, a, v, w, t, s} η θ f) := by
  apply PointHom.toLinearMap_injective
  rfl

/-- At every independent coefficient algebra the transported intertwiner uses
exactly the original scalar-extended linear map. -/
theorem changeTestLevelHom_evaluate (f : PointHom η θ)
    {R : Type r} [CommRing R] [Algebra K R] (g : A →ₐ[K] R) :
    (changeTestLevelHom.{u, a, v, w, t, s} η θ f).toLinearMap.baseChange R ∘ₗ
        (changeTestLevel.{u, a, v, t, s} η).evaluate g =
      (changeTestLevel.{u, a, w, t, s} θ).evaluate g ∘ₗ f.toLinearMap.baseChange R := by
  simpa only [changeTestLevelHom_toLinearMap] using
    (changeTestLevelHom.{u, a, v, w, t, s} η θ f).baseChange_comp_evaluate g

end Intertwiners

/-- For the scalar comodule, changing test levels leaves every available
component equal to the identity, for an arbitrary base module. -/
theorem changeTestLevel_scalar_operator (R : CommAlgCat.{max u s, u} K)
    (g : K →ₐ[K] R) :
    (changeTestLevel.{u, u, v, t, s}
      (ofRightComodule (Coalgebra.RightComodule.scalar K V))).operator R g = 1 := by
  rw [changeTestLevel_operator, pointAction_ofRightComodule]
  apply Units.ext
  rw [Coalgebra.RightComodule.pointAction_val, Coalgebra.RightComodule.scalar_evaluate]
  simp [Module.End.one_eq_id]

end PointRepresentation

end AlgebraicGeometry
