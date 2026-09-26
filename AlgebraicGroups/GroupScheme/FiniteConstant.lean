/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.RingTheory.TensorProduct.Pi

/-!
# Finite constant group schemes

This file constructs the constant group scheme attached to a finite abstract
group. Its coordinate ring is the algebra of functions on the group. A
dedicated type keeps its group-law coalgebra distinct from the componentwise
coalgebra already available on finite dependent products.

## Main definitions

- `AlgebraicGeometry.FiniteGroupFunctions`: the coordinate function algebra.
- `AlgebraicGeometry.FiniteGroupFunctions.comulAlgHom`: comultiplication dual
  to the abstract group law.
- `AlgebraicGeometry.finiteConstantGroupScheme`: the resulting affine group
  scheme.
- `AlgebraicGeometry.finiteConstantGroupSchemePointHom`: the multiplicative
  map from abstract group elements to rational points of the constant scheme.
- `AlgebraicGeometry.finiteConstantSigmaIso`: its underlying scheme is the
  finite coproduct of copies of the base.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

namespace AlgebraicGeometry

universe u v

/-- The coordinate ring of functions on a finite abstract group.  This is a
dedicated type because its coalgebra structure comes from multiplication in
the indexing group, not from the componentwise coalgebra on a finite product.
-/
def FiniteGroupFunctions (K : Type u) (Γ : Type v) := Γ → K

namespace FiniteGroupFunctions

variable (K : Type u) (Γ : Type v)

instance [CommRing K] : CommRing (FiniteGroupFunctions K Γ) :=
  inferInstanceAs (CommRing (Γ → K))

instance [CommRing K] : Algebra K (FiniteGroupFunctions K Γ) :=
  inferInstanceAs (Algebra K (Γ → K))

/-- Forget the dedicated Hopf-algebra type and view its elements as ordinary functions. -/
def toPiAlgEquiv [CommRing K] : FiniteGroupFunctions K Γ ≃ₐ[K] (Γ → K) :=
  AlgEquiv.refl

instance [CommRing K] [_root_.IsReduced K] : _root_.IsReduced (FiniteGroupFunctions K Γ) where
  eq_zero _f hf := funext fun g ↦ (hf.map (Pi.evalRingHom (fun _ : Γ ↦ K) g)).eq_zero

/-- The coordinate delta functions form the standard basis of the function algebra. -/
noncomputable def basis [CommRing K] [Fintype Γ] :
    Module.Basis Γ K (FiniteGroupFunctions K Γ) := by
  letI : Finite Γ := Fintype.finite (inferInstance : Fintype Γ)
  change Module.Basis Γ K (Γ → K)
  exact Pi.basisFun K Γ

noncomputable instance [CommRing K] [Fintype Γ] :
    Module.Finite K (FiniteGroupFunctions K Γ) := by
  let _ : Finite Γ := Fintype.finite (inferInstance : Fintype Γ)
  exact Module.Finite.of_basis (basis K Γ)

/-- Reassociate and swap curried variables so that a tensor of functions
`x ⊗ y` is evaluated at `(g, h)` as `x g * y h`. -/
def swapCurryAlgEquiv [CommRing K] :
    (Γ → FiniteGroupFunctions K Γ) ≃ₐ[K] ((Γ × Γ) → K) where
  toFun f p := f p.2 p.1
  invFun f h g := f (g, h)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The coordinate-ring equivalence identifying the tensor product of two
finite function algebras with functions on the product. -/
noncomputable def tensorAlgEquiv [CommRing K] [Fintype Γ] :
    FiniteGroupFunctions K Γ ⊗[K] FiniteGroupFunctions K Γ ≃ₐ[K]
      ((Γ × Γ) → K) := by
  classical
  exact (Algebra.TensorProduct.piScalarRight K K (FiniteGroupFunctions K Γ) Γ).trans
    (swapCurryAlgEquiv K Γ)

/-- Tensoring on the right by an arbitrary commutative algebra commutes with
the finite product defining `FiniteGroupFunctions`. -/
private noncomputable def tensorLeftAlgEquiv [CommRing K] [Fintype Γ]
    (B : Type*) [CommRing B] [Algebra K B] :
    FiniteGroupFunctions K Γ ⊗[K] B ≃ₐ[K] (Γ → B) := by
  classical
  exact (Algebra.TensorProduct.comm K (FiniteGroupFunctions K Γ) B).trans
    (Algebra.TensorProduct.piScalarRight K K B Γ)

@[simp]
lemma tensorAlgEquiv_tmul_apply [CommRing K] [Fintype Γ]
    (x y : FiniteGroupFunctions K Γ) (g h : Γ) :
    tensorAlgEquiv K Γ (x ⊗ₜ[K] y) (g, h) = x g * y h := by
  change y h * x g = x g * y h
  exact mul_comm _ _

variable [CommRing K] [Fintype Γ] [Group Γ]

/-- Evaluation of a finite function at a group element. -/
def evalAlgHom (g : Γ) : FiniteGroupFunctions K Γ →ₐ[K] K :=
  Pi.evalAlgHom K (fun _ : Γ ↦ K) g

/-- Evaluation of a tensor of finite functions at a pair of group elements. -/
private def tensorEvalAlgHom (g h : Γ) :
    FiniteGroupFunctions K Γ ⊗[K] FiniteGroupFunctions K Γ →ₐ[K] K :=
  Algebra.TensorProduct.lift (evalAlgHom K Γ g) (evalAlgHom K Γ h)
    fun _ _ ↦ Commute.all _ _

omit [Fintype Γ] [Group Γ] in
@[simp]
private lemma tensorEvalAlgHom_tmul (x y : FiniteGroupFunctions K Γ) (g h : Γ) :
    tensorEvalAlgHom K Γ g h (x ⊗ₜ[K] y) = x g * y h := by
  change (Algebra.TensorProduct.lift (evalAlgHom K Γ g) (evalAlgHom K Γ h)
    (fun _ _ ↦ Commute.all _ _)) (x ⊗ₜ[K] y) = x g * y h
  rw [Algebra.TensorProduct.lift_tmul]
  rfl

omit [Group Γ] in
private lemma tensorEvalAlgHom_eq_tensorAlgEquiv_apply
    (z : FiniteGroupFunctions K Γ ⊗[K] FiniteGroupFunctions K Γ) (g h : Γ) :
    tensorEvalAlgHom K Γ g h z = tensorAlgEquiv K Γ z (g, h) := by
  induction z using TensorProduct.inductionOn with
  | tmul x y => simp
  | add x y hx hy => simp [hx, hy]

/-- Evaluation of a right-associated triple tensor. -/
private def tripleEvalAlgHom (g h k : Γ) :
    FiniteGroupFunctions K Γ ⊗[K]
        (FiniteGroupFunctions K Γ ⊗[K] FiniteGroupFunctions K Γ) →ₐ[K] K :=
  Algebra.TensorProduct.lift (evalAlgHom K Γ g) (tensorEvalAlgHom K Γ h k)
    fun _ _ ↦ Commute.all _ _

omit [Fintype Γ] [Group Γ] in
@[simp]
private lemma tripleEvalAlgHom_tmul (x : FiniteGroupFunctions K Γ)
    (z : FiniteGroupFunctions K Γ ⊗[K] FiniteGroupFunctions K Γ) (g h k : Γ) :
    tripleEvalAlgHom K Γ g h k (x ⊗ₜ[K] z) =
      x g * tensorEvalAlgHom K Γ h k z := by
  change (Algebra.TensorProduct.lift (evalAlgHom K Γ g)
    (tensorEvalAlgHom K Γ h k) (fun _ _ ↦ Commute.all _ _))
      (x ⊗ₜ[K] z) = x g * tensorEvalAlgHom K Γ h k z
  rw [Algebra.TensorProduct.lift_tmul]
  rfl

omit [Fintype Γ] [Group Γ] in
private lemma tripleEvalAlgHom_assoc_tmul
    (z : FiniteGroupFunctions K Γ ⊗[K] FiniteGroupFunctions K Γ)
    (x : FiniteGroupFunctions K Γ) (g h k : Γ) :
    tripleEvalAlgHom K Γ g h k
        (Algebra.TensorProduct.assoc K K K _ _ _ (z ⊗ₜ[K] x)) =
      tensorEvalAlgHom K Γ g h z * x k := by
  induction z using TensorProduct.inductionOn with
  | tmul a b => simp [mul_assoc]
  | add a b ha hb =>
      rw [TensorProduct.add_tmul, map_add, map_add, ha, hb, map_add, add_mul]

omit [Group Γ] in
@[simp]
private lemma tensorLeftAlgEquiv_tmul_apply
    (x : FiniteGroupFunctions K Γ)
    (q : FiniteGroupFunctions K Γ ⊗[K] FiniteGroupFunctions K Γ) (g : Γ) :
    tensorLeftAlgEquiv K Γ
        (FiniteGroupFunctions K Γ ⊗[K] FiniteGroupFunctions K Γ)
        (x ⊗ₜ[K] q) g = x g • q := by
  classical
  change
    Algebra.TensorProduct.piScalarRight K K
        (FiniteGroupFunctions K Γ ⊗[K] FiniteGroupFunctions K Γ) Γ
        (Algebra.TensorProduct.comm K (FiniteGroupFunctions K Γ)
          (FiniteGroupFunctions K Γ ⊗[K] FiniteGroupFunctions K Γ) (x ⊗ₜ[K] q)) g =
      x g • q
  rw [Algebra.TensorProduct.comm_tmul]
  rfl

omit [Group Γ] in
private lemma tripleCoordinate_eq_tripleEvalAlgHom
    (z : FiniteGroupFunctions K Γ ⊗[K]
      (FiniteGroupFunctions K Γ ⊗[K] FiniteGroupFunctions K Γ))
    (g h k : Γ) :
    tensorAlgEquiv K Γ
        (tensorLeftAlgEquiv K Γ
          (FiniteGroupFunctions K Γ ⊗[K] FiniteGroupFunctions K Γ) z g)
        (h, k) = tripleEvalAlgHom K Γ g h k z := by
  induction z using TensorProduct.inductionOn with
  | tmul x q =>
      simp [tripleEvalAlgHom_tmul,
        tensorEvalAlgHom_eq_tensorAlgEquiv_apply]
  | add x y hx hy => simp [hx, hy]

/-- Comultiplication on functions, dual to multiplication in the group. -/
noncomputable def comulAlgHom :
    FiniteGroupFunctions K Γ →ₐ[K]
      FiniteGroupFunctions K Γ ⊗[K] FiniteGroupFunctions K Γ :=
  (tensorAlgEquiv K Γ).symm.toAlgHom.comp <|
    AlgHom.pi fun p : Γ × Γ ↦ Pi.evalAlgHom K (fun _ : Γ ↦ K) (p.1 * p.2)

/-- Counit on functions, given by evaluation at the identity. -/
def counitAlgHom : FiniteGroupFunctions K Γ →ₐ[K] K :=
  evalAlgHom K Γ 1

/-- Antipode on functions, given by precomposition with inversion. -/
def antipodeAlgHom :
    FiniteGroupFunctions K Γ →ₐ[K] FiniteGroupFunctions K Γ :=
  AlgHom.pi fun g : Γ ↦ Pi.evalAlgHom K (fun _ : Γ ↦ K) g⁻¹

@[simp]
lemma tensorAlgEquiv_comulAlgHom_apply
    (f : FiniteGroupFunctions K Γ) (g h : Γ) :
    tensorAlgEquiv K Γ (comulAlgHom K Γ f) (g, h) = f (g * h) := by
  let z : (Γ × Γ) → K :=
    (AlgHom.pi fun p : Γ × Γ ↦ Pi.evalAlgHom K (fun _ : Γ ↦ K) (p.1 * p.2)) f
  have hz := congrFun ((tensorAlgEquiv K Γ).apply_symm_apply z) (g, h)
  exact hz

@[simp]
private lemma tensorEvalAlgHom_comulAlgHom_apply
    (f : FiniteGroupFunctions K Γ) (g h : Γ) :
    tensorEvalAlgHom K Γ g h (comulAlgHom K Γ f) = f (g * h) := by
  rw [tensorEvalAlgHom_eq_tensorAlgEquiv_apply,
    tensorAlgEquiv_comulAlgHom_apply]

omit [Fintype Γ] in
@[simp]
lemma counitAlgHom_apply (f : FiniteGroupFunctions K Γ) :
    counitAlgHom K Γ f = f 1 := rfl

omit [Fintype Γ] in
@[simp]
lemma antipodeAlgHom_apply (f : FiniteGroupFunctions K Γ) (g : Γ) :
    antipodeAlgHom K Γ f g = f g⁻¹ := rfl

noncomputable instance instBialgebra : Bialgebra K (FiniteGroupFunctions K Γ) :=
  Bialgebra.ofAlgHom (comulAlgHom K Γ) (counitAlgHom K Γ)
    (by
      ext f
      apply (tensorLeftAlgEquiv K Γ
        (FiniteGroupFunctions K Γ ⊗[K] FiniteGroupFunctions K Γ)).injective
      funext g
      apply (tensorAlgEquiv K Γ).injective
      funext p
      rw [tripleCoordinate_eq_tripleEvalAlgHom,
        tripleCoordinate_eq_tripleEvalAlgHom]
      change tripleEvalAlgHom K Γ g p.1 p.2
          (Algebra.TensorProduct.assoc K K K _ _ _
            (Algebra.TensorProduct.map (comulAlgHom K Γ) (AlgHom.id K _)
              (comulAlgHom K Γ f))) =
        tripleEvalAlgHom K Γ g p.1 p.2
          (Algebra.TensorProduct.map (AlgHom.id K _) (comulAlgHom K Γ)
            (comulAlgHom K Γ f))
      calc
        _ = tensorEvalAlgHom K Γ (g * p.1) p.2 (comulAlgHom K Γ f) := by
          have h :
              (tripleEvalAlgHom K Γ g p.1 p.2).comp
                  ((Algebra.TensorProduct.assoc K K K _ _ _).toAlgHom.comp
                    (Algebra.TensorProduct.map (comulAlgHom K Γ) (AlgHom.id K _))) =
                tensorEvalAlgHom K Γ (g * p.1) p.2 := by
            apply Algebra.TensorProduct.ext'
            intro x y
            simp [tripleEvalAlgHom_assoc_tmul]
          exact DFunLike.congr_fun h (comulAlgHom K Γ f)
        _ = f ((g * p.1) * p.2) := by simp
        _ = f (g * (p.1 * p.2)) := by rw [mul_assoc]
        _ = tensorEvalAlgHom K Γ g (p.1 * p.2) (comulAlgHom K Γ f) := by simp
        _ = _ := by
          have h :
              (tripleEvalAlgHom K Γ g p.1 p.2).comp
                  (Algebra.TensorProduct.map (AlgHom.id K _) (comulAlgHom K Γ)) =
                tensorEvalAlgHom K Γ g (p.1 * p.2) := by
            apply Algebra.TensorProduct.ext'
            intro x y
            simp only [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
              AlgHom.id_apply, tripleEvalAlgHom_tmul,
              tensorEvalAlgHom_comulAlgHom_apply]
            rfl
          exact (DFunLike.congr_fun h (comulAlgHom K Γ f)).symm)
    (by
      ext f
      apply (Algebra.TensorProduct.lid K (FiniteGroupFunctions K Γ)).injective
      funext g
      calc
        _ = tensorEvalAlgHom K Γ 1 g (comulAlgHom K Γ f) := by
          have h :
              (evalAlgHom K Γ g).comp
                  ((Algebra.TensorProduct.lid K (FiniteGroupFunctions K Γ)).toAlgHom.comp
                    (Algebra.TensorProduct.map (counitAlgHom K Γ) (AlgHom.id K _))) =
                tensorEvalAlgHom K Γ 1 g := by
            apply Algebra.TensorProduct.ext'
            intro x y
            simp only [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
              AlgHom.id_apply, counitAlgHom_apply, tensorEvalAlgHom_tmul]
            rfl
          exact DFunLike.congr_fun h (comulAlgHom K Γ f)
        _ = f (1 * g) := by simp
        _ = f g := by rw [one_mul]
        _ = _ := (congrFun
          ((Algebra.TensorProduct.lid K (FiniteGroupFunctions K Γ)).apply_symm_apply f) g).symm)
    (by
      ext f
      apply (Algebra.TensorProduct.rid K K (FiniteGroupFunctions K Γ)).injective
      funext g
      calc
        _ = tensorEvalAlgHom K Γ g 1 (comulAlgHom K Γ f) := by
          have h :
              (evalAlgHom K Γ g).comp
                  ((Algebra.TensorProduct.rid K K (FiniteGroupFunctions K Γ)).toAlgHom.comp
                    (Algebra.TensorProduct.map (AlgHom.id K _) (counitAlgHom K Γ))) =
                tensorEvalAlgHom K Γ g 1 := by
            apply Algebra.TensorProduct.ext'
            intro x y
            simp only [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
              AlgHom.id_apply, counitAlgHom_apply, tensorEvalAlgHom_tmul]
            change (evalAlgHom K Γ g) (y 1 • x) = x g * y 1
            change y 1 * x g = x g * y 1
            exact mul_comm _ _
          exact DFunLike.congr_fun h (comulAlgHom K Γ f)
        _ = f (g * 1) := by simp
        _ = f g := by rw [mul_one]
        _ = _ := (congrFun
          ((Algebra.TensorProduct.rid K K (FiniteGroupFunctions K Γ)).apply_symm_apply f) g).symm)

omit [Fintype Γ] in
private lemma evalAlgHom_comp_lift_antipode_id (g : Γ) :
    (evalAlgHom K Γ g).comp
        (Algebra.TensorProduct.lift (antipodeAlgHom K Γ) (AlgHom.id K _)
          (fun _ _ ↦ Commute.all _ _)) =
      tensorEvalAlgHom K Γ g⁻¹ g := by
  apply Algebra.TensorProduct.ext'
  intro x y
  simp only [AlgHom.comp_apply, Algebra.TensorProduct.lift_tmul,
    AlgHom.id_apply, tensorEvalAlgHom_tmul]
  rfl

omit [Fintype Γ] in
private lemma evalAlgHom_comp_lift_id_antipode (g : Γ) :
    (evalAlgHom K Γ g).comp
        (Algebra.TensorProduct.lift (AlgHom.id K _) (antipodeAlgHom K Γ)
          (fun _ _ ↦ Commute.all _ _)) =
      tensorEvalAlgHom K Γ g g⁻¹ := by
  apply Algebra.TensorProduct.ext'
  intro x y
  simp only [AlgHom.comp_apply, Algebra.TensorProduct.lift_tmul,
    AlgHom.id_apply, tensorEvalAlgHom_tmul]
  rfl

noncomputable instance instHopfAlgebra : HopfAlgebra K (FiniteGroupFunctions K Γ) :=
  HopfAlgebra.ofAlgHom (antipodeAlgHom K Γ)
    (by
      ext f
      funext g
      calc
        _ = tensorEvalAlgHom K Γ g⁻¹ g (comulAlgHom K Γ f) :=
          DFunLike.congr_fun (evalAlgHom_comp_lift_antipode_id K Γ g)
            (comulAlgHom K Γ f)
        _ = f (g⁻¹ * g) := by simp
        _ = f 1 := by simp
        _ = _ := rfl)
    (by
      ext f
      funext g
      calc
        _ = tensorEvalAlgHom K Γ g g⁻¹ (comulAlgHom K Γ f) :=
          DFunLike.congr_fun (evalAlgHom_comp_lift_id_antipode K Γ g)
            (comulAlgHom K Γ f)
        _ = f (g * g⁻¹) := by simp
        _ = f 1 := by simp
        _ = _ := rfl)

/-- Evaluating the comultiplication at two group elements is evaluation at
their product. -/
@[simp]
lemma evalAlgHom_comp_comulAlgHom (g h : Γ) :
    (Algebra.TensorProduct.lift (evalAlgHom K Γ g) (evalAlgHom K Γ h)
      (fun _ _ ↦ Commute.all _ _)).comp
        (Bialgebra.comulAlgHom K (FiniteGroupFunctions K Γ)) =
      evalAlgHom K Γ (g * h) := by
  change (tensorEvalAlgHom K Γ g h).comp (comulAlgHom K Γ) =
    evalAlgHom K Γ (g * h)
  ext f
  exact tensorEvalAlgHom_comulAlgHom_apply K Γ f g h

end FiniteGroupFunctions

/-- The finite constant group scheme associated to an abstract finite group. -/
noncomputable abbrev finiteConstantGroupScheme (K Γ : Type u)
    [CommRing K] [Fintype Γ] [Group Γ] :
    CategoryTheory.Grp (CategoryTheory.Over (Spec (.of K))) :=
  ⟨(Spec (.of (FiniteGroupFunctions K Γ))).asOver (Spec (.of K))⟩

/-- The rational point of a finite constant group scheme labelled by an
element of the indexing group. -/
noncomputable def finiteConstantGroupSchemePoint (K Γ : Type u)
    [CommRing K] [Fintype Γ] [Group Γ] (g : Γ) :
    𝟙_ (Over (Spec (.of K))) ⟶ (finiteConstantGroupScheme K Γ).X :=
  Over.homMk
    (Spec.map (CommRingCat.ofHom (FiniteGroupFunctions.evalAlgHom K Γ g)))
    (by
      change Spec.map (CommRingCat.ofHom
          (FiniteGroupFunctions.evalAlgHom K Γ g).toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap K (FiniteGroupFunctions K Γ))) = 𝟙 _
      rw [← Spec.map_comp, Spec.map_eq_id]
      ext x
      rfl)

/-- Evaluation-labelled rational points multiply according to their abstract
group labels. -/
@[simp]
lemma finiteConstantGroupSchemePoint_mul (K Γ : Type u)
    [CommRing K] [Fintype Γ] [Group Γ] (g h : Γ) :
    finiteConstantGroupSchemePoint K Γ g * finiteConstantGroupSchemePoint K Γ h =
      finiteConstantGroupSchemePoint K Γ (g * h) := by
  rw [CategoryTheory.Hom.mul_def]
  ext
  dsimp only [finiteConstantGroupSchemePoint]
  simp only [Over.comp_left, Over.lift_left, mul_spec_asOver_spec_left]
  change pullback.lift
      (Spec.map (CommRingCat.ofHom
        (FiniteGroupFunctions.evalAlgHom K Γ g).toRingHom))
      (Spec.map (CommRingCat.ofHom
        (FiniteGroupFunctions.evalAlgHom K Γ h).toRingHom)) _ ≫
      (pullbackSpecIso K (FiniteGroupFunctions K Γ)
        (FiniteGroupFunctions K Γ)).hom ≫
      Spec.map (CommRingCat.ofHom
        (Bialgebra.comulAlgHom K (FiniteGroupFunctions K Γ)).toRingHom) =
    Spec.map (CommRingCat.ofHom
      (FiniteGroupFunctions.evalAlgHom K Γ (g * h)).toRingHom)
  let egh : FiniteGroupFunctions K Γ ⊗[K] FiniteGroupFunctions K Γ →ₐ[K] K :=
    Algebra.TensorProduct.lift
      (FiniteGroupFunctions.evalAlgHom K Γ g)
      (FiniteGroupFunctions.evalAlgHom K Γ h)
      (fun _ _ ↦ Commute.all _ _)
  have hw :
      Spec.map (CommRingCat.ofHom
          (FiniteGroupFunctions.evalAlgHom K Γ g).toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap K (FiniteGroupFunctions K Γ))) =
      Spec.map (CommRingCat.ofHom
          (FiniteGroupFunctions.evalAlgHom K Γ h).toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap K (FiniteGroupFunctions K Γ))) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
  have hPair :
      pullback.lift
          (Spec.map (CommRingCat.ofHom
            (FiniteGroupFunctions.evalAlgHom K Γ g).toRingHom))
          (Spec.map (CommRingCat.ofHom
            (FiniteGroupFunctions.evalAlgHom K Γ h).toRingHom)) hw ≫
        (pullbackSpecIso K (FiniteGroupFunctions K Γ)
          (FiniteGroupFunctions K Γ)).hom =
      Spec.map (CommRingCat.ofHom egh.toRingHom) := by
    rw [← cancel_mono (pullbackSpecIso K (FiniteGroupFunctions K Γ)
      (FiniteGroupFunctions K Γ)).inv]
    apply pullback.hom_ext
    · simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      rw [pullback.lift_fst, pullbackSpecIso_inv_fst, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp]
      congr 1
      ext x
      exact (DFunLike.congr_fun
        (Algebra.TensorProduct.lift_comp_includeLeft
          (FiniteGroupFunctions.evalAlgHom K Γ g)
          (FiniteGroupFunctions.evalAlgHom K Γ h)
          (fun _ _ ↦ Commute.all _ _)) x).symm
    · simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      rw [pullback.lift_snd, pullbackSpecIso_inv_snd, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp]
      congr 1
      ext x
      exact (DFunLike.congr_fun
        (Algebra.TensorProduct.lift_comp_includeRight'
          (FiniteGroupFunctions.evalAlgHom K Γ g)
          (FiniteGroupFunctions.evalAlgHom K Γ h)
          (fun _ _ ↦ Commute.all _ _)) x).symm
  rw [← Category.assoc, hPair, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  exact congrArg CommRingCat.ofHom <| congrArg AlgHom.toRingHom
    (FiniteGroupFunctions.evalAlgHom_comp_comulAlgHom K Γ g h)

/-- Abstract group elements map multiplicatively to rational points of the
corresponding finite constant group scheme. -/
noncomputable def finiteConstantGroupSchemePointHom (K Γ : Type u)
    [CommRing K] [Fintype Γ] [Group Γ] :
    Γ →* (𝟙_ (Over (Spec (.of K))) ⟶ (finiteConstantGroupScheme K Γ).X) where
  toFun := finiteConstantGroupSchemePoint K Γ
  map_one' := by
    apply mul_left_cancel (a := finiteConstantGroupSchemePoint K Γ 1)
    simpa only [_root_.one_mul, _root_.mul_one] using
      finiteConstantGroupSchemePoint_mul K Γ 1 1
  map_mul' := fun g h ↦ (finiteConstantGroupSchemePoint_mul K Γ g h).symm

/-- The underlying scheme of a finite constant group scheme is the finite
coproduct of copies of the base affine scheme indexed by the group. -/
noncomputable def finiteConstantSigmaIso (K Γ : Type u)
    [CommRing K] [Fintype Γ] [Group Γ] :
    (∐ fun _ : Γ ↦ Spec (.of K)) ≅ (finiteConstantGroupScheme K Γ).X.left := by
  letI : Finite Γ := Fintype.finite (inferInstance : Fintype Γ)
  exact CategoryTheory.asIso (sigmaSpec (fun _ : Γ ↦ .of K)) ≪≫
    Scheme.Spec.mapIso
      (FiniteGroupFunctions.toPiAlgEquiv K Γ).toRingEquiv.toCommRingCatIso.symm.op

/-- Under the coproduct description of a finite constant group scheme, the
inclusion of the summand labelled by `g` is its evaluation-labelled rational
point. -/
@[reassoc (attr := simp)]
lemma finiteConstantSigmaIso_hom_ι (K Γ : Type u)
    [CommRing K] [Fintype Γ] [Group Γ] (g : Γ) :
    Sigma.ι (fun _ : Γ ↦ Spec (.of K)) g ≫ (finiteConstantSigmaIso K Γ).hom =
      (finiteConstantGroupSchemePoint K Γ g).left := by
  change Sigma.ι _ g ≫ (sigmaSpec _ ≫ _) = Spec.map _
  rw [← Category.assoc, ι_sigmaSpec]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

instance finiteConstantGroupScheme_isAffine (K Γ : Type u)
    [CommRing K] [Fintype Γ] [Group Γ] :
    IsAffine (finiteConstantGroupScheme K Γ).X.left := by
  change IsAffine (Spec (.of (FiniteGroupFunctions K Γ)))
  infer_instance

instance finiteConstantGroupScheme_isFinite (K Γ : Type u)
    [CommRing K] [Fintype Γ] [Group Γ] :
    IsFinite (finiteConstantGroupScheme K Γ).X.hom := by
  change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap K (FiniteGroupFunctions K Γ))))
  rw [IsFinite.SpecMap_iff]
  change (algebraMap K (FiniteGroupFunctions K Γ)).Finite
  rw [RingHom.finite_algebraMap]
  infer_instance

instance finiteConstantGroupScheme_isReduced (K Γ : Type u)
    [CommRing K] [Fintype Γ] [Group Γ] [_root_.IsReduced K] :
    AlgebraicGeometry.IsReduced (finiteConstantGroupScheme K Γ).X.left := by
  change AlgebraicGeometry.IsReduced (Spec (.of (FiniteGroupFunctions K Γ)))
  rw [affine_isReduced_iff]
  infer_instance

end AlgebraicGeometry
