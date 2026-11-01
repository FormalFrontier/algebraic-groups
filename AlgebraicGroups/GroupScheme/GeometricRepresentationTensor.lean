/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.GeometricRepresentationSubgroup
public import Mathlib.RepresentationTheory.Basic

/-!
# Tensor products of geometric representations

Geometric representations of the same group scheme over a commutative ring have
a tensor product. Its point operators are the tensor products of the two given
operators, transported along Mathlib's scalar-extension equivalence
`TensorProduct.AlgebraTensorModule.distribBaseChange`. The construction is natural
for every coefficient-algebra map, without affineness or finiteness assumptions.

For a group-scheme morphism `i : N ⟶ G`, tensoring the inclusions of the two
subgroup-invariant submodules gives `GeometricRepresentation.tensorInvariantsMap`
into the invariants of the tensor representation. Its pure-tensor formula and
inclusion square describe the underlying linear map. Invariants are tested over
all coefficient algebras; neither injectivity nor surjectivity of this map is
asserted.

## References

* Mathlib's tensor representations, automorphism conjugation, scalar-extension
  tensor equivalence, tensor maps of submodule inclusions and codomain restriction.
* The geometric point operators, coefficient naturality and all-algebra invariants
  in this library.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct CategoryTheory.GrpObj

attribute [local instance] CategoryTheory.Hom.monoid CategoryTheory.Hom.group

universe u v w

namespace AlgebraicGeometry.GeometricRepresentation

variable {K : Type u} [CommRing K] {G : Scheme.{u}}
  [G.Over (Spec (.of K))] [GrpObj (G.asOver (Spec (.of K)))]
  {V : Type v} [AddCommGroup V] [Module K V]
  {W : Type w} [AddCommGroup W] [Module K W]

private def tensorPointHom
    (ρ : GeometricRepresentation (K := K) G V)
    (σ : GeometricRepresentation (K := K) G W)
    (R : CommAlgCat.{u, u} K) :
    ((Spec (.of R)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))) →*
      LinearMap.GeneralLinearGroup R (R ⊗[K] (V ⊗[K] W)) :=
  (LinearMap.GeneralLinearGroup.congrLinearEquiv
      (TensorProduct.AlgebraTensorModule.distribBaseChange K R V W).symm).toMonoidHom.comp
    (Representation.asGroupHom
      (Representation.tprod
        ((Units.coeHom _).comp (ρ.operator R))
        ((Units.coeHom _).comp (σ.operator R))))

private theorem tensorPointHom_val
    (ρ : GeometricRepresentation (K := K) G V)
    (σ : GeometricRepresentation (K := K) G W)
    (R : CommAlgCat.{u, u} K)
    (g : (Spec (.of R)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K)))
    (z : R ⊗[K] (V ⊗[K] W)) :
    (tensorPointHom ρ σ R g).val z =
      (TensorProduct.AlgebraTensorModule.distribBaseChange K R V W).symm
        (TensorProduct.map (ρ.operator R g).val (σ.operator R g).val
          (TensorProduct.AlgebraTensorModule.distribBaseChange K R V W z)) := by
  change (TensorProduct.AlgebraTensorModule.distribBaseChange K R V W).symm
      ((Representation.asGroupHom
        (Representation.tprod
          ((Units.coeHom _).comp (ρ.operator R))
          ((Units.coeHom _).comp (σ.operator R))) g).val
        (TensorProduct.AlgebraTensorModule.distribBaseChange K R V W z)) = _
  simp only [Representation.asGroupHom_apply, Representation.tprod_apply,
    MonoidHom.comp_apply, Units.coeHom_apply]

-- The inverse comparison is compatible with a given coefficient map on all
-- pairs of tensors, including sums that arise as values of point operators.
private theorem coefficient_distribBaseChange_symm
    {R S : CommAlgCat.{u, u} K} (φ : R →ₐ[K] S)
    (x : R ⊗[K] V) (y : R ⊗[K] W) :
    TensorProduct.map φ.toLinearMap (LinearMap.id : V ⊗[K] W →ₗ[K] V ⊗[K] W)
        ((TensorProduct.AlgebraTensorModule.distribBaseChange K R V W).symm
          (x ⊗ₜ[R] y)) =
      (TensorProduct.AlgebraTensorModule.distribBaseChange K S V W).symm
        (TensorProduct.map φ.toLinearMap (LinearMap.id : V →ₗ[K] V) x ⊗ₜ[S]
          TensorProduct.map φ.toLinearMap (LinearMap.id : W →ₗ[K] W) y) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
      induction y using TensorProduct.inductionOn with
      | tmul b y =>
          simp only [TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul,
            TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply, map_mul]
      | add y z hy hz =>
          simp only [TensorProduct.tmul_add, map_add, hy, hz]
  | add x z hx hz =>
      simp only [TensorProduct.add_tmul, map_add, hx, hz]

private theorem tensorPointHom_naturality_apply
    (ρ : GeometricRepresentation (K := K) G V)
    (σ : GeometricRepresentation (K := K) G W)
    {R S : CommAlgCat.{u, u} K} (φ : R →ₐ[K] S)
    (g : (Spec (.of R)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K)))
    (z : R ⊗[K] (V ⊗[K] W)) :
    (tensorPointHom ρ σ S
        (((affineGeometricPointFunctor (K := K) G).map (CommAlgCat.ofHom φ)).hom g)).val
        (TensorProduct.map φ.toLinearMap
          (LinearMap.id : V ⊗[K] W →ₗ[K] V ⊗[K] W) z) =
      TensorProduct.map φ.toLinearMap
        (LinearMap.id : V ⊗[K] W →ₗ[K] V ⊗[K] W)
        ((tensorPointHom ρ σ R g).val z) := by
  -- Give the transported point its geometric hom type before rewriting actions.
  let gS : (Spec (.of S)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K)) :=
    ((affineGeometricPointFunctor (K := K) G).map (CommAlgCat.ofHom φ)).hom g
  change (tensorPointHom ρ σ S gS).val
      (TensorProduct.map φ.toLinearMap
        (LinearMap.id : V ⊗[K] W →ₗ[K] V ⊗[K] W) z) = _
  rw [tensorPointHom_val ρ σ S gS, tensorPointHom_val ρ σ R g]
  induction z using TensorProduct.inductionOn with
  | tmul a z =>
      induction z using TensorProduct.inductionOn with
      | tmul x y =>
          have hx := ρ.naturality_apply φ g (a ⊗ₜ[K] x)
          have hy := σ.naturality_apply φ g (1 ⊗ₜ[K] y)
          change (ρ.operator S gS).val
              (TensorProduct.map φ.toLinearMap (LinearMap.id : V →ₗ[K] V)
                (a ⊗ₜ[K] x)) = _ at hx
          change (σ.operator S gS).val
              (TensorProduct.map φ.toLinearMap (LinearMap.id : W →ₗ[K] W)
                (1 ⊗ₜ[K] y)) = _ at hy
          simp only [TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
            LinearMap.id_apply, map_one] at hx hy
          simp only [TensorProduct.map_tmul,
            AlgHom.toLinearMap_apply, LinearMap.id_apply,
            TensorProduct.AlgebraTensorModule.distribBaseChange_tmul]
          rw [coefficient_distribBaseChange_symm, hx, hy]
      | add x y hx hy =>
          simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem tensorPointHom_baseChange
    (ρ : GeometricRepresentation (K := K) G V)
    (σ : GeometricRepresentation (K := K) G W)
    {R S : CommAlgCat.{u, u} K} (φ : R →ₐ[K] S)
    (g : (Spec (.of R)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))) :
    generalLinearModuleBaseChange K (V ⊗[K] W) R S φ (tensorPointHom ρ σ R g) =
      tensorPointHom ρ σ S
        (((affineGeometricPointFunctor (K := K) G).map (CommAlgCat.ofHom φ)).hom g) := by
  apply Units.ext
  apply LinearMap.ext
  intro z
  -- Equality on the coefficient-map image alone would not suffice: the target
  -- coefficient algebra need not be generated by that image.
  induction z using TensorProduct.inductionOn with
  | tmul s x =>
      rw [generalLinearModuleBaseChange_tmul, LinearMap.rTensor_def,
        ← tensorPointHom_naturality_apply ρ σ φ g (1 ⊗ₜ[K] x)]
      rw [TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply,
        map_one, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The tensor product representation of a group scheme on the ordinary tensor
product of the two modules. Its operators are transported tensor products along
`TensorProduct.AlgebraTensorModule.distribBaseChange`. -/
noncomputable def tensor
    (ρ : GeometricRepresentation (K := K) G V)
    (σ : GeometricRepresentation (K := K) G W) :
    GeometricRepresentation (K := K) G (V ⊗[K] W) where
  app R := GrpCat.ofHom
    (((LinearMap.GeneralLinearGroup.congrLinearEquiv
        (TensorProduct.AlgebraTensorModule.distribBaseChange K R V W).symm).toMonoidHom.comp
      (Representation.asGroupHom
        (Representation.tprod
          ((Units.coeHom _).comp (ρ.operator R))
          ((Units.coeHom _).comp (σ.operator R))))).comp
      (MulEquiv.ulift :
        ULift.{max v w} ((Spec (.of R)).asOver (Spec (.of K)) ⟶
          G.asOver (Spec (.of K))) ≃*
            ((Spec (.of R)).asOver (Spec (.of K)) ⟶
              G.asOver (Spec (.of K)))).toMonoidHom)
  naturality {R S} f := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    rintro ⟨g⟩
    exact (tensorPointHom_baseChange ρ σ f.hom g).symm

/-- The scalar-extension comparison intertwines the tensor representation's
operator with the tensor product of the two given point operators. -/
theorem operator_tensor
    (ρ : GeometricRepresentation (K := K) G V)
    (σ : GeometricRepresentation (K := K) G W)
    (R : CommAlgCat.{u, u} K)
    (g : (Spec (.of R)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))) :
    (TensorProduct.AlgebraTensorModule.distribBaseChange K R V W).toLinearMap ∘ₗ
        ((tensor ρ σ).operator R g).val =
      TensorProduct.map (ρ.operator R g).val (σ.operator R g).val ∘ₗ
        (TensorProduct.AlgebraTensorModule.distribBaseChange K R V W).toLinearMap := by
  apply LinearMap.ext
  intro z
  change TensorProduct.AlgebraTensorModule.distribBaseChange K R V W
      ((tensorPointHom ρ σ R g).val z) = _
  rw [tensorPointHom_val]
  exact (TensorProduct.AlgebraTensorModule.distribBaseChange K R V W).apply_symm_apply _

variable {N : Scheme.{u}} [N.Over (Spec (.of K))]
  [GrpObj (N.asOver (Spec (.of K)))]

/-- The tensor of two subgroup-invariant vectors is invariant for the tensor
representation, with fixedness tested over every coefficient algebra. -/
theorem tmul_mem_invariants_tensor_comap
    (ρ : GeometricRepresentation (K := K) G V)
    (σ : GeometricRepresentation (K := K) G W)
    (i : N.asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K)))
    [IsMonHom i] {x : V} {y : W}
    (hx : x ∈ (ρ.comap i).invariants)
    (hy : y ∈ (σ.comap i).invariants) :
    x ⊗ₜ[K] y ∈ ((tensor ρ σ).comap i).invariants := by
  apply (mem_invariants_iff _ _).mpr
  intro R n
  rw [operator_comap]
  have hx' := ((ρ.comap i).mem_invariants_iff x).mp hx R n
  have hy' := ((σ.comap i).mem_invariants_iff y).mp hy R n
  rw [operator_comap] at hx' hy'
  apply (TensorProduct.AlgebraTensorModule.distribBaseChange K R V W).injective
  calc
    _ = TensorProduct.map (ρ.operator R (n ≫ i)).val (σ.operator R (n ≫ i)).val
        (TensorProduct.AlgebraTensorModule.distribBaseChange K R V W
          (1 ⊗ₜ[K] (x ⊗ₜ[K] y))) :=
      LinearMap.congr_fun (operator_tensor ρ σ R (n ≫ i)) _
    _ = _ := by
      simp only [TensorProduct.AlgebraTensorModule.distribBaseChange_tmul,
        TensorProduct.map_tmul, hx', hy']

/-- Tensoring the two subgroup-invariant subtype inclusions, with codomain
restricted to the invariants of the tensor representation. -/
noncomputable def tensorInvariantsMap
    (ρ : GeometricRepresentation (K := K) G V)
    (σ : GeometricRepresentation (K := K) G W)
    (i : N.asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K)))
    [IsMonHom i] :
    ((ρ.comap i).invariants ⊗[K] (σ.comap i).invariants) →ₗ[K]
      ((tensor ρ σ).comap i).invariants :=
  LinearMap.codRestrict _
    (TensorProduct.mapIncl (ρ.comap i).invariants (σ.comap i).invariants) (by
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul x y => exact tmul_mem_invariants_tensor_comap ρ σ i x.property y.property
      | add x y hx hy =>
          rw [map_add]
          exact Submodule.add_mem _ hx hy)

/-- On a pure tensor the invariant tensor map is the tensor of the two
underlying vectors. -/
@[simp] theorem coe_tensorInvariantsMap_tmul
    (ρ : GeometricRepresentation (K := K) G V)
    (σ : GeometricRepresentation (K := K) G W)
    (i : N.asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K)))
    [IsMonHom i]
    (x : (ρ.comap i).invariants) (y : (σ.comap i).invariants) :
    (tensorInvariantsMap ρ σ i (x ⊗ₜ[K] y) : V ⊗[K] W) =
      (x : V) ⊗ₜ[K] (y : W) := rfl

/-- The invariant tensor map commutes with the original target subtype
inclusion and the tensor map of the two input subtype inclusions. -/
@[simp] theorem subtype_comp_tensorInvariantsMap
    (ρ : GeometricRepresentation (K := K) G V)
    (σ : GeometricRepresentation (K := K) G W)
    (i : N.asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K)))
    [IsMonHom i] :
    ((tensor ρ σ).comap i).invariants.subtype ∘ₗ tensorInvariantsMap ρ σ i =
      TensorProduct.mapIncl (ρ.comap i).invariants (σ.comap i).invariants := by
  simp only [tensorInvariantsMap, LinearMap.subtype_comp_codRestrict]

end AlgebraicGeometry.GeometricRepresentation
