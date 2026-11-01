/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.GeometricRepresentationSubgroup
public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.RingTheory.Flat.Basic

/-!
# The ambient representation on normal-subgroup invariants

For a geometric representation `ρ` over a field and a normal group-scheme
morphism `i`, `GeometricRepresentation.normalInvariantsRepresentation` is the
ambient representation on the original subtype `(ρ.comap i).invariants`.
Its scalar-extended subtype inclusion intertwines the original operators, and
this equation uniquely determines the representation as a natural transformation.
The original subgroup acts trivially on it.

At each coefficient algebra, the construction restricts the original action to
the scalar-extended invariant image using Mathlib's `Subrepresentation`. The
canonical flat base-change equivalence transports that action back to the
original tensor of the invariant subtype. Coefficient naturality is proved for
the existing general linear functor, including noninjective coefficient maps.

## Limitations

Neither group scheme is required to be affine, and the module universe is
independent of the field universe. Test algebras are all objects of the original
`CommAlgCat.{u, u} K`. No quotient action, comparison with finitely generated
testers, comparison of further-algebra tests, or source-coverage assertion is
made.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 4, for normal-subgroup
  invariants. The finitely generated tester comparison is not established here.
* Mathlib's `Subrepresentation.toRepresentation`, `Representation.asGroupHom`,
  `Submodule.toBaseChange.toLinearEquiv` and general linear group conjugation.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct CategoryTheory.GrpObj

universe u v

namespace AlgebraicGeometry.GeometricRepresentation

attribute [local instance] CategoryTheory.Hom.monoid CategoryTheory.Hom.group

variable {K : Type u} [Field K] {G N : Scheme.{u}}
  [G.Over (Spec (.of K))] [N.Over (Spec (.of K))]
  [GrpObj (G.asOver (Spec (.of K)))] [GrpObj (N.asOver (Spec (.of K)))]
  {V : Type v} [AddCommGroup V] [Module K V]

private theorem normalInvariants_inclusion_injective
    (ρ : GeometricRepresentation (K := K) G V)
    (i : N.asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))) [IsMonHom.Normal i]
    (R : CommAlgCat.{u, u} K) :
    Function.Injective ((ρ.comap i).invariants.subtype.baseChange R) := by
  exact Module.Flat.lTensor_preserves_injective_linearMap
    (M := R) (ρ.comap i).invariants.subtype Subtype.val_injective

/-- The scalar-extended invariant inclusion commutes with every original
coefficient map. The coefficient map need not be injective. -/
private theorem normalInvariants_subtype_baseChange_map
    (ρ : GeometricRepresentation (K := K) G V)
    (i : N.asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))) [IsMonHom.Normal i]
    {R S : CommAlgCat.{u, u} K} (φ : R →ₐ[K] S)
    (x : R ⊗[K] (ρ.comap i).invariants) :
    (ρ.comap i).invariants.subtype.baseChange S
        (TensorProduct.map φ.toLinearMap
          (LinearMap.id : (ρ.comap i).invariants →ₗ[K] (ρ.comap i).invariants) x) =
      TensorProduct.map φ.toLinearMap (LinearMap.id : V →ₗ[K] V)
        ((ρ.comap i).invariants.subtype.baseChange R x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r x => simp only [TensorProduct.map_tmul, LinearMap.id_apply,
      LinearMap.baseChange_tmul, AlgHom.toLinearMap_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The ambient point homomorphism on the original scalar tensor of the
normal-subgroup invariant subtype. It is obtained by stock restriction to the
base-change image and transport along the inverse canonical image equivalence. -/
def normalInvariantOperator (ρ : GeometricRepresentation (K := K) G V)
    (i : N.asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))) [IsMonHom.Normal i]
    (R : CommAlgCat.{u, u} K) :
    ((Spec (.of R)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))) →*
      LinearMap.GeneralLinearGroup R (R ⊗[K] (ρ.comap i).invariants) := by
  let U := (ρ.comap i).invariants
  -- Keep the restriction local: an exposed definition cannot use a private definition.
  let P : Subrepresentation
      ((Units.coeHom (Module.End R (R ⊗[K] V))).comp (ρ.operator R)) :=
    { toSubmodule := U.baseChange R
      apply_mem_toSubmodule g _ hw :=
        ρ.operator_mem_range_baseChange_comap_invariants i R g hw }
  let e : R ⊗[K] U ≃ₗ[R] U.baseChange R :=
    Submodule.toBaseChange.toLinearEquiv R U
  -- The restricted action is on the image, so transport back along `e.symm`.
  exact (LinearMap.GeneralLinearGroup.congrLinearEquiv e.symm).toMonoidHom.comp
    P.toRepresentation.asGroupHom

/-- The canonical operator is characterized on the original scalar-extended
subtype inclusion, not merely on an isomorphic image carrier. -/
theorem normalInvariantOperator_apply
    (ρ : GeometricRepresentation (K := K) G V)
    (i : N.asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))) [IsMonHom.Normal i]
    (R : CommAlgCat.{u, u} K)
    (g : (Spec (.of R)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K)))
    (x : R ⊗[K] (ρ.comap i).invariants) :
    (ρ.comap i).invariants.subtype.baseChange R
        ((ρ.normalInvariantOperator i R g).val x) =
      (ρ.operator R g).val ((ρ.comap i).invariants.subtype.baseChange R x) := by
  let U := (ρ.comap i).invariants
  let P : Subrepresentation
      ((Units.coeHom (Module.End R (R ⊗[K] V))).comp (ρ.operator R)) :=
    { toSubmodule := U.baseChange R
      apply_mem_toSubmodule g _ hw :=
        ρ.operator_mem_range_baseChange_comap_invariants i R g hw }
  let e : R ⊗[K] U ≃ₗ[R] U.baseChange R :=
    Submodule.toBaseChange.toLinearEquiv R U
  unfold normalInvariantOperator
  change U.subtype.baseChange R
      ((LinearMap.GeneralLinearGroup.congrLinearEquiv e.symm
        (P.toRepresentation.asGroupHom g)).val x) =
    (ρ.operator R g).val (U.subtype.baseChange R x)
  rw [LinearMap.GeneralLinearGroup.congrLinearEquiv_apply]
  change ((e (e.symm (P.toRepresentation g (e x)))) : R ⊗[K] V) =
    (P.toRepresentation g (e x) : R ⊗[K] V)
  exact congrArg (fun y : U.baseChange R => (y : R ⊗[K] V))
    (e.apply_symm_apply (P.toRepresentation g (e x)))

private theorem normalInvariantOperator_naturality_apply
    (ρ : GeometricRepresentation (K := K) G V)
    (i : N.asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))) [IsMonHom.Normal i]
    {R S : CommAlgCat.{u, u} K} (φ : R →ₐ[K] S)
    (g : (Spec (.of R)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K)))
    (x : R ⊗[K] (ρ.comap i).invariants) :
    (ρ.normalInvariantOperator i S
        (((affineGeometricPointFunctor (K := K) G).map (CommAlgCat.ofHom φ)).hom g)).val
        (TensorProduct.map φ.toLinearMap
          (LinearMap.id : (ρ.comap i).invariants →ₗ[K] (ρ.comap i).invariants) x) =
      TensorProduct.map φ.toLinearMap
        (LinearMap.id : (ρ.comap i).invariants →ₗ[K] (ρ.comap i).invariants)
        ((ρ.normalInvariantOperator i R g).val x) := by
  apply normalInvariants_inclusion_injective ρ i S
  calc
    _ = (ρ.operator S
        (((affineGeometricPointFunctor (K := K) G).map (CommAlgCat.ofHom φ)).hom g)).val
        ((ρ.comap i).invariants.subtype.baseChange S
          (TensorProduct.map φ.toLinearMap
            (LinearMap.id : (ρ.comap i).invariants →ₗ[K] (ρ.comap i).invariants) x)) :=
      ρ.normalInvariantOperator_apply i S _ _
    _ = TensorProduct.map φ.toLinearMap (LinearMap.id : V →ₗ[K] V)
        ((ρ.operator R g).val ((ρ.comap i).invariants.subtype.baseChange R x)) := by
      rw [normalInvariants_subtype_baseChange_map, ρ.naturality_apply]
    _ = _ := by
      rw [normalInvariants_subtype_baseChange_map, normalInvariantOperator_apply]

/-- The canonical invariant operators commute with the existing general linear
scalar-extension map. Pure tensors generate the target even when the coefficient
map is noninjective or its target is the zero algebra. -/
theorem normalInvariantOperator_baseChange
    (ρ : GeometricRepresentation (K := K) G V)
    (i : N.asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))) [IsMonHom.Normal i]
    {R S : CommAlgCat.{u, u} K} (φ : R →ₐ[K] S)
    (g : (Spec (.of R)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))) :
    generalLinearModuleBaseChange K (ρ.comap i).invariants R S φ
        (ρ.normalInvariantOperator i R g) =
      ρ.normalInvariantOperator i S
        (((affineGeometricPointFunctor (K := K) G).map (CommAlgCat.ofHom φ)).hom g) := by
  apply Units.ext
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul s x =>
    calc
      (generalLinearModuleBaseChange K (ρ.comap i).invariants R S φ
          (ρ.normalInvariantOperator i R g)).val (s ⊗ₜ[K] x) =
          s • TensorProduct.map φ.toLinearMap
            (LinearMap.id : (ρ.comap i).invariants →ₗ[K] (ρ.comap i).invariants)
            ((ρ.normalInvariantOperator i R g).val (1 ⊗ₜ[K] x)) := by
        rw [generalLinearModuleBaseChange_tmul, LinearMap.rTensor_def]
      _ = s • (ρ.normalInvariantOperator i S
          (((affineGeometricPointFunctor (K := K) G).map (CommAlgCat.ofHom φ)).hom g)).val
          (1 ⊗ₜ[K] x) := by
        rw [← ρ.normalInvariantOperator_naturality_apply i φ g (1 ⊗ₜ[K] x)]
        simp only [TensorProduct.map_tmul, LinearMap.id_apply,
          AlgHom.toLinearMap_apply, map_one]
      _ = (ρ.normalInvariantOperator i S
          (((affineGeometricPointFunctor (K := K) G).map (CommAlgCat.ofHom φ)).hom g)).val
          (s ⊗ₜ[K] x) := by
        rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The ambient geometric representation on the exact inherited subtype of
all-algebra invariants of a given normal subgroup. Its components act on the
original scalar tensors, and no stability or flatness input is required. -/
def normalInvariantsRepresentation (ρ : GeometricRepresentation (K := K) G V)
    (i : N.asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))) [IsMonHom.Normal i] :
    GeometricRepresentation (K := K) G (ρ.comap i).invariants where
  app R := GrpCat.ofHom ((ρ.normalInvariantOperator i R).comp
    (MulEquiv.ulift :
      ULift.{v} ((Spec (.of R)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))) ≃*
        ((Spec (.of R)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K)))).toMonoidHom)
  naturality {R S} φ := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    rintro ⟨g⟩
    exact (ρ.normalInvariantOperator_baseChange i φ.hom g).symm

/-- The geometric component is the canonical point homomorphism on the original
tensor of the invariant subtype. -/
@[simp] theorem operator_normalInvariantsRepresentation
    (ρ : GeometricRepresentation (K := K) G V)
    (i : N.asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))) [IsMonHom.Normal i]
    (R : CommAlgCat.{u, u} K)
    (g : (Spec (.of R)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))) :
    (ρ.normalInvariantsRepresentation i).operator R g =
      ρ.normalInvariantOperator i R g := rfl

/-- The original scalar-extended subtype inclusion intertwines the invariant
representation with the given ambient representation on every tensor. -/
theorem normalInvariantsRepresentation_operator_apply
    (ρ : GeometricRepresentation (K := K) G V)
    (i : N.asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))) [IsMonHom.Normal i]
    (R : CommAlgCat.{u, u} K)
    (g : (Spec (.of R)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K)))
    (x : R ⊗[K] (ρ.comap i).invariants) :
    (ρ.comap i).invariants.subtype.baseChange R
        (((ρ.normalInvariantsRepresentation i).operator R g).val x) =
      (ρ.operator R g).val ((ρ.comap i).invariants.subtype.baseChange R x) :=
  ρ.normalInvariantOperator_apply i R g x

/-- The inclusion intertwining equation as equality of linear maps on the
unchanged scalar tensors. -/
theorem normalInvariantsRepresentation_intertwines
    (ρ : GeometricRepresentation (K := K) G V)
    (i : N.asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))) [IsMonHom.Normal i]
    (R : CommAlgCat.{u, u} K)
    (g : (Spec (.of R)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))) :
    (ρ.comap i).invariants.subtype.baseChange R ∘ₗ
        ((ρ.normalInvariantsRepresentation i).operator R g).val =
      (ρ.operator R g).val ∘ₗ (ρ.comap i).invariants.subtype.baseChange R := by
  apply LinearMap.ext
  intro x
  exact ρ.normalInvariantsRepresentation_operator_apply i R g x

/-- The unchanged inclusion equation uniquely determines the invariant
representation as a value of the original natural-transformation type. -/
theorem normalInvariantsRepresentation_unique
    (ρ : GeometricRepresentation (K := K) G V)
    (i : N.asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))) [IsMonHom.Normal i]
    (θ : GeometricRepresentation (K := K) G (ρ.comap i).invariants)
    (hθ : ∀ (R : CommAlgCat.{u, u} K)
      (g : (Spec (.of R)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K)))
      (x : R ⊗[K] (ρ.comap i).invariants),
      (ρ.comap i).invariants.subtype.baseChange R ((θ.operator R g).val x) =
        (ρ.operator R g).val ((ρ.comap i).invariants.subtype.baseChange R x)) :
    θ = ρ.normalInvariantsRepresentation i := by
  apply GeometricRepresentation.ext
  intro R g
  apply Units.ext
  apply LinearMap.ext
  intro x
  apply normalInvariants_inclusion_injective ρ i R
  rw [hθ, normalInvariantsRepresentation_operator_apply]

/-- The original normal subgroup acts trivially on its invariant subtype.
This follows from invariant fixedness, not from triviality of the ambient action. -/
theorem normalInvariantsRepresentation_comap_operator
    (ρ : GeometricRepresentation (K := K) G V)
    (i : N.asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))) [IsMonHom.Normal i]
    (R : CommAlgCat.{u, u} K)
    (n : (Spec (.of R)).asOver (Spec (.of K)) ⟶ N.asOver (Spec (.of K))) :
    ((ρ.normalInvariantsRepresentation i).comap i).operator R n = 1 := by
  rw [operator_comap]
  apply Units.ext
  apply LinearMap.ext
  intro x
  apply normalInvariants_inclusion_injective ρ i R
  change (ρ.comap i).invariants.subtype.baseChange R
      (((ρ.normalInvariantsRepresentation i).operator R (n ≫ i)).val x) =
    (ρ.comap i).invariants.subtype.baseChange R x
  rw [normalInvariantsRepresentation_operator_apply]
  simpa only [operator_comap] using
    (ρ.comap i).apply_subtype_baseChange_invariants R n x

end AlgebraicGeometry.GeometricRepresentation
