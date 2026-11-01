/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.AffineRepresentation

/-!
# Invariants of geometric representations

The invariants of a geometric representation on `V` form a submodule of `V`:
a vector is invariant if its image `1 ⊗ v` is fixed by every scheme point over
every coefficient algebra. This is an intersection of linear kernels and does
not require the group scheme to be affine or the module to be finite-dimensional.

`GeometricRepresentation.mem_invariants_iff` characterizes this submodule.
`GeometricRepresentation.apply_subtype_baseChange_invariants` shows that every
point fixes the image of its scalar-extended subtype inclusion.
An equivariant linear map induces `GeometricRepresentation.invariantsMap` between
the original invariant subtypes. Its underlying map and scalar-extended inclusion
squares retain the given linear map, and it preserves identities and composition.

## Implementation notes

The test algebras range over all objects of `CommAlgCat.{u, u} K`, with no
finite-generation restriction. The module universes are independent of `u` and
of each other. The constructions, fixedness results and induced maps require only
a commutative base ring; the equivariant linear maps need not be invertible.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 4, Proposition 4.31,
  for invariants and further scalar extension over a field.
* Mathlib's submodule intersections, linear kernels, restrictions of linear maps
  and tensor products.
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct CategoryTheory.GrpObj

universe u v w z

namespace AlgebraicGeometry
namespace GeometricRepresentation

variable {K : Type u} [CommRing K] {G : Scheme.{u}}
  [G.Over (Spec (.of K))] [GrpObj (G.asOver (Spec (.of K)))]
  {V : Type v} [AddCommGroup V] [Module K V]

/-- The submodule of vectors whose images `1 ⊗ v` are fixed by all scheme points
over all coefficient algebras. No finite-generation restriction is imposed on
the coefficient algebras. -/
noncomputable def invariants (η : GeometricRepresentation (K := K) G V) : Submodule K V :=
  ⨅ (S : CommAlgCat.{u, u} K)
    (g : (Spec (.of S)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))),
    LinearMap.ker
      (((η.operator S g).val.restrictScalars K - LinearMap.id).comp
        (TensorProduct.mk K S V (1 : S)))

/-- A vector is invariant if and only if every scheme point fixes its image
after every coefficient extension. -/
@[simp] theorem mem_invariants_iff (η : GeometricRepresentation (K := K) G V) (v : V) :
    v ∈ η.invariants ↔
      ∀ (S : CommAlgCat.{u, u} K)
        (g : (Spec (.of S)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))),
        (η.operator S g).val (1 ⊗ₜ[K] v) = 1 ⊗ₜ[K] v := by
  simp only [invariants, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply,
    LinearMap.sub_apply, LinearMap.restrictScalars_apply, LinearMap.id_apply,
    TensorProduct.mk_apply, sub_eq_zero]

/-- Every point fixes a pure tensor with an invariant second factor. -/
theorem apply_tmul_of_mem_invariants (η : GeometricRepresentation (K := K) G V)
    {v : V} (hv : v ∈ η.invariants) (S : CommAlgCat.{u, u} K)
    (g : (Spec (.of S)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))) (s : S) :
    (η.operator S g).val (s ⊗ₜ[K] v) = s ⊗ₜ[K] v := by
  calc
    (η.operator S g).val (s ⊗ₜ[K] v) =
        (η.operator S g).val (s • (1 ⊗ₜ[K] v)) :=
      congrArg _ (TensorProduct.tmul_eq_smul_one_tmul s v)
    _ = s • (η.operator S g).val (1 ⊗ₜ[K] v) := map_smul _ _ _
    _ = s • (1 ⊗ₜ[K] v) :=
      congrArg (s • ·) ((η.mem_invariants_iff v).mp hv S g)
    _ = s ⊗ₜ[K] v := (TensorProduct.tmul_eq_smul_one_tmul s v).symm

/-- Every point fixes the image of the scalar-extended inclusion of the
invariant submodule. -/
theorem apply_subtype_baseChange_invariants (η : GeometricRepresentation (K := K) G V)
    (S : CommAlgCat.{u, u} K)
    (g : (Spec (.of S)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K)))
    (z : S ⊗[K] η.invariants) :
    (η.operator S g).val (η.invariants.subtype.baseChange S z) =
      η.invariants.subtype.baseChange S z := by
  induction z using TensorProduct.inductionOn with
  | tmul s v =>
    simpa only [LinearMap.baseChange_tmul, Submodule.subtype_apply] using
      η.apply_tmul_of_mem_invariants v.property S g s
  | add x y hx hy => simp only [map_add, hx, hy]

section Maps

variable {X : Scheme.{u}} [X.Over (Spec (.of K))]
  [GrpObj (X.asOver (Spec (.of K)))]
  {W : Type w} [AddCommGroup W] [Module K W]
  {Z : Type z} [AddCommGroup Z] [Module K Z]

/-- An equivariant linear map preserves all-algebra geometric invariants. -/
theorem map_mem_invariants
    (ρ : GeometricRepresentation (K := K) X V)
    (σ : GeometricRepresentation (K := K) X W)
    (f : V →ₗ[K] W)
    (hf : ∀ (R : CommAlgCat.{u, u} K)
      (g : (Spec (.of R)).asOver (Spec (.of K)) ⟶
        X.asOver (Spec (.of K))),
      f.baseChange R ∘ₗ (ρ.operator R g).val =
        (σ.operator R g).val ∘ₗ f.baseChange R)
    {x : V} (hx : x ∈ ρ.invariants) :
    f x ∈ σ.invariants := by
  apply (σ.mem_invariants_iff (f x)).mpr
  intro R g
  simpa only [LinearMap.comp_apply, (ρ.mem_invariants_iff x).mp hx R g,
    LinearMap.baseChange_tmul] using
    (LinearMap.congr_fun (hf R g) (1 ⊗ₜ[K] x)).symm

/-- The restriction of an equivariant linear map to the original
all-algebra invariant subtypes. -/
noncomputable def invariantsMap
    (ρ : GeometricRepresentation (K := K) X V)
    (σ : GeometricRepresentation (K := K) X W)
    (f : V →ₗ[K] W)
    (hf : ∀ (R : CommAlgCat.{u, u} K)
      (g : (Spec (.of R)).asOver (Spec (.of K)) ⟶
        X.asOver (Spec (.of K))),
      f.baseChange R ∘ₗ (ρ.operator R g).val =
        (σ.operator R g).val ∘ₗ f.baseChange R) :
    ρ.invariants →ₗ[K] σ.invariants :=
  f.restrict (p := ρ.invariants) (q := σ.invariants)
    (fun x hx => map_mem_invariants ρ σ f hf (x := x) hx)

/-- The restricted map retains the given underlying linear map. -/
@[simp] theorem coe_invariantsMap_apply
    (ρ : GeometricRepresentation (K := K) X V)
    (σ : GeometricRepresentation (K := K) X W)
    (f : V →ₗ[K] W)
    (hf : ∀ (R : CommAlgCat.{u, u} K)
      (g : (Spec (.of R)).asOver (Spec (.of K)) ⟶
        X.asOver (Spec (.of K))),
      f.baseChange R ∘ₗ (ρ.operator R g).val =
        (σ.operator R g).val ∘ₗ f.baseChange R)
    (x : ρ.invariants) :
    (invariantsMap ρ σ f hf x : W) = f (x : V) :=
  LinearMap.coe_restrict_apply (fun x hx => map_mem_invariants ρ σ f hf (x := x) hx) x

/-- The original subtype inclusions characterize the restricted map. -/
@[simp] theorem subtype_comp_invariantsMap
    (ρ : GeometricRepresentation (K := K) X V)
    (σ : GeometricRepresentation (K := K) X W)
    (f : V →ₗ[K] W)
    (hf : ∀ (R : CommAlgCat.{u, u} K)
      (g : (Spec (.of R)).asOver (Spec (.of K)) ⟶
        X.asOver (Spec (.of K))),
      f.baseChange R ∘ₗ (ρ.operator R g).val =
        (σ.operator R g).val ∘ₗ f.baseChange R) :
    σ.invariants.subtype ∘ₗ invariantsMap ρ σ f hf =
      f ∘ₗ ρ.invariants.subtype :=
  LinearMap.subtype_comp_restrict (fun x hx => map_mem_invariants ρ σ f hf (x := x) hx)

/-- Scalar extension of the original inclusion square, on the unchanged
scalar tensors of the original invariant subtypes. -/
theorem subtype_baseChange_comp_invariantsMap
    (ρ : GeometricRepresentation (K := K) X V)
    (σ : GeometricRepresentation (K := K) X W)
    (f : V →ₗ[K] W)
    (hf : ∀ (R : CommAlgCat.{u, u} K)
      (g : (Spec (.of R)).asOver (Spec (.of K)) ⟶
        X.asOver (Spec (.of K))),
      f.baseChange R ∘ₗ (ρ.operator R g).val =
        (σ.operator R g).val ∘ₗ f.baseChange R)
    (R : CommAlgCat.{u, u} K) :
    σ.invariants.subtype.baseChange R ∘ₗ
        (invariantsMap ρ σ f hf).baseChange R =
      f.baseChange R ∘ₗ ρ.invariants.subtype.baseChange R := by
  simpa only [LinearMap.baseChange_comp] using
    congrArg (fun F : ρ.invariants →ₗ[K] W => F.baseChange R)
      (subtype_comp_invariantsMap ρ σ f hf)

/-- Invariants preserve the identity linear map. -/
@[simp] theorem invariantsMap_id
    (ρ : GeometricRepresentation (K := K) X V) :
    invariantsMap ρ ρ (LinearMap.id : V →ₗ[K] V)
        (fun R g => by simp) =
      (LinearMap.id : ρ.invariants →ₗ[K] ρ.invariants) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [coe_invariantsMap_apply, LinearMap.id_apply]

/-- Invariants preserve composition of the given ambient linear maps. -/
theorem invariantsMap_comp
    (ρ : GeometricRepresentation (K := K) X V)
    (σ : GeometricRepresentation (K := K) X W)
    (f : V →ₗ[K] W)
    (hf : ∀ (R : CommAlgCat.{u, u} K)
      (g : (Spec (.of R)).asOver (Spec (.of K)) ⟶
        X.asOver (Spec (.of K))),
      f.baseChange R ∘ₗ (ρ.operator R g).val =
        (σ.operator R g).val ∘ₗ f.baseChange R)
    (τ : GeometricRepresentation (K := K) X Z)
    (f₂ : W →ₗ[K] Z)
    (hf₂ : ∀ (R : CommAlgCat.{u, u} K)
      (g : (Spec (.of R)).asOver (Spec (.of K)) ⟶
        X.asOver (Spec (.of K))),
      f₂.baseChange R ∘ₗ (σ.operator R g).val =
        (τ.operator R g).val ∘ₗ f₂.baseChange R) :
    invariantsMap ρ τ (f₂ ∘ₗ f)
        (fun R g => by
          rw [LinearMap.baseChange_comp, LinearMap.comp_assoc, hf R g,
            ← LinearMap.comp_assoc, hf₂ R g, LinearMap.comp_assoc]) =
      invariantsMap σ τ f₂ hf₂ ∘ₗ invariantsMap ρ σ f hf :=
  LinearMap.restrict_comp
    (fun x hx => map_mem_invariants ρ σ f hf (x := x) hx)
    (fun x hx => map_mem_invariants σ τ f₂ hf₂ (x := x) hx)

end Maps

end GeometricRepresentation
end AlgebraicGeometry
