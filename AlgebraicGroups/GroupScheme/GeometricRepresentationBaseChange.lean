/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.GeometricRepresentationInvariants
public import AlgebraicGroups.Algebra.TensorProduct.Submodule
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Invariants under further scalar extension

For an original geometric representation, scalar extension of its invariant
submodule is characterized over a field by fixedness after every further algebra
in the original coefficient category. The group scheme need not be affine, and
the universe of its representation module is independent of the base field.

## Implementation notes

All coefficient algebras in the original category are tested. Comparison with
invariants tested only on the source's finitely generated algebras, and comparison
of the further-algebra conditions, are separate results not proved here.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 4.31, for the formulation
  using finitely generated test algebras. Comparison with the all-algebra
  formulation here is not established in this module.
* Mathlib's tensor maps, tensor identity equivalences and scalar-extension images.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v

namespace AlgebraicGeometry.GeometricRepresentation

section CoefficientContraction

variable {K : Type u} [CommRing K]
variable {R T : Type u} [CommRing R] [Algebra K R] [CommRing T] [Algebra K T]
variable {V : Type v} [AddCommGroup V] [Module K V]

/-- Contract the first coefficient factor without changing any algebra structure. -/
private def coefficientContraction (f : R →ₗ[K] K) :
    (R ⊗[K] T) ⊗[K] V →ₗ[K] T ⊗[K] V :=
  TensorProduct.map
    ((TensorProduct.lid K T).toLinearMap.comp
      (TensorProduct.map f (LinearMap.id : T →ₗ[K] T)))
    (LinearMap.id : V →ₗ[K] V)

private theorem coefficientContraction_tmul (f : R →ₗ[K] K)
    (r : R) (t : T) (v : V) :
    coefficientContraction f ((r ⊗ₜ[K] t) ⊗ₜ[K] v) = f r • (t ⊗ₜ[K] v) := by
  simp [coefficientContraction, TensorProduct.smul_tmul']

private theorem coefficientContraction_smul_map_includeRight
    (f : R →ₗ[K] K) (r : R) (y : T ⊗[K] V) :
    coefficientContraction f
        ((r ⊗ₜ[K] (1 : T)) •
          TensorProduct.map
            (Algebra.TensorProduct.includeRight : T →ₐ[K] R ⊗[K] T).toLinearMap
            (LinearMap.id : V →ₗ[K] V) y) =
      f r • y := by
  induction y using TensorProduct.inductionOn with
  | tmul t v =>
      simp [TensorProduct.smul_tmul', smul_eq_mul,
        Algebra.TensorProduct.tmul_mul_tmul, coefficientContraction_tmul]
  | add y z hy hz => simp only [map_add, smul_add, hy, hz]

private theorem coefficientContraction_map_includeLeft
    (f : R →ₗ[K] K) (w : R ⊗[K] V) :
    coefficientContraction (T := T) f
        (TensorProduct.map
          (Algebra.TensorProduct.includeLeft : R →ₐ[K] R ⊗[K] T).toLinearMap
          (LinearMap.id : V →ₗ[K] V) w) =
      (1 : T) ⊗ₜ[K]
        (TensorProduct.lid K V
          (TensorProduct.map f (LinearMap.id : V →ₗ[K] V) w)) := by
  induction w using TensorProduct.inductionOn with
  | tmul r v =>
      simp [coefficientContraction_tmul, TensorProduct.tmul_smul]
  | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, hx, hy]

/-- Naturality along the right coefficient map lets contraction commute with
an action linear over the tensor-product algebra. -/
private theorem coefficientContraction_apply
    (f : R →ₗ[K] K)
    (a : T ⊗[K] V →ₗ[T] T ⊗[K] V)
    (b : (R ⊗[K] T) ⊗[K] V →ₗ[R ⊗[K] T] (R ⊗[K] T) ⊗[K] V)
    (h : ∀ y : T ⊗[K] V,
      b (TensorProduct.map
        (Algebra.TensorProduct.includeRight : T →ₐ[K] R ⊗[K] T).toLinearMap
        (LinearMap.id : V →ₗ[K] V) y) =
      TensorProduct.map
        (Algebra.TensorProduct.includeRight : T →ₐ[K] R ⊗[K] T).toLinearMap
        (LinearMap.id : V →ₗ[K] V) (a y))
    (z : (R ⊗[K] T) ⊗[K] V) :
    coefficientContraction f (b z) = a (coefficientContraction f z) := by
  induction z using TensorProduct.inductionOn with
  | tmul s v =>
      induction s using TensorProduct.inductionOn with
      | tmul r t =>
          have ht : ((r ⊗ₜ[K] t) ⊗ₜ[K] v) =
              (r ⊗ₜ[K] (1 : T)) •
                TensorProduct.map
                  (Algebra.TensorProduct.includeRight : T →ₐ[K] R ⊗[K] T).toLinearMap
                  (LinearMap.id : V →ₗ[K] V) (t ⊗ₜ[K] v) := by
            simp [TensorProduct.smul_tmul', smul_eq_mul,
              Algebra.TensorProduct.tmul_mul_tmul]
          calc
            coefficientContraction f (b ((r ⊗ₜ[K] t) ⊗ₜ[K] v)) =
                coefficientContraction f
                  ((r ⊗ₜ[K] (1 : T)) •
                    TensorProduct.map
                      (Algebra.TensorProduct.includeRight : T →ₐ[K] R ⊗[K] T).toLinearMap
                      (LinearMap.id : V →ₗ[K] V) (a (t ⊗ₜ[K] v))) := by
                        rw [ht, map_smul, h]
            _ = f r • a (t ⊗ₜ[K] v) :=
              coefficientContraction_smul_map_includeRight f r _
            _ = a (f r • (t ⊗ₜ[K] v)) := (a.map_smul_of_tower _ _).symm
            _ = a (coefficientContraction f ((r ⊗ₜ[K] t) ⊗ₜ[K] v)) := by
              rw [coefficientContraction_tmul]
      | add s t hs ht =>
          simp only [TensorProduct.add_tmul, map_add, hs, ht]
  | add x y hx hy => simp only [map_add, hx, hy]

end CoefficientContraction

section FurtherExtension

open scoped CategoryTheory.GrpObj

variable {K : Type u} [CommRing K] {G : Scheme.{u}}
  [G.Over (Spec (.of K))] [GrpObj (G.asOver (Spec (.of K)))]
  {V : Type v} [AddCommGroup V] [Module K V]

/-- The scalar-extended invariant inclusion stays fixed after each specified
further algebra map. This implication needs only a commutative base ring. -/
theorem apply_map_of_mem_range_baseChange_invariants
    (η : GeometricRepresentation (K := K) G V)
    (R S : CommAlgCat.{u, u} K) (φ : R →ₐ[K] S)
    (g : (Spec (.of S)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K)))
    {w : R ⊗[K] V} (hw : w ∈ LinearMap.range (η.invariants.subtype.baseChange R)) :
    (η.operator S g).val
        (TensorProduct.map φ.toLinearMap (LinearMap.id : V →ₗ[K] V) w) =
      TensorProduct.map φ.toLinearMap (LinearMap.id : V →ₗ[K] V) w := by
  change w ∈ η.invariants.baseChange R at hw
  obtain ⟨z, hz⟩ := η.invariants.map_mem_baseChange φ.toLinearMap hw
  rw [← hz]
  exact η.apply_subtype_baseChange_invariants S g z

/-- Every linear contraction of a tensor fixed after all further coefficient
extensions belongs to the original invariant submodule. -/
theorem contraction_mem_invariants_of_forall_fixed
    (η : GeometricRepresentation (K := K) G V)
    (R : CommAlgCat.{u, u} K) (w : R ⊗[K] V)
    (hw : ∀ (S : CommAlgCat.{u, u} K) (φ : R →ₐ[K] S)
      (g : (Spec (.of S)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))),
      (η.operator S g).val
          (TensorProduct.map φ.toLinearMap (LinearMap.id : V →ₗ[K] V) w) =
        TensorProduct.map φ.toLinearMap (LinearMap.id : V →ₗ[K] V) w)
    (f : R →ₗ[K] K) :
    TensorProduct.lid K V
      (TensorProduct.map f (LinearMap.id : V →ₗ[K] V) w) ∈ η.invariants := by
  apply (η.mem_invariants_iff _).2
  intro T g
  let S : CommAlgCat.{u, u} K := CommAlgCat.of K (R ⊗[K] T)
  let φ : R →ₐ[K] S := Algebra.TensorProduct.includeLeft
  let ψ : T →ₐ[K] S := Algebra.TensorProduct.includeRight
  let g' : (Spec (.of S)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K)) :=
    ((affineGeometricPointFunctor (K := K) G).map (CommAlgCat.ofHom ψ)).hom g
  have hcomm := coefficientContraction_apply f
    (η.operator T g).val
    (η.operator S g').val
    (fun y => η.naturality_apply (R := T) (S := S) ψ g y)
    (TensorProduct.map φ.toLinearMap (LinearMap.id : V →ₗ[K] V) w)
  have hc := coefficientContraction_map_includeLeft (T := T) f w
  calc
    (η.operator T g).val
        ((1 : T) ⊗ₜ[K] TensorProduct.lid K V
          (TensorProduct.map f (LinearMap.id : V →ₗ[K] V) w)) =
      (η.operator T g).val
        (coefficientContraction f
          (TensorProduct.map φ.toLinearMap (LinearMap.id : V →ₗ[K] V) w)) :=
      congrArg (η.operator T g).val hc.symm
    _ = coefficientContraction f
        ((η.operator S g').val
          (TensorProduct.map φ.toLinearMap (LinearMap.id : V →ₗ[K] V) w)) :=
      hcomm.symm
    _ = coefficientContraction f
        (TensorProduct.map φ.toLinearMap (LinearMap.id : V →ₗ[K] V) w) :=
      congrArg (coefficientContraction (T := T) f) (hw S φ g')
    _ = (1 : T) ⊗ₜ[K] TensorProduct.lid K V
        (TensorProduct.map f (LinearMap.id : V →ₗ[K] V) w) := hc

end FurtherExtension

section Field

open scoped CategoryTheory.GrpObj

variable {K : Type u} [Field K] {G : Scheme.{u}}
  [G.Over (Spec (.of K))] [GrpObj (G.asOver (Spec (.of K)))]
  {V : Type v} [AddCommGroup V] [Module K V]

/-- A tensor belongs to the image of the original scalar-extended invariant
inclusion if and only if it is fixed after every original map to a further
coefficient algebra. The group scheme need not be affine and the universe and
dimension of its representation module are unrestricted. This is an all-algebra
variant of the criterion in Milne, *Algebraic Groups* (2017), Proposition 4.31.
Comparison with its finitely generated test-algebra formulation is a separate
statement, not asserted by this theorem. -/
theorem mem_range_baseChange_invariants_iff
    (η : GeometricRepresentation (K := K) G V)
    (R : CommAlgCat.{u, u} K) (w : R ⊗[K] V) :
    w ∈ LinearMap.range (η.invariants.subtype.baseChange R) ↔
      ∀ (S : CommAlgCat.{u, u} K) (φ : R →ₐ[K] S)
        (g : (Spec (.of S)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))),
        (η.operator S g).val
            (TensorProduct.map φ.toLinearMap (LinearMap.id : V →ₗ[K] V) w) =
          TensorProduct.map φ.toLinearMap (LinearMap.id : V →ₗ[K] V) w := by
  constructor
  · intro hw S φ g
    exact η.apply_map_of_mem_range_baseChange_invariants R S φ g hw
  · intro hw
    apply (η.invariants.mem_range_baseChange_subtype_iff w).2
    intro f
    exact η.contraction_mem_invariants_of_forall_fixed R w hw f

end Field

end AlgebraicGeometry.GeometricRepresentation
