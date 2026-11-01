/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.GeometricRepresentationInvariants
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import SchemeProperties.FinitePresentation.PointDescent

/-!
# Finite-type tests for geometric representations

For a group scheme locally of finite presentation over `Spec K`, fixedness under
all coefficient algebras can be tested on finite-type algebras. The representation
is given on the whole geometric point functor, and the invariant submodule is the
existing `GeometricRepresentation.invariants`.

* `GeometricRepresentation.mem_invariants_iff_forall_finiteType` tests a vector
  using finite-type `K`-algebras.
* `GeometricRepresentation.forall_fixed_iff_forall_finiteType` tests an arbitrary
  tensor over a current algebra `R` using further maps of finite type over `R`.
  Here finiteness refers to the given map, not to finite type over `K`.

## Implementation notes

The base is any commutative ring, and the module has an independent universe.
The tested group scheme need not be affine. Point descent to a finitely generated
subalgebra and forward naturality suffice: no tensor injectivity, flatness,
finite-dimensionality or fixedness assumption on the initial tensor is used.
The scalar-extension image criterion over a field is separate from these comparisons.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 4.31, for invariants
  formulated with finitely generated test algebras over a field. The comparisons
  here hold over a commutative ring under local finite presentation.
* SchemeProperties' point-descent theorem
  `Scheme.exists_algSpec_map_subalgebra_val_comp_eq_of_locallyOfFinitePresentation`,
  for descent of points to finitely generated subalgebras.
* Mathlib's scalar towers, finite-type ring maps and tensor-map composition.
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct CategoryTheory.GrpObj

universe u v

namespace AlgebraicGeometry.GeometricRepresentation

variable {K : Type u} [CommRing K] {X : Scheme.{u}}
  [X.Over (Spec (.of K))] [GrpObj (X.asOver (Spec (.of K)))]
  {V : Type v} [AddCommGroup V] [Module K V]

/-- Push a fixedness equality forward along a coefficient map and its point map. -/
private theorem fixed_map (η : GeometricRepresentation (K := K) X V)
    {R S : CommAlgCat.{u, u} K} (φ : R →ₐ[K] S)
    (nR : (Spec (.of R)).asOver (Spec (.of K)) ⟶ X.asOver (Spec (.of K)))
    {nS : (Spec (.of S)).asOver (Spec (.of K)) ⟶ X.asOver (Spec (.of K))}
    (hn : (algSpec (.of K)).map (CommAlgCat.ofHom φ).op ≫ nR = nS)
    (w : R ⊗[K] V) (hw : (η.operator R nR).val w = w) :
    (η.operator S nS).val
        (TensorProduct.map φ.toLinearMap (LinearMap.id : V →ₗ[K] V) w) =
      TensorProduct.map φ.toLinearMap (LinearMap.id : V →ₗ[K] V) w := by
  have hpoint :
      (((affineGeometricPointFunctor (K := K) X).map (CommAlgCat.ofHom φ)).hom nR) =
        nS := hn
  have h := η.naturality_apply φ nR w
  rw [hpoint, hw] at h
  exact h

/-- For a group scheme locally of finite presentation, membership in the invariant
submodule is equivalent to fixedness on finite-type `K`-algebras. This comparison
extends the finitely generated test formulation over a field in Milne,
*Algebraic Groups* (2017), Proposition 4.31, to a commutative base ring. -/
theorem mem_invariants_iff_forall_finiteType
    (η : GeometricRepresentation (K := K) X V)
    [LocallyOfFinitePresentation (X ↘ Spec (.of K))] (x : V) :
    x ∈ η.invariants ↔
      ∀ (S : CommAlgCat.{u, u} K), Algebra.FiniteType K S →
        ∀ (n : (Spec (.of S)).asOver (Spec (.of K)) ⟶
          X.asOver (Spec (.of K))),
          (η.operator S n).val (1 ⊗ₜ[K] x) = 1 ⊗ₜ[K] x := by
  constructor
  · intro hx S _ n
    exact (η.mem_invariants_iff x).mp hx S n
  · intro hx
    apply (η.mem_invariants_iff x).mpr
    intro S n
    obtain ⟨A, hA, nA, hnA⟩ :=
      Scheme.exists_algSpec_map_subalgebra_val_comp_eq_of_locallyOfFinitePresentation
        (R := K) K X n
    have hfixed := fixed_map η (R := CommAlgCat.of K A) (S := S)
      (A.val.restrictScalars K) nA hnA (1 ⊗ₜ[K] x)
      (hx (CommAlgCat.of K A) ((Subalgebra.fg_iff_finiteType A).mp hA) nA)
    simpa only [TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
      LinearMap.id_apply, map_one] using hfixed

/-- For a group scheme locally of finite presentation, fixedness of an arbitrary
scalar tensor after all further coefficient maps is equivalent to fixedness after
all finite-type further maps. The finiteness predicate is attached to each given
map `φ`, and the current algebra `R` need not be finite type over `K`.
This is the further-test comparison underlying Milne, *Algebraic Groups* (2017),
Proposition 4.31, generalized here to a commutative base ring. -/
theorem forall_fixed_iff_forall_finiteType
    (η : GeometricRepresentation (K := K) X V)
    [LocallyOfFinitePresentation (X ↘ Spec (.of K))]
    (R : CommAlgCat.{u, u} K) (w : R ⊗[K] V) :
    (∀ (S : CommAlgCat.{u, u} K) (φ : R →ₐ[K] S)
      (n : (Spec (.of S)).asOver (Spec (.of K)) ⟶
        X.asOver (Spec (.of K))),
      (η.operator S n).val
          (TensorProduct.map φ.toLinearMap (LinearMap.id : V →ₗ[K] V) w) =
        TensorProduct.map φ.toLinearMap (LinearMap.id : V →ₗ[K] V) w) ↔
    (∀ (S : CommAlgCat.{u, u} K) (φ : R →ₐ[K] S),
      φ.toRingHom.FiniteType →
        ∀ (n : (Spec (.of S)).asOver (Spec (.of K)) ⟶
          X.asOver (Spec (.of K))),
          (η.operator S n).val
              (TensorProduct.map φ.toLinearMap (LinearMap.id : V →ₗ[K] V) w) =
            TensorProduct.map φ.toLinearMap (LinearMap.id : V →ₗ[K] V) w) := by
  constructor
  · intro hw S φ _ n
    exact hw S φ n
  · intro hw S φ n
    -- Install only the action induced by this map, retaining both original K-actions.
    let : Algebra R S := φ.toRingHom.toAlgebra
    let : IsScalarTower K R S := IsScalarTower.of_algHom φ
    obtain ⟨A, hA, nA, hnA⟩ :=
      Scheme.exists_algSpec_map_subalgebra_val_comp_eq_of_locallyOfFinitePresentation
        (R := R) K X n
    let φA : R →ₐ[K] A := IsScalarTower.toAlgHom K R A
    let jA : A →ₐ[K] S := A.val.restrictScalars K
    have hcomp : jA.comp φA = φ := by
      ext r
      change (algebraMap R A r : S) = φ r
      rw [Subalgebra.coe_algebraMap]
      rfl
    have hφA : φA.toRingHom.FiniteType := by
      change (algebraMap R A).FiniteType
      exact RingHom.finiteType_algebraMap.mpr ((Subalgebra.fg_iff_finiteType A).mp hA)
    have hmap :
        TensorProduct.map jA.toLinearMap (LinearMap.id : V →ₗ[K] V)
            (TensorProduct.map φA.toLinearMap (LinearMap.id : V →ₗ[K] V) w) =
          TensorProduct.map φ.toLinearMap (LinearMap.id : V →ₗ[K] V) w := by
      rw [TensorProduct.map_map, ← AlgHom.comp_toLinearMap, hcomp, LinearMap.id_comp]
    have hfixed := fixed_map η (R := CommAlgCat.of K A) (S := S) jA nA hnA
      (TensorProduct.map φA.toLinearMap (LinearMap.id : V →ₗ[K] V) w)
      (hw (CommAlgCat.of K A) φA hφA nA)
    simpa only [hmap] using hfixed

end AlgebraicGeometry.GeometricRepresentation
