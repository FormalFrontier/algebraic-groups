/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.HopfAlgebra.Frobenius
public import AlgebraicGroups.Algebra.HopfAlgebra.Pure
public import AlgebraicGroups.Algebra.HopfAlgebra.TensorQuotient
public import CoherentModules.RingTheory.Flat.Pure
public import CoherentModules.RingTheory.Flat.FaithfullyFlat
public import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-!
# Faithful flatness for finite-dimensional Hopf sources

An injective full bialgebra map from a finite-dimensional commutative Hopf algebra
into an arbitrary commutative Hopf algebra is faithfully flat. All base-field
structures are the parents of the given Hopf structures.

Self-injectivity of the source splits the map as a source-linear map. Tensor-unit
purity and the first-target-factor tensor-quotient equivalence give flatness by
pure descent. The surjective linear retraction then gives faithful flatness.

## References

* J. S. Milne, *Algebraic Groups*, Theorem 3.31. The argument here uses
  finite-dimensional self-injectivity rather than the nil-augmentation-ideal
  argument; it imposes no nilpotence assumption.
-/

@[expose] public section

universe u v w

open scoped TensorProduct

/-- An injective full bialgebra map with finite-dimensional commutative Hopf source
is faithfully flat as its underlying ring homomorphism. The target need not be
finite-dimensional or finitely generated. The proof uses source self-injectivity,
tensor-unit purity, and the first-target-factor tensor-quotient equivalence. -/
theorem BialgHom.faithfullyFlat_of_injective_of_finite
    {K : Type u} [Field K]
    {D : Type v} [CommRing D] [HopfAlgebra K D]
    {E : Type w} [CommRing E] [HopfAlgebra K E]
    [Module.Finite K D]
    (f : @BialgHom K D E _ _ _ _ _
      (inferInstance : CoalgebraStruct K D)
      (inferInstance : CoalgebraStruct K E))
    (hf : Function.Injective f) :
    (f.toAlgHom : D →+* E).FaithfullyFlat := by
  classical
  let : Algebra D E := (f.toAlgHom : D →+* E).toAlgebra
  have hmap : algebraMap D E = (f.toAlgHom : D →+* E) :=
    RingHom.algebraMap_toAlgebra (f.toAlgHom : D →+* E)
  let : IsScalarTower K D E :=
    IsScalarTower.of_algebraMap_eq (R := K) (S := D) (A := E) (fun k => by
      rw [hmap]
      exact (f.toAlgHom.commutes k).symm)
  have hg : IsScalarTower.toAlgHom K D E = f.toAlgHom := by
    ext d
    exact congrArg (fun g : D →+* E => g d) hmap
  have hcounit :
      (Bialgebra.counitAlgHom K E).comp (IsScalarTower.toAlgHom K D E) =
        Bialgebra.counitAlgHom K D := by
    rw [hg]
    ext d
    exact CoalgHomClass.counit_comp_apply f d
  have hcomul :
      (Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom K D E)
        (IsScalarTower.toAlgHom K D E)).comp (Bialgebra.comulAlgHom K D) =
          (Bialgebra.comulAlgHom K E).comp (IsScalarTower.toAlgHom K D E) := by
    rw [hg]
    ext d
    exact CoalgHomClass.map_comp_comul_apply f d
  have hinj : Function.Injective (algebraMap D E) := by
    rw [hmap]
    exact hf
  let : Module.Injective D D := HopfAlgebra.injective_self K D
  obtain ⟨r, hr⟩ := Module.Injective.extension_property D D D E
    (Algebra.linearMap D E) hinj (LinearMap.id : D →ₗ[D] D)
  have hsplit (d : D) : r (algebraMap D E d) = d := by
    have h := congrArg (fun g : D →ₗ[D] D => g d) hr
    simpa only [LinearMap.comp_apply, Algebra.linearMap_apply,
      LinearMap.id_apply] using h
  have hrone : r (1 : E) = 1 := by
    simpa only [map_one] using hsplit (1 : D)
  have hrsurj : Function.Surjective r := by
    intro d
    refine ⟨d • (1 : E), ?_⟩
    calc
      r (d • (1 : E)) = d • r (1 : E) := r.map_smul d (1 : E)
      _ = d := by
        rw [hrone]
        exact mul_one d
  have hunit (N : Type (max v w)) [AddCommMonoid N] [Module D N] :
      Function.Injective (TensorProduct.mk D E N 1) :=
    HopfAlgebra.tensorProduct_mk_one_injective K D E hinj N
  let Q := E ⧸ (RingHom.ker (Bialgebra.counitAlgHom K D : D →+* K)).map
    (algebraMap D E)
  let : Module.Flat K Q := inferInstance
  let : Module.Flat E (E ⊗[K] Q) := inferInstance
  let shear := HopfAlgebra.tensorQuotientAlgEquiv K D E hcounit hcomul
  let : Module.Flat E (E ⊗[D] E) :=
    Module.Flat.of_linearEquiv shear.toLinearEquiv
  let : Module.Flat D E :=
    Module.Flat.of_flat_tensorProduct_of_injective D E E hunit
  let : Module.FaithfullyFlat D E :=
    Module.FaithfullyFlat.of_surjective r hrsurj
  have hff : (algebraMap D E).FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
  simpa only [hmap] using hff
