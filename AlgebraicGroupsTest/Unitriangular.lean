/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import TauCeti.Algebra.AlgebraicGroup.UpperUnitriangular.Scheme
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.SchemePoints

/-!
# Upper-unitriangular group-scheme clients

These examples import the producer modules normally. They check the actual
matrix product, functoriality, the closed inclusion, and empty, singleton,
and zero-ring cases without imposing a field or positive-rank assumption.
-/

@[expose] public section

open TauCeti.UpperUnitriangularGroup


noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

universe u

variable (K : Type) [CommRing K]

example (R : Type) [CommRing R] [Algebra K R]
    (s t : TauCeti.upperUnitriangularGroup (Fin 2) R) :
    ((TauCeti.UpperUnitriangular.pointsMulEquiv K (Fin 2) (A := R)).symm (s * t)).ofConv
      ((TauCeti.UpperUnitriangular.coordinateHopfAlgebraAlgEquiv K (Fin 2)
        (TauCeti.UpperUnitriangular.genericMatrix K (Fin 2) 0 1))) =
      s.1 0 1 + t.1 0 1 := by
  rw [TauCeti.UpperUnitriangular.pointsMulEquiv_symm_apply,
    TauCeti.UpperUnitriangular.genericMatrix_apply_of_lt K _ (by decide),
    TauCeti.UpperUnitriangular.upperUnitriangularToPoint_apply]
  change ((s.1 : Matrix (Fin 2) (Fin 2) R) * (t.1 : Matrix (Fin 2) (Fin 2) R)) 0 1 = _
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  simp [add_comm]

example (R : Type) [CommRing R] [Algebra K R]
    (s t : TauCeti.upperUnitriangularGroup (Fin 3) R) :
    ((TauCeti.UpperUnitriangular.pointsMulEquiv K (Fin 3) (A := R)).symm (s * t)).ofConv
      ((TauCeti.UpperUnitriangular.coordinateHopfAlgebraAlgEquiv K (Fin 3)
        (TauCeti.UpperUnitriangular.genericMatrix K (Fin 3) 0 2))) =
      s.1 0 2 + t.1 0 2 + s.1 0 1 * t.1 1 2 := by
  rw [TauCeti.UpperUnitriangular.pointsMulEquiv_symm_apply,
    TauCeti.UpperUnitriangular.genericMatrix_apply_of_lt K _ (by decide),
    TauCeti.UpperUnitriangular.upperUnitriangularToPoint_apply]
  change ((s.1 : Matrix (Fin 3) (Fin 3) R) * (t.1 : Matrix (Fin 3) (Fin 3) R)) 0 2 = _
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  simp
  ring

example (R S : Type) [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    (v : R →ₐ[K] S) (s : TauCeti.upperUnitriangularGroup (Fin 2) R) :
    (map v.toRingHom s).1 0 1 = v (s.1 0 1) := by
  exact map_apply v.toRingHom s 0 1

example (n : Type) [Fintype n] [LinearOrder n]
    (R S : Type) [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    (v : R →ₐ[K] S) (s : TauCeti.upperUnitriangularGroup n R) :
    (TauCeti.UpperUnitriangular.upperUnitriangularToPoint K n (A := S) (map v.toRingHom s)).ofConv =
      v.comp ((TauCeti.UpperUnitriangular.upperUnitriangularToPoint K n (A := R) s).ofConv) :=
by
  simpa only [TauCeti.UpperUnitriangular.pointsMulEquiv_symm_apply,
    AlgHom.mapValue_apply, WithConv.ofConv_toConv] using
      (congrArg WithConv.ofConv
        (TauCeti.UpperUnitriangular.mapValue_pointsMulEquiv_symm_apply K n v s)).symm

example (n : Type) [Fintype n] [LinearOrder n]
    (R S : Type) [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    (v : R →ₐ[K] S) (f : (TauCeti.UpperUnitriangular.coordinateHopfAlgebra K n) →ₐ[K] R) :
    (TauCeti.UpperUnitriangular.pointToUpperUnitriangular K n (A := S) (WithConv.toConv
      (v.comp f))) =
      map v.toRingHom ((TauCeti.UpperUnitriangular.pointToUpperUnitriangular K n (A := R)
        (WithConv.toConv f))) :=
by
  simpa only [AlgHom.mapValue_apply, WithConv.ofConv_toConv] using
    TauCeti.UpperUnitriangular.pointToUpperUnitriangular_mapValue K n v (WithConv.toConv f)

example (n : ℕ) (R : Type) [CommRing R] [Algebra K R]
    (s : TauCeti.upperUnitriangularGroup (Fin n) R) :
    TauCeti.GeneralLinear.schemePointsMulEquiv n R
      ((TauCeti.UpperUnitriangular.schemePointsMulEquiv (R := K) (A := R) (Fin n)).symm s ≫
        (TauCeti.UpperUnitriangular.inclusion K n).hom.hom) = s.1 := by
  rw [TauCeti.UpperUnitriangular.schemePointsMulEquiv_comp_inclusion,
    MulEquiv.apply_symm_apply]

example (R : Type) [CommRing R] (s : TauCeti.upperUnitriangularGroup (Fin 0) R) : s = 1 := by
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  exact Fin.elim0 i

example (R : Type) [CommRing R] (s : TauCeti.upperUnitriangularGroup (Fin 1) R) : s = 1 := by
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst i
  subst j
  simp

example : TauCeti.UpperUnitriangular.coordinateHopfAlgebraAlgEquiv (ZMod 1) (Fin 0)
    (Ring.inverse (TauCeti.UpperUnitriangular.genericMatrix (ZMod 1) (Fin 0)).det) = 1 := by
  rw [(TauCeti.UpperUnitriangular.isUpperUnitriangular_genericMatrix (ZMod 1) (Fin 0)).det_eq_one,
    Ring.inverse_one, map_one]

example : Algebra.FiniteType (ZMod 1)
    ((TauCeti.UpperUnitriangular.coordinateHopfAlgebra (ZMod 1) (Fin 1))) := inferInstance
