/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.Unitriangular

/-!
# Upper-unitriangular group-scheme clients

These examples import the producer modules normally. They check the actual
matrix product, functoriality, the closed inclusion, and empty, singleton,
and zero-ring cases without imposing a field or positive-rank assumption.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry UnitriangularCoordinateRing
open scoped CategoryTheory.MonObj

universe u

variable (K : Type) [CommRing K]

example (R : Type) [CommRing R] [Algebra K R]
    (s t : Matrix.UnitriangularGroup (Fin 2) R) :
    (unitriangularGroupMulEquivAlgHom K (Fin 2) R (s * t)).ofConv
      (quotient K (Fin 2) (GeneralLinearCoordinateRing.matrix K (Fin 2) 0 1)) =
      s.1 0 1 + t.1 0 1 := by
  rw [unitriangularGroupMulEquivAlgHom_entry]
  change ((s.1 : Matrix (Fin 2) (Fin 2) R) * (t.1 : Matrix (Fin 2) (Fin 2) R)) 0 1 = _
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  simp [s.2.2 0, t.2.2 1, add_comm]

example (R : Type) [CommRing R] [Algebra K R]
    (s t : Matrix.UnitriangularGroup (Fin 3) R) :
    (unitriangularGroupMulEquivAlgHom K (Fin 3) R (s * t)).ofConv
      (quotient K (Fin 3) (GeneralLinearCoordinateRing.matrix K (Fin 3) 0 2)) =
      s.1 0 2 + t.1 0 2 + s.1 0 1 * t.1 1 2 := by
  rw [unitriangularGroupMulEquivAlgHom_entry]
  change ((s.1 : Matrix (Fin 3) (Fin 3) R) * (t.1 : Matrix (Fin 3) (Fin 3) R)) 0 2 = _
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  simp [s.2.2 0, t.2.2 2]
  ring

example (R S : Type) [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    (v : R →ₐ[K] S) (s : Matrix.UnitriangularGroup (Fin 2) R) :
    (Matrix.UnitriangularGroup.map v.toRingHom s).1 0 1 = v (s.1 0 1) := by
  exact Matrix.UnitriangularGroup.map_apply v.toRingHom s 0 1

example (n : Type) [Fintype n] [LinearOrder n]
    (R S : Type) [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    (v : R →ₐ[K] S) (s : Matrix.UnitriangularGroup n R) :
    unitriangularFromGL K n S (Matrix.UnitriangularGroup.map v.toRingHom s) =
      v.comp (unitriangularFromGL K n R s) :=
  unitriangularFromGL_natural K n R v s

example (n : Type) [Fintype n] [LinearOrder n]
    (R S : Type) [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    (v : R →ₐ[K] S) (f : UnitriangularCoordinateRing.CoordinateRing K n →ₐ[K] R) :
    unitriangularToGL K n S (v.comp f) =
      Matrix.UnitriangularGroup.map v.toRingHom (unitriangularToGL K n R f) :=
  unitriangularToGL_natural K n R v f

example (n : Type) [Fintype n] [LinearOrder n]
    (R : Type) [CommRing R] [Algebra K R]
    (s : Matrix.UnitriangularGroup n R) :
    unitriangularGroupMulEquivPoints K n R s ≫ (unitriangularInclusion K n).hom.hom =
      generalLinearGroupMulEquivPoints K n R s.1 :=
  unitriangularInclusion_point K n R s

example (R : Type) [CommRing R] (s : Matrix.UnitriangularGroup (Fin 0) R) : s = 1 := by
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  exact Fin.elim0 i

example (R : Type) [CommRing R] (s : Matrix.UnitriangularGroup (Fin 1) R) : s = 1 := by
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst i
  subst j
  simpa using s.2.2 0

example : quotient (ZMod 1) (Fin 0)
    (GeneralLinearCoordinateRing.detInverse (ZMod 1) (Fin 0)) = 1 :=
  quotient_detInverse (ZMod 1) (Fin 0)

example : Algebra.FiniteType (ZMod 1)
    (UnitriangularCoordinateRing.CoordinateRing (ZMod 1) (Fin 1)) := inferInstance
