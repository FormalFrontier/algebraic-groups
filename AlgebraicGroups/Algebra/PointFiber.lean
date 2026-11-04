/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Point fibers of finite algebra towers

For an algebra tower `R → C → A` and an `R`-algebra point `C → R`, the quotient
by the extended kernel has its inherited `C` action factor through the point
and the original `R` action. Thus a finite `C`-module has a finite point fiber
over `R`, even when the point does not extend to `A`.

The top algebra may be noncommutative: centrality of the scalar map makes the
extended kernel two-sided.

An ambient augmentation separately supplies nontriviality of its fiber over a
nontrivial base ring. No module-finiteness assumption is needed for that fact.
-/

@[expose] public section

universe u v w

/-- An ideal extended along the scalar map of an algebra is two-sided. -/
theorem Ideal.isTwoSided_map_algebraMap
    {C : Type v} {A : Type w} [CommSemiring C] [Semiring A] [Algebra C A]
    (I : Ideal C) : (I.map (algebraMap C A)).IsTwoSided := by
  constructor
  intro a b ha
  change a ∈ Submodule.span A ((algebraMap C A) '' (I : Set C)) at ha
  induction ha using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨c, hc, rfl⟩
      rw [Algebra.commutes c b]
      exact Ideal.mul_mem_left _ b (Ideal.mem_map_of_mem (algebraMap C A) hc)
  | zero =>
      simpa only [zero_mul] using (I.map (algebraMap C A)).zero_mem
  | add x y hx hy ihx ihy =>
      rw [add_mul]
      exact (I.map (algebraMap C A)).add_mem ihx ihy
  | smul r x hx ih =>
      simpa only [smul_eq_mul, mul_assoc] using
        (I.map (algebraMap C A)).mul_mem_left r ih

-- Centrality gives the quotient its ring and algebra structures.
attribute [local instance] Ideal.isTwoSided_map_algebraMap

namespace Algebra

variable {R : Type u} {C : Type v} {A : Type w}
variable [CommRing R] [CommRing C] [Ring A]
variable [Algebra R C] [Algebra R A] [Algebra C A] [IsScalarTower R C A]

section Point

variable (φ : C →ₐ[R] R)

local notation "Iφ" =>
  Ideal.map (algebraMap C A) (RingHom.ker (AlgHom.toRingHom φ))

/-- On a point fiber, the inherited middle-ring map factors through the point
and the original base-ring map. -/
theorem pointFiber_algebraMap_apply (c : C) :
    algebraMap C (A ⧸ Iφ) c = algebraMap R (A ⧸ Iφ) (φ c) := by
  change Ideal.Quotient.mk Iφ (algebraMap C A c) =
    Ideal.Quotient.mk Iφ (algebraMap R A (φ c))
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2
  have hc : c - algebraMap R C (φ c) ∈ RingHom.ker φ.toRingHom := by
    apply (RingHom.sub_mem_ker_iff φ.toRingHom).2
    simp
  rw [IsScalarTower.algebraMap_apply R C A (φ c)]
  simpa only [map_sub] using (Ideal.mem_map_of_mem (algebraMap C A) hc)

/-- The fiber of a module-finite algebra tower at an arbitrary base-valued point
is finite over the original base ring. The point need not extend to the top algebra. -/
theorem finite_pointFiber [Module.Finite C A] :
    Module.Finite R (A ⧸ Iφ) := by
  -- Keep the inherited quotient algebras while adding only the point action on R.
  let originalRQuotient : Algebra R (A ⧸ Iφ) := inferInstance
  let originalCQuotient : Algebra C (A ⧸ Iφ) := inferInstance
  have haction (c : C) :
      algebraMap C (A ⧸ Iφ) c = algebraMap R (A ⧸ Iφ) (φ c) :=
    pointFiber_algebraMap_apply (R := R) (C := C) (A := A) φ c
  have : Module.Finite C (A ⧸ Iφ) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ C Iφ).toLinearMap
      (Ideal.Quotient.mkₐ_surjective C Iφ)
  let : Algebra C R := φ.toRingHom.toAlgebra
  have : IsScalarTower C R (A ⧸ Iφ) :=
    IsScalarTower.of_algebraMap_eq fun c => by
      change algebraMap C (A ⧸ Iφ) c = algebraMap R (A ⧸ Iφ) (φ c)
      exact haction c
  exact Module.Finite.of_restrictScalars_finite C R (A ⧸ Iφ)

end Point

section Augmentation

variable (ε : A →ₐ[R] R)

local notation "Iε" =>
  Ideal.map (algebraMap C A)
    (RingHom.ker (AlgHom.toRingHom
      (AlgHom.comp ε (IsScalarTower.toAlgHom R C A))))

/-- An ambient augmentation makes its point fiber nontrivial over a nontrivial
base ring, independently of any finiteness assumption. -/
theorem nontrivial_augmentationFiber [Nontrivial R] :
    Nontrivial (A ⧸ Iε) := by
  have hI : Iε ≤ RingHom.ker ε.toRingHom := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro c hc
    change ε (algebraMap C A c) = 0 at hc ⊢
    exact hc
  exact (Ideal.Quotient.lift Iε ε.toRingHom (fun a ha => hI ha)).domain_nontrivial

end Augmentation

end Algebra

namespace Subalgebra

variable {R : Type u} {A : Type w} [CommRing R] [CommRing A] [Algebra R A]
variable (C : Subalgebra R A) (ε : A →ₐ[R] R)

local notation "Iε" =>
  Ideal.map (AlgHom.toRingHom (Subalgebra.val C))
    (RingHom.ker (AlgHom.toRingHom (AlgHom.comp ε (Subalgebra.val C))))

/-- The inherited subalgebra action on the augmentation quotient factors through
the restricted augmentation and the original base-ring action. -/
theorem augmentationQuotient_algebraMap_apply (c : C) :
    algebraMap C (A ⧸ Iε) c =
      algebraMap R (A ⧸ Iε) ((ε.comp C.val) c) := by
  exact Algebra.pointFiber_algebraMap_apply (R := R) (C := C) (A := A)
    (ε.comp C.val) c

/-- A module-finite extension of a subalgebra has a finite augmentation
quotient over the original base ring. -/
theorem finite_augmentationQuotient [Module.Finite C A] :
    Module.Finite R (A ⧸ Iε) := by
  exact Algebra.finite_pointFiber (R := R) (C := C) (A := A) (ε.comp C.val)

/-- An augmentation quotient of a subalgebra is nontrivial over a
nontrivial base ring, without a finiteness assumption. -/
theorem nontrivial_augmentationQuotient [Nontrivial R] :
    Nontrivial (A ⧸ Iε) := by
  exact Algebra.nontrivial_augmentationFiber (R := R) (C := C) (A := A) ε

end Subalgebra
