/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.RightComodule
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Module.NatInt
import Mathlib.RingTheory.Flat.Basic

/-!
# Kernels of specified right-comodule morphisms

Over a commutative ring, flatness of the coacting coalgebra makes a
morphism's ordinary linear kernel stable. Its subtype coaction and
factorization property come from `RightComodule.Subcomodule.ofIsStable`
and `RightComodule.Subcomodule.existsUnique_factorization`.

The kernel lift has the ordinary `LinearMap.codRestrict` as its underlying
map. The generic subcomodule factorization supplies only colinearity.
The argument uses Mathlib's exactness of tensoring by a flat module and
its exact kernel-subtype sequence. The given additive-monoid and module
parents are retained, with additive groups derived inside the stability proof.
Neither ambient module is assumed flat, and all universes are independent.

## References

This construction reuses the subtype-coaction and factorization formalization in
`AlgebraicGroups.Algebra.Coalgebra.RightComodule`, and Mathlib's linear kernel,
exactness and flatness APIs. The bibliographic background for right comodules
is recorded in that module.
-/

@[expose] public section

namespace Coalgebra.RightComoduleHom

universe uR uC uM uN uP

variable {R : Type uR} {C : Type uC} {M : Type uM} {N : Type uN}
variable [CommRing R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
variable [Module.Flat R C]
variable {X : RightComodule R C M} {Y : RightComodule R C N}

private theorem isStable_ker (f : RightComoduleHom X Y) :
    X.IsStable (LinearMap.ker f.toLinearMap) := by
  let : AddCommGroup C := Module.addCommMonoidToAddCommGroup R
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup R
  let : AddCommGroup N := Module.addCommMonoidToAddCommGroup R
  have hexact := Module.Flat.rTensor_exact C
    (LinearMap.exact_subtype_ker_map f.toLinearMap)
  intro m hm
  rw [← LinearMap.exact_iff.mp hexact]
  apply LinearMap.mem_ker.mpr
  calc
    f.toLinearMap.rTensor C (X.coaction m) = Y.coaction (f m) :=
      (f.colinear_apply m).symm
    _ = 0 := by rw [show f m = 0 from LinearMap.mem_ker.mp hm, map_zero]

/-- The linear kernel with its induced right coaction. Flatness of the coacting
coalgebra makes the linear kernel stable and determines its subtype coaction. -/
noncomputable def ker (f : RightComoduleHom X Y) : X.Subcomodule :=
  RightComodule.Subcomodule.ofIsStable X (LinearMap.ker f.toLinearMap)
    (private_decl% (isStable_ker f))

/-- The underlying submodule of the comodule kernel is the linear kernel. -/
@[simp] theorem ker_toSubmodule (f : RightComoduleHom X Y) :
    (ker f).toSubmodule = LinearMap.ker f.toLinearMap := rfl

/-- Membership in the comodule kernel is equivalent to vanishing under the morphism. -/
@[simp] theorem mem_ker (f : RightComoduleHom X Y) (m : M) :
    m ∈ ker f ↔ f m = 0 := LinearMap.mem_ker

/-- The given morphism vanishes on the kernel inclusion. -/
@[simp] theorem apply_ker_subtype (f : RightComoduleHom X Y)
    (k : LinearMap.ker f.toLinearMap) : f (k : M) = 0 :=
  (mem_ker f (k : M)).mp k.property

/-- The underlying linear composite with the kernel inclusion is zero. -/
theorem comp_ker_subtype (f : RightComoduleHom X Y) :
    f.toLinearMap ∘ₗ (ker f).subtype.toLinearMap = 0 := by
  apply LinearMap.ext
  intro k
  exact apply_ker_subtype f k

/-- Forgetting the bundled inclusion gives the ordinary linear kernel subtype. -/
@[simp] theorem ker_subtype_toLinearMap (f : RightComoduleHom X Y) :
    (ker f).subtype.toLinearMap = (LinearMap.ker f.toLinearMap).subtype := rfl

/-- Tensor inclusion reads the kernel coaction as the ambient coaction. -/
theorem ker_subtype_rTensor_comp_coaction (f : RightComoduleHom X Y) :
    (ker f).toSubmodule.subtype.rTensor C ∘ₗ (ker f).comodule.coaction =
      X.coaction ∘ₗ (ker f).toSubmodule.subtype :=
  (ker f).subtype_colinear

/-- The kernel coaction has the expected ambient value through tensor inclusion. -/
theorem ker_subtype_rTensor_coaction (f : RightComoduleHom X Y)
    (k : (ker f).toSubmodule) :
    (ker f).toSubmodule.subtype.rTensor C ((ker f).comodule.coaction k) =
      X.coaction (k : M) :=
  LinearMap.congr_fun (ker_subtype_rTensor_comp_coaction f) k

variable {P : Type uP} [AddCommMonoid P] [Module R P]
variable {Z : RightComodule R C P}

private theorem kerLift_colinear (f : RightComoduleHom X Y)
    (g : RightComoduleHom Z X) (h : ∀ p : P, f (g p) = 0) :
    let l := LinearMap.codRestrict (ker f).toSubmodule g.toLinearMap
      (fun p ↦ (mem_ker f (g p)).mpr (h p))
    (ker f).comodule.coaction ∘ₗ l = l.rTensor C ∘ₗ Z.coaction := by
  dsimp only
  obtain ⟨k, hk, _⟩ := (ker f).existsUnique_factorization Z g
    (fun p ↦ (mem_ker f (g p)).mpr (h p))
  have hk_linear : k.toLinearMap =
      LinearMap.codRestrict (ker f).toSubmodule g.toLinearMap
        (fun p ↦ (mem_ker f (g p)).mpr (h p)) := by
    apply LinearMap.ext
    intro p
    apply Subtype.ext
    exact congrArg (fun a : RightComoduleHom Z X ↦ a p) hk
  rw [← hk_linear]
  exact k.colinear

/-- Factor a morphism annihilated by `f` through its kernel, with underlying
linear map the ordinary codomain restriction. -/
noncomputable def kerLift (f : RightComoduleHom X Y) (g : RightComoduleHom Z X)
    (h : ∀ p : P, f (g p) = 0) : RightComoduleHom Z (ker f).comodule where
  toLinearMap := LinearMap.codRestrict (ker f).toSubmodule g.toLinearMap
    (fun p ↦ (mem_ker f (g p)).mpr (h p))
  colinear := private kerLift_colinear f g h

/-- The kernel lift factors the original morphism through the kernel inclusion. -/
@[simp] theorem subtype_comp_kerLift (f : RightComoduleHom X Y)
    (g : RightComoduleHom Z X) (h : ∀ p : P, f (g p) = 0) :
    (ker f).subtype.comp (kerLift f g h) = g := by
  apply RightComoduleHom.ext
  intro p
  rfl

/-- The value of the kernel lift has the same underlying element as the original morphism. -/
@[simp] theorem kerLift_apply (f : RightComoduleHom X Y) (g : RightComoduleHom Z X)
    (h : ∀ p : P, f (g p) = 0) (p : P) :
    (@DFunLike.coe _ _ _
        (@RightComoduleHom.instFunLike R C P (LinearMap.ker f.toLinearMap)
          _ _ _ _ _ _ (ker f).addCommMonoid (ker f).module Z (ker f).comodule)
        (kerLift f g h) p : M) = g p :=
  rfl

/-- Forgetting colinearity gives the specified stock linear codomain restriction. -/
@[simp] theorem kerLift_toLinearMap (f : RightComoduleHom X Y)
    (g : RightComoduleHom Z X) (h : ∀ p : P, f (g p) = 0) :
    (kerLift f g h).toLinearMap =
      LinearMap.codRestrict (ker f).toSubmodule g.toLinearMap
        (fun p ↦ (mem_ker f (g p)).mpr (h p)) := rfl

/-- A morphism with the prescribed inclusion composite is the canonical kernel lift. -/
theorem kerLift_unique (f : RightComoduleHom X Y) (g : RightComoduleHom Z X)
    (h : ∀ p : P, f (g p) = 0) (l : RightComoduleHom Z (ker f).comodule)
    (hl : (ker f).subtype.comp l = g) : l = kerLift f g h :=
  ((ker f).subtype_comp_eq_iff).mp (hl.trans (subtype_comp_kerLift f g h).symm)

/-- Every morphism annihilated by `f` has exactly one factorization through its kernel. -/
theorem existsUnique_kerLift (f : RightComoduleHom X Y) (g : RightComoduleHom Z X)
    (h : ∀ p : P, f (g p) = 0) :
    ∃! l : RightComoduleHom Z (ker f).comodule, (ker f).subtype.comp l = g := by
  refine ⟨kerLift f g h, subtype_comp_kerLift f g h, ?_⟩
  intro l hl
  exact kerLift_unique f g h l hl

end Coalgebra.RightComoduleHom
