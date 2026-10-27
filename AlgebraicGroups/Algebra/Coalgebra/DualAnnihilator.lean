/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Coalgebra.Convolution
public import Mathlib.RingTheory.Coalgebra.Quotient

/-!
# Coideal annihilators and convolution subalgebras

The ordinary full-dual annihilator of a coideal contains the counit and is
closed under stock convolution. These forward implications use only
`CoalgebraStruct`, not coalgebra laws, projectivity, flatness or finite rank.
The ring and the module have independent universes.

The carrier is Mathlib's `Submodule.dualAnnihilator` in `Module.Dual R C`.
Convolution is Mathlib's multiplication on `WithConv (Module.Dual R C)`;
`WithConv.toConv` and `WithConv.ofConv` make the carrier bridge explicit.
When `C` is a `Coalgebra R C`, this carrier defines the canonical subalgebra
`Submodule.IsCoideal.dualAnnihilatorSubalgebra` of the convolution algebra.
The full coalgebra laws supply the ambient unital associative algebra; the
two forward closure results themselves require only `CoalgebraStruct`.
No converse is asserted here.

## References

- Mathlib's `LinearAlgebra.Dual.Lemmas` supplies the ordinary annihilator and
  its identification with the ordinary quotient dual.
- Mathlib's `RingTheory.Coalgebra.Convolution`, by Yaël Dillies, Michał Mrugała
  and Yunzhou Xie, supplies the convolution operations.
- Mathlib's `RingTheory.Coalgebra.Quotient` supplies the coideal predicate.
- Mathlib's `Algebra.Algebra.Subalgebra.Basic` supplies `Submodule.toSubalgebra`.
-/

@[expose] public section

universe u v

namespace Submodule

variable {R : Type u} [CommRing R]
variable {C : Type v} [AddCommGroup C] [Module R C]

section CoalgebraStruct

variable [CoalgebraStruct R C]

/-- The counit belongs to the full-dual annihilator of a coideal. -/
theorem IsCoideal.counit_mem_dualAnnihilator {p : Submodule R C} (hp : p.IsCoideal) :
    (Coalgebra.counit (R := R) : Module.Dual R C) ∈ p.dualAnnihilator := by
  exact (mem_dualAnnihilator _).mpr fun _ hx => hp.counit_eq_zero hx

/-- The full-dual annihilator of a coideal is closed under stock convolution,
without projectivity or coalgebra laws. -/
theorem IsCoideal.convMul_mem_dualAnnihilator {p : Submodule R C} (hp : p.IsCoideal)
    {f g : Module.Dual R C} (hf : f ∈ p.dualAnnihilator) (hg : g ∈ p.dualAnnihilator) :
    (WithConv.toConv f * WithConv.toConv g).ofConv ∈ p.dualAnnihilator := by
  have hfker : p ≤ LinearMap.ker f := fun x hx => (mem_dualAnnihilator f).mp hf x hx
  have hgker : p ≤ LinearMap.ker g := fun x hx => (mem_dualAnnihilator g).mp hg x hx
  apply (mem_dualAnnihilator _).mpr
  intro x hx
  rw [LinearMap.convMul_def]
  change LinearMap.mul' R R (TensorProduct.map f g (Coalgebra.comul x)) = 0
  rw [← p.liftQ_mkQ f hfker, ← p.liftQ_mkQ g hgker, TensorProduct.map_comp]
  simp only [LinearMap.comp_apply, hp.map_mkQ_comul_eq_zero hx, map_zero]

end CoalgebraStruct

section Coalgebra

variable [Coalgebra R C]

/-- The full-dual annihilator of a coideal as a subalgebra of the convolution algebra. -/
noncomputable def IsCoideal.dualAnnihilatorSubalgebra {p : Submodule R C} (hp : p.IsCoideal) :
    Subalgebra R (WithConv (Module.Dual R C)) :=
  (p.dualAnnihilator.comap (WithConv.linearEquiv R (Module.Dual R C)).toLinearMap).toSubalgebra
    (by
      change (1 : WithConv (Module.Dual R C)).ofConv ∈ p.dualAnnihilator
      simpa only [LinearMap.convOne_def, WithConv.ofConv_toConv, Algebra.linearMap_self,
        LinearMap.id_comp] using hp.counit_mem_dualAnnihilator)
    (by
      intro f g hf hg
      change (f * g).ofConv ∈ p.dualAnnihilator
      exact hp.convMul_mem_dualAnnihilator hf hg)

/-- Forgetting the subalgebra recovers the annihilator transported by `WithConv.linearEquiv`. -/
@[simp]
theorem IsCoideal.dualAnnihilatorSubalgebra_toSubmodule {p : Submodule R C}
    (hp : p.IsCoideal) :
    hp.dualAnnihilatorSubalgebra.toSubmodule =
      p.dualAnnihilator.comap (WithConv.linearEquiv R (Module.Dual R C)).toLinearMap := rfl

/-- Membership in the convolution subalgebra is ordinary annihilator membership after `ofConv`. -/
@[simp]
theorem IsCoideal.mem_dualAnnihilatorSubalgebra {p : Submodule R C} (hp : p.IsCoideal)
    {f : WithConv (Module.Dual R C)} :
    f ∈ hp.dualAnnihilatorSubalgebra ↔ f.ofConv ∈ p.dualAnnihilator := Iff.rfl

/-- A convolution functional belongs to the subalgebra exactly when it vanishes on the coideal. -/
theorem IsCoideal.mem_dualAnnihilatorSubalgebra_iff {p : Submodule R C} (hp : p.IsCoideal)
    {f : WithConv (Module.Dual R C)} :
    f ∈ hp.dualAnnihilatorSubalgebra ↔ ∀ x ∈ p, f.ofConv x = 0 := by
  rw [hp.mem_dualAnnihilatorSubalgebra, mem_dualAnnihilator]

/-- `toConv` carries precisely the ordinary annihilator into the convolution subalgebra. -/
theorem IsCoideal.toConv_mem_dualAnnihilatorSubalgebra {p : Submodule R C}
    (hp : p.IsCoideal) {f : Module.Dual R C} :
    WithConv.toConv f ∈ hp.dualAnnihilatorSubalgebra ↔ f ∈ p.dualAnnihilator := Iff.rfl

end Coalgebra

end Submodule
