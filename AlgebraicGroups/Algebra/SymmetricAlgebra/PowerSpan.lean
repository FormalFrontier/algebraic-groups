/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic

/-!
# Pure-power spans in symmetric algebras

The submodule `SymmetricAlgebra.purePowerSubmodule K V n` is spanned by the `n`th
powers of the generators of the symmetric algebra. Every linear map induces an
algebra homomorphism preserving these spans, and hence a linear map between them.
These induced maps preserve identities and composition for every natural exponent.

## Implementation notes

The span need not be the whole homogeneous symmetric component. The induced map
is linear in its span element, but its dependence on the original linear map is
generally neither additive nor linear: scaling that map by `a` scales the induced
map by `a ^ n`. In degree zero, the span is the unit span and every induced map
fixes scalar units, including when the original linear map is zero; `0 ^ 0 = 1`.
No coaction or characteristic assumption is used.

## References

* Mathlib's symmetric-algebra universal property, submodule spans and linear-map
  restriction API.
-/

@[expose] public section

universe u a v w z

namespace SymmetricAlgebra

section CommSemiring

variable (K : Type u) (V : Type v)
variable [CommSemiring K] [AddCommMonoid V] [Module K V]

/-- The submodule of the symmetric algebra spanned by the `n`th powers of its generators. -/
def purePowerSubmodule (n : ℕ) : Submodule K (SymmetricAlgebra K V) :=
  Submodule.span K (Set.range fun v : V ↦ (ι K V v) ^ n)

/-- The power submodule has the span universal property. -/
theorem purePowerSubmodule_eq_span (n : ℕ) :
    purePowerSubmodule K V n =
      Submodule.span K (Set.range fun v : V ↦ (ι K V v) ^ n) := rfl

/-- Every generating power belongs to the power submodule. -/
theorem ι_pow_mem_purePowerSubmodule (n : ℕ) (v : V) :
    (ι K V v) ^ n ∈ purePowerSubmodule K V n := by
  exact Submodule.subset_span ⟨v, rfl⟩

/-- Containment of a power submodule is tested on every generating power. -/
theorem purePowerSubmodule_le_iff (n : ℕ) (U : Submodule K (SymmetricAlgebra K V)) :
    purePowerSubmodule K V n ≤ U ↔ ∀ v : V, (ι K V v) ^ n ∈ U := by
  constructor
  · intro h v
    exact h (ι_pow_mem_purePowerSubmodule K V n v)
  · intro h
    apply Submodule.span_le.mpr
    rintro _ ⟨v, rfl⟩
    exact h v

/-- The zeroth-power submodule is the unit line. -/
@[simp] theorem purePowerSubmodule_zero :
    purePowerSubmodule K V 0 = Submodule.span K {1} := by
  rw [purePowerSubmodule_eq_span]
  simp only [pow_zero, Set.range_const]

/-- The first-power submodule is the image of the original generator map. -/
@[simp] theorem purePowerSubmodule_one :
    purePowerSubmodule K V 1 = LinearMap.range (ι K V) := by
  apply le_antisymm
  · rw [purePowerSubmodule_le_iff]
    intro v
    exact ⟨v, by simp only [pow_one]⟩
  · rintro _ ⟨v, rfl⟩
    simpa only [pow_one] using ι_pow_mem_purePowerSubmodule K V 1 v

section Map

variable {K V} {W : Type w} {U : Type z}
variable [AddCommMonoid W] [Module K W] [AddCommMonoid U] [Module K U]

/-- The algebra homomorphism on symmetric algebras induced by a linear map. -/
def map (f : V →ₗ[K] W) : SymmetricAlgebra K V →ₐ[K] SymmetricAlgebra K W :=
  lift (ι K W ∘ₗ f)

/-- The induced algebra homomorphism sends generators to their specified images. -/
@[simp] theorem map_ι (f : V →ₗ[K] W) (v : V) :
    map f (ι K V v) = ι K W (f v) :=
  lift_ι_apply _ v

/-- A map induced on symmetric algebras is determined by its generator equation. -/
theorem map_unique (f : V →ₗ[K] W)
    (g : SymmetricAlgebra K V →ₐ[K] SymmetricAlgebra K W)
    (hg : ∀ v : V, g (ι K V v) = ι K W (f v)) : g = map f := by
  apply algHom_ext
  apply LinearMap.ext
  intro v
  exact (hg v).trans (map_ι f v).symm

/-- The symmetric-algebra construction preserves identity maps. -/
@[simp] theorem map_id :
    map (LinearMap.id : V →ₗ[K] V) = AlgHom.id K (SymmetricAlgebra K V) := by
  apply algHom_ext
  apply LinearMap.ext
  intro v
  exact map_ι (LinearMap.id : V →ₗ[K] V) v

/-- The symmetric-algebra construction preserves composition of linear maps. -/
@[simp] theorem map_comp (g : W →ₗ[K] U) (f : V →ₗ[K] W) :
    map (g.comp f) = (map g).comp (map f) := by
  apply algHom_ext
  apply LinearMap.ext
  intro v
  change map (g.comp f) (ι K V v) = map g (map f (ι K V v))
  calc
    map (g.comp f) (ι K V v) = ι K U (g (f v)) := map_ι (g.comp f) v
    _ = map g (ι K W (f v)) := (map_ι g (f v)).symm
    _ = map g (map f (ι K V v)) := congrArg (map g) (map_ι f v).symm

/-- The algebra homomorphism induced by a linear map preserves every pure-power span. -/
theorem map_mem_purePowerSubmodule (n : ℕ) (f : V →ₗ[K] W)
    {x : SymmetricAlgebra K V} (hx : x ∈ purePowerSubmodule K V n) :
    map f x ∈ purePowerSubmodule K W n := by
  have hle : purePowerSubmodule K V n ≤
      (purePowerSubmodule K W n).comap (map f).toLinearMap := by
    apply (purePowerSubmodule_le_iff K V n _).2
    intro v
    simpa only [Submodule.mem_comap, AlgHom.toLinearMap_apply, map_pow, map_ι] using
      ι_pow_mem_purePowerSubmodule K W n (f v)
  exact hle hx

namespace purePowerSubmodule

/-- The linear map between pure-power spans induced by a linear map on the original modules.
It is linear in the span element, but its dependence on `f` is generally neither additive nor
linear. In degree zero it fixes scalar units, even when `f` is zero. -/
def map (n : ℕ) (f : V →ₗ[K] W) :
    purePowerSubmodule K V n →ₗ[K] purePowerSubmodule K W n :=
  LinearMap.restrict (SymmetricAlgebra.map f).toLinearMap
    (fun _ hx ↦ map_mem_purePowerSubmodule n f hx)

/-- The underlying value of the induced span map is the induced algebra homomorphism. -/
@[simp] theorem coe_map_apply (n : ℕ) (f : V →ₗ[K] W)
    (x : purePowerSubmodule K V n) :
    (map n f x : SymmetricAlgebra K W) =
      SymmetricAlgebra.map f (x : SymmetricAlgebra K V) :=
  LinearMap.coe_restrict_apply
    (f := (SymmetricAlgebra.map f).toLinearMap)
    (fun _ hx ↦ map_mem_purePowerSubmodule n f hx) x

/-- Inclusion of the induced span map agrees with the ambient induced linear map. -/
theorem subtype_comp_map (n : ℕ) (f : V →ₗ[K] W) :
    (purePowerSubmodule K W n).subtype.comp (map n f) =
      (SymmetricAlgebra.map f).toLinearMap.comp (purePowerSubmodule K V n).subtype :=
  LinearMap.subtype_comp_restrict
    (f := (SymmetricAlgebra.map f).toLinearMap)
    (fun _ hx ↦ map_mem_purePowerSubmodule n f hx)

/-- The induced span map sends a generating power to the power of its specified image. -/
@[simp] theorem map_ι_pow (n : ℕ) (f : V →ₗ[K] W) (v : V) :
    map n f ⟨(ι K V v) ^ n, ι_pow_mem_purePowerSubmodule K V n v⟩ =
      ⟨(ι K W (f v)) ^ n, ι_pow_mem_purePowerSubmodule K W n (f v)⟩ := by
  apply Subtype.ext
  simp only [coe_map_apply, map_pow, SymmetricAlgebra.map_ι]

/-- The pure-power span construction preserves identity maps. -/
@[simp] theorem map_id (n : ℕ) :
    map n (LinearMap.id : V →ₗ[K] V) =
      (LinearMap.id : purePowerSubmodule K V n →ₗ[K] purePowerSubmodule K V n) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [coe_map_apply, SymmetricAlgebra.map_id, AlgHom.id_apply, LinearMap.id_apply]

/-- The pure-power span construction preserves composition of linear maps. -/
@[simp] theorem map_comp (n : ℕ) (g : W →ₗ[K] U) (f : V →ₗ[K] W) :
    map n (g.comp f) = (map n g).comp (map n f) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [LinearMap.comp_apply, coe_map_apply, SymmetricAlgebra.map_comp,
    AlgHom.comp_apply]

end purePowerSubmodule

end Map

end CommSemiring

end SymmetricAlgebra
