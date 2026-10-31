/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupObject.Flat
public import SchemeProperties.GenericFlatness.Reduced

/-!
# Flatness of group homomorphisms over a field

A surjective locally finite type homomorphism of group schemes over a field is flat if
its target is reduced and has finitely many irreducible components. The group objects
are taken for a fixed Cartesian-monoidal structure on the over category.

The proof combines the nonempty affine flat source open supplied by
`Scheme.Hom.exists_nonempty_isAffineOpen_flat_of_finite_irreducibleComponents` with the
group-family flatness criterion `Flat.of_group_hom_family`. The parameter is the original
open subscheme, with no group structure required on it. Structural flatness over the field
follows from Mathlib's flatness instance for morphisms to a subsingleton integral scheme.

## References

* J. S. Milne, *Algebraic Groups* (2017), for the general theory of algebraic groups and
  generic flatness.

This formalization uses Mathlib and Scheme Properties and was prepared with AI assistance.
-/

@[expose] public section

open CategoryTheory MonoidalCategory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A surjective locally finite type homomorphism of group schemes over a field is flat
if the target is reduced and has finitely many irreducible components. The proof combines
generic flatness with the group-family criterion; see Milne, *Algebraic Groups* (2017),
for background. -/
theorem Flat.of_group_hom_over_field
    (k : Type u) [Field k]
    [c : CartesianMonoidalCategory (Over (Spec (CommRingCat.of k)))]
    (G H : Over (Spec (CommRingCat.of k))) [GrpObj G] [GrpObj H]
    (f : G ⟶ H) [IsMonHom f]
    [LocallyOfFiniteType f.left] [Surjective f.left] [IsReduced H.left]
    (hfinite : (irreducibleComponents H.left).Finite) : Flat f.left := by
  let S := Spec (CommRingCat.of k)
  let e : (𝟙_ (Over S)) ≅ Over.mk (𝟙 S) :=
    (CategoryTheory.SemiCartesianMonoidalCategory.isTerminalTensorUnit
      (C := Over S)).uniqueUpToIso (Over.mkIdTerminal (X := S))
  let σ : Over.mk (𝟙 S) ⟶ H := e.inv ≫ MonObj.one (X := H)
  have : Nonempty H.left := Nonempty.map σ.left (inferInstance : Nonempty S)
  obtain ⟨U, hU, _, hflat⟩ :=
    Scheme.Hom.exists_nonempty_isAffineOpen_flat_of_finite_irreducibleComponents
      f.left hfinite
  let P : Over S := Over.mk (U.ι ≫ G.hom)
  let i : P ⟶ G := Over.homMk U.ι rfl
  have : Flat P.hom := by infer_instance
  have : Surjective P.hom := by
    obtain ⟨x, hx⟩ := hU
    let u₀ : U.toScheme := ⟨x, hx⟩
    exact ⟨fun s ↦ ⟨u₀, Subsingleton.elim (P.hom u₀) s⟩⟩
  have : Flat G.hom := by infer_instance
  have : Flat (i ≫ f).left := hflat
  exact Flat.of_group_hom_family G H f P i

end AlgebraicGeometry
