/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.Quotient
public import AlgebraicGroups.Algebra.Coalgebra.Subcoalgebra.Hom
public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
public import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# A noninjective endomorphism of the diagonal additive monoid coalgebra

For every field `K`, the zero additive map `ℕ →+ ℕ` induces a coalgebra
endomorphism of `AddMonoidAlgebra K ℕ`. Each standard basis vector is group-like,
and the endomorphism sends every such vector to the vector at `0`. The difference
of the vectors at `0` and `1` is a nonzero element of its kernel, including in
positive characteristic.

The range is exactly the nonzero line spanned by the vector at `0`. It excludes
the vector at `1`, so is proper, and its subtype is a finite-dimensional
`K`-module. Both source and target are the same infinite-dimensional module:
their standard basis is indexed by `ℕ`.

The morphism is the coalgebra homomorphism underlying
`AddMonoidAlgebra.mapDomainBialgHom`; no coalgebra structure or instance is added.
The linear range calculations also describe `CoalgHom.range` on this same morphism.
Its `CoalgHom.rangeRestrict` gives the surjective factor in the factorization through the
range inclusion.

Its kernel is a coideal: in the linear quotient by the kernel, every standard
basis vector has the same class, so projected comultiplication is the counit
followed by the linear map sending `1` to the tensor square of that class. This
direct calculation uses only the stock coideal definition. The field kernel
theorem also applies to this same noninjective, nonsurjective morphism.

## References

The bundled index map and group-like elements are those of Mathlib's
`Mathlib.RingTheory.Bialgebra.MonoidAlgebra`. The standard basis is
`AddMonoidAlgebra.basis`, and infinite dimensionality uses
`Module.not_finite_of_infinite_basis`. The range computation uses the basis span
and `Submodule.map_span`; finite dimensionality uses `Submodule.fg_span_singleton`
and `Module.Finite.iff_fg`. The coideal calculation uses `Basis.ext`,
`Submodule.Quotient.eq`, and the two fields of Mathlib's `Submodule.IsCoideal`.
The subcoalgebra range and unique factorization use
`AlgebraicGroups.Algebra.Coalgebra.Subcoalgebra.Hom`.
-/

@[expose] public section

open TauCeti


noncomputable section

universe u

open scoped TensorProduct

namespace AddMonoidAlgebra

variable (K : Type u) [Field K]

/-- The index-collapse endomorphism, with the coalgebra structure inherited from Mathlib. -/
private abbrev collapse : AddMonoidAlgebra K ℕ →ₗc[K] AddMonoidAlgebra K ℕ :=
  (mapDomainBialgHom K (0 : ℕ →+ ℕ)).toCoalgHom

private lemma collapse_single (i : ℕ) (a : K) :
    collapse K (single i a) = single 0 a := by
  change mapDomainBialgHom K (0 : ℕ →+ ℕ) (single i a) = single 0 a
  rw [mapDomainBialgHom_single]
  rfl

private lemma collapse_basis (i : ℕ) :
    collapse K (basis ℕ K i) = basis ℕ K 0 := by
  rw [basis_apply, basis_apply, collapse_single]

private lemma isGroupLikeElem_basis (i : ℕ) :
    IsGroupLikeElem K (basis ℕ K i) := by
  rw [basis_apply]
  exact isGroupLikeElem_single_one i

private lemma kernel_vector_ne_zero :
    (single 0 (1 : K) - single 1 (1 : K) : AddMonoidAlgebra K ℕ) ≠ 0 := by
  intro h
  have h0 := congrArg (fun x : AddMonoidAlgebra K ℕ => x.coeff 0) h
  simp at h0

private lemma collapse_kernel_vector :
    collapse K (single 0 (1 : K) - single 1 (1 : K)) = 0 := by
  rw [map_sub, collapse_single, collapse_single, sub_self]

private lemma kernel_vector_mem_ker :
    single 0 (1 : K) - single 1 (1 : K) ∈ LinearMap.ker (collapse K).toLinearMap := by
  rw [LinearMap.mem_ker]
  exact collapse_kernel_vector K

private lemma collapse_not_injective : ¬ Function.Injective (collapse K) := by
  intro h
  apply kernel_vector_ne_zero K
  apply h
  rw [collapse_kernel_vector, map_zero]

private lemma collapse_range :
    LinearMap.range (collapse K).toLinearMap =
      Submodule.span K ({basis ℕ K 0} : Set (AddMonoidAlgebra K ℕ)) := by
  have himage : (collapse K).toLinearMap '' Set.range (basis ℕ K) =
      ({basis ℕ K 0} : Set (AddMonoidAlgebra K ℕ)) := by
    ext x
    constructor
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      exact Set.mem_singleton_iff.mpr (collapse_basis K i)
    · intro hx
      have hx' : x = basis ℕ K 0 := Set.mem_singleton_iff.mp hx
      subst x
      exact ⟨basis ℕ K 0, ⟨0, rfl⟩, collapse_basis K 0⟩
  rw [LinearMap.range_eq_map, ← (basis ℕ K).span_eq, Submodule.map_span, himage]

private lemma single_zero_mem_range :
    single 0 (1 : K) ∈ LinearMap.range (collapse K).toLinearMap :=
  ⟨single 0 (1 : K), collapse_single K 0 1⟩

private lemma collapse_range_ne_bot : LinearMap.range (collapse K).toLinearMap ≠ ⊥ := by
  intro h
  have he := single_zero_mem_range K
  rw [h, Submodule.mem_bot] at he
  exact (isGroupLikeElem_single_one (R := K) (A := K) (0 : ℕ)).ne_zero he

private lemma single_one_not_mem_range :
    single 1 (1 : K) ∉ LinearMap.range (collapse K).toLinearMap := by
  rw [collapse_range, basis_apply]
  intro hx
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hx
  have h1 := congrArg (fun x : AddMonoidAlgebra K ℕ => x.coeff 1) ha
  simp at h1

private lemma collapse_range_ne_top : LinearMap.range (collapse K).toLinearMap ≠ ⊤ := by
  intro h
  apply single_one_not_mem_range K
  rw [h]
  exact Submodule.mem_top

private lemma collapse_range_fg : (LinearMap.range (collapse K).toLinearMap).FG := by
  rw [collapse_range]
  exact Submodule.fg_span_singleton _

private lemma collapse_range_finite : Module.Finite K (LinearMap.range (collapse K).toLinearMap) :=
  Module.Finite.iff_fg.mpr (collapse_range_fg K)

private lemma not_finite_nat_monoidAlgebra : ¬ Module.Finite K (AddMonoidAlgebra K ℕ) :=
  Module.not_finite_of_infinite_basis (basis ℕ K)

/-- The coalgebra homomorphism induced by the zero additive map on `ℕ` sends all
standard basis vectors to the vector at `0`. These vectors have diagonal
comultiplication and counit `1`. Their difference at `0` and `1` is nonzero and
lies in the kernel, so the morphism is not injective, over every field. -/
theorem mapDomainBialgHom_zero_basis_and_kernel :
    let f := (mapDomainBialgHom K (0 : ℕ →+ ℕ)).toCoalgHom
    (∀ (i : ℕ) (a : K), f (single i a) = single 0 a) ∧
      (∀ i : ℕ,
        Coalgebra.counit (R := K) (basis ℕ K i) = 1 ∧
          Coalgebra.comul (R := K) (basis ℕ K i) =
            basis ℕ K i ⊗ₜ[K] basis ℕ K i ∧
          f (basis ℕ K i) = basis ℕ K 0) ∧
      (single 0 (1 : K) - single 1 (1 : K) : AddMonoidAlgebra K ℕ) ≠ 0 ∧
      f (single 0 (1 : K) - single 1 (1 : K)) = 0 ∧
      single 0 (1 : K) - single 1 (1 : K) ∈ LinearMap.ker f.toLinearMap ∧
      ¬ Function.Injective f := by
  refine ⟨collapse_single K, ?_, kernel_vector_ne_zero K, collapse_kernel_vector K,
    kernel_vector_mem_ker K, collapse_not_injective K⟩
  intro i
  have hi := isGroupLikeElem_basis K i
  exact ⟨hi.counit_eq_one, hi.comul_eq_tmul_self, collapse_basis K i⟩

/-- The range of the coalgebra homomorphism induced by the zero additive map on
`ℕ` is exactly the line spanned by the standard basis vector at `0`. This range
is nonzero, proper, finitely generated and finite-dimensional. Its source and
target are both `AddMonoidAlgebra K ℕ`, which is not a finite `K`-module. -/
theorem mapDomainBialgHom_zero_range_finite :
    let f := (mapDomainBialgHom K (0 : ℕ →+ ℕ)).toCoalgHom
    LinearMap.range f.toLinearMap =
        Submodule.span K ({basis ℕ K 0} : Set (AddMonoidAlgebra K ℕ)) ∧
      LinearMap.range f.toLinearMap ≠ ⊥ ∧
      LinearMap.range f.toLinearMap ≠ ⊤ ∧
      single 0 (1 : K) ∈ LinearMap.range f.toLinearMap ∧
      single 1 (1 : K) ∉ LinearMap.range f.toLinearMap ∧
      (LinearMap.range f.toLinearMap).FG ∧
      Module.Finite K (LinearMap.range f.toLinearMap) ∧
      ¬ Module.Finite K (AddMonoidAlgebra K ℕ) := by
  exact ⟨collapse_range K, collapse_range_ne_bot K, collapse_range_ne_top K,
    single_zero_mem_range K, single_one_not_mem_range K, collapse_range_fg K,
    collapse_range_finite K, not_finite_nat_monoidAlgebra K⟩

private lemma collapse_quotient_basis (i : ℕ) :
    (LinearMap.ker (collapse K).toLinearMap).mkQ (basis ℕ K i) =
      (LinearMap.ker (collapse K).toLinearMap).mkQ (basis ℕ K 0) := by
  apply (Submodule.Quotient.eq _).2
  rw [LinearMap.mem_ker]
  change collapse K (basis ℕ K i - basis ℕ K 0) = 0
  rw [map_sub, collapse_basis, collapse_basis, sub_self]

/-- The kernel of index collapse is a coideal by a direct calculation on the
standard basis. Projected comultiplication factors through the counit because
all basis vectors have the same class in the linear quotient by the kernel. -/
theorem mapDomainBialgHom_zero_ker_isCoideal :
    let f := (mapDomainBialgHom K (0 : ℕ →+ ℕ)).toCoalgHom
    (LinearMap.ker f.toLinearMap).IsCoideal := by
  let I := LinearMap.ker (collapse K).toLinearMap
  let q := I.mkQ
  have hq (i : ℕ) : q (basis ℕ K i) = q (basis ℕ K 0) :=
    collapse_quotient_basis K i
  have hcomul :
      (TensorProduct.map q q).comp (Coalgebra.comul (R := K)) =
        (LinearMap.toSpanSingleton K _
          (q (basis ℕ K 0) ⊗ₜ[K] q (basis ℕ K 0))).comp
            (Coalgebra.counit (R := K)) := by
    apply (basis ℕ K).ext
    intro i
    have hi := isGroupLikeElem_basis K i
    simp only [LinearMap.comp_apply, hi.comul_eq_tmul_self,
      TensorProduct.map_tmul, hq i, hi.counit_eq_one,
      LinearMap.toSpanSingleton_apply_one]
  have hcounit (x : AddMonoidAlgebra K ℕ) (hx : x ∈ I) :
      Coalgebra.counit (R := K) x = 0 := by
    have hx0 : collapse K x = 0 := hx
    rw [← CoalgHomClass.counit_comp_apply (collapse K) x, hx0, map_zero]
  refine ⟨?_, ?_⟩
  · intro x hx
    exact hcounit x hx
  · intro x hx
    change TensorProduct.map q q (Coalgebra.comul x) = 0
    simpa only [LinearMap.comp_apply, hcounit x hx, map_zero] using
      LinearMap.congr_fun hcomul x

/-- The field kernel theorem applies to index collapse despite its nonzero
kernel and proper range, witnessed by the preceding basis and range results. -/
theorem mapDomainBialgHom_zero_ker_coideal_not_injective_not_surjective :
    let f := (mapDomainBialgHom K (0 : ℕ →+ ℕ)).toCoalgHom
    (LinearMap.ker f.toLinearMap).IsCoideal ∧
      ¬ Function.Injective f ∧ ¬ Function.Surjective f := by
  refine ⟨CoalgHomClass.ker_isCoideal (collapse K), collapse_not_injective K, ?_⟩
  intro h
  exact single_one_not_mem_range K (h _)

/-- The coalgebra range of the index-collapse morphism has the same nonzero proper
one-dimensional carrier as its linear range, although its source and target are infinite
dimensional. -/
theorem mapDomainBialgHom_zero_subcoalgebra_range :
    let f := (mapDomainBialgHom K (0 : ℕ →+ ℕ)).toCoalgHom
    f.range.toSubmodule =
        Submodule.span K ({basis ℕ K 0} : Set (AddMonoidAlgebra K ℕ)) ∧
      f.range.toSubmodule ≠ ⊥ ∧
      f.range.toSubmodule ≠ ⊤ ∧
      single 0 (1 : K) ∈ f.range ∧
      single 1 (1 : K) ∉ f.range ∧
      Module.Finite K f.range.toSubmodule ∧
      ¬ Module.Finite K (AddMonoidAlgebra K ℕ) := by
  dsimp only
  rcases mapDomainBialgHom_zero_range_finite K with
    ⟨hrange, hbot, htop, hzero, hone, hfg, _, hinfinite⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hinfinite⟩
  · simpa only [CoalgHom.range_toSubmodule, CoalgHom.toLinearMap_eq_ofClass] using hrange
  · simpa only [CoalgHom.range_toSubmodule, CoalgHom.toLinearMap_eq_ofClass] using hbot
  · simpa only [CoalgHom.range_toSubmodule, CoalgHom.toLinearMap_eq_ofClass] using htop
  · exact CoalgHom.mem_range.mpr (LinearMap.mem_range.mp hzero)
  · intro hx
    exact hone (LinearMap.mem_range.mpr (CoalgHom.mem_range.mp hx))
  · change Module.Finite K ((collapse K).range.toSubmodule)
    apply Module.Finite.iff_fg.mpr
    simpa only [CoalgHom.range_toSubmodule, CoalgHom.toLinearMap_eq_ofClass] using hfg

/-- The index-collapse morphism factors through its coalgebra range by a surjection and an
injection. The factor has unchanged ambient values and is the unique factor through this
inclusion, even though the original morphism has a nonzero kernel. -/
theorem mapDomainBialgHom_zero_range_factorization :
    let f := (mapDomainBialgHom K (0 : ℕ →+ ℕ)).toCoalgHom
    (∀ x, (f.rangeRestrict x : AddMonoidAlgebra K ℕ) = f x) ∧
      f.range.subtype.comp f.rangeRestrict = f ∧
      Function.Surjective f.rangeRestrict ∧
      Function.Injective f.range.subtype ∧
      (∀ g : AddMonoidAlgebra K ℕ →ₗc[K] f.range.toSubmodule,
        f.range.subtype.comp g = f → g = f.rangeRestrict) ∧
      (single 0 (1 : K) - single 1 (1 : K) : AddMonoidAlgebra K ℕ) ≠ 0 ∧
      f (single 0 (1 : K) - single 1 (1 : K)) = 0 := by
  dsimp only
  refine ⟨CoalgHom.coe_rangeRestrict _, CoalgHom.subtype_comp_rangeRestrict _,
    CoalgHom.surjective_rangeRestrict _, Subcoalgebra.subtype_injective _,
    ?_, kernel_vector_ne_zero K, collapse_kernel_vector K⟩
  intro g hg
  exact CoalgHom.rangeRestrict_unique _ g hg

end AddMonoidAlgebra
