/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import AlgebraicGroups.GroupScheme.Multiplicative
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import AlgebraicGroups.GroupScheme.Separated

/-!
# Multiplicative-group coordinate tests

These clients check the unit-valued coordinate formula and include zero-ring targets.
-/

set_option warningAsError true

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

universe u

variable (K R : Type u)
variable [CommRing K] [CommRing R] [Algebra K R]

private theorem persistentTestMultiplicative001 :
    Algebra.FiniteType K (multiplicativeGroupCoordinateRing K) :=
  inferInstance

private theorem persistentTestMultiplicative002 :
    LocallyOfFiniteType (multiplicativeGroupUnderlyingScheme K).hom :=
  inferInstance

private theorem persistentTestMultiplicative003 :
    QuasiCompact (multiplicativeGroupUnderlyingScheme K).hom :=
  inferInstance

private noncomputable def persistentTestMultiplicative004 :
    Rˣ ≃* WithConv (multiplicativeGroupCoordinateRing K →ₐ[K] R) :=
  multiplicativeGroupMulEquivAlgHom K R

private noncomputable def persistentTestMultiplicative005 :
    Rˣ ≃* ((Spec (.of R)).asOver (Spec (.of K)) ⟶ multiplicativeGroupUnderlyingScheme K) :=
  multiplicativeGroupMulEquivPoints K R

/-- The algebra map represented by a unit sends the multiplicative coordinate to that unit. -/
public theorem multiplicativeGroup_coordinate_evaluation (u : Rˣ) :
    (multiplicativeGroupMulEquivAlgHom K R u).ofConv
        (multiplicativeGroupCoordinate K) = u :=
  multiplicativeGroupMulEquivAlgHom_coordinate K R u

private theorem persistentTestMultiplicative007 {S : Type u} [CommRing S] [Algebra K S]
    (f : R →ₐ[K] S) (u : Rˣ) :
    (multiplicativeGroupMulEquivAlgHom K S (Units.map f u)).ofConv =
      f.comp (multiplicativeGroupMulEquivAlgHom K R u).ofConv :=
  multiplicativeGroupMulEquivAlgHom_naturality K R f u

private theorem persistentTestMultiplicative008 (u : Rˣ) :
    (multiplicativeGroupMulEquivPoints K R u).left =
      Spec.map (CommRingCat.ofHom
        (multiplicativeGroupMulEquivAlgHom K R u).ofConv.toRingHom) :=
  multiplicativeGroupMulEquivPoints_apply_left K R u

private theorem persistentTestMultiplicative009 :
    CoalgebraStruct.comul (multiplicativeGroupCoordinate K) =
      multiplicativeGroupCoordinate K ⊗ₜ[K] multiplicativeGroupCoordinate K :=
  multiplicativeGroupCoordinate_comul K

-- The entire API remains available when the target algebra is the zero ring.
private noncomputable def persistentTestMultiplicative010 [Subsingleton R] :
    Rˣ ≃* ((Spec (.of R)).asOver (Spec (.of K)) ⟶
      multiplicativeGroupUnderlyingScheme K) :=
  multiplicativeGroupMulEquivPoints K R

private noncomputable def persistentTestMultiplicative011 :
    (ZMod 1)ˣ ≃* WithConv
      (multiplicativeGroupCoordinateRing (ZMod 1) →ₐ[ZMod 1] ZMod 1) :=
  multiplicativeGroupMulEquivAlgHom (ZMod 1) (ZMod 1)

end AlgebraicGeometry

namespace AlgebraicGeometry

universe w

open CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj

section ProjectionKernel

variable (R : Type w) [CommRing R]

local notation "M" => multiplicativeGroupUnderlyingScheme R
local notation "q" => snd M M
local notation "K" => pullback q η[M]

-- Laurent-coordinate evaluation at the unit is evaluation at 1, over any ring.
private theorem multiplicative_unit_coordinate_one :
    (multiplicativeGroupMulEquivAlgHom R R (1 : Rˣ)).ofConv
      (multiplicativeGroupCoordinate R) = 1 := by
  exact multiplicativeGroupMulEquivAlgHom_coordinate R R (1 : Rˣ)

-- The counit is a quotient map: its composite with the scalar inclusion is identity.
private theorem multiplicative_unit_closed : IsClosedImmersion η[M].left := by
  rw [one_spec_asOver_spec_left]
  apply IsClosedImmersion.spec_of_surjective
  intro r
  exact ⟨algebraMap R (multiplicativeGroupCoordinateRing R) r,
    (Bialgebra.counitAlgHom R (multiplicativeGroupCoordinateRing R)).commutes r⟩

-- The closed unit makes the group separated, hence so is this base-change projection.
private theorem multiplicative_projection_separated : IsSeparated (q).left := by
  have : IsSeparated (M).hom :=
    isSeparated_of_isClosedImmersion_unit M (multiplicative_unit_closed R)
  change IsSeparated (pullback.snd (M).hom (M).hom)
  infer_instance

-- The kernel-pair square uses the pullback kernel and its first projection.
private theorem multiplicative_projection_kernel_pair :
    IsPullback ((pullback.fst q η[M] ⊗ₘ 𝟙 (M ⊗ M)) ≫ μ[M ⊗ M])
      (snd K (M ⊗ M)) q q := by
  have hp : pullback.snd q η[M] = toUnit K := toUnit_unique _ _
  have hK : IsPullback (pullback.fst q η[M]) (toUnit K) q η[M] := by
    simpa only [hp] using IsPullback.of_hasPullback q η[M]
  exact GrpObj.isPullback_kernel_mul _ q hK

-- The kernel-unit criterion gives closedness of the canonical lift, not of an ambient unit.
private theorem multiplicative_projection_kernelUnit_closed :
    IsClosedImmersion
      (pullback.lift (f := q) (g := η[M]) η[M ⊗ M]
        (𝟙 (𝟙_ (Over (Spec (.of R)))))
        (by simpa only [Category.id_comp] using IsMonHom.one_hom q)).left :=
  (isSeparated_iff_isClosedImmersion_kernelUnit q).mp
    (multiplicative_projection_separated R)

-- Both projections characterize this lift in the installed Over-category pullback.
private theorem multiplicative_projection_kernelUnit_projections :
    let k := pullback.lift (f := q) (g := η[M]) η[M ⊗ M]
      (𝟙 (𝟙_ (Over (Spec (.of R)))))
      (by simpa only [Category.id_comp] using IsMonHom.one_hom q)
    k ≫ pullback.fst q η[M] = η[M ⊗ M] ∧
      k ≫ pullback.snd q η[M] = 𝟙 (𝟙_ (Over (Spec (.of R)))) := by
  exact ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

end ProjectionKernel

-- The first factor contributes distinct 1 and -1 points to the actual unit fibre over Z.
private theorem multiplicative_projection_integer_kernel_nontrivial :
    let M := multiplicativeGroupUnderlyingScheme ℤ
    let q := snd M M
    ∃ a b : (Spec (.of ℤ)).asOver (Spec (.of ℤ)) ⟶ pullback q η[M], a ≠ b := by
  dsimp only
  let M := multiplicativeGroupUnderlyingScheme ℤ
  let q := snd M M
  let T := (Spec (.of ℤ)).asOver (Spec (.of ℤ))
  let point (u : ℤˣ) : T ⟶ pullback q η[M] :=
    pullback.lift (lift (multiplicativeGroupMulEquivPoints ℤ ℤ u)
      (toUnit T ≫ η[M])) (toUnit T) (by simp [q])
  refine ⟨point 1, point (-1), ?_⟩
  intro h
  have hpoints : multiplicativeGroupMulEquivPoints ℤ ℤ 1 =
      multiplicativeGroupMulEquivPoints ℤ ℤ (-1) := by
    have h' := congrArg (fun f : T ⟶ pullback q η[M] ↦
      f ≫ pullback.fst q η[M] ≫ fst M M) h
    simpa [point, Category.assoc, pullback.lift_fst_assoc] using h'
  have hunits := (multiplicativeGroupMulEquivPoints ℤ ℤ).injective hpoints
  have hvalues := congrArg Units.val hunits
  norm_num at hvalues

section Boundaries

variable {S : Scheme.{w}}

-- A unit-source map allows an arbitrary monoid target, without a target group instance.
private theorem unit_source_kernelUnit_closed (Q : Over S) [MonObj Q] :
    IsClosedImmersion
      (pullback.lift (f := η[Q]) (g := η[Q]) η[𝟙_ (Over S)]
        (𝟙 (𝟙_ (Over S)))
        (by simpa only [Category.id_comp] using IsMonHom.one_hom η[Q])).left := by
  have : IsSplitMono η[Q].left :=
    ⟨⟨{ retraction := Q.hom, id := by exact η[Q].w }⟩⟩
  exact (isSeparated_iff_isClosedImmersion_kernelUnit η[Q]).mp inferInstance

-- An identity has closed relative kernel unit without assuming its ambient unit closed.
private theorem identity_kernelUnit_closed (G : Over S) [GrpObj G] :
    IsClosedImmersion
      (pullback.lift (f := 𝟙 G) (g := η[G]) η[G] (𝟙 (𝟙_ (Over S)))
        (by simp)).left :=
  (isSeparated_iff_isClosedImmersion_kernelUnit (𝟙 G)).mp inferInstance

-- Spec of the zero ring is an empty base; no nontriviality premise is used above.
private theorem zero_base_projection_separated :
    IsSeparated (snd (multiplicativeGroupUnderlyingScheme (ZMod 1))
      (multiplicativeGroupUnderlyingScheme (ZMod 1))).left :=
  multiplicative_projection_separated (ZMod 1)

end Boundaries

end AlgebraicGeometry

namespace AlgebraicGeometry

attribute [local instance] Over.cartesianMonoidalCategory

/-- The multiplicative group scheme over the integers, with the distinct points
corresponding to the units `-1` and `1`. -/
private def integerMultiplicativeGroupPoints :
    Σ G : Grp (Over (Spec (.of ℤ))),
      {p : (((Spec (.of ℤ)).asOver (Spec (.of ℤ)) ⟶ G.X) ×
          ((Spec (.of ℤ)).asOver (Spec (.of ℤ)) ⟶ G.X)) // p.1 ≠ p.2} := by
  let Gm : Grp (Over (Spec (.of ℤ))) := multiplicativeGroupScheme ℤ
  let e := multiplicativeGroupMulEquivPoints ℤ ℤ
  have h : Gm.X = multiplicativeGroupUnderlyingScheme ℤ :=
    multiplicativeGroupScheme_X ℤ
  let pMinus : (Spec (.of ℤ)).asOver (Spec (.of ℤ)) ⟶ Gm.X :=
    e (-1 : ℤˣ) ≫ eqToHom h.symm
  let pPlus : (Spec (.of ℤ)).asOver (Spec (.of ℤ)) ⟶ Gm.X :=
    e (1 : ℤˣ) ≫ eqToHom h.symm
  refine ⟨Gm, ⟨(pMinus, pPlus), ?_⟩⟩
  intro hp
  have hu : (-1 : ℤˣ) = 1 :=
    e.injective ((cancel_mono (eqToHom h.symm)).1 hp)
  exact (by decide : (-1 : ℤ) ≠ 1) (congrArg (fun u : ℤˣ => (u : ℤ)) hu)

end AlgebraicGeometry
