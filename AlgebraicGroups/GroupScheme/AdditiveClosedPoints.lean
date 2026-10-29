/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.Additive
public import AlgebraicGroups.GroupScheme.ClosedPoints
public import Mathlib.Topology.Constructions
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Separation.Hausdorff

/-!
# Closed points of the additive group scheme

Over an algebraically closed field, field coordinates identify the closed-point
subspace of the additive group scheme with the cofinite topology. The comparison
composes the additive group scheme's point equivalence, precomposition by the
identity-underlying isomorphism of terminal test objects, and the rational-point/
closed-point group equivalence. It sends addition to multiplication in the group
explicitly supplied by `groupSchemeClosedPointsGroup`.

The standard polynomial presentation of the symmetric-algebra coordinate ring
identifies proper closed-set pullbacks with subsets of finite root sets.
Multiplication is not continuous for the ordinary product of the closed-point
subspace topologies. Indeed, the cofinite field-coordinate homeomorphism gives a
nontrivial irreducible T₀ space. Scheme-induced inversion is continuous for the
same transported group structure, independently of multiplication. If
multiplication were continuous, the topological-group separation theorems would
make this space Hausdorff, a contradiction.

## References

- J. S. Milne, *Algebraic Groups* (2017), items 1.7–1.8, for the closed-point
  group and the distinction from a topological group.
- `AlgebraicGroups.GroupScheme.Additive` and `AlgebraicGroups.GroupScheme.ClosedPoints`,
  for additive-group points, the transported closed-point group, and continuity
  of scheme-induced inversion.
- Mathlib, `CategoryTheory.yonedaMon`, `CategoryTheory.Over.isoMk`,
  `Polynomial.finite_setOfPred_isRoot`, `Homeomorph.irreducibleSpace_iff`,
  `IsTopologicalGroup.regularSpace`, and `not_preirreducible_nontrivial_t2`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

/-- The group-object structure selected by the additive group scheme. -/
local instance (K : Type u) [CommRing K] :
    GrpObj (Over.mk (additiveGroupScheme K).X.hom) :=
  (additiveGroupScheme K).grp

/-- Field elements, with addition written multiplicatively, identify with the
closed-point group of the additive group scheme. The target multiplication is
explicitly the one transported by `groupSchemeClosedPointsGroup`. -/
def additiveGroupMulEquivClosedPoints (K : Type u) [Field K] [IsAlgClosed K] :
    @MulEquiv (Multiplicative K) (closedPoints (additiveGroupScheme K).X.left)
      inferInstance
      (groupSchemeClosedPointsGroup (additiveGroupScheme K).X.hom).toMul := by
  letI := groupSchemeClosedPointsGroup (additiveGroupScheme K).X.hom
  let e : 𝟙_ (Over (Spec (.of K))) ≅ (Spec (.of K)).asOver (Spec (.of K)) :=
    Over.isoMk (Iso.refl _) (by
      calc
        _ = ((Spec (.of K)).asOver (Spec (.of K))).hom := Category.id_comp _
        _ = _ := by
          change Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 (Spec (.of K))
          rw [Algebra.algebraMap_self, CommRingCat.ofHom_id]
          exact Spec.map_id _)
  exact ((additiveGroupMulEquivPoints K K).trans
    (((yonedaMon.obj (.mk (additiveGroupScheme K).X)).mapIso
      e.op).monCatIsoToMulEquiv)).trans
        (groupSchemePointMulEquivClosedPoint (additiveGroupScheme K).X.hom)

/-- The closed-point comparison evaluates the original additive-group point at
its unique field-valued source point. -/
@[simp]
theorem additiveGroupMulEquivClosedPoints_apply_value
    (K : Type u) [Field K] [IsAlgClosed K] (a : K) :
    (additiveGroupMulEquivClosedPoints K (Multiplicative.ofAdd a)).1 =
      (additiveGroupMulEquivPoints K K (Multiplicative.ofAdd a)).left
        (IsLocalRing.closedPoint K) := by
  let := groupSchemeClosedPointsGroup (additiveGroupScheme K).X.hom
  let e : 𝟙_ (Over (Spec (.of K))) ≅ (Spec (.of K)).asOver (Spec (.of K)) :=
    Over.isoMk (Iso.refl _) (by
      calc
        _ = ((Spec (.of K)).asOver (Spec (.of K))).hom := Category.id_comp _
        _ = _ := by
          change Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 (Spec (.of K))
          rw [Algebra.algebraMap_self, CommRingCat.ofHom_id]
          exact Spec.map_id _)
  change (groupSchemePointMulEquivClosedPoint (additiveGroupScheme K).X.hom
    (e.hom ≫
      additiveGroupMulEquivPoints K K (Multiplicative.ofAdd a))).1 = _
  rw [groupSchemePointMulEquivClosedPoint_apply,
    groupSchemePointEquivClosedPoint_apply_value]
  have h :
      ((e.hom ≫
        additiveGroupMulEquivPoints K K (Multiplicative.ofAdd a)).left :
          Spec (.of K) ⟶ Spec (.of (additiveGroupCoordinateRing K))) =
      (additiveGroupMulEquivPoints K K (Multiplicative.ofAdd a)).left := by
    change (𝟙 (Spec (.of K))) ≫
      (additiveGroupMulEquivPoints K K (Multiplicative.ofAdd a)).left = _
    exact Category.id_comp _
  exact congrArg
    (fun p : Spec (.of K) ⟶ Spec (.of (additiveGroupCoordinateRing K)) =>
      p (IsLocalRing.closedPoint K)) h

private lemma additiveGroupMulEquivAlgHom_apply_eq_eval
    (K : Type u) [Field K] (a : K) (q : additiveGroupCoordinateRing K) :
    (additiveGroupMulEquivAlgHom K K (Multiplicative.ofAdd a)).ofConv q =
      (additiveGroupCoordinateAlgEquiv K q).eval a := by
  let e := additiveGroupCoordinateAlgEquiv K
  let f := (additiveGroupMulEquivAlgHom K K (Multiplicative.ofAdd a)).ofConv
  have hX : e.symm Polynomial.X = additiveGroupCoordinate K := by
    apply e.injective
    simp [e]
  have hf : f.comp e.symm.toAlgHom = Polynomial.aeval a := by
    apply Polynomial.algHom_ext
    change f (e.symm Polynomial.X) = Polynomial.aeval a Polynomial.X
    rw [hX]
    exact (additiveGroupMulEquivAlgHom_coordinate K K a).trans
      (Polynomial.aeval_X a).symm
  calc
    f q = (f.comp e.symm.toAlgHom) (e q) := by simp
    _ = Polynomial.aeval a (e q) := congrArg (fun g => g (e q)) hf
    _ = (e q).eval a := congrFun (Polynomial.coe_aeval_eq_eval a) (e q)

private lemma additiveGroupMulEquivClosedPoints_mem_asIdeal
    (K : Type u) [Field K] [IsAlgClosed K] (a : K)
    (q : additiveGroupCoordinateRing K) :
    q ∈ (additiveGroupMulEquivClosedPoints K (Multiplicative.ofAdd a)).1.asIdeal ↔
      (additiveGroupCoordinateAlgEquiv K q).eval a = 0 := by
  let f : additiveGroupCoordinateRing K →+* K :=
    (additiveGroupMulEquivAlgHom K K (Multiplicative.ofAdd a)).ofConv.toRingHom
  let x : Spec (.of K) := IsLocalRing.closedPoint K
  have hvalue :
      ((additiveGroupMulEquivClosedPoints K (Multiplicative.ofAdd a)).1 :
          PrimeSpectrum (additiveGroupCoordinateRing K)) =
        ((additiveGroupMulEquivPoints K K (Multiplicative.ofAdd a)).left x :
          PrimeSpectrum (additiveGroupCoordinateRing K)) :=
    additiveGroupMulEquivClosedPoints_apply_value K a
  have hleft : (additiveGroupMulEquivPoints K K (Multiplicative.ofAdd a)).left =
      Spec.map (CommRingCat.ofHom f) :=
    additiveGroupMulEquivPoints_apply_left K K a
  have hmap :
      ((Spec.map (CommRingCat.ofHom f)) x :
          PrimeSpectrum (additiveGroupCoordinateRing K)) =
        PrimeSpectrum.comap f (IsLocalRing.closedPoint K) :=
    Spec.map_apply (CommRingCat.ofHom f) x
  have hpoint :
      ((additiveGroupMulEquivClosedPoints K (Multiplicative.ofAdd a)).1 :
          PrimeSpectrum (additiveGroupCoordinateRing K)) =
        PrimeSpectrum.comap f (IsLocalRing.closedPoint K) :=
    hvalue.trans ((congrArg
      (fun p : Spec (.of K) ⟶ Spec (.of (additiveGroupCoordinateRing K)) =>
        (p x : PrimeSpectrum (additiveGroupCoordinateRing K))) hleft).trans hmap)
  rw [hpoint]
  change (additiveGroupMulEquivAlgHom K K (Multiplicative.ofAdd a)).ofConv q ∈
      IsLocalRing.maximalIdeal K ↔ _
  rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot,
    additiveGroupMulEquivAlgHom_apply_eq_eval]

private def additiveGroupClosedPointsEquiv
    (K : Type u) [Field K] [IsAlgClosed K] :
    CofiniteTopology K ≃ closedPoints (additiveGroupScheme K).X.left := by
  letI := groupSchemeClosedPointsGroup (additiveGroupScheme K).X.hom
  exact (CofiniteTopology.of : K ≃ CofiniteTopology K).symm.trans
    (Multiplicative.ofAdd.trans (additiveGroupMulEquivClosedPoints K).toEquiv)

private lemma additiveGroupClosedPointsEquiv_apply
    (K : Type u) [Field K] [IsAlgClosed K] (a : CofiniteTopology K) :
    additiveGroupClosedPointsEquiv K a =
      additiveGroupMulEquivClosedPoints K
        (Multiplicative.ofAdd (CofiniteTopology.of.symm a)) :=
  rfl

private lemma additiveGroupClosedPointsEquiv_continuous_val
    (K : Type u) [Field K] [IsAlgClosed K] :
    Continuous (fun a : CofiniteTopology K => (additiveGroupClosedPointsEquiv K a).1) := by
  apply continuous_iff_isClosed.mpr
  intro Z hZ
  obtain ⟨I, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal Z).mp hZ
  by_cases hI : I = ⊥
  · subst I
    apply CofiniteTopology.isClosed_iff.mpr
    left
    apply Set.eq_univ_iff_forall.mpr
    intro a
    change (⊥ : Ideal (additiveGroupCoordinateRing K)) ≤
      (additiveGroupClosedPointsEquiv K a).1.asIdeal
    exact bot_le
  · obtain ⟨q, hqI, hq⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    have hq' : additiveGroupCoordinateAlgEquiv K q ≠ 0 := by
      intro h
      exact hq ((additiveGroupCoordinateAlgEquiv K).injective
        (h.trans (map_zero (additiveGroupCoordinateAlgEquiv K)).symm))
    apply CofiniteTopology.isClosed_iff.mpr
    right
    refine ((Polynomial.finite_setOfPred_isRoot hq').image
      (CofiniteTopology.of : K → CofiniteTopology K)).subset ?_
    intro a ha
    have hqa : q ∈ (additiveGroupClosedPointsEquiv K a).1.asIdeal := ha hqI
    rw [additiveGroupClosedPointsEquiv_apply] at hqa
    refine ⟨CofiniteTopology.of.symm a, ?_, CofiniteTopology.of.apply_symm_apply a⟩
    exact (additiveGroupMulEquivClosedPoints_mem_asIdeal K
      (CofiniteTopology.of.symm a) q).mp hqa

private lemma additiveGroupClosedPointsEquiv_isClosedMap
    (K : Type u) [Field K] [IsAlgClosed K] :
    IsClosedMap (additiveGroupClosedPointsEquiv K) := by
  let : T1Space (closedPoints (additiveGroupScheme K).X.left) :=
    ⟨fun x => by
      have hx : IsClosed ((Subtype.val : closedPoints (additiveGroupScheme K).X.left →
          (additiveGroupScheme K).X.left) ⁻¹' {x.1}) :=
        x.2.preimage continuous_subtype_val
      convert hx using 1
      ext y
      exact Subtype.ext_iff⟩
  intro s hs
  rcases CofiniteTopology.isClosed_iff.mp hs with rfl | hs
  · rw [Set.image_univ, (additiveGroupClosedPointsEquiv K).surjective.range_eq]
    exact isClosed_univ
  · exact (hs.image (additiveGroupClosedPointsEquiv K)).isClosed

/-- Field coordinates identify the closed-point subspace of the additive group
scheme with the cofinite topology, as in Milne, *Algebraic Groups* (2017),
item 1.7. The underlying bijection is the additive-group point comparison. -/
def additiveGroupClosedPointsHomeomorph
    (K : Type u) [Field K] [IsAlgClosed K] :
    CofiniteTopology K ≃ₜ closedPoints (additiveGroupScheme K).X.left := by
  letI := groupSchemeClosedPointsGroup (additiveGroupScheme K).X.hom
  exact Equiv.toHomeomorphOfContinuousClosed
    ((CofiniteTopology.of : K ≃ CofiniteTopology K).symm.trans
      (Multiplicative.ofAdd.trans (additiveGroupMulEquivClosedPoints K).toEquiv))
    (by exact continuous_induced_rng.mpr (additiveGroupClosedPointsEquiv_continuous_val K))
    (by exact additiveGroupClosedPointsEquiv_isClosedMap K)

/-- The closed-point homeomorphism sends a field coordinate to the closed point
of its additive-group-valued point. -/
@[simp]
theorem additiveGroupClosedPointsHomeomorph_apply
    (K : Type u) [Field K] [IsAlgClosed K] (a : K) :
    additiveGroupClosedPointsHomeomorph K (CofiniteTopology.of a) =
      additiveGroupMulEquivClosedPoints K (Multiplicative.ofAdd a) :=
  rfl

/-- Addition in field coordinates is the transported closed-point group law. -/
theorem additiveGroupClosedPointsHomeomorph_add
    (K : Type u) [Field K] [IsAlgClosed K] (a b : K) :
    additiveGroupClosedPointsHomeomorph K (CofiniteTopology.of (a + b)) =
      @Mul.mul _ (groupSchemeClosedPointsGroup (additiveGroupScheme K).X.hom).toMul
        (additiveGroupClosedPointsHomeomorph K (CofiniteTopology.of a))
        (additiveGroupClosedPointsHomeomorph K (CofiniteTopology.of b)) := by
  let := groupSchemeClosedPointsGroup (additiveGroupScheme K).X.hom
  rw [additiveGroupClosedPointsHomeomorph_apply,
    additiveGroupClosedPointsHomeomorph_apply,
    additiveGroupClosedPointsHomeomorph_apply]
  exact (additiveGroupMulEquivClosedPoints K).map_mul
    (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)

/-- Multiplication in the closed-point group of the additive group scheme is
not continuous for the ordinary product of the closed-point subspace
topologies. This gives an example of Milne's distinction between a closed-point
group and a topological group in *Algebraic Groups* (2017), item 1.7. -/
theorem additiveGroupClosedPoints_not_continuous_mul
    (K : Type u) [Field K] [IsAlgClosed K] :
    ¬ Continuous
      (fun p :
        ↥(closedPoints (additiveGroupScheme K).X.left) ×
          ↥(closedPoints (additiveGroupScheme K).X.left) =>
        @Mul.mul _ (groupSchemeClosedPointsGroup (additiveGroupScheme K).X.hom).toMul
          p.1 p.2) := by
  let := groupSchemeClosedPointsGroup (additiveGroupScheme K).X.hom
  let H := additiveGroupClosedPointsHomeomorph K
  let : Nontrivial (closedPoints (additiveGroupScheme K).X.left) := by
    refine ⟨⟨H (CofiniteTopology.of (0 : K)), H (CofiniteTopology.of (1 : K)), ?_⟩⟩
    intro h
    exact zero_ne_one ((CofiniteTopology.of : K ≃ CofiniteTopology K).injective
      (H.injective h))
  let : IrreducibleSpace (closedPoints (additiveGroupScheme K).X.left) :=
    H.irreducibleSpace_iff.mp inferInstance
  let : T0Space (closedPoints (additiveGroupScheme K).X.left) := H.t0Space
  intro hmul
  let : ContinuousMul (closedPoints (additiveGroupScheme K).X.left) :=
    { continuous_mul := hmul }
  let : ContinuousInv (closedPoints (additiveGroupScheme K).X.left) :=
    { continuous_inv :=
        groupSchemeClosedPoints_continuous_inv (additiveGroupScheme K).X.hom }
  let : IsTopologicalGroup (closedPoints (additiveGroupScheme K).X.left) :=
    { toContinuousMul := inferInstance
      toContinuousInv := inferInstance }
  let : RegularSpace (closedPoints (additiveGroupScheme K).X.left) := inferInstance
  let : T2Space (closedPoints (additiveGroupScheme K).X.left) := inferInstance
  exact not_preirreducible_nontrivial_t2
    (closedPoints (additiveGroupScheme K).X.left)

end AlgebraicGeometry
