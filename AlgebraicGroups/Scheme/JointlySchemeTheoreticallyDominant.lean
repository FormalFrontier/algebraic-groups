/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Joint scheme-theoretic dominance

This file extends scheme-theoretic dominance from one morphism to a family of morphisms. It also
specializes the definition to sets of rational points of a scheme over a field, gives the affine
criterion in terms of an intersection of maximal ideals, and packages all points valued in a field
extension.

## Main results

- `AlgebraicGeometry.JointlySchemeTheoreticallyDominant`
- `AlgebraicGeometry.jointlySchemeTheoreticallyDominant_iff_subscheme`
- `AlgebraicGeometry.jointlySchemeTheoreticallyDominant_iff_iInf_appTop_ker`
- `AlgebraicGeometry.JointlySchemeTheoreticallyDominant.hom_ext`
- `AlgebraicGeometry.JointlySchemeTheoreticallyDominant.over_hom_ext`
- `AlgebraicGeometry.jointlySchemeTheoreticallyDominant_iff_isReduced_and_denseRange`
- `AlgebraicGeometry.RationalPointSet.SchematicallyDense`
- `AlgebraicGeometry.RationalPointSet.schematicallyDense_iff_subscheme`
- `AlgebraicGeometry.RationalPointSet.schematicallyDense_iff_iInf_eval_ker`
- `AlgebraicGeometry.RationalPointSet.schematicallyDense_iff_isReduced_and_dense`
- `AlgebraicGeometry.RationalPointSet.schematicallyDense_iff_locallyEvaluationInjective`
- `AlgebraicGeometry.FieldValuedPoint`
- `AlgebraicGeometry.FieldValuedPoints.SchematicallyDense`
- `AlgebraicGeometry.FieldValuedPoints.SchematicallyDense.over_hom_ext`
- `AlgebraicGeometry.FieldValuedPoints.eval`
- `AlgebraicGeometry.FieldValuedPoints.schematicallyDense_iff_iInf_eval_ker`
- `AlgebraicGeometry.FieldValuedPoints.subschemePoints`
- `AlgebraicGeometry.FieldValuedPoints.schematicallyDense_iff_subscheme`
- `AlgebraicGeometry.FieldValuedPoints.eq_of_schematicallyDense_of_subschemePoints_eq`
- `AlgebraicGeometry.FieldValuedPoints.schematicallyDense_iff_isReduced_and_dense`
- `AlgebraicGeometry.FieldValuedPoints.fieldValuedPointEquivRationalPointBaseChange`
- `AlgebraicGeometry.FieldValuedPoints.schematicallyDense_of_geometricallyReduced_of_dense_baseChange`

The rational points here are morphisms over `Spec K`. They are not identified with all closed
points unless additional hypotheses, such as an algebraically closed base and finite type, are
available.

## References

- J. S. Milne, *Algebraic Groups*, Definition 1.15, Proposition 1.16, and
  Corollary 1.18, for schematic density of field-valued points, reducedness
  and density, and determination of closed subvarieties from their points.
  The proof here uses a family-of-morphisms criterion instead of the reduction
  and descent argument in Proposition 1.16.
- Mathlib's `SchemeTheoreticallyDominant`, ideal-sheaf kernels, and
  `Scheme.IdealSheafData.vanishingIdeal` provide the formal scheme-theoretic
  dominance and reduced-closure constructions generalized to families here.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

namespace AlgebraicGeometry

variable {J : Type v} {X : J → Scheme.{u}} {Y : Scheme.{u}}

/-- A family of scheme morphisms is jointly scheme-theoretically dominant when the intersection
of their ideal-sheaf kernels is trivial. -/
def JointlySchemeTheoreticallyDominant (f : ∀ j, X j ⟶ Y) : Prop :=
  (⨅ j, (f j).ker) = ⊥

/-- A family is jointly scheme-theoretically dominant exactly when every closed subscheme through
which all family members factor is the whole target. -/
theorem jointlySchemeTheoreticallyDominant_iff_subscheme
    (f : ∀ j, X j ⟶ Y) :
    JointlySchemeTheoreticallyDominant f ↔
      ∀ I : Y.IdealSheafData,
        (∀ j, ∃ g : X j ⟶ I.subscheme, g ≫ I.subschemeι = f j) → I = ⊥ := by
  constructor
  · intro hf I hI
    apply le_bot_iff.mp
    rw [← hf]
    refine le_iInf fun j ↦ ?_
    obtain ⟨g, hg⟩ := hI j
    rw [← hg]
    simpa only [I.ker_subschemeι] using g.le_ker_comp I.subschemeι
  · intro h
    let I : Y.IdealSheafData := ⨅ j, (f j).ker
    apply h I
    intro j
    have hIf : I ≤ (f j).ker := iInf_le (fun i ↦ (f i).ker) j
    have hker : I.subschemeι.ker ≤ (f j).ker := by
      simpa only [I.ker_subschemeι] using hIf
    let g := IsClosedImmersion.lift I.subschemeι (f j) hker
    exact ⟨g, IsClosedImmersion.lift_fac _ _ _⟩

/-- On an affine target, joint scheme-theoretic dominance says that the intersection of the
kernels of the induced maps on global sections is zero. -/
theorem jointlySchemeTheoreticallyDominant_iff_iInf_appTop_ker
    (f : ∀ j, X j ⟶ Y) [IsAffine Y] :
    JointlySchemeTheoreticallyDominant f ↔
      (⨅ j, RingHom.ker (f j).appTop.hom) = ⊥ := by
  change (⨅ j, (f j).ker) = ⊥ ↔ _
  rw [← (Scheme.IdealSheafData.equivOfIsAffine (X := Y)).injective.eq_iff]
  simp [Scheme.ker_of_isAffine]

/-- Two morphisms to a separated scheme are equal if they agree after precomposition with a
jointly scheme-theoretically dominant family. -/
theorem JointlySchemeTheoreticallyDominant.hom_ext
    {f : ∀ j, X j ⟶ Y} (hf : JointlySchemeTheoreticallyDominant f)
    {Z : Scheme.{u}} {g h : Y ⟶ Z} [Z.IsSeparated]
    (eq : ∀ j, f j ≫ g = f j ≫ h) : g = h := by
  have hker : (equalizer.ι g h).ker = ⊥ := by
    apply le_bot_iff.mp
    rw [← hf]
    refine le_iInf fun j ↦ ?_
    simpa only [equalizer.lift_ι] using
      (equalizer.lift (f j) (eq j)).le_ker_comp (equalizer.ι g h)
  have : IsIso (equalizer.ι g h) :=
    IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hker
  rw [← cancel_epi (equalizer.ι g h)]
  exact equalizer.condition g h

/-- Relative version of `JointlySchemeTheoreticallyDominant.hom_ext`: two morphisms in an
over-category are equal if their underlying morphisms agree on a jointly scheme-theoretically
dominant family and their common target is separated over the base. -/
theorem JointlySchemeTheoreticallyDominant.over_hom_ext
    {S : Scheme.{u}} {Y Z : Over S} {f : ∀ j, X j ⟶ Y.left}
    (hf : JointlySchemeTheoreticallyDominant f) {g h : Y ⟶ Z} [IsSeparated Z.hom]
    (eq : ∀ j, f j ≫ g.left = f j ≫ h.left) : g = h := by
  let X' (j : J) : Over S := Over.mk (f j ≫ Y.hom)
  let f' (j : J) : X' j ⟶ Y := Over.homMk (f j)
  have eq' (j : J) : f' j ≫ g = f' j ≫ h := by
    apply CostructuredArrow.ext
    exact eq j
  have hker : (equalizer.ι g h).left.ker = ⊥ := by
    apply le_bot_iff.mp
    rw [← hf]
    refine le_iInf fun j ↦ ?_
    simpa only [← Over.comp_left, equalizer.lift_ι, f', Over.homMk_left] using
      (equalizer.lift (f' j) (eq' j)).left.le_ker_comp (equalizer.ι g h).left
  have : IsIso (equalizer.ι g h).left :=
    IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hker
  apply CostructuredArrow.ext
  rw [← cancel_epi (equalizer.ι g h).left]
  exact congr($(equalizer.condition g h).left)

/-- The ideal-sheaf kernel of a quasi-compact morphism from a reduced scheme is radical. -/
lemma Scheme.Hom.ker_radical_of_isReduced_source {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [IsReduced X] :
    f.ker.radical = f.ker := by
  ext U : 2
  rw [Scheme.IdealSheafData.radical_ideal, f.ker_apply]
  exact (Ideal.isRadical_bot.comap (f.app U).hom).radical

/-- The kernel of a quasi-compact morphism from a reduced scheme is the vanishing ideal of the
closure of its range. -/
lemma Scheme.Hom.ker_eq_vanishingIdeal_closure_range {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [IsReduced X] :
    f.ker = Scheme.IdealSheafData.vanishingIdeal (X := Y)
      (Closeds.closure (Set.range f)) := by
  calc
    f.ker = f.ker.radical := f.ker_radical_of_isReduced_source.symm
    _ = Scheme.IdealSheafData.vanishingIdeal f.ker.support :=
      Scheme.IdealSheafData.vanishingIdeal_support.symm
    _ = Scheme.IdealSheafData.vanishingIdeal (Closeds.closure (Set.range f)) := by
      congr 1
      exact Closeds.ext f.support_ker

/-- The intersection of kernels of quasi-compact morphisms from reduced schemes is the vanishing
ideal of the closure of the union of their ranges. -/
lemma iInf_ker_eq_vanishingIdeal_iSup_closure_range
    (f : ∀ j, X j ⟶ Y) [∀ j, QuasiCompact (f j)] [∀ j, IsReduced (X j)] :
    (⨅ j, (f j).ker) = Scheme.IdealSheafData.vanishingIdeal (X := Y)
      (⨆ j, Closeds.closure (Set.range (f j))) := by
  rw [Scheme.IdealSheafData.vanishingIdeal_iSup]
  congr 1
  funext j
  exact (f j).ker_eq_vanishingIdeal_closure_range

/-- A scheme is reduced exactly when its ideal-sheaf nilradical is trivial. -/
lemma isReduced_iff_nilradical_eq_bot (Y : Scheme.{u}) :
    IsReduced Y ↔ Y.nilradical = ⊥ := by
  constructor
  · intro hred
    let _ := hred
    exact Scheme.nilradical_eq_bot
  · intro hnil
    let hred (i : Y.affineCover.I₀) : IsReduced (Y.affineCover.X i) := by
      let hredTop : _root_.IsReduced Γ(Y.affineCover.X i, ⊤) := by
        let U : Y.affineOpens :=
          ⟨(Y.affineCover.f i).opensRange, isAffineOpen_opensRange (Y.affineCover.f i)⟩
        have hU := congrArg (fun I : Y.IdealSheafData ↦ I.ideal U) hnil
        have hredU : _root_.IsReduced Γ(Y, U.1) := by
          rw [← Ideal.isRadical_bot_iff, ← Ideal.radical_eq_iff]
          simpa [Scheme.nilradical] using hU
        let _ := hredU
        exact isReduced_of_injective (IsOpenImmersion.ΓIsoTop (Y.affineCover.f i)).hom.hom
          (IsOpenImmersion.ΓIsoTop
            (Y.affineCover.f i)).commRingCatIsoToRingEquiv.injective
      let _ := hredTop
      exact isReduced_of_isAffine_isReduced (Y.affineCover.X i)
    let _ (i : Y.affineCover.I₀) : IsReduced (Y.affineCover.X i) := hred i
    exact IsReduced.of_openCover Y Y.affineCover

private lemma iSup_closure_eq_closure_iUnion (s : J → Set Y) :
    (⨆ j, Closeds.closure (s j)) = Closeds.closure (⋃ j, s j) := by
  apply le_antisymm
  · refine iSup_le fun j ↦ Closeds.closure_le.mpr ?_
    exact (Set.subset_iUnion s j).trans subset_closure
  · apply Closeds.closure_le.mpr
    refine Set.iUnion_subset fun j ↦ ?_
    exact subset_closure.trans (SetLike.coe_mono (le_iSup (fun j ↦ Closeds.closure (s j)) j))

private lemma iSup_closure_eq_top_iff_dense (s : J → Set Y) :
    (⨆ j, Closeds.closure (s j)) = ⊤ ↔ Dense (⋃ j, s j) := by
  rw [iSup_closure_eq_closure_iUnion, ← SetLike.coe_injective.eq_iff,
    Closeds.coe_top, Closeds.coe_closure, dense_iff_closure_eq]

/-- A family of quasi-compact morphisms from reduced schemes is jointly scheme-theoretically
dominant exactly when the target is reduced and the union of the ranges is dense.
For families of field-valued points this generalizes the reducedness implication
of Milne, *Algebraic Groups*, Proposition 1.16. -/
theorem jointlySchemeTheoreticallyDominant_iff_isReduced_and_denseRange
    (f : ∀ j, X j ⟶ Y) [∀ j, QuasiCompact (f j)] [∀ j, IsReduced (X j)] :
    JointlySchemeTheoreticallyDominant f ↔
      IsReduced Y ∧ Dense (⋃ j, Set.range (f j)) := by
  constructor
  · intro hf
    have hker : Scheme.IdealSheafData.vanishingIdeal (X := Y)
        (⨆ j, Closeds.closure (Set.range (f j))) = ⊥ := by
      rw [← iInf_ker_eq_vanishingIdeal_iSup_closure_range f]
      exact hf
    have hnil : Y.nilradical = ⊥ := by
      apply le_bot_iff.mp
      rw [← Scheme.IdealSheafData.vanishingIdeal_top, ← hker]
      exact Scheme.IdealSheafData.vanishingIdeal_antimono le_top
    have hred := (isReduced_iff_nilradical_eq_bot Y).mpr hnil
    refine ⟨hred, (iSup_closure_eq_top_iff_dense
      (fun j ↦ Set.range (f j))).mp ?_⟩
    let _ := hred
    have hs : (Scheme.IdealSheafData.vanishingIdeal (X := Y)
        (⨆ j, Closeds.closure (Set.range (f j)))).support = ⊤ :=
      Scheme.IdealSheafData.support_eq_top_iff.mpr hker
    apply Closeds.ext
    simpa only [Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_top] using
      congrArg (fun Z : Closeds Y ↦ (Z : Set Y)) hs
  · rintro ⟨hred, hdense⟩
    let _ := hred
    unfold JointlySchemeTheoreticallyDominant
    rw [iInf_ker_eq_vanishingIdeal_iSup_closure_range f,
      (iSup_closure_eq_top_iff_dense (fun j ↦ Set.range (f j))).mpr hdense,
      Scheme.IdealSheafData.vanishingIdeal_top, Scheme.nilradical_eq_bot]

/-- A rational point of a scheme over `K` is a scheme morphism from `Spec K` over `Spec K`. -/
abbrev RationalPoint {K : Type u} [Field K] (Y : Over (Spec (.of K))) :=
  {p : Spec (.of K) ⟶ Y.left // p ≫ Y.hom = 𝟙 _}

namespace RationalPointSet

/-- A set of rational points is schematically dense when its underlying scheme morphisms are
jointly scheme-theoretically dominant. For the full set of rational points this specializes
Milne, *Algebraic Groups*, Definition 1.15 to the base field itself. -/
def SchematicallyDense {K : Type u} [Field K] {Y : Over (Spec (.of K))}
    (S : Set (RationalPoint Y)) : Prop :=
  JointlySchemeTheoreticallyDominant (fun s : S ↦ s.1.1)

/-- A rational point is quasi-compact. In fact, its underlying morphism is a closed immersion
because it is a section over the one-point scheme `Spec K`. -/
lemma quasiCompact {K : Type u} [Field K] {Y : Over (Spec (.of K))}
    (s : RationalPoint Y) : QuasiCompact s.1 := by
  let _ : s.1.IsOver (Spec (.of K)) := ⟨s.2⟩
  have : IsClosedImmersion s.1 := inferInstance
  infer_instance

/-- The subset of the underlying space of a scheme represented by a set of rational points. -/
def underlyingPoints {K : Type u} [Field K] {Y : Over (Spec (.of K))}
    (S : Set (RationalPoint Y)) : Set Y.left :=
  ⋃ s : S, Set.range s.1.1

/-- Membership in the underlying point set represented by a set of rational points. -/
theorem mem_underlyingPoints {K : Type u} [Field K] {Y : Over (Spec (.of K))}
    {S : Set (RationalPoint Y)} {x : Y.left} :
    x ∈ underlyingPoints S ↔ ∃ s : S, x ∈ Set.range s.1.1 := by
  simp [underlyingPoints]

/-- The local-section form of injectivity of the family of evaluations at a set of rational
points. For each open `U`, the component at `s` maps into the sections on the inverse image of
`U`; this ring is canonically isomorphic to `K` when `s` lies in `U` and is the zero ring
otherwise. -/
def LocallyEvaluationInjective {K : Type u} [Field K]
    {Y : Over (Spec (.of K))} (S : Set (RationalPoint Y)) : Prop :=
  ∀ (U : Y.left.Opens) (r : Γ(Y.left, U)),
    (∀ s : S, s.1.1.app U r = 0) → r = 0

/-- Rational points are schematically dense exactly when the scheme is reduced and their
underlying points are topologically dense. In the case of all points valued in the base
field, the forward implication specializes Milne, *Algebraic Groups*, Proposition 1.16. -/
theorem schematicallyDense_iff_isReduced_and_dense
    {K : Type u} [Field K] {Y : Over (Spec (.of K))}
    (S : Set (RationalPoint Y)) :
    SchematicallyDense S ↔ IsReduced Y.left ∧ Dense (underlyingPoints S) := by
  let _ (s : S) : QuasiCompact s.1.1 := quasiCompact s.1
  let _ (s : S) : IsReduced (Spec (.of K)) := inferInstance
  exact jointlySchemeTheoreticallyDominant_iff_isReduced_and_denseRange
    (fun s : S ↦ s.1.1)

lemma locallyEvaluationInjective_of_isReduced_of_dense
    {K : Type u} [Field K] {Y : Over (Spec (.of K))}
    (S : Set (RationalPoint Y)) [IsReduced Y.left]
    (hdense : Dense (underlyingPoints S)) : LocallyEvaluationInjective S := by
  intro U r hr
  rw [← basicOpen_eq_bot_iff r]
  apply (Opens.not_nonempty_iff_eq_bot _).mp
  intro hnonempty
  obtain ⟨x, hxS, hxopen⟩ := hdense.exists_mem_open
    (Y.left.basicOpen r).isOpen hnonempty
  simp only [underlyingPoints, Set.mem_iUnion, Set.mem_range] at hxS
  obtain ⟨s, y, rfl⟩ := hxS
  have hy : y ∈ s.1.1 ⁻¹ᵁ Y.left.basicOpen r := hxopen
  rw [Scheme.preimage_basicOpen, hr s, Scheme.basicOpen_zero] at hy
  exact hy

lemma schematicallyDense_of_locallyEvaluationInjective
    {K : Type u} [Field K] {Y : Over (Spec (.of K))}
    (S : Set (RationalPoint Y)) (h : LocallyEvaluationInjective S) :
    SchematicallyDense S := by
  unfold SchematicallyDense JointlySchemeTheoreticallyDominant
  apply le_bot_iff.mp
  intro U r hr
  have hrzero : r = 0 := h U.1 r fun s ↦ by
    let _ : QuasiCompact s.1.1 := quasiCompact s.1
    have hrs : r ∈ (s.1.1).ker.ideal U :=
      (iInf_le (fun s : S ↦ (s.1.1).ker) s) U hr
    simpa only [Scheme.Hom.ker_apply, RingHom.mem_ker] using hrs
  simp [hrzero]

/-- Schematic density of rational points is equivalent to injectivity of the family of
evaluations on the sections of every open set. -/
theorem schematicallyDense_iff_locallyEvaluationInjective
    {K : Type u} [Field K] {Y : Over (Spec (.of K))}
    (S : Set (RationalPoint Y)) :
    SchematicallyDense S ↔ LocallyEvaluationInjective S := by
  constructor
  · intro h
    have hb := (schematicallyDense_iff_isReduced_and_dense S).mp h
    let _ := hb.1
    exact locallyEvaluationInjective_of_isReduced_of_dense S hb.2
  · exact schematicallyDense_of_locallyEvaluationInjective S

/-- Local injectivity of rational-point evaluations is equivalent to reducedness and ordinary
density of the represented underlying points. -/
theorem locallyEvaluationInjective_iff_isReduced_and_dense
    {K : Type u} [Field K] {Y : Over (Spec (.of K))}
    (S : Set (RationalPoint Y)) :
    LocallyEvaluationInjective S ↔
      IsReduced Y.left ∧ Dense (underlyingPoints S) :=
  (schematicallyDense_iff_locallyEvaluationInjective S).symm.trans
    (schematicallyDense_iff_isReduced_and_dense S)

/-- Schematic density of rational points is the assertion that every closed subscheme containing
all the points is the whole scheme. -/
theorem schematicallyDense_iff_subscheme
    {K : Type u} [Field K] {Y : Over (Spec (.of K))}
    (S : Set (RationalPoint Y)) :
    SchematicallyDense S ↔
      ∀ I : Y.left.IdealSheafData,
        (∀ s : S, ∃ g : Spec (.of K) ⟶ I.subscheme,
          g ≫ I.subschemeι = s.1.1) → I = ⊥ :=
  jointlySchemeTheoreticallyDominant_iff_subscheme _

/-- On an affine scheme, schematic density of rational points is detected by the intersection of
the kernels on global sections. -/
theorem schematicallyDense_iff_iInf_appTop_ker
    {K : Type u} [Field K] {Y : Over (Spec (.of K))}
    (S : Set (RationalPoint Y)) [IsAffine Y.left] :
    SchematicallyDense S ↔
      (⨅ s : S, RingHom.ker s.1.1.appTop.hom) = ⊥ :=
  jointlySchemeTheoreticallyDominant_iff_iInf_appTop_ker _

/-- Evaluation of global sections at a rational point. The codomain is transported from the
global sections of `Spec K` to `K` itself. -/
def eval {K : Type u} [Field K] {Y : Over (Spec (.of K))}
    (s : RationalPoint Y) : Γ(Y.left, ⊤) →+* K :=
  (s.1.appTop ≫ (Scheme.ΓSpecIso (.of K)).hom).hom

/-- Transporting the codomain of a rational-point evaluation from `Γ(Spec K)` to `K` does not
change its kernel. -/
theorem eval_ker {K : Type u} [Field K] {Y : Over (Spec (.of K))}
    (s : RationalPoint Y) :
    RingHom.ker (eval s) = RingHom.ker s.1.appTop.hom := by
  change RingHom.ker (((Scheme.ΓSpecIso (.of K)).hom.hom).comp s.1.appTop.hom) = _
  rw [RingHom.ker_comp_of_injective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).hom).1]

/-- Evaluation at a rational point is surjective because the point is a section of the structure
morphism. -/
theorem eval_surjective {K : Type u} [Field K] {Y : Over (Spec (.of K))}
    (s : RationalPoint Y) : Function.Surjective (eval s) := by
  intro x
  refine ⟨Y.hom.appTop ((Scheme.ΓSpecIso (.of K)).inv x), ?_⟩
  change (Y.hom.appTop ≫ s.1.appTop ≫ (Scheme.ΓSpecIso (.of K)).hom)
    ((Scheme.ΓSpecIso (.of K)).inv x) = x
  rw [← Category.assoc, ← Scheme.Hom.comp_appTop, s.2, Scheme.Hom.id_appTop]
  simp

/-- The kernel of evaluation at a rational point is a maximal ideal of the global sections. -/
theorem eval_ker_isMaximal {K : Type u} [Field K] {Y : Over (Spec (.of K))}
    (s : RationalPoint Y) : (RingHom.ker (eval s)).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (eval s) (eval_surjective s)

/-- On an affine scheme, rational points are schematically dense exactly when the intersection of
their maximal evaluation ideals is zero. -/
theorem schematicallyDense_iff_iInf_eval_ker
    {K : Type u} [Field K] {Y : Over (Spec (.of K))}
    (S : Set (RationalPoint Y)) [IsAffine Y.left] :
    SchematicallyDense S ↔ (⨅ s : S, RingHom.ker (eval s.1)) = ⊥ := by
  rw [schematicallyDense_iff_iInf_appTop_ker]
  simp_rw [eval_ker]

end RationalPointSet

/-- A point of a scheme over `K` valued in a field extension `L / K`. -/
abbrev FieldValuedPoint {K L : Type u} [Field K] [Field L] [Algebra K L]
    (Y : Over (Spec (.of K))) :=
  {p : Spec (.of L) ⟶ Y.left //
    p ≫ Y.hom = Spec.map (CommRingCat.ofHom (algebraMap K L))}

namespace FieldValuedPoints

/-- All `L`-valued points are schematically dense when their underlying scheme morphisms are
jointly scheme-theoretically dominant. This represents Milne,
*Algebraic Groups*, Definition 1.15, using ideal-sheaf kernels. -/
def SchematicallyDense {K L : Type u} [Field K] [Field L] [Algebra K L]
    {Y : Over (Spec (.of K))} : Prop :=
  JointlySchemeTheoreticallyDominant
    (fun p : FieldValuedPoint (L := L) Y ↦ p.1)

/-- Two morphisms to a separated target are equal if they agree on all extension-field-valued
points and those points are schematically dense. -/
theorem SchematicallyDense.over_hom_ext
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {Y Z : Over (Spec (.of K))} (hY : SchematicallyDense (Y := Y) (L := L))
    {f g : Y ⟶ Z} [IsSeparated Z.hom]
    (h : ∀ p : FieldValuedPoint (L := L) Y,
      p.1 ≫ f.left = p.1 ≫ g.left) : f = g :=
  JointlySchemeTheoreticallyDominant.over_hom_ext hY h

/-- Evaluation of global sections at an extension-field-valued point. The codomain is transported
from the global sections of `Spec L` to `L` itself. -/
def eval {K L : Type u} [Field K] [Field L] [Algebra K L]
    {Y : Over (Spec (.of K))} (p : FieldValuedPoint (L := L) Y) :
    Γ(Y.left, ⊤) →+* L :=
  (p.1.appTop ≫ (Scheme.ΓSpecIso (.of L)).hom).hom

/-- Transporting the codomain of an extension-field-valued-point evaluation from `Γ(Spec L)` to
`L` does not change its kernel. -/
theorem eval_ker {K L : Type u} [Field K] [Field L] [Algebra K L]
    {Y : Over (Spec (.of K))} (p : FieldValuedPoint (L := L) Y) :
    RingHom.ker (eval p) = RingHom.ker p.1.appTop.hom := by
  change RingHom.ker (((Scheme.ΓSpecIso (.of L)).hom.hom).comp p.1.appTop.hom) = _
  rw [RingHom.ker_comp_of_injective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of L)).hom).1]

/-- On an affine scheme, schematic density of all extension-field-valued points is detected by the
intersection of their evaluation kernels on global sections. -/
theorem schematicallyDense_iff_iInf_eval_ker
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {Y : Over (Spec (.of K))} [IsAffine Y.left] :
    SchematicallyDense (Y := Y) (L := L) ↔
      (⨅ p : FieldValuedPoint (L := L) Y, RingHom.ker (eval p)) = ⊥ := by
  rw [SchematicallyDense, jointlySchemeTheoreticallyDominant_iff_iInf_appTop_ker]
  simp_rw [eval_ker]

/-- The extension-field-valued points of a closed subscheme, regarded as a subset of the
extension-field-valued points of the ambient scheme. -/
def subschemePoints
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {Y : Over (Spec (.of K))} (I : Y.left.IdealSheafData) :
    Set (FieldValuedPoint (L := L) Y) :=
  {p | ∃ q : FieldValuedPoint (L := L)
      (Over.mk (I.subschemeι ≫ Y.hom)), q.1 ≫ I.subschemeι = p.1}

/-- Schematically dense closed subschemes with the same extension-field-valued points inside an
ambient scheme are equal. This is the point-determination argument of Milne,
*Algebraic Groups*, Corollary 1.18, without its geometric-reducedness or
separably-closed-field hypotheses: schematic density is assumed directly. -/
theorem eq_of_schematicallyDense_of_subschemePoints_eq
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {Y : Over (Spec (.of K))} (I J : Y.left.IdealSheafData)
    (hI : SchematicallyDense
      (Y := Over.mk (I.subschemeι ≫ Y.hom)) (L := L))
    (hJ : SchematicallyDense
      (Y := Over.mk (J.subschemeι ≫ Y.hom)) (L := L))
    (h : subschemePoints (L := L) I = subschemePoints (L := L) J) :
    I = J := by
  have le_of_points_subset
      (A B : Y.left.IdealSheafData)
      (hA : SchematicallyDense
        (Y := Over.mk (A.subschemeι ≫ Y.hom)) (L := L))
      (hAB : subschemePoints (L := L) A ⊆ subschemePoints (L := L) B) :
      B ≤ A := by
    rw [← A.ker_subschemeι, ← Scheme.IdealSheafData.map_bot]
    rw [Scheme.IdealSheafData.le_map_iff_comap_le]
    unfold SchematicallyDense JointlySchemeTheoreticallyDominant at hA
    rw [← hA]
    refine le_iInf fun p ↦ ?_
    rw [← Scheme.IdealSheafData.le_map_iff_comap_le,
      ← Scheme.Hom.ker_comp]
    let pY : FieldValuedPoint (L := L) Y :=
      ⟨p.1 ≫ A.subschemeι, by
        rw [Category.assoc]
        exact p.2⟩
    have hpY : pY ∈ subschemePoints (L := L) A := ⟨p, rfl⟩
    obtain ⟨q, hq⟩ := hAB hpY
    simpa only [B.ker_subschemeι, hq] using q.1.le_ker_comp B.subschemeι
  apply le_antisymm
  · exact le_of_points_subset J I hJ (Set.Subset.rfl.trans_eq h.symm)
  · exact le_of_points_subset I J hI (Set.Subset.rfl.trans_eq h)

/-- Field-valued points are schematically dense exactly when every closed subscheme containing all
of them is the whole scheme. The factorization point is explicitly a morphism over the base
field. This is Milne, *Algebraic Groups*, Definition 1.15. -/
theorem schematicallyDense_iff_subscheme
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {Y : Over (Spec (.of K))} :
    SchematicallyDense (Y := Y) (L := L) ↔
      ∀ I : Y.left.IdealSheafData,
        (∀ p : FieldValuedPoint (L := L) Y,
          ∃ q : FieldValuedPoint (L := L)
              (Over.mk (I.subschemeι ≫ Y.hom)),
            q.1 ≫ I.subschemeι = p.1) → I = ⊥ := by
  rw [SchematicallyDense,
    jointlySchemeTheoreticallyDominant_iff_subscheme]
  constructor
  · intro h I hI
    apply h I
    intro p
    obtain ⟨q, hq⟩ := hI p
    exact ⟨q.1, hq⟩
  · intro h I hI
    apply h I
    intro p
    obtain ⟨q, hq⟩ := hI p
    refine ⟨⟨q, ?_⟩, hq⟩
    change q ≫ (I.subschemeι ≫ Y.hom) = _
    rw [← Category.assoc, hq, p.2]

/-- The underlying points represented by all points valued in an extension field. -/
def underlyingPoints {K L : Type u} [Field K] [Field L] [Algebra K L]
    {Y : Over (Spec (.of K))} : Set Y.left :=
  ⋃ p : FieldValuedPoint (L := L) Y, Set.range p.1

/-- Field-valued points are schematically dense exactly when the target is reduced and their
underlying points are topologically dense. In particular, schematic density implies reducedness
as in Milne, *Algebraic Groups*, Proposition 1.16; the converse here assumes reducedness and
density on the original scheme, rather than geometric reducedness and density after base change. -/
theorem schematicallyDense_iff_isReduced_and_dense
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {Y : Over (Spec (.of K))} :
    SchematicallyDense (Y := Y) (L := L) ↔
      IsReduced Y.left ∧ Dense (underlyingPoints (Y := Y) (L := L)) := by
  let _ (p : FieldValuedPoint (L := L) Y) : QuasiCompact p.1 :=
    ⟨fun _ _ _ ↦ Set.Subsingleton.isCompact fun _ _ _ _ ↦ Subsingleton.elim _ _⟩
  let _ (p : FieldValuedPoint (L := L) Y) : IsReduced (Spec (.of L)) := inferInstance
  exact jointlySchemeTheoreticallyDominant_iff_isReduced_and_denseRange
    (fun p : FieldValuedPoint (L := L) Y ↦ p.1)

/-- Base change of a scheme over `K` to an extension field `L`. -/
abbrev baseChange {K L : Type u} [Field K] [Field L] [Algebra K L]
    (Y : Over (Spec (.of K))) : Over (Spec (.of L)) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj Y

/-- An extension-field-valued point gives a rational point after scalar extension by the universal
property of the pullback. -/
def toBaseChangeRationalPoint {K L : Type u} [Field K] [Field L] [Algebra K L]
    {Y : Over (Spec (.of K))} (p : FieldValuedPoint (L := L) Y) :
    RationalPoint (baseChange (L := L) Y) :=
  ⟨pullback.lift p.1 (𝟙 _)
      (by simpa using p.2), by
    exact pullback.lift_snd _ _ _⟩

/-- A rational point of the base change gives an extension-field-valued point of the original
scheme by composing with the base-change projection. -/
def ofBaseChangeRationalPoint {K L : Type u} [Field K] [Field L] [Algebra K L]
    {Y : Over (Spec (.of K))} (q : RationalPoint (baseChange (L := L) Y)) :
    FieldValuedPoint (L := L) Y :=
  ⟨q.1 ≫ pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (algebraMap K L))), by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    simpa [baseChange] using congrArg
      (fun f ↦ f ≫ Spec.map (CommRingCat.ofHom (algebraMap K L))) q.2⟩

/-- Points of a scheme valued in an extension field are equivalent to rational points of its base
change to that field. -/
def fieldValuedPointEquivRationalPointBaseChange
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {Y : Over (Spec (.of K))} :
    FieldValuedPoint (L := L) Y ≃ RationalPoint (baseChange (L := L) Y) where
  toFun := toBaseChangeRationalPoint
  invFun := ofBaseChangeRationalPoint
  left_inv p := by
    apply Subtype.ext
    exact pullback.lift_fst _ _ _
  right_inv q := by
    apply Subtype.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · dsimp only [toBaseChangeRationalPoint]
      rw [pullback.lift_snd]
      simpa [baseChange] using q.2.symm

/-- Topological density of the rational points after scalar extension implies topological density
of the represented extension-field-valued points on the original scheme. -/
theorem dense_underlyingPoints_of_dense_baseChange
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {Y : Over (Spec (.of K))}
    (h : Dense (RationalPointSet.underlyingPoints
      (Set.univ : Set (RationalPoint (baseChange (L := L) Y))))) :
    Dense (underlyingPoints (Y := Y) (L := L)) := by
  let g : Spec (.of L) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K L))
  let π : (baseChange (L := L) Y).left ⟶ Y.left := pullback.fst Y.hom g
  have hg : Surjective g := by
    dsimp [g]
    infer_instance
  let _ : Surjective g := hg
  let _ : Surjective π := by
    dsimp [π, baseChange]
    infer_instance
  apply π.surjective.denseRange.dense_of_mapsTo π.continuous h
  intro x hx
  simp only [RationalPointSet.underlyingPoints, Set.mem_iUnion, Set.mem_range] at hx
  obtain ⟨q, t, rfl⟩ := hx
  simp only [underlyingPoints, Set.mem_iUnion, Set.mem_range]
  exact ⟨ofBaseChangeRationalPoint q, t, rfl⟩

/-- If a scheme is geometrically reduced and its rational points become topologically dense after
scalar extension, then its extension-field-valued points are schematically dense. This is the second
implication of Milne, *Algebraic Groups*, Proposition 1.16; unlike the source's descent proof,
the argument transports density from the base change and applies a reduced-dense-points criterion.
No finite-type hypothesis is needed here. -/
theorem schematicallyDense_of_geometricallyReduced_of_dense_baseChange
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {Y : Over (Spec (.of K))} [GeometricallyReduced Y.hom]
    (h : Dense (RationalPointSet.underlyingPoints
      (Set.univ : Set (RationalPoint (baseChange (L := L) Y))))) :
    SchematicallyDense (Y := Y) (L := L) := by
  apply (schematicallyDense_iff_isReduced_and_dense (Y := Y) (L := L)).2
  constructor
  · let _ : Flat Y.hom := by infer_instance
    exact GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian Y.hom
  · exact dense_underlyingPoints_of_dense_baseChange h

end FieldValuedPoints

end AlgebraicGeometry
