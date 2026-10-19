/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.DiagonalProduct
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.Tactic.NormNum

/-!
# Two sections of the kernel of a diagonal projection

The projection `D₂ → Gₘ` over `Spec ℤ` has the two sections with unit
coordinates `(1, 1)` and `(1, -1)` in its kernel. We calculate their images
using the diagonal point equivalence, and lift the original scheme maps
through any supplied pullback square. The chosen categorical pullback is
also treated explicitly.

The test scheme `(Spec ℤ).asOver (Spec ℤ)` has structure map `Spec.map` of
the self-algebra map. Its comparison with the terminal object is proved,
not used as a definitional identification. The statements require no group
or monoid dictionary on the kernel scheme.

## References

* J. S. Milne, *Algebraic Groups* (2017), §2.2 and §2.9, for the
  multiplicative and diagonal groups; §12.d for the diagonal product.
* AlgebraicGroups, `GroupScheme.Diagonal`, `GroupScheme.Multiplicative`
  and `GroupScheme.DiagonalProduct`, for the coordinate rings, group
  objects, point equivalences and projection calculation.
* Mathlib, `AlgebraicGeometry.Group.Affine`, for affine group points;
  `CategoryTheory.Monoidal.Cartesian.Over` and the pullback API.

Written by Formal Frontier Agents with AI assistance, following these
AlgebraicGroups and Mathlib formalizations.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

private abbrev integerBase : Scheme := Spec (.of ℤ)

local instance : CartesianMonoidalCategory (Over (Spec (.of ℤ))) :=
  Over.cartesianMonoidalCategory (Spec (.of ℤ))

private abbrev integerDomain : Over integerBase := integerBase.asOver integerBase
private abbrev integerDiagonal := diagonalGroupScheme ℤ (Fin 2)
private abbrev integerMultiplicative := (multiplicativeGroupScheme ℤ).toMon

local instance : GrpObj (diagonalGroupScheme ℤ (Fin 2)).X :=
  (diagonalGroupScheme ℤ (Fin 2)).grp
local instance : MonObj (multiplicativeGroupScheme ℤ).toMon.X :=
  (multiplicativeGroupScheme ℤ).toMon.mon

private abbrev integerProjection : integerDiagonal.X ⟶ integerMultiplicative.X :=
  (diagonalGroupProjection ℤ (Fin 2) (0 : Fin 2)).hom.hom

local instance : IsMonHom (diagonalGroupProjection ℤ (Fin 2) (0 : Fin 2)).hom.hom :=
  (diagonalGroupProjection ℤ (Fin 2) (0 : Fin 2)).hom.isMonHom_hom

private abbrev positivePoint : integerDomain ⟶ integerDiagonal.X :=
  diagonalGroupUnitsEquivPoints ℤ (Fin 2) ℤ (fun _ => 1)

private abbrev negativePoint : integerDomain ⟶ integerDiagonal.X :=
  diagonalGroupUnitsEquivPoints ℤ (Fin 2) ℤ (fun k => if k = 0 then 1 else -1)

/-- The structure map of the self-algebra test scheme is the identity. -/
theorem integerSpec_asOver_hom :
    ((Spec (.of ℤ)).asOver (Spec (.of ℤ))).hom = 𝟙 (Spec (.of ℤ)) := by
  change Spec.map (CommRingCat.ofHom (algebraMap ℤ ℤ)) = 𝟙 _
  rw [Algebra.algebraMap_self, CommRingCat.ofHom_id]
  exact Spec.map_id _

private theorem integerPoint_projection (v : Fin 2 → ℤˣ) :
    diagonalGroupUnitsEquivPoints ℤ (Fin 2) ℤ v ≫ integerProjection =
      multiplicativeGroupMulEquivPoints ℤ ℤ (v 0) := by
  change diagonalGroupMulEquivPoints ℤ (Fin 2) ℤ
    ((Matrix.DiagonalGroup.unitsEquiv :
      Matrix.DiagonalGroup (Fin 2) ℤ ≃* (Fin 2 → ℤˣ)).symm v) ≫
        integerProjection = _
  simpa only [MulEquiv.apply_symm_apply] using
    diagonalGroupProjection_point ℤ (Fin 2) ℤ
      ((Matrix.DiagonalGroup.unitsEquiv :
        Matrix.DiagonalGroup (Fin 2) ℤ ≃* (Fin 2 → ℤˣ)).symm v) (0 : Fin 2)

/-- The all-one tuple is the hom-unit, with its original test-scheme domain. -/
theorem diagonalGroup_integerPoint_one :
    diagonalGroupUnitsEquivPoints ℤ (Fin 2) ℤ (fun _ => 1) =
      toUnit ((Spec (.of ℤ)).asOver (Spec (.of ℤ))) ≫
        η[(diagonalGroupScheme ℤ (Fin 2)).X] := by
  change (diagonalGroupUnitsEquivPoints ℤ (Fin 2) ℤ)
    (1 : Fin 2 → ℤˣ) = _
  rw [map_one, Hom.one_def]

/-- On the original scheme `Spec ℤ`, the all-one point is the unit section. -/
theorem diagonalGroup_integerPoint_one_left :
    (diagonalGroupUnitsEquivPoints ℤ (Fin 2) ℤ (fun _ => 1)).left =
      (η[(diagonalGroupScheme ℤ (Fin 2)).X]).left := by
  have h := congrArg (fun q : integerDomain ⟶ integerDiagonal.X => q.left)
    diagonalGroup_integerPoint_one
  calc
    _ = integerDomain.hom ≫ (η[integerDiagonal.X]).left := by
      simpa only [Over.comp_left, Over.toUnit_left] using h
    _ = _ := by rw [integerSpec_asOver_hom]; exact Category.id_comp _

private theorem positivePoint_projection :
    positivePoint ≫ integerProjection = toUnit integerDomain ≫ η[integerMultiplicative.X] := by
  simpa only [map_one, Hom.one_def] using
    integerPoint_projection (fun _ => 1)

private theorem negativePoint_projection :
    negativePoint ≫ integerProjection = toUnit integerDomain ≫ η[integerMultiplicative.X] := by
  have h := integerPoint_projection (fun k => if k = 0 then 1 else -1)
  change negativePoint ≫ integerProjection =
    multiplicativeGroupMulEquivPoints ℤ ℤ (1 : ℤˣ) at h
  simpa only [map_one, Hom.one_def] using h

/-- Both specified integer points give commutative squares of original scheme maps. -/
theorem diagonalGroup_integerPoints_squares :
    let qPos := diagonalGroupUnitsEquivPoints ℤ (Fin 2) ℤ (fun _ => 1)
    let qNeg := diagonalGroupUnitsEquivPoints ℤ (Fin 2) ℤ
      (fun k => if k = 0 then 1 else -1)
    let f := (diagonalGroupProjection ℤ (Fin 2) (0 : Fin 2)).hom.hom.left
    let e := (η[(multiplicativeGroupScheme ℤ).toMon.X]).left
    qPos.left ≫ f = (𝟙 (Spec (.of ℤ))) ≫ e ∧
      qNeg.left ≫ f = (𝟙 (Spec (.of ℤ))) ≫ e := by
  constructor
  · have h : positivePoint.left ≫ integerProjection.left =
        integerDomain.hom ≫ (η[integerMultiplicative.X]).left := by
      simpa only [Over.comp_left, Over.toUnit_left] using
        congrArg (fun q : integerDomain ⟶ integerMultiplicative.X => q.left)
          positivePoint_projection
    simpa only [Category.id_comp] using
      h.trans (congrArg
        (fun g : integerBase ⟶ integerBase => g ≫ (η[integerMultiplicative.X]).left)
        integerSpec_asOver_hom)
  · have h : negativePoint.left ≫ integerProjection.left =
        integerDomain.hom ≫ (η[integerMultiplicative.X]).left := by
      simpa only [Over.comp_left, Over.toUnit_left] using
        congrArg (fun q : integerDomain ⟶ integerMultiplicative.X => q.left)
          negativePoint_projection
    simpa only [Category.id_comp] using
      h.trans (congrArg
        (fun g : integerBase ⟶ integerBase => g ≫ (η[integerMultiplicative.X]).left)
        integerSpec_asOver_hom)

/-- The source unit gives the unit square for the integer diagonal projection. -/
theorem diagonalGroup_integerPoint_unit_square :
    (η[(diagonalGroupScheme ℤ (Fin 2)).X]).left ≫
        (diagonalGroupProjection ℤ (Fin 2) (0 : Fin 2)).hom.hom.left =
      (𝟙 (Spec (.of ℤ))) ≫ (η[(multiplicativeGroupScheme ℤ).toMon.X]).left := by
  rw [← diagonalGroup_integerPoint_one_left]
  exact diagonalGroup_integerPoints_squares.1

private theorem integerPoint_section (v : Fin 2 → ℤˣ) :
    (diagonalGroupUnitsEquivPoints ℤ (Fin 2) ℤ v).left ≫ integerDiagonal.X.hom =
      𝟙 integerBase := by
  rw [Over.w, integerSpec_asOver_hom]

/-- Both specified points are sections over the original integer base scheme. -/
theorem diagonalGroup_integerPoints_sections :
    let qPos := diagonalGroupUnitsEquivPoints ℤ (Fin 2) ℤ (fun _ => 1)
    let qNeg := diagonalGroupUnitsEquivPoints ℤ (Fin 2) ℤ
      (fun k => if k = 0 then 1 else -1)
    let g := (diagonalGroupScheme ℤ (Fin 2)).X.hom
    qPos.left ≫ g = 𝟙 (Spec (.of ℤ)) ∧ qNeg.left ≫ g = 𝟙 (Spec (.of ℤ)) :=
  ⟨integerPoint_section _, integerPoint_section _⟩

/-- The two original scheme maps are different, already in their second unit coordinate. -/
theorem diagonalGroup_integerPoints_ne :
    (diagonalGroupUnitsEquivPoints ℤ (Fin 2) ℤ (fun _ => 1)).left ≠
      (diagonalGroupUnitsEquivPoints ℤ (Fin 2) ℤ
        (fun k => if k = 0 then 1 else -1)).left := by
  intro h
  have hq : positivePoint = negativePoint := Over.OverMorphism.ext h
  have hv := (diagonalGroupUnitsEquivPoints ℤ (Fin 2) ℤ).injective hq
  have hz := congrArg (fun v : Fin 2 → ℤˣ => ((v (1 : Fin 2) : ℤˣ) : ℤ)) hv
  norm_num at hz

/-- The specified sections factor through any original scheme-theoretic kernel.

The displayed lifts are those of the supplied square, with no structure on `N`
assumed. Their slice morphisms have the same underlying maps. The positive lift
is the lift of the source unit, by pullback uniqueness.
-/
theorem diagonalKernel_integerPoints
    (N : Scheme) (i : N ⟶ (diagonalGroupScheme ℤ (Fin 2)).X.left)
    (p : N ⟶ Spec (.of ℤ))
    (hPB : IsPullback i p
      (diagonalGroupProjection ℤ (Fin 2) (0 : Fin 2)).hom.hom.left
      (η[(multiplicativeGroupScheme ℤ).toMon.X]).left) :
    let A := (Spec (.of ℤ)).asOver (Spec (.of ℤ))
    let qPos := diagonalGroupUnitsEquivPoints ℤ (Fin 2) ℤ (fun _ => 1)
    let qNeg := diagonalGroupUnitsEquivPoints ℤ (Fin 2) ℤ
      (fun k => if k = 0 then 1 else -1)
    let kPos := hPB.lift qPos.left (𝟙 _) diagonalGroup_integerPoints_squares.1
    let kNeg := hPB.lift qNeg.left (𝟙 _) diagonalGroup_integerPoints_squares.2
    let lPos : A ⟶ Over.mk p := Over.homMk kPos (by
      change hPB.lift qPos.left (𝟙 _) diagonalGroup_integerPoints_squares.1 ≫ p = A.hom
      exact (hPB.lift_snd _ _ _).trans integerSpec_asOver_hom.symm)
    let lNeg : A ⟶ Over.mk p := Over.homMk kNeg (by
      change hPB.lift qNeg.left (𝟙 _) diagonalGroup_integerPoints_squares.2 ≫ p = A.hom
      exact (hPB.lift_snd _ _ _).trans integerSpec_asOver_hom.symm)
    kPos ≫ i = qPos.left ∧ kNeg ≫ i = qNeg.left ∧
      kPos ≫ p = 𝟙 _ ∧ kNeg ≫ p = 𝟙 _ ∧ kPos ≠ kNeg ∧
      lPos.left = kPos ∧ lNeg.left = kNeg ∧ lPos ≠ lNeg ∧
      kPos = hPB.lift (η[(diagonalGroupScheme ℤ (Fin 2)).X]).left
        (𝟙 _) diagonalGroup_integerPoint_unit_square := by
  dsimp only
  have hne :
      hPB.lift positivePoint.left (𝟙 _) diagonalGroup_integerPoints_squares.1 ≠
        hPB.lift negativePoint.left (𝟙 _) diagonalGroup_integerPoints_squares.2 := by
    intro h
    apply diagonalGroup_integerPoints_ne
    have hi := congrArg (fun k : Spec (.of ℤ) ⟶ N => k ≫ i) h
    exact (hPB.lift_fst _ _ _).symm.trans (hi.trans (hPB.lift_fst _ _ _))
  refine ⟨hPB.lift_fst _ _ _, hPB.lift_fst _ _ _, hPB.lift_snd _ _ _,
    hPB.lift_snd _ _ _, hne, rfl, rfl, ?_, ?_⟩
  · intro h
    exact hne (congrArg (fun ℓ : integerDomain ⟶ Over.mk p => ℓ.left) h)
  · apply hPB.hom_ext
    · exact (hPB.lift_fst _ _ _).trans
        (diagonalGroup_integerPoint_one_left.trans (hPB.lift_fst _ _ _).symm)
    · exact (hPB.lift_snd _ _ _).trans (hPB.lift_snd _ _ _).symm

/-- The chosen pullback has the two distinct sections given by `pullback.lift`.

Their comparison with lifts supplied by `IsPullback.of_hasPullback` uses
uniqueness, keeping the two APIs distinct.
-/
theorem diagonalKernel_integerPoints_pullback :
    let S := Spec (.of ℤ)
    let f := (diagonalGroupProjection ℤ (Fin 2) (0 : Fin 2)).hom.hom.left
    let e := (η[(multiplicativeGroupScheme ℤ).toMon.X]).left
    let qPos := diagonalGroupUnitsEquivPoints ℤ (Fin 2) ℤ (fun _ => 1)
    let qNeg := diagonalGroupUnitsEquivPoints ℤ (Fin 2) ℤ
      (fun k => if k = 0 then 1 else -1)
    let kPos := pullback.lift qPos.left (𝟙 S) diagonalGroup_integerPoints_squares.1
    let kNeg := pullback.lift qNeg.left (𝟙 S) diagonalGroup_integerPoints_squares.2
    kPos ≫ pullback.fst f e = qPos.left ∧
      kNeg ≫ pullback.fst f e = qNeg.left ∧
      kPos ≫ pullback.snd f e = 𝟙 S ∧
      kNeg ≫ pullback.snd f e = 𝟙 S ∧ kPos ≠ kNeg ∧
      kPos = (IsPullback.of_hasPullback f e).lift qPos.left (𝟙 S)
        diagonalGroup_integerPoints_squares.1 ∧
      kNeg = (IsPullback.of_hasPullback f e).lift qNeg.left (𝟙 S)
        diagonalGroup_integerPoints_squares.2 := by
  dsimp only
  let f := integerProjection.left
  let e := (η[integerMultiplicative.X]).left
  let hPB := IsPullback.of_hasPullback f e
  have hgiven := diagonalKernel_integerPoints (pullback f e)
    (pullback.fst f e) (pullback.snd f e) hPB
  have hplus :
      pullback.lift positivePoint.left (𝟙 _) diagonalGroup_integerPoints_squares.1 =
        hPB.lift positivePoint.left (𝟙 _) diagonalGroup_integerPoints_squares.1 := by
    apply hPB.hom_ext
    · exact (pullback.lift_fst _ _ _).trans (hPB.lift_fst _ _ _).symm
    · exact (pullback.lift_snd _ _ _).trans (hPB.lift_snd _ _ _).symm
  have hminus :
      pullback.lift negativePoint.left (𝟙 _) diagonalGroup_integerPoints_squares.2 =
        hPB.lift negativePoint.left (𝟙 _) diagonalGroup_integerPoints_squares.2 := by
    apply hPB.hom_ext
    · exact (pullback.lift_fst _ _ _).trans (hPB.lift_fst _ _ _).symm
    · exact (pullback.lift_snd _ _ _).trans (hPB.lift_snd _ _ _).symm
  refine ⟨pullback.lift_fst _ _ _, pullback.lift_fst _ _ _,
    pullback.lift_snd _ _ _, pullback.lift_snd _ _ _, ?_, hplus, hminus⟩
  intro h
  exact hgiven.2.2.2.2.1 (hplus.symm.trans (h.trans hminus))

end AlgebraicGeometry
