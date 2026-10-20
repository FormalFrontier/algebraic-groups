/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.Monoidal.Internal.Limits
public import AlgebraicGroups.GroupObject.Kernel

/-!
# Monoid and group objects on a unit pullback

A pullback of a monoid morphism along the target unit has a monoid structure on
its supplied apex. Both supplied projections are monoid morphisms. If the source
is a group object in a Cartesian monoidal category, the same apex is a group
object; no group structure on the target is required.

The monoid construction uses `Mon.limit` on the supplied underlying limiting
cone, with the trivial monoid on the tensor unit as the other source. Its apex
is the supplied object, not a separately chosen categorical pullback. The group
construction applies `GrpObj.ofIsPullback` to this monoid structure, after
identifying the supplied map to the terminal tensor unit with `toUnit`.

## References

The monoid construction uses Mathlib's `Mon.limit` and its cone API
(`Mathlib.CategoryTheory.Monoidal.Internal.Limits`, revision
`83abb3e776bdefcbc447a1e44d0debe4010039e5`; Kim Morrison and Bhavik Mehta).
The group extension is the existing `GrpObj.ofIsPullback` from
`AlgebraicGroups.GroupObject.Kernel`.
-/

@[expose] public section

universe v u

open CategoryTheory Limits MonoidalCategory
open scoped MonObj

namespace CategoryTheory.MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {G H N : C} [MonObj G] [MonObj H]
  (f : G ⟶ H) (i : N ⟶ G) (p : N ⟶ 𝟙_ C) [IsMonHom f]
  (hPB : IsPullback i p f η[H])

/-- The monoid object on the supplied apex of a pullback along the target unit.

This is the monoid structure of `Mon.limit` for the cospan in `Mon C` with
arrows `f` and `η[H]`, using the limiting cone supplied by `hPB`. No monoid
structure on `N`, terminal tensor unit, or ambient existence of limits is assumed. -/
@[instance_reducible]
noncomputable def ofUnitPullback
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {G H N : C} [MonObj G] [MonObj H]
    (f : G ⟶ H) (i : N ⟶ G) (p : N ⟶ 𝟙_ C) [IsMonHom f]
    (hPB : IsPullback i p f η[H]) : MonObj N := by
  let F : WalkingCospan ⥤ Mon C :=
    cospan (Mon.Hom.mk f : Mon.mk G ⟶ Mon.mk H)
      (default : Mon.trivial C ⟶ Mon.mk H)
  let c : Cone (F ⋙ Mon.forget C) :=
    { pt := N
      π.app j := match j with
        | .left => i
        | .right => p
        | .one => i ≫ f
      π.naturality j k a := by
        cases a with
        | id j =>
            change 𝟙 N ≫ _ = _ ≫ 𝟙 _
            simp only [Category.id_comp, Category.comp_id]
        | term j =>
            cases j with
            | left =>
                change 𝟙 N ≫ (i ≫ f) = i ≫ f
                exact Category.id_comp _
            | right =>
                change 𝟙 N ≫ (i ≫ f) = p ≫ η[H]
                simpa only [Category.id_comp] using hPB.w }
  let hc : IsLimit c :=
    { lift s := hPB.lift (s.π.app .left) (s.π.app .right) (by
        change s.π.app .left ≫ f = s.π.app .right ≫ η[H]
        exact (s.w WalkingCospan.Hom.inl).trans
          (s.w WalkingCospan.Hom.inr).symm)
      fac s j := by
        cases j with
        | none =>
            change hPB.lift _ _ _ ≫ (i ≫ f) = s.π.app .one
            exact (Category.assoc _ _ _).symm.trans
              ((congrArg (fun k : s.pt ⟶ G => k ≫ f)
                (hPB.lift_fst (s.π.app .left) (s.π.app .right) _)).trans
                (s.w WalkingCospan.Hom.inl))
        | some j =>
            cases j with
            | left => exact hPB.lift_fst _ _ _
            | right => exact hPB.lift_snd _ _ _
      uniq s m hm := by
        apply hPB.hom_ext
        · exact (hm .left).trans
            (hPB.lift_fst (s.π.app .left) (s.π.app .right) _).symm
        · exact (hm .right).trans
            (hPB.lift_snd (s.π.app .left) (s.π.app .right) _).symm }
  exact (Mon.limit F c hc).mon

/-- The induced unit has the prescribed source projection. -/
@[simp, reassoc]
theorem ofUnitPullback_one_comp_i :
    (ofUnitPullback f i p hPB).one ≫ i = η[G] := by
  change hPB.lift η[G] η[𝟙_ C] _ ≫ i = η[G]
  exact hPB.lift_fst _ _ _

/-- The induced unit has the prescribed tensor-unit projection. -/
@[simp, reassoc]
theorem ofUnitPullback_one_comp_p :
    (ofUnitPullback f i p hPB).one ≫ p = η[𝟙_ C] := by
  change hPB.lift η[G] η[𝟙_ C] _ ≫ p = η[𝟙_ C]
  exact hPB.lift_snd _ _ _

/-- The induced multiplication has the prescribed source projection. -/
@[simp, reassoc]
theorem ofUnitPullback_mul_comp_i :
    (ofUnitPullback f i p hPB).mul ≫ i = (i ⊗ₘ i) ≫ μ[G] := by
  change hPB.lift ((i ⊗ₘ i) ≫ μ[G]) ((p ⊗ₘ p) ≫ μ[𝟙_ C]) _ ≫ i =
    (i ⊗ₘ i) ≫ μ[G]
  exact hPB.lift_fst _ _ _

/-- The induced multiplication has the prescribed tensor-unit projection. -/
@[simp, reassoc]
theorem ofUnitPullback_mul_comp_p :
    (ofUnitPullback f i p hPB).mul ≫ p = (p ⊗ₘ p) ≫ μ[𝟙_ C] := by
  change hPB.lift ((i ⊗ₘ i) ≫ μ[G]) ((p ⊗ₘ p) ≫ μ[𝟙_ C]) _ ≫ p =
    (p ⊗ₘ p) ≫ μ[𝟙_ C]
  exact hPB.lift_snd _ _ _

/-- The original source projection preserves the constructed monoid structure. -/
theorem ofUnitPullback_isMonHom_i :
    @IsMonHom C _ _ N G (ofUnitPullback f i p hPB) inferInstance i := by
  let : MonObj N := ofUnitPullback f i p hPB
  exact ⟨ofUnitPullback_one_comp_i f i p hPB, ofUnitPullback_mul_comp_i f i p hPB⟩

/-- The original tensor-unit projection preserves the constructed monoid structure. -/
theorem ofUnitPullback_isMonHom_p :
    @IsMonHom C _ _ N (𝟙_ C) (ofUnitPullback f i p hPB) inferInstance p := by
  let : MonObj N := ofUnitPullback f i p hPB
  exact ⟨ofUnitPullback_one_comp_p f i p hPB, ofUnitPullback_mul_comp_p f i p hPB⟩

/-- The supplied projections determine the monoid structure uniquely. -/
theorem ofUnitPullback_unique (m : MonObj N)
    (hi : @IsMonHom C _ _ N G m inferInstance i)
    (hp : @IsMonHom C _ _ N (𝟙_ C) m inferInstance p) :
    m = ofUnitPullback f i p hPB := by
  let : MonObj N := m
  let : IsMonHom i := hi
  let : IsMonHom p := hp
  apply MonObj.ext
  apply hPB.hom_ext
  · exact (IsMonHom.mul_hom i).trans
      (ofUnitPullback_mul_comp_i f i p hPB).symm
  · exact (IsMonHom.mul_hom p).trans
      (ofUnitPullback_mul_comp_p f i p hPB).symm

/-- Lift a monoid cone through the supplied unit pullback. -/
noncomputable def ofUnitPullbackLift
    {T : C} [MonObj T] (a : T ⟶ G) (b : T ⟶ 𝟙_ C)
    [IsMonHom a] [IsMonHom b] (w : a ≫ f = b ≫ η[H]) :
    Mon.mk T ⟶ Mon.mk (mon := ofUnitPullback f i p hPB) N := by
  letI : MonObj N := ofUnitPullback f i p hPB
  let l := hPB.lift a b w
  have li : l ≫ i = a := hPB.lift_fst a b w
  have lp : l ≫ p = b := hPB.lift_snd a b w
  refine { hom := l, isMonHom_hom := ?_ }
  constructor
  · apply hPB.hom_ext
    · calc
        (η[T] ≫ l) ≫ i = η[T] ≫ a := by rw [Category.assoc, li]
        _ = η[G] := IsMonHom.one_hom a
        _ = (ofUnitPullback f i p hPB).one ≫ i :=
          (ofUnitPullback_one_comp_i f i p hPB).symm
    · calc
        (η[T] ≫ l) ≫ p = η[T] ≫ b := by rw [Category.assoc, lp]
        _ = η[𝟙_ C] := IsMonHom.one_hom b
        _ = (ofUnitPullback f i p hPB).one ≫ p :=
          (ofUnitPullback_one_comp_p f i p hPB).symm
  · apply hPB.hom_ext
    · calc
        (μ[T] ≫ l) ≫ i = (a ⊗ₘ a) ≫ μ[G] := by
          simpa only [Category.assoc, li] using (IsMonHom.mul_hom a)
        _ = ((l ≫ i) ⊗ₘ (l ≫ i)) ≫ μ[G] := by rw [li]
        _ = ((l ⊗ₘ l) ≫ (i ⊗ₘ i)) ≫ μ[G] := by
          rw [tensorHom_comp_tensorHom]
        _ = ((l ⊗ₘ l) ≫ μ[N]) ≫ i := by
          simp only [Category.assoc, ofUnitPullback_mul_comp_i]
    · calc
        (μ[T] ≫ l) ≫ p = (b ⊗ₘ b) ≫ μ[𝟙_ C] := by
          simpa only [Category.assoc, lp] using (IsMonHom.mul_hom b)
        _ = ((l ≫ p) ⊗ₘ (l ≫ p)) ≫ μ[𝟙_ C] := by rw [lp]
        _ = ((l ⊗ₘ l) ≫ (p ⊗ₘ p)) ≫ μ[𝟙_ C] := by
          rw [tensorHom_comp_tensorHom]
        _ = ((l ⊗ₘ l) ≫ μ[N]) ≫ p := by
          simp only [Category.assoc, ofUnitPullback_mul_comp_p]

/-- The monoid lift is the lift of the original underlying pullback square. -/
@[simp]
theorem ofUnitPullbackLift_hom
    {T : C} [MonObj T] (a : T ⟶ G) (b : T ⟶ 𝟙_ C)
    [IsMonHom a] [IsMonHom b] (w : a ≫ f = b ≫ η[H]) :
    (ofUnitPullbackLift f i p hPB a b w).hom = hPB.lift a b w := rfl

/-- The two original projections detect equality of morphisms into the induced monoid. -/
theorem ofUnitPullback_hom_ext
    {T : Mon C} {a b : T ⟶ Mon.mk (mon := ofUnitPullback f i p hPB) N}
    (hi : a.hom ≫ i = b.hom ≫ i) (hp : a.hom ≫ p = b.hom ≫ p) : a = b := by
  apply Mon.Hom.ext
  exact hPB.hom_ext hi hp

end CategoryTheory.MonObj

namespace CategoryTheory.GrpObj

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {G H N : C} [GrpObj G] [MonObj H]
  (f : G ⟶ H) (i : N ⟶ G) (p : N ⟶ 𝟙_ C) [IsMonHom f]
  (hPB : IsPullback i p f η[H])

/-- The group object on a supplied unit pullback, including its monoid structure.

Unlike `GrpObj.ofIsPullback`, this construction does not take a monoid structure
on `N` or a monoid-morphism instance for `i` as input. It first constructs
`MonObj.ofUnitPullback`, then applies that existing group extension. -/
@[instance_reducible]
noncomputable def ofUnitPullback
    {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    {G H N : C} [GrpObj G] [MonObj H]
    (f : G ⟶ H) (i : N ⟶ G) (p : N ⟶ 𝟙_ C) [IsMonHom f]
    (hPB : IsPullback i p f η[H]) : GrpObj N := by
  letI : MonObj N := MonObj.ofUnitPullback f i p hPB
  letI : IsMonHom i := MonObj.ofUnitPullback_isMonHom_i f i p hPB
  have hp : p = CartesianMonoidalCategory.toUnit N :=
    CartesianMonoidalCategory.isTerminalTensorUnit.hom_ext _ _
  have hPB' : IsPullback i (CartesianMonoidalCategory.toUnit N) f η[H] := by
    simpa only [hp] using hPB
  exact GrpObj.ofIsPullback f i hPB'

/-- The composed group construction retains the constructed monoid dictionary. -/
@[simp]
theorem ofUnitPullback_toMonObj :
    (ofUnitPullback f i p hPB).toMonObj = MonObj.ofUnitPullback f i p hPB := rfl

/-- The supplied source projection, bundled as a morphism of group objects. -/
noncomputable def ofUnitPullbackHom :
    Grp.mk (grp := ofUnitPullback f i p hPB) N ⟶ Grp.mk G := by
  letI := ofUnitPullback f i p hPB
  haveI : IsMonHom i := by
    simpa only [ofUnitPullback_toMonObj] using
      (MonObj.ofUnitPullback_isMonHom_i f i p hPB)
  exact Grp.homMk i

/-- The bundled group projection has exactly the supplied underlying map. -/
@[simp]
theorem ofUnitPullbackHom_hom :
    (ofUnitPullbackHom f i p hPB).hom.hom = i := rfl

/-- The supplied source projection intertwines inverses. -/
@[reassoc]
theorem ofUnitPullback_inv_comp :
    (ofUnitPullback f i p hPB).inv ≫ i = i ≫ ι[G] := by
  let := ofUnitPullback f i p hPB
  have : IsMonHom i := by
    simpa only [ofUnitPullback_toMonObj] using
      (MonObj.ofUnitPullback_isMonHom_i f i p hPB)
  exact GrpObj.inv_hom i

end CategoryTheory.GrpObj
