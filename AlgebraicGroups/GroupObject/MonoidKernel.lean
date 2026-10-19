/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mon
public import Mathlib.CategoryTheory.Monoidal.Internal.Limits

/-!
# Kernels of monoid objects as fibres of the unit

The underlying cone of a kernel of monoid objects is a pullback of the unit.
Conversely, a monoid homomorphism exhibiting this pullback identifies its domain
with the kernel through the canonical kernel lift.

Only a terminal tensor unit is needed. Equalizers in the ambient category ensure
that the forgetful functor preserves the kernel's parallel-pair limit; the
converse uses only the existence of the particular kernel.

## Implementation notes

The proofs use Mathlib's fork preservation and reflection API
(`isLimitForkMapOfIsLimit`, `isLimitOfIsLimitForkMap`) and the limit-lift
isomorphism criterion `IsLimit.nonempty_isLimit_iff_isIso_lift`.
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits CartesianMonoidalCategory MonObj

namespace CategoryTheory.Mon

variable {C : Type u} [Category.{v} C] [SemiCartesianMonoidalCategory C]

-- A terminal-object equalizer/pullback bridge; a candidate for the general limits API.
private theorem nonempty_isLimit_fork_iff_isPullback
    {K X Y : C} {i : K ⟶ X} {f : X ⟶ Y} (e : 𝟙_ C ⟶ Y)
    (w : i ≫ f = i ≫ (toUnit X ≫ e)) :
    Nonempty (IsLimit (Fork.ofι i w)) ↔ IsPullback i (toUnit K) f e := by
  constructor
  · rintro ⟨hc⟩
    have comm : i ≫ f = toUnit K ≫ e := by
      calc
        i ≫ f = i ≫ (toUnit X ≫ e) := w
        _ = toUnit K ≫ e := by
          rw [← Category.assoc, toUnit_unique (i ≫ toUnit X) (toUnit K)]
    let lift : ∀ s : PullbackCone f e, s.pt ⟶ K := fun s =>
      hc.lift (Fork.ofι s.fst (by
        calc
          s.fst ≫ f = s.snd ≫ e := s.condition
          _ = s.fst ≫ (toUnit X ≫ e) := by
            rw [← Category.assoc, toUnit_unique s.snd (s.fst ≫ toUnit X)]))
    refine ⟨⟨comm⟩, ⟨PullbackCone.IsLimit.mk comm lift ?_ ?_ ?_⟩⟩
    · intro s
      exact hc.fac _ WalkingParallelPair.zero
    · intro s
      exact toUnit_unique _ _
    · intro s m hm _
      apply Fork.IsLimit.hom_ext hc
      have hs : lift s ≫ i = s.fst := hc.fac _ WalkingParallelPair.zero
      exact hm.trans hs.symm
  · intro hp
    let lift : ∀ s : Fork f (toUnit X ≫ e), s.pt ⟶ K := fun s =>
      hp.isLimit.lift (PullbackCone.mk s.ι (toUnit s.pt) (by
        calc
          s.ι ≫ f = s.ι ≫ (toUnit X ≫ e) := s.condition
          _ = toUnit s.pt ≫ e := by
            rw [← Category.assoc, toUnit_unique (s.ι ≫ toUnit X) (toUnit s.pt)]))
    refine ⟨Fork.IsLimit.mk _ lift ?_ ?_⟩
    · intro s
      exact hp.isLimit.fac _ WalkingCospan.left
    · intro s m hm
      apply PullbackCone.IsLimit.hom_ext hp.isLimit
      · have hs : lift s ≫ i = s.ι := hp.isLimit.fac _ WalkingCospan.left
        exact hm.trans hs.symm
      · exact toUnit_unique _ _

/-- The underlying kernel inclusion of a monoid homomorphism is the pullback of
its target's unit. Ambient equalizers ensure preservation of the parallel-pair
limit by the forgetful functor. -/
theorem isPullback_kernel_ι [HasEqualizers C] {G H : Mon C} (f : G ⟶ H) :
    IsPullback (kernel.ι f).hom (toUnit (kernel f).X) f.hom η[H.X] := by
  have w : (kernel.ι f).hom ≫ f.hom =
      (kernel.ι f).hom ≫ (toUnit G.X ≫ η[H.X]) :=
    congrArg (fun k : kernel f ⟶ H => k.hom)
      ((kernel.condition f).trans comp_zero.symm)
  apply (nonempty_isLimit_fork_iff_isPullback η[H.X] w).mp
  exact ⟨isLimitForkMapOfIsLimit (forget C) _ (kernelIsKernel f)⟩

/-- If the underlying inclusion of a monoid object exhibits the fibre of the
unit, its canonical lift to the kernel is an isomorphism. Only this kernel must
exist: the forgetful functor reflects its limiting fork. The equation `h` is
used by the canonical lift; its characteristic equation is `kernel.lift_ι`. -/
theorem isIso_kernel_lift_of_isPullback {G H : Mon C} (f : G ⟶ H)
    [HasKernel f] {N : Mon C} (i : N ⟶ G) (h : i ≫ f = 0)
    (hi : IsPullback i.hom (toUnit N.X) f.hom η[H.X]) :
    IsIso (kernel.lift f i h) := by
  apply (IsLimit.nonempty_isLimit_iff_isIso_lift (kernelIsKernel f)).mp
  have w : i.hom ≫ f.hom = i.hom ≫ (toUnit G.X ≫ η[H.X]) :=
    congrArg (fun k : N ⟶ H => k.hom) (h.trans comp_zero.symm)
  obtain ⟨hl⟩ := (nonempty_isLimit_fork_iff_isPullback η[H.X] w).mpr hi
  exact ⟨isLimitOfIsLimitForkMap (forget C) (h.trans comp_zero.symm) hl⟩

end CategoryTheory.Mon
