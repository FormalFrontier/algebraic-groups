/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import AlgebraicGroups.Algebra.Bialgebra.Range
public import Mathlib.RingTheory.Bialgebra.Equiv
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.Basic

/-!
# Postcomposition on algebra ranges of bialgebra homomorphisms

`BialgHom.rangeMap f g` maps the ordinary algebra range of `f` onto that of
`g.comp f`. It has underlying function `g`. Its coalgebra compatibility uses the
canonical weak coalgebra structures on those ranges, not coalgebra laws on the
ambient algebras.

`BialgHom.rangeEquiv f g h` is the resulting equivalence when `g` is injective on
`f.toAlgHom.range`. Global injectivity of `g` is not required.

## Implementation notes

The algebra map is `AlgHom.subalgebraMap`, with its codomain identified by
`AlgHom.range_comp`. Coalgebra compatibility is obtained from `CoalgHom.ofComp`
using the inclusion of the *target range* in the ambient algebra on both tensor
factors. Additive groups used to obtain flatness are local to that proof and
extend the given positive additive and scalar data.

For inference on ordinary ranges and ranges displayed as algebra-map composites,
use `BialgHom.rangeCoalgebraStruct` and `BialgHom.rangeCompCoalgebraStruct` as local
instances. Neither structure is a global instance.
-/

@[expose] public section

open scoped TensorProduct

universe uK uA uB uC uD

namespace BialgHom

attribute [local instance] BialgHom.rangeCoalgebraStruct

variable {K : Type uK} {A : Type uA} {B : Type uB} {C : Type uC}
variable [Field K]
variable [Semiring A] [Algebra K A] [CoalgebraStruct K A]
variable [Semiring B] [Algebra K B] [CoalgebraStruct K B]
variable [Semiring C] [Algebra K C] [CoalgebraStruct K C]

/-- The canonical weak coalgebra on the ordinary algebra range of a composite.
This is the same structure as `rangeCoalgebraStruct (g.comp f)`. -/
@[instance_reducible]
noncomputable def rangeCompCoalgebraStruct
    (f : A →ₐc[K] B) (g : B →ₐc[K] C) :
    CoalgebraStruct K (g.toAlgHom.comp f.toAlgHom).range :=
  rangeCoalgebraStruct (g.comp f)

attribute [local instance] rangeCompCoalgebraStruct

/-- Postcomposition by `g` on the ordinary algebra range of `f`. -/
noncomputable def rangeMap (f : A →ₐc[K] B) (g : B →ₐc[K] C) :
    @BialgHom K f.toAlgHom.range (g.toAlgHom.comp f.toAlgHom).range _ _
      (Subalgebra.algebra f.toAlgHom.range) _
      (Subalgebra.algebra (g.toAlgHom.comp f.toAlgHom).range)
      (rangeCoalgebraStruct f) (rangeCoalgebraStruct (g.comp f)) :=
  let p : f.toAlgHom.range →ₐ[K] (g.comp f).toAlgHom.range :=
    (Subalgebra.equivOfEq _ _ (AlgHom.range_comp f.toAlgHom g.toAlgHom).symm).toAlgHom.comp
      (g.toAlgHom.subalgebraMap f.toAlgHom.range)
  { toCoalgHom :=
      CoalgHom.ofComp (rangeInclusion (g.comp f)).toCoalgHom
        (g.toCoalgHom.comp (rangeInclusion f).toCoalgHom)
        p.toLinearMap
        (by
          ext x
          change (p x : C) = g (x : B)
          rfl)
        (by
          let : AddCommGroup C := Module.addCommMonoidToAddCommGroup K
          let : AddCommGroup (g.toAlgHom.comp f.toAlgHom).range :=
            Module.addCommMonoidToAddCommGroup K
          exact TensorProduct.map_injective_of_flat_flat _ _
            (injective_rangeInclusion (g.comp f)) (injective_rangeInclusion (g.comp f)))
    map_one' := _root_.map_one p
    map_mul' x y := _root_.map_mul p x y }

/-- The algebra map of `rangeMap` is the stock subalgebra image map. -/
@[simp]
theorem rangeMap_toAlgHom (f : A →ₐc[K] B) (g : B →ₐc[K] C) :
    (rangeMap f g).toAlgHom =
      (Subalgebra.equivOfEq _ _ (AlgHom.range_comp f.toAlgHom g.toAlgHom).symm).toAlgHom.comp
        (g.toAlgHom.subalgebraMap f.toAlgHom.range) := by
  apply AlgHom.ext
  intro x
  rfl

/-- The linear map of `rangeMap` is that of the stock subalgebra image map. -/
theorem rangeMap_toLinearMap (f : A →ₐc[K] B) (g : B →ₐc[K] C) :
    (rangeMap f g).toLinearMap =
      ((Subalgebra.equivOfEq _ _
        (AlgHom.range_comp f.toAlgHom g.toAlgHom).symm).toAlgHom.comp
          (g.toAlgHom.subalgebraMap f.toAlgHom.range)).toLinearMap := by
  exact congrArg
    (fun p : f.toAlgHom.range →ₐ[K] (g.comp f).toAlgHom.range => p.toLinearMap)
    (rangeMap_toAlgHom f g)

/-- Coercing a value of `rangeMap` to the ambient algebra gives `g`. -/
@[simp]
theorem coe_rangeMap_apply (f : A →ₐc[K] B) (g : B →ₐc[K] C)
    (x : f.toAlgHom.range) : ((rangeMap f g).toLinearMap x : C) = g (x : B) := by
  exact congrArg Subtype.val (AlgHom.congr_fun (rangeMap_toAlgHom f g) x)

/-- The value of `rangeMap`, with its ordinary range membership witness. -/
theorem rangeMap_apply (f : A →ₐc[K] B) (g : B →ₐc[K] C) (x : f.toAlgHom.range) :
    (rangeMap f g).toFun x = ⟨g (x : B), by
      obtain ⟨a, ha⟩ := x.property
      exact ⟨a, congrArg g ha⟩⟩ :=
  Subtype.ext (coe_rangeMap_apply f g x)

/-- The underlying ambient-valued function of `rangeMap` is `g`. -/
theorem coe_rangeMap (f : A →ₐc[K] B) (g : B →ₐc[K] C) :
    (fun x : f.toAlgHom.range => ((rangeMap f g).toFun x : C)) =
      fun x : f.toAlgHom.range => g (x : B) :=
  funext (coe_rangeMap_apply f g)

/-- Postcomposition commutes with the canonical range restriction, pointwise. -/
@[simp]
theorem rangeMap_rangeRestrict (f : A →ₐc[K] B) (g : B →ₐc[K] C) (a : A) :
    (rangeMap f g).toFun (rangeRestrict f a) = rangeRestrict (g.comp f) a := by
  apply Subtype.ext
  exact congrArg Subtype.val (rangeMap_apply f g (rangeRestrict f a))

/-- The range-restriction triangle for postcomposition. -/
@[simp]
theorem rangeMap_comp_rangeRestrict (f : A →ₐc[K] B) (g : B →ₐc[K] C) :
    (rangeMap f g).comp (rangeRestrict f) = rangeRestrict (g.comp f) := by
  apply BialgHom.ext
  intro a
  exact rangeMap_rangeRestrict f g a

/-- The inclusion triangle for postcomposition. -/
@[simp]
theorem rangeInclusion_comp_rangeMap (f : A →ₐc[K] B) (g : B →ₐc[K] C) :
    (rangeInclusion (g.comp f)).comp (rangeMap f g) = g.comp (rangeInclusion f) := by
  ext x
  change (rangeInclusion (g.comp f)) ((rangeMap f g).toFun x) = g (rangeInclusion f x)
  exact (rangeInclusion_apply (g.comp f) ((rangeMap f g).toFun x)).trans
    ((coe_rangeMap_apply f g x).trans (congrArg g (rangeInclusion_apply f x)).symm)

/-- Postcomposition is surjective onto the range of the composite. -/
theorem surjective_rangeMap (f : A →ₐc[K] B) (g : B →ₐc[K] C) :
    Function.Surjective (rangeMap f g).toFun := by
  intro y
  obtain ⟨a, rfl⟩ := surjective_rangeRestrict (g.comp f) y
  exact ⟨rangeRestrict f a, rangeMap_rangeRestrict f g a⟩

/-- The restriction triangle uniquely characterizes `rangeMap`. -/
theorem rangeMap_unique (f : A →ₐc[K] B) (g : B →ₐc[K] C)
    (p : f.toAlgHom.range →ₐc[K] (g.comp f).toAlgHom.range)
    (hp : p.comp (rangeRestrict f) = rangeRestrict (g.comp f)) : p = rangeMap f g := by
  apply BialgHom.ext
  intro x
  obtain ⟨a, rfl⟩ := surjective_rangeRestrict f x
  exact (DFunLike.congr_fun hp a).trans (rangeMap_rangeRestrict f g a).symm

/-- Injectivity of postcomposition is precisely injectivity on the original range. -/
theorem injective_rangeMap_iff (f : A →ₐc[K] B) (g : B →ₐc[K] C) :
    Function.Injective (rangeMap f g).toFun ↔ Set.InjOn g (f.toAlgHom.range : Set B) := by
  constructor
  · intro h x hx y hy hxy
    have he : (rangeMap f g).toFun ⟨x, hx⟩ = (rangeMap f g).toFun ⟨y, hy⟩ := by
      apply Subtype.ext
      exact (congrArg Subtype.val (rangeMap_apply f g ⟨x, hx⟩)).trans
        (hxy.trans (congrArg Subtype.val (rangeMap_apply f g ⟨y, hy⟩)).symm)
    exact congrArg Subtype.val (h he)
  · intro h x y hxy
    apply Subtype.ext
    apply h x.property y.property
    exact (congrArg Subtype.val (rangeMap_apply f g x)).symm.trans
      ((congrArg Subtype.val hxy).trans (congrArg Subtype.val (rangeMap_apply f g y)))

/-- Global injectivity is a sufficient, but unnecessary, condition for bijectivity. -/
theorem bijective_rangeMap_of_injective (f : A →ₐc[K] B) (g : B →ₐc[K] C)
    (hg : Function.Injective g) : Function.Bijective (rangeMap f g).toFun :=
  ⟨(injective_rangeMap_iff f g).2 (fun _ _ _ _ h => hg h), surjective_rangeMap f g⟩

/-- Identity coherence, reindexed along the existing identity-composition equality. -/
theorem rangeMap_id (f : A →ₐc[K] B) :
    cast (congrArg (fun q : A →ₐc[K] B =>
      f.toAlgHom.range →ₐc[K] q.toAlgHom.range) (BialgHom.id_comp f))
        (rangeMap f (BialgHom.id K B)) = BialgHom.id K f.toAlgHom.range := by
  apply BialgHom.ext
  intro x
  apply Subtype.ext
  change ((rangeMap f (BialgHom.id K B)).toFun x : B) = (x : B)
  exact congrArg Subtype.val (rangeMap_apply f (BialgHom.id K B) x)

variable {D : Type uD} [Semiring D] [Algebra K D] [CoalgebraStruct K D]

/-- Composition coherence, reindexed along the existing associativity equality. -/
theorem rangeMap_comp (f : A →ₐc[K] B) (g : B →ₐc[K] C) (h : C →ₐc[K] D) :
    cast (congrArg (fun q : A →ₐc[K] D =>
      f.toAlgHom.range →ₐc[K] q.toAlgHom.range) (BialgHom.comp_assoc h g f))
        (rangeMap f (h.comp g)) =
      (rangeMap (g.comp f) h).comp (rangeMap f g) := by
  apply BialgHom.ext
  intro x
  apply Subtype.ext
  change ((rangeMap f (h.comp g)).toFun x : D) =
    ((rangeMap (g.comp f) h).toFun ((rangeMap f g).toFun x) : D)
  calc
    ((rangeMap f (h.comp g)).toFun x : D) = (h.comp g) (x : B) :=
      coe_rangeMap_apply f (h.comp g) x
    _ = h (g (x : B)) := rfl
    _ = h ((rangeMap f g).toFun x : C) := (congrArg h (coe_rangeMap_apply f g x)).symm
    _ = ((rangeMap (g.comp f) h).toFun ((rangeMap f g).toFun x) : D) :=
      (coe_rangeMap_apply (g.comp f) h ((rangeMap f g).toFun x)).symm

/-- Postcomposition gives a weak bialgebra equivalence if it is injective on the range.
Its underlying algebra equivalence is the stock `AlgEquiv.ofBijective` applied to
`rangeMap`, not a strong bialgebra-equivalence constructor. -/
noncomputable def rangeEquiv (f : A →ₐc[K] B) (g : B →ₐc[K] C)
    (hg : Set.InjOn g (f.toAlgHom.range : Set B)) :
    @BialgEquiv K _ f.toAlgHom.range (g.toAlgHom.comp f.toAlgHom).range _ _
      (Subalgebra.algebra f.toAlgHom.range)
      (Subalgebra.algebra (g.toAlgHom.comp f.toAlgHom).range)
      (rangeCoalgebraStruct f) (rangeCoalgebraStruct (g.comp f)) :=
  let e := AlgEquiv.ofBijective (rangeMap f g).toAlgHom
    ⟨(injective_rangeMap_iff f g).2 hg, surjective_rangeMap f g⟩
  { toCoalgEquiv := { (rangeMap f g).toCoalgHom, e.toLinearEquiv with }
    map_mul' := e.map_mul }

/-- The forward bialgebra homomorphism of `rangeEquiv` is `rangeMap`. -/
theorem rangeEquiv_toBialgHom (f : A →ₐc[K] B) (g : B →ₐc[K] C)
    (hg : Set.InjOn g (f.toAlgHom.range : Set B)) :
    (rangeEquiv f g hg).toBialgHom = rangeMap f g := by
  ext x
  rfl

/-- The underlying algebra equivalence is the stock equivalence of the fixed map. -/
@[simp]
theorem rangeEquiv_toAlgEquiv (f : A →ₐc[K] B) (g : B →ₐc[K] C)
    (hg : Set.InjOn g (f.toAlgHom.range : Set B)) :
    (rangeEquiv f g hg).toAlgEquiv =
      AlgEquiv.ofBijective (rangeMap f g).toAlgHom
        ⟨(injective_rangeMap_iff f g).2 hg, surjective_rangeMap f g⟩ := by
  ext x
  rfl

/-- The equivalence has the same forward value as `rangeMap`. -/
@[simp]
theorem rangeEquiv_apply (f : A →ₐc[K] B) (g : B →ₐc[K] C)
    (hg : Set.InjOn g (f.toAlgHom.range : Set B)) (x : f.toAlgHom.range) :
    (rangeEquiv f g hg).toFun x = (rangeMap f g).toFun x := rfl

/-- The ambient value of the image equivalence is `g`. -/
theorem coe_rangeEquiv_apply (f : A →ₐc[K] B) (g : B →ₐc[K] C)
    (hg : Set.InjOn g (f.toAlgHom.range : Set B)) (x : f.toAlgHom.range) :
    ((rangeEquiv f g hg).toFun x : C) = g (x : B) :=
  coe_rangeMap_apply f g x

/-- The inverse selects the unique preimage lying in the original range. -/
@[simp]
theorem rangeEquiv_symm_rangeMap (f : A →ₐc[K] B) (g : B →ₐc[K] C)
    (hg : Set.InjOn g (f.toAlgHom.range : Set B)) (x : f.toAlgHom.range) :
    (rangeEquiv f g hg).symm.toLinearMap ((rangeMap f g).toLinearMap x) = x := by
  exact (rangeEquiv f g hg).toEquiv.left_inv x

/-- Applying `g` to the inverse value gives the original ambient value. -/
@[simp]
theorem coe_rangeEquiv_symm_apply (f : A →ₐc[K] B) (g : B →ₐc[K] C)
    (hg : Set.InjOn g (f.toAlgHom.range : Set B)) (y : (g.comp f).toAlgHom.range) :
    g ((rangeEquiv f g hg).symm.toLinearMap y : B) = (y : C) := by
  calc
    g ((rangeEquiv f g hg).symm.toFun y : B) =
        ((rangeEquiv f g hg).toFun ((rangeEquiv f g hg).symm.toFun y) : C) :=
      (coe_rangeEquiv_apply f g hg _).symm
    _ = (y : C) := congrArg Subtype.val ((rangeEquiv f g hg).apply_symm_apply y)

/-- An inverse value is characterized by its ambient image under `g`. -/
theorem rangeEquiv_symm_apply_eq_iff (f : A →ₐc[K] B) (g : B →ₐc[K] C)
    (hg : Set.InjOn g (f.toAlgHom.range : Set B))
    (y : (g.comp f).toAlgHom.range) (x : f.toAlgHom.range) :
    (rangeEquiv f g hg).symm.toFun y = x ↔ (y : C) = g (x : B) := by
  constructor
  · intro h
    rw [← h]
    exact (coe_rangeEquiv_symm_apply f g hg y).symm
  · intro h
    apply Subtype.ext
    apply hg ((rangeEquiv f g hg).symm.toFun y).property x.property
    exact (coe_rangeEquiv_symm_apply f g hg y).trans h

/-- Injectivity on two successive ranges implies injectivity of the composite on the first. -/
theorem injOn_comp_range (f : A →ₐc[K] B) (g : B →ₐc[K] C)
    (h : C →ₐc[K] D) (hg : Set.InjOn g (f.toAlgHom.range : Set B))
    (hh : Set.InjOn h ((g.comp f).toAlgHom.range : Set C)) :
    Set.InjOn (h.comp g) (f.toAlgHom.range : Set B) := by
  have hmem : ∀ z ∈ f.toAlgHom.range, g z ∈ (g.comp f).toAlgHom.range := by
    intro z hz
    obtain ⟨a, rfl⟩ := hz
    exact ⟨a, rfl⟩
  intro x hx y hy hxy
  apply hg hx hy
  exact hh (hmem x hx) (hmem y hy) hxy

/-- The identity image equivalence, reindexed along identity composition. -/
theorem rangeEquiv_id (f : A →ₐc[K] B) :
    cast (congrArg (fun q : A →ₐc[K] B =>
      f.toAlgHom.range ≃ₐc[K] q.toAlgHom.range) (BialgHom.id_comp f))
        (rangeEquiv f (BialgHom.id K B) (by
          intro x _ y _ hxy
          simpa only [BialgHom.coe_id, _root_.id] using hxy)) =
      BialgEquiv.refl K f.toAlgHom.range := by
  apply BialgEquiv.ext
  intro x
  apply Subtype.ext
  have hi : Set.InjOn (BialgHom.id K B) (f.toAlgHom.range : Set B) := by
    intro a _ b _ hab
    simpa only [BialgHom.coe_id, _root_.id] using hab
  change ((rangeEquiv f (BialgHom.id K B) hi).toFun x : B) = (x : B)
  simp only [coe_rangeEquiv_apply, BialgHom.coe_id, _root_.id]

/-- Image equivalences compose with injectivity only on the successive ranges.
The injectivity condition for the composite is derived, not assumed. -/
theorem rangeEquiv_comp (f : A →ₐc[K] B) (g : B →ₐc[K] C) (h : C →ₐc[K] D)
    (hg : Set.InjOn g (f.toAlgHom.range : Set B))
    (hh : Set.InjOn h ((g.comp f).toAlgHom.range : Set C)) :
    cast (congrArg (fun q : A →ₐc[K] D =>
      f.toAlgHom.range ≃ₐc[K] q.toAlgHom.range) (BialgHom.comp_assoc h g f))
        (rangeEquiv f (h.comp g) (injOn_comp_range f g h hg hh)) =
      (rangeEquiv f g hg).trans (rangeEquiv (g.comp f) h hh) := by
  apply BialgEquiv.ext
  intro x
  apply Subtype.ext
  change ((rangeEquiv f (h.comp g) (injOn_comp_range f g h hg hh)).toFun x : D) =
    ((rangeEquiv (g.comp f) h hh).toFun ((rangeEquiv f g hg).toFun x) : D)
  calc
    ((rangeEquiv f (h.comp g) (injOn_comp_range f g h hg hh)).toFun x : D) =
        (h.comp g) (x : B) := coe_rangeEquiv_apply f (h.comp g) _ x
    _ = h (g (x : B)) := rfl
    _ = h ((rangeEquiv f g hg).toFun x : C) :=
      (congrArg h (coe_rangeEquiv_apply f g hg x)).symm
    _ = ((rangeEquiv (g.comp f) h hh).toFun ((rangeEquiv f g hg).toFun x) : D) :=
      (coe_rangeEquiv_apply (g.comp f) h hh ((rangeEquiv f g hg).toFun x)).symm

end BialgHom
