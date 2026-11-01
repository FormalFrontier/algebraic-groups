/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import AlgebraicGroups.Algebra.Coalgebra.Range
public import AlgebraicGroups.Algebra.Coalgebra.Hom
public import Mathlib.RingTheory.Bialgebra.Hom

/-!
# The ordinary algebra range of a bialgebra homomorphism

The ordinary algebra range of a homomorphism preserving comultiplication and counit
has a canonical weak coalgebra structure. Its corestriction and inclusion preserve
both the algebra and the coalgebra data. No coalgebra laws on the ambient target
are needed.

When the source is a coalgebra, the range satisfies the coalgebra laws. When the
source is a bialgebra, its range is a bialgebra with the same algebra and weak
coalgebra data.

## Implementation notes

The weak structure is `LinearMap.rangeCoalgebraStruct` on the underlying linear
range. Additive groups needed for this construction are obtained privately from
the given modules over the field; their addition, zero and natural scalar action
are unchanged. The named range structures are not global instances: use them as
local instances when working with a fixed homomorphism.
-/

@[expose] public section

universe u v w z

open scoped TensorProduct

namespace BialgHom

section Weak

variable {K : Type u} {A : Type v} {B : Type w}
variable [Field K] [Semiring A] [Semiring B] [Algebra K A] [Algebra K B]
variable [CoalgebraStruct K A] [CoalgebraStruct K B]

/-- The canonical weak coalgebra on the ordinary algebra range. -/
@[instance_reducible]
noncomputable def rangeCoalgebraStruct (f : A →ₐc[K] B) :
    CoalgebraStruct K f.toAlgHom.range := by
  letI : AddCommGroup A := Module.addCommMonoidToAddCommGroup K
  letI : AddCommGroup B := Module.addCommMonoidToAddCommGroup K
  letI : (LinearMap.ker f.toLinearMap).IsCoideal := CoalgHomClass.ker_isCoideal f
  exact LinearMap.rangeCoalgebraStruct f.toLinearMap

attribute [local instance] rangeCoalgebraStruct

/-- Corestrict a bialgebra homomorphism to its ordinary algebra range. -/
noncomputable def rangeRestrict (f : A →ₐc[K] B) : A →ₐc[K] f.toAlgHom.range := by
  letI : AddCommGroup A := Module.addCommMonoidToAddCommGroup K
  letI : AddCommGroup B := Module.addCommMonoidToAddCommGroup K
  letI : (LinearMap.ker f.toLinearMap).IsCoideal := CoalgHomClass.ker_isCoideal f
  exact
    { toLinearMap := f.toAlgHom.rangeRestrict.toLinearMap
      map_one' := map_one f.toAlgHom.rangeRestrict
      map_mul' := map_mul f.toAlgHom.rangeRestrict
      counit_comp := by
        ext a
        exact LinearMap.rangeCoalgebraStruct_counit_apply_rangeRestrict
          (l := f.toLinearMap) a
      map_comp_comul := by
        ext a
        exact (LinearMap.rangeCoalgebraStruct_comul_apply_rangeRestrict
          (l := f.toLinearMap) a).symm }

@[simp]
theorem rangeRestrict_toAlgHom (f : A →ₐc[K] B) :
    f.rangeRestrict.toAlgHom = f.toAlgHom.rangeRestrict := rfl

theorem rangeRestrict_toLinearMap (f : A →ₐc[K] B) :
    f.rangeRestrict.toLinearMap = f.toLinearMap.rangeRestrict := rfl

theorem rangeRestrict_apply (f : A →ₐc[K] B) (a : A) :
    f.rangeRestrict a = f.toAlgHom.rangeRestrict a := rfl

/-- Coercing the range corestriction to the ambient algebra gives the original map. -/
theorem coe_rangeRestrict_apply (f : A →ₐc[K] B) (a : A) :
    (rangeRestrict f a : B) = f a := rfl

/-- The range corestriction has the original ambient value. -/
@[simp]
theorem coe_rangeRestrict (f : A →ₐc[K] B) (a : A) :
    (f.rangeRestrict a : B) = f a := coe_rangeRestrict_apply f a

/-- Corestriction to the ordinary range is surjective. -/
theorem surjective_rangeRestrict (f : A →ₐc[K] B) :
    Function.Surjective f.rangeRestrict := by
  intro x
  obtain ⟨a, ha⟩ := f.toAlgHom.mem_range.mp x.property
  exact ⟨a, Subtype.ext ha⟩

/-- Counit on the range is characterized on the corestriction. -/
theorem counit_rangeRestrict (f : A →ₐc[K] B) (a : A) :
    Coalgebra.counit (R := K) (f.rangeRestrict a) = Coalgebra.counit (R := K) a :=
  LinearMap.congr_fun f.rangeRestrict.counit_comp a

/-- Comultiplication on the range is characterized on the corestriction. -/
theorem comul_rangeRestrict (f : A →ₐc[K] B) (a : A) :
    Coalgebra.comul (R := K) (f.rangeRestrict a) =
      TensorProduct.map f.rangeRestrict.toLinearMap f.rangeRestrict.toLinearMap
        (Coalgebra.comul (R := K) a) :=
  (LinearMap.congr_fun f.rangeRestrict.map_comp_comul a).symm

/-- The inclusion of the ordinary algebra range as a bialgebra homomorphism. -/
noncomputable def rangeInclusion (f : A →ₐc[K] B) :
    f.toAlgHom.range →ₐc[K] B where
  toLinearMap := f.toAlgHom.range.val.toLinearMap
  map_one' := map_one f.toAlgHom.range.val
  map_mul' := map_mul f.toAlgHom.range.val
  counit_comp := by
    ext x
    obtain ⟨a, rfl⟩ := f.surjective_rangeRestrict x
    change Coalgebra.counit (R := K) (f a) =
      Coalgebra.counit (R := K) (f.rangeRestrict a)
    rw [counit_rangeRestrict]
    exact LinearMap.congr_fun f.counit_comp a
  map_comp_comul := by
    ext x
    obtain ⟨a, rfl⟩ := f.surjective_rangeRestrict x
    change TensorProduct.map f.toAlgHom.range.val.toLinearMap
        f.toAlgHom.range.val.toLinearMap
        (Coalgebra.comul (R := K) (f.rangeRestrict a)) =
      Coalgebra.comul (R := K) (f a)
    rw [comul_rangeRestrict, ← LinearMap.comp_apply, ← TensorProduct.map_comp]
    exact LinearMap.congr_fun f.map_comp_comul a

@[simp]
theorem rangeInclusion_toAlgHom (f : A →ₐc[K] B) :
    f.rangeInclusion.toAlgHom = f.toAlgHom.range.val := rfl

theorem rangeInclusion_toLinearMap (f : A →ₐc[K] B) :
    f.rangeInclusion.toLinearMap = f.toAlgHom.range.val.toLinearMap := rfl

@[simp]
theorem rangeInclusion_apply (f : A →ₐc[K] B) (x : f.toAlgHom.range) :
    f.rangeInclusion x = (x : B) := rfl

/-- The range inclusion is injective. -/
theorem injective_rangeInclusion (f : A →ₐc[K] B) :
    Function.Injective f.rangeInclusion := Subtype.coe_injective

/-- Counit on the range agrees with counit after inclusion. -/
theorem rangeInclusion_counit (f : A →ₐc[K] B) (x : f.toAlgHom.range) :
    Coalgebra.counit (R := K) (x : B) = Coalgebra.counit (R := K) x :=
  LinearMap.congr_fun f.rangeInclusion.counit_comp x

/-- Comultiplication on the range agrees with comultiplication after inclusion. -/
theorem comul_rangeInclusion (f : A →ₐc[K] B) (x : f.toAlgHom.range) :
    Coalgebra.comul (R := K) (x : B) =
      TensorProduct.map f.rangeInclusion.toLinearMap f.rangeInclusion.toLinearMap
        (Coalgebra.comul (R := K) x) :=
  (LinearMap.congr_fun f.rangeInclusion.map_comp_comul x).symm

@[simp]
theorem rangeInclusion_comp_rangeRestrict (f : A →ₐc[K] B) :
    f.rangeInclusion.comp f.rangeRestrict = f := by
  apply DFunLike.ext
  intro a
  rfl

/-- Corestriction is the unique map whose composite with the range inclusion is the
original homomorphism. -/
theorem rangeRestrict_unique (f : A →ₐc[K] B) (h : A →ₐc[K] f.toAlgHom.range)
    (hh : f.rangeInclusion.comp h = f) : h = f.rangeRestrict := by
  apply DFunLike.ext
  intro a
  apply Subtype.ext
  exact congrArg (fun k : A →ₐc[K] B => k a) hh

/-- Precomposition with the range corestriction is injective. -/
theorem rangeRestrict_comp_injective {C : Type z} [Semiring C] [Algebra K C]
    [CoalgebraStruct K C] (f : A →ₐc[K] B) :
    Function.Injective (fun g : f.toAlgHom.range →ₐc[K] C => g.comp f.rangeRestrict) := by
  intro g h hgh
  apply DFunLike.ext
  intro x
  obtain ⟨a, rfl⟩ := f.surjective_rangeRestrict x
  exact DFunLike.congr_fun hgh a

end Weak

section Coalgebra

variable {K : Type u} {A : Type v} {B : Type w}
variable [Field K] [Semiring A] [Semiring B] [Algebra K A] [Algebra K B]
variable [Coalgebra K A] [CoalgebraStruct K B]

attribute [local instance] rangeCoalgebraStruct

/-- The full coalgebra on the ordinary algebra range, extending its canonical weak
coalgebra. Only the source needs to satisfy the coalgebra laws. -/
@[instance_reducible]
noncomputable def rangeCoalgebra (f : A →ₐc[K] B) :
    Coalgebra K f.toAlgHom.range := by
  letI : AddCommGroup A := Module.addCommMonoidToAddCommGroup K
  letI : AddCommGroup B := Module.addCommMonoidToAddCommGroup K
  let l : A →ₗ[K] B := f.toLinearMap
  letI : (LinearMap.ker l).IsCoideal := CoalgHomClass.ker_isCoideal f
  letI : Coalgebra K (A ⧸ LinearMap.ker l) := inferInstance
  let e : (A ⧸ LinearMap.ker l) ≃ₗc[K] f.toAlgHom.range :=
    { l.quotKerEquivRange with
      counit_comp := by
        change
          @CoalgebraStruct.counit K (LinearMap.range l) _ _ _
              (LinearMap.rangeCoalgebraStruct l) ∘ₗ
            l.quotKerEquivRange.toLinearMap = Coalgebra.counit (R := K)
        rw [LinearMap.rangeCoalgebraStruct_counit]
        ext x
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
          LinearEquiv.symm_apply_apply]
      map_comp_comul := by
        change
          TensorProduct.map l.quotKerEquivRange.toLinearMap
              l.quotKerEquivRange.toLinearMap ∘ₗ Coalgebra.comul (R := K) =
            @CoalgebraStruct.comul K (LinearMap.range l) _ _ _
                (LinearMap.rangeCoalgebraStruct l) ∘ₗ
              l.quotKerEquivRange.toLinearMap
        rw [LinearMap.rangeCoalgebraStruct_comul]
        ext x
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
          LinearEquiv.symm_apply_apply] }
  exact e.toCoalgebra

/-- The full range coalgebra retains the canonical weak range data. -/
@[simp]
theorem rangeCoalgebra_toCoalgebraStruct (f : A →ₐc[K] B) :
    (rangeCoalgebra f).toCoalgebraStruct = rangeCoalgebraStruct f := rfl

end Coalgebra

section Surjective

variable {R : Type u} {S : Type v} {T : Type w}
variable [CommSemiring R] [Semiring S] [Semiring T]
variable [Bialgebra R S] [Algebra R T] [Coalgebra R T]

/-- A surjective bialgebra homomorphism descends the bialgebra laws to its target,
without changing the target algebra or coalgebra data. -/
@[instance_reducible]
noncomputable def bialgebraOfSurjective (r : S →ₐc[R] T)
    (hr : Function.Surjective r) : Bialgebra R T := by
  have hε (a : S) : Coalgebra.counit (R := R) (r a) =
      Coalgebra.counit (R := R) a :=
    LinearMap.congr_fun r.counit_comp a
  have hΔ (a : S) : Coalgebra.comul (R := R) (r a) =
      TensorProduct.map r.toLinearMap r.toLinearMap
        (Coalgebra.comul (R := R) a) :=
    (LinearMap.congr_fun r.map_comp_comul a).symm
  refine Bialgebra.mk' R T ?_ (fun {x y} => ?_) ?_ (fun {x y} => ?_)
  · rw [← map_one r, hε, Bialgebra.counit_one]
  · obtain ⟨a, rfl⟩ := hr x
    obtain ⟨b, rfl⟩ := hr y
    rw [← map_mul r, hε, hε, hε, Bialgebra.counit_mul]
  · rw [← map_one r, hΔ, Bialgebra.comul_one]
    exact map_one (Algebra.TensorProduct.map r.toAlgHom r.toAlgHom)
  · obtain ⟨a, rfl⟩ := hr x
    obtain ⟨b, rfl⟩ := hr y
    rw [← map_mul r, hΔ, hΔ, hΔ, Bialgebra.comul_mul]
    exact map_mul (Algebra.TensorProduct.map r.toAlgHom r.toAlgHom) _ _

/-- The surjective law-layer construction retains the given target coalgebra. -/
@[simp]
theorem bialgebraOfSurjective_toCoalgebra (r : S →ₐc[R] T)
    (hr : Function.Surjective r) :
    (bialgebraOfSurjective r hr).toCoalgebra = (inferInstance : Coalgebra R T) := rfl

/-- The surjective law-layer construction retains the given target algebra. -/
@[simp]
theorem bialgebraOfSurjective_toAlgebra (r : S →ₐc[R] T)
    (hr : Function.Surjective r) :
    (bialgebraOfSurjective r hr).toAlgebra = (inferInstance : Algebra R T) := rfl

end Surjective

section Bialgebra

variable {K : Type u} {A : Type v} {B : Type w}
variable [Field K] [Semiring A] [Semiring B] [Bialgebra K A]
variable [Algebra K B] [CoalgebraStruct K B]

attribute [local instance] rangeCoalgebra

/-- The bialgebra on the ordinary algebra range, retaining its inherited algebra
and canonical range coalgebra. Only the source needs to be a bialgebra. -/
@[instance_reducible]
noncomputable def rangeBialgebra (f : A →ₐc[K] B) : Bialgebra K f.toAlgHom.range := by
  exact bialgebraOfSurjective (rangeRestrict f) (surjective_rangeRestrict f)

/-- The range bialgebra retains the full range coalgebra. -/
theorem rangeBialgebra_toCoalgebra (f : A →ₐc[K] B) :
    (rangeBialgebra f).toCoalgebra = rangeCoalgebra f := rfl

/-- The range bialgebra retains the inherited range algebra. -/
theorem rangeBialgebra_toAlgebra (f : A →ₐc[K] B) :
    (rangeBialgebra f).toAlgebra = Subalgebra.algebra f.toAlgHom.range := rfl

end Bialgebra

end BialgHom
