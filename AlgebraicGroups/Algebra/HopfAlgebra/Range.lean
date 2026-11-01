/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Bialgebra.Quotient
public import AlgebraicGroups.Algebra.Bialgebra.Range
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.Basic
public import AlgebraicGroups.Algebra.Coalgebra.Range
public import AlgebraicGroups.Algebra.Coalgebra.Subcoalgebra.Hom
public import AlgebraicGroups.Algebra.HopfAlgebra.Ideal
public import Mathlib.RingTheory.Bialgebra.Equiv

/-!
# Hopf structure on the ordinary algebra range

Over a field, the ordinary `AlgHom.range` of a bialgebra homomorphism between Hopf
algebras is a Hopf algebra. The source is a possibly noncommutative ring and the
target need only be a semiring. All semiring, algebra and module data on the range
are inherited from its subalgebra. The coalgebra is the restricted coalgebra of
`CoalgHom.range`; its data agree with `LinearMap.rangeCoalgebraStruct`.

The canonical bialgebra range maps are provided by
`AlgebraicGroups.Algebra.Bialgebra.Range`. The maps `BialgHom.hopfRangeRestrict`
and `BialgHom.hopfRangeInclusion` instead retain the given Hopf range structure.
Their ordinary algebra maps agree, while their coalgebra parents remain explicit.

`BialgHom.quotientKerEquivRange` refines `Ideal.quotientKerEquivRange` between
the canonical Hopf quotient and this fixed range structure. Its two triangles and
representative formulas give unique factorization of maps and equivalences, not
uniqueness of arbitrary Hopf structures on these carriers. Antipode compatibility
uses `BialgHom.map_antipode`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Propositions 3.11–3.12, for the
  kernel and quotient factorization of commutative Hopf algebras over a field.
* Mathlib's `Ideal.quotientKerEquivRange`, `Bialgebra.mk'`,
  `HopfAlgebra.ofSurjective`, and canonical Hopf ideal quotient.
* The restricted range coalgebra and quotient factorization APIs in
  `AlgebraicGroups.Algebra.Coalgebra.Subcoalgebra.Hom` and
  `AlgebraicGroups.Algebra.Bialgebra.Quotient`.
-/

@[expose] public section

universe u v w z

namespace Ideal

/-- The ordinary algebra first-isomorphism equivalence sends a quotient
representative to the same element of the ordinary algebra range. -/
@[simp]
theorem quotientKerEquivRange_mk
    {R : Type u} {A : Type v} {B : Type w}
    [CommSemiring R] [Ring A] [Algebra R A] [Semiring B] [Algebra R B]
    (f : A →ₐ[R] B) (a : A) :
    quotientKerEquivRange f (Quotient.mk (RingHom.ker (f : A →+* B)) a) =
      f.rangeRestrict a :=
  rfl

end Ideal

namespace BialgHom

variable {K : Type u} {A : Type v} {B : Type w}
variable [Field K] [Ring A] [Semiring B] [HopfAlgebra K A] [HopfAlgebra K B]

section Construction

/-- The full Hopf algebra on the ordinary algebra range, retaining its inherited
semiring, algebra, scalar and module data and its restricted range coalgebra. -/
noncomputable instance rangeHopfAlgebra (f : A →ₐc[K] B) :
    HopfAlgebra K f.toAlgHom.range := by
  letI : AddCommGroup B := Module.addCommMonoidToAddCommGroup K
  letI : Algebra K f.toAlgHom.range := Subalgebra.algebra f.toAlgHom.range
  let c : Coalgebra K f.toAlgHom.range := f.toCoalgHom.range.coalgebra
  letI : Coalgebra K f.toAlgHom.range := c
  let r : A →ₐc[K] f.toAlgHom.range :=
    { f.toCoalgHom.rangeRestrict with
      map_one' := map_one f.toAlgHom.rangeRestrict
      map_mul' := map_mul f.toAlgHom.rangeRestrict }
  have hr : Function.Surjective r := f.toAlgHom.rangeRestrict_surjective
  letI : Bialgebra K f.toAlgHom.range :=
    @bialgebraOfSurjective K A f.toAlgHom.range _ _ _ _
      (Subalgebra.algebra f.toAlgHom.range) c r hr
  letI : HopfAlgebraStruct K f.toAlgHom.range :=
    { antipode :=
        ((HopfAlgebra.antipode K).domRestrict f.toAlgHom.range.toSubmodule).codRestrict
          f.toAlgHom.range.toSubmodule (by
            rintro ⟨b, hb⟩
            obtain ⟨a, rfl⟩ := f.toAlgHom.mem_range.mp hb
            exact f.toAlgHom.mem_range.mpr ⟨HopfAlgebra.antipode K a, f.map_antipode a⟩) }
  exact HopfAlgebra.ofSurjective r hr (by
      apply LinearMap.ext
      intro a
      apply Subtype.ext
      exact (f.map_antipode a).symm)

end Construction

/-- Corestriction to the range equipped with its Hopf coalgebra structure. -/
noncomputable def hopfRangeRestrict (f : A →ₐc[K] B) :
    @BialgHom K A f.toAlgHom.range _ _ _ _ (Subalgebra.algebra f.toAlgHom.range) _
      (rangeHopfAlgebra f).toBialgebra.toCoalgebra.toCoalgebraStruct := by
  letI : AddCommGroup B := Module.addCommMonoidToAddCommGroup K
  letI : Coalgebra K f.toAlgHom.range := f.toCoalgHom.range.coalgebra
  exact { f.toCoalgHom.rangeRestrict with
    map_one' := map_one f.toAlgHom.rangeRestrict
    map_mul' := map_mul f.toAlgHom.rangeRestrict }

/-- The Hopf range corestriction has the ordinary range corestriction as algebra map. -/
@[simp]
theorem hopfRangeRestrict_toAlgHom (f : A →ₐc[K] B) :
    (hopfRangeRestrict f).toAlgHom = f.toAlgHom.rangeRestrict := rfl

/-- The linear map of the Hopf range corestriction is ordinary corestriction. -/
theorem hopfRangeRestrict_toLinearMap (f : A →ₐc[K] B) :
    (hopfRangeRestrict f).toLinearMap = f.toAlgHom.rangeRestrict.toLinearMap :=
  congrArg AlgHom.toLinearMap (hopfRangeRestrict_toAlgHom f)

/-- The Hopf range corestriction represents the ordinary image value. -/
@[simp]
theorem hopfRangeRestrict_apply (f : A →ₐc[K] B) (a : A) :
    hopfRangeRestrict f a = f.toAlgHom.rangeRestrict a := rfl

/-- The Hopf range corestriction is surjective. -/
theorem hopfRangeRestrict_surjective (f : A →ₐc[K] B) :
    Function.Surjective (hopfRangeRestrict f) := by
  intro x
  obtain ⟨a, ha⟩ := f.toAlgHom.mem_range.mp x.property
  exact ⟨a, Subtype.ext ha⟩

/-- The inclusion of the range equipped with its Hopf coalgebra structure. -/
noncomputable def hopfRangeInclusion (f : A →ₐc[K] B) :
    @BialgHom K f.toAlgHom.range B _ _ (Subalgebra.algebra f.toAlgHom.range) _ _
      (rangeHopfAlgebra f).toBialgebra.toCoalgebra.toCoalgebraStruct _ := by
  letI : AddCommGroup B := Module.addCommMonoidToAddCommGroup K
  letI : Coalgebra K f.toAlgHom.range := f.toCoalgHom.range.coalgebra
  exact { f.toCoalgHom.range.subtype with
    map_one' := map_one f.toAlgHom.range.val
    map_mul' := map_mul f.toAlgHom.range.val }

/-- The Hopf range inclusion has the ordinary subalgebra inclusion as algebra map. -/
@[simp]
theorem hopfRangeInclusion_toAlgHom (f : A →ₐc[K] B) :
    (hopfRangeInclusion f).toAlgHom = f.toAlgHom.range.val := rfl

/-- The linear map of the Hopf range inclusion is the subtype inclusion. -/
theorem hopfRangeInclusion_toLinearMap (f : A →ₐc[K] B) :
    (hopfRangeInclusion f).toLinearMap = f.toAlgHom.range.val.toLinearMap :=
  congrArg AlgHom.toLinearMap (hopfRangeInclusion_toAlgHom f)

/-- The Hopf range inclusion is the identity on ambient values. -/
@[simp]
theorem hopfRangeInclusion_apply (f : A →ₐc[K] B) (x : f.toAlgHom.range) :
    hopfRangeInclusion f x = (x : B) := rfl

/-- The algebra parent of the range Hopf structure is the inherited subalgebra
structure, not an algebra transported from a quotient. -/
theorem rangeHopfAlgebra_toAlgebra (f : A →ₐc[K] B) :
    (rangeHopfAlgebra f).toBialgebra.toAlgebra = Subalgebra.algebra f.toAlgHom.range :=
  rfl

section RangeComparison

private theorem rangeSubtype_tensor_injective (f : A →ₐc[K] B) :
    Function.Injective
      (TensorProduct.map f.toAlgHom.range.val.toLinearMap
        f.toAlgHom.range.val.toLinearMap) := by
  let : AddCommGroup B := Module.addCommMonoidToAddCommGroup K
  let : AddCommGroup f.toAlgHom.range := Module.addCommMonoidToAddCommGroup K
  exact TensorProduct.map_injective_of_flat_flat _ _
    Subtype.coe_injective Subtype.coe_injective

/-- Counit of the Hopf range is counit of the weak range coalgebra. -/
theorem rangeHopfAlgebra_counit (f : A →ₐc[K] B) :
    @CoalgebraStruct.counit K f.toAlgHom.range _ _ _
        (rangeHopfAlgebra f).toBialgebra.toCoalgebra.toCoalgebraStruct =
      @CoalgebraStruct.counit K f.toAlgHom.range _ _ _ (rangeCoalgebraStruct f) := by
  calc
    _ = Coalgebra.counit (R := K) ∘ₗ f.toAlgHom.range.val.toLinearMap := by
      simpa only [hopfRangeInclusion_toLinearMap] using
        (@CoalgHom.counit_comp K f.toAlgHom.range B _ _ _ _ _
          (rangeHopfAlgebra f).toBialgebra.toCoalgebra.toCoalgebraStruct _
          (@BialgHom.toCoalgHom K f.toAlgHom.range B _ _
            (Subalgebra.algebra f.toAlgHom.range) _ _
            (rangeHopfAlgebra f).toBialgebra.toCoalgebra.toCoalgebraStruct _
            (hopfRangeInclusion f))).symm
    _ = _ := by
      simpa only [rangeInclusion_toLinearMap] using
        @CoalgHom.counit_comp K f.toAlgHom.range B _ _ _ _ _
          (rangeCoalgebraStruct f) _
          (@BialgHom.toCoalgHom K f.toAlgHom.range B _ _
            (Subalgebra.algebra f.toAlgHom.range) _ _
            (rangeCoalgebraStruct f) _ (rangeInclusion f))

/-- Comultiplication of the Hopf range is that of the weak range coalgebra. -/
theorem rangeHopfAlgebra_comul (f : A →ₐc[K] B) :
    @CoalgebraStruct.comul K f.toAlgHom.range _ _ _
        (rangeHopfAlgebra f).toBialgebra.toCoalgebra.toCoalgebraStruct =
      @CoalgebraStruct.comul K f.toAlgHom.range _ _ _ (rangeCoalgebraStruct f) := by
  have hH := @CoalgHom.map_comp_comul K f.toAlgHom.range B _ _ _ _ _
    (rangeHopfAlgebra f).toBialgebra.toCoalgebra.toCoalgebraStruct _
    (@BialgHom.toCoalgHom K f.toAlgHom.range B _ _
      (Subalgebra.algebra f.toAlgHom.range) _ _
      (rangeHopfAlgebra f).toBialgebra.toCoalgebra.toCoalgebraStruct _
      (hopfRangeInclusion f))
  have hW := @CoalgHom.map_comp_comul K f.toAlgHom.range B _ _ _ _ _
    (rangeCoalgebraStruct f) _
    (@BialgHom.toCoalgHom K f.toAlgHom.range B _ _
      (Subalgebra.algebra f.toAlgHom.range) _ _
      (rangeCoalgebraStruct f) _ (rangeInclusion f))
  simp only [hopfRangeInclusion_toLinearMap] at hH
  simp only [rangeInclusion_toLinearMap] at hW
  apply LinearMap.ext
  intro x
  apply rangeSubtype_tensor_injective f
  exact (LinearMap.congr_fun hH x).trans (LinearMap.congr_fun hW x).symm

/-- The identity algebra equivalence compares the Hopf and weak range coalgebras. -/
noncomputable def rangeHopfBialgEquiv (f : A →ₐc[K] B) :
    @BialgEquiv K _ f.toAlgHom.range f.toAlgHom.range _ _
      (Subalgebra.algebra f.toAlgHom.range) (Subalgebra.algebra f.toAlgHom.range)
      (rangeHopfAlgebra f).toBialgebra.toCoalgebra.toCoalgebraStruct
      (rangeCoalgebraStruct f) :=
  @BialgEquiv.mk K _ f.toAlgHom.range f.toAlgHom.range _ _
    (Subalgebra.algebra f.toAlgHom.range) (Subalgebra.algebra f.toAlgHom.range)
    (rangeHopfAlgebra f).toBialgebra.toCoalgebra.toCoalgebraStruct
    (rangeCoalgebraStruct f)
    (@CoalgEquiv.mk K _ f.toAlgHom.range f.toAlgHom.range _ _ _ _
      (rangeHopfAlgebra f).toBialgebra.toCoalgebra.toCoalgebraStruct
      (rangeCoalgebraStruct f)
      (@CoalgHom.mk K f.toAlgHom.range f.toAlgHom.range _ _ _ _ _
        (rangeHopfAlgebra f).toBialgebra.toCoalgebra.toCoalgebraStruct
        (rangeCoalgebraStruct f)
        (AlgEquiv.refl : f.toAlgHom.range ≃ₐ[K] f.toAlgHom.range).toLinearEquiv.toLinearMap
        (by
          change
            @CoalgebraStruct.counit K f.toAlgHom.range _ _ _ (rangeCoalgebraStruct f) ∘ₗ
                LinearMap.id =
              @CoalgebraStruct.counit K f.toAlgHom.range _ _ _
                (rangeHopfAlgebra f).toBialgebra.toCoalgebra.toCoalgebraStruct
          simpa only [LinearMap.comp_id] using (rangeHopfAlgebra_counit f).symm)
        (by
          change
            TensorProduct.map (LinearMap.id : f.toAlgHom.range →ₗ[K] f.toAlgHom.range)
                LinearMap.id ∘ₗ
                @CoalgebraStruct.comul K f.toAlgHom.range _ _ _
                  (rangeHopfAlgebra f).toBialgebra.toCoalgebra.toCoalgebraStruct =
              @CoalgebraStruct.comul K f.toAlgHom.range _ _ _ (rangeCoalgebraStruct f) ∘ₗ
                LinearMap.id
          simpa only [TensorProduct.map_id, LinearMap.id_comp, LinearMap.comp_id] using
            rangeHopfAlgebra_comul f))
      (fun x => x) (fun _ => rfl) (fun _ => rfl))
    (fun _ _ => rfl)

/-- The range comparison preserves the ordinary algebra equivalence. -/
@[simp]
theorem rangeHopfBialgEquiv_toAlgEquiv (f : A →ₐc[K] B) :
    @BialgEquiv.toAlgEquiv K f.toAlgHom.range f.toAlgHom.range _ _ _
        (Subalgebra.algebra f.toAlgHom.range) (Subalgebra.algebra f.toAlgHom.range)
        (rangeHopfAlgebra f).toBialgebra.toCoalgebra.toCoalgebraStruct
        (rangeCoalgebraStruct f) (rangeHopfBialgEquiv f) =
      (AlgEquiv.refl : f.toAlgHom.range ≃ₐ[K] f.toAlgHom.range) :=
  AlgEquiv.ext fun _ => rfl

/-- The range comparison is the identity on the ordinary range carrier. -/
@[simp]
theorem rangeHopfBialgEquiv_apply (f : A →ₐc[K] B) (x : f.toAlgHom.range) :
    rangeHopfBialgEquiv f x = x := rfl

/-- Comparing range structures commutes with corestriction from the source. -/
theorem rangeHopfBialgEquiv_comp_hopfRangeRestrict (f : A →ₐc[K] B) :
    @BialgHom.comp K A f.toAlgHom.range f.toAlgHom.range _ _ _ _
        _ (Subalgebra.algebra f.toAlgHom.range) (Subalgebra.algebra f.toAlgHom.range)
        _ (rangeHopfAlgebra f).toBialgebra.toCoalgebra.toCoalgebraStruct
        (rangeCoalgebraStruct f)
        (@BialgEquiv.toBialgHom K f.toAlgHom.range f.toAlgHom.range _ _ _
          (Subalgebra.algebra f.toAlgHom.range) (Subalgebra.algebra f.toAlgHom.range)
          (rangeHopfAlgebra f).toBialgebra.toCoalgebra.toCoalgebraStruct
          (rangeCoalgebraStruct f) (rangeHopfBialgEquiv f))
        (hopfRangeRestrict f) = rangeRestrict f := by
  exact DFunLike.ext _ _ fun _ => rfl

/-- Comparing range structures commutes with inclusion into the given target. -/
theorem rangeInclusion_comp_rangeHopfBialgEquiv (f : A →ₐc[K] B) :
    @BialgHom.comp K f.toAlgHom.range f.toAlgHom.range B _ _ _ _
        (Subalgebra.algebra f.toAlgHom.range) (Subalgebra.algebra f.toAlgHom.range) _
        (rangeHopfAlgebra f).toBialgebra.toCoalgebra.toCoalgebraStruct
        (rangeCoalgebraStruct f) _ (rangeInclusion f)
        (@BialgEquiv.toBialgHom K f.toAlgHom.range f.toAlgHom.range _ _ _
          (Subalgebra.algebra f.toAlgHom.range) (Subalgebra.algebra f.toAlgHom.range)
          (rangeHopfAlgebra f).toBialgebra.toCoalgebra.toCoalgebraStruct
          (rangeCoalgebraStruct f) (rangeHopfBialgEquiv f)) = hopfRangeInclusion f := by
  exact DFunLike.ext _ _ fun _ => rfl

end RangeComparison

/-- The coalgebra parent is exactly the full restricted range coalgebra. -/
theorem rangeHopfAlgebra_toCoalgebra (f : A →ₐc[K] B) :
    (rangeHopfAlgebra f).toBialgebra.toCoalgebra = rangeCoalgebra f := by
  have hε := rangeHopfAlgebra_counit f
  have hΔ := rangeHopfAlgebra_comul f
  rw [← rangeCoalgebra_toCoalgebraStruct f] at hε hΔ
  have hdata :
      (rangeHopfAlgebra f).toBialgebra.toCoalgebra.toCoalgebraStruct =
        (rangeCoalgebra f).toCoalgebraStruct := by
    generalize (rangeHopfAlgebra f).toBialgebra.toCoalgebra.toCoalgebraStruct = C
      at hε hΔ ⊢
    generalize (rangeCoalgebra f).toCoalgebraStruct = D at hε hΔ ⊢
    cases C
    cases D
    congr 1
  have hfull : ∀ (C D : Coalgebra K f.toAlgHom.range),
      C.toCoalgebraStruct = D.toCoalgebraStruct → C = D := by
    intro C D h
    cases C
    cases D
    cases h
    rfl
  exact hfull _ _ hdata

/-- Antipode on a range representative. -/
theorem antipode_rangeRestrict (f : A →ₐc[K] B) (a : A) :
    HopfAlgebra.antipode K (f.rangeRestrict a) = f.rangeRestrict (HopfAlgebra.antipode K a) := by
  have h := @BialgHom.map_antipode K A f.toAlgHom.range _ _ _ _
    (rangeHopfAlgebra f) (hopfRangeRestrict f) a
  simpa only [hopfRangeRestrict_apply, rangeRestrict_apply] using h.symm

/-- The range counit is the original target counit after inclusion. -/
theorem counit_rangeInclusion (f : A →ₐc[K] B) (x : f.toAlgHom.range) :
    Coalgebra.counit (R := K) (f.rangeInclusion x) = Coalgebra.counit (R := K) x :=
  CoalgHomClass.counit_comp_apply (hopfRangeInclusion f) x

/-- Inclusion intertwines range and ambient comultiplication. -/
theorem map_rangeInclusion_comul (f : A →ₐc[K] B) (x : f.toAlgHom.range) :
    TensorProduct.map (hopfRangeInclusion f).toLinearMap (hopfRangeInclusion f).toLinearMap
        (Coalgebra.comul (R := K) x) =
      Coalgebra.comul (R := K) (f.rangeInclusion x) :=
  CoalgHomClass.map_comp_comul_apply (hopfRangeInclusion f) x

/-- Inclusion intertwines range and ambient antipodes. -/
theorem rangeInclusion_antipode (f : A →ₐc[K] B) (x : f.toAlgHom.range) :
    f.rangeInclusion (HopfAlgebra.antipode K x) =
      HopfAlgebra.antipode K (f.rangeInclusion x) := by
  have h := @BialgHom.map_antipode K f.toAlgHom.range B _ _ _
    (rangeHopfAlgebra f) _ (hopfRangeInclusion f) x
  simpa only [hopfRangeInclusion_apply, rangeInclusion_apply] using h

/-- The restricted full range counit agrees with the selected quotient-transported
weak linear-range counit. -/
theorem range_counit_eq (f : A →ₐc[K] B) :
    Coalgebra.counit (R := K) (A := f.toAlgHom.range) =
      @CoalgebraStruct.counit K (LinearMap.range f.toLinearMap) _ _ _
        (@LinearMap.rangeCoalgebraStruct K A B _ _ _
          (Module.addCommMonoidToAddCommGroup K) _ _ f.toLinearMap
          (@CoalgHomClass.ker_isCoideal K _ A _ _ _ B
            (Module.addCommMonoidToAddCommGroup K) _ _ _ _ _ f.toCoalgHom)) := by
  let : AddCommGroup B := Module.addCommMonoidToAddCommGroup K
  let : (LinearMap.ker f.toLinearMap).IsCoideal :=
    CoalgHomClass.ker_isCoideal f.toCoalgHom
  apply LinearMap.ext
  intro x
  obtain ⟨a, rfl⟩ := f.surjective_rangeRestrict x
  exact (LinearMap.congr_fun (hopfRangeRestrict f).counit_comp a).trans
    (LinearMap.rangeCoalgebraStruct_counit_apply_rangeRestrict f.toLinearMap a).symm

/-- The restricted full range comultiplication agrees with the selected
quotient-transported weak linear-range comultiplication. -/
theorem range_comul_eq (f : A →ₐc[K] B) :
    Coalgebra.comul (R := K) (A := f.toAlgHom.range) =
      @CoalgebraStruct.comul K (LinearMap.range f.toLinearMap) _ _ _
        (@LinearMap.rangeCoalgebraStruct K A B _ _ _
          (Module.addCommMonoidToAddCommGroup K) _ _ f.toLinearMap
          (@CoalgHomClass.ker_isCoideal K _ A _ _ _ B
            (Module.addCommMonoidToAddCommGroup K) _ _ _ _ _ f.toCoalgHom)) := by
  let : AddCommGroup B := Module.addCommMonoidToAddCommGroup K
  let : (LinearMap.ker f.toLinearMap).IsCoideal :=
    CoalgHomClass.ker_isCoideal f.toCoalgHom
  apply LinearMap.ext
  intro x
  obtain ⟨a, rfl⟩ := f.surjective_rangeRestrict x
  exact (LinearMap.congr_fun (hopfRangeRestrict f).map_comp_comul a).symm.trans
    (LinearMap.rangeCoalgebraStruct_comul_apply_rangeRestrict f.toLinearMap a).symm

private theorem ker_isHopfIdeal_coe (f : A →ₐc[K] B) :
    Ideal.IsHopfIdeal K (RingHom.ker (f.toAlgHom : A →+* B)) := by
  simpa only [AlgHom.toRingHom_eq_coe] using f.ker_isHopfIdeal

end BialgHom

namespace BialgHom

/-- Over a field, the scalar restriction of the ordinary ring kernel of a
bialgebra-structure-preserving map is a coideal. Only counit and comultiplication
data are needed, not the coalgebra laws or antipodes. The source retains its
given ring structure, and the target need only be a semiring. -/
theorem ker_restrictScalars_isCoideal
    {K : Type u} {A : Type v} {B : Type w}
    [Field K] [Ring A] [Semiring B] [Algebra K A] [Algebra K B]
    [CoalgebraStruct K A] [CoalgebraStruct K B] (f : A →ₐc[K] B) :
    ((RingHom.ker (f.toAlgHom : A →+* B)).restrictScalars K).IsCoideal := by
  let : AddCommGroup B := Module.addCommMonoidToAddCommGroup K
  have hker : LinearMap.ker f.toLinearMap =
      (RingHom.ker f.toAlgHom.toRingHom).restrictScalars K := by
    ext x
    simp only [LinearMap.mem_ker, Submodule.restrictScalars_mem, RingHom.mem_ker,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, BialgHom.coe_toAlgHom]
    rfl
  have hco : ((RingHom.ker f.toAlgHom.toRingHom).restrictScalars K).IsCoideal := by
    rw [← hker]
    exact CoalgHomClass.ker_isCoideal f.toCoalgHom
  simpa only [AlgHom.toRingHom_eq_coe] using hco

variable {K : Type u} {A : Type v} {B : Type w}
variable [Field K] [Ring A] [Semiring B] [HopfAlgebra K A] [HopfAlgebra K B]

/-- The first isomorphism theorem for Hopf algebras on the ordinary ideal quotient
and ordinary algebra range, with their fixed full Hopf structures. Its underlying
algebra equivalence is `Ideal.quotientKerEquivRange`. -/
noncomputable def quotientKerEquivRange (f : A →ₐc[K] B) :
    @BialgEquiv K _ (A ⧸ RingHom.ker (f.toAlgHom : A →+* B)) f.toAlgHom.range _ _
      (Ideal.Quotient.algebra K) (Subalgebra.algebra f.toAlgHom.range)
      (@Bialgebra.Quotient.instQuotientIdeal K A _ _ _
        (RingHom.ker (f.toAlgHom : A →+* B)) _
        (ker_restrictScalars_isCoideal f)).toCoalgebra.toCoalgebraStruct
      (rangeHopfAlgebra f).toBialgebra.toCoalgebra.toCoalgebraStruct := by
  let : ((RingHom.ker (f.toAlgHom : A →+* B)).restrictScalars K).IsCoideal :=
    ker_restrictScalars_isCoideal f
  have hf : RingHom.ker (f.toAlgHom : A →+* B) ≤
      RingHom.ker ((hopfRangeRestrict f).toAlgHom : A →+* f.toAlgHom.range) := by
    rw [hopfRangeRestrict_toAlgHom]
    exact (AlgHom.ker_rangeRestrict f.toAlgHom).ge
  let g := Bialgebra.Quotient.liftBialgHom (RingHom.ker (f.toAlgHom : A →+* B))
    (hopfRangeRestrict f) hf
  have he : (Ideal.quotientKerEquivRange f.toAlgHom).toAlgHom = g.toAlgHom := by
    apply AlgHom.ext
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact (Ideal.quotientKerEquivRange_mk f.toAlgHom a).trans
      (Bialgebra.Quotient.liftBialgHom_mk _ (hopfRangeRestrict f) hf a).symm
  refine @BialgEquiv.ofAlgEquiv K
    (A ⧸ RingHom.ker (f.toAlgHom : A →+* B)) f.toAlgHom.range _ _ _
    (@Bialgebra.Quotient.instQuotientIdeal K A _ _ _
      (RingHom.ker (f.toAlgHom : A →+* B)) _ (ker_restrictScalars_isCoideal f))
    (rangeHopfAlgebra f).toBialgebra (Ideal.quotientKerEquivRange f.toAlgHom) ?_ ?_
  -- Congruence transports the laws without rewriting the fixed algebra parents.
  · exact (congrArg
        (fun h : (A ⧸ RingHom.ker (f.toAlgHom : A →+* B)) →ₐ[K] f.toAlgHom.range =>
          (Bialgebra.counitAlgHom K f.toAlgHom.range).comp h) he).trans
        g.counitAlgHom_comp
  · exact (congrArg
        (fun h : (A ⧸ RingHom.ker (f.toAlgHom : A →+* B)) →ₐ[K] f.toAlgHom.range =>
          (Algebra.TensorProduct.map h h).comp
              (Bialgebra.comulAlgHom K (A ⧸ RingHom.ker (f.toAlgHom : A →+* B))) =
            (Bialgebra.comulAlgHom K f.toAlgHom.range).comp h) he).mpr
        g.map_comp_comulAlgHom

-- Projections and compositions use the same fixed quotient data as the equivalence.
-- Typeclass search cannot recover the morphism from its ordinary ring kernel.
@[simp]
theorem quotientKerEquivRange_toAlgEquiv (f : A →ₐc[K] B) :
    @BialgEquiv.toAlgEquiv K
        (A ⧸ RingHom.ker (f.toAlgHom : A →+* B)) f.toAlgHom.range _ _ _
        (Ideal.Quotient.algebra K) (Subalgebra.algebra f.toAlgHom.range)
        (@Bialgebra.Quotient.instQuotientIdeal K A _ _ _
          (RingHom.ker (f.toAlgHom : A →+* B)) _
          (ker_restrictScalars_isCoideal f)).toCoalgebra.toCoalgebraStruct
        (rangeHopfAlgebra f).toBialgebra.toCoalgebra.toCoalgebraStruct
        f.quotientKerEquivRange = Ideal.quotientKerEquivRange f.toAlgHom := rfl

/-- Evaluation of the Hopf first-isomorphism equivalence on a representative. -/
@[simp]
theorem quotientKerEquivRange_mk (f : A →ₐc[K] B) (a : A) :
    f.quotientKerEquivRange (Ideal.Quotient.mk (RingHom.ker (f.toAlgHom : A →+* B)) a) =
      f.rangeRestrict a :=
  Ideal.quotientKerEquivRange_mk f.toAlgHom a

/-- Evaluation of the inverse equivalence on a range representative. -/
@[simp]
theorem quotientKerEquivRange_symm_rangeRestrict (f : A →ₐc[K] B) (a : A) :
    @BialgEquiv.symm K
        (A ⧸ RingHom.ker (f.toAlgHom : A →+* B)) f.toAlgHom.range _ _ _
        (Ideal.Quotient.algebra K) (Subalgebra.algebra f.toAlgHom.range)
        (@Bialgebra.Quotient.instQuotientIdeal K A _ _ _
          (RingHom.ker (f.toAlgHom : A →+* B)) _
          (ker_restrictScalars_isCoideal f)).toCoalgebra.toCoalgebraStruct
        (rangeHopfAlgebra f).toBialgebra.toCoalgebra.toCoalgebraStruct
        f.quotientKerEquivRange (f.rangeRestrict a) =
      Ideal.Quotient.mk (RingHom.ker (f.toAlgHom : A →+* B)) a := by
  apply f.quotientKerEquivRange.injective
  exact (EquivLike.right_inv f.quotientKerEquivRange _).trans
    (quotientKerEquivRange_mk f a).symm

/-- The first triangle: equivalence after quotient projection is corestriction. -/
@[simp]
theorem quotientKerEquivRange_comp_mkBialgHom (f : A →ₐc[K] B) :
    @BialgHom.comp K A
        (A ⧸ RingHom.ker (f.toAlgHom : A →+* B)) f.toAlgHom.range _ _ _ _
        _ (Ideal.Quotient.algebra K) (Subalgebra.algebra f.toAlgHom.range) _
        (@Bialgebra.Quotient.instQuotientIdeal K A _ _ _
          (RingHom.ker (f.toAlgHom : A →+* B)) _
          (ker_restrictScalars_isCoideal f)).toCoalgebra.toCoalgebraStruct
        (rangeHopfAlgebra f).toBialgebra.toCoalgebra.toCoalgebraStruct
        (↑f.quotientKerEquivRange)
        (@Bialgebra.Quotient.mkBialgHom K A _ _ _
          (RingHom.ker (f.toAlgHom : A →+* B)) _ (ker_restrictScalars_isCoideal f)) =
      hopfRangeRestrict f := by
  apply DFunLike.ext
  intro a
  change quotientKerEquivRange f (Ideal.Quotient.mk
    (RingHom.ker (f.toAlgHom : A →+* B)) a) = hopfRangeRestrict f a
  simp only [quotientKerEquivRange_mk, rangeRestrict_apply, hopfRangeRestrict_apply]

/-- The second triangle: inclusion after equivalence is the existing quotient lift. -/
@[simp]
theorem rangeInclusion_comp_quotientKerEquivRange (f : A →ₐc[K] B) :
    @BialgHom.comp K
        (A ⧸ RingHom.ker (f.toAlgHom : A →+* B)) f.toAlgHom.range B _ _ _ _
        (Ideal.Quotient.algebra K) (Subalgebra.algebra f.toAlgHom.range) _
        (@Bialgebra.Quotient.instQuotientIdeal K A _ _ _
          (RingHom.ker (f.toAlgHom : A →+* B)) _
          (ker_restrictScalars_isCoideal f)).toCoalgebra.toCoalgebraStruct
        (rangeHopfAlgebra f).toBialgebra.toCoalgebra.toCoalgebraStruct _
        (hopfRangeInclusion f)
        (↑f.quotientKerEquivRange) =
      @Bialgebra.Quotient.liftBialgHom K A B _ _ _ _ _
        (RingHom.ker (f.toAlgHom : A →+* B)) _ (ker_restrictScalars_isCoideal f) f le_rfl := by
  let : ((RingHom.ker (f.toAlgHom : A →+* B)).restrictScalars K).IsCoideal :=
    ker_restrictScalars_isCoideal f
  apply Bialgebra.Quotient.liftBialgHom_unique
  rw [BialgHom.comp_assoc, quotientKerEquivRange_comp_mkBialgHom]
  apply BialgHom.coe_toAlgHom_injective
  simpa only [BialgHom.comp_toAlgHom, hopfRangeInclusion_toAlgHom,
    hopfRangeRestrict_toAlgHom] using AlgHom.val_comp_rangeRestrict f.toAlgHom

/-- Equivalence, inclusion and projection recover the original morphism. -/
theorem rangeInclusion_comp_quotientKerEquivRange_comp_mkBialgHom (f : A →ₐc[K] B) :
    @BialgHom.comp K A
        (A ⧸ RingHom.ker (f.toAlgHom : A →+* B)) B _ _ _ _
        _ (Ideal.Quotient.algebra K) _ _
        (@Bialgebra.Quotient.instQuotientIdeal K A _ _ _
          (RingHom.ker (f.toAlgHom : A →+* B)) _
          (ker_restrictScalars_isCoideal f)).toCoalgebra.toCoalgebraStruct _
        (@BialgHom.comp K
          (A ⧸ RingHom.ker (f.toAlgHom : A →+* B)) f.toAlgHom.range B _ _ _ _
          (Ideal.Quotient.algebra K) (Subalgebra.algebra f.toAlgHom.range) _
          (@Bialgebra.Quotient.instQuotientIdeal K A _ _ _
            (RingHom.ker (f.toAlgHom : A →+* B)) _
            (ker_restrictScalars_isCoideal f)).toCoalgebra.toCoalgebraStruct
          (rangeHopfAlgebra f).toBialgebra.toCoalgebra.toCoalgebraStruct _
          (hopfRangeInclusion f)
          (@BialgEquiv.toBialgHom K
            (A ⧸ RingHom.ker (f.toAlgHom : A →+* B)) f.toAlgHom.range _ _ _
            (Ideal.Quotient.algebra K) (Subalgebra.algebra f.toAlgHom.range)
            (@Bialgebra.Quotient.instQuotientIdeal K A _ _ _
              (RingHom.ker (f.toAlgHom : A →+* B)) _
              (ker_restrictScalars_isCoideal f)).toCoalgebra.toCoalgebraStruct
            (rangeHopfAlgebra f).toBialgebra.toCoalgebra.toCoalgebraStruct
            f.quotientKerEquivRange))
        (@Bialgebra.Quotient.mkBialgHom K A _ _ _
          (RingHom.ker (f.toAlgHom : A →+* B)) _ (ker_restrictScalars_isCoideal f)) = f := by
  let : ((RingHom.ker (f.toAlgHom : A →+* B)).restrictScalars K).IsCoideal :=
    ker_restrictScalars_isCoideal f
  rw [BialgEquiv.toBialgHom_eq_coe, BialgHom.comp_assoc,
    quotientKerEquivRange_comp_mkBialgHom]
  apply BialgHom.coe_toAlgHom_injective
  simpa only [BialgHom.comp_toAlgHom, hopfRangeInclusion_toAlgHom,
    hopfRangeRestrict_toAlgHom] using AlgHom.val_comp_rangeRestrict f.toAlgHom

/-- The first triangle uniquely determines an equivalence between these fixed
quotient and range structures. This uses quotient representative extensionality. -/
theorem quotientKerEquivRange_unique (f : A →ₐc[K] B)
    (e : @BialgEquiv K _ (A ⧸ RingHom.ker (f.toAlgHom : A →+* B)) f.toAlgHom.range _ _
      (Ideal.Quotient.algebra K) (Subalgebra.algebra f.toAlgHom.range)
      (@Bialgebra.Quotient.instQuotientIdeal K A _ _ _
        (RingHom.ker (f.toAlgHom : A →+* B)) _
        (ker_restrictScalars_isCoideal f)).toCoalgebra.toCoalgebraStruct
      (rangeHopfAlgebra f).toBialgebra.toCoalgebra.toCoalgebraStruct)
    (he : @BialgHom.comp K A
      (A ⧸ RingHom.ker (f.toAlgHom : A →+* B)) f.toAlgHom.range _ _ _ _
      _ (Ideal.Quotient.algebra K) (Subalgebra.algebra f.toAlgHom.range) _
      (@Bialgebra.Quotient.instQuotientIdeal K A _ _ _
        (RingHom.ker (f.toAlgHom : A →+* B)) _
        (ker_restrictScalars_isCoideal f)).toCoalgebra.toCoalgebraStruct
      (rangeHopfAlgebra f).toBialgebra.toCoalgebra.toCoalgebraStruct
      (@BialgEquiv.toBialgHom K
        (A ⧸ RingHom.ker (f.toAlgHom : A →+* B)) f.toAlgHom.range _ _ _
        (Ideal.Quotient.algebra K) (Subalgebra.algebra f.toAlgHom.range)
        (@Bialgebra.Quotient.instQuotientIdeal K A _ _ _
          (RingHom.ker (f.toAlgHom : A →+* B)) _
          (ker_restrictScalars_isCoideal f)).toCoalgebra.toCoalgebraStruct
        (rangeHopfAlgebra f).toBialgebra.toCoalgebra.toCoalgebraStruct e)
      (@Bialgebra.Quotient.mkBialgHom K A _ _ _
        (RingHom.ker (f.toAlgHom : A →+* B)) _ (ker_restrictScalars_isCoideal f)) =
        (hopfRangeRestrict f)) : e = f.quotientKerEquivRange := by
  let : ((RingHom.ker (f.toAlgHom : A →+* B)).restrictScalars K).IsCoideal :=
    ker_restrictScalars_isCoideal f
  have h := Bialgebra.Quotient.hom_ext (RingHom.ker (f.toAlgHom : A →+* B))
    e.toBialgHom f.quotientKerEquivRange.toBialgHom
    (he.trans (quotientKerEquivRange_comp_mkBialgHom f).symm)
  exact DFunLike.ext _ _ fun x => DFunLike.congr_fun h x

/-- The second triangle also uniquely determines the equivalence, by injectivity
of the ordinary range inclusion. -/
theorem quotientKerEquivRange_unique_of_comp_inclusion (f : A →ₐc[K] B)
    (e : @BialgEquiv K _ (A ⧸ RingHom.ker (f.toAlgHom : A →+* B)) f.toAlgHom.range _ _
      (Ideal.Quotient.algebra K) (Subalgebra.algebra f.toAlgHom.range)
      (@Bialgebra.Quotient.instQuotientIdeal K A _ _ _
        (RingHom.ker (f.toAlgHom : A →+* B)) _
        (ker_restrictScalars_isCoideal f)).toCoalgebra.toCoalgebraStruct
      (rangeHopfAlgebra f).toBialgebra.toCoalgebra.toCoalgebraStruct)
    (he : @BialgHom.comp K
      (A ⧸ RingHom.ker (f.toAlgHom : A →+* B)) f.toAlgHom.range B _ _ _ _
      (Ideal.Quotient.algebra K) (Subalgebra.algebra f.toAlgHom.range) _
      (@Bialgebra.Quotient.instQuotientIdeal K A _ _ _
        (RingHom.ker (f.toAlgHom : A →+* B)) _
        (ker_restrictScalars_isCoideal f)).toCoalgebra.toCoalgebraStruct
      (rangeHopfAlgebra f).toBialgebra.toCoalgebra.toCoalgebraStruct _
      (hopfRangeInclusion f)
      (@BialgEquiv.toBialgHom K
        (A ⧸ RingHom.ker (f.toAlgHom : A →+* B)) f.toAlgHom.range _ _ _
        (Ideal.Quotient.algebra K) (Subalgebra.algebra f.toAlgHom.range)
        (@Bialgebra.Quotient.instQuotientIdeal K A _ _ _
          (RingHom.ker (f.toAlgHom : A →+* B)) _
          (ker_restrictScalars_isCoideal f)).toCoalgebra.toCoalgebraStruct
        (rangeHopfAlgebra f).toBialgebra.toCoalgebra.toCoalgebraStruct e) =
      @Bialgebra.Quotient.liftBialgHom K A B _ _ _ _ _
        (RingHom.ker (f.toAlgHom : A →+* B)) _ (ker_restrictScalars_isCoideal f) f le_rfl) :
    e = f.quotientKerEquivRange := by
  apply DFunLike.ext _ _
  intro x
  apply f.injective_rangeInclusion
  exact DFunLike.congr_fun
    (he.trans (rangeInclusion_comp_quotientKerEquivRange f).symm) x

end BialgHom
