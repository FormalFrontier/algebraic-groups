/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Bialgebra.Quotient
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

`BialgHom.rangeRestrict` and `BialgHom.rangeInclusion` retain the ordinary algebra
maps. `BialgHom.quotientKerEquivRange` refines `Ideal.quotientKerEquivRange` between
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

/-- The full restricted coalgebra on the ordinary algebra range. The additive
group needed by the subcoalgebra construction is derived from the given module;
its additive monoid is unchanged. -/
@[instance_reducible]
noncomputable def rangeCoalgebra (f : A →ₐc[K] B) : Coalgebra K f.toAlgHom.range := by
  letI : AddCommGroup B := Module.addCommMonoidToAddCommGroup K
  exact f.toCoalgHom.range.coalgebra

attribute [local instance] rangeCoalgebra

/-- Corestrict a bialgebra homomorphism to its ordinary algebra range. -/
noncomputable def rangeRestrict (f : A →ₐc[K] B) : A →ₐc[K] f.toAlgHom.range := by
  letI : AddCommGroup B := Module.addCommMonoidToAddCommGroup K
  exact { f.toCoalgHom.rangeRestrict with
    map_one' := map_one f.toAlgHom.rangeRestrict
    map_mul' := map_mul f.toAlgHom.rangeRestrict }

@[simp]
theorem rangeRestrict_toAlgHom (f : A →ₐc[K] B) :
    f.rangeRestrict.toAlgHom = f.toAlgHom.rangeRestrict := rfl

@[simp]
theorem rangeRestrict_toLinearMap (f : A →ₐc[K] B) :
    (f.rangeRestrict.toCoalgHom : A →ₗ[K] f.toAlgHom.range) =
      f.toAlgHom.rangeRestrict.toLinearMap := rfl

/-- Corestriction is the same range member as ordinary algebra corestriction. -/
theorem rangeRestrict_apply (f : A →ₐc[K] B) (a : A) :
    f.rangeRestrict a = f.toAlgHom.rangeRestrict a := rfl

@[simp]
theorem coe_rangeRestrict (f : A →ₐc[K] B) (a : A) :
    (f.rangeRestrict a : B) = f a := rfl

/-- Range corestriction is surjective, without a surjectivity assumption on `f`. -/
theorem surjective_rangeRestrict (f : A →ₐc[K] B) : Function.Surjective f.rangeRestrict :=
  f.toAlgHom.rangeRestrict_surjective

/-- Counit on a range representative. -/
theorem counit_rangeRestrict (f : A →ₐc[K] B) (a : A) :
    Coalgebra.counit (R := K) (f.rangeRestrict a) = Coalgebra.counit (R := K) a :=
  CoalgHomClass.counit_comp_apply f.rangeRestrict a

/-- Comultiplication on a range representative. -/
theorem comul_rangeRestrict (f : A →ₐc[K] B) (a : A) :
    Coalgebra.comul (R := K) (f.rangeRestrict a) =
      TensorProduct.map f.rangeRestrict.toLinearMap f.rangeRestrict.toLinearMap
        (Coalgebra.comul (R := K) a) :=
  (CoalgHomClass.map_comp_comul_apply f.rangeRestrict a).symm

/-- The full Hopf algebra on the ordinary algebra range, retaining its inherited
semiring, algebra, scalar and module data and its restricted range coalgebra. -/
noncomputable instance rangeHopfAlgebra (f : A →ₐc[K] B) :
    HopfAlgebra K f.toAlgHom.range := by
  letI : Bialgebra K f.toAlgHom.range := by
    refine Bialgebra.mk' K f.toAlgHom.range ?_ (fun {x y} => ?_) ?_ (fun {x y} => ?_)
    · rw [← map_one f.rangeRestrict, counit_rangeRestrict, Bialgebra.counit_one]
    · obtain ⟨a, rfl⟩ := f.surjective_rangeRestrict x
      obtain ⟨b, rfl⟩ := f.surjective_rangeRestrict y
      rw [← map_mul f.rangeRestrict, counit_rangeRestrict,
        counit_rangeRestrict, counit_rangeRestrict, Bialgebra.counit_mul]
    · rw [← map_one f.rangeRestrict, comul_rangeRestrict, Bialgebra.comul_one]
      exact map_one (Algebra.TensorProduct.map f.rangeRestrict.toAlgHom
        f.rangeRestrict.toAlgHom)
    · obtain ⟨a, rfl⟩ := f.surjective_rangeRestrict x
      obtain ⟨b, rfl⟩ := f.surjective_rangeRestrict y
      rw [← map_mul f.rangeRestrict, comul_rangeRestrict,
        comul_rangeRestrict, comul_rangeRestrict, Bialgebra.comul_mul]
      exact map_mul (Algebra.TensorProduct.map f.rangeRestrict.toAlgHom
        f.rangeRestrict.toAlgHom) _ _
  letI : HopfAlgebraStruct K f.toAlgHom.range :=
    { antipode :=
        ((HopfAlgebra.antipode K).domRestrict f.toAlgHom.range.toSubmodule).codRestrict
          f.toAlgHom.range.toSubmodule (by
            rintro ⟨b, hb⟩
            obtain ⟨a, rfl⟩ := f.toAlgHom.mem_range.mp hb
            exact f.toAlgHom.mem_range.mpr ⟨HopfAlgebra.antipode K a, f.map_antipode a⟩) }
  exact HopfAlgebra.ofSurjective f.rangeRestrict f.surjective_rangeRestrict (by
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    exact (f.map_antipode a).symm)

end Construction

/-- The algebra parent of the range Hopf structure is the inherited subalgebra
structure, not an algebra transported from a quotient. -/
theorem rangeHopfAlgebra_toAlgebra (f : A →ₐc[K] B) :
    (rangeHopfAlgebra f).toBialgebra.toAlgebra = Subalgebra.algebra f.toAlgHom.range :=
  rfl

/-- The coalgebra parent is exactly the full restricted range coalgebra. -/
theorem rangeHopfAlgebra_toCoalgebra (f : A →ₐc[K] B) :
    (rangeHopfAlgebra f).toBialgebra.toCoalgebra = rangeCoalgebra f :=
  rfl

/-- The inclusion of the ordinary algebra range as a bialgebra homomorphism. -/
noncomputable def rangeInclusion (f : A →ₐc[K] B) : f.toAlgHom.range →ₐc[K] B := by
  letI : AddCommGroup B := Module.addCommMonoidToAddCommGroup K
  exact { f.toCoalgHom.range.subtype with
    map_one' := map_one f.toAlgHom.range.val
    map_mul' := map_mul f.toAlgHom.range.val }

@[simp]
theorem rangeInclusion_toAlgHom (f : A →ₐc[K] B) :
    f.rangeInclusion.toAlgHom = f.toAlgHom.range.val := rfl

@[simp]
theorem rangeInclusion_apply (f : A →ₐc[K] B) (x : f.toAlgHom.range) :
    f.rangeInclusion x = (x : B) := rfl

@[simp]
theorem rangeInclusion_comp_rangeRestrict (f : A →ₐc[K] B) :
    f.rangeInclusion.comp f.rangeRestrict = f :=
  BialgHom.ext fun _ => rfl

/-- The range inclusion is injective, without an injectivity assumption on `f`. -/
theorem injective_rangeInclusion (f : A →ₐc[K] B) : Function.Injective f.rangeInclusion :=
  Subtype.val_injective

/-- A corestriction through the same ordinary range inclusion is unique. -/
theorem rangeRestrict_unique (f : A →ₐc[K] B) (g : A →ₐc[K] f.toAlgHom.range)
    (hg : f.rangeInclusion.comp g = f) : g = f.rangeRestrict := by
  apply BialgHom.ext
  intro a
  apply f.injective_rangeInclusion
  exact BialgHom.congr_fun hg a

/-- Maps from the fixed range are determined by their values on original
representatives, equivalently by precomposition with range corestriction. -/
theorem rangeRestrict_comp_injective {C : Type z} [Semiring C] [Algebra K C]
    [CoalgebraStruct K C] (f : A →ₐc[K] B) :
    Function.Injective (fun g : f.toAlgHom.range →ₐc[K] C => g.comp f.rangeRestrict) := by
  intro g h hcomp
  apply BialgHom.ext
  intro x
  obtain ⟨a, rfl⟩ := f.surjective_rangeRestrict x
  exact BialgHom.congr_fun hcomp a

/-- Antipode on a range representative. -/
theorem antipode_rangeRestrict (f : A →ₐc[K] B) (a : A) :
    HopfAlgebra.antipode K (f.rangeRestrict a) = f.rangeRestrict (HopfAlgebra.antipode K a) :=
  (f.rangeRestrict.map_antipode a).symm

/-- The range counit is the original target counit after inclusion. -/
theorem counit_rangeInclusion (f : A →ₐc[K] B) (x : f.toAlgHom.range) :
    Coalgebra.counit (R := K) (f.rangeInclusion x) = Coalgebra.counit (R := K) x :=
  CoalgHomClass.counit_comp_apply f.rangeInclusion x

/-- Inclusion intertwines range and ambient comultiplication. -/
theorem map_rangeInclusion_comul (f : A →ₐc[K] B) (x : f.toAlgHom.range) :
    TensorProduct.map f.rangeInclusion.toLinearMap f.rangeInclusion.toLinearMap
        (Coalgebra.comul (R := K) x) =
      Coalgebra.comul (R := K) (f.rangeInclusion x) :=
  CoalgHomClass.map_comp_comul_apply f.rangeInclusion x

/-- Inclusion intertwines range and ambient antipodes. -/
theorem rangeInclusion_antipode (f : A →ₐc[K] B) (x : f.toAlgHom.range) :
    f.rangeInclusion (HopfAlgebra.antipode K x) =
      HopfAlgebra.antipode K (f.rangeInclusion x) :=
  f.rangeInclusion.map_antipode x

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
  exact (counit_rangeRestrict f a).trans
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
  exact (comul_rangeRestrict f a).trans
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
      RingHom.ker (f.rangeRestrict.toAlgHom : A →+* f.toAlgHom.range) := by
    rw [rangeRestrict_toAlgHom]
    exact (AlgHom.ker_rangeRestrict f.toAlgHom).ge
  let g := Bialgebra.Quotient.liftBialgHom (RingHom.ker (f.toAlgHom : A →+* B))
    f.rangeRestrict hf
  have he : (Ideal.quotientKerEquivRange f.toAlgHom).toAlgHom = g.toAlgHom := by
    apply AlgHom.ext
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact (Ideal.quotientKerEquivRange_mk f.toAlgHom a).trans
      (Bialgebra.Quotient.liftBialgHom_mk _ f.rangeRestrict hf a).symm
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
      f.rangeRestrict := by
  apply BialgHom.ext
  intro a
  exact quotientKerEquivRange_mk f a

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
        f.rangeInclusion
        (↑f.quotientKerEquivRange) =
      @Bialgebra.Quotient.liftBialgHom K A B _ _ _ _ _
        (RingHom.ker (f.toAlgHom : A →+* B)) _ (ker_restrictScalars_isCoideal f) f le_rfl := by
  let : ((RingHom.ker (f.toAlgHom : A →+* B)).restrictScalars K).IsCoideal :=
    ker_restrictScalars_isCoideal f
  apply Bialgebra.Quotient.liftBialgHom_unique
  rw [BialgHom.comp_assoc, quotientKerEquivRange_comp_mkBialgHom,
    rangeInclusion_comp_rangeRestrict]

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
          f.rangeInclusion
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
    quotientKerEquivRange_comp_mkBialgHom, rangeInclusion_comp_rangeRestrict]

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
        f.rangeRestrict) : e = f.quotientKerEquivRange := by
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
      f.rangeInclusion
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
