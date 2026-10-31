/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.CoidealCorrespondence
public import AlgebraicGroups.Algebra.HopfAlgebra.Hom
public import Mathlib.RingTheory.HopfAlgebra.Quotient

/-!
# Hopf ideals and the surjective ideal correspondence

For full Hopf algebras and a bundled bialgebra homomorphism, inverse images
preserve `Ideal.IsHopfIdeal` whenever the scalar-restricted ordinary ideal
preimage is a coideal. The corresponding kernel theorem assumes precisely the
coideality of the scalar-restricted ordinary ring kernel. Over a field, both
coideality conditions follow without additional hypotheses. For a surjective
bialgebra homomorphism over a commutative ring, the ordinary ideal
correspondence restricts to the Hopf-ideal predicates: target Hopf ideals
correspond to source Hopf ideals containing the ordinary ring kernel.

The source and target rings need not be commutative. The kernel theorems allow
a semiring target. The property `Ideal.IsHopfIdeal` consists of restricted
coideality and antipode stability; two-sidedness is not a field of this predicate. A quotient
ring or quotient Hopf algebra requires the separate two-sidedness condition.

## References

* J. S. Milne, *Algebraic Groups*, Proposition 3.11, for kernels as Hopf ideals.
* Mathlib, `Mathlib.RingTheory.HopfAlgebra.Quotient`, for `Ideal.IsHopfIdeal`.
* `AlgebraicGroups.Algebra.HopfAlgebra.Hom`, for compatibility of bialgebra
  homomorphisms with antipodes.
* `AlgebraicGroups.Algebra.Coalgebra.Quotient`, for field kernel coideality,
  and Mathlib, `Mathlib.RingTheory.Coalgebra.Quotient`, for the linear
  coalgebra quotient used for inverse images.
-/

@[expose] public section

universe u v w

/-- The inverse image of an ideal with the Hopf-ideal property has that property
if its scalar-restricted ordinary ideal preimage is a coideal. This does not
assert two-sidedness of either ideal. -/
theorem Ideal.IsHopfIdeal.comap_of_isCoideal
    {R : Type u} {A : Type v} {B : Type w}
    [CommRing R] [Ring A] [Ring B]
    [HopfAlgebra R A] [HopfAlgebra R B]
    {J : Ideal B} (hJ : Ideal.IsHopfIdeal R J) (f : A →ₐc[R] B)
    (hco : ((J.comap f.toAlgHom.toRingHom).restrictScalars R).IsCoideal) :
    Ideal.IsHopfIdeal R (J.comap f.toAlgHom.toRingHom) := by
  refine
    { toIsCoideal := hco
      antipode_mem := ?_ }
  intro x hx
  change f (HopfAlgebra.antipode R x) ∈ J
  rw [f.map_antipode]
  exact hJ.antipode_mem (Ideal.mem_comap.mp hx)

/-- The ordinary ring kernel of a bialgebra homomorphism between full Hopf
algebras has the Hopf-ideal property if its scalar restriction is a coideal.
The target need only be a semiring. -/
theorem BialgHom.ker_isHopfIdeal_of_isCoideal
    {R : Type u} {A : Type v} {B : Type w}
    [CommRing R] [Ring A] [Semiring B]
    [HopfAlgebra R A] [HopfAlgebra R B]
    (f : A →ₐc[R] B)
    (hco : ((RingHom.ker f.toAlgHom.toRingHom).restrictScalars R).IsCoideal) :
    Ideal.IsHopfIdeal R (RingHom.ker f.toAlgHom.toRingHom) := by
  refine
    { toIsCoideal := hco
      antipode_mem := ?_ }
  intro x hx
  have hfx : f x = 0 := RingHom.mem_ker.mp hx
  change f (HopfAlgebra.antipode R x) = 0
  rw [f.map_antipode, hfx, map_zero]

/-- Over a field, inverse images along bialgebra homomorphisms between full
Hopf algebras preserve the Hopf-ideal property. No coideality, surjectivity or
two-sidedness hypothesis is needed beyond the target ideal's Hopf-ideal
property. -/
theorem Ideal.IsHopfIdeal.comap
    {k : Type u} {A : Type v} {B : Type w}
    [Field k] [Ring A] [Ring B]
    [HopfAlgebra k A] [HopfAlgebra k B]
    {J : Ideal B} (hJ : Ideal.IsHopfIdeal k J) (f : A →ₐc[k] B) :
    Ideal.IsHopfIdeal k (J.comap f.toAlgHom.toRingHom) := by
  let : (J.restrictScalars k).IsCoideal := hJ.toIsCoideal
  let q := Coalgebra.Quotient.mkQCoalgHom (J.restrictScalars k)
  let g := q.comp f.toCoalgHom
  have hker : LinearMap.ker g.toLinearMap =
      (J.comap f.toAlgHom.toRingHom).restrictScalars k := by
    ext x
    change Submodule.Quotient.mk (p := J.restrictScalars k) (f x) = 0 ↔
      x ∈ (J.comap f.toAlgHom.toRingHom).restrictScalars k
    simp only [Submodule.Quotient.mk_eq_zero, Submodule.restrictScalars_mem, Ideal.mem_comap,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, BialgHom.coe_toAlgHom]
  apply hJ.comap_of_isCoideal f
  rw [← hker]
  exact CoalgHomClass.ker_isCoideal g

/-- Over a field, the ordinary ring kernel of a bialgebra homomorphism between
full Hopf algebras has the Hopf-ideal property, without an additional coideality
or surjectivity hypothesis. The target need only be a semiring. This generalizes
Milne, *Algebraic Groups*, Proposition 3.11, taking a full bundled bialgebra
homomorphism as input and allowing noncommutative source rings. -/
theorem BialgHom.ker_isHopfIdeal
    {k : Type u} {A : Type v} {B : Type w}
    [Field k] [Ring A] [Semiring B]
    [HopfAlgebra k A] [HopfAlgebra k B]
    (f : A →ₐc[k] B) :
    Ideal.IsHopfIdeal k (RingHom.ker f.toAlgHom.toRingHom) := by
  let : AddCommGroup B := Module.addCommMonoidToAddCommGroup k
  have hker : LinearMap.ker f.toLinearMap =
      (RingHom.ker f.toAlgHom.toRingHom).restrictScalars k := by
    ext x
    simp only [LinearMap.mem_ker, Submodule.restrictScalars_mem, RingHom.mem_ker,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, BialgHom.coe_toAlgHom]
    rfl
  apply f.ker_isHopfIdeal_of_isCoideal
  rw [← hker]
  exact CoalgHomClass.ker_isCoideal f.toCoalgHom

/-- For a surjective algebra homomorphism, restricting scalars turns the ordinary
ideal image into the image under the same scalar-linear map. -/
theorem Ideal.restrictScalars_map_of_surjective
    {R : Type u} {A : Type v} {B : Type w}
    [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) (hf : Function.Surjective f) (I : Ideal A) :
    (I.map f.toRingHom).restrictScalars R = (I.restrictScalars R).map f.toLinearMap := by
  ext y
  change y ∈ I.map f.toRingHom ↔ y ∈ (I.restrictScalars R).map f.toLinearMap
  rw [Ideal.mem_map_iff_of_surjective f.toRingHom hf, Submodule.mem_map]
  rfl

/-- The ordinary ideal image under a surjective bialgebra homomorphism between
full Hopf algebras has the Hopf-ideal property. -/
theorem Ideal.IsHopfIdeal.map_of_surjective
    {R : Type u} {A : Type v} {B : Type w}
    [CommRing R] [Ring A] [Ring B] [HopfAlgebra R A] [HopfAlgebra R B]
    {I : Ideal A} (hI : Ideal.IsHopfIdeal R I) (f : A →ₐc[R] B)
    (hf : Function.Surjective f) : Ideal.IsHopfIdeal R (I.map f.toAlgHom.toRingHom) := by
  refine { toIsCoideal := ?_, antipode_mem := ?_ }
  · rw [Ideal.restrictScalars_map_of_surjective f.toAlgHom hf]
    exact hI.toIsCoideal.map f.toCoalgHom
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := (Ideal.mem_map_iff_of_surjective f.toAlgHom.toRingHom hf).mp hy
    change HopfAlgebra.antipode R (f x) ∈ I.map f.toAlgHom.toRingHom
    rw [← f.map_antipode]
    exact Ideal.mem_map_of_mem _ (hI.antipode_mem hx)

section SurjectiveCorrespondence

variable {R : Type u} {A : Type v} {B : Type w}
  [CommRing R] [Ring A] [Ring B] [HopfAlgebra R A] [HopfAlgebra R B]

/-- The ordinary ideal correspondence for a surjective bialgebra homomorphism,
restricted to the Hopf-ideal predicates. The forward map is ordinary ideal
preimage, and its inverse is ordinary ideal image. The source interval uses
the ordinary ring kernel of the same homomorphism. -/
noncomputable def Ideal.hopfIdealOrderIsoOfSurjective (f : A →ₐc[R] B)
    (hf : Function.Surjective f) :
    {J : Ideal B // Ideal.IsHopfIdeal R J} ≃o
      {I : Ideal A // Ideal.IsHopfIdeal R I ∧ RingHom.ker (f.toAlgHom : A →+* B) ≤ I} := by
  let e := Ideal.relIsoOfSurjective (f.toAlgHom : A →+* B) hf
  let g : {J : Ideal B // Ideal.IsHopfIdeal R J} →
      {I : Ideal A // Ideal.IsHopfIdeal R I ∧ RingHom.ker (f.toAlgHom : A →+* B) ≤ I} :=
    fun J => ⟨(e J.val).val, by
      refine ⟨J.property.comap_of_isCoideal f ?_, (e J.val).property⟩
      change ((J.val.restrictScalars R).comap f.toLinearMap).IsCoideal
      exact J.property.toIsCoideal.comap_of_surjective f.toCoalgHom hf⟩
  refine OrderIso.ofSurjective (OrderEmbedding.ofMapLEIff g ?_) ?_
  · intro J L
    change e J.val ≤ e L.val ↔ J.val ≤ L.val
    exact e.map_rel_iff
  · intro I
    refine ⟨⟨e.symm ⟨I.val, I.property.2⟩, ?_⟩, ?_⟩
    · exact I.property.1.map_of_surjective f hf
    · apply Subtype.ext
      change (e (e.symm ⟨I.val, I.property.2⟩)).val = I.val
      exact congrArg
        (fun K : {K : Ideal A // RingHom.ker (f.toAlgHom : A →+* B) ≤ K} => K.val)
        (e.apply_symm_apply ⟨I.val, I.property.2⟩)

/-- The forward correspondence is ordinary ideal preimage. -/
@[simp]
theorem Ideal.hopfIdealOrderIsoOfSurjective_apply_val (f : A →ₐc[R] B)
    (hf : Function.Surjective f) (J : {J : Ideal B // Ideal.IsHopfIdeal R J}) :
    (Ideal.hopfIdealOrderIsoOfSurjective f hf J).val =
      J.val.comap (f.toAlgHom : A →+* B) :=
  rfl

/-- The inverse correspondence is ordinary ideal image. -/
@[simp]
theorem Ideal.hopfIdealOrderIsoOfSurjective_symm_apply_val (f : A →ₐc[R] B)
    (hf : Function.Surjective f)
    (I : {I : Ideal A // Ideal.IsHopfIdeal R I ∧ RingHom.ker (f.toAlgHom : A →+* B) ≤ I}) :
    ((Ideal.hopfIdealOrderIsoOfSurjective f hf).symm I).val =
      I.val.map (f.toAlgHom : A →+* B) := by
  let e := Ideal.relIsoOfSurjective (f.toAlgHom : A →+* B) hf
  have h : (((Ideal.hopfIdealOrderIsoOfSurjective f hf).symm I).val).comap
      (f.toAlgHom : A →+* B) = I.val := by
    simpa only [Ideal.hopfIdealOrderIsoOfSurjective_apply_val] using
      congrArg Subtype.val ((Ideal.hopfIdealOrderIsoOfSurjective f hf).apply_symm_apply I)
  calc
    _ = e.symm (e (((Ideal.hopfIdealOrderIsoOfSurjective f hf).symm I).val)) :=
      (e.symm_apply_apply _).symm
    _ = e.symm ⟨I.val, I.property.2⟩ := congrArg e.symm (Subtype.ext h)
    _ = I.val.map (f.toAlgHom : A →+* B) := rfl

end SurjectiveCorrespondence
