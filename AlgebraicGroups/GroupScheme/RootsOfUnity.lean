/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import AlgebraicGroups.GroupScheme.Multiplicative

import all Mathlib.RingTheory.Bialgebra.MonoidAlgebra -- to unfold `AddMonoidAlgebra.liftMulEquiv`

/-!
# Roots-of-unity group schemes at all orders

This file packages the affine group scheme represented by the Hopf algebra
`K[ZMod n]` and identifies its points with the `n`-th roots of unity.
For positive `n`, Milne's *Algebraic Groups*, item 2.4, gives the roots-of-unity
functor, the quotient `k[T]/(T ^ n - 1)` and the multiplication-induced
comultiplication `T ↦ T ⊗ T` over a field. The construction here uses the
cyclic group algebra over any commutative base and represents roots of unity
for every natural `n`. At `n = 0`, every unit is a root, `ZMod 0` is `ℤ`, and
the coordinate Hopf algebra is the Laurent algebra of the existing multiplicative
group scheme. This zero-order extension is beyond Milne's positive-order item.

The polynomial quotient equivalence and its `T ^ (n - 1)` antipode formula
require `[NeZero n]` (equivalently, positive `n`). At zero the coordinate algebra
is Laurent, not the polynomial algebra `K[T]/(T ^ 0 - 1)`.

## Main definitions

- `AlgebraicGeometry.rootsOfUnityGroupScheme`
- `AlgebraicGeometry.rootsOfUnityMulEquivPoints`
- `AlgebraicGeometry.rootsOfUnityPointsIso`
- `AlgebraicGeometry.rootsOfUnityGroupSchemeZeroIsoMultiplicativeGroup`
- `AlgebraicGeometry.rootsOfUnityCoordinateAlgEquiv`
- `AlgebraicGeometry.rootsOfUnityCoordinateAlgEquiv_symm_root_isGroupLike`

## References

- James S. Milne, *Algebraic Groups* (2017), item 2.4, p. 40 (positive-order
  roots of unity, the quotient coordinate and multiplicative comultiplication).
- Mathlib, `Mathlib.RingTheory.RootsOfUnity.Basic`,
  `Mathlib.RingTheory.Bialgebra.MonoidAlgebra`,
  `Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra`, and
  `Mathlib.RingTheory.AdjoinRoot` (root construction, group-algebra Hopf
  structure and the polynomial quotient presentation).
- Mathlib, `Mathlib.AlgebraicGeometry.Group.Affine` (the affine Hopf `Spec`
  construction and points equivalence used here).
-/

@[expose] public section

noncomputable section

open CategoryTheory Polynomial
open scoped CategoryTheory.MonObj

universe u v w t

namespace AlgebraicGeometry

/-- The cyclic group-algebra coordinate ring of the roots-of-unity group scheme. -/
abbrev rootsOfUnityCoordinateRing (K : Type u) [CommRing K] (n : ℕ) :=
  AddMonoidAlgebra K (ZMod n)

instance rootsOfUnityCoordinateRing_finiteType
    (K : Type u) [CommRing K] (n : ℕ) [NeZero n] :
    Algebra.FiniteType K (rootsOfUnityCoordinateRing K n) := by
  infer_instance

/-- The affine scheme over `K` represented by `K[ZMod n]`. -/
abbrev rootsOfUnityScheme (K : Type u) [CommRing K] (n : ℕ) :
    Over (Spec (.of K)) :=
  (Spec (.of (rootsOfUnityCoordinateRing K n))).asOver (Spec (.of K))

instance rootsOfUnityScheme_locallyOfFiniteType
    (K : Type u) [CommRing K] (n : ℕ) [NeZero n] :
    LocallyOfFiniteType (rootsOfUnityScheme K n).hom := by
  let _ : Algebra.FiniteType K (rootsOfUnityCoordinateRing K n) :=
    rootsOfUnityCoordinateRing_finiteType K n
  change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
    (algebraMap K (rootsOfUnityCoordinateRing K n))))
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  simpa [RingHom.finiteType_algebraMap]

instance rootsOfUnityScheme_quasiCompact
    (K : Type u) [CommRing K] (n : ℕ) [NeZero n] :
    QuasiCompact (rootsOfUnityScheme K n).hom := by
  change QuasiCompact (Spec.map (CommRingCat.ofHom
    (algebraMap K (rootsOfUnityCoordinateRing K n))))
  infer_instance

/-- The roots-of-unity group scheme, using the standard Hopf structure on
`K[ZMod n]`. For positive `n` this represents the group in Milne's
*Algebraic Groups*, item 2.4; the construction itself also allows `n = 0`. -/
abbrev rootsOfUnityGroupScheme (K : Type u) [CommRing K] (n : ℕ) :
    Grp (Over (Spec (.of K))) :=
  ⟨rootsOfUnityScheme K n⟩

/-- The group-valued functor sending a `K`-algebra to its group of `n`-th
roots of unity. -/
def rootsOfUnityFunctor (K : Type u) [CommRing K] (n : ℕ) :
    CommAlgCat K ⥤ GrpCat where
  obj R := GrpCat.of (rootsOfUnity n R)
  map f := GrpCat.ofHom (restrictRootsOfUnity f.hom n)
  map_id R := by
    ext ζ
    simp
  map_comp f g := by
    ext ζ
    simp

/-- The group-valued functor of points of `rootsOfUnityGroupScheme`, restricted
to affine test schemes. -/
abbrev rootsOfUnityPointsFunctor (K : Type u) [CommRing K] (n : ℕ) :
    CommAlgCat K ⥤ GrpCat :=
  (algSpec (.of K)).rightOp ⋙
    yonedaGrp.obj (rootsOfUnityGroupScheme K n)

namespace RootsOfUnity

variable {R : Type v} [CommMonoid R]

/-- The additive homomorphism from `ZMod n` determined by a root of unity. -/
def rootAddHom {n : ℕ} (ζ : rootsOfUnity n R) : ZMod n →+ Additive Rˣ :=
  ZMod.lift n ⟨
    { toFun := fun z ↦ .ofMul ((ζ : Rˣ) ^ z)
      map_zero' := by simp
      map_add' := by intro x y; exact add_zsmul _ _ _ },
    by
      change Additive.ofMul ((ζ : Rˣ) ^ n) = Additive.ofMul 1
      exact congrArg Additive.ofMul ζ.prop⟩

/-- The monoid homomorphism from the cyclic character group determined by a
root of unity. -/
def rootMonoidHom {n : ℕ} (ζ : rootsOfUnity n R) :
    Multiplicative (ZMod n) →* R :=
  Units.coeHom R |>.comp <|
    (MulEquiv.multiplicativeAdditive Rˣ).toMonoidHom.comp
      (AddMonoidHom.toMultiplicative (rootAddHom ζ))

@[simp]
lemma rootMonoidHom_generator {n : ℕ} (ζ : rootsOfUnity n R) :
    rootMonoidHom ζ (.ofAdd 1) = ((ζ : Rˣ) : R) := by
  simp [rootMonoidHom]
  rw [show (1 : ZMod n) = Int.castAddHom (ZMod n) 1 by simp]
  rw [rootAddHom, ZMod.lift_castAddHom]
  simp

private lemma cyclicCharacter_ext {n : ℕ}
    {f g : Multiplicative (ZMod n) →* R}
    (h : f (.ofAdd 1) = g (.ofAdd 1)) : f = g := by
  apply MonoidHom.toAdditiveRight.injective
  -- Integer casts generate `ZMod n`, also when `n = 0`.
  have hcast : f.toAdditiveRight.comp (Int.castAddHom (ZMod n)) =
      g.toAdditiveRight.comp (Int.castAddHom (ZMod n)) := by
    apply AddMonoidHom.ext_int
    change Additive.ofMul (f (.ofAdd ((1 : ℤ) : ZMod n))) =
      Additive.ofMul (g (.ofAdd ((1 : ℤ) : ZMod n)))
    simpa only [Int.cast_one] using congrArg Additive.ofMul h
  apply AddMonoidHom.ext
  intro x
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  exact DFunLike.congr_fun hcast z

/-- Cyclic characters commute with restriction along a multiplicative map. -/
@[simp]
lemma rootMonoidHom_restrict {S : Type w} [CommMonoid S]
    {F : Type t} [FunLike F R S] [MonoidHomClass F R S]
    (σ : F) {n : ℕ} (ζ : rootsOfUnity n R) :
    rootMonoidHom (restrictRootsOfUnity σ n ζ) =
      (σ : R →* S).comp (rootMonoidHom ζ) := by
  apply cyclicCharacter_ext
  simp only [rootMonoidHom_generator, MonoidHom.comp_apply,
    restrictRootsOfUnity_coe_apply, MonoidHom.coe_coe]

/-- Recover a root of unity by evaluating a cyclic character at its standard
generator. -/
def monoidHomRoot {n : ℕ}
    (f : Multiplicative (ZMod n) →* R) : rootsOfUnity n R :=
  ⟨f.toHomUnits (.ofAdd 1), by
    have hg : (Multiplicative.ofAdd (1 : ZMod n)) ^ n = 1 := by
      change Multiplicative.ofAdd (n • (1 : ZMod n)) = Multiplicative.ofAdd 0
      congr 1
      simp
    change (f.toHomUnits (.ofAdd 1)) ^ n = 1
    rw [← (f.toHomUnits).map_pow, hg, map_one]⟩

/-- The inverse character construction uses the unit supplied by the source group. -/
@[simp]
lemma monoidHomRoot_coe {n : ℕ} (f : Multiplicative (ZMod n) →* R) :
    (monoidHomRoot f : Rˣ) = f.toHomUnits (.ofAdd 1) := by
  rfl

/-- The underlying value of the inverse character construction is generator evaluation. -/
@[simp]
lemma monoidHomRoot_val {n : ℕ} (f : Multiplicative (ZMod n) →* R) :
    ((monoidHomRoot f : Rˣ) : R) = f (.ofAdd 1) := by
  rw [monoidHomRoot_coe, MonoidHom.coe_toHomUnits]

/-- Recovering a root after taking its character is the identity. -/
@[simp]
lemma monoidHomRoot_rootMonoidHom {n : ℕ}
    (ζ : rootsOfUnity n R) : monoidHomRoot (rootMonoidHom ζ) = ζ := by
  apply rootsOfUnity.coe_injective
  change ((monoidHomRoot (rootMonoidHom ζ) : Rˣ) : R) = ((ζ : Rˣ) : R)
  rw [monoidHomRoot_val, rootMonoidHom_generator]

/-- Taking the character of its recovered root is the identity. -/
@[simp]
lemma rootMonoidHom_monoidHomRoot {n : ℕ}
    (f : Multiplicative (ZMod n) →* R) : rootMonoidHom (monoidHomRoot f) = f := by
  apply cyclicCharacter_ext
  rw [rootMonoidHom_generator, monoidHomRoot_val]

/-- Recovering roots commutes with postcomposition of characters. -/
lemma monoidHomRoot_restrict {S : Type w} [CommMonoid S]
    {F : Type t} [FunLike F R S] [MonoidHomClass F R S]
    (σ : F) {n : ℕ} (f : Multiplicative (ZMod n) →* R) :
    monoidHomRoot ((σ : R →* S).comp f) =
      restrictRootsOfUnity σ n (monoidHomRoot f) := by
  apply rootsOfUnity.coe_injective
  simp only [monoidHomRoot_val, MonoidHom.comp_apply,
    restrictRootsOfUnity_coe_apply, MonoidHom.coe_coe]

/-- Evaluation at the standard generator identifies roots of unity with
characters of `ZMod n`. -/
def equivMonoidHom (n : ℕ) :
    rootsOfUnity n R ≃ (Multiplicative (ZMod n) →* R) where
  toFun := rootMonoidHom
  invFun := monoidHomRoot
  left_inv := monoidHomRoot_rootMonoidHom
  right_inv := rootMonoidHom_monoidHomRoot

/-- The group equivalence between roots of unity and cyclic characters. -/
def mulEquivMonoidHom (n : ℕ) :
    rootsOfUnity n R ≃* (Multiplicative (ZMod n) →* R) where
  __ := equivMonoidHom n
  map_mul' ζ ξ := by
    apply cyclicCharacter_ext
    change rootMonoidHom (ζ * ξ) (.ofAdd 1) =
      (rootMonoidHom ζ * rootMonoidHom ξ) (.ofAdd 1)
    simp only [rootMonoidHom_generator, MonoidHom.mul_apply,
      Subgroup.coe_mul, Units.val_mul]

end RootsOfUnity

private lemma addMonoidAlgebra_liftMulEquiv_apply
    {R : Type u} {A : Type v} {M : Type w}
    [CommSemiring R] [CommSemiring A] [Algebra R A] [AddMonoid M]
    (f : Multiplicative M →* A) :
    (AddMonoidAlgebra.liftMulEquiv (R := R) (A := A) (M := M) f).ofConv =
      AddMonoidAlgebra.lift R A M f :=
  rfl

variable (K : Type u) [CommRing K]

section AlgebraMaps

variable (R : Type v) [CommSemiring R] [Algebra K R]

/-- Roots of unity are multiplicatively equivalent to algebra maps out of
their group-algebra coordinate ring, at every natural order. -/
def rootsOfUnityMulEquivAlgHom (n : ℕ) :
    rootsOfUnity n R ≃*
      WithConv (rootsOfUnityCoordinateRing K n →ₐ[K] R) :=
  (RootsOfUnity.mulEquivMonoidHom (R := R) n).trans
    (AddMonoidAlgebra.liftMulEquiv (R := K) (A := R) (M := ZMod n))

@[simp]
lemma rootsOfUnityMulEquivAlgHom_apply (n : ℕ) (ζ : rootsOfUnity n R) :
    (rootsOfUnityMulEquivAlgHom K R n ζ).ofConv =
      AddMonoidAlgebra.lift K R (ZMod n) (RootsOfUnity.rootMonoidHom ζ) := by
  exact addMonoidAlgebra_liftMulEquiv_apply (R := K) (RootsOfUnity.rootMonoidHom ζ)

/-- The inverse algebra-map equivalence recovers the character and evaluates its generator. -/
lemma rootsOfUnityMulEquivAlgHom_symm_apply (n : ℕ)
    (φ : WithConv (rootsOfUnityCoordinateRing K n →ₐ[K] R)) :
    (rootsOfUnityMulEquivAlgHom K R n).symm φ =
      RootsOfUnity.monoidHomRoot
        ((AddMonoidAlgebra.lift K R (ZMod n)).symm φ.ofConv) := by
  apply (rootsOfUnityMulEquivAlgHom K R n).injective
  apply (WithConv.equiv _).injective
  simp only [MulEquiv.apply_symm_apply, WithConv.equiv_apply,
    rootsOfUnityMulEquivAlgHom_apply, RootsOfUnity.rootMonoidHom_monoidHomRoot,
    Equiv.apply_symm_apply]

/-- The algebra-map equivalence is natural in the target algebra. -/
@[simp]
lemma rootsOfUnityMulEquivAlgHom_naturality
    {S : Type w} [CommSemiring S] [Algebra K S]
    (f : R →ₐ[K] S) (n : ℕ) (ζ : rootsOfUnity n R) :
    (rootsOfUnityMulEquivAlgHom K S n
      (restrictRootsOfUnity f n ζ)).ofConv =
      f.comp (rootsOfUnityMulEquivAlgHom K R n ζ).ofConv := by
  rw [rootsOfUnityMulEquivAlgHom_apply, rootsOfUnityMulEquivAlgHom_apply,
    RootsOfUnity.rootMonoidHom_restrict]
  apply (AddMonoidAlgebra.lift K S (ZMod n)).symm.injective
  ext a
  simp

end AlgebraMaps

section AffinePoints

variable (R : Type u) [CommRing R] [Algebra K R]

/-- The functor-of-points equivalence at a `K`-algebra `R`, at every natural order. -/
def rootsOfUnityMulEquivPoints (n : ℕ) :
    rootsOfUnity n R ≃*
      ((Spec (.of R)).asOver (Spec (.of K)) ⟶ rootsOfUnityScheme K n) :=
  (rootsOfUnityMulEquivAlgHom K R n).trans
    (Spec.mapMulEquiv
      (R := K) (S := rootsOfUnityCoordinateRing K n) (T := R))

@[simp]
lemma rootsOfUnityMulEquivPoints_map_mul (n : ℕ)
    (ζ ξ : rootsOfUnity n R) :
    rootsOfUnityMulEquivPoints K R n (ζ * ξ) =
      rootsOfUnityMulEquivPoints K R n ζ *
        rootsOfUnityMulEquivPoints K R n ξ :=
  (rootsOfUnityMulEquivPoints K R n).map_mul ζ ξ

@[simp]
lemma rootsOfUnityMulEquivPoints_apply_left (n : ℕ)
    (ζ : rootsOfUnity n R) :
    (rootsOfUnityMulEquivPoints K R n ζ).left =
      Spec.map (CommRingCat.ofHom
        (rootsOfUnityMulEquivAlgHom K R n ζ).ofConv.toRingHom) :=
  rfl

/-- Restricting a root along an algebra map precomposes the corresponding affine point. -/
lemma rootsOfUnityMulEquivPoints_naturality
    {S : Type u} [CommRing S] [Algebra K S]
    (f : R →ₐ[K] S) (n : ℕ) (ζ : rootsOfUnity n R) :
    rootsOfUnityMulEquivPoints K S n (restrictRootsOfUnity f n ζ) =
      (algSpec (.of K)).map (CommAlgCat.ofHom f).op ≫
        rootsOfUnityMulEquivPoints K R n ζ := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, rootsOfUnityMulEquivPoints_apply_left,
    rootsOfUnityMulEquivAlgHom_naturality, algSpec_map_left]
  exact Spec.map_comp
    (CommRingCat.ofHom (rootsOfUnityMulEquivAlgHom K R n ζ).ofConv.toRingHom)
    (CommRingCat.ofHom f.toRingHom)

end AffinePoints

/-- The affine group scheme `rootsOfUnityGroupScheme K n` represents roots of
unity over an arbitrary commutative base for every natural `n`. For positive
`n` this extends Milne's *Algebraic Groups*, item 2.4; at zero it represents units. -/
def rootsOfUnityPointsIso (n : ℕ) :
    rootsOfUnityFunctor K n ≅ rootsOfUnityPointsFunctor K n :=
  NatIso.ofComponents
    (fun R ↦ (rootsOfUnityMulEquivPoints K R n).toGrpIso)
    (fun {R S} f ↦ by
      apply GrpCat.ext
      intro ζ
      exact rootsOfUnityMulEquivPoints_naturality K R f.hom n ζ)

/-- The forward component of the representing isomorphism is the point equivalence. -/
@[simp]
lemma rootsOfUnityPointsIso_hom_app_apply
    (R : Type u) [CommRing R] [Algebra K R] (n : ℕ) (ζ : rootsOfUnity n R) :
    (rootsOfUnityPointsIso K n).hom.app (CommAlgCat.of K R) ζ =
      rootsOfUnityMulEquivPoints K R n ζ := by
  rfl

/-- The inverse component of the representing isomorphism recovers the root from its point. -/
@[simp]
lemma rootsOfUnityPointsIso_inv_app_apply
    (R : Type u) [CommRing R] [Algebra K R] (n : ℕ)
    (p : (Spec (.of R)).asOver (Spec (.of K)) ⟶ rootsOfUnityScheme K n) :
    (rootsOfUnityPointsIso K n).inv.app (CommAlgCat.of K R) p =
      (rootsOfUnityMulEquivPoints K R n).symm p := by
  rfl

/-- The polynomial defining the usual coordinate presentation of the
roots-of-unity scheme. -/
abbrev rootsOfUnityPolynomial (K : Type u) [CommRing K] (n : ℕ) : K[X] :=
  X ^ n - 1

/-- The standard generator of the group-algebra coordinate ring. -/
def rootsOfUnityCoordinateGenerator (n : ℕ) :
    rootsOfUnityCoordinateRing K n :=
  AddMonoidAlgebra.single 1 1

@[simp]
lemma rootsOfUnityCoordinateGenerator_pow (n : ℕ) :
    rootsOfUnityCoordinateGenerator K n ^ n = 1 := by
  simp [rootsOfUnityCoordinateGenerator, AddMonoidAlgebra.one_def]

/-- The algebra map associated to a root evaluates the coordinate generator at that root. -/
@[simp]
lemma rootsOfUnityMulEquivAlgHom_generator
    (R : Type v) [CommSemiring R] [Algebra K R] (n : ℕ) (ζ : rootsOfUnity n R) :
    (rootsOfUnityMulEquivAlgHom K R n ζ).ofConv
      (rootsOfUnityCoordinateGenerator K n) = ((ζ : Rˣ) : R) := by
  rw [rootsOfUnityMulEquivAlgHom_apply]
  simpa only [rootsOfUnityCoordinateGenerator, AddMonoidAlgebra.lift_single, one_smul]
    using RootsOfUnity.rootMonoidHom_generator ζ

/-- At order zero the cyclic coordinate Hopf algebra is the Laurent coordinate
Hopf algebra of the multiplicative group, by the identity on integer monomials. -/
def rootsOfUnityCoordinateZeroBialgEquivMultiplicativeGroup :
    rootsOfUnityCoordinateRing K 0 ≃ₐc[K] multiplicativeGroupCoordinateRing K :=
  BialgEquiv.refl (R := K) (A := AddMonoidAlgebra K ℤ)

/-- The zero-order coordinate comparison sends each integer monomial to itself. -/
@[simp]
lemma rootsOfUnityCoordinateZeroBialgEquivMultiplicativeGroup_apply
    (x : rootsOfUnityCoordinateRing K 0) :
    rootsOfUnityCoordinateZeroBialgEquivMultiplicativeGroup K x = x := by
  rfl

/-- The inverse zero-order coordinate comparison is the identity on integer monomials. -/
@[simp]
lemma rootsOfUnityCoordinateZeroBialgEquivMultiplicativeGroup_symm_apply
    (x : multiplicativeGroupCoordinateRing K) :
    (rootsOfUnityCoordinateZeroBialgEquivMultiplicativeGroup K).symm x = x := by
  rfl

/-- The zero-order coordinate generator corresponds to the multiplicative-group coordinate. -/
@[simp]
lemma rootsOfUnityCoordinateZeroBialgEquivMultiplicativeGroup_generator :
    rootsOfUnityCoordinateZeroBialgEquivMultiplicativeGroup K
      (rootsOfUnityCoordinateGenerator K 0) = multiplicativeGroupCoordinate K := by
  rw [rootsOfUnityCoordinateZeroBialgEquivMultiplicativeGroup_apply]
  rfl

/-- The multiplicative-group coordinate pulls back to the zero-order coordinate generator. -/
@[simp]
lemma rootsOfUnityCoordinateZeroBialgEquivMultiplicativeGroup_symm_coordinate :
    (rootsOfUnityCoordinateZeroBialgEquivMultiplicativeGroup K).symm
      (multiplicativeGroupCoordinate K) = rootsOfUnityCoordinateGenerator K 0 := by
  rw [rootsOfUnityCoordinateZeroBialgEquivMultiplicativeGroup_symm_apply]
  rfl

/-- The order-zero roots-of-unity group scheme is canonically the existing
multiplicative group. The map is induced contravariantly by the identity
bialgebra equivalence, not by the inversion automorphism. -/
def rootsOfUnityGroupSchemeZeroIsoMultiplicativeGroup :
    rootsOfUnityGroupScheme K 0 ≅ multiplicativeGroupScheme K :=
  (hopfSpec (.of K)).mapIso
    (CommHopfAlgCat.isoMk
      (rootsOfUnityCoordinateZeroBialgEquivMultiplicativeGroup K)).symm.op

/-- The forward group-scheme comparison is induced by the inverse coordinate comparison. -/
lemma rootsOfUnityGroupSchemeZeroIsoMultiplicativeGroup_hom_left :
    (rootsOfUnityGroupSchemeZeroIsoMultiplicativeGroup K).hom.hom.hom.left =
      Spec.map (CommRingCat.ofHom
        ((rootsOfUnityCoordinateZeroBialgEquivMultiplicativeGroup K).symm :
          multiplicativeGroupCoordinateRing K →ₐ[K] rootsOfUnityCoordinateRing K 0).toRingHom) := by
  rfl

/-- The inverse group-scheme comparison is induced by the forward coordinate comparison. -/
lemma rootsOfUnityGroupSchemeZeroIsoMultiplicativeGroup_inv_left :
    (rootsOfUnityGroupSchemeZeroIsoMultiplicativeGroup K).inv.hom.hom.left =
      Spec.map (CommRingCat.ofHom
        (rootsOfUnityCoordinateZeroBialgEquivMultiplicativeGroup K :
          rootsOfUnityCoordinateRing K 0 →ₐ[K] multiplicativeGroupCoordinateRing K).toRingHom) := by
  rfl

/-- The zero-order comparison carries a root's point to the multiplicative-group point
of its underlying unit. -/
lemma rootsOfUnityGroupSchemeZeroIsoMultiplicativeGroup_point
    (R : Type u) [CommRing R] [Algebra K R] (ζ : rootsOfUnity 0 R) :
    rootsOfUnityMulEquivPoints K R 0 ζ ≫
        (rootsOfUnityGroupSchemeZeroIsoMultiplicativeGroup K).hom.hom.hom =
      multiplicativeGroupMulEquivPoints K R (ζ : Rˣ) := by
  have hφ :
      (rootsOfUnityMulEquivAlgHom K R 0 ζ).ofConv.comp
          ((rootsOfUnityCoordinateZeroBialgEquivMultiplicativeGroup K).symm :
            multiplicativeGroupCoordinateRing K →ₐ[K] rootsOfUnityCoordinateRing K 0) =
        (multiplicativeGroupMulEquivAlgHom K R (ζ : Rˣ)).ofConv := by
    -- A character of the integers, hence its lifted algebra map, is determined by `T`.
    apply AddMonoidAlgebra.algHom_ext'
    · apply MonoidHom.ext_mint
      change (rootsOfUnityMulEquivAlgHom K R 0 ζ).ofConv
          ((rootsOfUnityCoordinateZeroBialgEquivMultiplicativeGroup K).symm
            (multiplicativeGroupCoordinate K)) =
        (multiplicativeGroupMulEquivAlgHom K R (ζ : Rˣ)).ofConv
          (multiplicativeGroupCoordinate K)
      rw [rootsOfUnityCoordinateZeroBialgEquivMultiplicativeGroup_symm_coordinate,
        rootsOfUnityMulEquivAlgHom_generator, multiplicativeGroupMulEquivAlgHom_coordinate]
    · ext
  apply Over.OverMorphism.ext
  -- Normalize the scheme endpoints before applying contravariant functoriality.
  change
    Spec.map (CommRingCat.ofHom
      (rootsOfUnityMulEquivAlgHom K R 0 ζ).ofConv.toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          ((rootsOfUnityCoordinateZeroBialgEquivMultiplicativeGroup K).symm :
            multiplicativeGroupCoordinateRing K →ₐ[K] rootsOfUnityCoordinateRing K 0).toRingHom) =
      Spec.map (CommRingCat.ofHom
        (multiplicativeGroupMulEquivAlgHom K R (ζ : Rˣ)).ofConv.toRingHom)
  exact (Spec.map_comp
    (CommRingCat.ofHom
      ((rootsOfUnityCoordinateZeroBialgEquivMultiplicativeGroup K).symm :
        multiplicativeGroupCoordinateRing K →ₐ[K] rootsOfUnityCoordinateRing K 0).toRingHom)
    (CommRingCat.ofHom (rootsOfUnityMulEquivAlgHom K R 0 ζ).ofConv.toRingHom)).symm.trans
      (congrArg (fun φ : multiplicativeGroupCoordinateRing K →ₐ[K] R ↦
        Spec.map (CommRingCat.ofHom φ.toRingHom)) hφ)

/-- The distinguished root in `AdjoinRoot (X ^ n - 1)` as an `n`-th root of
unity. -/
def adjoinRootRootsOfUnity (n : ℕ) [NeZero n] :
    rootsOfUnity n (AdjoinRoot (rootsOfUnityPolynomial K n)) :=
  rootsOfUnity.mkOfPowEq (AdjoinRoot.root (rootsOfUnityPolynomial K n)) (by
    have h : AdjoinRoot.root (rootsOfUnityPolynomial K n) ^ n - 1 = 0 := by
      simpa [rootsOfUnityPolynomial] using
        AdjoinRoot.eval₂_root (rootsOfUnityPolynomial K n)
    exact sub_eq_zero.mp h)

/-- The coordinate-ring map sending the cyclic group generator to the
distinguished root of `X ^ n - 1`. -/
def rootsOfUnityCoordinateToAdjoinRoot (n : ℕ) [NeZero n] :
    rootsOfUnityCoordinateRing K n →ₐ[K]
      AdjoinRoot (rootsOfUnityPolynomial K n) :=
  AddMonoidAlgebra.lift K _ (ZMod n)
    (RootsOfUnity.rootMonoidHom (adjoinRootRootsOfUnity K n))

@[simp]
lemma rootsOfUnityCoordinateToAdjoinRoot_generator (n : ℕ) [NeZero n] :
    rootsOfUnityCoordinateToAdjoinRoot K n
      (rootsOfUnityCoordinateGenerator K n) =
        AdjoinRoot.root (rootsOfUnityPolynomial K n) := by
  simp [rootsOfUnityCoordinateToAdjoinRoot,
    rootsOfUnityCoordinateGenerator, adjoinRootRootsOfUnity]

/-- The coordinate-ring map sending the distinguished root of `X ^ n - 1` to
the cyclic group-algebra generator. -/
def adjoinRootToRootsOfUnityCoordinate (n : ℕ) :
    AdjoinRoot (rootsOfUnityPolynomial K n) →ₐ[K]
      rootsOfUnityCoordinateRing K n :=
  AdjoinRoot.liftAlgHom (rootsOfUnityPolynomial K n)
    (Algebra.ofId K _) (rootsOfUnityCoordinateGenerator K n) (by
      simp [rootsOfUnityPolynomial])

@[simp]
lemma adjoinRootToRootsOfUnityCoordinate_root (n : ℕ) :
    adjoinRootToRootsOfUnityCoordinate K n
      (AdjoinRoot.root (rootsOfUnityPolynomial K n)) =
        rootsOfUnityCoordinateGenerator K n := by
  simp [adjoinRootToRootsOfUnityCoordinate]

lemma rootsOfUnityCoordinateToAdjoinRoot_comp_adjoinRootTo (n : ℕ)
    [NeZero n] :
    (rootsOfUnityCoordinateToAdjoinRoot K n).comp
      (adjoinRootToRootsOfUnityCoordinate K n) =
        AlgHom.id K (AdjoinRoot (rootsOfUnityPolynomial K n)) := by
  ext
  simp

lemma adjoinRootToRootsOfUnityCoordinate_comp_coordinateTo (n : ℕ)
    [NeZero n] :
    (adjoinRootToRootsOfUnityCoordinate K n).comp
      (rootsOfUnityCoordinateToAdjoinRoot K n) =
        AlgHom.id K (rootsOfUnityCoordinateRing K n) := by
  apply AddMonoidAlgebra.algHom_ext
  · intro x
    rw [← ZMod.natCast_zmod_val x]
    change ((adjoinRootToRootsOfUnityCoordinate K n).comp
        (rootsOfUnityCoordinateToAdjoinRoot K n))
          (AddMonoidAlgebra.single (x.val : ZMod n) 1) =
      (AlgHom.id K (rootsOfUnityCoordinateRing K n))
        (AddMonoidAlgebra.single (x.val : ZMod n) 1)
    rw [show AddMonoidAlgebra.single (x.val : ZMod n) (1 : K) =
        rootsOfUnityCoordinateGenerator K n ^ x.val by
      simp [rootsOfUnityCoordinateGenerator]]
    simp
  · ext

/-- The coordinate presentation `K[ZMod n] ≃ₐ[K] K[T]/(T ^ n - 1)` from
Milne's *Algebraic Groups*, item 2.4, extended from fields to commutative
bases for positive `n`. -/
def rootsOfUnityCoordinateAlgEquiv (n : ℕ) [NeZero n] :
    rootsOfUnityCoordinateRing K n ≃ₐ[K]
      AdjoinRoot (rootsOfUnityPolynomial K n) :=
  AlgEquiv.ofAlgHom
    (rootsOfUnityCoordinateToAdjoinRoot K n)
    (adjoinRootToRootsOfUnityCoordinate K n)
    (rootsOfUnityCoordinateToAdjoinRoot_comp_adjoinRootTo K n)
    (adjoinRootToRootsOfUnityCoordinate_comp_coordinateTo K n)

@[simp]
lemma rootsOfUnityCoordinateAlgEquiv_generator (n : ℕ) [NeZero n] :
    rootsOfUnityCoordinateAlgEquiv K n
      (rootsOfUnityCoordinateGenerator K n) =
        AdjoinRoot.root (rootsOfUnityPolynomial K n) := by
  simp [rootsOfUnityCoordinateAlgEquiv]

@[simp]
lemma rootsOfUnityCoordinateAlgEquiv_symm_root (n : ℕ) [NeZero n] :
    (rootsOfUnityCoordinateAlgEquiv K n).symm
      (AdjoinRoot.root (rootsOfUnityPolynomial K n)) =
        rootsOfUnityCoordinateGenerator K n := by
  simp [rootsOfUnityCoordinateAlgEquiv]

/-- The distinguished root of `K[T]/(T ^ n - 1)` is group-like for the
group-algebra Hopf structure, transported back along the coordinate
equivalence. -/
lemma rootsOfUnityCoordinateAlgEquiv_symm_root_isGroupLike
    (n : ℕ) [NeZero n] :
    IsGroupLikeElem K
      ((rootsOfUnityCoordinateAlgEquiv K n).symm
        (AdjoinRoot.root (rootsOfUnityPolynomial K n))) := by
  rw [rootsOfUnityCoordinateAlgEquiv_symm_root]
  exact AddMonoidAlgebra.isGroupLikeElem_single_one 1

/-- Under the coordinate equivalence, comultiplication sends the distinguished
root to its tensor square, as in Milne's *Algebraic Groups*, item 2.4. This
is the multiplicative-group comultiplication on the quotient generator. -/
lemma rootsOfUnityCoordinateAlgEquiv_comul_root (n : ℕ) [NeZero n] :
    Algebra.TensorProduct.map
        (rootsOfUnityCoordinateAlgEquiv K n).toAlgHom
        (rootsOfUnityCoordinateAlgEquiv K n).toAlgHom
        (Coalgebra.comul
          ((rootsOfUnityCoordinateAlgEquiv K n).symm
            (AdjoinRoot.root (rootsOfUnityPolynomial K n)))) =
      AdjoinRoot.root (rootsOfUnityPolynomial K n) ⊗ₜ[K]
        AdjoinRoot.root (rootsOfUnityPolynomial K n) := by
  rw [(rootsOfUnityCoordinateAlgEquiv_symm_root_isGroupLike K n).comul_eq_tmul_self]
  rw [Algebra.TensorProduct.map_tmul]
  simp

/-- Under the coordinate equivalence, the counit sends the distinguished root
to one. -/
lemma rootsOfUnityCoordinateAlgEquiv_counit_root (n : ℕ) [NeZero n] :
    Coalgebra.counit (R := K)
        ((rootsOfUnityCoordinateAlgEquiv K n).symm
          (AdjoinRoot.root (rootsOfUnityPolynomial K n))) = 1 :=
  (rootsOfUnityCoordinateAlgEquiv_symm_root_isGroupLike K n).counit_eq_one

/-- Under the coordinate equivalence, the antipode sends the distinguished
root to its standard inverse representative `T ^ (n - 1)`. -/
lemma rootsOfUnityCoordinateAlgEquiv_antipode_root (n : ℕ) [NeZero n] :
    rootsOfUnityCoordinateAlgEquiv K n
        (HopfAlgebra.antipode K
          ((rootsOfUnityCoordinateAlgEquiv K n).symm
            (AdjoinRoot.root (rootsOfUnityPolynomial K n)))) =
      AdjoinRoot.root (rootsOfUnityPolynomial K n) ^ (n - 1) := by
  rw [rootsOfUnityCoordinateAlgEquiv_symm_root]
  change rootsOfUnityCoordinateAlgEquiv K n
      (HopfAlgebra.antipode K
        (AddMonoidAlgebra.single (1 : ZMod n) 1)) = _
  rw [AddMonoidAlgebra.antipode_single]
  simp only [HopfAlgebra.antipode_one]
  rw [show AddMonoidAlgebra.single (-(1 : ZMod n)) (1 : K) =
      rootsOfUnityCoordinateGenerator K n ^ (n - 1) by
    rw [show rootsOfUnityCoordinateGenerator K n ^ (n - 1) =
        AddMonoidAlgebra.single ((n - 1 : ℕ) : ZMod n) (1 : K) by
      simp [rootsOfUnityCoordinateGenerator]]
    congr 1
    have hn : 1 ≤ n := (Nat.one_le_iff_ne_zero).2 (NeZero.ne n)
    rw [Nat.cast_sub hn]
    simp]
  simp

end AlgebraicGeometry
