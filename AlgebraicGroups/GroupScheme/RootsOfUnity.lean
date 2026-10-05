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

/-!
# Finite roots-of-unity group schemes

This file packages the affine group scheme represented by the Hopf algebra
`K[ZMod n]` and identifies its points with the `n`-th roots of unity.
For positive `n`, Milne's *Algebraic Groups*, item 2.4, gives the roots-of-unity
functor, the quotient `k[T]/(T ^ n - 1)` and the multiplication-induced
comultiplication `T ↦ T ⊗ T` over a field. The construction here uses the
cyclic group algebra over any commutative base. The coordinate ring and group
scheme are also defined at `n = 0`, but the points isomorphism and polynomial
quotient equivalence below require `[NeZero n]` (equivalently, positive `n`).

## Main definitions

- `AlgebraicGeometry.rootsOfUnityGroupScheme`
- `AlgebraicGeometry.rootsOfUnityMulEquivPoints`
- `AlgebraicGeometry.rootsOfUnityPointsIso`
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

universe u

namespace AlgebraicGeometry

/-- The coordinate ring used for the finite roots-of-unity group scheme. -/
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

variable {R : Type u} [CommRing R]

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

@[simp]
lemma rootMonoidHom_restrict {S : Type u} [CommRing S]
    (σ : R →+* S) {n : ℕ} (ζ : rootsOfUnity n R) :
    rootMonoidHom (restrictRootsOfUnity σ n ζ) =
      σ.toMonoidHom.comp (rootMonoidHom ζ) := by
  apply MonoidHom.ext
  intro x
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  have heq : Multiplicative.ofAdd (z : ZMod n) =
      (Multiplicative.ofAdd (1 : ZMod n)) ^ z := by
    change Multiplicative.ofAdd (z : ZMod n) =
      Multiplicative.ofAdd (z • (1 : ZMod n))
    congr 1
    simp
  change rootMonoidHom (restrictRootsOfUnity σ n ζ)
      (Multiplicative.ofAdd (z : ZMod n)) =
    (σ.toMonoidHom.comp (rootMonoidHom ζ))
      (Multiplicative.ofAdd (z : ZMod n))
  rw [← MonoidHom.coe_toHomUnits
      (rootMonoidHom (restrictRootsOfUnity σ n ζ)),
    ← MonoidHom.coe_toHomUnits (σ.toMonoidHom.comp (rootMonoidHom ζ))]
  rw [heq, map_zpow, map_zpow]
  have hbase :
      (rootMonoidHom (restrictRootsOfUnity σ n ζ)).toHomUnits
          (Multiplicative.ofAdd (1 : ZMod n)) =
        (σ.toMonoidHom.comp (rootMonoidHom ζ)).toHomUnits
          (Multiplicative.ofAdd (1 : ZMod n)) := by
    apply Units.ext
    simp
  rw [hbase]

/-- Recover a root of unity by evaluating a cyclic character at its standard
generator. -/
def monoidHomRoot {n : ℕ} [NeZero n]
    (f : Multiplicative (ZMod n) →* R) : rootsOfUnity n R :=
  rootsOfUnity.mkOfPowEq (f (.ofAdd 1)) (by
    have hg : (Multiplicative.ofAdd (1 : ZMod n)) ^ n = 1 := by
      change Multiplicative.ofAdd (n • (1 : ZMod n)) = Multiplicative.ofAdd 0
      congr 1
      simp
    rw [← f.map_pow, hg, map_one])

@[simp]
lemma monoidHomRoot_rootMonoidHom {n : ℕ} [NeZero n]
    (ζ : rootsOfUnity n R) : monoidHomRoot (rootMonoidHom ζ) = ζ := by
  apply rootsOfUnity.coe_injective
  simp [monoidHomRoot]

@[simp]
lemma rootMonoidHom_monoidHomRoot {n : ℕ} [NeZero n]
    (f : Multiplicative (ZMod n) →* R) : rootMonoidHom (monoidHomRoot f) = f := by
  apply MonoidHom.ext
  intro x
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  have heq : Multiplicative.ofAdd (z : ZMod n) =
      (Multiplicative.ofAdd (1 : ZMod n)) ^ z := by
    change Multiplicative.ofAdd (z : ZMod n) =
      Multiplicative.ofAdd (z • (1 : ZMod n))
    congr 1
    simp
  change rootMonoidHom (monoidHomRoot f) (Multiplicative.ofAdd (z : ZMod n)) =
    f (Multiplicative.ofAdd (z : ZMod n))
  rw [← MonoidHom.coe_toHomUnits (rootMonoidHom (monoidHomRoot f)),
    ← MonoidHom.coe_toHomUnits f]
  rw [heq, map_zpow, map_zpow]
  have hbase : (rootMonoidHom (monoidHomRoot f)).toHomUnits
      (Multiplicative.ofAdd (1 : ZMod n)) =
      f.toHomUnits (Multiplicative.ofAdd (1 : ZMod n)) := by
    apply Units.ext
    simp [monoidHomRoot]
  rw [hbase]

/-- Evaluation at the standard generator identifies roots of unity with
characters of `ZMod n`. -/
def equivMonoidHom (n : ℕ) [NeZero n] :
    rootsOfUnity n R ≃ (Multiplicative (ZMod n) →* R) where
  toFun := rootMonoidHom
  invFun := monoidHomRoot
  left_inv := monoidHomRoot_rootMonoidHom
  right_inv := rootMonoidHom_monoidHomRoot

/-- The group equivalence between roots of unity and cyclic characters. -/
def mulEquivMonoidHom (n : ℕ) [NeZero n] :
    rootsOfUnity n R ≃* (Multiplicative (ZMod n) →* R) where
  __ := equivMonoidHom n
  map_mul' ζ ξ := by
    apply (equivMonoidHom (R := R) n).symm.injective
    apply rootsOfUnity.coe_injective
    simp [equivMonoidHom, monoidHomRoot]

end RootsOfUnity

variable (K : Type u) [CommRing K]
variable (R : Type u) [CommRing R] [Algebra K R]

/-- Roots of unity are multiplicatively equivalent to algebra maps out of
their group-algebra coordinate ring. -/
def rootsOfUnityMulEquivAlgHom (n : ℕ) [NeZero n] :
    rootsOfUnity n R ≃*
      WithConv (rootsOfUnityCoordinateRing K n →ₐ[K] R) where
  toEquiv := (RootsOfUnity.mulEquivMonoidHom (R := R) n).toEquiv.trans <|
    (AddMonoidAlgebra.lift K R (ZMod n)).trans (WithConv.equiv _).symm
  map_mul' ζ ξ := by
    apply WithConv.ofConv_injective
    ext
    simp [AlgHom.convMul_apply]

@[simp]
lemma rootsOfUnityMulEquivAlgHom_apply (n : ℕ) [NeZero n]
    (ζ : rootsOfUnity n R) :
    (rootsOfUnityMulEquivAlgHom K R n ζ).ofConv =
      AddMonoidAlgebra.lift K R (ZMod n) (RootsOfUnity.rootMonoidHom ζ) :=
  rfl

@[simp]
lemma rootsOfUnityMulEquivAlgHom_naturality
    {S : Type u} [CommRing S] [Algebra K S]
    (f : R →ₐ[K] S) (n : ℕ) [NeZero n] (ζ : rootsOfUnity n R) :
    (rootsOfUnityMulEquivAlgHom K S n
      (restrictRootsOfUnity f n ζ)).ofConv =
      f.comp (rootsOfUnityMulEquivAlgHom K R n ζ).ofConv := by
  apply AddMonoidAlgebra.algHom_ext
  · intro x
    rw [rootsOfUnityMulEquivAlgHom_apply,
      rootsOfUnityMulEquivAlgHom_apply]
    simp only [AddMonoidAlgebra.lift_single, one_smul, AlgHom.comp_apply]
    change RootsOfUnity.rootMonoidHom
        (restrictRootsOfUnity f.toRingHom n ζ) (.ofAdd x) =
      f.toRingHom (RootsOfUnity.rootMonoidHom ζ (.ofAdd x))
    rw [RootsOfUnity.rootMonoidHom_restrict]
    rfl
  · ext

/-- The functor-of-points equivalence at a `K`-algebra `R`. -/
def rootsOfUnityMulEquivPoints (n : ℕ) [NeZero n] :
    rootsOfUnity n R ≃*
      ((Spec (.of R)).asOver (Spec (.of K)) ⟶ rootsOfUnityScheme K n) :=
  (rootsOfUnityMulEquivAlgHom K R n).trans
    (Spec.mapMulEquiv
      (R := K) (S := rootsOfUnityCoordinateRing K n) (T := R))

@[simp]
lemma rootsOfUnityMulEquivPoints_map_mul (n : ℕ) [NeZero n]
    (ζ ξ : rootsOfUnity n R) :
    rootsOfUnityMulEquivPoints K R n (ζ * ξ) =
      rootsOfUnityMulEquivPoints K R n ζ *
        rootsOfUnityMulEquivPoints K R n ξ :=
  (rootsOfUnityMulEquivPoints K R n).map_mul ζ ξ

@[simp]
lemma rootsOfUnityMulEquivPoints_apply_left (n : ℕ) [NeZero n]
    (ζ : rootsOfUnity n R) :
    (rootsOfUnityMulEquivPoints K R n ζ).left =
      Spec.map (CommRingCat.ofHom
        (rootsOfUnityMulEquivAlgHom K R n ζ).ofConv.toRingHom) :=
  rfl

/-- The affine group scheme `rootsOfUnityGroupScheme K n` represents the
group-valued roots-of-unity functor of Milne's *Algebraic Groups*, item 2.4,
over an arbitrary commutative base for positive `n`. -/
def rootsOfUnityPointsIso (n : ℕ) [NeZero n] :
    rootsOfUnityFunctor K n ≅ rootsOfUnityPointsFunctor K n :=
  NatIso.ofComponents
    (fun R ↦ (rootsOfUnityMulEquivPoints K R n).toGrpIso)
    (fun {R S} f ↦ by
      ext ζ
      apply Over.OverMorphism.ext
      change
        (rootsOfUnityMulEquivPoints K S n
          (restrictRootsOfUnity f.hom n ζ)).left =
        ((algSpec (.of K)).map f.op).left ≫
          (rootsOfUnityMulEquivPoints K R n ζ).left
      rw [rootsOfUnityMulEquivPoints_apply_left]
      change
        Spec.map (CommRingCat.ofHom
          (rootsOfUnityMulEquivAlgHom K S n
            (restrictRootsOfUnity f.hom n ζ)).ofConv.toRingHom) =
        Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫
          Spec.map (CommRingCat.ofHom
            (rootsOfUnityMulEquivAlgHom K R n ζ).ofConv.toRingHom)
      rw [← Spec.map_comp]
      congr 1
      exact congrArg (fun h : rootsOfUnityCoordinateRing K n →ₐ[K] S ↦
          CommRingCat.ofHom h.toRingHom)
        (rootsOfUnityMulEquivAlgHom_naturality K R f.hom n ζ))

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
