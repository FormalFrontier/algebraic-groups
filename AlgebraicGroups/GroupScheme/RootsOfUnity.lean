/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import TauCeti.Algebra.AlgebraicGroup.RootsOfUnity.Scheme
public import TauCeti.Algebra.AlgebraicGroup.RootsOfUnity.AdjoinRoot
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import AlgebraicGroups.GroupScheme.Multiplicative


import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Roots-of-unity group schemes at all orders

The group scheme and inclusion are Tau Ceti's
`TauCeti.RootsOfUnityGroup.groupScheme` and `inclusionGroupSchemeMap`.
Their coordinate Hopf algebra is the group algebra of
`ULift (Multiplicative (ZMod n))`; scheme-valued points over affine test schemes
are identified with roots of unity by `schemePointsMulEquiv`.
This file supplies the representing natural isomorphism, the scheme-theoretic
power-kernel property for arbitrary test schemes, and finite, flat and rank geometry.

For positive n, Milne's Algebraic Groups, item 2.4 gives the roots-of-unity functor,
the quotient k[T]/(T ^ n - 1) and multiplication-induced comultiplication
T ↦ T ⊗ T over a field. Tau Ceti's `adjoinRootEquiv` supplies the polynomial
presentation over every commutative base. The comultiplication, counit and
antipode formulas below use that existing equivalence directly.
At order zero every unit is a root, ZMod 0 is ℤ, and the character group agrees
with that of the canonical multiplicative group; the polynomial presentation
and its T ^ (n - 1) inverse formula require positive order.

The coordinate algebra has Mathlib's `MonoidAlgebra.basis` at every order.
At positive order its basis has n indices and the structure morphism is finite,
flat and locally of finite presentation, with rank n at every base point.
Algebra finite presentation, flatness and local finite presentation also hold
at zero. No field, Noetherian or invertibility-of-n hypothesis is required.
The rank statement is pointwise on Spec K; the zero ring has empty spectrum.

## References

- James S. Milne, Algebraic Groups (2017), item 2.4, p. 40: positive-order
  roots of unity, the quotient coordinate and multiplicative comultiplication.
- Tau Ceti's RootsOfUnity.Scheme and RootsOfUnity.AdjoinRoot: the canonical
  diagonalizable group, inclusion, points and polynomial presentation.
- Mathlib's RingTheory.RootsOfUnity.Basic, RingTheory.Bialgebra.MonoidAlgebra,
  RingTheory.HopfAlgebra.MonoidAlgebra and RingTheory.AdjoinRoot: roots,
  group-algebra Hopf structure and polynomial quotient infrastructure.
- Mathlib's AlgebraicGeometry.Group.Affine and Tau Ceti's
  CommHopfAlgCat.SchemePoints: affine Hopf spectrum and arbitrary-source
  relative global-sections points.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory Polynomial
open scoped CategoryTheory.MonObj

universe u v w t

namespace AlgebraicGeometry

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

variable (K : Type u) [CommRing K]

/-- The affine group scheme represents roots of unity over every commutative base,
including order zero. -/
def rootsOfUnityPointsIso (n : ℕ) :
    rootsOfUnityFunctor K n ≅ TauCeti.GroupScheme.algebraPointsFunctor K
      (TauCeti.RootsOfUnityGroup.groupScheme K n) :=
  NatIso.ofComponents
    (fun R ↦ (TauCeti.RootsOfUnityGroup.schemePointsMulEquiv
      (R := K) (A := R) n).symm.toGrpIso)
    (fun {R S} f ↦ by
      ext ζ
      change rootsOfUnity n R at ζ
      change (TauCeti.RootsOfUnityGroup.schemePointsMulEquiv
        (R := K) (A := S) n).symm (restrictRootsOfUnity f.hom n ζ) =
          (Spec.map (CommRingCat.ofHom f.hom.toRingHom)).asOver (Spec (.of K)) ≫
            (TauCeti.RootsOfUnityGroup.schemePointsMulEquiv
              (R := K) (A := R) n).symm ζ
      apply (TauCeti.RootsOfUnityGroup.schemePointsMulEquiv (R := K) (A := S) n).injective
      rw [MulEquiv.apply_symm_apply,
        TauCeti.RootsOfUnityGroup.schemePointsMulEquiv_mapValue, MulEquiv.apply_symm_apply]
      rfl)

/-- Maps from an arbitrary base scheme to the cyclic diagonalizable group
are roots of unity among its global units. -/
private def rootsOfUnityHomOver (n : ℕ) (T : Over (Spec (.of K))) :
    (T ⟶ (TauCeti.RootsOfUnityGroup.groupScheme K n).X) ≃*
      rootsOfUnity n ((algΓ (.of K)).obj T).unop := by
  change (T ⟶ (Spec (.of (MonoidAlgebra K
    (ULift.{u} (Multiplicative (ZMod n)))))).asOver (Spec (.of K))) ≃* _
  exact (TauCeti.CommHopfAlgCat.schemePointsAlgΓMulEquiv (R := K)
    (MonoidAlgebra K (ULift.{u} (Multiplicative (ZMod n)))) T).trans
      (((TauCeti.DiagonalizableGroup.pointsMulEquiv (R := K)
        (A := ((algΓ (.of K)).obj T).unop)
        (G := ULift.{u} (Multiplicative (ZMod n)))).trans
        (MulEquiv.ulift : ULift.{u} (Multiplicative (ZMod n)) ≃*
          Multiplicative (ZMod n)).monoidHomCongrLeft).trans
        (TauCeti.RootsOfUnityGroup.characterMulEquivRootsOfUnity n))

private lemma rootsOfUnityHomOver_inclusion (n : ℕ) (T : Over (Spec (.of K)))
    (f : T ⟶ (TauCeti.RootsOfUnityGroup.groupScheme K n).X) :
    multiplicativeGroupHomUnits K T
        (f ≫ (TauCeti.RootsOfUnityGroup.inclusionGroupSchemeMap K n).hom.hom) =
      (rootsOfUnityHomOver K n T f : ((algΓ (.of K)).obj T).unopˣ) := by
  unfold multiplicativeGroupHomUnits rootsOfUnityHomOver
  dsimp only [id_eq, MulEquiv.trans_apply]
  apply Units.ext
  erw [TauCeti.RootsOfUnityGroup.characterMulEquivRootsOfUnity_apply,
    TauCeti.DiagonalizableGroup.uliftZPowersMulEquiv_symm_apply]
  change _ = (TauCeti.DiagonalizableGroup.pointsMulEquiv
    ((TauCeti.CommHopfAlgCat.schemePointsAlgΓMulEquiv (R := K)
      (MonoidAlgebra K (ULift.{u} (Multiplicative (ZMod n)))) T) f)
        (ULift.up (TauCeti.RootsOfUnityGroup.generator n)) : ((algΓ (.of K)).obj T).unop)
  rw [TauCeti.RootsOfUnityGroup.inclusionGroupSchemeMap_def]
  simp only [TauCeti.DiagonalizableGroup.pointsMulEquiv_apply,
    TauCeti.DiagonalizableGroup.charOfPoint_apply_coe]
  erw [TauCeti.CommHopfAlgCat.schemePointsAlgΓMulEquiv_mapDomain,
    TauCeti.DiagonalizableGroup.pointsMulEquiv_apply,
    TauCeti.DiagonalizableGroup.charOfPoint_apply_coe]
  erw [BialgHom.mapDomain_apply_apply]
  change ((TauCeti.CommHopfAlgCat.schemePointsAlgΓMulEquiv (R := K)
    (MonoidAlgebra K (ULift.{u} (Multiplicative (ZMod n)))) T) f).ofConv
      ((TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
        (TauCeti.DiagonalizableGroup.coordinateMap K
          (TauCeti.RootsOfUnityGroup.characterQuotient n)))
            (MonoidAlgebra.single (ULift.up (Multiplicative.ofAdd 1)) 1)) = _
  rw [TauCeti.DiagonalizableGroup.toBialgHom_coordinateMap]
  rw [MonoidAlgebra.mapDomainBialgHom_single,
    TauCeti.RootsOfUnityGroup.characterQuotient_apply_up,
    TauCeti.RootsOfUnityGroup.toMultiplicativeZMod_ofAdd_one]


private lemma rootsOfUnityPower_comp (n : ℕ) (T : Over (Spec (.of K)))
    (f : T ⟶ (TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K).X) :
    f ≫ ((𝟙 (TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K)) ^ n).hom.hom = f ^ n := by
  rw [Grp.Hom.hom_pow, Mon.Hom.hom_pow]
  change f ≫ (𝟙 ((TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K).X)) ^ n = f ^ n
  rw [MonObj.comp_pow, Category.comp_id]

private theorem rootsOfUnityPowerSquare_over (n : ℕ) :
    IsPullback (TauCeti.RootsOfUnityGroup.inclusionGroupSchemeMap K n).hom.hom
      (toUnit ((TauCeti.RootsOfUnityGroup.groupScheme K n).X))
      ((𝟙 (TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K)) ^ n).hom.hom
      η[(TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K).X] := by
  have hcomm : (TauCeti.RootsOfUnityGroup.inclusionGroupSchemeMap K n).hom.hom ≫
        ((𝟙 (TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K)) ^ n).hom.hom =
      toUnit ((TauCeti.RootsOfUnityGroup.groupScheme K n).X) ≫
        η[(TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K).X] := by
    rw [rootsOfUnityPower_comp]
    change (TauCeti.RootsOfUnityGroup.inclusionGroupSchemeMap K n).hom.hom ^ n =
      (1 : (TauCeti.RootsOfUnityGroup.groupScheme K n).X ⟶
        (TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K).X)
    apply (multiplicativeGroupHomUnits K ((TauCeti.RootsOfUnityGroup.groupScheme K n).X)).injective
    rw [map_pow, map_one]
    have hunit := rootsOfUnityHomOver_inclusion K n
      (TauCeti.RootsOfUnityGroup.groupScheme K n).X
      (𝟙 (TauCeti.RootsOfUnityGroup.groupScheme K n).X)
    rw [Category.id_comp] at hunit
    rw [hunit]
    exact (rootsOfUnityHomOver K n
      (TauCeti.RootsOfUnityGroup.groupScheme K n).X
      (𝟙 (TauCeti.RootsOfUnityGroup.groupScheme K n).X)).prop
  apply IsPullback.of_isLimit (c := PullbackCone.mk _ _ hcomm)
  refine PullbackCone.isLimitAux' _ (fun s ↦ ?_)
  let U := multiplicativeGroupHomUnits K s.pt
  let E := (rootsOfUnityHomOver K n s.pt).symm
  have hf : s.fst ^ n = (1 : s.pt ⟶ (TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K).X)
    := by
    calc
      s.fst ^ n = s.fst ≫ ((𝟙 (TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K)) ^
        n).hom.hom :=
        (rootsOfUnityPower_comp K n s.pt s.fst).symm
      _ = s.snd ≫ η[(TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K).X] := s.condition
      _ = toUnit s.pt ≫ η[(TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K).X] :=
        congrArg (fun g ↦ g ≫ η[(TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K).X])
          (toUnit_unique _ _)
      _ = 1 := rfl
  have hroot : U s.fst ^ n = 1 := by
    simpa only [map_pow, map_one] using congrArg U hf
  let ζ : rootsOfUnity n ((algΓ (.of K)).obj s.pt).unop := ⟨U s.fst, hroot⟩
  refine ⟨E ζ, ?_, toUnit_unique _ _, ?_⟩
  · apply U.injective
    change multiplicativeGroupHomUnits K s.pt
      (E ζ ≫ (TauCeti.RootsOfUnityGroup.inclusionGroupSchemeMap K n).hom.hom) = U s.fst
    rw [rootsOfUnityHomOver_inclusion]
    change ((rootsOfUnityHomOver K n s.pt)
      ((rootsOfUnityHomOver K n s.pt).symm ζ) : ((algΓ (.of K)).obj s.pt).unopˣ) = U s.fst
    rw [MulEquiv.apply_symm_apply]
  · intro m hm _
    apply (rootsOfUnityHomOver K n s.pt).injective
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [← rootsOfUnityHomOver_inclusion]
    change m ≫ (TauCeti.RootsOfUnityGroup.inclusionGroupSchemeMap K n).hom.hom = s.fst at hm
    rw [hm]

/-- The roots-of-unity scheme is the pullback, in schemes, of the `n`-th power
endomorphism of the multiplicative group along its unit section. This includes
order zero, where the power map is constant one and the kernel is all of `Gₘ`. -/
theorem rootsOfUnityPowerSquare_isPullback (n : ℕ) :
    IsPullback (TauCeti.RootsOfUnityGroup.inclusionGroupSchemeMap K n).hom.hom.left
      ((TauCeti.RootsOfUnityGroup.groupScheme K n).X).hom
      ((𝟙 (TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K)) ^ n).hom.hom.left
      η[(TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K).X].left := by
  exact IsPullback.map (Over.forget (Spec (.of K)))
    (rootsOfUnityPowerSquare_over K n)

/-- The power-kernel square is a pullback over the base, with arbitrary schemes
as test objects. -/
theorem rootsOfUnityPowerSquare_isPullback_over (n : ℕ) :
    IsPullback (TauCeti.RootsOfUnityGroup.inclusionGroupSchemeMap K n).hom.hom
      (toUnit ((TauCeti.RootsOfUnityGroup.groupScheme K n).X))
      ((𝟙 (TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K)) ^ n).hom.hom
      η[(TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K).X] := by
  exact rootsOfUnityPowerSquare_over K n

/-- Every morphism from a scheme over `K` to `Gₘ` whose `n`-th power is the unit
factors uniquely through the canonical roots-of-unity inclusion. The source
need not be affine, reduced or nonempty. -/
theorem rootsOfUnitySchemeKernel_universal (n : ℕ)
    (T : Over (Spec (.of K))) (f : T ⟶ (TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K).X)
    (hf : f ≫ ((𝟙 (TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K)) ^ n).hom.hom =
      toUnit T ≫ η[(TauCeti.DiagonalizableGroup.multiplicativeGroupScheme K).X]) :
    ∃! lift : T ⟶ (TauCeti.RootsOfUnityGroup.groupScheme K n).X,
      lift ≫ (TauCeti.RootsOfUnityGroup.inclusionGroupSchemeMap K n).hom.hom = f := by
  let square := rootsOfUnityPowerSquare_isPullback_over K n
  refine ⟨square.lift f (toUnit T) hf, square.lift_fst _ _ _, ?_⟩
  intro candidate hcandidate
  apply square.hom_ext
  · exact hcandidate.trans (square.lift_fst _ _ _).symm
  · exact toUnit_unique _ _


/-- Under the coordinate equivalence, comultiplication sends the distinguished
root to its tensor square, as in Milne's Algebraic Groups, item 2.4. -/
lemma rootsOfUnity_adjoinRootEquiv_comul_root (n : ℕ) [NeZero n] :
    Algebra.TensorProduct.map
        (TauCeti.RootsOfUnityGroup.adjoinRootEquiv (R := K) n).symm.toAlgHom
        (TauCeti.RootsOfUnityGroup.adjoinRootEquiv (R := K) n).symm.toAlgHom
        (Coalgebra.comul
          (TauCeti.RootsOfUnityGroup.adjoinRootEquiv (R := K) n
            (AdjoinRoot.root (X ^ n - 1 : K[X])))) =
      AdjoinRoot.root (X ^ n - 1 : K[X]) ⊗ₜ[K]
        AdjoinRoot.root (X ^ n - 1 : K[X]) := by
  rw [TauCeti.RootsOfUnityGroup.adjoinRootEquiv_root,
    (MonoidAlgebra.isGroupLikeElem_single_one _).comul_eq_tmul_self,
    Algebra.TensorProduct.map_tmul]
  simp

/-- Under the coordinate equivalence, the counit sends the distinguished root to one. -/
lemma rootsOfUnity_adjoinRootEquiv_counit_root (n : ℕ) [NeZero n] :
    Coalgebra.counit (R := K)
        (TauCeti.RootsOfUnityGroup.adjoinRootEquiv (R := K) n
          (AdjoinRoot.root (X ^ n - 1 : K[X]))) = 1 := by
  rw [TauCeti.RootsOfUnityGroup.adjoinRootEquiv_root]
  exact (MonoidAlgebra.isGroupLikeElem_single_one _).counit_eq_one

/-- Under the coordinate equivalence, the antipode sends the distinguished
root to its standard inverse representative T ^ (n - 1). -/
lemma rootsOfUnity_adjoinRootEquiv_antipode_root (n : ℕ) [NeZero n] :
    (TauCeti.RootsOfUnityGroup.adjoinRootEquiv (R := K) n).symm
        (HopfAlgebra.antipode K
          (TauCeti.RootsOfUnityGroup.adjoinRootEquiv (R := K) n
            (AdjoinRoot.root (X ^ n - 1 : K[X])))) =
      AdjoinRoot.root (X ^ n - 1 : K[X]) ^ (n - 1) := by
  rw [TauCeti.RootsOfUnityGroup.adjoinRootEquiv_root, MonoidAlgebra.antipode_single]
  simp only [HopfAlgebra.antipode_one]
  rw [show MonoidAlgebra.single (TauCeti.RootsOfUnityGroup.generator n)⁻¹ (1 : K) =
      MonoidAlgebra.single (TauCeti.RootsOfUnityGroup.generator n) (1 : K) ^ (n - 1) by
    rw [MonoidAlgebra.single_pow, one_pow]
    congr 1
    rw [inv_eq_iff_mul_eq_one, ← pow_succ',
      Nat.sub_add_cancel ((Nat.one_le_iff_ne_zero).2 (NeZero.ne n)),
      TauCeti.RootsOfUnityGroup.generator_pow_eq_one]]
  rw [map_pow, TauCeti.RootsOfUnityGroup.adjoinRootEquiv_symm_single_generator]

/-- The cyclic coordinate algebra is finitely presented over every commutative base,
including at order zero, where it is a Laurent polynomial algebra. -/
instance rootsOfUnityCoordinate_finitePresentation (n : ℕ) :
    Algebra.FinitePresentation K
      (MonoidAlgebra K (TauCeti.RootsOfUnityGroup.characterGroup.{u} n)) := by
  let e := MonoidAlgebra.domCongr K K
    (MulEquiv.ulift : ULift.{u} (Multiplicative (ZMod n)) ≃* Multiplicative (ZMod n))
  have : Algebra.FinitePresentation K (MonoidAlgebra K (Multiplicative (ZMod n))) := by
    cases n with
    | zero =>
      let : IsScalarTower K K[X] (LaurentPolynomial K) :=
        IsScalarTower.of_algebraMap_eq fun r => by
          change LaurentPolynomial.C r = Polynomial.toLaurent (Polynomial.C r)
          exact (Polynomial.toLaurent_C r).symm
      let : Algebra.FinitePresentation K (LaurentPolynomial K) :=
        Algebra.FinitePresentation.of_isLocalizationAway (X : K[X])
      exact Algebra.FinitePresentation.equiv
        (AddMonoidAlgebra.toMultiplicativeAlgEquiv K K ℤ)
    | succ n =>
      exact Algebra.FinitePresentation.equiv
        (TauCeti.RootsOfUnityGroup.adjoinRootEquiv (R := K) (n + 1))
  exact Algebra.FinitePresentation.equiv e.symm

/-- The roots-of-unity structure morphism is finite at every positive order. -/
instance rootsOfUnityScheme_isFinite (n : ℕ) [NeZero n] :
    IsFinite (TauCeti.RootsOfUnityGroup.groupScheme K n).X.hom := by
  unfold TauCeti.RootsOfUnityGroup.groupScheme
  rw [TauCeti.DiagonalizableGroup.groupScheme_def, TauCeti.hopfSpec_obj_eq_asOver]
  exact (IsFinite.SpecMap_iff
    (CommRingCat.ofHom (algebraMap K
      (MonoidAlgebra K (TauCeti.RootsOfUnityGroup.characterGroup.{u} n))))).mpr
      ((RingHom.finite_algebraMap (A := K)).mpr inferInstance)

/-- The roots-of-unity structure morphism is flat at every order, including zero. -/
instance rootsOfUnityScheme_flat (n : ℕ) :
    Flat (TauCeti.RootsOfUnityGroup.groupScheme K n).X.hom := by
  unfold TauCeti.RootsOfUnityGroup.groupScheme
  rw [TauCeti.DiagonalizableGroup.groupScheme_def, TauCeti.hopfSpec_obj_eq_asOver]
  exact (Flat.SpecMap_iff (f := CommRingCat.ofHom (algebraMap K
    (MonoidAlgebra K (TauCeti.RootsOfUnityGroup.characterGroup.{u} n))))).mpr
      ((RingHom.flat_algebraMap_iff (R := K)).mpr Module.Flat.of_free)

/-- The structure morphism is locally of finite presentation at every order, including zero. -/
instance rootsOfUnityScheme_locallyOfFinitePresentation (n : ℕ) :
    LocallyOfFinitePresentation (TauCeti.RootsOfUnityGroup.groupScheme K n).X.hom := by
  unfold TauCeti.RootsOfUnityGroup.groupScheme
  rw [TauCeti.DiagonalizableGroup.groupScheme_def, TauCeti.hopfSpec_obj_eq_asOver]
  exact (LocallyOfFinitePresentation.SpecMap_iff (CommRingCat.ofHom (algebraMap K
    (MonoidAlgebra K (TauCeti.RootsOfUnityGroup.characterGroup.{u} n))))).mpr
      ((RingHom.finitePresentation_algebraMap (A := K)).mpr inferInstance)

/-- At positive order, the structure morphism has rank n at every base point.
The base may be any commutative ring; the spectrum of the zero ring is empty. -/
@[simp]
lemma rootsOfUnityScheme_finrank (n : ℕ) [NeZero n] (x : Spec (.of K)) :
    (TauCeti.RootsOfUnityGroup.groupScheme K n).X.hom.finrank x = n := by
  unfold TauCeti.RootsOfUnityGroup.groupScheme
  rw [TauCeti.DiagonalizableGroup.groupScheme_def, TauCeti.hopfSpec_obj_eq_asOver]
  let : Nontrivial K := x.nontrivial
  have h : Module.finrank K
      (MonoidAlgebra K (TauCeti.RootsOfUnityGroup.characterGroup.{u} n)) = n := by
    have hc : Fintype.card (TauCeti.RootsOfUnityGroup.characterGroup.{u} n) = n := by
      change Fintype.card (ULift.{u} (Multiplicative (ZMod n))) = n
      simp [ZMod.card]
    exact (Module.finrank_eq_card_basis
      (MonoidAlgebra.basis (TauCeti.RootsOfUnityGroup.characterGroup.{u} n) K)).trans hc
  exact (Scheme.Hom.finrank_SpecMap_algebraMap K
    (MonoidAlgebra K (TauCeti.RootsOfUnityGroup.characterGroup.{u} n)) x).trans
      ((congrFun (Module.rankAtStalk_eq_finrank_of_free
        (R := K) (M := MonoidAlgebra K (TauCeti.RootsOfUnityGroup.characterGroup.{u} n))) x).trans
          h)

end AlgebraicGeometry
