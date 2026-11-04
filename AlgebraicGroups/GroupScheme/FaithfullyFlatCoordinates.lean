/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupObject.FlatOverField
public import AlgebraicGroups.GroupScheme.SurjectiveBaseChange
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-!
# Faithfully flat coordinate maps of affine group schemes

A dominant homomorphism between affine group schemes locally of finite type over a field
has a faithfully flat coordinate map when its target is reduced. The coordinate rings may
be presented in universes independent of the field and of one another. Compatibility of
the presentations with the coefficient map identifies the scalar action in the conclusion.

The geometric step uses `Flat.of_group_hom_over_field`, together with surjectivity from
schematic dominance. The coordinate step uses Mathlib's affine faithfully-flatness criterion,
scalar-specific algebra equivalences and `Module.FaithfullyFlat.trans`.

For these coordinate presentations, injectivity of the coefficient map forces dominance
of the group homomorphism and therefore also implies faithful flatness.

## Limitations

This result takes presentations of the coordinate rings of given group schemes. It does
not construct a group scheme from a Hopf algebra in another universe or transport Hopf
operations between universes.

## References

* J. S. Milne, *Algebraic Groups* (2017), 1.70.
* The group-homomorphism flatness criterion in `AlgebraicGroups.GroupObject.FlatOverField`.
* Mathlib's affine flatness and faithfully flat module APIs.

This formalization was prepared with AI assistance.
-/

@[expose] public section

universe u v w
namespace AlgebraicGeometry
open CategoryTheory
open scoped CategoryTheory.MonObj

/-- The coefficient map of a dominant homomorphism of affine group schemes locally of
finite type over a field is faithfully flat if the target is reduced, for any compatible
coordinate presentations. This is the coordinate-ring form of Milne, 1.70. -/
theorem faithfullyFlat_of_dominant_affine_group_hom_coordinates
    {K : Type u} [Field K] {G H : Scheme.{u}}
    (fG : G ⟶ Spec (.of K)) (fH : H ⟶ Spec (.of K))
    [IsAffine G] [IsAffine H]
    [LocallyOfFiniteType fG] [LocallyOfFiniteType fH]
    [GrpObj (Over.mk fG)] [GrpObj (Over.mk fH)]
    (φ : Over.mk fG ⟶ Over.mk fH) [IsMonHom φ]
    [IsDominant φ.left] [IsReduced H]
    {A : Type v} {B : Type w} [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] [Algebra A B]
    (eA : A ≃ₐ[K] ((algΓ (.of K)).obj (Over.mk fH)).unop)
    (eB : B ≃ₐ[K] ((algΓ (.of K)).obj (Over.mk fG)).unop)
    (hφ : eB.toRingHom.comp (algebraMap A B) =
      φ.left.appTop.hom.comp eA.toRingHom) :
    Module.FaithfullyFlat A B := by
  have : IsAffine (Over.mk fG).left := (show IsAffine G from inferInstance)
  have : IsAffine (Over.mk fH).left := (show IsAffine H from inferInstance)
  have : IsReduced (Over.mk fH).left := (show IsReduced H from inferInstance)
  -- Retain the supplied action before introducing any coordinate-ring scalar structures.
  let originalAB : Algebra A B := inferInstance
  let originalModule : Module A B := inferInstance
  let originalMap : A →+* B := @algebraMap A B _ _ originalAB
  let regularA : Algebra A A := inferInstance
  have hcomp : φ.left ≫ fH = fG := Over.w φ
  have : LocallyOfFiniteType (φ.left ≫ fH) := by
    rw [hcomp]
    infer_instance
  have : LocallyOfFiniteType φ.left := locallyOfFiniteType_of_comp φ.left fH
  have : IsSchemeTheoreticallyDominant φ.left :=
    IsSchemeTheoreticallyDominant.of_isDominant φ.left
  have : Surjective φ.left :=
    Surjective.of_schemeTheoreticallyDominant_affine_group_hom fG fH φ
  have : IsLocallyNoetherian (Spec (.of K)) :=
    isLocallyNoetherian_Spec.mpr inferInstance
  have : IsLocallyNoetherian H := LocallyOfFiniteType.isLocallyNoetherian fH
  have : CompactSpace H :=
    isCompact_univ_iff.mp (isAffineOpen_top H).isCompact
  have : IsNoetherian H := {}
  have : Flat φ.left :=
    Flat.of_group_hom_over_field K (Over.mk fG) (Over.mk fH) φ
      (finite_irreducibleComponents_of_isNoetherian (X := H))
  let As : Type u := ((algΓ (.of K)).obj (Over.mk fH)).unop
  let Bs : Type u := ((algΓ (.of K)).obj (Over.mk fG)).unop
  let ψ : As →+* Bs := φ.left.appTop.hom
  let EA : As ≃ₐ[K] A := eA.symm
  let EB : Bs ≃ₐ[K] B := eB.symm
  have hψ : ψ.FaithfullyFlat :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine φ.left).mp
      ⟨inferInstance, inferInstance⟩
  -- The coefficient square supplies linearity over As, not just over K.
  have hcoeff (a : A) : eB (originalMap a) = ψ (eA a) :=
    congrArg (fun f : A →+* Bs => f a) hφ
  have hEB (x : As) : EB (ψ x) = originalMap (EA x) := by
    apply eB.injective
    change eB (eB.symm (ψ x)) = eB (originalMap (eA.symm x))
    rw [eB.apply_symm_apply, hcoeff, eA.apply_symm_apply]
  -- These are three different scalar structures; none replaces Algebra A B.
  let coordinateAlgebra : Algebra As Bs := ψ.toAlgebra
  let presentationAlgebra : Algebra A As := eA.toRingHom.toAlgebra
  let restrictedAlgebra : Algebra As B := (originalMap.comp EA.toRingHom).toAlgebra
  let : Algebra As Bs := coordinateAlgebra
  let : Algebra A As := presentationAlgebra
  let : Algebra As B := restrictedAlgebra
  have hFFAsBs : Module.FaithfullyFlat As Bs := by
    apply (RingHom.faithfullyFlat_algebraMap_iff).mp
    change ψ.FaithfullyFlat
    exact hψ
  let EBOverAs : @AlgEquiv As Bs B _ _ _ coordinateAlgebra restrictedAlgebra :=
    AlgEquiv.ofRingEquiv (f := EB.toRingEquiv) (by
      intro x
      change EB (ψ x) = originalMap (EA x)
      exact hEB x)
  let EAOverA : @AlgEquiv A As A _ _ _ presentationAlgebra regularA := by
    letI : Algebra A A := regularA
    exact AlgEquiv.ofRingEquiv (f := EA.toRingEquiv) (by
      intro a
      change eA.symm (eA a) = a
      exact eA.symm_apply_apply a)
  have hFFAsB : @Module.FaithfullyFlat As B _ _
      (@Algebra.toModule As B _ _ restrictedAlgebra) := by
    have : Module.FaithfullyFlat As Bs := hFFAsBs
    exact Module.FaithfullyFlat.of_linearEquiv (R := As) (M := Bs)
      EBOverAs.symm.toLinearEquiv
  have hFFAAs : @Module.FaithfullyFlat A As _ _
      (@Algebra.toModule A As _ _ presentationAlgebra) := by
    let : Algebra A A := regularA
    exact Module.FaithfullyFlat.of_linearEquiv (R := A) (M := A)
      EAOverA.toLinearEquiv
  have htower : IsScalarTower A As B := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    change originalMap a = originalMap (EA (eA a))
    calc
      originalMap a = EB (eB (originalMap a)) := (eB.symm_apply_apply _).symm
      _ = EB (ψ (eA a)) := congrArg EB (hcoeff a)
      _ = originalMap (EA (eA a)) := hEB _
  -- The last module argument is the supplied A-action on B, including for equal carriers.
  exact @Module.FaithfullyFlat.trans A _ As _ presentationAlgebra B _ originalModule
    (@Algebra.toModule As B _ _ restrictedAlgebra) htower hFFAAs hFFAsB

/-- An injective coefficient map between compatible coordinate presentations of affine
group schemes locally of finite type over a field is faithfully flat when the target
group scheme is reduced. This follows from the coordinate-ring form of Milne,
1.70, by deriving dominance from injectivity. -/
theorem faithfullyFlat_of_injective_group_coordinate_map
    {K : Type u} [Field K] {G H : Scheme.{u}}
    (fG : G ⟶ Spec (.of K)) (fH : H ⟶ Spec (.of K))
    [IsAffine G] [IsAffine H]
    [LocallyOfFiniteType fG] [LocallyOfFiniteType fH]
    [GrpObj (Over.mk fG)] [GrpObj (Over.mk fH)]
    (φ : Over.mk fG ⟶ Over.mk fH) [IsMonHom φ]
    [IsReduced H]
    {A : Type v} {B : Type w} [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] [Algebra A B]
    (eA : A ≃ₐ[K] ((algΓ (.of K)).obj (Over.mk fH)).unop)
    (eB : B ≃ₐ[K] ((algΓ (.of K)).obj (Over.mk fG)).unop)
    (hφ : eB.toRingHom.comp (algebraMap A B) =
      φ.left.appTop.hom.comp eA.toRingHom)
    (hinj : Function.Injective (algebraMap A B)) :
    Module.FaithfullyFlat A B := by
  have : IsAffine (Over.mk fG).left := (show IsAffine G from inferInstance)
  have : IsAffine (Over.mk fH).left := (show IsAffine H from inferInstance)
  have hψ : Function.Injective φ.left.appTop.hom := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := eA.surjective x
    obtain ⟨b, rfl⟩ := eA.surjective y
    have hab : algebraMap A B a = algebraMap A B b := by
      apply eB.injective
      change (eB.toRingHom.comp (algebraMap A B)) a =
        (eB.toRingHom.comp (algebraMap A B)) b
      rw [hφ]
      exact hxy
    exact congrArg eA (hinj hab)
  have hker : RingHom.ker φ.left.appTop.hom = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot φ.left.appTop.hom).mp hψ
  have hkerSheaf : φ.left.ker = ⊥ := by
    apply Scheme.IdealSheafData.ext_of_isAffine
    rw [Scheme.IdealSheafData.ideal_bot]
    have hle : φ.left.ker.ideal ⟨⊤, isAffineOpen_top H⟩ ≤
        RingHom.ker φ.left.appTop.hom :=
      φ.left.ideal_ker_le ⟨⊤, isAffineOpen_top H⟩
    exact le_antisymm (hle.trans (le_of_eq hker)) bot_le
  have : IsAffineHom φ.left := isAffineHom_of_isAffine φ.left
  have : QuasiCompact φ.left := inferInstance
  have hclosure : closure (Set.range φ.left) = Set.univ := by
    rw [← Scheme.Hom.support_ker φ.left, hkerSheaf,
      Scheme.IdealSheafData.support_bot]
    simp
  have hdense : DenseRange φ.left := by
    change Dense (Set.range φ.left)
    exact dense_iff_closure_eq.mpr hclosure
  have : IsDominant φ.left := by
    rw [dominant_eq_topologically]
    change DenseRange φ.left
    exact hdense
  exact faithfullyFlat_of_dominant_affine_group_hom_coordinates fG fH φ eA eB hφ

end AlgebraicGeometry
