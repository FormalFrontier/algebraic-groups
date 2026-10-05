/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.EffectiveEpi
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.CategoryTheory.EquivalenceRelation
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import AlgebraicGroups.RingTheory.FaithfullyFlat

@[expose] public section

/-!
# Quotients of affine relations

This file defines the categorical affine coequalizer of a pair of affine-
scheme morphisms, its canonical comparison with the kernel pair, and the
coordinate-ring package that implies the expected quotient geometry.

The principal bridge is `hasExpectedGeometry_of_hasExpectedAlgebra`: faithful
flatness of the invariant-ring inclusion and bijectivity of the canonical
tensor-product comparison imply flatness and surjectivity of the quotient map
and invertibility of the kernel-pair comparison.

An arbitrary affine pair has the categorical coequalizer here. The bridge
*assumes* the two hard ring facts; an internal equivalence relation and
finite-flat relation legs are not shown to imply them. Consequently this file
does not prove the finite locally free affine quotient theorem or represent
an fppf quotient sheaf. Its ring comparison applies the first relation map
to the first tensor factor and the second to the second, reversing the leg
order of the displayed comparison in Stacks Project, Proposition 39.23.9
(tag 03BM).

## References

* Stacks Project, Proposition 39.23.9 (tag 03BM), for the finite locally
  free affine equivalence-relation theorem motivating the conditional bridge;
  Lemma 10.83.2 (tag 03C4), for descent of finite module presentation.
* J. S. Milne, *Algebraic Groups*, Appendix B, Theorems B.26 and B.37, for
  the wider quotient setting; their nonaffine and subgroup conclusions are
  not obtained here.
* Mathlib, `Mathlib.AlgebraicGeometry.AffineScheme` for affine spectra and
  coequalizers, `Mathlib.CategoryTheory.EquivalenceRelation` for internal
  relation/effectivity structures, and `Mathlib.AlgebraicGeometry.EffectiveEpi`
  for the faithfully flat geometric setting.
* Mathlib, `Mathlib.Algebra.Algebra.Subalgebra.Basic` for the
  `AlgHom.equalizer` defining the invariant ring, and
  `Mathlib.RingTheory.Flat.Equalizer` for separate flat base-change context;
  `Mathlib.Algebra.Category.Ring.Constructions` and
  `Mathlib.AlgebraicGeometry.Pullbacks` for tensor pushouts and affine
  pullbacks, and `Mathlib.RingTheory.Flat.EquationalCriterion` for the
  finite-presentation-to-projectivity step.
-/

noncomputable section

open CategoryTheory Limits
open scoped TensorProduct

namespace AlgebraicGeometry.AffineRelationQuotient

universe u

variable {R X : AffineScheme.{u}} (s t : R ⟶ X)

/-- The affine coequalizer of a pair `R ⇉ X`. -/
abbrev quotient : AffineScheme.{u} :=
  coequalizer s t

/-- The canonical map from `X` to the affine coequalizer. -/
abbrev quotientMap : X ⟶ quotient s t :=
  coequalizer.π s t

lemma quotientMap_condition :
    s ≫ quotientMap s t = t ≫ quotientMap s t :=
  coequalizer.condition s t

/-- A map invariant under the pair `R ⇉ X` descends to the affine
coequalizer. -/
abbrev lift {Y : AffineScheme.{u}} (f : X ⟶ Y)
    (h : s ≫ f = t ≫ f) : quotient s t ⟶ Y :=
  coequalizer.desc f h

@[reassoc]
lemma quotientMap_lift {Y : AffineScheme.{u}} (f : X ⟶ Y)
    (h : s ≫ f = t ≫ f) : quotientMap s t ≫ lift s t f h = f :=
  coequalizer.π_desc f h

/-- The canonical comparison from `R` to the kernel pair of the affine
coequalizer map. -/
def kernelPairComparison :
    R ⟶ pullback (quotientMap s t) (quotientMap s t) :=
  pullback.lift s t (quotientMap_condition s t)

@[reassoc]
lemma kernelPairComparison_fst :
    kernelPairComparison s t ≫ pullback.fst _ _ = s :=
  pullback.lift_fst _ _ _

@[reassoc]
lemma kernelPairComparison_snd :
    kernelPairComparison s t ≫ pullback.snd _ _ = t :=
  pullback.lift_snd _ _ _

/-- The expected geometric properties of the affine coequalizer: its quotient
map is flat and surjective, and the given relation is its kernel pair. -/
def HasExpectedGeometry : Prop :=
  Flat (quotientMap s t).hom ∧
    Surjective (quotientMap s t).hom ∧
    IsIso (kernelPairComparison s t)

/-- Once the kernel-pair comparison is invertible, the affine coequalizer is
an effective quotient of a categorical equivalence relation. This packages
the final categorical step of Stacks Project, Proposition 39.23.9 (tag
03BM), assuming rather than proving comparison invertibility. -/
def effectiveEquivalenceRelation
    (e : EquivalenceRelation s t) [IsIso (kernelPairComparison s t)] :
    EffectiveEquivalenceRelation s t where
  __ := e
  B := quotient s t
  π := quotientMap s t
  isKernelPair :=
    IsPullback.of_iso_pullback ⟨quotientMap_condition s t⟩
      (asIso (kernelPairComparison s t))
      (kernelPairComparison_fst s t) (kernelPairComparison_snd s t)
  isPushout := IsPushout.mk' (quotientMap_condition s t)
    (fun {_ _ _} h₁ _ ↦ coequalizer.hom_ext h₁)
    (fun {_} a b h ↦ by
      have hab : a = b := by
        calc
          a = 𝟙 _ ≫ a := by simp
          _ = (e.r ≫ s) ≫ a := by rw [e.reflexivity₁]
          _ = e.r ≫ (s ≫ a) := by simp
          _ = e.r ≫ (t ≫ b) := by rw [h]
          _ = (e.r ≫ t) ≫ b := by simp
          _ = 𝟙 _ ≫ b := by rw [e.reflexivity₂]
          _ = b := by simp
      subst b
      exact ⟨lift s t a h, quotientMap_lift s t a h,
        quotientMap_lift s t a h⟩)

namespace Ring

universe v w z

variable (S : Type v) (A : Type w) (C : Type z)
  [CommRing S] [CommRing A] [CommRing C]
  [Algebra S A] [Algebra S C]
variable (f g : A →ₐ[S] C)

/-- The ring on which two algebra morphisms agree. -/
abbrev invariantRing := AlgHom.equalizer f g

/-- Use the first map to make the target an algebra over the invariant ring.
The second map induces the same scalar action. -/
local instance invariantRingAlgebra : Algebra (invariantRing S A C f g) C :=
  (f.comp (invariantRing S A C f g).val).toRingHom.toAlgebra

/-- The first map, regarded as a morphism over the invariant ring. -/
def fst : A →ₐ[invariantRing S A C f g] C :=
  AlgHom.mk' f.toRingHom (fun b x ↦ by
    change f (b.1 * x) = f b.1 * f x
    rw [map_mul])

/-- The second map, regarded as a morphism over the invariant ring. -/
def snd : A →ₐ[invariantRing S A C f g] C :=
  AlgHom.mk' g.toRingHom (fun b x ↦ by
    change g (b.1 * x) = f b.1 * g x
    rw [map_mul, b.2])

/-- The canonical map from the tensor square over the invariant ring to the
target ring. It sends `x ⊗ₜ y` to `f x * g y`, the swapped-leg orientation
relative to the displayed map in Stacks Project, Proposition 39.23.9
(tag 03BM). -/
def kernelPairComparison :
    _root_.TensorProduct (invariantRing S A C f g) A A
      →ₐ[invariantRing S A C f g] C :=
  Algebra.TensorProduct.lift (fst S A C f g) (snd S A C f g)
    (fun _ _ ↦ Commute.all _ _)

@[simp]
lemma kernelPairComparison_tmul (x y : A) :
    kernelPairComparison S A C f g (x ⊗ₜ y) = f x * g y :=
  rfl

/-- The coordinate-algebra hypotheses needed for the affine quotient: the
object ring is faithfully flat over the invariant ring, and the canonical
tensor-square map identifies the relation ring. -/
def HasExpectedAlgebra : Prop :=
  Module.FaithfullyFlat (invariantRing S A C f g) A ∧
    Function.Bijective (kernelPairComparison S A C f g)

/-- Under the expected tensor-square comparison, finite presentation of the
relation ring over the object ring descends to finite presentation of the
object ring over the invariant ring. This is the module-presentation descent
of Stacks Project, Lemma 10.83.2 (tag 03C4), conditional on the faithful
flatness and tensor equivalence supplied as hypotheses. -/
lemma finitePresentation_of_hasExpectedAlgebra
    [Algebra A C] [Module.FinitePresentation A C]
    (hf : algebraMap A C = f.toRingHom) (h : HasExpectedAlgebra S A C f g) :
    Module.FinitePresentation (invariantRing S A C f g) A := by
  let k : _root_.TensorProduct (invariantRing S A C f g) A A →ₐ[A] C :=
    AlgHom.mk' (kernelPairComparison S A C f g).toRingHom fun a x ↦ by
      rw [Algebra.smul_def, Algebra.smul_def, map_mul]
      congr 1
      simp [kernelPairComparison]
      exact (DFunLike.congr_fun hf a).symm
  let _ : Module.FaithfullyFlat (invariantRing S A C f g) A := h.1
  let e := LinearEquiv.ofBijective
    k.toLinearMap h.2
  let _ : Module.FinitePresentation A
      (_root_.TensorProduct (invariantRing S A C f g) A A) :=
    Module.FinitePresentation.of_equiv e.symm
  exact Module.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat A

/-- Under the same hypotheses, the object ring is a finite projective module
over the invariant ring: descend module finite presentation as in Stacks
Project, Lemma 10.83.2 (tag 03C4), then use Mathlib's theorem that finitely
presented flat modules are projective. Faithful flatness and the comparison
are assumed here rather than derived as in Proposition 39.23.9 (tag 03BM). -/
lemma projective_of_hasExpectedAlgebra
    [Algebra A C] [Module.FinitePresentation A C]
    (hf : algebraMap A C = f.toRingHom) (h : HasExpectedAlgebra S A C f g) :
    Module.Projective (invariantRing S A C f g) A := by
  let _ : Module.FaithfullyFlat (invariantRing S A C f g) A := h.1
  let _ : Module.FinitePresentation (invariantRing S A C f g) A :=
    finitePresentation_of_hasExpectedAlgebra S A C f g hf h
  exact Module.Flat.projective_of_finitePresentation

end Ring

/-- The invariant ring of the maps on global sections induced by `s` and
`t`. -/
abbrev coordinateInvariantRing := Ring.invariantRing
  ℤ Γ(X.obj, ⊤) Γ(R.obj, ⊤)
    s.hom.appTop.hom.toIntAlgHom t.hom.appTop.hom.toIntAlgHom

/-- The opposite of the affine coequalizer cofork, expressed as a fork. -/
def quotientOpFork : Fork s.op t.op :=
  Fork.ofι (coequalizer.π s t).op (by
    simp only [← op_comp]
    rw [coequalizer.condition])

/-- The opposite affine coequalizer fork is limiting. -/
def quotientOpForkIsLimit : IsLimit (quotientOpFork s t) :=
  Cofork.isColimitOfπEquivIsLimitOp
    (coequalizer.π s t) (coequalizer.π s t)
    (coequalizer.condition s t) (by
      simp only [← op_comp]
      rw [coequalizer.condition]) rfl
    (coequalizerIsCoequalizer s t)

/-- Applying global sections to the opposite affine coequalizer fork gives a
fork of commutative rings. -/
def quotientRingFork :
    Fork (AffineScheme.Γ.map s.op) (AffineScheme.Γ.map t.op) :=
  Fork.ofι (AffineScheme.Γ.map (coequalizer.π s t).op) (by
    simp only [← AffineScheme.Γ.map_comp]
    rw [← op_comp, ← op_comp, coequalizer.condition])

/-- The global-sections fork of the affine coequalizer is limiting. -/
def quotientRingForkIsLimit : IsLimit (quotientRingFork s t) := by
  apply isLimitForkMapOfIsLimit
  exact quotientOpForkIsLimit s t

/-- The global sections of the affine coequalizer are canonically the
equalizer of the maps on global sections. -/
def quotientInvariantIso :
    (quotientRingFork s t).pt ≅
      (CommRingCat.equalizerFork
        (AffineScheme.Γ.map s.op) (AffineScheme.Γ.map t.op)).pt :=
  (quotientRingForkIsLimit s t).conePointUniqueUpToIso
    (CommRingCat.equalizerForkIsLimit
      (AffineScheme.Γ.map s.op) (AffineScheme.Γ.map t.op))

lemma quotientInvariantIso_hom_comp :
    (quotientInvariantIso s t).hom ≫ CommRingCat.ofHom
      (coordinateInvariantRing s t).val.toRingHom =
      (quotientMap s t).hom.appTop := by
  exact (quotientRingForkIsLimit s t).conePointUniqueUpToIso_hom_comp
    (CommRingCat.equalizerForkIsLimit
      (AffineScheme.Γ.map s.op) (AffineScheme.Γ.map t.op)) WalkingParallelPair.zero

/-- Faithful flatness of the invariant-ring inclusion transports to the affine
coequalizer map. -/
lemma quotientMap_faithfullyFlat_of_hasExpectedAlgebra
    (h : Ring.HasExpectedAlgebra
      ℤ Γ(X.obj, ⊤) Γ(R.obj, ⊤)
        s.hom.appTop.hom.toIntAlgHom t.hom.appTop.hom.toIntAlgHom) :
    (quotientMap s t).hom.appTop.hom.FaithfullyFlat := by
  let D := coordinateInvariantRing s t
  let _ : Algebra D Γ(X.obj, ⊤) := D.val.toRingHom.toAlgebra
  have hD : D.val.toRingHom.FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.mpr h.1
  have hIso : (quotientInvariantIso s t).hom.hom.FaithfullyFlat :=
    RingHom.FaithfullyFlat.of_bijective
      (ConcreteCategory.bijective_of_isIso (quotientInvariantIso s t).hom)
  have hcomp := RingHom.FaithfullyFlat.stableUnderComposition
    (quotientInvariantIso s t).hom.hom D.val.toRingHom hIso hD
  rw [← quotientInvariantIso_hom_comp s t]
  exact hcomp

set_option linter.style.haveILetI false in
/-- Bijectivity of the tensor comparison identifies the square of coordinate
rings as a pushout over the invariant ring. -/
lemma invariantSquare_isPushout_of_hasExpectedAlgebra
    (h : Ring.HasExpectedAlgebra
      ℤ Γ(X.obj, ⊤) Γ(R.obj, ⊤)
        s.hom.appTop.hom.toIntAlgHom t.hom.appTop.hom.toIntAlgHom) :
    IsPushout
      (CommRingCat.ofHom (coordinateInvariantRing s t).val.toRingHom)
      (CommRingCat.ofHom (coordinateInvariantRing s t).val.toRingHom)
      s.hom.appTop t.hom.appTop := by
  letI : Algebra (coordinateInvariantRing s t) Γ(R.obj, ⊤) :=
    (s.hom.appTop.hom.toIntAlgHom.comp
      (coordinateInvariantRing s t).val).toRingHom.toAlgebra
  let k := Ring.kernelPairComparison
    ℤ Γ(X.obj, ⊤) Γ(R.obj, ⊤)
      s.hom.appTop.hom.toIntAlgHom t.hom.appTop.hom.toIntAlgHom
  let e : CommRingCat.of
        (_root_.TensorProduct (coordinateInvariantRing s t)
          Γ(X.obj, ⊤) Γ(X.obj, ⊤)) ≅
      CommRingCat.of Γ(R.obj, ⊤) :=
    (RingEquiv.ofBijective k.toRingHom h.2).toCommRingCatIso
  apply (CommRingCat.isPushout_tensorProduct
    (coordinateInvariantRing s t) Γ(X.obj, ⊤) Γ(X.obj, ⊤)).of_iso
      (Iso.refl _) (Iso.refl _) (Iso.refl _) e
  · rfl
  · rfl
  · ext x
    simp [e]
    simp [k]
  · ext x
    simp [e]
    simp [k]

/-- The affine coequalizer is canonically the spectrum of the invariant
ring. -/
def quotientInvariantSpecIso :
    (quotient s t).obj ≅ Spec (CommRingCat.of (coordinateInvariantRing s t)) :=
  (quotient s t).obj.isoSpec ≪≫
    Scheme.Spec.mapIso (quotientInvariantIso s t).symm.op

set_option backward.isDefEq.respectTransparency false in
lemma specMap_coordinateInvariantVal :
    Spec.map (CommRingCat.ofHom
      (coordinateInvariantRing s t).val.toRingHom) =
      Spec.map (quotientMap s t).hom.appTop ≫
        (Scheme.Spec.mapIso (quotientInvariantIso s t).symm.op).hom := by
  change Spec.map (CommRingCat.ofHom
      (coordinateInvariantRing s t).val.toRingHom) =
    Spec.map (quotientMap s t).hom.appTop ≫
      Spec.map (quotientInvariantIso s t).inv
  have hring :
      (quotientInvariantIso s t).inv ≫ (quotientMap s t).hom.appTop =
        CommRingCat.ofHom (coordinateInvariantRing s t).val.toRingHom := by
    exact (quotientInvariantIso s t).inv_comp_eq.mpr
      (quotientInvariantIso_hom_comp s t).symm
  calc
    Spec.map (CommRingCat.ofHom
        (coordinateInvariantRing s t).val.toRingHom) =
        Spec.map ((quotientInvariantIso s t).inv ≫
          (quotientMap s t).hom.appTop) :=
      congrArg (fun f : CommRingCat.of (coordinateInvariantRing s t) ⟶
        Γ(X.obj, ⊤) ↦ Spec.map f) hring.symm
    _ = Spec.map (quotientMap s t).hom.appTop ≫
        Spec.map (quotientInvariantIso s t).inv := Spec.map_comp _ _

/-- The coordinate-ring pushout gives a pullback square of affine spectra. -/
lemma invariantSpecSquare_isPullback_of_hasExpectedAlgebra
    (h : Ring.HasExpectedAlgebra
      ℤ Γ(X.obj, ⊤) Γ(R.obj, ⊤)
        s.hom.appTop.hom.toIntAlgHom t.hom.appTop.hom.toIntAlgHom) :
    IsPullback
      (Spec.map s.hom.appTop) (Spec.map t.hom.appTop)
      (Spec.map (CommRingCat.ofHom
        (coordinateInvariantRing s t).val.toRingHom))
      (Spec.map (CommRingCat.ofHom
        (coordinateInvariantRing s t).val.toRingHom)) :=
  AlgebraicGeometry.isPullback_SpecMap_of_isPushout
    (CommRingCat.ofHom (coordinateInvariantRing s t).val.toRingHom)
    (CommRingCat.ofHom (coordinateInvariantRing s t).val.toRingHom)
    s.hom.appTop t.hom.appTop
    (invariantSquare_isPushout_of_hasExpectedAlgebra s t h)

/-- The original relation square over the affine coequalizer is a pullback
whenever its coordinate rings have the expected algebraic form. -/
lemma relationSquare_isPullback_of_hasExpectedAlgebra
    (h : Ring.HasExpectedAlgebra
      ℤ Γ(X.obj, ⊤) Γ(R.obj, ⊤)
        s.hom.appTop.hom.toIntAlgHom t.hom.appTop.hom.toIntAlgHom) :
    IsPullback s.hom t.hom (quotientMap s t).hom (quotientMap s t).hom := by
  apply (invariantSpecSquare_isPullback_of_hasExpectedAlgebra s t h).of_iso'
    R.obj.isoSpec X.obj.isoSpec X.obj.isoSpec (quotientInvariantSpecIso s t)
  · exact Scheme.isoSpec_hom_naturality s.hom
  · exact Scheme.isoSpec_hom_naturality t.hom
  · simp only [quotientInvariantSpecIso, Iso.trans_hom]
    rw [specMap_coordinateInvariantVal]
    exact Scheme.isoSpec_hom_naturality_assoc (quotientMap s t).hom _
  · simp only [quotientInvariantSpecIso, Iso.trans_hom]
    rw [specMap_coordinateInvariantVal]
    exact Scheme.isoSpec_hom_naturality_assoc (quotientMap s t).hom _

set_option backward.isDefEq.respectTransparency false in
/-- The canonical comparison from the relation to the kernel pair is
invertible under the expected coordinate-algebra hypotheses. -/
lemma kernelPairComparison_isIso_of_hasExpectedAlgebra
    (h : Ring.HasExpectedAlgebra
      ℤ Γ(X.obj, ⊤) Γ(R.obj, ⊤)
        s.hom.appTop.hom.toIntAlgHom t.hom.appTop.hom.toIntAlgHom) :
    IsIso (kernelPairComparison s t) := by
  let hrel := relationSquare_isPullback_of_hasExpectedAlgebra s t h
  let hpull : IsPullback
      (pullback.fst (quotientMap s t) (quotientMap s t)).hom
      (pullback.snd (quotientMap s t) (quotientMap s t)).hom
      (quotientMap s t).hom (quotientMap s t).hom :=
    (IsPullback.of_hasPullback (quotientMap s t) (quotientMap s t)).map
      AffineScheme.forgetToScheme
  let e := hrel.isoIsPullback _ _ hpull
  have heq : (kernelPairComparison s t).hom = e.hom := by
    apply hpull.hom_ext
    · calc
        (kernelPairComparison s t).hom ≫
            (pullback.fst (quotientMap s t) (quotientMap s t)).hom = s.hom := by
          have hk := congrArg (fun f ↦ AffineScheme.forgetToScheme.map f)
            (kernelPairComparison_fst s t)
          change (kernelPairComparison s t).hom ≫
            (pullback.fst (quotientMap s t) (quotientMap s t)).hom = s.hom at hk
          exact hk
        _ = e.hom ≫
            (pullback.fst (quotientMap s t) (quotientMap s t)).hom :=
          (hrel.isoIsPullback_hom_fst _ _ hpull).symm
    · calc
        (kernelPairComparison s t).hom ≫
            (pullback.snd (quotientMap s t) (quotientMap s t)).hom = t.hom := by
          have hk := congrArg (fun f ↦ AffineScheme.forgetToScheme.map f)
            (kernelPairComparison_snd s t)
          change (kernelPairComparison s t).hom ≫
            (pullback.snd (quotientMap s t) (quotientMap s t)).hom = t.hom at hk
          exact hk
        _ = e.hom ≫
            (pullback.snd (quotientMap s t) (quotientMap s t)).hom :=
          (hrel.isoIsPullback_hom_snd _ _ hpull).symm
  let _ : IsIso (AffineScheme.forgetToScheme.map
      (kernelPairComparison s t)) := by
    change IsIso (kernelPairComparison s t).hom
    rw [heq]
    infer_instance
  exact isIso_of_reflects_iso (kernelPairComparison s t)
    AffineScheme.forgetToScheme

/-- Faithful flatness and tensor-comparison bijectivity imply all expected
geometric properties of the affine coequalizer. These are the geometric
consequences in Stacks Project, Proposition 39.23.9 (tag 03BM), but the two
algebraic hypotheses are assumed here, not deduced from finite-flat relation
legs. -/
lemma hasExpectedGeometry_of_hasExpectedAlgebra
    (h : Ring.HasExpectedAlgebra
      ℤ Γ(X.obj, ⊤) Γ(R.obj, ⊤)
        s.hom.appTop.hom.toIntAlgHom t.hom.appTop.hom.toIntAlgHom) :
    HasExpectedGeometry s t := by
  have hfs := (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine
    (quotientMap s t).hom).mpr
      (quotientMap_faithfullyFlat_of_hasExpectedAlgebra s t h)
  exact ⟨hfs.1, hfs.2,
    kernelPairComparison_isIso_of_hasExpectedAlgebra s t h⟩

end AlgebraicGeometry.AffineRelationQuotient
