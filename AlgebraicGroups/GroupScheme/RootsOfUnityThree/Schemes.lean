/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.RootsOfUnityThree.Algebra
public import AlgebraicGroups.GroupScheme.RootsOfUnityThree.Quadratic
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# Disjoint-union decompositions of the scheme of cube roots of unity

The coordinate algebra decompositions give isomorphisms of schemes over the
base, not decompositions as group objects. The split coproduct is ordered and
right associated. Over a disconnected base its summands need not be connected;
over the zero ring they need not be nonempty.

The comparison from a coproduct in the over category to a coproduct of schemes
is displayed explicitly. In particular the inverse scheme isomorphism is
`coprodSpec` followed by `Spec` of the forward coordinate algebra equivalence.

## References

* James S. Milne, *Algebraic Groups* (2017), Example 1.6.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Polynomial
open scoped CategoryTheory.MonObj

universe u v

namespace AlgebraicGeometry.RootsOfUnityThree

variable (R : Type u) [CommRing R]

private abbrev specOver (A : Type u) [CommRing A] [Algebra R A] :=
  (algSpec (.of R)).obj (.op (CommAlgCat.of R A))

/-- A copy of the base scheme, regarded as a scheme over itself. -/
abbrev baseScheme : Over (Spec (.of R)) :=
  (algSpec (.of R)).obj (.op (CommAlgCat.of R R))

/-- The quadratic summand, without an assertion that it is a field. -/
abbrev quadraticScheme : Over (Spec (.of R)) :=
  (algSpec (.of R)).obj
    (.op (CommAlgCat.of R (AdjoinRoot (X ^ 2 + X + 1 : R[X]))))

/-- The two-factor disjoint union in the category over the base. -/
abbrev twoFactorScheme : Over (Spec (.of R)) :=
  baseScheme R ⨿ quadraticScheme R

/-- Three ordered, right-associated copies of the base scheme. -/
abbrev splitScheme : Over (Spec (.of R)) :=
  baseScheme R ⨿ (baseScheme R ⨿ baseScheme R)

section CoproductComparison

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- The stock product-spectrum map, lifted to the over category. -/
private def coprodSpecOver : specOver R A ⨿ specOver R B ⟶ specOver R (A × B) :=
  coprod.desc
    ((algSpec (.of R)).map (CommAlgCat.ofHom (AlgHom.fst R A B)).op)
    ((algSpec (.of R)).map (CommAlgCat.ofHom (AlgHom.snd R A B)).op)

-- Lean 4.34 needs this local compatibility setting when identifying the chosen
-- coproducts at the abstract forgetful-functor and concrete spectrum endpoints.
set_option backward.isDefEq.respectTransparency false in
private lemma coprodSpecOver_left :
    (coprodSpecOver R A B).left =
      inv (coprodComparison (Over.forget (Spec (.of R))) (specOver R A) (specOver R B)) ≫
        coprodSpec A B := by
  let c : Spec (.of A) ⨿ Spec (.of B) ⟶ (specOver R A ⨿ specOver R B).left :=
    coprodComparison (Over.forget (Spec (.of R))) (specOver R A) (specOver R B)
  have : IsIso c := inferInstanceAs <|
    IsIso (coprodComparison (Over.forget (Spec (.of R))) (specOver R A) (specOver R B))
  let f : (specOver R A ⨿ specOver R B).left ⟶ Spec (.of (A × B)) :=
    (coprodSpecOver R A B).left
  change f = inv c ≫ coprodSpec A B
  let F := Over.forget (Spec (.of R))
  let p := (algSpec (.of R)).map (CommAlgCat.ofHom (AlgHom.fst R A B)).op
  let q := (algSpec (.of R)).map (CommAlgCat.ofHom (AlgHom.snd R A B)).op
  -- Keep the chosen coproducts in F.obj form until the categorical law is proved.
  have hmap :
      coprodComparison F (specOver R A) (specOver R B) ≫ F.map (coprod.desc p q) =
        coprod.desc (F.map p) (F.map q) := by
    apply coprod.hom_ext
    · simp only [coprodComparison_inl_assoc, ← F.map_comp, coprod.inl_desc]
    · simp only [coprodComparison_inr_assoc, ← F.map_comp, coprod.inr_desc]
  have h : c ≫ f = coprodSpec A B := by
    calc
      c ≫ f = coprod.desc (F.map p) (F.map q) := hmap
      _ = coprodSpec A B := by
        apply coprod.hom_ext
        · rw [coprod.inl_desc, coprodSpec_inl]
          rfl
        · rw [coprod.inr_desc, coprodSpec_inr]
          rfl
  apply (cancel_epi c).1
  simpa only [IsIso.hom_inv_id_assoc] using h

private instance coprodSpecOver_isIso : IsIso (coprodSpecOver R A B) := by
  have : IsIso ((Over.forget (Spec (.of R))).map (coprodSpecOver R A B)) := by
    let c : Spec (.of A) ⨿ Spec (.of B) ⟶ (specOver R A ⨿ specOver R B).left :=
      coprodComparison (Over.forget (Spec (.of R))) (specOver R A) (specOver R B)
    let f : (specOver R A ⨿ specOver R B).left ⟶ Spec (.of (A × B)) :=
      (coprodSpecOver R A B).left
    have : IsIso c := inferInstanceAs <|
      IsIso (coprodComparison (Over.forget (Spec (.of R))) (specOver R A) (specOver R B))
    have h : f = inv c ≫ coprodSpec A B := coprodSpecOver_left R A B
    change IsIso f
    rw [h]
    infer_instance
  exact isIso_of_reflects_iso _ (Over.forget (Spec (.of R)))

end CoproductComparison

section CoordinateComparison

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

private def factorIso (e : rootsOfUnityCoordinateRing R 3 ≃ₐ[R] A × B) :
    rootsOfUnityScheme R 3 ≅ specOver R A ⨿ specOver R B :=
  ((algSpec (.of R)).mapIso (CommAlgCat.isoMk e).op).symm ≪≫
    (asIso (coprodSpecOver R A B)).symm

private lemma factorIso_inv_left (e : rootsOfUnityCoordinateRing R 3 ≃ₐ[R] A × B) :
    (factorIso R e).inv.left =
      inv (coprodComparison (Over.forget (Spec (.of R))) (specOver R A) (specOver R B)) ≫
        coprodSpec A B ≫ Spec.map (CommRingCat.ofHom e.toAlgHom.toRingHom) := by
  let c : Spec (.of A) ⨿ Spec (.of B) ⟶ (specOver R A ⨿ specOver R B).left :=
    coprodComparison (Over.forget (Spec (.of R))) (specOver R A) (specOver R B)
  let : IsIso c := inferInstanceAs <|
    IsIso (coprodComparison (Over.forget (Spec (.of R))) (specOver R A) (specOver R B))
  let s : Spec (.of (A × B)) ⟶ Spec (.of (rootsOfUnityCoordinateRing R 3)) :=
    Spec.map (CommRingCat.ofHom e.toAlgHom.toRingHom)
  let f : (specOver R A ⨿ specOver R B).left ⟶ Spec (.of (A × B)) :=
    (coprodSpecOver R A B).left
  change f ≫ s = inv c ≫ coprodSpec A B ≫ s
  have h : f = inv c ≫ coprodSpec A B := coprodSpecOver_left R A B
  exact (congrArg
    (fun f : (specOver R A ⨿ specOver R B).left ⟶ Spec (.of (A × B)) ↦ f ≫ s) h).trans
      (Category.assoc (inv c) (coprodSpec A B) s)

private lemma factorIso_inl (e : rootsOfUnityCoordinateRing R 3 ≃ₐ[R] A × B) :
    (coprod.inl ≫ (factorIso R e).inv).left =
      Spec.map (CommRingCat.ofHom ((AlgHom.fst R A B).comp e.toAlgHom).toRingHom) := by
  change (coprod.inl ≫ coprodSpecOver R A B ≫
    (algSpec (.of R)).map (CommAlgCat.ofHom e.toAlgHom).op).left = _
  rw [← Category.assoc, coprodSpecOver, coprod.inl_desc]
  change Spec.map (CommRingCat.ofHom (RingHom.fst A B)) ≫
    Spec.map (CommRingCat.ofHom e.toAlgHom.toRingHom) = _
  rw [← Spec.map_comp]
  rfl

private lemma factorIso_inr (e : rootsOfUnityCoordinateRing R 3 ≃ₐ[R] A × B) :
    (coprod.inr ≫ (factorIso R e).inv).left =
      Spec.map (CommRingCat.ofHom ((AlgHom.snd R A B).comp e.toAlgHom).toRingHom) := by
  change (coprod.inr ≫ coprodSpecOver R A B ≫
    (algSpec (.of R)).map (CommAlgCat.ofHom e.toAlgHom).op).left = _
  rw [← Category.assoc, coprodSpecOver, coprod.inr_desc]
  change Spec.map (CommRingCat.ofHom (RingHom.snd A B)) ≫
    Spec.map (CommRingCat.ofHom e.toAlgHom.toRingHom) = _
  rw [← Spec.map_comp]
  rfl

end CoordinateComparison

/-- The two-factor decomposition of the existing scheme of cube roots of unity. -/
def twoFactorSchemeIso (h3 : IsUnit (3 : R)) :
    rootsOfUnityScheme R 3 ≅ twoFactorScheme R :=
  let f := coprod.desc
    ((algSpec (.of R)).map (CommAlgCat.ofHom
      (AlgHom.fst R R (AdjoinRoot (X ^ 2 + X + 1 : R[X])))).op)
    ((algSpec (.of R)).map (CommAlgCat.ofHom
      (AlgHom.snd R R (AdjoinRoot (X ^ 2 + X + 1 : R[X])))).op)
  letI : IsIso f := by exact coprodSpecOver_isIso R R _
  ((algSpec (.of R)).mapIso
    (CommAlgCat.isoMk (coordinateTwoFactorAlgEquiv R h3)).op).symm ≪≫ (asIso f).symm

/-- The forward map commutes with the structure maps to the base. -/
lemma twoFactorSchemeIso_hom_base (h3 : IsUnit (3 : R)) :
    (twoFactorSchemeIso R h3).hom.left ≫ (twoFactorScheme R).hom =
      (rootsOfUnityScheme R 3).hom :=
  (twoFactorSchemeIso R h3).hom.w

/-- The inverse map commutes with the structure maps to the base. -/
lemma twoFactorSchemeIso_inv_base (h3 : IsUnit (3 : R)) :
    (twoFactorSchemeIso R h3).inv.left ≫ (rootsOfUnityScheme R 3).hom =
      (twoFactorScheme R).hom :=
  (twoFactorSchemeIso R h3).inv.w

/-- Contravariance: the inverse uses the forward coordinate equivalence. -/
lemma twoFactorSchemeIso_inv_left (h3 : IsUnit (3 : R)) :
    (twoFactorSchemeIso R h3).inv.left =
      inv (coprodComparison (Over.forget (Spec (.of R)))
        (baseScheme R) (quadraticScheme R)) ≫
      coprodSpec R (AdjoinRoot (X ^ 2 + X + 1 : R[X])) ≫
      Spec.map (CommRingCat.ofHom (coordinateTwoFactorAlgEquiv R h3).toAlgHom.toRingHom) :=
  factorIso_inv_left R _

/-- The first component is the spectrum of the first projection after the
coordinate equivalence. -/
lemma twoFactorSchemeIso_inl (h3 : IsUnit (3 : R)) :
    (coprod.inl ≫ (twoFactorSchemeIso R h3).inv).left =
      Spec.map (CommRingCat.ofHom
        ((AlgHom.fst R R (AdjoinRoot (X ^ 2 + X + 1 : R[X]))).comp
          (coordinateTwoFactorAlgEquiv R h3).toAlgHom).toRingHom) :=
  factorIso_inl R _

/-- The quadratic component is the spectrum of the second projection. -/
lemma twoFactorSchemeIso_inr (h3 : IsUnit (3 : R)) :
    (coprod.inr ≫ (twoFactorSchemeIso R h3).inv).left =
      Spec.map (CommRingCat.ofHom
        ((AlgHom.snd R R (AdjoinRoot (X ^ 2 + X + 1 : R[X]))).comp
          (coordinateTwoFactorAlgEquiv R h3).toAlgHom).toRingHom) :=
  factorIso_inr R _

/-- The first component has its canonical base map. -/
lemma twoFactorSchemeIso_inl_base (h3 : IsUnit (3 : R)) :
    (coprod.inl ≫ (twoFactorSchemeIso R h3).inv).left ≫
      (rootsOfUnityScheme R 3).hom = (baseScheme R).hom :=
  (coprod.inl ≫ (twoFactorSchemeIso R h3).inv).w

/-- The quadratic component has its canonical base map. -/
lemma twoFactorSchemeIso_inr_base (h3 : IsUnit (3 : R)) :
    (coprod.inr ≫ (twoFactorSchemeIso R h3).inv).left ≫
      (rootsOfUnityScheme R 3).hom = (quadraticScheme R).hom :=
  (coprod.inr ≫ (twoFactorSchemeIso R h3).inv).w

/-- The two pullbacks evaluate the coordinate at `1` and at the quadratic root. -/
lemma twoFactorSchemeIso_component_coordinates (h3 : IsUnit (3 : R)) :
    ((coordinateTwoFactorAlgEquiv R h3 (rootsOfUnityCoordinateGenerator R 3)).1 = 1) ∧
    ((coordinateTwoFactorAlgEquiv R h3 (rootsOfUnityCoordinateGenerator R 3)).2 =
      AdjoinRoot.root (X ^ 2 + X + 1 : R[X])) := by
  simp

/-- Scalars pull back by the canonical scalar maps on both summands. -/
lemma twoFactorSchemeIso_component_scalars (h3 : IsUnit (3 : R)) (a : R) :
    coordinateTwoFactorAlgEquiv R h3 (algebraMap R (rootsOfUnityCoordinateRing R 3) a) =
      (a, algebraMap R (AdjoinRoot (X ^ 2 + X + 1 : R[X])) a) :=
  coordinateTwoFactorAlgEquiv_algebraMap R h3 a

/-- The iterated product-spectrum comparison, in the over category. -/
def splitCoprodSpec : splitScheme R ⟶
    (algSpec (.of R)).obj (.op (CommAlgCat.of R (R × (R × R)))) :=
  coprod.map (𝟙 (baseScheme R))
    (coprod.desc
      ((algSpec (.of R)).map (CommAlgCat.ofHom (AlgHom.fst R R R)).op)
      ((algSpec (.of R)).map (CommAlgCat.ofHom (AlgHom.snd R R R)).op)) ≫
    coprod.desc
      ((algSpec (.of R)).map (CommAlgCat.ofHom (AlgHom.fst R R (R × R))).op)
      ((algSpec (.of R)).map (CommAlgCat.ofHom (AlgHom.snd R R (R × R))).op)

/-- The canonical iterated product-spectrum comparison is an isomorphism. -/
instance splitCoprodSpec_isIso : IsIso (splitCoprodSpec R) := by
  change IsIso (coprod.map (𝟙 (baseScheme R)) (coprodSpecOver R R R) ≫
    coprodSpecOver R R (R × R))
  infer_instance

-- The final endpoint identification crosses the same chosen-coproduct boundary
-- as coprodSpecOver_left; this setting is confined to this proof declaration.
set_option backward.isDefEq.respectTransparency false in
/-- The three-summand comparison consists of the two stock `coprodSpec` maps,
with the canonical forgetful comparisons made explicit. -/
lemma splitCoprodSpec_left :
    (splitCoprodSpec R).left =
      inv (coprodComparison (Over.forget (Spec (.of R)))
        (baseScheme R) (baseScheme R ⨿ baseScheme R)) ≫
      coprod.map (𝟙 (Spec (.of R)))
        (inv (coprodComparison (Over.forget (Spec (.of R))) (baseScheme R) (baseScheme R)) ≫
          coprodSpec R R) ≫ coprodSpec R (R × R) := by
  let F := Over.forget (Spec (.of R))
  let c : Spec (.of R) ⨿ (baseScheme R ⨿ baseScheme R).left ⟶
      (splitScheme R).left :=
    coprodComparison F (baseScheme R) (baseScheme R ⨿ baseScheme R)
  let d : Spec (.of R) ⨿ Spec (.of (R × R)) ⟶
      (specOver R R ⨿ specOver R (R × R)).left :=
    coprodComparison F (specOver R R) (specOver R (R × R))
  let b : Spec (.of R) ⨿ Spec (.of R) ⟶ (baseScheme R ⨿ baseScheme R).left :=
    coprodComparison F (baseScheme R) (baseScheme R)
  let : IsIso c := inferInstanceAs <|
    IsIso (coprodComparison (Over.forget (Spec (.of R)))
      (baseScheme R) (baseScheme R ⨿ baseScheme R))
  let : IsIso d := inferInstanceAs <|
    IsIso (coprodComparison (Over.forget (Spec (.of R)))
      (specOver R R) (specOver R (R × R)))
  let : IsIso b := inferInstanceAs <|
    IsIso (coprodComparison (Over.forget (Spec (.of R))) (baseScheme R) (baseScheme R))
  let s : (baseScheme R ⨿ baseScheme R).left ⟶ Spec (.of (R × R)) :=
    (coprodSpecOver R R R).left
  let t : (specOver R R ⨿ specOver R (R × R)).left ⟶ Spec (.of (R × (R × R))) :=
    (coprodSpecOver R R (R × R)).left
  let f : (splitScheme R).left ⟶ (specOver R R ⨿ specOver R (R × R)).left :=
    F.map (coprod.map (𝟙 (baseScheme R)) (coprodSpecOver R R R))
  have hs : s = inv b ≫ coprodSpec R R := coprodSpecOver_left R R R
  have ht : t = inv d ≫ coprodSpec R (R × R) := coprodSpecOver_left R R (R × R)
  -- Normalize at arbitrary Over objects before specializing to concrete spectra.
  have hnOver (X Y Z : Over (Spec (.of R))) (g : Y ⟶ Z) :
      inv (coprodComparison F X Y) ≫ coprod.map (𝟙 (F.obj X)) (F.map g) =
        F.map (coprod.map (𝟙 X) g) ≫ inv (coprodComparison F X Z) := by
    exact
      (congrArg
        (fun u : F.obj X ⟶ F.obj X =>
          inv (coprodComparison F X Y) ≫ coprod.map u (F.map g))
        (F.map_id X)).symm.trans
        (coprodComparison_inv_natural (F := F) (𝟙 X) g)
  have hn : inv c ≫ coprod.map (𝟙 (Spec (.of R))) s = f ≫ inv d :=
    hnOver (baseScheme R) (baseScheme R ⨿ baseScheme R) (specOver R (R × R))
      (coprodSpecOver R R R)
  change f ≫ t = inv c ≫ coprod.map (𝟙 (Spec (.of R)))
    (inv b ≫ coprodSpec R R) ≫ coprodSpec R (R × R)
  calc
    f ≫ t = f ≫ (inv d ≫ coprodSpec R (R × R)) :=
      congrArg (fun g : (specOver R R ⨿ specOver R (R × R)).left ⟶
        Spec (.of (R × (R × R))) ↦ f ≫ g) ht
    _ = (f ≫ inv d) ≫ coprodSpec R (R × R) := (Category.assoc _ _ _).symm
    _ = (inv c ≫ coprod.map (𝟙 (Spec (.of R))) s) ≫ coprodSpec R (R × R) :=
      congrArg (fun g : (splitScheme R).left ⟶ Spec (.of R) ⨿ Spec (.of (R × R)) ↦
        g ≫ coprodSpec R (R × R)) hn.symm
    _ = (inv c ≫ coprod.map (𝟙 (Spec (.of R))) (inv b ≫ coprodSpec R R)) ≫
        coprodSpec R (R × R) :=
      congrArg
        (fun g : (baseScheme R ⨿ baseScheme R).left ⟶ Spec (.of (R × R)) ↦
          (inv c ≫ coprod.map (𝟙 (Spec (.of R))) g) ≫ coprodSpec R (R × R)) hs
    _ = _ := Category.assoc _ _ _

/-- The split decomposition over a ring with 3 invertible and a root of the
quadratic factor. No nontriviality or connectedness hypothesis is needed. -/
def splitSchemeIsoOfQuadraticRoot (h3 : IsUnit (3 : R)) (ζ : R)
    (hq : (X ^ 2 + X + 1 : R[X]).eval ζ = 0) :
    rootsOfUnityScheme R 3 ≅ splitScheme R :=
  letI : IsIso (splitCoprodSpec R) := splitCoprodSpec_isIso R
  ((algSpec (.of R)).mapIso
    (CommAlgCat.isoMk (coordinateSplitAlgEquivOfQuadraticRoot R h3 ζ hq)).op).symm ≪≫
      (asIso (splitCoprodSpec R)).symm

lemma splitSchemeIsoOfQuadraticRoot_hom_base (h3 : IsUnit (3 : R)) (ζ : R)
    (hq : (X ^ 2 + X + 1 : R[X]).eval ζ = 0) :
    (splitSchemeIsoOfQuadraticRoot R h3 ζ hq).hom.left ≫ (splitScheme R).hom =
      (rootsOfUnityScheme R 3).hom :=
  (splitSchemeIsoOfQuadraticRoot R h3 ζ hq).hom.w

lemma splitSchemeIsoOfQuadraticRoot_inv_base (h3 : IsUnit (3 : R)) (ζ : R)
    (hq : (X ^ 2 + X + 1 : R[X]).eval ζ = 0) :
    (splitSchemeIsoOfQuadraticRoot R h3 ζ hq).inv.left ≫ (rootsOfUnityScheme R 3).hom =
      (splitScheme R).hom :=
  (splitSchemeIsoOfQuadraticRoot R h3 ζ hq).inv.w

/-- The inverse split isomorphism is iterated `coprodSpec` followed by the
spectrum of the forward coordinate equivalence. -/
lemma splitSchemeIsoOfQuadraticRoot_inv_left (h3 : IsUnit (3 : R)) (ζ : R)
    (hq : (X ^ 2 + X + 1 : R[X]).eval ζ = 0) :
    (splitSchemeIsoOfQuadraticRoot R h3 ζ hq).inv.left =
      (splitCoprodSpec R).left ≫ Spec.map (CommRingCat.ofHom
        (coordinateSplitAlgEquivOfQuadraticRoot R h3 ζ hq).toAlgHom.toRingHom) := by
  rfl

/-- The ordered component pullbacks, bundled as algebra homomorphisms. -/
def splitComponentZero (h3 : IsUnit (3 : R)) (ζ : R)
    (hq : (X ^ 2 + X + 1 : R[X]).eval ζ = 0) :
    rootsOfUnityCoordinateRing R 3 →ₐ[R] R :=
  (AlgHom.fst R R (R × R)).comp
    (coordinateSplitAlgEquivOfQuadraticRoot R h3 ζ hq).toAlgHom

/-- The pullback from the middle ordered summand, evaluating the coordinate at `ζ`. -/
def splitComponentOne (h3 : IsUnit (3 : R)) (ζ : R)
    (hq : (X ^ 2 + X + 1 : R[X]).eval ζ = 0) :
    rootsOfUnityCoordinateRing R 3 →ₐ[R] R :=
  (AlgHom.fst R R R).comp ((AlgHom.snd R R (R × R)).comp
    (coordinateSplitAlgEquivOfQuadraticRoot R h3 ζ hq).toAlgHom)

/-- The pullback from the last ordered summand, evaluating the coordinate at `ζ²`. -/
def splitComponentTwo (h3 : IsUnit (3 : R)) (ζ : R)
    (hq : (X ^ 2 + X + 1 : R[X]).eval ζ = 0) :
    rootsOfUnityCoordinateRing R 3 →ₐ[R] R :=
  (AlgHom.snd R R R).comp ((AlgHom.snd R R (R × R)).comp
    (coordinateSplitAlgEquivOfQuadraticRoot R h3 ζ hq).toAlgHom)

private lemma splitCoprodSpec_map_components
    {C : Type u} [CommRing C] [Algebra R C] (φ : C →ₐ[R] R × (R × R)) :
    coprod.inl ≫ splitCoprodSpec R ≫
        (algSpec (.of R)).map (CommAlgCat.ofHom φ).op =
      (algSpec (.of R)).map (CommAlgCat.ofHom ((AlgHom.fst R R (R × R)).comp φ)).op ∧
    coprod.inl ≫ coprod.inr ≫ splitCoprodSpec R ≫
        (algSpec (.of R)).map (CommAlgCat.ofHom φ).op =
      (algSpec (.of R)).map (CommAlgCat.ofHom
        ((AlgHom.fst R R R).comp ((AlgHom.snd R R (R × R)).comp φ))).op ∧
    coprod.inr ≫ coprod.inr ≫ splitCoprodSpec R ≫
        (algSpec (.of R)).map (CommAlgCat.ofHom φ).op =
      (algSpec (.of R)).map (CommAlgCat.ofHom
        ((AlgHom.snd R R R).comp ((AlgHom.snd R R (R × R)).comp φ))).op := by
  have hmap (π : R × R →ₐ[R] R) :
      (algSpec (.of R)).map (CommAlgCat.ofHom π).op ≫
          (algSpec (.of R)).map (CommAlgCat.ofHom (AlgHom.snd R R (R × R))).op ≫
          (algSpec (.of R)).map (CommAlgCat.ofHom φ).op =
        (algSpec (.of R)).map
          (CommAlgCat.ofHom (π.comp ((AlgHom.snd R R (R × R)).comp φ))).op := by
    calc
      _ = (algSpec (.of R)).map (CommAlgCat.ofHom π).op ≫
          (algSpec (.of R)).map
            ((CommAlgCat.ofHom (AlgHom.snd R R (R × R))).op ≫
              (CommAlgCat.ofHom φ).op) :=
        congrArg
          (fun g : specOver R (R × R) ⟶ specOver R C ↦
            (algSpec (.of R)).map (CommAlgCat.ofHom π).op ≫ g)
          (Functor.map_comp (algSpec (.of R))
            (CommAlgCat.ofHom (AlgHom.snd R R (R × R))).op
            (CommAlgCat.ofHom φ).op).symm
      _ = (algSpec (.of R)).map
          ((CommAlgCat.ofHom π).op ≫
            (CommAlgCat.ofHom (AlgHom.snd R R (R × R))).op ≫
            (CommAlgCat.ofHom φ).op) :=
        (Functor.map_comp (algSpec (.of R)) _ _).symm
      _ = _ := rfl
  have h0 :
      (coprod.inl : baseScheme R ⟶ splitScheme R) ≫ splitCoprodSpec R ≫
          (algSpec (.of R)).map (CommAlgCat.ofHom φ).op =
        (algSpec (.of R)).map
          (CommAlgCat.ofHom ((AlgHom.fst R R (R × R)).comp φ)).op := by
    calc
      _ = (algSpec (.of R)).map (CommAlgCat.ofHom (AlgHom.fst R R (R × R))).op ≫
          (algSpec (.of R)).map (CommAlgCat.ofHom φ).op := by
        simp only [splitCoprodSpec, Category.assoc, coprod.inl_map_assoc,
          Category.id_comp, coprod.inl_desc_assoc]
      _ = (algSpec (.of R)).map
          ((CommAlgCat.ofHom (AlgHom.fst R R (R × R))).op ≫
            (CommAlgCat.ofHom φ).op) :=
        (Functor.map_comp (algSpec (.of R)) _ _).symm
      _ = _ := rfl
  have h1 :
      (coprod.inl : baseScheme R ⟶ baseScheme R ⨿ baseScheme R) ≫ coprod.inr ≫
          splitCoprodSpec R ≫ (algSpec (.of R)).map (CommAlgCat.ofHom φ).op =
        (algSpec (.of R)).map (CommAlgCat.ofHom
          ((AlgHom.fst R R R).comp ((AlgHom.snd R R (R × R)).comp φ))).op := by
    calc
      _ = (algSpec (.of R)).map (CommAlgCat.ofHom (AlgHom.fst R R R)).op ≫
          (algSpec (.of R)).map (CommAlgCat.ofHom (AlgHom.snd R R (R × R))).op ≫
          (algSpec (.of R)).map (CommAlgCat.ofHom φ).op := by
        simp only [splitCoprodSpec, Category.assoc, coprod.inr_map_assoc,
          coprod.inr_desc_assoc, coprod.inl_desc_assoc]
      _ = _ := hmap (AlgHom.fst R R R)
  have h2 :
      (coprod.inr : baseScheme R ⟶ baseScheme R ⨿ baseScheme R) ≫ coprod.inr ≫
          splitCoprodSpec R ≫ (algSpec (.of R)).map (CommAlgCat.ofHom φ).op =
        (algSpec (.of R)).map (CommAlgCat.ofHom
          ((AlgHom.snd R R R).comp ((AlgHom.snd R R (R × R)).comp φ))).op := by
    calc
      _ = (algSpec (.of R)).map (CommAlgCat.ofHom (AlgHom.snd R R R)).op ≫
          (algSpec (.of R)).map (CommAlgCat.ofHom (AlgHom.snd R R (R × R))).op ≫
          (algSpec (.of R)).map (CommAlgCat.ofHom φ).op := by
        simp only [splitCoprodSpec, Category.assoc, coprod.inr_map_assoc,
          coprod.inr_desc_assoc]
      _ = _ := hmap (AlgHom.snd R R R)
  exact ⟨h0, h1, h2⟩

-- Only this specialization crosses from Over coproducts to concrete spectra;
-- allow the ordinary Lean 4.34 endpoint conversion, not a global option change.
set_option backward.isDefEq.respectTransparency false in
/-- Each inclusion followed by the inverse split isomorphism is `Spec` of
projection after the forward coordinate equivalence, in the order `1,ζ,ζ²`. -/
lemma splitSchemeIsoOfQuadraticRoot_components (h3 : IsUnit (3 : R)) (ζ : R)
    (hq : (X ^ 2 + X + 1 : R[X]).eval ζ = 0) :
    (coprod.inl ≫ (splitSchemeIsoOfQuadraticRoot R h3 ζ hq).inv).left =
      Spec.map (CommRingCat.ofHom (splitComponentZero R h3 ζ hq).toRingHom) ∧
    (coprod.inl ≫ coprod.inr ≫ (splitSchemeIsoOfQuadraticRoot R h3 ζ hq).inv).left =
      Spec.map (CommRingCat.ofHom (splitComponentOne R h3 ζ hq).toRingHom) ∧
    (coprod.inr ≫ coprod.inr ≫ (splitSchemeIsoOfQuadraticRoot R h3 ζ hq).inv).left =
      Spec.map (CommRingCat.ofHom (splitComponentTwo R h3 ζ hq).toRingHom) := by
  let φ : rootsOfUnityCoordinateRing R 3 →ₐ[R] R × (R × R) :=
    (coordinateSplitAlgEquivOfQuadraticRoot R h3 ζ hq).toAlgHom
  obtain ⟨h0, h1, h2⟩ := splitCoprodSpec_map_components R φ
  -- Specialize the typed Over equalities first; forget only the settled maps.
  refine ⟨?_, ?_, ?_⟩
  · exact (congrArg
      (fun f : baseScheme R ⟶ rootsOfUnityScheme R 3 ↦ f.left) h0).trans (by rfl)
  · exact (congrArg
      (fun f : baseScheme R ⟶ rootsOfUnityScheme R 3 ↦ f.left) h1).trans (by rfl)
  · exact (congrArg
      (fun f : baseScheme R ⟶ rootsOfUnityScheme R 3 ↦ f.left) h2).trans (by rfl)

/-- The first component is evaluation at one, as an equality of algebra maps. -/
lemma splitComponentZero_eq (h3 : IsUnit (3 : R)) (ζ : R)
    (hq : (X ^ 2 + X + 1 : R[X]).eval ζ = 0) :
    splitComponentZero R h3 ζ hq =
      (evalOne R).comp (rootsOfUnityCoordinateAlgEquiv R 3).toAlgHom :=
  coordinateSplitAlgEquivOfQuadraticRoot_fst R h3 ζ hq

/-- The second component is evaluation at the specified quadratic root. -/
lemma splitComponentOne_eq (h3 : IsUnit (3 : R)) (ζ : R)
    (hq : (X ^ 2 + X + 1 : R[X]).eval ζ = 0) :
    splitComponentOne R h3 ζ hq =
      (evalCubeRoot R ζ (quadraticRoot_cube R ζ hq)).comp
        (rootsOfUnityCoordinateAlgEquiv R 3).toAlgHom :=
  coordinateSplitAlgEquivOfQuadraticRoot_snd_fst R h3 ζ hq

/-- The third component is evaluation at the square of the specified root. -/
lemma splitComponentTwo_eq (h3 : IsUnit (3 : R)) (ζ : R)
    (hq : (X ^ 2 + X + 1 : R[X]).eval ζ = 0) :
    splitComponentTwo R h3 ζ hq =
      (evalCubeRoot R (ζ ^ 2) (quadraticRoot_sq_cube R ζ hq)).comp
        (rootsOfUnityCoordinateAlgEquiv R 3).toAlgHom :=
  coordinateSplitAlgEquivOfQuadraticRoot_snd_snd R h3 ζ hq

/-- On polynomial classes, the three pullbacks are the ordered evaluations. -/
lemma splitComponent_polynomial (h3 : IsUnit (3 : R)) (ζ : R)
    (hq : (X ^ 2 + X + 1 : R[X]).eval ζ = 0) (p : R[X]) :
    let c := (rootsOfUnityCoordinateAlgEquiv R 3).symm (AdjoinRoot.mk _ p)
    (splitComponentZero R h3 ζ hq c, (splitComponentOne R h3 ζ hq c,
      splitComponentTwo R h3 ζ hq c)) = (p.eval 1, (p.eval ζ, p.eval (ζ ^ 2))) := by
  simp [splitComponentZero, splitComponentOne, splitComponentTwo]

/-- The component coordinates are precisely the ordered roots. -/
lemma splitComponent_generator (h3 : IsUnit (3 : R)) (ζ : R)
    (hq : (X ^ 2 + X + 1 : R[X]).eval ζ = 0) :
    let c := rootsOfUnityCoordinateGenerator R 3
    (splitComponentZero R h3 ζ hq c, (splitComponentOne R h3 ζ hq c,
      splitComponentTwo R h3 ζ hq c)) = (1, (ζ, ζ ^ 2)) := by
  simp [splitComponentZero, splitComponentOne, splitComponentTwo]

/-- Each component fixes the base scalars. -/
lemma splitComponent_algebraMap (h3 : IsUnit (3 : R)) (ζ : R)
    (hq : (X ^ 2 + X + 1 : R[X]).eval ζ = 0) (a : R) :
    let c := algebraMap R (rootsOfUnityCoordinateRing R 3) a
    (splitComponentZero R h3 ζ hq c, (splitComponentOne R h3 ζ hq c,
      splitComponentTwo R h3 ζ hq c)) = (a, (a, a)) := by
  exact Prod.ext
    (by simpa only [Algebra.algebraMap_self_apply] using
      (splitComponentZero R h3 ζ hq).commutes a)
    (Prod.ext
      (by simpa only [Algebra.algebraMap_self_apply] using
        (splitComponentOne R h3 ζ hq).commutes a)
      (by simpa only [Algebra.algebraMap_self_apply] using
        (splitComponentTwo R h3 ζ hq).commutes a))

/-- All three inclusions commute with the base maps. -/
lemma splitSchemeIsoOfQuadraticRoot_components_base (h3 : IsUnit (3 : R)) (ζ : R)
    (hq : (X ^ 2 + X + 1 : R[X]).eval ζ = 0) :
    (coprod.inl ≫ (splitSchemeIsoOfQuadraticRoot R h3 ζ hq).inv).left ≫
        (rootsOfUnityScheme R 3).hom = (baseScheme R).hom ∧
    (coprod.inl ≫ coprod.inr ≫ (splitSchemeIsoOfQuadraticRoot R h3 ζ hq).inv).left ≫
        (rootsOfUnityScheme R 3).hom = (baseScheme R).hom ∧
    (coprod.inr ≫ coprod.inr ≫ (splitSchemeIsoOfQuadraticRoot R h3 ζ hq).inv).left ≫
        (rootsOfUnityScheme R 3).hom = (baseScheme R).hom :=
  ⟨(coprod.inl ≫ (splitSchemeIsoOfQuadraticRoot R h3 ζ hq).inv).w,
    (coprod.inl ≫ coprod.inr ≫ (splitSchemeIsoOfQuadraticRoot R h3 ζ hq).inv).w,
    (coprod.inr ≫ coprod.inr ≫ (splitSchemeIsoOfQuadraticRoot R h3 ζ hq).inv).w⟩

section Points

variable {R} (A : Type u) [CommRing A] [Algebra R A]

/-- The affine evaluation map agrees with the existing roots-of-unity point
representation, with the root recovered by its algebra-map equivalence. -/
lemma coordinatePoint_eq (φ : rootsOfUnityCoordinateRing R 3 →ₐ[R] A) :
    (algSpec (.of R)).map (CommAlgCat.ofHom φ).op =
      rootsOfUnityMulEquivPoints R A 3
        ((rootsOfUnityMulEquivAlgHom R A 3).symm (WithConv.toConv φ)) := by
  simp only [rootsOfUnityMulEquivPoints, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]; rfl

/-- The same affine evaluation, stated directly through the natural
isomorphism of the existing roots-of-unity and scheme-point functors. -/
lemma coordinatePoint_eq_pointsIso (φ : rootsOfUnityCoordinateRing R 3 →ₐ[R] A) :
    (CategoryTheory.ConcreteCategory.hom
      ((rootsOfUnityPointsIso R 3).hom.app (CommAlgCat.of R A)) :
        rootsOfUnity 3 A →*
          ((Spec (.of A)).asOver (Spec (.of R)) ⟶ rootsOfUnityScheme R 3))
      ((rootsOfUnityMulEquivAlgHom R A 3).symm (WithConv.toConv φ)) =
        (algSpec (.of R)).map (CommAlgCat.ofHom φ).op := by
  rw [rootsOfUnityPointsIso_hom_app_apply]
  exact (coordinatePoint_eq A φ).symm

/-- A component with the stated spectrum map is the corresponding point of
the existing roots-of-unity representation. -/
lemma coordinatePoint_of_left (φ : rootsOfUnityCoordinateRing R 3 →ₐ[R] A)
    (p : (Spec (.of A)).asOver (Spec (.of R)) ⟶ rootsOfUnityScheme R 3)
    (h : p.left = Spec.map (CommRingCat.ofHom φ.toRingHom)) :
    p = rootsOfUnityMulEquivPoints R A 3
      ((rootsOfUnityMulEquivAlgHom R A 3).symm (WithConv.toConv φ)) := by
  have hp : p = (algSpec (.of R)).map (CommAlgCat.ofHom φ).op := by
    ext : 1
    exact h
  exact hp.trans (coordinatePoint_eq A φ)

/-- The root recovered from a component is its pullback of the coordinate. -/
lemma coordinatePoint_root (φ : rootsOfUnityCoordinateRing R 3 →ₐ[R] A) :
    (((rootsOfUnityMulEquivAlgHom R A 3).symm (WithConv.toConv φ) : Aˣ) : A) =
      φ (rootsOfUnityCoordinateGenerator R 3) := by
  let ζ := (rootsOfUnityMulEquivAlgHom R A 3).symm (WithConv.toConv φ)
  have h : (rootsOfUnityMulEquivAlgHom R A 3 ζ).ofConv = φ :=
    congrArg WithConv.ofConv ((rootsOfUnityMulEquivAlgHom R A 3).apply_symm_apply
      (WithConv.toConv φ))
  have hgen := rootsOfUnityMulEquivAlgHom_generator R A 3 ζ
  rw [← rootsOfUnityMulEquivAlgHom_apply R A 3 ζ, h] at hgen
  exact hgen.symm

/-- Evaluation is natural on affine test-algebra maps. -/
lemma coordinatePoint_naturality {B : Type u} [CommRing B] [Algebra R B]
    (φ : rootsOfUnityCoordinateRing R 3 →ₐ[R] A) (f : A →ₐ[R] B) :
    (algSpec (.of R)).map (CommAlgCat.ofHom f).op ≫
      (algSpec (.of R)).map (CommAlgCat.ofHom φ).op =
        (algSpec (.of R)).map (CommAlgCat.ofHom (f.comp φ)).op := by
  rw [← Functor.map_comp]; rfl

end Points

/-- The split component morphisms agree with the existing represented
points, rather than a new notion of roots-of-unity points. -/
lemma splitSchemeIsoOfQuadraticRoot_component_points (h3 : IsUnit (3 : R)) (ζ : R)
    (hq : (X ^ 2 + X + 1 : R[X]).eval ζ = 0) :
    coprod.inl ≫ (splitSchemeIsoOfQuadraticRoot R h3 ζ hq).inv =
      rootsOfUnityMulEquivPoints R R 3 ((rootsOfUnityMulEquivAlgHom R R 3).symm
        (WithConv.toConv (splitComponentZero R h3 ζ hq))) ∧
    coprod.inl ≫ coprod.inr ≫ (splitSchemeIsoOfQuadraticRoot R h3 ζ hq).inv =
      rootsOfUnityMulEquivPoints R R 3 ((rootsOfUnityMulEquivAlgHom R R 3).symm
        (WithConv.toConv (splitComponentOne R h3 ζ hq))) ∧
    coprod.inr ≫ coprod.inr ≫ (splitSchemeIsoOfQuadraticRoot R h3 ζ hq).inv =
      rootsOfUnityMulEquivPoints R R 3 ((rootsOfUnityMulEquivAlgHom R R 3).symm
        (WithConv.toConv (splitComponentTwo R h3 ζ hq))) := by
  have h := splitSchemeIsoOfQuadraticRoot_components R h3 ζ hq
  exact ⟨coordinatePoint_of_left R _ _ h.1,
    coordinatePoint_of_left R _ _ h.2.1, coordinatePoint_of_left R _ _ h.2.2⟩

/-- Under the point equivalence those three points are exactly the
ordered roots `1,ζ,ζ²`, read in the underlying ring. -/
lemma splitComponent_point_roots (h3 : IsUnit (3 : R)) (ζ : R)
    (hq : (X ^ 2 + X + 1 : R[X]).eval ζ = 0) :
    let ρ := fun φ : rootsOfUnityCoordinateRing R 3 →ₐ[R] R ↦
      (((rootsOfUnityMulEquivAlgHom R R 3).symm (WithConv.toConv φ) : Rˣ) : R)
    (ρ (splitComponentZero R h3 ζ hq),
      (ρ (splitComponentOne R h3 ζ hq), ρ (splitComponentTwo R h3 ζ hq))) =
        (1, (ζ, ζ ^ 2)) := by
  dsimp only
  rw [coordinatePoint_root, coordinatePoint_root, coordinatePoint_root]
  exact splitComponent_generator R h3 ζ hq

section Fields

variable (k : Type u) [Field k]

/-- A primitive cube root gives the split isomorphism without an additional
characteristic or quadratic-root hypothesis. -/
def splitSchemeIso (ζ : k) (hζ : IsPrimitiveRoot ζ 3) :
    rootsOfUnityScheme k 3 ≅ splitScheme k :=
  splitSchemeIsoOfQuadraticRoot k (primitiveRoot_three_isUnit k ζ hζ) ζ
    (primitiveRoot_quadratic_eval k ζ hζ)

/-- The algebraically closed characteristic-not-three specialization, retaining
the chosen root used for the ordered evaluation readbacks. -/
def splitSchemeIsoOfIsAlgClosed [IsAlgClosed k] (h3 : (3 : k) ≠ 0) :
    rootsOfUnityScheme k 3 ≅ splitScheme k :=
  splitSchemeIso k (algebraicallyClosedCubeRoot k h3)
    (algebraicallyClosedCubeRoot_isPrimitive k h3)

variable (L : Type u) [CommRing L] [IsDomain L] [Algebra k L]

/-- The chosen-subalgebra disjoint union, over the base field. -/
def adjoinSchemeIso (hnosplit : ¬ ∃ a : k, IsPrimitiveRoot a 3)
    (ζ : L) (hζ : IsPrimitiveRoot ζ 3) :
    rootsOfUnityScheme k 3 ≅ baseScheme k ⨿
      (algSpec (.of k)).obj (.op (CommAlgCat.of k (Algebra.adjoin k ({ζ} : Set L)))) :=
  let A := Algebra.adjoin k ({ζ} : Set L)
  let f := coprod.desc
    ((algSpec (.of k)).map (CommAlgCat.ofHom (AlgHom.fst k k A)).op)
    ((algSpec (.of k)).map (CommAlgCat.ofHom (AlgHom.snd k k A)).op)
  letI : IsIso f := by exact coprodSpecOver_isIso k k A
  ((algSpec (.of k)).mapIso
    (CommAlgCat.isoMk (coordinateAdjoinAlgEquiv k L hnosplit ζ hζ)).op).symm ≪≫
      (asIso f).symm

lemma adjoinSchemeIso_hom_base (hnosplit : ¬ ∃ a : k, IsPrimitiveRoot a 3)
    (ζ : L) (hζ : IsPrimitiveRoot ζ 3) :
    (adjoinSchemeIso k L hnosplit ζ hζ).hom.left ≫
      (baseScheme k ⨿ (algSpec (.of k)).obj
        (.op (CommAlgCat.of k (Algebra.adjoin k ({ζ} : Set L))))).hom =
      (rootsOfUnityScheme k 3).hom :=
  (adjoinSchemeIso k L hnosplit ζ hζ).hom.w

lemma adjoinSchemeIso_inv_base (hnosplit : ¬ ∃ a : k, IsPrimitiveRoot a 3)
    (ζ : L) (hζ : IsPrimitiveRoot ζ 3) :
    (adjoinSchemeIso k L hnosplit ζ hζ).inv.left ≫ (rootsOfUnityScheme k 3).hom =
      (baseScheme k ⨿ (algSpec (.of k)).obj
        (.op (CommAlgCat.of k (Algebra.adjoin k ({ζ} : Set L))))).hom :=
  (adjoinSchemeIso k L hnosplit ζ hζ).inv.w

lemma adjoinSchemeIso_inv_left (hnosplit : ¬ ∃ a : k, IsPrimitiveRoot a 3)
    (ζ : L) (hζ : IsPrimitiveRoot ζ 3) :
    (adjoinSchemeIso k L hnosplit ζ hζ).inv.left =
      inv (coprodComparison (Over.forget (Spec (.of k))) (baseScheme k)
        ((algSpec (.of k)).obj (.op (CommAlgCat.of k (Algebra.adjoin k ({ζ} : Set L)))))) ≫
      coprodSpec k (Algebra.adjoin k ({ζ} : Set L)) ≫
      Spec.map (CommRingCat.ofHom
        (coordinateAdjoinAlgEquiv k L hnosplit ζ hζ).toAlgHom.toRingHom) :=
  factorIso_inv_left k _

lemma adjoinSchemeIso_inl (hnosplit : ¬ ∃ a : k, IsPrimitiveRoot a 3)
    (ζ : L) (hζ : IsPrimitiveRoot ζ 3) :
    (coprod.inl ≫ (adjoinSchemeIso k L hnosplit ζ hζ).inv).left =
      Spec.map (CommRingCat.ofHom
        ((AlgHom.fst k k (Algebra.adjoin k ({ζ} : Set L))).comp
          (coordinateAdjoinAlgEquiv k L hnosplit ζ hζ).toAlgHom).toRingHom) :=
  factorIso_inl k _

lemma adjoinSchemeIso_inr (hnosplit : ¬ ∃ a : k, IsPrimitiveRoot a 3)
    (ζ : L) (hζ : IsPrimitiveRoot ζ 3) :
    (coprod.inr ≫ (adjoinSchemeIso k L hnosplit ζ hζ).inv).left =
      Spec.map (CommRingCat.ofHom
        ((AlgHom.snd k k (Algebra.adjoin k ({ζ} : Set L))).comp
          (coordinateAdjoinAlgEquiv k L hnosplit ζ hζ).toAlgHom).toRingHom) :=
  factorIso_inr k _

/-- Each chosen component commutes with its map to the base. -/
lemma adjoinSchemeIso_components_base (hnosplit : ¬ ∃ a : k, IsPrimitiveRoot a 3)
    (ζ : L) (hζ : IsPrimitiveRoot ζ 3) :
    (coprod.inl ≫ (adjoinSchemeIso k L hnosplit ζ hζ).inv).left ≫
      (rootsOfUnityScheme k 3).hom = (baseScheme k).hom ∧
    (coprod.inr ≫ (adjoinSchemeIso k L hnosplit ζ hζ).inv).left ≫
      (rootsOfUnityScheme k 3).hom = ((algSpec (.of k)).obj
        (.op (CommAlgCat.of k (Algebra.adjoin k ({ζ} : Set L))))).hom :=
  ⟨(coprod.inl ≫ (adjoinSchemeIso k L hnosplit ζ hζ).inv).w,
    (coprod.inr ≫ (adjoinSchemeIso k L hnosplit ζ hζ).inv).w⟩

/-- The canonical nonsplit decomposition using the specified primitive root in
the separable closure, rather than replacing it by an algebraic closure. -/
def separableClosureSchemeIso (h3 : (3 : k) ≠ 0)
    (hnosplit : ¬ ∃ a : k, IsPrimitiveRoot a 3) :
    rootsOfUnityScheme k 3 ≅ baseScheme k ⨿
      (algSpec (.of k)).obj (.op (CommAlgCat.of k
        (Algebra.adjoin k ({separableClosureRoot h3} : Set (SeparableClosure k))))) :=
  adjoinSchemeIso k (SeparableClosure k) hnosplit (separableClosureRoot h3)
    (separableClosureRoot_isPrimitiveRoot h3)

end Fields

end AlgebraicGeometry.RootsOfUnityThree
