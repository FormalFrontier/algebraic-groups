/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.AdditivePowerQuotient
public import AlgebraicGroups.GroupScheme.InfinitesimalAdditive
public import AlgebraicGroups.GroupScheme.RootsOfUnity
public import Mathlib.Algebra.CharP.Lemmas

public section

/-!
# Translation between prime-power infinitesimal and roots-of-unity schemes

In characteristic `p`, translation by one identifies the algebra of functions on
the `p ^ m`-th roots of unity with that on the `p ^ m`-th infinitesimal additive
scheme. This works for every `m`, including zero, and gives an isomorphism of
underlying schemes over the base field. It does not assert an isomorphism of
group schemes: an algebra isomorphism need not respect comultiplication. For
`m = 0`, a separate group-scheme isomorphism exists but is not supplied here.

The coordinate maps send `u` to `1 + t` and `t` to `u - 1`. Their pointwise
readbacks hold for arbitrary commutative algebras over the field, including
the zero algebra, without assuming that the test algebra has characteristic
exactly `p`.
-/

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable (K : Type u) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (m : ℕ)

omit [Fact p.Prime] in
private theorem translation_char_target (R : Type u) [CommRing R] [Algebra K R] :
    (p : R) = 0 := by
  calc
    (p : R) = algebraMap K R (p : K) := (map_natCast (algebraMap K R) p).symm
    _ = 0 := by rw [CharP.cast_eq_zero K p]; simp

private theorem translation_add_pow (R : Type u) [CommRing R] [Algebra K R]
    (x : R) : (1 + x) ^ (p ^ m) = 1 + x ^ (p ^ m) := by
  rw [(Commute.all (1 : R) x).add_pow_prime_pow_eq' (Fact.out : p.Prime) m,
    translation_char_target K p R]
  simp

private theorem translation_sub_pow (R : Type u) [CommRing R] [Algebra K R]
    (x : R) : (x - 1) ^ (p ^ m) = x ^ (p ^ m) - 1 := by
  have h := translation_add_pow K p m R (x - 1)
  rw [show (1 : R) + (x - 1) = x by ring] at h
  rw [h]
  ring

private def translationToPowerAlgHom :
    AdjoinRoot (rootsOfUnityPolynomial K (p ^ m)) →ₐ[K]
      AdjoinRoot ((Polynomial.X : Polynomial K) ^ (p ^ m)) :=
  AdjoinRoot.liftAlgHom (rootsOfUnityPolynomial K (p ^ m)) (Algebra.ofId K _)
    (1 + AdjoinRoot.root ((Polynomial.X : Polynomial K) ^ (p ^ m))) (by
      have hroot : AdjoinRoot.root ((Polynomial.X : Polynomial K) ^ (p ^ m)) ^
          (p ^ m) = 0 := by
        simpa using AdjoinRoot.eval₂_root ((Polynomial.X : Polynomial K) ^ (p ^ m))
      simp [rootsOfUnityPolynomial, translation_add_pow K p m, hroot])

private def translationFromPowerAlgHom :
    AdjoinRoot ((Polynomial.X : Polynomial K) ^ (p ^ m)) →ₐ[K]
      AdjoinRoot (rootsOfUnityPolynomial K (p ^ m)) :=
  AdjoinRoot.liftAlgHom ((Polynomial.X : Polynomial K) ^ (p ^ m)) (Algebra.ofId K _)
    (AdjoinRoot.root (rootsOfUnityPolynomial K (p ^ m)) - 1) (by
      have hroot : AdjoinRoot.root (rootsOfUnityPolynomial K (p ^ m)) ^
          (p ^ m) - 1 = 0 := by
        simpa [rootsOfUnityPolynomial] using
          AdjoinRoot.eval₂_root (rootsOfUnityPolynomial K (p ^ m))
      simp [translation_sub_pow K p m, sub_eq_zero.mp hroot])

private theorem translationToPower_comp_translationFromPower :
    (translationToPowerAlgHom K p m).comp (translationFromPowerAlgHom K p m) =
      AlgHom.id K (AdjoinRoot ((Polynomial.X : Polynomial K) ^ (p ^ m))) := by
  apply AdjoinRoot.algHom_ext
  simp [translationToPowerAlgHom, translationFromPowerAlgHom]

private theorem translationFromPower_comp_translationToPower :
    (translationFromPowerAlgHom K p m).comp (translationToPowerAlgHom K p m) =
      AlgHom.id K (AdjoinRoot (rootsOfUnityPolynomial K (p ^ m))) := by
  apply AdjoinRoot.algHom_ext
  simp [translationToPowerAlgHom, translationFromPowerAlgHom]

private def translationPowerAlgEquiv :
    AdjoinRoot (rootsOfUnityPolynomial K (p ^ m)) ≃ₐ[K]
      AdjoinRoot ((Polynomial.X : Polynomial K) ^ (p ^ m)) :=
  AlgEquiv.ofAlgHom (translationToPowerAlgHom K p m)
    (translationFromPowerAlgHom K p m)
    (translationToPower_comp_translationFromPower K p m)
    (translationFromPower_comp_translationToPower K p m)

private instance translation_power_neZero : NeZero (p ^ m) :=
  ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩

/-- Prime-power translation of the two coordinate rings, valid also for `m = 0`. -/
def infinitesimalAdditiveTranslationAlgEquiv :
    rootsOfUnityCoordinateRing K (p ^ m) ≃ₐ[K]
      infinitesimalAdditiveCoordinateRing K p m :=
  ((rootsOfUnityCoordinateAlgEquiv K (p ^ m)).trans
    (translationPowerAlgEquiv K p m)).trans
      (additivePowerCoordinateAlgEquiv K (p ^ m)).symm

@[simp]
theorem infinitesimalAdditiveTranslationAlgEquiv_generator :
    infinitesimalAdditiveTranslationAlgEquiv K p m
      (rootsOfUnityCoordinateGenerator K (p ^ m)) =
        1 + infinitesimalAdditiveCoordinate K p m := by
  simp [infinitesimalAdditiveTranslationAlgEquiv, translationPowerAlgEquiv,
    translationToPowerAlgHom, infinitesimalAdditiveCoordinate,
    additivePowerCoordinate, infinitesimalAdditiveIdeal, additivePowerIdeal]

@[simp]
theorem infinitesimalAdditiveTranslationAlgEquiv_symm_coordinate :
    (infinitesimalAdditiveTranslationAlgEquiv K p m).symm
      (infinitesimalAdditiveCoordinate K p m) =
        rootsOfUnityCoordinateGenerator K (p ^ m) - 1 := by
  simp [infinitesimalAdditiveTranslationAlgEquiv, translationPowerAlgEquiv,
    translationFromPowerAlgHom, infinitesimalAdditiveCoordinate,
    infinitesimalAdditiveIdeal]

/-- The contravariant scheme isomorphism attached to the coordinate translation. -/
def infinitesimalAdditiveTranslationIso :
    infinitesimalAdditiveUnderlyingScheme K p m ≅
      rootsOfUnityScheme K (p ^ m) :=
  (algSpec (.of K)).mapIso
    (CommAlgCat.isoMk (infinitesimalAdditiveTranslationAlgEquiv K p m)).op

/-- The forward scheme map is `Spec` of the forward coordinate map. -/
@[simp]
theorem infinitesimalAdditiveTranslationIso_hom_left :
    (infinitesimalAdditiveTranslationIso K p m).hom.left =
      Spec.map (CommRingCat.ofHom
        (infinitesimalAdditiveTranslationAlgEquiv K p m).toAlgHom.toRingHom) := by
  rfl

/-- The inverse scheme map is `Spec` of the inverse coordinate translation. -/
@[simp]
theorem infinitesimalAdditiveTranslationIso_inv_left :
    (infinitesimalAdditiveTranslationIso K p m).inv.left =
      Spec.map (CommRingCat.ofHom
        (infinitesimalAdditiveTranslationAlgEquiv K p m).symm.toAlgHom.toRingHom) := by
  rfl

/-- Evaluation of a translated roots-of-unity coordinate on any test algebra. -/
@[simp]
theorem infinitesimalAdditiveTranslation_point_generator
    (R : Type u) [CommRing R] [Algebra K R]
    (sigma : infinitesimalAdditiveCoordinateRing K p m →ₐ[K] R) :
    (sigma.comp (infinitesimalAdditiveTranslationAlgEquiv K p m).toAlgHom)
      (rootsOfUnityCoordinateGenerator K (p ^ m)) =
        1 + sigma (infinitesimalAdditiveCoordinate K p m) := by
  simp

/-- Evaluation of the inverse coordinate translation on any test algebra. -/
@[simp]
theorem infinitesimalAdditiveTranslation_point_coordinate
    (R : Type u) [CommRing R] [Algebra K R]
    (rho : rootsOfUnityCoordinateRing K (p ^ m) →ₐ[K] R) :
    (rho.comp (infinitesimalAdditiveTranslationAlgEquiv K p m).symm.toAlgHom)
      (infinitesimalAdditiveCoordinate K p m) =
        rho (rootsOfUnityCoordinateGenerator K (p ^ m)) - 1 := by
  simp

/-- Translation of a point commutes with extension of its test algebra. -/
theorem infinitesimalAdditiveTranslation_point_naturality
    (R S : Type u) [CommRing R] [Algebra K R] [CommRing S] [Algebra K S]
    (sigma : infinitesimalAdditiveCoordinateRing K p m →ₐ[K] R)
    (f : R →ₐ[K] S) :
    f.comp (sigma.comp (infinitesimalAdditiveTranslationAlgEquiv K p m).toAlgHom) =
      (f.comp sigma).comp (infinitesimalAdditiveTranslationAlgEquiv K p m).toAlgHom := by
  rw [AlgHom.comp_assoc]

/-- The inverse translation of a point is natural in the test algebra. -/
theorem infinitesimalAdditiveTranslation_point_symm_naturality
    (R S : Type u) [CommRing R] [Algebra K R] [CommRing S] [Algebra K S]
    (rho : rootsOfUnityCoordinateRing K (p ^ m) →ₐ[K] R)
    (f : R →ₐ[K] S) :
    f.comp (rho.comp (infinitesimalAdditiveTranslationAlgEquiv K p m).symm.toAlgHom) =
      (f.comp rho).comp (infinitesimalAdditiveTranslationAlgEquiv K p m).symm.toAlgHom := by
  rw [AlgHom.comp_assoc]

#print axioms translation_char_target
#print axioms translation_add_pow
#print axioms translation_sub_pow
#print axioms translationToPowerAlgHom
#print axioms translationFromPowerAlgHom
#print axioms translationToPower_comp_translationFromPower
#print axioms translationFromPower_comp_translationToPower
#print axioms translationPowerAlgEquiv
#print axioms translation_power_neZero
#print axioms infinitesimalAdditiveTranslationAlgEquiv
#print axioms infinitesimalAdditiveTranslationAlgEquiv_generator
#print axioms infinitesimalAdditiveTranslationAlgEquiv_symm_coordinate
#print axioms infinitesimalAdditiveTranslationIso
#print axioms infinitesimalAdditiveTranslationIso_hom_left
#print axioms infinitesimalAdditiveTranslationIso_inv_left
#print axioms infinitesimalAdditiveTranslation_point_generator
#print axioms infinitesimalAdditiveTranslation_point_coordinate
#print axioms infinitesimalAdditiveTranslation_point_naturality
#print axioms infinitesimalAdditiveTranslation_point_symm_naturality

end AlgebraicGeometry
