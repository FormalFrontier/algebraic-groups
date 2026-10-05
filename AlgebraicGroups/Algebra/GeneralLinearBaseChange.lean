/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.MatrixEndBaseChange
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# General linear groups under extension of scalars

For an arbitrary module, extension of scalars acts on endomorphisms by the
tensor-cancellation construction. Its multiplicative structure makes the
groups of invertible endomorphisms functorial in every coefficient algebra map,
without finiteness of the module or flatness or injectivity of the coefficient
map. A module isomorphism acts by conjugation; an arbitrary linear map does not
induce a homomorphism on automorphism groups.

## References

* J. S. Milne, *Algebraic Groups* (2017), §2, item 2.8, p. 41: the functor
  of automorphisms of the scalar extension of a vector space over a field.
* Mathlib, `LinearAlgebra/TensorProduct/Tower`: `Module.End.baseChangeHom` and
  `AlgebraTensorModule.cancelBaseChange` underlying endomorphism extension.
* Mathlib, `Algebra/Category/Grp/Adjunctions`: `MonCat.units` turns the
  endomorphism composition functor into a group-valued functor.
* Mathlib, `LinearAlgebra/GeneralLinearGroup/Basic`: the comparison
  `generalLinearEquiv` between endomorphism units and linear automorphisms,
  and `congrLinearEquiv` for conjugation by linear equivalences.
-/

public section

noncomputable section

open CategoryTheory TensorProduct
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (V : Type u) [AddCommGroup V] [Module K V]
  (R : Type u) [CommRing R] [Algebra K R]

/-- The existing tensor-cancellation extension of endomorphisms, as a ring map. -/
@[expose] def endBaseChangeRingHom (S : Type u) [CommRing S] [Algebra K S]
    (g : R →ₐ[K] S) :
    Module.End R (SourceOrderTensor K V R) →+*
      Module.End S (SourceOrderTensor K V S) := by
  letI : Algebra R S := g.toRingHom.toAlgebra
  exact (LinearEquiv.conjRingEquiv
    (AlgebraTensorModule.cancelBaseChange K R S S V)).toRingHom.comp
    (Module.End.baseChangeHom R S (SourceOrderTensor K V R)).toRingHom

@[simp] theorem endBaseChangeRingHom_apply (S : Type u) [CommRing S] [Algebra K S]
    (g : R →ₐ[K] S) (f : Module.End R (SourceOrderTensor K V R)) :
    endBaseChangeRingHom K V R S g f = endBaseChange K V R S g f := by
  rfl

/-- The composition monoid of endomorphisms after scalar extension. -/
@[expose] def endCompositionFunctor : CommAlgCat K ⥤ MonCat where
  obj R := MonCat.of (Module.End R (SourceOrderTensor K V R))
  map f := MonCat.ofHom (endBaseChangeRingHom K V _ _ f.hom).toMonoidHom
  map_id R := by
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro f
    exact endBaseChange_id K V R f
  map_comp f g := by
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro h
    exact (endBaseChange_comp K V _ _ _ f.hom g.hom h).symm

/-- The automorphism-group functor on scalar extensions, extending Milne's
case over a field base, with all commutative algebras over that field as test
algebras (*Algebraic Groups*, item 2.8), to arbitrary commutative base rings
and arbitrary modules. -/
@[expose] def generalLinearModuleFunctor : CommAlgCat K ⥤ GrpCat :=
  endCompositionFunctor K V ⋙ MonCat.units

/-- Explicit scalar extension of an invertible endomorphism. -/
@[expose] def generalLinearModuleBaseChange (S : Type u) [CommRing S] [Algebra K S]
    (g : R →ₐ[K] S) :
    LinearMap.GeneralLinearGroup R (SourceOrderTensor K V R) →*
      LinearMap.GeneralLinearGroup S (SourceOrderTensor K V S) :=
  Units.map (endBaseChangeRingHom K V R S g).toMonoidHom

@[simp] theorem generalLinearModuleBaseChange_val (S : Type u) [CommRing S] [Algebra K S]
    (g : R →ₐ[K] S) (f : LinearMap.GeneralLinearGroup R (SourceOrderTensor K V R)) :
    (generalLinearModuleBaseChange K V R S g f).val = endBaseChange K V R S g f := rfl

@[simp] theorem generalLinearModuleBaseChange_id
    (f : LinearMap.GeneralLinearGroup R (SourceOrderTensor K V R)) :
    generalLinearModuleBaseChange K V R R (AlgHom.id K R) f = f := by
  apply Units.ext
  simp

@[simp] theorem generalLinearModuleBaseChange_comp
    (S T : Type u) [CommRing S] [Algebra K S] [CommRing T] [Algebra K T]
    (g : R →ₐ[K] S) (h : S →ₐ[K] T)
    (f : LinearMap.GeneralLinearGroup R (SourceOrderTensor K V R)) :
    generalLinearModuleBaseChange K V S T h
        (generalLinearModuleBaseChange K V R S g f) =
      generalLinearModuleBaseChange K V R T (h.comp g) f := by
  apply Units.ext
  simpa only [generalLinearModuleBaseChange_val] using
    endBaseChange_comp K V R S T g h f.val

theorem generalLinearModuleBaseChange_inv (S : Type u) [CommRing S] [Algebra K S]
    (g : R →ₐ[K] S) (f : LinearMap.GeneralLinearGroup R (SourceOrderTensor K V R)) :
    (generalLinearModuleBaseChange K V R S g f).inv = endBaseChange K V R S g f.inv := rfl

theorem generalLinearModuleBaseChange_tmul (S : Type u) [CommRing S] [Algebra K S]
    (g : R →ₐ[K] S) (f : LinearMap.GeneralLinearGroup R (SourceOrderTensor K V R))
    (s : S) (v : V) :
    (generalLinearModuleBaseChange K V R S g f).val (s ⊗ₜ[K] v) =
      s • (g.toLinearMap.rTensor V) (f.val (1 ⊗ₜ[K] v)) := by
  rw [generalLinearModuleBaseChange_val, endBaseChange_tmul]

/-- Endomorphism units are linear automorphisms by Mathlib's
`LinearMap.GeneralLinearGroup.generalLinearEquiv`, without finiteness assumptions. -/
def generalLinearModuleAutomorphisms :
    LinearMap.GeneralLinearGroup R (SourceOrderTensor K V R) ≃*
      (SourceOrderTensor K V R ≃ₗ[R] SourceOrderTensor K V R) :=
  LinearMap.GeneralLinearGroup.generalLinearEquiv R (SourceOrderTensor K V R)

/-- Transport an automorphism to the literal source-order tensor with its transported action. -/
def sourceOrderedGeneralLinearEquiv :
    LinearMap.GeneralLinearGroup R (SourceOrderedTensor K V R) ≃*
      LinearMap.GeneralLinearGroup R (SourceOrderTensor K V R) :=
  LinearMap.GeneralLinearGroup.congrLinearEquiv (sourceOrderedCanonicalLinearEquiv K V R)

@[simp] theorem sourceOrderedGeneralLinearEquiv_tmul
    (f : LinearMap.GeneralLinearGroup R (SourceOrderedTensor K V R))
    (v : V) (r : R) :
    (sourceOrderedGeneralLinearEquiv K V R f).val (r ⊗ₜ[K] v) =
      sourceOrderedCanonicalLinearEquiv K V R (f.val (sourceOrderedTmul K V R v r)) := by
  simp [sourceOrderedGeneralLinearEquiv]
  congr 1

/-- Scalar extension of the literal-order module is conjugate to canonical scalar extension. -/
def sourceOrderedGeneralLinearBaseChange (S : Type u) [CommRing S] [Algebra K S]
    (g : R →ₐ[K] S) :
    LinearMap.GeneralLinearGroup R (SourceOrderedTensor K V R) →*
      LinearMap.GeneralLinearGroup S (SourceOrderedTensor K V S) :=
  (sourceOrderedGeneralLinearEquiv K V S).symm.toMonoidHom.comp
    ((generalLinearModuleBaseChange K V R S g).comp
      (sourceOrderedGeneralLinearEquiv K V R).toMonoidHom)

@[simp] theorem sourceOrderedGeneralLinearBaseChange_id
    (f : LinearMap.GeneralLinearGroup R (SourceOrderedTensor K V R)) :
    sourceOrderedGeneralLinearBaseChange K V R R (AlgHom.id K R) f = f := by
  apply (sourceOrderedGeneralLinearEquiv K V R).injective
  simp [sourceOrderedGeneralLinearBaseChange]

@[simp] theorem sourceOrderedGeneralLinearBaseChange_comp
    (S T : Type u) [CommRing S] [Algebra K S] [CommRing T] [Algebra K T]
    (g : R →ₐ[K] S) (h : S →ₐ[K] T)
    (f : LinearMap.GeneralLinearGroup R (SourceOrderedTensor K V R)) :
    sourceOrderedGeneralLinearBaseChange K V S T h
        (sourceOrderedGeneralLinearBaseChange K V R S g f) =
      sourceOrderedGeneralLinearBaseChange K V R T (h.comp g) f := by
  apply (sourceOrderedGeneralLinearEquiv K V T).injective
  simp [sourceOrderedGeneralLinearBaseChange, generalLinearModuleBaseChange_comp]

/-- The general linear functor on the transported literal-order tensor module. -/
def sourceOrderedGeneralLinearFunctor : CommAlgCat K ⥤ GrpCat where
  obj R := GrpCat.of (LinearMap.GeneralLinearGroup R (SourceOrderedTensor K V R))
  map f := GrpCat.ofHom (sourceOrderedGeneralLinearBaseChange K V _ _ f.hom)
  map_id R := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro f
    exact sourceOrderedGeneralLinearBaseChange_id K V R f
  map_comp f g := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro h
    exact (sourceOrderedGeneralLinearBaseChange_comp K V _ _ _ f.hom g.hom h).symm

/-- Naturality of the literal-order/canonical automorphism comparison. -/
def sourceOrderedGeneralLinearIso :
    sourceOrderedGeneralLinearFunctor K V ≅ generalLinearModuleFunctor K V :=
  NatIso.ofComponents
    (fun R ↦ (sourceOrderedGeneralLinearEquiv K V R).toGrpIso)
    (fun {R S} g ↦ by
      apply GrpCat.hom_ext
      apply MonoidHom.ext
      intro f
      change sourceOrderedGeneralLinearEquiv K V S
        (sourceOrderedGeneralLinearBaseChange K V R S g.hom f) =
          generalLinearModuleBaseChange K V R S g.hom
            (sourceOrderedGeneralLinearEquiv K V R f)
      change sourceOrderedGeneralLinearEquiv K V S
        ((sourceOrderedGeneralLinearEquiv K V S).symm
          (generalLinearModuleBaseChange K V R S g.hom
            (sourceOrderedGeneralLinearEquiv K V R f))) = _
      exact (sourceOrderedGeneralLinearEquiv K V S).apply_symm_apply _)

/-- The transported literal-order action on pure tensors under coefficient change. -/
theorem sourceOrderedGeneralLinearBaseChange_tmul
    (S : Type u) [CommRing S] [Algebra K S]
    (g : R →ₐ[K] S) (f : LinearMap.GeneralLinearGroup R (SourceOrderedTensor K V R))
    (v : V) (s : S) :
    (sourceOrderedGeneralLinearBaseChange K V R S g f).val
        (sourceOrderedTmul K V S v s) =
      (sourceOrderedCanonicalLinearEquiv K V S).symm
        (s • (g.toLinearMap.rTensor V)
          ((sourceOrderedGeneralLinearEquiv K V R f).val (1 ⊗ₜ[K] v))) := by
  apply (sourceOrderedCanonicalLinearEquiv K V S).injective
  simp only [LinearEquiv.apply_symm_apply]
  rw [← sourceOrderedGeneralLinearEquiv_tmul]
  have comparison : sourceOrderedGeneralLinearEquiv K V S
      (sourceOrderedGeneralLinearBaseChange K V R S g f) =
        generalLinearModuleBaseChange K V R S g (sourceOrderedGeneralLinearEquiv K V R f) := by
    simp [sourceOrderedGeneralLinearBaseChange]
  rw [comparison]
  exact generalLinearModuleBaseChange_tmul K V R S g _ s v

end AlgebraicGeometry

#lint
