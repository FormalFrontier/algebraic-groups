/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

import AlgebraicGroups.GroupScheme.FiniteConstantPoints

set_option warningAsError true

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

universe u

variable (K Γ R : Type u)
variable [CommRing K] [CommRing R] [Algebra K R] [Fintype Γ] [Group Γ]

-- The unrestricted theorem has no nontriviality hypothesis and therefore also
-- applies when the target algebra is the zero ring.
private noncomputable def persistentTestFiniteConstantPoints001 [Subsingleton R] :
    LocallyConstant (PrimeSpectrum R) Γ ≃*
      ((Spec (.of R)).asOver (Spec (.of K)) ⟶
        (finiteConstantGroupScheme K Γ).X) :=
  finiteConstantLocallyConstantMulEquivPoints K Γ R

private noncomputable def persistentTestFiniteConstantPoints002 [Nontrivial R]
    (h : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1) :
    Γ ≃* ((Spec (.of R)).asOver (Spec (.of K)) ⟶
      (finiteConstantGroupScheme K Γ).X) :=
  finiteConstantMulEquivPointsOfTrivialIdempotents K Γ R h

private theorem persistentTestFiniteConstantPoints003 (g : Γ) :
    (finiteConstantLocallyConstantMulEquivPoints K Γ K
      (LocallyConstant.const (PrimeSpectrum K) g)).left =
        (finiteConstantGroupSchemePoint K Γ g).left :=
  finiteConstantLocallyConstantMulEquivPoints_const K Γ g

private theorem persistentTestFiniteConstantPoints004 {S : Type u} [CommRing S] [Algebra K S] (a : R →ₐ[K] S)
    (f : LocallyConstant (PrimeSpectrum R) Γ) :
    finiteConstantLocallyConstantMulEquivPoints K Γ S
        (LocallyConstant.comap
          ⟨PrimeSpectrum.comap a.toRingHom,
            PrimeSpectrum.continuous_comap a.toRingHom⟩ f) =
      (Spec.map (CommRingCat.ofHom a.toRingHom)).asOver (Spec (.of K)) ≫
        finiteConstantLocallyConstantMulEquivPoints K Γ R f :=
  finiteConstantLocallyConstantMulEquivPoints_naturality K Γ R a f

private noncomputable def persistentTestFiniteConstantPoints005 [Unique Γ] : FiniteGroupFunctions K Γ ≃ₐ[K] K :=
  FiniteGroupFunctions.uniqueAlgEquiv K Γ

end AlgebraicGeometry
