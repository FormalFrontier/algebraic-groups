/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.RightComodule
public import Mathlib.Algebra.DirectSum.Module

/-!
# Direct sums of specified right comodules

The direct sum of a family of specified right comodules over one coalgebra
has the coaction obtained from the component coactions by `DirectSum.toModule`.
The coalgebra factor remains on the right. The coassociativity and counit laws
are checked on the linear inclusions.

`directSumLof` supplies these inclusions without an index-decidability hypothesis.
The characteristic map and application lemmas describe the coaction without
unfolding the construction.
-/

@[expose] public section

universe uR uC uI uM

open scoped TensorProduct DirectSum

namespace Coalgebra.RightComodule

section LinearInclusions

variable (R : Type uR) {I : Type uI} (M : I → Type uM)
variable [Semiring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

/-- The linear inclusion into a direct sum, with index decidability chosen internally. -/
noncomputable def directSumLof (i : I) : M i →ₗ[R] ⨁ i, M i := by
  classical
  exact DirectSum.lof R I M i

/-- The inclusion agrees with the canonical inclusion for any decision procedure on the index. -/
theorem directSumLof_eq_lof [DecidableEq I] (i : I) :
    directSumLof R M i = DirectSum.lof R I M i := by
  exact congrArg (fun (d : DecidableEq I) =>
    letI : DecidableEq I := d
    DirectSum.lof R I M i) (Subsingleton.elim _ _)

end LinearInclusions

variable {R : Type uR} {C : Type uC} {I : Type uI} {M : I → Type uM}
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

private theorem directSum_coassoc [DecidableEq I]
    (X : ∀ i, RightComodule R C (M i))
    (ρ : (⨁ i, M i) →ₗ[R] (⨁ i, M i) ⊗[R] C)
    (hρ : ∀ i, ρ ∘ₗ DirectSum.lof R I M i =
      (DirectSum.lof R I M i).rTensor C ∘ₗ (X i).coaction) :
    TensorProduct.assoc R (⨁ i, M i) C C ∘ₗ ρ.rTensor C ∘ₗ ρ =
      (comul (R := R) (A := C)).lTensor (⨁ i, M i) ∘ₗ ρ := by
  apply DirectSum.linearMap_ext
  intro i
  let j := DirectSum.lof R I M i
  have hj : ρ ∘ₗ j = j.rTensor C ∘ₗ (X i).coaction := hρ i
  have ht : ρ.rTensor C ∘ₗ j.rTensor C =
      (j.rTensor C).rTensor C ∘ₗ (X i).coaction.rTensor C := by
    rw [← LinearMap.rTensor_comp, hj, LinearMap.rTensor_comp]
  have hα : TensorProduct.assoc R (⨁ i, M i) C C ∘ₗ (j.rTensor C).rTensor C =
      j.rTensor (C ⊗[R] C) ∘ₗ TensorProduct.assoc R (M i) C C := by
    ext m c d
    rfl
  have hΔ : j.rTensor (C ⊗[R] C) ∘ₗ
        (comul (R := R) (A := C)).lTensor (M i) =
      (comul (R := R) (A := C)).lTensor (⨁ i, M i) ∘ₗ j.rTensor C := by
    ext m c
    rfl
  change ((TensorProduct.assoc R (⨁ i, M i) C C).toLinearMap ∘ₗ ρ.rTensor C ∘ₗ ρ) ∘ₗ j = _
  calc
    (TensorProduct.assoc R (⨁ i, M i) C C ∘ₗ ρ.rTensor C ∘ₗ ρ) ∘ₗ j =
        TensorProduct.assoc R (⨁ i, M i) C C ∘ₗ ρ.rTensor C ∘ₗ
          j.rTensor C ∘ₗ (X i).coaction := by
      simp only [LinearMap.comp_assoc, hj]
    _ = TensorProduct.assoc R (⨁ i, M i) C C ∘ₗ (j.rTensor C).rTensor C ∘ₗ
          (X i).coaction.rTensor C ∘ₗ (X i).coaction := by
      simpa only [LinearMap.comp_assoc] using
        congrArg (fun f => (TensorProduct.assoc R (⨁ i, M i) C C).toLinearMap ∘ₗ f ∘ₗ
          (X i).coaction) ht
    _ = j.rTensor (C ⊗[R] C) ∘ₗ
          (TensorProduct.assoc R (M i) C C ∘ₗ (X i).coaction.rTensor C ∘ₗ
            (X i).coaction) := by
      simpa only [LinearMap.comp_assoc] using
        congrArg (fun f => f ∘ₗ (X i).coaction.rTensor C ∘ₗ (X i).coaction) hα
    _ = j.rTensor (C ⊗[R] C) ∘ₗ
          ((comul (R := R) (A := C)).lTensor (M i) ∘ₗ (X i).coaction) := by
      rw [(X i).coassoc]
    _ = (comul (R := R) (A := C)).lTensor (⨁ i, M i) ∘ₗ
          j.rTensor C ∘ₗ (X i).coaction := by
      simpa only [LinearMap.comp_assoc] using
        congrArg (fun f => f ∘ₗ (X i).coaction) hΔ
    _ = ((comul (R := R) (A := C)).lTensor (⨁ i, M i) ∘ₗ ρ) ∘ₗ j := by
      simp only [LinearMap.comp_assoc, hj]

private theorem directSum_counit_comp [DecidableEq I]
    (X : ∀ i, RightComodule R C (M i))
    (ρ : (⨁ i, M i) →ₗ[R] (⨁ i, M i) ⊗[R] C)
    (hρ : ∀ i, ρ ∘ₗ DirectSum.lof R I M i =
      (DirectSum.lof R I M i).rTensor C ∘ₗ (X i).coaction) :
    (counit (R := R) (A := C)).lTensor (⨁ i, M i) ∘ₗ ρ =
      (TensorProduct.rid R (⨁ i, M i)).symm.toLinearMap := by
  apply DirectSum.linearMap_ext
  intro i
  let j := DirectSum.lof R I M i
  have hj : ρ ∘ₗ j = j.rTensor C ∘ₗ (X i).coaction := hρ i
  have hε : (counit (R := R) (A := C)).lTensor (⨁ i, M i) ∘ₗ j.rTensor C =
      j.rTensor R ∘ₗ (counit (R := R) (A := C)).lTensor (M i) := by
    ext m c
    rfl
  change ((counit (R := R) (A := C)).lTensor (⨁ i, M i) ∘ₗ ρ) ∘ₗ j = _
  calc
    ((counit (R := R) (A := C)).lTensor (⨁ i, M i) ∘ₗ ρ) ∘ₗ j =
        (counit (R := R) (A := C)).lTensor (⨁ i, M i) ∘ₗ
          j.rTensor C ∘ₗ (X i).coaction := by
      simp only [LinearMap.comp_assoc, hj]
    _ = j.rTensor R ∘ₗ
          ((counit (R := R) (A := C)).lTensor (M i) ∘ₗ (X i).coaction) := by
      simpa only [LinearMap.comp_assoc] using
        congrArg (fun f => f ∘ₗ (X i).coaction) hε
    _ = j.rTensor R ∘ₗ (TensorProduct.rid R (M i)).symm.toLinearMap := by
      rw [(X i).counit_comp]
    _ = (TensorProduct.rid R (⨁ i, M i)).symm.toLinearMap ∘ₗ j := by
      ext m
      rfl

/-- The specified right comodule on the direct sum of a family of right comodules
    over the same coalgebra. -/
noncomputable def directSum (X : ∀ i, RightComodule R C (M i)) :
    RightComodule R C (⨁ i, M i) where
  coaction := by
    classical
    exact DirectSum.toModule R I ((⨁ i, M i) ⊗[R] C)
      (fun i => (DirectSum.lof R I M i).rTensor C ∘ₗ (X i).coaction)
  coassoc := by
    classical
    apply directSum_coassoc X
    intro i
    ext m
    simp only [LinearMap.comp_apply, DirectSum.toModule_lof]
  counit_comp := by
    classical
    apply directSum_counit_comp X
    intro i
    ext m
    simp only [LinearMap.comp_apply, DirectSum.toModule_lof]

/-- The coaction of a direct sum restricts to the supplied coaction on each summand. -/
theorem directSum_coaction_comp_lof (X : ∀ i, RightComodule R C (M i)) (i : I) :
    (directSum X).coaction ∘ₗ directSumLof R M i =
      (directSumLof R M i).rTensor C ∘ₗ (X i).coaction := by
  classical
  ext m
  simp only [directSum, directSumLof_eq_lof, LinearMap.comp_apply, DirectSum.toModule_lof]

/-- The characteristic coaction formula evaluated on an element of one summand. -/
@[simp] theorem directSum_coaction_lof (X : ∀ i, RightComodule R C (M i))
    (i : I) (m : M i) :
    (directSum X).coaction (directSumLof R M i m) =
      (directSumLof R M i).rTensor C ((X i).coaction m) :=
  LinearMap.congr_fun (directSum_coaction_comp_lof X i) m

end Coalgebra.RightComodule

/-!
## Inclusions and maps defined on a direct sum

The canonical inclusions are right-colinear, and every family of right-colinear
maps to one specified right comodule extends to the direct sum. The characteristic
linear-map equations describe these maps on each summand.
-/

universe uP

namespace Coalgebra.RightComoduleHom

variable {R : Type uR} {C : Type uC} {I : Type uI} {M : I → Type uM}
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

/-- The canonical inclusion of one specified right comodule into their direct sum. -/
noncomputable def lof (X : ∀ i, RightComodule R C (M i)) (i : I) :
    RightComoduleHom (X i) (RightComodule.directSum X) where
  toLinearMap := RightComodule.directSumLof R M i
  colinear := by
    exact RightComodule.directSum_coaction_comp_lof X i

/-- The underlying linear map of the inclusion is the canonical direct-sum inclusion. -/
@[simp] theorem lof_toLinearMap (X : ∀ i, RightComodule R C (M i)) (i : I) :
    (lof X i).toLinearMap = RightComodule.directSumLof R M i := rfl

section Desc

variable {P : Type uP} [AddCommMonoid P] [Module R P]
variable {X : ∀ i, RightComodule R C (M i)} {Z : RightComodule R C P}

private theorem desc_colinear [DecidableEq I]
    (φ : ∀ i, RightComoduleHom (X i) Z) :
    Z.coaction ∘ₗ DirectSum.toModule R I P (fun i => (φ i).toLinearMap) =
      (DirectSum.toModule R I P (fun i => (φ i).toLinearMap)).rTensor C ∘ₗ
        (RightComodule.directSum X).coaction := by
  let L := DirectSum.toModule R I P (fun i => (φ i).toLinearMap)
  change Z.coaction ∘ₗ L = L.rTensor C ∘ₗ (RightComodule.directSum X).coaction
  apply DirectSum.linearMap_ext
  intro i
  let j := DirectSum.lof R I M i
  have hL : L ∘ₗ j = (φ i).toLinearMap := by
    ext m
    simp only [L, j, LinearMap.comp_apply, DirectSum.toModule_lof]
  have hρ : (RightComodule.directSum X).coaction ∘ₗ j =
      j.rTensor C ∘ₗ (X i).coaction := by
    simpa only [RightComodule.directSumLof_eq_lof] using
      RightComodule.directSum_coaction_comp_lof X i
  change (Z.coaction ∘ₗ L) ∘ₗ j =
    (L.rTensor C ∘ₗ (RightComodule.directSum X).coaction) ∘ₗ j
  calc
    (Z.coaction ∘ₗ L) ∘ₗ j = Z.coaction ∘ₗ (φ i).toLinearMap := by
      simp only [LinearMap.comp_assoc, hL]
    _ = (φ i).toLinearMap.rTensor C ∘ₗ (X i).coaction := (φ i).colinear
    _ = (L ∘ₗ j).rTensor C ∘ₗ (X i).coaction := by rw [hL]
    _ = L.rTensor C ∘ₗ j.rTensor C ∘ₗ (X i).coaction := by
      rw [LinearMap.rTensor_comp, LinearMap.comp_assoc]
    _ = (L.rTensor C ∘ₗ (RightComodule.directSum X).coaction) ∘ₗ j := by
      simp only [LinearMap.comp_assoc, hρ]

/-- Extend a family of right-colinear maps to the direct sum of their sources. -/
noncomputable def desc (φ : ∀ i, RightComoduleHom (X i) Z) :
    RightComoduleHom (RightComodule.directSum X) Z where
  toLinearMap := by
    classical
    exact DirectSum.toModule R I P (fun i => (φ i).toLinearMap)
  colinear := by
    classical
    exact desc_colinear φ

/-- The underlying map of the extension restricts to the supplied map on each summand. -/
theorem desc_toLinearMap_comp_lof (φ : ∀ i, RightComoduleHom (X i) Z) (i : I) :
    (desc φ).toLinearMap ∘ₗ RightComodule.directSumLof R M i = (φ i).toLinearMap := by
  classical
  ext m
  simp only [desc, RightComodule.directSumLof_eq_lof, LinearMap.comp_apply,
    DirectSum.toModule_lof]

/-- The characteristic equation of the extension evaluated on a summand element. -/
theorem desc_toLinearMap_lof (φ : ∀ i, RightComoduleHom (X i) Z)
    (i : I) (m : M i) :
    (desc φ).toLinearMap (RightComodule.directSumLof R M i m) = (φ i).toLinearMap m :=
  LinearMap.congr_fun (desc_toLinearMap_comp_lof φ i) m

/-- The underlying extension is the canonical linear map for any index decision procedure. -/
theorem desc_toLinearMap [DecidableEq I] (φ : ∀ i, RightComoduleHom (X i) Z) :
    (desc φ).toLinearMap = DirectSum.toModule R I P (fun i => (φ i).toLinearMap) := by
  apply DirectSum.linearMap_ext
  intro i
  calc
    (desc φ).toLinearMap ∘ₗ DirectSum.lof R I M i = (φ i).toLinearMap := by
      simpa only [RightComodule.directSumLof_eq_lof] using desc_toLinearMap_comp_lof φ i
    _ = DirectSum.toModule R I P (fun i => (φ i).toLinearMap) ∘ₗ
        DirectSum.lof R I M i := by
      ext m
      simp only [LinearMap.comp_apply, DirectSum.toModule_lof]

end Desc

end Coalgebra.RightComoduleHom

/-!
## The coproduct universal property

Restriction to the canonical inclusions and extension from a family of maps are
mutually inverse. This gives a plain equivalence of types of right-comodule maps,
natural in the target, without placing finite-support conditions on the family.
-/

universe uQ

namespace Coalgebra.RightComoduleHom

variable {R : Type uR} {C : Type uC} {I : Type uI} {M : I → Type uM}
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

section UniversalProperty

variable {P : Type uP} [AddCommMonoid P] [Module R P]
variable {X : ∀ i, RightComodule R C (M i)} {Z : RightComodule R C P}

/-- The extension factors the supplied map through each canonical inclusion. -/
@[simp] theorem desc_comp_lof (φ : ∀ i, RightComoduleHom (X i) Z) (i : I) :
    (desc φ).comp (lof X i) = φ i := by
  apply RightComoduleHom.ext
  intro m
  exact desc_toLinearMap_lof φ i m

/-- The extension evaluated at an element of one summand. -/
theorem desc_lof_apply (φ : ∀ i, RightComoduleHom (X i) Z) (i : I) (m : M i) :
    desc φ (lof X i m) = φ i m :=
  desc_toLinearMap_lof φ i m

/-- Maps from a direct sum are determined by their values on the summands. -/
theorem directSum_ext_apply {f g : RightComoduleHom (RightComodule.directSum X) Z}
    (h : ∀ i m, f (lof X i m) = g (lof X i m)) : f = g := by
  apply RightComoduleHom.ext
  intro d
  have hlinear : f.toLinearMap = g.toLinearMap := by
    classical
    apply DirectSum.linearMap_ext
    intro i
    apply LinearMap.ext
    intro m
    have hi : f.toLinearMap (RightComodule.directSumLof R M i m) =
        g.toLinearMap (RightComodule.directSumLof R M i m) := h i m
    simpa only [LinearMap.comp_apply, RightComodule.directSumLof_eq_lof] using hi
  exact LinearMap.congr_fun hlinear d

/-- Maps from a direct sum are determined by their composites with the inclusions. -/
@[ext] theorem directSum_ext {f g : RightComoduleHom (RightComodule.directSum X) Z}
    (h : ∀ i, f.comp (lof X i) = g.comp (lof X i)) : f = g := by
  apply directSum_ext_apply
  intro i m
  simpa only [comp_apply] using
    congrArg (fun k : RightComoduleHom (X i) Z => k m) (h i)

/-- The extension is the unique map factoring a given family through the inclusions. -/
theorem desc_unique (φ : ∀ i, RightComoduleHom (X i) Z)
    (f : RightComoduleHom (RightComodule.directSum X) Z)
    (h : ∀ i, f.comp (lof X i) = φ i) : f = desc φ := by
  apply directSum_ext
  intro i
  rw [desc_comp_lof, h i]

/-- Every map from a direct sum is recovered from all its restrictions. -/
@[simp] theorem desc_eta (f : RightComoduleHom (RightComodule.directSum X) Z) :
    desc (fun i => f.comp (lof X i)) = f := by
  exact (desc_unique (fun i => f.comp (lof X i)) f (fun i => rfl)).symm

/-- Restricting an extension recovers the entire supplied family. -/
theorem desc_comp_lof_family (φ : ∀ i, RightComoduleHom (X i) Z) :
    (fun i => (desc φ).comp (lof X i)) = φ := by
  funext i
  exact desc_comp_lof φ i

/-- The extension of the zero family is zero. -/
@[simp] theorem desc_zero :
    desc (fun i => (0 : RightComoduleHom (X i) Z)) = 0 := by
  apply directSum_ext_apply
  intro i m
  simp only [desc_lof_apply, zero_apply]

/-- Maps from a direct sum correspond to arbitrary families of maps from its summands. -/
noncomputable def directSumEquiv (X : ∀ i, RightComodule R C (M i))
    (Z : RightComodule R C P) :
    RightComoduleHom (RightComodule.directSum X) Z ≃ (∀ i, RightComoduleHom (X i) Z) where
  toFun f := fun i => f.comp (lof X i)
  invFun φ := desc φ
  left_inv f := desc_eta f
  right_inv φ := desc_comp_lof_family φ

/-- The coproduct equivalence restricts a map to the indicated summand. -/
@[simp] theorem directSumEquiv_apply
    (f : RightComoduleHom (RightComodule.directSum X) Z) (i : I) :
    directSumEquiv X Z f i = f.comp (lof X i) := rfl

/-- The inverse coproduct equivalence extends a family of maps. -/
@[simp] theorem directSumEquiv_symm_apply (φ : ∀ i, RightComoduleHom (X i) Z) :
    (directSumEquiv X Z).symm φ = desc φ := rfl

end UniversalProperty

/-- Extending the family of canonical inclusions gives the identity map. -/
@[simp] theorem desc_lof (X : ∀ i, RightComodule R C (M i)) :
    desc (fun i => lof X i) = id (RightComodule.directSum X) := by
  apply directSum_ext
  intro i
  rw [desc_comp_lof, id_comp]

section Naturality

variable {P : Type uP} {Q : Type uQ}
variable [AddCommMonoid P] [Module R P] [AddCommMonoid Q] [Module R Q]
variable {X : ∀ i, RightComodule R C (M i)}
variable {Z : RightComodule R C P} {W : RightComodule R C Q}

/-- Postcomposition commutes with extension from a family. -/
theorem comp_desc (g : RightComoduleHom Z W) (φ : ∀ i, RightComoduleHom (X i) Z) :
    g.comp (desc φ) = desc (fun i => g.comp (φ i)) := by
  apply directSum_ext
  intro i
  simp only [comp_assoc, desc_comp_lof]

/-- The coproduct equivalence is natural under postcomposition in its target. -/
theorem directSumEquiv_natural (g : RightComoduleHom Z W)
    (f : RightComoduleHom (RightComodule.directSum X) Z) :
    directSumEquiv X W (g.comp f) = fun i => g.comp (directSumEquiv X Z f i) := by
  funext i
  simpa only [directSumEquiv_apply] using comp_assoc g f (lof X i)

end Naturality

end Coalgebra.RightComoduleHom
