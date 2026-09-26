/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.Extensive

/-!
# Finite coproduct squares in extensive categories

This file records a componentwise pullback property of the map between two
finite coproducts induced by a family of morphisms.
-/

public section

open CategoryTheory Limits

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- In a finitary extensive category, the square formed by one component of a
map between finite coproducts and the corresponding coproduct inclusions is a
pullback. -/
lemma FinitaryExtensive.isPullback_sigmaMap_ι [FinitaryExtensive C]
    {ι : Type*} [Finite ι] (X Y : ι → C) (f : ∀ i, X i ⟶ Y i) (i : ι) :
    IsPullback (Sigma.ι X i) (f i) (Limits.Sigma.map f) (Sigma.ι Y i) := by
  let cX : Cofan X := Cofan.mk _ (Sigma.ι X)
  let cY : Cofan Y := Cofan.mk _ (Sigma.ι Y)
  have h := FinitaryExtensive.isVanKampen_finiteCoproducts
    (coproductIsCoproduct Y)
  apply (h cX (Discrete.natTrans fun i ↦ f i.as) (Limits.Sigma.map f) (by aesop_cat)
    (.of_discrete _)).mp ⟨coproductIsCoproduct X⟩ ⟨i⟩

end CategoryTheory
