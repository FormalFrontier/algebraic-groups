/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AlgebraicGroups.Algebra.HopfAlgebra.Ideal
import AlgebraicGroups.Algebra.Bialgebra.Quotient

/-!
# Extended augmentation quotients along the original maps

For `C → A → B`, extension of the counit kernel of `C` gives Hopf ideals in
`A` and `B`. The quotient Hopf structures and the induced bialgebra map below
are inherited from those original algebras and maps. The representative formula
is checked through the ordinary algebra quotient lift.
-/

universe uK uC uA uB

noncomputable section

variable {K : Type uK} {C : Type uC} {A : Type uA} {B : Type uB}
  [CommRing K] [Ring C] [CommRing A] [CommRing B]
  [HopfAlgebra K C] [HopfAlgebra K A] [HopfAlgebra K B]
  (i : C →ₐc[K] A) (f : A →ₐc[K] B)

local notation "I" => RingHom.ker (AlgHom.toRingHom (Bialgebra.counitAlgHom K C))
local notation "JA" => Ideal.map (AlgHom.toRingHom (BialgHom.toAlgHom i)) I
local notation "JB" =>
  Ideal.map (AlgHom.toRingHom (BialgHom.toAlgHom (BialgHom.comp f i))) I

local instance : Ideal.IsHopfIdeal K JA :=
  (Bialgebra.counit_ker_isHopfIdeal (K := K) (A := C)).map i

local instance : Ideal.IsHopfIdeal K JB :=
  (Bialgebra.counit_ker_isHopfIdeal (K := K) (A := C)).map (f.comp i)

-- These are the full quotient structures, not separately assumed Hopf algebras.
example : HopfAlgebra K (A ⧸ JA) := inferInstance
example : HopfAlgebra K (B ⧸ JB) := inferInstance

/-- The original map induces the full quotient map, with the usual formula on
representatives. There is no surjectivity or finiteness hypothesis. -/
example : ∃ d : (A ⧸ JA) →ₐc[K] (B ⧸ JB),
    ∀ a : A, d (Ideal.Quotient.mk JA a) = Ideal.Quotient.mk JB (f a) := by
  let q := Bialgebra.Quotient.mkBialgHom (R := K) JB
  have h : JA ≤ RingHom.ker (q.comp f).toAlgHom.toRingHom := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨c, hc, rfl⟩
    change Ideal.Quotient.mk JB (f (i c)) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hc)
  refine ⟨Bialgebra.Quotient.liftBialgHom JA (q.comp f) h, ?_⟩
  intro a
  change (Bialgebra.Quotient.liftBialgHom JA (q.comp f) h).toAlgHom
    (Ideal.Quotient.mk JA a) = Ideal.Quotient.mk JB (f a)
  rw [Bialgebra.Quotient.liftBialgHom_toAlgHom]
  rfl
