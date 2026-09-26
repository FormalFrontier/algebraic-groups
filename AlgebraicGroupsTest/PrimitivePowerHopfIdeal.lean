/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AlgebraicGroups.Algebra.PrimitivePowerHopfIdeal
import AlgebraicGroups.GroupScheme.Additive
import Mathlib.Data.ZMod.Basic

set_option warningAsError true

noncomputable section

open scoped TensorProduct

variable {K A : Type*} [CommRing K] [CommRing A] [HopfAlgebra K A]
  {p : ℕ} [Fact p.Prime] [CharP K p] {a : A}

private theorem persistentTestPrimitivePowerHopfIdeal001 (ha : Bialgebra.IsPrimitiveElem K a) (m : ℕ) :
    Ideal.IsHopfIdeal K (Ideal.span {a ^ (p ^ m)}) :=
  ha.isHopfIdeal_span_pow_char_pow m

private theorem persistentTestPrimitivePowerHopfIdeal002 (ha : Bialgebra.IsPrimitiveElem K a) :
    Ideal.IsHopfIdeal K (Ideal.span {a ^ (p ^ 0)}) :=
  ha.isHopfIdeal_span_pow_char_pow 0

private theorem persistentTestPrimitivePowerHopfIdeal003 (ha : Bialgebra.IsPrimitiveElem K a) :
    Ideal.IsHopfIdeal K (Ideal.span {a ^ (p ^ 1)}) :=
  ha.isHopfIdeal_span_pow_char_pow 1

private theorem persistentTestPrimitivePowerHopfIdeal004 (ha : Bialgebra.IsPrimitiveElem K a) :
    Ideal.IsHopfIdeal K (Ideal.span {a ^ (p ^ 2)}) :=
  ha.isHopfIdeal_span_pow_char_pow 2

private theorem persistentTestPrimitivePowerHopfIdeal005 (m : ℕ) : Ideal.IsHopfIdeal K (Ideal.span {(0 : A) ^ (p ^ m)}) := by
  have hzero : Bialgebra.IsPrimitiveElem K (0 : A) := by
    constructor <;> simp
  exact hzero.isHopfIdeal_span_pow_char_pow m

@[instance_reducible] private noncomputable def persistentTestPrimitivePowerHopfIdeal006 (ha : Bialgebra.IsPrimitiveElem K a) (m : ℕ) :
    HopfAlgebra K (A ⧸ Ideal.span {a ^ (p ^ m)}) := by
  letI : Ideal.IsHopfIdeal K (Ideal.span {a ^ (p ^ m)}) :=
    ha.isHopfIdeal_span_pow_char_pow m
  infer_instance

private theorem persistentTestPrimitivePowerHopfIdeal007 (K : Type*) [CommRing K] (B : Type*) [CommRing B] [Algebra K B]
    [Subsingleton B] (I : Ideal K) (f : (K ⧸ I) →ₐ[K] B) (x : K) :
    f (Ideal.Quotient.mk I x) = 0 := Subsingleton.elim _ _

private theorem persistentTestPrimitivePowerHopfIdeal008 (I : Ideal (ZMod 2)) (f : ((ZMod 2) ⧸ I) →ₐ[ZMod 2] PUnit)
    (x : ZMod 2) : f (Ideal.Quotient.mk I x) = 0 := Subsingleton.elim _ _

namespace SymmetricAlgebra

variable (K : Type*) [CommRing K] (M : Type*) [AddCommMonoid M] [Module K M]

private lemma primitive_ι (x : M) : Bialgebra.IsPrimitiveElem K (ι K M x) := by
  constructor
  · simp
  · simpa only [add_comm] using (comul_ι K M x)

#print axioms primitive_ι

private theorem persistentTestPrimitivePowerHopfIdeal009 [Fact (Nat.Prime 2)] [CharP K 2] (x : M) :
    Ideal.IsHopfIdeal K (Ideal.span {(ι K M x) ^ (2 ^ 2)}) :=
  (primitive_ι K M x).isHopfIdeal_span_pow_char_pow 2

private theorem persistentTestPrimitivePowerHopfIdeal010 [Fact (Nat.Prime 3)] [CharP K 3] (x : M) :
    Ideal.IsHopfIdeal K (Ideal.span {(ι K M x) ^ (3 ^ 1)}) :=
  (primitive_ι K M x).isHopfIdeal_span_pow_char_pow 1

end SymmetricAlgebra

namespace AlgebraicGeometry

variable (K : Type*) [CommRing K]

private lemma primitive_additiveGroupCoordinate :
    Bialgebra.IsPrimitiveElem K (additiveGroupCoordinate K) := by
  constructor
  · simp
  · simpa only [add_comm] using (additiveGroupCoordinate_comul K)

#print axioms primitive_additiveGroupCoordinate

private theorem persistentTestPrimitivePowerHopfIdeal011 [Fact (Nat.Prime 2)] [CharP K 2] :
    Ideal.IsHopfIdeal K (Ideal.span {(additiveGroupCoordinate K) ^ (2 ^ 0)}) :=
  (primitive_additiveGroupCoordinate K).isHopfIdeal_span_pow_char_pow 0

private theorem persistentTestPrimitivePowerHopfIdeal012 [Fact (Nat.Prime 2)] [CharP K 2] :
    Ideal.IsHopfIdeal K (Ideal.span {(additiveGroupCoordinate K) ^ (2 ^ 1)}) :=
  (primitive_additiveGroupCoordinate K).isHopfIdeal_span_pow_char_pow 1

private theorem persistentTestPrimitivePowerHopfIdeal013 [Fact (Nat.Prime 3)] [CharP K 3] :
    Ideal.IsHopfIdeal K (Ideal.span {(additiveGroupCoordinate K) ^ (3 ^ 2)}) :=
  (primitive_additiveGroupCoordinate K).isHopfIdeal_span_pow_char_pow 2

private theorem persistentTestPrimitivePowerHopfIdeal014 : Ideal.IsHopfIdeal (Polynomial (ZMod 2))
    (Ideal.span {(additiveGroupCoordinate (Polynomial (ZMod 2))) ^ (2 ^ 2)}) :=
  (primitive_additiveGroupCoordinate (Polynomial (ZMod 2))).isHopfIdeal_span_pow_char_pow 2

@[instance_reducible] private noncomputable def persistentTestPrimitivePowerHopfIdeal015 : HopfAlgebra (ZMod 3)
    (additiveGroupCoordinateRing (ZMod 3) ⧸
      Ideal.span {(additiveGroupCoordinate (ZMod 3)) ^ (3 ^ 2)}) := by
  letI : Ideal.IsHopfIdeal (ZMod 3)
      (Ideal.span {(additiveGroupCoordinate (ZMod 3)) ^ (3 ^ 2)}) :=
    (primitive_additiveGroupCoordinate (ZMod 3)).isHopfIdeal_span_pow_char_pow 2
  infer_instance

end AlgebraicGeometry

#print axioms Bialgebra.IsPrimitiveElem.isHopfIdeal_span_pow_char_pow
#print axioms Bialgebra.IsPrimitiveElem.antipode_eq_neg
#print axioms HopfAlgebra.antipodeAlgHom
#print axioms Commute.add_pow_prime_pow_eq'
#print axioms CharP.cast_eq_zero
#print axioms AlgebraicGeometry.additiveGroupCoordinate_comul
#print axioms AlgebraicGeometry.additiveGroupCoordinate_counit
#print axioms SymmetricAlgebra.comul_ι
#print axioms SymmetricAlgebra.counit_ι
#print axioms HopfAlgebra.Quotient.instQuotientIdeal
#print axioms Ideal.Quotient.eq_zero_iff_mem
#print axioms Ideal.mem_span_singleton'
