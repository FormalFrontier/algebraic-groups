/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.GroupLikeHom
public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.Dual
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.RingTheory.HopfAlgebra.GroupLike
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra

/-!
# A nontrivial group-like line over the natural numbers

The group algebra `ℕ[Multiplicative ℤ]` has a group-like unit supported at `1 : ℤ`.
Its antipode is supported at `-1 : ℤ`, so the two characters are distinct even
though both are invertible. The line is obtained from the public scalar comodule
by changing its coacting coalgebra. A tensor unitor followed by a coefficient
map reads its character back from its actual coaction. The canonical dual
coaction is the existing inverse-character line on the stock module dual.
Contraction readback distinguishes it from zero, the trivial character, and
the original character. Evaluation and coevaluation characters cancel in
their respective fixed orders.
-/

public noncomputable section

open TensorProduct

namespace RightComoduleDualTest

abbrev G := Multiplicative ℤ
abbrev C := MonoidAlgebra ℕ G
abbrev D := Module.Dual ℕ ℕ

/-- The positive generator of the infinite cyclic group. -/
def t : G := Multiplicative.ofAdd 1

/-- The monomial character at the positive generator, with its stock proof of
being group-like. -/
def g : GroupLike ℕ C :=
  ⟨MonoidAlgebra.single t 1, MonoidAlgebra.isGroupLikeElem_single_one t⟩

theorem g_isGroupLike : IsGroupLikeElem ℕ g.val := g.isGroupLikeElem_val

/-- This character is a unit, as every group-like element of a Hopf algebra is. -/
theorem g_isUnit : IsUnit g.val := g_isGroupLike.isUnit

private theorem int_one_ne_neg_one : (1 : ℤ) ≠ -1 := by decide

private theorem t_ne_inv : t ≠ t⁻¹ := by
  change (1 : ℤ) ≠ -1
  exact int_one_ne_neg_one

private theorem t_ne_one : t ≠ 1 := by decide

/-- The antipode inverts the support of the monomial. -/
theorem antipode_g : HopfAlgebra.antipode ℕ g.val =
    MonoidAlgebra.single t⁻¹ 1 := by
  simp [g, MonoidAlgebra.antipode_single]

/-- In additive integer coordinates the inverse support is `-1`. -/
theorem antipode_g_ofAdd : HopfAlgebra.antipode ℕ g.val =
    MonoidAlgebra.single (Multiplicative.ofAdd (-1 : ℤ)) 1 := by
  simpa only [t, ofAdd_neg] using antipode_g

/-- Coefficient at the positive generator. -/
def coefficientAtT : C →ₗ[ℕ] ℕ where
  toFun c := c.coeff t
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem coefficientAtT_apply (c : C) :
    coefficientAtT c = c.coeff t := rfl

@[simp] theorem coefficientAtT_g : coefficientAtT g.val = 1 := by
  simp only [coefficientAtT_apply, g, MonoidAlgebra.coeff_single,
    Finsupp.single_eq_same]

@[simp] theorem coefficientAtT_antipode_g :
    coefficientAtT (HopfAlgebra.antipode ℕ g.val) = 0 := by
  rw [antipode_g]
  rw [coefficientAtT_apply, MonoidAlgebra.coeff_single]
  exact Finsupp.single_eq_of_ne t_ne_inv

@[simp] theorem coefficientAtT_one : coefficientAtT 1 = 0 := by
  rw [MonoidAlgebra.one_def]
  rw [coefficientAtT_apply, MonoidAlgebra.coeff_single]
  exact Finsupp.single_eq_of_ne t_ne_one

theorem g_ne_zero : g.val ≠ 0 := by
  intro h
  have hcoeff := congrArg coefficientAtT h
  simp at hcoeff

theorem g_ne_one : g.val ≠ 1 := by
  intro h
  have hcoeff := congrArg coefficientAtT h
  simp at hcoeff

/-- The coefficient at `t` distinguishes the antipode from the original
character; in particular omitting the antipode changes this line. -/
theorem antipode_g_ne_g : HopfAlgebra.antipode ℕ g.val ≠ g.val := by
  intro h
  have hcoeff := congrArg coefficientAtT h
  simp at hcoeff

/-- The evaluation character, in its fixed order. -/
theorem antipode_g_mul_g : HopfAlgebra.antipode ℕ g.val * g.val = 1 :=
  g_isGroupLike.antipode_mul_cancel

/-- The coevaluation character, in its fixed order. -/
theorem g_mul_antipode_g : g.val * HopfAlgebra.antipode ℕ g.val = 1 :=
  g_isGroupLike.mul_antipode_cancel

/-- A group-like line formed using the existing scalar and coalgebra-change APIs. -/
def line (h : GroupLike ℕ C) : Coalgebra.RightComodule ℕ C ℕ :=
  (Coalgebra.RightComodule.scalar ℕ ℕ).mapCoalgebra (GroupLike.coalgHomEquiv h)

@[simp] theorem line_coaction (h : GroupLike ℕ C) (r : ℕ) :
    (line h).coaction r = r ⊗ₜ[ℕ] h.val := by
  simp [line, LinearMap.lTensor_tmul]

/-- The same existing construction for the inverse character on the stock dual. -/
def inverseDualLine : Coalgebra.RightComodule ℕ C D :=
  (Coalgebra.RightComodule.scalar ℕ D).mapCoalgebra (GroupLike.coalgHomEquiv g⁻¹)

@[simp] theorem inverseDualLine_coaction (f : D) :
    inverseDualLine.coaction f = f ⊗ₜ[ℕ] HopfAlgebra.antipode ℕ g.val := by
  simp [inverseDualLine, LinearMap.lTensor_tmul]

/-- The usual scalar functional on the stock dual of `ℕ`. -/
def functional (a : ℕ) : D := a • LinearMap.id

@[simp] theorem functional_apply (a r : ℕ) : functional a r = a * r := by
  simp [functional, smul_eq_mul]

/-- Read the coefficient at `t` after the genuine left tensor unitor. -/
def tensorCoefficient : ℕ ⊗[ℕ] C →ₗ[ℕ] ℕ :=
  coefficientAtT ∘ₗ (TensorProduct.lid ℕ C).toLinearMap

private theorem tensorCoefficient_apply (z : ℕ ⊗[ℕ] C) :
    tensorCoefficient z = coefficientAtT ((TensorProduct.lid ℕ C) z) := rfl

@[simp] theorem tensorCoefficient_tmul (r : ℕ) (c : C) :
    tensorCoefficient (r ⊗ₜ[ℕ] c) = r * coefficientAtT c := by
  rw [tensorCoefficient_apply, TensorProduct.lid_tmul, map_smul, smul_eq_mul]

/-- Reading the actual positive-character coaction gives back its scalar. -/
@[simp] theorem tensorCoefficient_coaction (r : ℕ) :
    tensorCoefficient ((line g).coaction r) = r := by
  simp

/-- Reading the actual inverse-character coaction at `t` gives zero. -/
@[simp] theorem tensorCoefficient_inverse_coaction (r : ℕ) :
    tensorCoefficient ((line g⁻¹).coaction r) = 0 := by
  simp

/-- The positive-character coaction at `1` is not zero. -/
theorem coaction_one_ne_zero : (line g).coaction 1 ≠ 0 := by
  intro h
  have hcoeff := congrArg tensorCoefficient h
  simp at hcoeff

/-- The positive-character coaction is not the trivial-character coaction. -/
theorem coaction_one_ne_trivial : (line g).coaction 1 ≠ 1 ⊗ₜ[ℕ] (1 : C) := by
  intro h
  have hcoeff := congrArg tensorCoefficient h
  simp at hcoeff

/-- The same unitor/coefficient readback distinguishes inverse and original
characters on their actual stock coactions. -/
theorem inverse_coaction_one_ne_coaction_one :
    (line g⁻¹).coaction 1 ≠ (line g).coaction 1 := by
  intro h
  have hcoeff := congrArg tensorCoefficient h
  simp at hcoeff

/-- The dual coaction of the specified line has the inverse character. -/
@[simp] theorem dualCoaction_line (f : D) :
    Coalgebra.RightComodule.dualCoaction (line g) f =
      f ⊗ₜ[ℕ] HopfAlgebra.antipode ℕ g.val :=
  Coalgebra.RightComodule.dualCoaction_eq_tmul_of_coaction_eq_tmul
    (line g) g.val (line_coaction g) f

/-- In particular, this is the dual coaction of the functional `r ↦ a * r`. -/
theorem dualCoaction_functional (a : ℕ) :
    Coalgebra.RightComodule.dualCoaction (line g) (functional a) =
      functional a ⊗ₜ[ℕ] HopfAlgebra.antipode ℕ g.val :=
  dualCoaction_line (functional a)

/-- The already-existing inverse-character comodule realizes the canonical raw
coaction on the very same stock dual module. -/
theorem inverseDualLine_coaction_eq_dualCoaction :
    inverseDualLine.coaction = Coalgebra.RightComodule.dualCoaction (line g) := by
  ext f
  rw [inverseDualLine_coaction, dualCoaction_line]

/-- The inverse-character line is the canonical bundled dual on the stock dual. -/
theorem inverseDualLine_eq_dual :
    inverseDualLine = Coalgebra.RightComodule.dual (line g) := by
  apply Coalgebra.RightComodule.eq_dual_of_characteristic (line g) inverseDualLine
  intro f r
  rw [inverseDualLine_coaction_eq_dualCoaction]
  exact Coalgebra.RightComodule.dualCoaction_characteristic (line g) f r

/-- Read a dual tensor by the stock tensor--Hom contraction, evaluated at `1`. -/
def dualReadback : D ⊗[ℕ] C →ₗ[ℕ] C where
  toFun z := dualTensorHom ℕ ℕ C z 1
  map_add' _ _ := by simp
  map_smul' a z := by
    rw [map_smul, LinearMap.smul_apply]
    rfl

private theorem dualReadback_apply (z : D ⊗[ℕ] C) :
    dualReadback z = dualTensorHom ℕ ℕ C z 1 := rfl

@[simp] theorem dualReadback_tmul (f : D) (c : C) :
    dualReadback (f ⊗ₜ[ℕ] c) = f 1 • c := by
  rw [dualReadback_apply, dualTensorHom_apply]

@[simp] theorem dualReadback_dualCoaction_functional (a : ℕ) :
    dualReadback (Coalgebra.RightComodule.dualCoaction (line g) (functional a)) =
      a • HopfAlgebra.antipode ℕ g.val := by
  simp

/-- Contraction of the bundled dual coaction reads the inverse character on `D`. -/
@[simp] theorem dualReadback_dual_coaction_functional (a : ℕ) :
    dualReadback ((Coalgebra.RightComodule.dual (line g)).coaction (functional a)) =
      a • HopfAlgebra.antipode ℕ g.val := by
  rw [← inverseDualLine_eq_dual]
  simp

/-- Genuine contraction readback rules out the zero dual coaction. -/
theorem dualCoaction_functional_one_ne_zero :
    Coalgebra.RightComodule.dualCoaction (line g) (functional 1) ≠ 0 := by
  intro h
  have hread : HopfAlgebra.antipode ℕ g.val = 0 := by
    simpa using congrArg dualReadback h
  have hchar := antipode_g_mul_g
  rw [hread, zero_mul] at hchar
  exact zero_ne_one hchar

/-- The canonical dual is not the trivial-character line. -/
theorem dualCoaction_functional_one_ne_trivial :
    Coalgebra.RightComodule.dualCoaction (line g) (functional 1) ≠
      functional 1 ⊗ₜ[ℕ] (1 : C) := by
  intro h
  have hread : HopfAlgebra.antipode ℕ g.val = 1 := by
    simpa using congrArg dualReadback h
  apply g_ne_one
  calc
    g.val = HopfAlgebra.antipode ℕ g.val * g.val := by rw [hread, one_mul]
    _ = 1 := antipode_g_mul_g

/-- Omitting the antipode is detected by contraction of the actual canonical
coaction, followed by the coefficient distinction at `t`. -/
theorem dualCoaction_functional_one_ne_original :
    Coalgebra.RightComodule.dualCoaction (line g) (functional 1) ≠
      functional 1 ⊗ₜ[ℕ] g.val := by
  intro h
  apply antipode_g_ne_g
  simpa using congrArg dualReadback h

/-- Evaluation contracts the canonical dual coaction and then multiplies the
characters in the order `Sg * g`. -/
theorem evaluation_character (a r : ℕ) :
    dualTensorHom ℕ ℕ C
      (Coalgebra.RightComodule.dualCoaction (line g) (functional a)) r * g.val =
        (a * r) • (1 : C) := by
  rw [dualCoaction_functional]
  change ((functional a) r • HopfAlgebra.antipode ℕ g.val) * g.val =
    (a * r) • (1 : C)
  rw [functional_apply, smul_mul_assoc, antipode_g_mul_g]

/-- The coevaluation character uses the opposite fixed order `g * Sg`. -/
theorem coevaluation_character (a r : ℕ) :
    g.val * dualTensorHom ℕ ℕ C
      (Coalgebra.RightComodule.dualCoaction (line g) (functional a)) r =
        (a * r) • (1 : C) := by
  rw [dualCoaction_functional]
  change g.val * ((functional a) r • HopfAlgebra.antipode ℕ g.val) =
    (a * r) • (1 : C)
  rw [functional_apply, mul_smul_comm, g_mul_antipode_g]

end RightComoduleDualTest
