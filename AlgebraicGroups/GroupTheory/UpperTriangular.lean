/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Basic
public import TauCeti.Algebra.AlgebraicGroup.UpperUnitriangular.Scheme
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.SchemePoints
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# Native upper-triangular general linear groups

Invertible upper-triangular matrices form a subgroup of the matrix general
linear group over every commutative ring. Their diagonal is a split quotient
with kernel the existing upper-unitriangular subgroup *inside this subgroup*.
The U-first semidirect equivalence uses column normalization and commutes
with every ring homomorphism, including noninjective ones. This is a result
about groups of points, not a scheme base-change theorem.

## References

* J. S. Milne, *Algebraic Groups* (2017), item 2.9, p. 42:
  the `T_n`, `U_n` and `D_n` subgroup functors on commutative algebras.
  The arbitrary-ring U-first semidirect equivalence is proved here, not
  attributed to this item.
* Mathlib, `Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean` for
  matrix units and coefficient maps, and
  `Mathlib/LinearAlgebra/Matrix/Block.lean` for triangular matrix products,
  inverses and determinants.
* Mathlib, `Mathlib/Algebra/Group/Subgroup/Ker.lean` for homomorphism kernels,
  `Mathlib/GroupTheory/Subgroup/Centralizer.lean` for conjugation on a
  normalizer, `Mathlib/Algebra/Group/End.lean` for `MulAut.congr`, and
  `Mathlib/GroupTheory/SemidirectProduct.lean` for `lift` and Thomas
  Browning's `map` construction.
* `TauCeti/LinearAlgebra/Matrix/GeneralLinearGroup/UpperTriangular/Basic.lean`
  and `TauCeti/Algebra/AlgebraicGroup/UpperUnitriangular/Scheme.lean` supply
  the canonical diagonal and unitriangular groups.
-/

@[expose] public section

noncomputable section

universe u v

namespace TauCeti.UpperTriangularGroup

open Matrix

variable {ι : Type v} [Fintype ι] [LinearOrder ι]
variable {R S : Type u} [CommRing R] [CommRing S]

/-- Coefficient change commutes with the subgroup inclusion. -/
theorem inclusion_map (f : R →+* S) (g : upperUnitriangularGroup ι R) :
    map f (Subgroup.inclusion upperUnitriangularGroup_le_upperTriangularGroup g) =
      Subgroup.inclusion upperUnitriangularGroup_le_upperTriangularGroup
        (UpperUnitriangularGroup.map f g) := by
  apply Subtype.ext
  simp only [coe_map, Subgroup.coe_inclusion, UpperUnitriangularGroup.coe_map]

/-- The diagonal projection commutes with entrywise coefficient change. -/
theorem diag_map (f : R →+* S) (g : upperTriangularGroup ι R) :
    diag (map f g) = fun i ↦ Units.map f.toMonoidHom (diag g i) := by
  funext i
  apply Units.ext
  simp only [diag_apply_val, map_apply, Units.coe_map]
  rfl

/-- The diagonal section commutes with entrywise coefficient change. -/
theorem diagonalHom_map (f : R →+* S) (d : ι → Rˣ) :
    map f (diagonalHom d) = diagonalHom (fun i ↦ Units.map f.toMonoidHom (d i)) := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  simp only [coe_map, coe_diagonalHom, Matrix.GeneralLinearGroup.map_apply,
    TauCeti.diagGL_apply, Units.coe_map]
  split_ifs <;> simp_all

/-- The upper-unitriangular group is the kernel of the diagonal projection. -/
def kernelEquiv : upperUnitriangularGroup ι R ≃* (diag (m := ι) (R := R)).ker where
  toFun g := ⟨Subgroup.inclusion upperUnitriangularGroup_le_upperTriangularGroup g,
    diag_eq_one_iff.mpr g.2⟩
  invFun g := ⟨g.1.1, diag_eq_one_iff.mp g.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp]
theorem diag_inclusion (g : upperUnitriangularGroup ι R) :
    diag (Subgroup.inclusion upperUnitriangularGroup_le_upperTriangularGroup g) = 1 :=
  diag_eq_one_iff.mpr g.2

/-- Diagonal conjugation on the existing unitriangular group, transported
through Mathlib's normalizer action and `MulAut.congr`. The entrywise weight
is `dᵢ * uᵢⱼ * dⱼ⁻¹`; normality in all of GL is not claimed. -/
def diagonalAction : (ι → Rˣ) →* MulAut (upperUnitriangularGroup ι R) :=
  (MulAut.congr (kernelEquiv (ι := ι) (R := R)).symm).toMonoidHom.comp
    (((diag (m := ι) (R := R)).ker.normalizerMonoidHom).comp
      ((diagonalHom (m := ι) (R := R)).codRestrict _
        (fun _ => by simp only [Subgroup.normalizer_eq_top, Subgroup.mem_top])))

/-- The action is conjugation inside the actual upper-triangular matrix group. -/
theorem inUpperTriangular_diagonalAction (d : (ι → Rˣ))
    (unit : upperUnitriangularGroup ι R) :
    (Subgroup.inclusion upperUnitriangularGroup_le_upperTriangularGroup) (diagonalAction d unit) =
      diagonalHom d * (Subgroup.inclusion upperUnitriangularGroup_le_upperTriangularGroup) unit *
        (diagonalHom d)⁻¹ := by
  rfl

/-- Recover the unitriangular factor by column normalization. -/
def unipotentPart (matrix : upperTriangularGroup ι R) : upperUnitriangularGroup ι R :=
  (kernelEquiv (ι := ι) (R := R)).symm
    ⟨matrix * (diagonalHom (diag matrix))⁻¹, by
      apply MonoidHom.mem_ker.mpr
      simp⟩

theorem inUpperTriangular_unipotentPart (matrix : upperTriangularGroup ι R) :
    (Subgroup.inclusion upperUnitriangularGroup_le_upperTriangularGroup) (unipotentPart matrix) =
      matrix * (diagonalHom (diag matrix))⁻¹ := by
  rfl

@[simp] theorem unipotentPart_factor (matrix : upperTriangularGroup ι R) :
    (Subgroup.inclusion upperUnitriangularGroup_le_upperTriangularGroup) (unipotentPart matrix) *
      diagonalHom (diag matrix) = matrix := by
  rw [inUpperTriangular_unipotentPart]
  exact mul_inv_cancel_right matrix _

/-- The U-first product map, whose multiplication uses diag conjugation. -/
def semidirHom :
    (upperUnitriangularGroup ι R ⋊[diagonalAction (ι := ι) (R := R)] (ι → Rˣ)) →*
      upperTriangularGroup ι R :=
  SemidirectProduct.lift (Subgroup.inclusion upperUnitriangularGroup_le_upperTriangularGroup)
    diagonalHom (by
    intro d
    apply MonoidHom.ext
    intro unit
    exact inUpperTriangular_diagonalAction d unit)

@[simp] theorem semidirHom_apply
    (coords : upperUnitriangularGroup ι R ⋊[diagonalAction (ι := ι) (R := R)]
      (ι → Rˣ)) :
    semidirHom coords = (Subgroup.inclusion upperUnitriangularGroup_le_upperTriangularGroup)
      coords.left *
      diagonalHom coords.right := rfl

theorem diagonal_semidirHom
    (coords : upperUnitriangularGroup ι R ⋊[diagonalAction (ι := ι) (R := R)]
      (ι → Rˣ)) : diag (semidirHom coords) = coords.right := by
  rw [semidirHom_apply, map_mul, diag_inclusion, diag_diagonalHom, one_mul]

/-- Every upper-triangular matrix factors uniquely as a unitriangular matrix
times its diag. Mathlib's `SemidirectProduct.lift` encodes the U-first
product with diag conjugation; the inverse is column normalization.
Milne, *Algebraic Groups* (2017), item 2.9 describes the subgroup functors,
not this arbitrary-ring splitting of their point groups. -/
def semidirEquiv :
    (upperUnitriangularGroup ι R ⋊[diagonalAction (ι := ι) (R := R)] (ι → Rˣ)) ≃*
      upperTriangularGroup ι R :=
  MulEquiv.ofBijective semidirHom (by
    constructor
    · intro left right equal
      have diagEqual : left.right = right.right := by
        have mapped := congrArg diag equal
        simpa using mapped
      have unitEqual : left.left = right.left := by
        apply Subgroup.inclusion_injective upperUnitriangularGroup_le_upperTriangularGroup
        have canceled := congrArg
          (fun matrix : upperTriangularGroup ι R => matrix *
            (diagonalHom left.right)⁻¹) equal
        simpa [semidirHom_apply, diagEqual, mul_assoc] using canceled
      exact SemidirectProduct.ext unitEqual diagEqual
    · intro matrix
      refine ⟨⟨unipotentPart matrix, diag matrix⟩, ?_⟩
      exact unipotentPart_factor matrix)

@[simp] theorem semidirEquiv_apply
    (coords : upperUnitriangularGroup ι R ⋊[diagonalAction (ι := ι) (R := R)]
      (ι → Rˣ)) :
    semidirEquiv coords = (Subgroup.inclusion upperUnitriangularGroup_le_upperTriangularGroup)
      coords.left *
      diagonalHom coords.right := rfl

@[simp] theorem semidirEquiv_symm_left (matrix : upperTriangularGroup ι R) :
    (semidirEquiv.symm matrix).left = unipotentPart matrix := by
  apply Subgroup.inclusion_injective upperUnitriangularGroup_le_upperTriangularGroup
  have factor := congrArg (fun value : upperTriangularGroup ι R =>
      value * (diagonalHom (diag matrix))⁻¹)
    (semidirEquiv.apply_symm_apply matrix)
  have diagEq : (semidirEquiv.symm matrix).right = diag matrix := by
    have mapped := congrArg diag (semidirEquiv.apply_symm_apply matrix)
    simpa only [semidirEquiv_apply, map_mul, diag_inclusion,
      diag_diagonalHom, one_mul] using mapped
  rw [semidirEquiv_apply, diagEq, mul_inv_cancel_right] at factor
  exact factor.trans (inUpperTriangular_unipotentPart matrix).symm

@[simp] theorem semidirEquiv_symm_right (matrix : upperTriangularGroup ι R) :
    (semidirEquiv.symm matrix).right = diag matrix := by
  have mapped := congrArg diag (semidirEquiv.apply_symm_apply matrix)
  simpa only [semidirEquiv_apply, map_mul, diag_inclusion,
    diag_diagonalHom, one_mul] using mapped

/-- Column normalization uses the unit in the *column* of the input matrix. -/
theorem unipotentPart_apply (matrix : upperTriangularGroup ι R) (row col : ι) :
    (unipotentPart matrix).1 row col = matrix.1 row col *
      (((diag matrix col)⁻¹ : Rˣ) : R) := by
  have entry := congrArg (fun value : upperTriangularGroup ι R => value.1 row col)
    (inUpperTriangular_unipotentPart matrix)
  simp only [Subgroup.coe_inclusion, Subgroup.coe_mul, Subgroup.coe_inv,
    coe_diagonalHom] at entry
  rw [← map_inv (TauCeti.diagGL (ι := ι) (k := R))] at entry
  simpa only [Units.val_mul, TauCeti.diagGL_coe, Matrix.mul_diagonal,
    Pi.inv_apply] using entry

/-- The conjugation action has the expected two-sided scalar weight. -/
theorem diagonalAction_apply (d : (ι → Rˣ))
    (unit : upperUnitriangularGroup ι R) (row col : ι) :
    (diagonalAction d unit).1 row col =
      (d row : Rˣ) * unit.1 row col *
        (((d col)⁻¹ : Rˣ) : R) := by
  have acted := congrArg (fun value : upperTriangularGroup ι R => value.1 row col)
    (inUpperTriangular_diagonalAction d unit)
  simp only [Subgroup.coe_inclusion, Subgroup.coe_mul, Subgroup.coe_inv,
    coe_diagonalHom] at acted
  rw [← map_inv (TauCeti.diagGL (ι := ι) (k := R))] at acted
  simpa only [Units.val_mul, TauCeti.diagGL_coe, Matrix.mul_diagonal,
    Matrix.diagonal_mul, Pi.inv_apply] using acted

/-- Entrywise maps commute with column normalization, without assuming injectivity. -/
theorem unipotentPart_map (ringHom : R →+* S) (matrix : upperTriangularGroup ι R) :
    UpperUnitriangularGroup.map ringHom (unipotentPart matrix) =
      unipotentPart (map ringHom matrix) := by
  apply Subgroup.inclusion_injective upperUnitriangularGroup_le_upperTriangularGroup
  calc
    (Subgroup.inclusion upperUnitriangularGroup_le_upperTriangularGroup)
      (UpperUnitriangularGroup.map ringHom
        (unipotentPart matrix)) =
        map ringHom ((Subgroup.inclusion upperUnitriangularGroup_le_upperTriangularGroup)
          (unipotentPart matrix)) :=
      (inclusion_map ringHom _).symm
    _ = map ringHom matrix *
        (diagonalHom (diag (map ringHom matrix)))⁻¹ := by
      rw [inUpperTriangular_unipotentPart, map_mul]
      simp [map_inv, diagonalHom_map, diag_map]
    _ = (Subgroup.inclusion upperUnitriangularGroup_le_upperTriangularGroup) (unipotentPart (map
      ringHom matrix)) :=
      (inUpperTriangular_unipotentPart _).symm

/-- Native diag conjugation commutes with every ring homomorphism. -/
theorem diagonalAction_map (ringHom : R →+* S) (d : (ι → Rˣ))
    (unit : upperUnitriangularGroup ι R) :
    UpperUnitriangularGroup.map ringHom (diagonalAction d unit) =
      diagonalAction ((fun i ↦ Units.map ringHom.toMonoidHom (d i))) (UpperUnitriangularGroup.map
        ringHom unit) := by
  apply Subgroup.inclusion_injective upperUnitriangularGroup_le_upperTriangularGroup
  calc
    (Subgroup.inclusion upperUnitriangularGroup_le_upperTriangularGroup)
      (UpperUnitriangularGroup.map ringHom
        (diagonalAction d unit)) =
        map ringHom ((Subgroup.inclusion upperUnitriangularGroup_le_upperTriangularGroup)
          (diagonalAction d unit)) :=
      (inclusion_map ringHom _).symm
    _ = diagonalHom ((fun i ↦ Units.map ringHom.toMonoidHom (d i))) *
        (Subgroup.inclusion upperUnitriangularGroup_le_upperTriangularGroup)
          (UpperUnitriangularGroup.map ringHom unit) *
          (diagonalHom ((fun i ↦ Units.map ringHom.toMonoidHom (d i))))⁻¹ := by
      rw [inUpperTriangular_diagonalAction, map_mul, map_mul, map_inv,
        diagonalHom_map, inclusion_map]
    _ = (Subgroup.inclusion upperUnitriangularGroup_le_upperTriangularGroup)
        (diagonalAction ((fun i ↦ Units.map ringHom.toMonoidHom (d i)))
          (UpperUnitriangularGroup.map ringHom unit)) :=
      (inUpperTriangular_diagonalAction _ _).symm

/-- The natural coefficient-change map of U-first semidirect products. -/
def semidirMap (ringHom : R →+* S) :
    (upperUnitriangularGroup ι R ⋊[diagonalAction (ι := ι) (R := R)] (ι → Rˣ)) →*
      (upperUnitriangularGroup ι S ⋊[diagonalAction (ι := ι) (R := S)] (ι → Sˣ)) :=
  SemidirectProduct.map (UpperUnitriangularGroup.map ringHom) (MonoidHom.pi fun i ↦ (Units.map
    ringHom.toMonoidHom).comp (Pi.evalMonoidHom _ i)) (by
    intro d
    apply MonoidHom.ext
    intro unit
    exact diagonalAction_map ringHom d unit)

theorem semidirEquiv_map (ringHom : R →+* S)
    (coords : upperUnitriangularGroup ι R ⋊[diagonalAction (ι := ι) (R := R)]
      (ι → Rˣ)) :
    map ringHom (semidirEquiv coords) = semidirEquiv (semidirMap ringHom coords) := by
  simp [semidirEquiv_apply, semidirMap, map_mul, diagonalHom_map,
    inclusion_map]
  rfl

theorem semidirEquiv_symm_map (ringHom : R →+* S)
    (matrix : upperTriangularGroup ι R) :
    semidirMap ringHom (semidirEquiv.symm matrix) =
      semidirEquiv.symm (map ringHom matrix) := by
  apply (semidirEquiv (ι := ι) (R := S)).injective
  rw [semidirEquiv.apply_symm_apply, ← semidirEquiv_map,
    semidirEquiv.apply_symm_apply]

theorem semidirEquiv_inl (unit : upperUnitriangularGroup ι R) :
    semidirEquiv (SemidirectProduct.inl unit) =
      (Subgroup.inclusion upperUnitriangularGroup_le_upperTriangularGroup) unit := by
  simp [semidirEquiv_apply]

theorem semidirEquiv_inr (d : (ι → Rˣ)) :
    semidirEquiv (SemidirectProduct.inr d) = diagonalHom d := by
  simp [semidirEquiv_apply]

theorem semidirEquiv_mul_formula (first second :
    upperUnitriangularGroup ι R ⋊[diagonalAction (ι := ι) (R := R)] (ι → Rˣ)) :
    (Subgroup.inclusion upperUnitriangularGroup_le_upperTriangularGroup) first.left * diagonalHom
      first.right *
      ((Subgroup.inclusion upperUnitriangularGroup_le_upperTriangularGroup) second.left *
        diagonalHom second.right) =
    (Subgroup.inclusion upperUnitriangularGroup_le_upperTriangularGroup)
        (first.left * diagonalAction first.right second.left) *
      diagonalHom (first.right * second.right) := by
  simpa only [← semidirEquiv_apply, ← SemidirectProduct.mul_left,
    ← SemidirectProduct.mul_right] using (semidirEquiv.map_mul first second).symm

end TauCeti.UpperTriangularGroup
