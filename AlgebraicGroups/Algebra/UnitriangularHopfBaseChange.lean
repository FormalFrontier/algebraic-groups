/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.UnitriangularBaseChange
public import Mathlib.RingTheory.HopfAlgebra.TensorProduct
public import Mathlib.RingTheory.HopfAlgebra.Convolution

/-!
# Hopf compatibility of unitriangular coordinate base change

The canonical scalar extension of the determinant-localized unitriangular Hopf
quotient is equivalent to the corresponding quotient over the new base. Both
bialgebra structures are their independently defined tensor-product and quotient
structures, not structures transported along the algebra equivalence.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u

namespace UnitriangularCoordinateRing

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (ι : Type u) [Fintype ι] [LinearOrder ι]

private theorem counit_entry (K : Type u) [CommRing K]
    (ι : Type u) [Fintype ι] [LinearOrder ι] (i j : ι) :
    Coalgebra.counit (R := K)
        (quotient K ι (GeneralLinearCoordinateRing.matrix K ι i j)) =
      (1 : Matrix ι ι K) i j := by
  change Coalgebra.counit (R := K)
      (Ideal.Quotient.mk (ideal K ι) (GeneralLinearCoordinateRing.matrix K ι i j)) = _
  rw [Bialgebra.Quotient.counit_mk, GeneralLinearCoordinateRing.native_counit_matrix]

/-- The canonical coproduct of every matrix entry in the actual quotient,
including diagonal and lower entries. -/
theorem comul_entry (K : Type u) [CommRing K]
    (ι : Type u) [Fintype ι] [LinearOrder ι] (i j : ι) :
    Coalgebra.comul (R := K)
        (quotient K ι (GeneralLinearCoordinateRing.matrix K ι i j)) =
      ∑ k : ι, quotient K ι (GeneralLinearCoordinateRing.matrix K ι i k) ⊗ₜ[K]
        quotient K ι (GeneralLinearCoordinateRing.matrix K ι k j) := by
  change Coalgebra.comul (R := K)
      (Ideal.Quotient.mk (ideal K ι) (GeneralLinearCoordinateRing.matrix K ι i j)) = _
  rw [Bialgebra.Quotient.comul_mk, GeneralLinearCoordinateRing.native_comul_matrix,
    map_sum]
  simp only [TensorProduct.map_tmul, AlgHom.toLinearMap_apply]
  rfl

private theorem algHom_ext_entries (B : Type u) [CommRing B] [Algebra S B]
    (f g : S ⊗[R] CoordinateRing R ι →ₐ[S] B)
    (h : ∀ p : StrictUpperPair ι,
      f (1 ⊗ₜ[R] quotient R ι
          (GeneralLinearCoordinateRing.matrix R ι p.1.1 p.1.2)) =
        g (1 ⊗ₜ[R] quotient R ι
          (GeneralLinearCoordinateRing.matrix R ι p.1.1 p.1.2))) : f = g := by
  letI : Algebra R B := Algebra.compHom B (algebraMap R S)
  letI : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  apply Algebra.TensorProduct.ext_ring
  have hp : ((f.restrictScalars R).comp Algebra.TensorProduct.includeRight).comp
        (freeEquiv R ι).toAlgHom =
      ((g.restrictScalars R).comp Algebra.TensorProduct.includeRight).comp
        (freeEquiv R ι).toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro p
    change f (1 ⊗ₜ[R] freeEquiv R ι (MvPolynomial.X p)) =
      g (1 ⊗ₜ[R] freeEquiv R ι (MvPolynomial.X p))
    rw [freeEquiv_variable]
    exact h p
  apply AlgHom.ext
  intro x
  obtain ⟨p, rfl⟩ := (freeEquiv R ι).surjective x
  exact congrArg (fun φ => φ p) hp

/-- The counit of the canonical scalar-extension bialgebra commutes with
base change of the actual unitriangular quotient. -/
theorem baseChange_counit :
    (Bialgebra.counitAlgHom S (CoordinateRing S ι)).comp
      (baseChange R S ι).toAlgHom =
    Bialgebra.counitAlgHom S (S ⊗[R] CoordinateRing R ι) := by
  apply algHom_ext_entries R S ι
  intro p
  change (Bialgebra.counitAlgHom S (CoordinateRing S ι))
      (baseChange R S ι (1 ⊗ₜ[R] quotient R ι
        (GeneralLinearCoordinateRing.matrix R ι p.1.1 p.1.2))) =
      (Bialgebra.counitAlgHom S (S ⊗[R] CoordinateRing R ι))
        (1 ⊗ₜ[R] quotient R ι
          (GeneralLinearCoordinateRing.matrix R ι p.1.1 p.1.2))
  rw [baseChange_tmul_entry, map_mul]
  simp only [map_one, one_mul]
  change Coalgebra.counit (R := S)
      (quotient S ι (GeneralLinearCoordinateRing.matrix S ι p.1.1 p.1.2)) =
    Coalgebra.counit (R := S)
      ((1 : S) ⊗ₜ[R] quotient R ι (GeneralLinearCoordinateRing.matrix R ι p.1.1 p.1.2))
  rw [TensorProduct.counit_tmul, counit_entry S ι,
    counit_entry R ι, CommSemiring.counit_apply]
  simp [ne_of_lt p.2]

/-- The comultiplication of the canonical tensor-product bialgebra commutes
with base change of the actual unitriangular quotient. -/
theorem baseChange_comul :
    (Algebra.TensorProduct.map (baseChange R S ι).toAlgHom
      (baseChange R S ι).toAlgHom).comp
        (Bialgebra.comulAlgHom S (S ⊗[R] CoordinateRing R ι)) =
    (Bialgebra.comulAlgHom S (CoordinateRing S ι)).comp
      (baseChange R S ι).toAlgHom := by
  apply algHom_ext_entries R S ι
    (CoordinateRing S ι ⊗[S] CoordinateRing S ι)
  intro p
  change (Algebra.TensorProduct.map (baseChange R S ι).toAlgHom
      (baseChange R S ι).toAlgHom)
      (Coalgebra.comul (R := S) ((1 : S) ⊗ₜ[R] quotient R ι
        (GeneralLinearCoordinateRing.matrix R ι p.1.1 p.1.2))) =
    Coalgebra.comul (R := S)
      (baseChange R S ι ((1 : S) ⊗ₜ[R] quotient R ι
        (GeneralLinearCoordinateRing.matrix R ι p.1.1 p.1.2)))
  rw [baseChange_tmul_entry, Bialgebra.comul_mul]
  simp only [map_one, one_mul, Bialgebra.comul_one]
  rw [comul_entry S ι p.1.1 p.1.2]
  rw [TensorProduct.comul_tmul, CommSemiring.comul_apply,
    comul_entry R ι p.1.1 p.1.2]
  simp only [TensorProduct.tmul_sum, map_sum, Algebra.TensorProduct.map_tmul,
    TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul]
  apply Finset.sum_congr rfl
  intro k _
  change baseChange R S ι
        ((1 : S) ⊗ₜ[R] quotient R ι (GeneralLinearCoordinateRing.matrix R ι p.1.1 k)) ⊗ₜ[S]
      baseChange R S ι
        ((1 : S) ⊗ₜ[R] quotient R ι (GeneralLinearCoordinateRing.matrix R ι k p.1.2)) =
    quotient S ι (GeneralLinearCoordinateRing.matrix S ι p.1.1 k) ⊗ₜ[S]
      quotient S ι (GeneralLinearCoordinateRing.matrix S ι k p.1.2)
  rw [baseChange_tmul_entry, baseChange_tmul_entry]
  simp only [map_one, one_mul]

set_option maxHeartbeats 1000000

/-- The published scalar-extension algebra equivalence respects the two
independently given bialgebra structures. -/
def baseChangeBialgEquiv :
    S ⊗[R] CoordinateRing R ι ≃ₐc[S] CoordinateRing S ι := by
  let sourceBialgebra : Bialgebra S (S ⊗[R] CoordinateRing R ι) := inferInstance
  let targetBialgebra : Bialgebra S (CoordinateRing S ι) := inferInstance
  let algebraTypes :
      (S ⊗[R] CoordinateRing R ι ≃ₐ[S] CoordinateRing S ι) =
        @AlgEquiv S (S ⊗[R] CoordinateRing R ι) (CoordinateRing S ι) (inferInstance)
          (inferInstance) (inferInstance) sourceBialgebra.toAlgebra
          targetBialgebra.toAlgebra := rfl
  let bialgebraTypes :
      (S ⊗[R] CoordinateRing R ι ≃ₐc[S] CoordinateRing S ι) =
        @BialgEquiv S (inferInstance) (S ⊗[R] CoordinateRing R ι) (CoordinateRing S ι)
          (inferInstance) (inferInstance) sourceBialgebra.toAlgebra
          targetBialgebra.toAlgebra sourceBialgebra.toCoalgebra.toCoalgebraStruct
          targetBialgebra.toCoalgebra.toCoalgebraStruct := rfl
  let algebraEquiv := algebraTypes.mp (baseChange R S ι)
  have algebraEquiv_eq : algebraEquiv = baseChange R S ι := by
    dsimp [algebraEquiv, algebraTypes]
  apply bialgebraTypes.mpr
  exact BialgEquiv.ofAlgEquiv algebraEquiv
    (by rw [algebraEquiv_eq]; exact baseChange_counit R S ι)
    (by rw [algebraEquiv_eq]; exact baseChange_comul R S ι)

@[simp] theorem baseChangeBialgEquiv_apply (x : S ⊗[R] CoordinateRing R ι) :
    baseChangeBialgEquiv R S ι x = baseChange R S ι x := rfl

private theorem bialgHom_antipode (K : Type*) [CommRing K]
    (A B : Type*) [CommRing A] [CommRing B]
    [HopfAlgebra K A] [HopfAlgebra K B]
    (f : A →ₐc[K] B) (x : A) :
    f (HopfAlgebra.antipode K x) = HopfAlgebra.antipode K (f x) := by
  open WithConv in
  let g : A →ₐ[K] B := f
  have hunit : ((1 : WithConv (B →ₐ[K] B)).ofConv.comp g) =
      (1 : WithConv (A →ₐ[K] B)).ofConv := by
    apply AlgHom.ext
    intro a
    change algebraMap K B (Coalgebra.counit (R := K) (f a)) =
      algebraMap K B (Coalgebra.counit (R := K) a)
    rw [CoalgHomClass.counit_comp_apply]
  have hleft : (WithConv.toConv ((HopfAlgebra.antipodeAlgHom K B).comp g) *
      WithConv.toConv g : WithConv (A →ₐ[K] B)) = 1 := by
    apply WithConv.ofConv_injective
    calc
      (WithConv.toConv ((HopfAlgebra.antipodeAlgHom K B).comp g) *
          WithConv.toConv g : WithConv (A →ₐ[K] B)).ofConv =
          ((WithConv.toConv (HopfAlgebra.antipodeAlgHom K B) *
            WithConv.toConv (AlgHom.id K B)) : WithConv (B →ₐ[K] B)).ofConv.comp g := by
            rw [AlgHom.convMul_comp_bialgHom_distrib]
            rfl
      _ = (1 : WithConv (B →ₐ[K] B)).ofConv.comp g := by
        rw [AlgHom.antipode_id_cancel]
      _ = (1 : WithConv (A →ₐ[K] B)).ofConv := hunit
  have hright : (WithConv.toConv g *
      WithConv.toConv (g.comp (HopfAlgebra.antipodeAlgHom K A)) :
        WithConv (A →ₐ[K] B)) = 1 := by
    change WithConv.toConv g * (WithConv.toConv g)⁻¹ = 1
    exact mul_inv_cancel _
  have heq : (HopfAlgebra.antipodeAlgHom K B).comp g =
      g.comp (HopfAlgebra.antipodeAlgHom K A) :=
    WithConv.toConv_injective (left_inv_eq_right_inv hleft hright)
  exact (AlgHom.congr_fun heq x).symm

/-- The antipodes of the existing scalar-extension and quotient Hopf algebras
intertwine under the published algebra base-change map. -/
theorem baseChange_antipode (x : S ⊗[R] CoordinateRing R ι) :
    baseChange R S ι
        ((@HopfAlgebraStruct.antipode S (S ⊗[R] CoordinateRing R ι)
          inferInstance inferInstance (inferInstance : HopfAlgebraStruct S
            (S ⊗[R] CoordinateRing R ι))) x) =
      (@HopfAlgebraStruct.antipode S (CoordinateRing S ι)
        inferInstance inferInstance (inferInstance : HopfAlgebraStruct S
          (CoordinateRing S ι))) (baseChange R S ι x) := by
  have hpoint (y : S ⊗[R] CoordinateRing R ι) :
      (baseChangeBialgEquiv R S ι).toBialgHom y = baseChange R S ι y :=
    baseChangeBialgEquiv_apply R S ι y
  have h := bialgHom_antipode S
    (S ⊗[R] CoordinateRing R ι) (CoordinateRing S ι)
    (baseChangeBialgEquiv R S ι).toBialgHom x
  simpa only [hpoint] using h

end UnitriangularCoordinateRing
