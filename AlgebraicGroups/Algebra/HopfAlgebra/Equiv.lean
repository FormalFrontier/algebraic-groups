/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.Equiv
public import AlgebraicGroups.Algebra.TensorProduct.Maps
public import Mathlib.RingTheory.HopfAlgebra.Basic

/-!
# Transport of bialgebras and Hopf algebras

A scalar equivalence `σ : R ≃+* S` and a ring equivalence `e : A ≃+* B`
which commute with the algebra maps transport a bialgebra or Hopf algebra on `B`
to the given `R`-algebra `A`. The four universes are independent.

The semilinear equivalence uses the modules induced by the given algebras. Its
tensor square is Mathlib's `TensorProduct.congr`. The coalgebra laws are supplied
by `LinearEquiv.coalgebraOfRingEquiv`; the additional multiplicativity and
antipode laws are transported along the ring equivalence. In particular, the
algebra structure on `A` is not transported or replaced.

The constructions have separate bialgebra, antipode-data and full Hopf-algebra
interfaces. `HopfAlgebraStruct` already includes all bialgebra laws.
-/

@[expose] public section

universe uR uS uA uB

open scoped TensorProduct

namespace RingEquiv

-- Use the coercion to ring homomorphisms, as in the semilinear coalgebra transport.
-- The canonical inverse-pair lemmas are stated with these coercions, not `toRingHom`.
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

section Algebra

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}
variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]
variable [α : Algebra R A] [β : Algebra S B]

/-- An equivalence commuting with the algebra maps is semilinear over the
specified scalar equivalence, on the modules induced by the given algebras. -/
def semilinearEquivOfAlgebraMap (σ : R ≃+* S) (e : A ≃+* B)
    (h : ∀ r, e (algebraMap R A r) = algebraMap S B (σ r)) :
    @LinearEquiv R S _ _ (σ : R →+* S) (σ.symm : S →+* R)
      (RingHomInvPair.of_ringEquiv σ) (RingHomInvPair.of_ringEquiv_symm σ)
      A B _ _ (@Algebra.toModule R A _ _ α) (@Algebra.toModule S B _ _ β) :=
  @LinearEquiv.mk R S _ _ (σ : R →+* S) (σ.symm : S →+* R)
    (RingHomInvPair.of_ringEquiv σ) (RingHomInvPair.of_ringEquiv_symm σ)
    A B _ _ (@Algebra.toModule R A _ _ α) (@Algebra.toModule S B _ _ β)
    { toFun := e
      map_add' := e.map_add
      map_smul' := fun r a => by
        simp only [Algebra.smul_def, map_mul, h, RingEquiv.coe_toRingHom] }
    e.symm e.symm_apply_apply e.apply_symm_apply

/-- The semilinear equivalence acts by the given ring equivalence. -/
@[simp]
theorem semilinearEquivOfAlgebraMap_apply (σ : R ≃+* S) (e : A ≃+* B)
    (h : ∀ r, e (algebraMap R A r) = algebraMap S B (σ r)) (a : A) :
    semilinearEquivOfAlgebraMap σ e h a = e a := rfl

/-- Its inverse acts by the inverse ring equivalence. -/
@[simp]
theorem semilinearEquivOfAlgebraMap_symm_apply (σ : R ≃+* S) (e : A ≃+* B)
    (h : ∀ r, e (algebraMap R A r) = algebraMap S B (σ r)) (b : B) :
    (semilinearEquivOfAlgebraMap σ e h).symm b = e.symm b := rfl

/-- The tensor square of the scalar-compatible semilinear equivalence. -/
def tensorProductCongrOfAlgebraMap (σ : R ≃+* S) (e : A ≃+* B)
    (h : ∀ r, e (algebraMap R A r) = algebraMap S B (σ r)) :
    @LinearEquiv R S _ _ (σ : R →+* S) (σ.symm : S →+* R)
      (RingHomInvPair.of_ringEquiv σ) (RingHomInvPair.of_ringEquiv_symm σ)
      (A ⊗[R] A) (B ⊗[S] B) _ _ _ _ :=
  @TensorProduct.congr R S _ _ (σ : R →+* S) A A B B _ _ _ _
    (@Algebra.toModule R A _ _ α) (@Algebra.toModule R A _ _ α)
    (@Algebra.toModule S B _ _ β) (@Algebra.toModule S B _ _ β)
    (σ.symm : S →+* R) (RingHomInvPair.of_ringEquiv σ)
    (RingHomInvPair.of_ringEquiv_symm σ)
    (semilinearEquivOfAlgebraMap σ e h) (semilinearEquivOfAlgebraMap σ e h)

/-- The tensor equivalence is exactly the tensor square of the induced semilinear map. -/
@[simp]
theorem tensorProductCongrOfAlgebraMap_toLinearMap (σ : R ≃+* S) (e : A ≃+* B)
    (h : ∀ r, e (algebraMap R A r) = algebraMap S B (σ r)) :
    (tensorProductCongrOfAlgebraMap σ e h).toLinearMap =
      TensorProduct.map (semilinearEquivOfAlgebraMap σ e h).toLinearMap
        (semilinearEquivOfAlgebraMap σ e h).toLinearMap := rfl

/-- The tensor equivalence applies the ring equivalence to both factors. -/
@[simp]
theorem tensorProductCongrOfAlgebraMap_tmul (σ : R ≃+* S) (e : A ≃+* B)
    (h : ∀ r, e (algebraMap R A r) = algebraMap S B (σ r)) (a a' : A) :
    tensorProductCongrOfAlgebraMap σ e h (a ⊗ₜ[R] a') = e a ⊗ₜ[S] e a' := rfl

/-- The inverse tensor equivalence applies the inverse ring equivalence to both factors. -/
@[simp]
theorem tensorProductCongrOfAlgebraMap_symm_tmul (σ : R ≃+* S) (e : A ≃+* B)
    (h : ∀ r, e (algebraMap R A r) = algebraMap S B (σ r)) (b b' : B) :
    (tensorProductCongrOfAlgebraMap σ e h).symm (b ⊗ₜ[S] b') =
      e.symm b ⊗ₜ[R] e.symm b' := rfl

/-- The scalar-changing tensor equivalence preserves multiplication. -/
theorem tensorProductCongrOfAlgebraMap_mul (σ : R ≃+* S) (e : A ≃+* B)
    (h : ∀ r, e (algebraMap R A r) = algebraMap S B (σ r)) (x y : A ⊗[R] A) :
    tensorProductCongrOfAlgebraMap σ e h (x * y) =
      tensorProductCongrOfAlgebraMap σ e h x * tensorProductCongrOfAlgebraMap σ e h y := by
  exact (tensorProductCongrOfAlgebraMap σ e h).toLinearMap.toAddMonoidHom.map_mul_of_map_mul_tmul
    (fun a₁ a₂ b₁ b₂ => by
      change tensorProductCongrOfAlgebraMap σ e h ((a₁ * a₂) ⊗ₜ[R] (b₁ * b₂)) =
        tensorProductCongrOfAlgebraMap σ e h (a₁ ⊗ₜ[R] b₁) *
          tensorProductCongrOfAlgebraMap σ e h (a₂ ⊗ₜ[R] b₂)
      simp only [tensorProductCongrOfAlgebraMap_tmul, map_mul,
        Algebra.TensorProduct.tmul_mul_tmul]) x y

/-- The scalar-changing tensor equivalence preserves the unit. -/
@[simp]
theorem tensorProductCongrOfAlgebraMap_one (σ : R ≃+* S) (e : A ≃+* B)
    (h : ∀ r, e (algebraMap R A r) = algebraMap S B (σ r)) :
    tensorProductCongrOfAlgebraMap σ e h 1 = 1 := by
  simp only [Algebra.TensorProduct.one_def, tensorProductCongrOfAlgebraMap_tmul, map_one]

/-- The inverse tensor equivalence preserves multiplication. -/
theorem tensorProductCongrOfAlgebraMap_symm_mul (σ : R ≃+* S) (e : A ≃+* B)
    (h : ∀ r, e (algebraMap R A r) = algebraMap S B (σ r)) (x y : B ⊗[S] B) :
    (tensorProductCongrOfAlgebraMap σ e h).symm (x * y) =
      (tensorProductCongrOfAlgebraMap σ e h).symm x *
        (tensorProductCongrOfAlgebraMap σ e h).symm y := by
  apply (tensorProductCongrOfAlgebraMap σ e h).injective
  simp only [LinearEquiv.apply_symm_apply, tensorProductCongrOfAlgebraMap_mul]

/-- The inverse tensor equivalence preserves the unit. -/
@[simp]
theorem tensorProductCongrOfAlgebraMap_symm_one (σ : R ≃+* S) (e : A ≃+* B)
    (h : ∀ r, e (algebraMap R A r) = algebraMap S B (σ r)) :
    (tensorProductCongrOfAlgebraMap σ e h).symm 1 = 1 := by
  apply (tensorProductCongrOfAlgebraMap σ e h).injective
  simp only [LinearEquiv.apply_symm_apply, tensorProductCongrOfAlgebraMap_one]

end Algebra

section Bialgebra

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}
variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]
variable [α : Algebra R A] [Bialgebra S B]

/-- Pull back a bialgebra along scalar and carrier equivalences, retaining the
given algebra on the source carrier. -/
@[instance_reducible]
def bialgebra (σ : R ≃+* S) (e : A ≃+* B)
    (h : ∀ r, e (algebraMap R A r) = algebraMap S B (σ r)) : Bialgebra R A := by
  let E := semilinearEquivOfAlgebraMap σ e h
  let C : Coalgebra R A := LinearEquiv.coalgebraOfRingEquiv σ E
  exact @Bialgebra.mk' R A _ _ α C
    (by
      change σ.symm (Coalgebra.counit (R := S) (e 1)) = 1
      simp only [map_one, Bialgebra.counit_one])
    (by
      intro a b
      change σ.symm (Coalgebra.counit (R := S) (e (a * b))) =
        σ.symm (Coalgebra.counit (R := S) (e a)) *
          σ.symm (Coalgebra.counit (R := S) (e b))
      simp only [map_mul, Bialgebra.counit_mul])
    (by
      change (tensorProductCongrOfAlgebraMap σ e h).symm
        (Coalgebra.comul (R := S) (e 1)) = 1
      simp only [map_one, Bialgebra.comul_one, tensorProductCongrOfAlgebraMap_symm_one])
    (by
      intro a b
      change (tensorProductCongrOfAlgebraMap σ e h).symm
          (Coalgebra.comul (R := S) (e (a * b))) =
        (tensorProductCongrOfAlgebraMap σ e h).symm
            (Coalgebra.comul (R := S) (e a)) *
          (tensorProductCongrOfAlgebraMap σ e h).symm
            (Coalgebra.comul (R := S) (e b))
      simp only [map_mul, Bialgebra.comul_mul,
        tensorProductCongrOfAlgebraMap_symm_mul])

/-- The transported bialgebra retains the given algebra parent. -/
@[simp]
theorem bialgebra_toAlgebra (σ : R ≃+* S) (e : A ≃+* B)
    (h : ∀ r, e (algebraMap R A r) = algebraMap S B (σ r)) :
    (bialgebra σ e h).toAlgebra = α := rfl

/-- The coalgebra parent is the full semilinear coalgebra pullback. -/
@[simp]
theorem bialgebra_toCoalgebra (σ : R ≃+* S) (e : A ≃+* B)
    (h : ∀ r, e (algebraMap R A r) = algebraMap S B (σ r)) :
    (bialgebra σ e h).toCoalgebra =
      LinearEquiv.coalgebraOfRingEquiv σ (semilinearEquivOfAlgebraMap σ e h) := rfl

/-- The induced module is exactly the module of the given algebra. -/
theorem bialgebra_toModule (σ : R ≃+* S) (e : A ≃+* B)
    (h : ∀ r, e (algebraMap R A r) = algebraMap S B (σ r)) :
    @Algebra.toModule R A _ _ (bialgebra σ e h).toAlgebra =
      @Algebra.toModule R A _ _ α := rfl

/-- The transported counit is the target counit followed by inverse scalar change. -/
@[simp]
theorem bialgebra_counit_apply (σ : R ≃+* S) (e : A ≃+* B)
    (h : ∀ r, e (algebraMap R A r) = algebraMap S B (σ r)) (a : A) :
    @CoalgebraStruct.counit R A _ _ _ (bialgebra σ e h).toCoalgebra.toCoalgebraStruct a =
      σ.symm (Coalgebra.counit (R := S) (e a)) := rfl

/-- The transported comultiplication is conjugation by the induced tensor equivalence. -/
theorem bialgebra_comul_apply (σ : R ≃+* S) (e : A ≃+* B)
    (h : ∀ r, e (algebraMap R A r) = algebraMap S B (σ r)) (a : A) :
    @CoalgebraStruct.comul R A _ _ _ (bialgebra σ e h).toCoalgebra.toCoalgebraStruct a =
      (tensorProductCongrOfAlgebraMap σ e h).symm (Coalgebra.comul (R := S) (e a)) := rfl

/-- The induced tensor equivalence intertwines the two comultiplications. -/
theorem tensorProductCongr_bialgebra_comul (σ : R ≃+* S) (e : A ≃+* B)
    (h : ∀ r, e (algebraMap R A r) = algebraMap S B (σ r)) (a : A) :
    tensorProductCongrOfAlgebraMap σ e h
        (@CoalgebraStruct.comul R A _ _ _ (bialgebra σ e h).toCoalgebra.toCoalgebraStruct a) =
      Coalgebra.comul (R := S) (e a) :=
  (tensorProductCongrOfAlgebraMap σ e h).apply_symm_apply _

end Bialgebra

section HopfAlgebraStruct

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}
variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]
variable [α : Algebra R A] [HopfAlgebraStruct S B]

/-- The antipode conjugated by the scalar-compatible carrier equivalence. -/
def antipodeOfRingEquiv (σ : R ≃+* S) (e : A ≃+* B)
    (h : ∀ r, e (algebraMap R A r) = algebraMap S B (σ r)) : A →ₗ[R] A := by
  let inv : RingHomInvPair (σ : R →+* S) (σ.symm : S →+* R) :=
    RingHomInvPair.of_ringEquiv σ
  let inv' : RingHomInvPair (σ.symm : S →+* R) (σ : R →+* S) :=
    RingHomInvPair.of_ringEquiv_symm σ
  let E : A ≃ₛₗ[(σ : R →+* S)] B := semilinearEquivOfAlgebraMap σ e h
  exact E.symm.toLinearMap ∘ₛₗ HopfAlgebra.antipode S ∘ₛₗ E.toLinearMap

/-- The conjugated antipode on an element. -/
@[simp]
theorem antipodeOfRingEquiv_apply (σ : R ≃+* S) (e : A ≃+* B)
    (h : ∀ r, e (algebraMap R A r) = algebraMap S B (σ r)) (a : A) :
    antipodeOfRingEquiv σ e h a = e.symm (HopfAlgebra.antipode S (e a)) := rfl

/-- Transport bialgebra and antipode data; no antipode laws on the target are required. -/
@[instance_reducible]
def hopfAlgebraStruct (σ : R ≃+* S) (e : A ≃+* B)
    (h : ∀ r, e (algebraMap R A r) = algebraMap S B (σ r)) : HopfAlgebraStruct R A :=
  @HopfAlgebraStruct.mk R A _ _ (bialgebra (α := α) σ e h)
    (antipodeOfRingEquiv (α := α) σ e h)

/-- The bialgebra parent is exactly the bialgebra pullback. -/
@[simp]
theorem hopfAlgebraStruct_toBialgebra (σ : R ≃+* S) (e : A ≃+* B)
    (h : ∀ r, e (algebraMap R A r) = algebraMap S B (σ r)) :
    (hopfAlgebraStruct σ e h).toBialgebra = bialgebra σ e h := rfl

/-- The antipode data are exactly the conjugated antipode. -/
@[simp]
theorem hopfAlgebraStruct_antipode (σ : R ≃+* S) (e : A ≃+* B)
    (h : ∀ r, e (algebraMap R A r) = algebraMap S B (σ r)) :
    @HopfAlgebraStruct.antipode R A _ _ (hopfAlgebraStruct σ e h) =
      antipodeOfRingEquiv σ e h := rfl

private theorem mul_antipode_rTensor_transport (σ : R ≃+* S) (e : A ≃+* B)
    (h : ∀ r, e (algebraMap R A r) = algebraMap S B (σ r)) (x : A ⊗[R] A) :
    e (LinearMap.mul' R A ((antipodeOfRingEquiv σ e h).rTensor A x)) =
      LinearMap.mul' S B ((HopfAlgebra.antipode S).rTensor B
        (tensorProductCongrOfAlgebraMap σ e h x)) := by
  induction x with
  | tmul a b =>
    change e (e.symm (HopfAlgebra.antipode S (e a)) * b) =
      HopfAlgebra.antipode S (e a) * e b
    rw [map_mul, e.apply_symm_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem mul_antipode_lTensor_transport (σ : R ≃+* S) (e : A ≃+* B)
    (h : ∀ r, e (algebraMap R A r) = algebraMap S B (σ r)) (x : A ⊗[R] A) :
    e (LinearMap.mul' R A ((antipodeOfRingEquiv σ e h).lTensor A x)) =
      LinearMap.mul' S B ((HopfAlgebra.antipode S).lTensor B
        (tensorProductCongrOfAlgebraMap σ e h x)) := by
  induction x with
  | tmul a b =>
    change e (a * e.symm (HopfAlgebra.antipode S (e b))) =
      e a * HopfAlgebra.antipode S (e b)
    rw [map_mul, e.apply_symm_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

end HopfAlgebraStruct

section HopfAlgebra

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}
variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]
variable [α : Algebra R A] [HopfAlgebra S B]

/-- Pull back a Hopf algebra along compatible scalar and carrier equivalences.
The algebra parent on the source carrier is the given algebra. -/
@[instance_reducible]
def hopfAlgebra (σ : R ≃+* S) (e : A ≃+* B)
    (h : ∀ r, e (algebraMap R A r) = algebraMap S B (σ r)) : HopfAlgebra R A := by
  letI H : HopfAlgebraStruct R A := hopfAlgebraStruct (α := α) σ e h
  refine @HopfAlgebra.mk R A _ _ H ?_ ?_
  · apply LinearMap.ext
    intro a
    apply e.injective
    change e (LinearMap.mul' R A
        ((antipodeOfRingEquiv σ e h).rTensor A (Coalgebra.comul (R := R) a))) =
      e (algebraMap R A (Coalgebra.counit (R := R) a))
    rw [(private_decl% (mul_antipode_rTensor_transport
        (R := R) (S := S) (A := A) (B := B) (α := α) σ e h)),
      tensorProductCongr_bialgebra_comul,
      HopfAlgebra.mul_antipode_rTensor_comul_apply, h, bialgebra_counit_apply,
      σ.apply_symm_apply]
  · apply LinearMap.ext
    intro a
    apply e.injective
    change e (LinearMap.mul' R A
        ((antipodeOfRingEquiv σ e h).lTensor A (Coalgebra.comul (R := R) a))) =
      e (algebraMap R A (Coalgebra.counit (R := R) a))
    rw [(private_decl% (mul_antipode_lTensor_transport
        (R := R) (S := S) (A := A) (B := B) (α := α) σ e h)),
      tensorProductCongr_bialgebra_comul,
      HopfAlgebra.mul_antipode_lTensor_comul_apply, h, bialgebra_counit_apply,
      σ.apply_symm_apply]

/-- The full Hopf structure has exactly the transported antipode-data parent. -/
@[simp]
theorem hopfAlgebra_toHopfAlgebraStruct (σ : R ≃+* S) (e : A ≃+* B)
    (h : ∀ r, e (algebraMap R A r) = algebraMap S B (σ r)) :
    (hopfAlgebra σ e h).toHopfAlgebraStruct = hopfAlgebraStruct σ e h := rfl

/-- The full Hopf pullback retains the original algebra. -/
@[simp]
theorem hopfAlgebra_toAlgebra (σ : R ≃+* S) (e : A ≃+* B)
    (h : ∀ r, e (algebraMap R A r) = algebraMap S B (σ r)) :
    (hopfAlgebra σ e h).toBialgebra.toAlgebra = α := rfl

/-- The full Hopf pullback uses the original algebra-induced module. -/
theorem hopfAlgebra_toModule (σ : R ≃+* S) (e : A ≃+* B)
    (h : ∀ r, e (algebraMap R A r) = algebraMap S B (σ r)) :
    @Algebra.toModule R A _ _ (hopfAlgebra σ e h).toBialgebra.toAlgebra =
      @Algebra.toModule R A _ _ α := rfl

/-- The full Hopf pullback has the chosen full coalgebra parent. -/
@[simp]
theorem hopfAlgebra_toCoalgebra (σ : R ≃+* S) (e : A ≃+* B)
    (h : ∀ r, e (algebraMap R A r) = algebraMap S B (σ r)) :
    (hopfAlgebra σ e h).toBialgebra.toCoalgebra =
      LinearEquiv.coalgebraOfRingEquiv σ (semilinearEquivOfAlgebraMap σ e h) := rfl

/-- The counit of the full Hopf pullback changes scalars by the inverse equivalence. -/
@[simp]
theorem hopfAlgebra_counit_apply (σ : R ≃+* S) (e : A ≃+* B)
    (h : ∀ r, e (algebraMap R A r) = algebraMap S B (σ r)) (a : A) :
    @CoalgebraStruct.counit R A _ _ _
        (hopfAlgebra σ e h).toBialgebra.toCoalgebra.toCoalgebraStruct a =
      σ.symm (Coalgebra.counit (R := S) (e a)) := rfl

/-- The full Hopf comultiplication is conjugation by the induced tensor equivalence. -/
theorem hopfAlgebra_comul_apply (σ : R ≃+* S) (e : A ≃+* B)
    (h : ∀ r, e (algebraMap R A r) = algebraMap S B (σ r)) (a : A) :
    @CoalgebraStruct.comul R A _ _ _
        (hopfAlgebra σ e h).toBialgebra.toCoalgebra.toCoalgebraStruct a =
      (tensorProductCongrOfAlgebraMap σ e h).symm (Coalgebra.comul (R := S) (e a)) := rfl

/-- The full Hopf antipode is conjugation by the carrier equivalence. -/
@[simp]
theorem hopfAlgebra_antipode_apply (σ : R ≃+* S) (e : A ≃+* B)
    (h : ∀ r, e (algebraMap R A r) = algebraMap S B (σ r)) (a : A) :
    @HopfAlgebraStruct.antipode R A _ _ (hopfAlgebra σ e h).toHopfAlgebraStruct a =
      e.symm (HopfAlgebra.antipode S (e a)) := rfl

end HopfAlgebra

section FixedScalars

variable {R : Type uR} {A : Type uA} {B : Type uB}
variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A]

/-- At fixed scalars the induced semilinear equivalence is the algebra equivalence's
linear equivalence. -/
@[simp]
theorem semilinearEquivOfAlgebraMap_refl [Algebra R B] (e : A ≃ₐ[R] B) :
    semilinearEquivOfAlgebraMap (RingEquiv.refl R) e.toRingEquiv e.commutes =
      e.toLinearEquiv := rfl

/-- At fixed scalars the coalgebra parent agrees with Mathlib's linear pullback. -/
@[simp]
theorem bialgebra_refl_toCoalgebra [Bialgebra R B] (e : A ≃ₐ[R] B) :
    (bialgebra (RingEquiv.refl R) e.toRingEquiv e.commutes).toCoalgebra =
      e.toLinearEquiv.coalgebra R := rfl

end FixedScalars

end RingEquiv
