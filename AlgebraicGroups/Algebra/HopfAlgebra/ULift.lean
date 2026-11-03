/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.HopfAlgebra.Equiv
public import Mathlib.RingTheory.Bialgebra.Hom
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra

/-!
# Scalar and carrier lifts of Hopf algebras

Bialgebras, bialgebras with antipode data, and Hopf algebras can be lifted in both
the scalar and carrier universes independently. The algebra parent is precisely
`ULift.algebra'` applied to `ULift.algebra`, the parent used by `AlgHom.ulift`.
No lifted algebra or Hopf structure is installed as a global instance.

The characteristic formulas recover the original counit, comultiplication and
antipode by scalar and carrier down maps. The tensor down equivalences are
natural for `AlgHom.ulift`, which preserves identities and composition with
independent carrier lift levels. For bialgebra homomorphisms, these squares
bundle the stock lifted algebra map between the prescribed full lifted
bialgebras, without an antipode hypothesis. This lift also preserves identities
and composition. The Laurent-polynomial formula uses the stock Hopf structure
and its exponent-reversing formula on Laurent monomials.
-/

@[expose] public section

universe uR uA uB uC p q t s

open scoped TensorProduct

namespace AlgHom

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC}
variable [CommSemiring R] [Semiring A] [Semiring B] [Semiring C]
variable [α : Algebra R A] [β : Algebra R B] [γ : Algebra R C]

/-- Lifting the identity is the identity on the same carrier lift level. -/
@[simp]
theorem ulift_id :
    (show @AlgHom (ULift.{q} R) (ULift.{p} A) (ULift.{p} A) _ _ _
      (@ULift.algebra' R (ULift.{p} A) _ _ (@ULift.algebra R A _ _ α))
      (@ULift.algebra' R (ULift.{p} A) _ _ (@ULift.algebra R A _ _ α))
      from (AlgHom.id R A).ulift) =
    @AlgHom.id (ULift.{q} R) (ULift.{p} A) _ _
      (@ULift.algebra' R (ULift.{p} A) _ _ (@ULift.algebra R A _ _ α)) := by
  let : Algebra (ULift.{q} R) (ULift.{p} A) :=
    @ULift.algebra' R (ULift.{p} A) _ _ (@ULift.algebra R A _ _ α)
  exact AlgHom.ext fun _ => rfl

/-- Lifting preserves composition; the three carrier lift levels are independent. -/
theorem ulift_comp (k : B →ₐ[R] C) (j : A →ₐ[R] B) :
    (show @AlgHom (ULift.{q} R) (ULift.{p} A) (ULift.{s} C) _ _ _
      (@ULift.algebra' R (ULift.{p} A) _ _ (@ULift.algebra R A _ _ α))
      (@ULift.algebra' R (ULift.{s} C) _ _ (@ULift.algebra R C _ _ γ))
      from (k.comp j).ulift) =
    @AlgHom.comp (ULift.{q} R) (ULift.{p} A) (ULift.{t} B) (ULift.{s} C) _ _ _ _
      (@ULift.algebra' R (ULift.{p} A) _ _ (@ULift.algebra R A _ _ α))
      (@ULift.algebra' R (ULift.{t} B) _ _ (@ULift.algebra R B _ _ β))
      (@ULift.algebra' R (ULift.{s} C) _ _ (@ULift.algebra R C _ _ γ))
      k.ulift j.ulift := by
  let : Algebra (ULift.{q} R) (ULift.{p} A) :=
    @ULift.algebra' R (ULift.{p} A) _ _ (@ULift.algebra R A _ _ α)
  let : Algebra (ULift.{q} R) (ULift.{s} C) :=
    @ULift.algebra' R (ULift.{s} C) _ _ (@ULift.algebra R C _ _ γ)
  exact AlgHom.ext fun _ => rfl

/-- The scalar-and-carrier tensor down equivalences are natural for the stock
lifted algebra homomorphism, on the modules of the specified lifted algebras. -/
theorem ulift_tensorProduct_naturality (j : A →ₐ[R] B)
    (z : @TensorProduct (ULift.{q} R) _ (ULift.{p} A) (ULift.{p} A) _ _
      (@Algebra.toModule (ULift.{q} R) (ULift.{p} A) _ _
        (@ULift.algebra' R (ULift.{p} A) _ _ (@ULift.algebra R A _ _ α)))
      (@Algebra.toModule (ULift.{q} R) (ULift.{p} A) _ _
        (@ULift.algebra' R (ULift.{p} A) _ _ (@ULift.algebra R A _ _ α)))) :
    @RingEquiv.tensorProductCongrOfAlgebraMap (ULift.{q} R) R (ULift.{t} B) B _ _ _ _
      (@ULift.algebra' R (ULift.{t} B) _ _ (@ULift.algebra R B _ _ β)) β
      ULift.ringEquiv ULift.ringEquiv (fun _ => rfl)
      (TensorProduct.map
        (@AlgHom.toLinearMap (ULift.{q} R) (ULift.{p} A) (ULift.{t} B) _ _ _
          (@ULift.algebra' R (ULift.{p} A) _ _ (@ULift.algebra R A _ _ α))
          (@ULift.algebra' R (ULift.{t} B) _ _ (@ULift.algebra R B _ _ β)) j.ulift)
        (@AlgHom.toLinearMap (ULift.{q} R) (ULift.{p} A) (ULift.{t} B) _ _ _
          (@ULift.algebra' R (ULift.{p} A) _ _ (@ULift.algebra R A _ _ α))
          (@ULift.algebra' R (ULift.{t} B) _ _ (@ULift.algebra R B _ _ β)) j.ulift) z) =
    TensorProduct.map j.toLinearMap j.toLinearMap
      (@RingEquiv.tensorProductCongrOfAlgebraMap (ULift.{q} R) R (ULift.{p} A) A _ _ _ _
        (@ULift.algebra' R (ULift.{p} A) _ _ (@ULift.algebra R A _ _ α)) α
        ULift.ringEquiv ULift.ringEquiv (fun _ => rfl) z) := by
  let : Algebra (ULift.{q} R) (ULift.{p} A) :=
    @ULift.algebra' R (ULift.{p} A) _ _ (@ULift.algebra R A _ _ α)
  let : Algebra (ULift.{q} R) (ULift.{t} B) :=
    @ULift.algebra' R (ULift.{t} B) _ _ (@ULift.algebra R B _ _ β)
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    rw [TensorProduct.map_tmul,
      RingEquiv.tensorProductCongrOfAlgebraMap_tmul
        (R := ULift.{q} R) (S := R) (A := ULift.{t} B) (B := B)
        (α := @ULift.algebra' R (ULift.{t} B) _ _ (@ULift.algebra R B _ _ β))
        (β := β) ULift.ringEquiv ULift.ringEquiv (fun _ => rfl),
      RingEquiv.tensorProductCongrOfAlgebraMap_tmul
        (R := ULift.{q} R) (S := R) (A := ULift.{p} A) (B := A)
        (α := @ULift.algebra' R (ULift.{p} A) _ _ (@ULift.algebra R A _ _ α))
        (β := α) ULift.ringEquiv ULift.ringEquiv (fun _ => rfl),
      TensorProduct.map_tmul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end AlgHom

namespace Bialgebra

variable (R : Type uR) (A : Type uA) [CommSemiring R] [Semiring A] [Bialgebra R A]

/-- Lift the scalar and carrier universes of a bialgebra independently. -/
@[instance_reducible]
def ulift : Bialgebra (ULift.{q} R) (ULift.{p} A) := by
  letI : Algebra (ULift.{q} R) (ULift.{p} A) :=
    @ULift.algebra' R (ULift.{p} A) _ _ (@ULift.algebra R A _ _ inferInstance)
  exact RingEquiv.bialgebra ULift.ringEquiv ULift.ringEquiv (fun _ => rfl)

/-- The lifted bialgebra uses the stock scalar-and-carrier lifted algebra. -/
@[simp]
theorem ulift_toAlgebra :
    (ulift R A : Bialgebra (ULift.{q} R) (ULift.{p} A)).toAlgebra =
      @ULift.algebra' R (ULift.{p} A) _ _ (@ULift.algebra R A _ _ inferInstance) := rfl

/-- The lifted module is the module induced by the stock lifted algebra parent. -/
theorem ulift_toModule :
    @Algebra.toModule (ULift.{q} R) (ULift.{p} A) _ _ (ulift R A).toAlgebra =
      @Algebra.toModule (ULift.{q} R) (ULift.{p} A) _ _
        (@ULift.algebra' R (ULift.{p} A) _ _ (@ULift.algebra R A _ _ inferInstance)) := rfl

/-- The counit of a lifted bialgebra is the lift of the original counit. -/
theorem ulift_counit_apply (a : ULift.{p} A) :
    @CoalgebraStruct.counit (ULift.{q} R) (ULift.{p} A) _ _ _
        (ulift R A).toCoalgebra.toCoalgebraStruct a =
      ULift.up (Coalgebra.counit (R := R) a.down) := rfl

/-- Scalar down recovers the original counit. -/
theorem down_ulift_counit_apply (a : ULift.{p} A) :
    (@CoalgebraStruct.counit (ULift.{q} R) (ULift.{p} A) _ _ _
        (ulift R A).toCoalgebra.toCoalgebraStruct a).down =
      Coalgebra.counit (R := R) a.down := rfl

/-- The specific semilinear tensor down equivalence recovers the original comultiplication. -/
theorem ulift_comul_down (a : ULift.{p} A) :
    @RingEquiv.tensorProductCongrOfAlgebraMap (ULift.{q} R) R (ULift.{p} A) A _ _ _ _
        (@ULift.algebra' R (ULift.{p} A) _ _ (@ULift.algebra R A _ _ inferInstance))
        inferInstance ULift.ringEquiv ULift.ringEquiv (fun _ => rfl)
        (@CoalgebraStruct.comul (ULift.{q} R) (ULift.{p} A) _ _ _
          (ulift R A).toCoalgebra.toCoalgebraStruct a) =
      Coalgebra.comul (R := R) a.down := by
  exact RingEquiv.tensorProductCongr_bialgebra_comul
    (R := ULift.{q} R) (S := R) (A := ULift.{p} A) (B := A)
    (α := @ULift.algebra' R (ULift.{p} A) _ _ (@ULift.algebra R A _ _ inferInstance))
    ULift.ringEquiv ULift.ringEquiv (fun _ => rfl) a

end Bialgebra

namespace BialgHom

section Squares

variable {R : Type uR} {A : Type uA} {B : Type uB}
variable [CommSemiring R] [Semiring A] [Semiring B] [Bialgebra R A] [Bialgebra R B]

/-- The stock lifted algebra map intertwines the counits of the lifted bialgebras. -/
theorem ulift_counit_apply (j : A →ₐc[R] B) (a : ULift.{p} A) :
    @CoalgebraStruct.counit (ULift.{q} R) (ULift.{t} B) _ _ _
      (Bialgebra.ulift R B).toCoalgebra.toCoalgebraStruct
        (AlgHom.ulift.{p, q, t, uR, uA, uB} j.toAlgHom a) =
    @CoalgebraStruct.counit (ULift.{q} R) (ULift.{p} A) _ _ _
      (Bialgebra.ulift R A).toCoalgebra.toCoalgebraStruct a := by
  rw [Bialgebra.ulift_counit_apply, Bialgebra.ulift_counit_apply,
    AlgHom.down_ulift_apply]
  exact congrArg (ULift.up : R → ULift.{q} R) (CoalgHomClass.counit_comp_apply j a.down)

/-- The tensor square of the stock lifted algebra map intertwines the
comultiplications of the lifted bialgebras. No antipode is required. -/
theorem ulift_map_comul_apply (j : A →ₐc[R] B) (a : ULift.{p} A) :
    TensorProduct.map
      (@AlgHom.toLinearMap (ULift.{q} R) (ULift.{p} A) (ULift.{t} B) _ _ _
        (@ULift.algebra' R (ULift.{p} A) _ _ (@ULift.algebra R A _ _ inferInstance))
        (@ULift.algebra' R (ULift.{t} B) _ _ (@ULift.algebra R B _ _ inferInstance))
        (AlgHom.ulift.{p, q, t, uR, uA, uB} j.toAlgHom))
      (@AlgHom.toLinearMap (ULift.{q} R) (ULift.{p} A) (ULift.{t} B) _ _ _
        (@ULift.algebra' R (ULift.{p} A) _ _ (@ULift.algebra R A _ _ inferInstance))
        (@ULift.algebra' R (ULift.{t} B) _ _ (@ULift.algebra R B _ _ inferInstance))
        (AlgHom.ulift.{p, q, t, uR, uA, uB} j.toAlgHom))
      (@CoalgebraStruct.comul (ULift.{q} R) (ULift.{p} A) _ _ _
        (Bialgebra.ulift R A).toCoalgebra.toCoalgebraStruct a) =
    @CoalgebraStruct.comul (ULift.{q} R) (ULift.{t} B) _ _ _
      (Bialgebra.ulift R B).toCoalgebra.toCoalgebraStruct
        (AlgHom.ulift.{p, q, t, uR, uA, uB} j.toAlgHom a) := by
  apply (@RingEquiv.tensorProductCongrOfAlgebraMap (ULift.{q} R) R (ULift.{t} B) B _ _ _ _
    (@ULift.algebra' R (ULift.{t} B) _ _ (@ULift.algebra R B _ _ inferInstance))
    inferInstance ULift.ringEquiv ULift.ringEquiv (fun _ => rfl)).injective
  rw [AlgHom.ulift_tensorProduct_naturality, Bialgebra.ulift_comul_down,
    Bialgebra.ulift_comul_down, AlgHom.down_ulift_apply]
  exact CoalgHomClass.map_comp_comul_apply j a.down

end Squares

/-- Lift a bialgebra homomorphism in the scalar and carrier universes, between
the full bialgebras obtained by lifting its given source and target. -/
def ulift
    {R : Type uR} {A : Type uA} {B : Type uB}
    [cR : CommSemiring R] [sA : Semiring A] [sB : Semiring B]
    [BA : Bialgebra R A] [BB : Bialgebra R B]
    (j : @BialgHom R A B cR
      sA BA.toAlgebra sB BB.toAlgebra
      BA.toCoalgebra.toCoalgebraStruct BB.toCoalgebra.toCoalgebraStruct) :
    @BialgHom (ULift.{q} R) (ULift.{p} A) (ULift.{t} B)
      (@ULift.commSemiring R cR)
      (@ULift.semiring A sA)
      (@Bialgebra.ulift R A cR sA BA).toAlgebra
      (@ULift.semiring B sB)
      (@Bialgebra.ulift R B cR sB BB).toAlgebra
      (@Bialgebra.ulift R A cR sA BA).toCoalgebra.toCoalgebraStruct
      (@Bialgebra.ulift R B cR sB BB).toCoalgebra.toCoalgebraStruct := by
  letI : Bialgebra (ULift.{q} R) (ULift.{p} A) := @Bialgebra.ulift R A cR sA BA
  letI : Bialgebra (ULift.{q} R) (ULift.{t} B) := @Bialgebra.ulift R B cR sB BB
  refine BialgHom.ofAlgHom (AlgHom.ulift.{p, q, t, uR, uA, uB} j.toAlgHom) ?_ ?_
  · apply AlgHom.toLinearMap_injective
    simp only [AlgHom.comp_toLinearMap, Bialgebra.toLinearMap_counitAlgHom]
    exact LinearMap.ext fun a => ulift_counit_apply.{uR, uA, uB, p, q, t} j a
  · apply AlgHom.toLinearMap_injective
    simp only [AlgHom.comp_toLinearMap, Bialgebra.toLinearMap_comulAlgHom,
      Algebra.TensorProduct.toLinearMap_map, TensorProduct.AlgebraTensorModule.map_eq]
    exact LinearMap.ext fun a => ulift_map_comul_apply j a

variable {R : Type uR} {A : Type uA} {B : Type uB}
variable [cR : CommSemiring R] [sA : Semiring A] [sB : Semiring B]
variable [BA : Bialgebra R A] [BB : Bialgebra R B]

/-- The derived algebra map of a lifted bialgebra homomorphism is the stock lift. -/
@[simp]
theorem ulift_toAlgHom (j : A →ₐc[R] B) :
    @BialgHom.toAlgHom (ULift.{q} R) (ULift.{p} A) (ULift.{t} B)
      (@ULift.commSemiring R cR)
      (@ULift.semiring A sA) (@ULift.semiring B sB)
      (@Bialgebra.ulift R A cR sA BA).toAlgebra
      (@Bialgebra.ulift R B cR sB BB).toAlgebra
      (@Bialgebra.ulift R A cR sA BA).toCoalgebra.toCoalgebraStruct
      (@Bialgebra.ulift R B cR sB BB).toCoalgebra.toCoalgebraStruct
      (@BialgHom.ulift R A B cR sA sB BA BB j) =
    @AlgHom.ulift.{p, q, t, uR, uA, uB} R A B cR sA sB BA.toAlgebra BB.toAlgebra
      (@BialgHom.toAlgHom R A B cR sA sB BA.toAlgebra BB.toAlgebra
        BA.toCoalgebra.toCoalgebraStruct BB.toCoalgebra.toCoalgebraStruct j) := rfl

/-- The lifted bialgebra homomorphism acts by carrier up after the original map and down. -/
theorem ulift_apply (j : A →ₐc[R] B) (a : ULift.{p} A) :
    (show @BialgHom (ULift.{q} R) (ULift.{p} A) (ULift.{t} B)
      (@ULift.commSemiring R cR)
      (@ULift.semiring A sA) (@Bialgebra.ulift R A cR sA BA).toAlgebra
      (@ULift.semiring B sB) (@Bialgebra.ulift R B cR sB BB).toAlgebra
      (@Bialgebra.ulift R A cR sA BA).toCoalgebra.toCoalgebraStruct
      (@Bialgebra.ulift R B cR sB BB).toCoalgebra.toCoalgebraStruct
      from j.ulift) a = (ULift.up (j a.down) : ULift.{t} B) := by
  exact (DFunLike.congr_fun (ulift_toAlgHom.{uR, uA, uB, p, q, t} j) a).trans rfl

/-- Carrier down recovers the original bialgebra homomorphism. -/
@[simp]
theorem down_ulift_apply (j : A →ₐc[R] B) (a : ULift.{p} A) :
    ((show @BialgHom (ULift.{q} R) (ULift.{p} A) (ULift.{t} B)
      (@ULift.commSemiring R cR)
      (@ULift.semiring A sA) (@Bialgebra.ulift R A cR sA BA).toAlgebra
      (@ULift.semiring B sB) (@Bialgebra.ulift R B cR sB BB).toAlgebra
      (@Bialgebra.ulift R A cR sA BA).toCoalgebra.toCoalgebraStruct
      (@Bialgebra.ulift R B cR sB BB).toCoalgebra.toCoalgebraStruct
      from j.ulift) a).down = j a.down := by
  exact congrArg ULift.down (ulift_apply.{uR, uA, uB, p, q, t} j a)

/-- Lifting the identity gives the identity at the same carrier lift level. -/
@[simp]
theorem ulift_id :
    (show @BialgHom (ULift.{q} R) (ULift.{p} A) (ULift.{p} A)
      (@ULift.commSemiring R cR)
      (@ULift.semiring A sA) (@Bialgebra.ulift R A cR sA BA).toAlgebra
      (@ULift.semiring A sA) (@Bialgebra.ulift R A cR sA BA).toAlgebra
      (@Bialgebra.ulift R A cR sA BA).toCoalgebra.toCoalgebraStruct
      (@Bialgebra.ulift R A cR sA BA).toCoalgebra.toCoalgebraStruct
      from (BialgHom.id R A).ulift) =
    @BialgHom.id (ULift.{q} R) (ULift.{p} A)
      (@ULift.commSemiring R cR) (@ULift.semiring A sA)
      (@Bialgebra.ulift R A cR sA BA).toAlgebra
      (@Bialgebra.ulift R A cR sA BA).toCoalgebra.toCoalgebraStruct := by
  let : Bialgebra (ULift.{q} R) (ULift.{p} A) := @Bialgebra.ulift R A cR sA BA
  apply coe_toAlgHom_injective
  simpa only [ulift_toAlgHom, id_toAlgHom] using
    (AlgHom.ulift_id (R := R) (A := A))

variable {C : Type uC} [sC : Semiring C] [BC : Bialgebra R C]

/-- Lifting preserves composition, with three independent carrier lift levels. -/
theorem ulift_comp (k : B →ₐc[R] C) (j : A →ₐc[R] B) :
    (show @BialgHom (ULift.{q} R) (ULift.{p} A) (ULift.{s} C)
      (@ULift.commSemiring R cR)
      (@ULift.semiring A sA) (@Bialgebra.ulift R A cR sA BA).toAlgebra
      (@ULift.semiring C sC) (@Bialgebra.ulift R C cR sC BC).toAlgebra
      (@Bialgebra.ulift R A cR sA BA).toCoalgebra.toCoalgebraStruct
      (@Bialgebra.ulift R C cR sC BC).toCoalgebra.toCoalgebraStruct
      from (k.comp j).ulift) =
    @BialgHom.comp (ULift.{q} R) (ULift.{p} A) (ULift.{t} B) (ULift.{s} C)
      (@ULift.commSemiring R cR)
      (@ULift.semiring A sA) (@ULift.semiring B sB) (@ULift.semiring C sC)
      (@Bialgebra.ulift R A cR sA BA).toAlgebra
      (@Bialgebra.ulift R B cR sB BB).toAlgebra
      (@Bialgebra.ulift R C cR sC BC).toAlgebra
      (@Bialgebra.ulift R A cR sA BA).toCoalgebra.toCoalgebraStruct
      (@Bialgebra.ulift R B cR sB BB).toCoalgebra.toCoalgebraStruct
      (@Bialgebra.ulift R C cR sC BC).toCoalgebra.toCoalgebraStruct
      k.ulift j.ulift := by
  let : Bialgebra (ULift.{q} R) (ULift.{p} A) := @Bialgebra.ulift R A cR sA BA
  let : Bialgebra (ULift.{q} R) (ULift.{s} C) := @Bialgebra.ulift R C cR sC BC
  apply coe_toAlgHom_injective
  simpa only [ulift_toAlgHom, comp_toAlgHom] using
    (AlgHom.ulift_comp k.toAlgHom j.toAlgHom)

end BialgHom

namespace HopfAlgebraStruct

variable (R : Type uR) (A : Type uA) [CommSemiring R] [Semiring A] [HopfAlgebraStruct R A]

/-- Lift the scalar and carrier universes of bialgebra and antipode data independently. -/
@[instance_reducible]
def ulift : HopfAlgebraStruct (ULift.{q} R) (ULift.{p} A) := by
  letI : Algebra (ULift.{q} R) (ULift.{p} A) :=
    @ULift.algebra' R (ULift.{p} A) _ _ (@ULift.algebra R A _ _ inferInstance)
  exact RingEquiv.hopfAlgebraStruct ULift.ringEquiv ULift.ringEquiv (fun _ => rfl)

/-- The bialgebra parent is exactly the lifted bialgebra. -/
@[simp]
theorem ulift_toBialgebra :
    (ulift R A : HopfAlgebraStruct (ULift.{q} R) (ULift.{p} A)).toBialgebra =
      Bialgebra.ulift R A := rfl

/-- The lifted antipode is carrier up after the original antipode and carrier down. -/
@[simp]
theorem ulift_antipode_apply (a : ULift.{p} A) :
    @HopfAlgebraStruct.antipode (ULift.{q} R) (ULift.{p} A) _ _ (ulift R A) a =
      ULift.up (HopfAlgebra.antipode R a.down) := rfl

end HopfAlgebraStruct

namespace HopfAlgebra

variable (R : Type uR) (A : Type uA) [CommSemiring R] [Semiring A] [HopfAlgebra R A]

/-- Lift the scalar and carrier universes of a Hopf algebra independently. -/
@[instance_reducible]
def ulift : HopfAlgebra (ULift.{q} R) (ULift.{p} A) := by
  letI : Algebra (ULift.{q} R) (ULift.{p} A) :=
    @ULift.algebra' R (ULift.{p} A) _ _ (@ULift.algebra R A _ _ inferInstance)
  exact RingEquiv.hopfAlgebra ULift.ringEquiv ULift.ringEquiv (fun _ => rfl)

/-- The antipode-data parent is exactly the lifted antipode-data structure. -/
@[simp]
theorem ulift_toHopfAlgebraStruct :
    (ulift R A : HopfAlgebra (ULift.{q} R) (ULift.{p} A)).toHopfAlgebraStruct =
      HopfAlgebraStruct.ulift R A := rfl

/-- The full lifted Hopf algebra retains the stock lifted algebra parent. -/
@[simp]
theorem ulift_toAlgebra :
    (ulift R A : HopfAlgebra (ULift.{q} R) (ULift.{p} A)).toBialgebra.toAlgebra =
      @ULift.algebra' R (ULift.{p} A) _ _ (@ULift.algebra R A _ _ inferInstance) := rfl

/-- The full lifted Hopf algebra uses the module of that exact lifted algebra. -/
theorem ulift_toModule :
    @Algebra.toModule (ULift.{q} R) (ULift.{p} A) _ _ (ulift R A).toBialgebra.toAlgebra =
      @Algebra.toModule (ULift.{q} R) (ULift.{p} A) _ _
        (@ULift.algebra' R (ULift.{p} A) _ _ (@ULift.algebra R A _ _ inferInstance)) := rfl

/-- The full lifted Hopf algebra has exactly the lifted full coalgebra. -/
@[simp]
theorem ulift_toCoalgebra :
    (ulift R A : HopfAlgebra (ULift.{q} R) (ULift.{p} A)).toBialgebra.toCoalgebra =
      (Bialgebra.ulift R A).toCoalgebra := rfl

/-- The counit of the full lifted Hopf algebra is the lifted original counit. -/
theorem ulift_counit_apply (a : ULift.{p} A) :
    @CoalgebraStruct.counit (ULift.{q} R) (ULift.{p} A) _ _ _
        (ulift R A).toBialgebra.toCoalgebra.toCoalgebraStruct a =
      ULift.up (Coalgebra.counit (R := R) a.down) := rfl

/-- Scalar down recovers the counit of the original full Hopf algebra. -/
theorem down_ulift_counit_apply (a : ULift.{p} A) :
    (@CoalgebraStruct.counit (ULift.{q} R) (ULift.{p} A) _ _ _
        (ulift R A).toBialgebra.toCoalgebra.toCoalgebraStruct a).down =
      Coalgebra.counit (R := R) a.down := rfl

/-- The specific tensor down equivalence recovers the original full Hopf comultiplication. -/
theorem ulift_comul_down (a : ULift.{p} A) :
    @RingEquiv.tensorProductCongrOfAlgebraMap (ULift.{q} R) R (ULift.{p} A) A _ _ _ _
        (@ULift.algebra' R (ULift.{p} A) _ _ (@ULift.algebra R A _ _ inferInstance))
        inferInstance ULift.ringEquiv ULift.ringEquiv (fun _ => rfl)
        (@CoalgebraStruct.comul (ULift.{q} R) (ULift.{p} A) _ _ _
          (ulift R A).toBialgebra.toCoalgebra.toCoalgebraStruct a) =
      Coalgebra.comul (R := R) a.down :=
  Bialgebra.ulift_comul_down R A a

/-- The lifted antipode acts by up after the original antipode and down. -/
@[simp]
theorem ulift_antipode_apply (a : ULift.{p} A) :
    @HopfAlgebraStruct.antipode (ULift.{q} R) (ULift.{p} A) _ _
        (ulift R A).toHopfAlgebraStruct a =
      ULift.up (HopfAlgebra.antipode R a.down) := rfl

/-- Carrier down recovers the original antipode. -/
@[simp]
theorem down_ulift_antipode_apply (a : ULift.{p} A) :
    (@HopfAlgebraStruct.antipode (ULift.{q} R) (ULift.{p} A) _ _
        (ulift R A).toHopfAlgebraStruct a).down =
      HopfAlgebra.antipode R a.down := rfl

end HopfAlgebra

namespace LaurentPolynomial

variable {R : Type uR} {A : Type uA} [CommSemiring R] [Semiring A] [HopfAlgebra R A]

/-- On the lifted Laurent-polynomial Hopf algebra, the antipode reverses the exponent. -/
theorem ulift_antipode_T (n : ℤ) :
    @HopfAlgebraStruct.antipode (ULift.{q} R) (ULift.{p} (LaurentPolynomial A)) _ _
        (HopfAlgebra.ulift R (LaurentPolynomial A)).toHopfAlgebraStruct
        (ULift.up (T n)) =
      ULift.up (T (-n)) := by
  rw [HopfAlgebra.ulift_antipode_apply, antipode_T]

end LaurentPolynomial

/-- Independent scalar and carrier lifts of the stock natural-number Hopf algebra
retain its counit, including at the nonzero unit. -/
theorem Bialgebra.ulift_nat_counit (n : ℕ) :
    @CoalgebraStruct.counit (ULift.{q} ℕ) (ULift.{p} ℕ) _ _ _
        (Bialgebra.ulift ℕ ℕ).toCoalgebra.toCoalgebraStruct (ULift.up n) = ULift.up n := rfl
