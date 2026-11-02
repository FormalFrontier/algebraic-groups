/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.BaseChange
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.HopfAlgebra.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Frobenius scalar extension

The Frobenius twist of a `K`-module `V` is the coefficient-first tensor product
`K ⊗[K] V`, where the old action on the coefficient factor is through an iterated
Frobenius. Its new `K`-action is ordinary multiplication on that factor. The additive
and module structures require only an additive commutative monoid `V` with its given
`K`-module structure. For a `K`-algebra `A`, the ring, algebra, coalgebra, bialgebra and
Hopf algebra structures are Mathlib's scalar-extension structures. The original
structures on `V` and `A` are unchanged. For a semiring `A` and a given central
`K`-algebra `B`, the balanced lift extends ring homomorphisms `f : A →+* B` satisfying
Frobenius-semilinear scalar compatibility, and is characterized on pure tensors by
`algebraMap K B c * f a`.

The canonical right inclusion sends `a` to `1 ⊗ a` and requires only a semiring
algebra. It is a ring homomorphism, semilinear for iterated coefficient Frobenius
with respect to the new ordinary coefficient action. For commutative bialgebras,
its composites with relative Frobenius are the corresponding `p ^ r`th power maps.
Each element of the relative-Frobenius kernel has vanishing `p ^ r`th power; this
is not a statement about a power of the kernel ideal.

## Implementation notes

The two scalar rings have the same carrier but different roles. Scalar-extension
providers are bound with distinct scalar variables before specialization. The
relative Frobenius is a bialgebra homomorphism. Its underlying algebra image is
the `K`-submodule spanned by the `p ^ r`th powers, not necessarily the set of such powers.
Right-oriented tensor notation requires the right-factor algebra action, and no
right-oriented coalgebra transport is defined here.

## References

Mathlib supplies iterated Frobenius, the scalar-extension adjunction
`AlgHom.liftEquiv`, and scalar-extension algebra, coalgebra, bialgebra and Hopf
algebra structures.
-/

@[expose] public noncomputable section

universe u v w

open scoped TensorProduct

namespace Algebra.FrobeniusTwist

/- Bind the two scalar roles before they can become the same carrier. -/
private abbrev baseChangeType (R : Type u) (S : Type v) (A : Type w)
    [CommSemiring R] [CommSemiring S] [AddCommMonoid A] [Algebra R S] [Module R A] :=
  S ⊗[R] A

private def baseChangeTmul (R : Type u) (S : Type v) (A : Type w)
    [CommSemiring R] [Semiring S] [AddCommMonoid A] [Algebra R S] [Module R A]
    (c : S) (a : A) : S ⊗[R] A := c ⊗ₜ[R] a

private def scalarBasis (R : Type*) (S : Type*) (M : Type*) (I : Type*)
    [CommSemiring R] [Semiring S] [AddCommMonoid M] [Algebra R S] [Module R M]
    (b : Module.Basis I R M) : Module.Basis I S (S ⊗[R] M) :=
  b.baseChange S

/- Bind the stock basis formula before identifying the scalar rings. -/
private theorem baseChangeBasis_tmul (R : Type*) (S : Type*) (M : Type*) (I : Type*)
    [CommSemiring R] [Semiring S] [AddCommMonoid M] [Algebra R S] [Module R M]
    (b : Module.Basis I R M) (i : I) :
    scalarBasis R S M I b i = baseChangeTmul R S M 1 (b i) := by
  simpa only [scalarBasis, baseChangeTmul] using (Module.Basis.baseChange_apply S b i)

/- Use the commutative coefficient-module context when applying the basis. -/
private theorem baseChangeBasis_apply (R : Type*) (S : Type*) (M : Type*) (I : Type*)
    [CommSemiring R] [CommSemiring S] [AddCommMonoid M] [Algebra R S] [Module R M]
    (b : Module.Basis I R M) (i : I) :
    (let bS : Module.Basis I S (S ⊗[R] M) := scalarBasis R S M I b; bS i) =
      baseChangeTmul R S M 1 (b i) := by
  exact baseChangeBasis_tmul R S M I b i

/- Compute coordinates before identifying the scalar rings. -/
private theorem baseChangeBasis_repr_tmul (R : Type*) (S : Type*) (M : Type*) (I : Type*)
    [CommSemiring R] [Semiring S] [AddCommMonoid M] [Algebra R S] [Module R M]
    (b : Module.Basis I R M) (i : I) :
    (scalarBasis R S M I b).repr (baseChangeTmul R S M 1 (b i)) = Finsupp.single i 1 := by
  exact (congrArg (scalarBasis R S M I b).repr
    (baseChangeBasis_tmul R S M I b i).symm).trans
      ((scalarBasis R S M I b).repr_self i)

private theorem baseChangeTmul_add (R : Type u) (S : Type v) (A : Type w)
    [CommSemiring R] [CommSemiring S] [AddCommMonoid A] [Algebra R S] [Module R A]
    (c : S) (a b : A) :
    baseChangeTmul R S A c (a + b) =
      baseChangeTmul R S A c a + baseChangeTmul R S A c b :=
  TensorProduct.tmul_add c a b

private def baseChangeDistrib (R : Type u) (S : Type v) (A : Type w)
    [CommSemiring R] [CommSemiring S] [Semiring A] [Algebra R S] [Algebra R A] :
    baseChangeType R S (A ⊗[R] A) ≃ₗ[S]
      baseChangeType R S A ⊗[S] baseChangeType R S A :=
  TensorProduct.AlgebraTensorModule.distribBaseChange R S A A

private theorem baseChangeDistrib_tmul (R : Type u) (S : Type v) (A : Type w)
    [CommSemiring R] [CommSemiring S] [Semiring A] [Algebra R S] [Algebra R A]
    (c : S) (a b : A) :
    baseChangeDistrib R S A (baseChangeTmul R S (A ⊗[R] A) c (a ⊗ₜ[R] b)) =
      baseChangeTmul R S A c a ⊗ₜ[S] baseChangeTmul R S A 1 b := by
  simp only [baseChangeDistrib, baseChangeTmul,
    TensorProduct.AlgebraTensorModule.distribBaseChange_tmul]

private theorem baseChange_comul_tmul (R : Type u) (S : Type v) (A : Type w)
    [CommSemiring R] [CommSemiring S] [Semiring A] [Algebra R S] [Bialgebra R A]
    (c : S) (a : A) :
    Coalgebra.comul (R := S) (baseChangeTmul R S A c a) =
      baseChangeDistrib R S A
        (baseChangeTmul R S (A ⊗[R] A) c (Coalgebra.comul (R := R) a)) := by
  change Coalgebra.comul (R := S) (c ⊗ₜ[R] a) =
    TensorProduct.AlgebraTensorModule.distribBaseChange R S A A
      (c ⊗ₜ[R] Coalgebra.comul (R := R) a)
  exact LinearMap.congr_fun (Coalgebra.comul_baseChange R S A) (c ⊗ₜ[R] a)

private theorem baseChange_smul_tmul (R : Type u) (S : Type v) (A : Type w)
    [CommSemiring R] [CommSemiring S] [AddCommMonoid A] [Algebra R S] [Module R A]
    (d c : S) (a : A) :
    d • baseChangeTmul R S A c a = baseChangeTmul R S A (d * c) a :=
  TensorProduct.smul_tmul' d c a

private theorem baseChange_balance (R : Type u) (S : Type v) (A : Type w)
    [CommSemiring R] [CommSemiring S] [AddCommMonoid A] [Algebra R S] [Module R A]
    (d : R) (c : S) (a : A) :
    baseChangeTmul R S A (algebraMap R S d * c) a = baseChangeTmul R S A c (d • a) := by
  change (algebraMap R S d * c) ⊗ₜ[R] a = c ⊗ₜ[R] (d • a)
  calc
    (algebraMap R S d * c) ⊗ₜ[R] a = (d • c) ⊗ₜ[R] a :=
      congrArg (fun s : S => s ⊗ₜ[R] a) (Algebra.smul_def d c).symm
    _ = c ⊗ₜ[R] (d • a) := TensorProduct.smul_tmul d c a

private theorem baseChange_algebraMap (R : Type u) (S : Type v) (A : Type w)
    [CommSemiring R] [CommSemiring S] [Semiring A] [Algebra R S] [Algebra R A]
    (c : S) : algebraMap S (baseChangeType R S A) c = baseChangeTmul R S A c 1 := rfl

/- Restrict only the old scalar action, retaining the given new action on the target.
The scalar roles are distinct while the stock adjunction and its formula are bound. -/
private def baseChangeLift (R : Type*) (S : Type*) (A : Type*) (B : Type*)
    [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]
    [Algebra R S] [Algebra R A] [Algebra S B] (f : A →+* B)
    (hf : ∀ d : R, f (algebraMap R A d) = algebraMap S B (algebraMap R S d)) :
    S ⊗[R] A →ₐ[S] B := by
  let : Algebra R B := Algebra.restrictScalars R S B
  let : IsScalarTower R S B := IsScalarTower.restrictScalars R S B
  exact AlgHom.liftEquiv R S A B { f with commutes' := hf }

/- A regular type synonym below keeps its instance head distinct from ordinary tensors.
Its value is still the same old-balanced tensor, by definitional equality. -/
section Module

variable (K : Type u) (V : Type v) [CommSemiring K] [AddCommMonoid V] [Module K V]
variable (p r : ℕ) [ExpChar K p]

/-- The old coefficient algebra, on the same ring `K`, with algebra map `c ↦ c^(p^r)`.
This is not the new coefficient-self algebra. -/
@[instance_reducible]
def coefficientAlgebra : Algebra K K := (iterateFrobenius K p r).toAlgebra

/-- The old coefficient algebra map is the iterated Frobenius. -/
@[simp]
theorem coefficientAlgebra_algebraMap (c : K) :
    @algebraMap K K _ _ (coefficientAlgebra K p r) c = c ^ (p ^ r) := rfl

/-- The coefficient-first Frobenius scalar extension of a module. The coefficient
carrier is `K` with its original ring operations and its old scalar action through
Frobenius. The given additive and module structures on the other factor are unchanged. -/
def twistObject : Type (max u v) :=
  let scalarExtension :
      ∀ (R S : Type u) (M : Type v)
        [CommSemiring R] [CommSemiring S] [AddCommMonoid M]
        [Algebra R S] [Module R M], Type (max u v) :=
    fun R S M _ _ _ _ _ => S ⊗[R] M
  @scalarExtension K K V _ _ _ (coefficientAlgebra K p r) ‹Module K V›

/-- The additive structure of the coefficient-first tensor product. -/
instance instAddCommMonoid : AddCommMonoid (twistObject K V p r) := by
  let scalarExtension :
      ∀ (R S : Type u) (M : Type v)
        [CommSemiring R] [CommSemiring S] [AddCommMonoid M]
        [Algebra R S] [Module R M], AddCommMonoid (S ⊗[R] M) :=
    fun R S M _ _ _ _ _ => inferInstance
  unfold twistObject
  exact @scalarExtension K K V _ _ _ (coefficientAlgebra K p r) ‹Module K V›

/- The same-base tensor shortcuts use the old left-factor module. These higher-priority
instances retain the stock new scalar-extension module and its scalar projections. -/
/-- The coefficient-self module on the Frobenius scalar extension. -/
instance (priority := 1100) instModule : Module K (twistObject K V p r) := by
  let scalarExtension :
      ∀ (R S : Type u) (M : Type v)
        [CommSemiring R] [CommSemiring S] [AddCommMonoid M]
        [Algebra R S] [Module R M], Module S (S ⊗[R] M) :=
    fun R S M _ _ _ _ _ => inferInstance
  unfold twistObject
  exact @scalarExtension K K V _ _ _ (coefficientAlgebra K p r) ‹Module K V›

/-- The distributive action inherited from the coefficient-self module. -/
instance (priority := 1100) instDistribMulAction :
    DistribMulAction K (twistObject K V p r) :=
  (instModule K V p r).toDistribMulAction

/-- Scalar multiplication inherited from the coefficient-self module. -/
instance (priority := 1100) instSMul : SMul K (twistObject K V p r) :=
  (instModule K V p r).toDistribMulAction.toMulAction.toSMul

/-- A pure tensor in the coefficient-first Frobenius scalar extension. -/
def tmul (c : K) (v : V) : twistObject K V p r := by
  let scalarExtension :
      ∀ (R S : Type u) (A : Type v)
        [CommSemiring R] [CommSemiring S] [AddCommMonoid A]
        [Algebra R S] [Module R A], S → A → S ⊗[R] A :=
    fun R S A _ _ _ _ _ c a => c ⊗ₜ[R] a
  unfold twistObject
  exact @scalarExtension K K V _ _ _ (coefficientAlgebra K p r) ‹Module K V› c v

/-- A pure tensor is additive in its original module factor. -/
@[simp]
theorem tmul_add (c : K) (v w : V) :
    tmul K V p r c (v + w) = tmul K V p r c v + tmul K V p r c w := by
  exact @baseChangeTmul_add K K V _ _ _ (coefficientAlgebra K p r) ‹Module K V› c v w

/-- The new scalar action is ordinary multiplication on coefficients. -/
@[simp]
theorem smul_tmul (d c : K) (v : V) :
    d • tmul K V p r c v = tmul K V p r (d * c) v := by
  exact @baseChange_smul_tmul K K V _ _ _ (coefficientAlgebra K p r) ‹Module K V› d c v

/-- Balancing uses the old Frobenius action, not the new scalar action. -/
theorem balance (d c : K) (v : V) :
    tmul K V p r (d ^ (p ^ r) * c) v = tmul K V p r c (d • v) := by
  change @baseChangeTmul K K V _ _ _ (coefficientAlgebra K p r) ‹Module K V›
      (@algebraMap K K _ _ (coefficientAlgebra K p r) d * c) v =
    @baseChangeTmul K K V _ _ _ (coefficientAlgebra K p r) ‹Module K V› c (d • v)
  exact @baseChange_balance K K V _ _ _ (coefficientAlgebra K p r) ‹Module K V› d c v

/-- Additive maps out of the twist are determined by their values on pure tensors. -/
@[ext]
theorem ext {M : Type w} [AddCommMonoid M]
    {f g : twistObject K V p r →+ M}
    (h : ∀ c v, f (tmul K V p r c v) = g (tmul K V p r c v)) : f = g := by
  let f' : @baseChangeType K K V _ _ _ (coefficientAlgebra K p r) ‹Module K V› →+ M := f
  let g' : @baseChangeType K K V _ _ _ (coefficientAlgebra K p r) ‹Module K V› →+ M := g
  change f' = g'
  apply AddMonoidHom.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul c v => exact h c v
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- Induction on the named Frobenius scalar extension, using pure tensors and sums. -/
@[elab_as_elim]
theorem inductionOn (x : twistObject K V p r) {motive : twistObject K V p r → Prop}
    (htmul : ∀ c v, motive (tmul K V p r c v))
    (hadd : ∀ x y, motive x → motive y → motive (x + y)) : motive x := by
  -- Keep the raw tensor carrier internal to this eliminator.
  let motive' : @baseChangeType K K V _ _ _ (coefficientAlgebra K p r) ‹Module K V› →
      Prop := motive
  change motive' x
  induction x using TensorProduct.inductionOn with
  | tmul c v => exact htmul c v
  | add x y hx hy => exact hadd x y hx hy

/-- The scalar extension of a linear map, linear for the new coefficient action. -/
def map {W : Type w} [AddCommMonoid W] [Module K W] (f : V →ₗ[K] W) :
    twistObject K V p r →ₗ[K] twistObject K W p r := by
  let baseChange :
      ∀ (R S : Type u) (M : Type v) (N : Type w)
        [CommSemiring R] [CommSemiring S] [Algebra R S]
        [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N],
        (M →ₗ[R] N) → (S ⊗[R] M →ₗ[S] S ⊗[R] N) :=
    fun R S M N _ _ _ _ _ _ _ g => g.baseChange S
  unfold twistObject
  exact @baseChange K K V W _ _ (coefficientAlgebra K p r)
    _ _ ‹Module K V› ‹Module K W› f

/-- Scalar extension of a linear map retains the coefficient of a pure tensor. -/
@[simp]
theorem map_tmul {W : Type w} [AddCommMonoid W] [Module K W] (f : V →ₗ[K] W)
    (c : K) (v : V) :
    map K V p r f (tmul K V p r c v) = tmul K W p r c (f v) := rfl

/-- Scalar extension preserves the identity linear map. -/
@[simp]
theorem map_id : map K V p r (LinearMap.id : V →ₗ[K] V) = LinearMap.id := by
  apply LinearMap.toAddMonoidHom_injective
  apply ext K V p r
  intro c v
  change map K V p r LinearMap.id (tmul K V p r c v) = tmul K V p r c v
  rw [map_tmul, LinearMap.id_apply]

/-- Scalar extension preserves composition of linear maps. -/
theorem map_comp {W : Type w} {X : Type*}
    [AddCommMonoid W] [Module K W] [AddCommMonoid X] [Module K X]
    (f : V →ₗ[K] W) (g : W →ₗ[K] X) :
    map K V p r (g.comp f) = (map K W p r g).comp (map K V p r f) := by
  apply LinearMap.toAddMonoidHom_injective
  apply ext K V p r
  intro c v
  change map K V p r (g.comp f) (tmul K V p r c v) =
    map K W p r g (map K V p r f (tmul K V p r c v))
  rw [map_tmul, map_tmul, map_tmul, LinearMap.comp_apply]

/-- The base-changed basis of the Frobenius scalar extension. -/
def basis {I : Type w} (b : Module.Basis I K V) :
    Module.Basis I K (twistObject K V p r) := by
  let scalarBasis := private_decl% (@scalarBasis)
  unfold twistObject
  exact @scalarBasis K K V I ‹CommSemiring K› (‹CommSemiring K›).toSemiring
    ‹AddCommMonoid V› (coefficientAlgebra K p r) ‹Module K V› b

/-- The base-changed basis vector has coefficient one and its original module factor. -/
@[simp]
theorem basis_apply {I : Type w} (b : Module.Basis I K V) (i : I) :
    basis K V p r b i = tmul K V p r 1 (b i) := by
  apply (basis K V p r b).repr.injective
  rw [Module.Basis.repr_self]
  exact (@baseChangeBasis_repr_tmul K K V I ‹CommSemiring K›
    (‹CommSemiring K›).toSemiring ‹AddCommMonoid V›
    (coefficientAlgebra K p r) ‹Module K V› b i).symm

/-- Finite generation is preserved by Frobenius scalar extension. -/
theorem moduleFinite [Module.Finite K V] : Module.Finite K (twistObject K V p r) := by
  let extendFinite :
      ∀ (R S : Type u) (M : Type v)
        [CommSemiring R] [CommSemiring S] [Algebra R S]
        [AddCommMonoid M] [Module R M],
        Module.Finite R M → Module.Finite S (S ⊗[R] M) :=
    fun R S M _ _ _ _ _ finite =>
      @Module.Finite.base_change R S M _ _ _ _ _ finite
  unfold twistObject
  exact @extendFinite K K V _ _ (coefficientAlgebra K p r) _ ‹Module K V› inferInstance

/-- Frobenius base extension of a projective module is projective for the new
ordinary coefficient-self action. -/
theorem moduleProjective [Module.Projective K V] :
    Module.Projective K (twistObject K V p r) := by
  let extendProjective :
      ∀ (R S : Type u) (M : Type v)
        [CommSemiring R] [CommSemiring S] [Algebra R S]
        [AddCommMonoid M] [Module R M],
        Module.Projective R M → Module.Projective S (S ⊗[R] M) :=
    fun R S M _ _ _ _ _ projective => by
      let originalProjective : Module.Projective R M := projective
      let coefficientFree : Module.Free S S := Module.Free.self S
      let coefficientProjective : Module.Projective S S := Module.Projective.of_free
      exact Module.Projective.tensorProduct (R := S) (R₀ := R) (M := S) (N := M)
  unfold twistObject
  exact @extendProjective K K V ‹CommSemiring K› ‹CommSemiring K›
    (coefficientAlgebra K p r) ‹AddCommMonoid V› ‹Module K V› ‹Module.Projective K V›

/-- Frobenius base extension of a free module is free for the new ordinary
coefficient-self action. -/
theorem moduleFree [Module.Free K V] : Module.Free K (twistObject K V p r) := by
  let extendFree :
      ∀ (R S : Type u) (M : Type v)
        [CommSemiring R] [CommSemiring S] [Algebra R S]
        [AddCommMonoid M] [Module R M],
        Module.Free R M → Module.Free S (S ⊗[R] M) :=
    fun R S M _ _ _ _ _ free => by
      let originalFree : Module.Free R M := free
      let coefficientFree : Module.Free S S := Module.Free.self S
      exact Module.Free.tensor (R := R) (S := S) (M := S) (N := M)
  unfold twistObject
  exact @extendFree K K V ‹CommSemiring K› ‹CommSemiring K›
    (coefficientAlgebra K p r) ‹AddCommMonoid V› ‹Module K V› ‹Module.Free K V›

end Module

section Semiring

variable (K : Type u) (A : Type v) [CommSemiring K] [Semiring A] [Algebra K A]
variable (p r : ℕ) [ExpChar K p]

instance instSemiring : Semiring (twistObject K A p r) := by
  let scalarExtension :
      ∀ (R S : Type u) (B : Type v)
        [CommSemiring R] [CommSemiring S] [Semiring B]
        [Algebra R S] [Algebra R B], Semiring (S ⊗[R] B) :=
    fun R S B _ _ _ _ _ => inferInstance
  unfold twistObject
  exact @scalarExtension K K A _ _ _ (coefficientAlgebra K p r) ‹Algebra K A›

/-- The new scalar action multiplies the coefficient factor without Frobenius. -/
instance (priority := 1100) instAlgebra : Algebra K (twistObject K A p r) := by
  let scalarExtension :
      ∀ (R S : Type u) (B : Type v)
        [CommSemiring R] [CommSemiring S] [Semiring B]
        [Algebra R S] [Algebra R B], Algebra S (S ⊗[R] B) :=
    fun R S B _ _ _ _ _ => inferInstance
  unfold twistObject
  exact @scalarExtension K K A _ _ _ (coefficientAlgebra K p r) ‹Algebra K A›

/-- The public module agrees with the module induced by the coefficient-self algebra. -/
theorem instAlgebra_toModule :
    @Algebra.toModule K (twistObject K A p r) _ _ (instAlgebra K A p r) =
      (inferInstance : Module K (twistObject K A p r)) := rfl

/-- The public scalar action agrees with the scalar action of the coefficient-self algebra. -/
theorem instAlgebra_toSMul :
    (instAlgebra K A p r).toSMul =
      (inferInstance : SMul K (twistObject K A p r)) := rfl

/-- Scalar extension commutes with the tensor square, with coefficients first. -/
def distrib : twistObject K (A ⊗[K] A) p r ≃ₗ[K]
    twistObject K A p r ⊗[K] twistObject K A p r := by
  let scalarExtension :
      ∀ (R S : Type u) (B : Type v)
        [CommSemiring R] [CommSemiring S] [Semiring B]
        [Algebra R S] [Algebra R B],
        S ⊗[R] (B ⊗[R] B) ≃ₗ[S] (S ⊗[R] B) ⊗[S] (S ⊗[R] B) :=
    fun R S B _ _ _ _ _ =>
      TensorProduct.AlgebraTensorModule.distribBaseChange R S B B
  unfold twistObject
  exact @scalarExtension K K A _ _ _ (coefficientAlgebra K p r) ‹Algebra K A›

/-- Tensor distribution retains the coefficient in the first tensor factor. -/
@[simp]
theorem distrib_tmul (c : K) (a b : A) :
    distrib K A p r (tmul K (A ⊗[K] A) p r c (a ⊗ₜ[K] b)) =
      tmul K A p r c a ⊗ₜ[K] tmul K A p r 1 b := by
  rfl

/-- Scalars enter through the coefficient factor. -/
@[simp]
theorem algebraMap_twistObject (c : K) :
    algebraMap K (twistObject K A p r) c = tmul K A p r c 1 := by
  rfl

/-- The right inclusion into the coefficient-first Frobenius twist, regarded as a
ring homomorphism. It sends `a` to `1 ⊗ a` and need not preserve the new ordinary
coefficient algebra structure. -/
def includeRight : A →+* twistObject K A p r := by
  let rightInclusion :
      ∀ (R S : Type u) (B : Type v)
        [CommSemiring R] [CommSemiring S] [Semiring B]
        [Algebra R S] [Algebra R B], B →+* S ⊗[R] B :=
    fun R S B _ _ _ _ _ =>
      (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := B)).toRingHom
  unfold twistObject
  exact @rightInclusion K K A _ _ _ (coefficientAlgebra K p r) ‹Algebra K A›

/-- The right inclusion is the pure tensor with coefficient one. -/
@[simp]
theorem includeRight_apply (a : A) :
    includeRight K A p r a = tmul K A p r 1 a := by
  rfl

/-- The right inclusion sends an original scalar to its Frobenius power under
 the new ordinary coefficient map. -/
theorem includeRight_algebraMap (c : K) :
    includeRight K A p r (algebraMap K A c) =
      algebraMap K (twistObject K A p r) (c ^ (p ^ r)) := by
  rw [includeRight_apply, algebraMap_twistObject]
  simpa only [Algebra.smul_def, mul_one] using (balance K A p r c 1 (1 : A)).symm

/-- The right inclusion is semilinear for iterated coefficient Frobenius. -/
theorem includeRight_smul (c : K) (a : A) :
    includeRight K A p r (c • a) =
      (c ^ (p ^ r)) • includeRight K A p r a := by
  simpa only [includeRight_apply, smul_tmul, mul_one] using
    (balance K A p r c 1 a).symm

/-- Extend a Frobenius-semilinear ring homomorphism into the given central `K`-algebra.
The result is linear for the new coefficient action; the original algebra structures on
`A` and `B` are unchanged. -/
def lift (B : Type w) [Semiring B] [Algebra K B] (f : A →+* B)
    (hf : ∀ d : K, f (algebraMap K A d) = algebraMap K B (d ^ (p ^ r))) :
    twistObject K A p r →ₐ[K] B := by
  -- Bind the adjunction while the old and new scalar roles are still distinct.
  let scalarExtension := private_decl% (@baseChangeLift)
  unfold twistObject
  exact @scalarExtension K K A B _ _ _ _
    (coefficientAlgebra K p r) ‹Algebra K A› ‹Algebra K B› f hf

/-- The balanced lift multiplies the coefficient by the image of the original factor. -/
@[simp]
theorem lift_tmul (B : Type w) [Semiring B] [Algebra K B] (f : A →+* B)
    (hf : ∀ d : K, f (algebraMap K A d) = algebraMap K B (d ^ (p ^ r)))
    (c : K) (a : A) :
    lift K A p r B f hf (tmul K A p r c a) = algebraMap K B c * f a := by
  change c • f a = algebraMap K B c * f a
  exact Algebra.smul_def c (f a)

/-- Algebra maps out of the twist are determined by the original algebra factor. -/
@[ext]
theorem algHom_ext {B : Type w} [Semiring B] [Algebra K B]
    {g h : twistObject K A p r →ₐ[K] B}
    (hgh : ∀ a : A, g (tmul K A p r 1 a) = h (tmul K A p r 1 a)) : g = h := by
  apply AlgHom.coe_addMonoidHom_injective
  apply ext K A p r
  intro c a
  change g (tmul K A p r c a) = h (tmul K A p r c a)
  have ht : tmul K A p r c a = c • tmul K A p r 1 a := by
    rw [smul_tmul, mul_one]
  rw [ht, map_smul, map_smul, hgh]

/-- The balanced lift is the unique new-`K` algebra map extending the given ring map. -/
theorem lift_unique (B : Type w) [Semiring B] [Algebra K B] (f : A →+* B)
    (hf : ∀ d : K, f (algebraMap K A d) = algebraMap K B (d ^ (p ^ r)))
    (g : twistObject K A p r →ₐ[K] B)
    (hg : ∀ a : A, g (tmul K A p r 1 a) = f a) : g = lift K A p r B f hf := by
  apply algHom_ext K A p r
  intro a
  rw [hg, lift_tmul, map_one, one_mul]

end Semiring

end Algebra.FrobeniusTwist

namespace Algebra.FrobeniusTwist

section CommSemiring

variable (K : Type u) (A : Type v) [CommSemiring K] [CommSemiring A] [Algebra K A]
variable (p r : ℕ) [ExpChar K p]

instance instCommSemiring : CommSemiring (twistObject K A p r) := by
  let scalarExtension :
      ∀ (R S : Type u) (B : Type v)
        [CommSemiring R] [CommSemiring S] [CommSemiring B]
        [Algebra R S] [Algebra R B], CommSemiring (S ⊗[R] B) :=
    fun R S B _ _ _ _ _ => inferInstance
  unfold twistObject
  exact @scalarExtension K K A _ _ _ (coefficientAlgebra K p r) ‹Algebra K A›

end CommSemiring

section Ring

variable (K : Type u) (A : Type v) [CommRing K] [Semiring A] [Algebra K A]
variable (p r : ℕ) [ExpChar K p]

/-- The stock tensor ring structure, with the old and new scalar roles bound separately. -/
instance instRing : Ring (twistObject K A p r) := by
  let scalarExtension :
      ∀ (R S : Type u) (B : Type v)
        [CommSemiring R] [CommRing S] [Semiring B]
        [Algebra R S] [Algebra R B], Ring (S ⊗[R] B) :=
    fun R S B _ _ _ _ _ => inferInstance
  unfold twistObject
  exact @scalarExtension K K A _ _ _ (coefficientAlgebra K p r) ‹Algebra K A›

/-- The tensor ring structure retains the existing semiring structure. -/
theorem instRing_toSemiring :
    (instRing K A p r).toSemiring = instSemiring K A p r := rfl

/-- Integer scalars enter the twist through the coefficient factor. -/
@[simp]
theorem intCast_twistObject (z : ℤ) :
    (z : twistObject K A p r) = tmul K A p r (z : K) 1 := rfl

end Ring

section CommRing

variable (K : Type u) (A : Type v) [CommRing K] [CommSemiring A] [Algebra K A]
variable (p r : ℕ) [ExpChar K p]

/-- The stock commutative tensor ring structure on the Frobenius scalar extension. -/
instance instCommRing : CommRing (twistObject K A p r) := by
  let scalarExtension :
      ∀ (R S : Type u) (B : Type v)
        [CommSemiring R] [CommRing S] [CommSemiring B]
        [Algebra R S] [Algebra R B], CommRing (S ⊗[R] B) :=
    fun R S B _ _ _ _ _ => inferInstance
  unfold twistObject
  exact @scalarExtension K K A _ _ _ (coefficientAlgebra K p r) ‹Algebra K A›

/-- The commutative tensor ring retains the transported ring structure. -/
theorem instCommRing_toRing :
    (instCommRing K A p r).toRing = instRing K A p r := rfl

/-- The commutative tensor ring retains the existing commutative semiring structure. -/
theorem instCommRing_toCommSemiring :
    @CommRing.toCommSemiring (twistObject K A p r) (instCommRing K A p r) =
      instCommSemiring K A p r := rfl

end CommRing

end Algebra.FrobeniusTwist

namespace Algebra.FrobeniusTwist

variable (K : Type u) (A : Type v) [CommSemiring K] [Semiring A]
variable (p r : ℕ) [ExpChar K p]

/-- The canonical scalar-extension bialgebra uses the given bialgebra on `A`. -/
instance (priority := 1100) instBialgebra [Bialgebra K A] :
    Bialgebra K (twistObject K A p r) := by
  let scalarExtension :
      ∀ (R S : Type u) (B : Type v)
        [CommSemiring R] [CommSemiring S] [Semiring B]
        [Algebra R S] [Bialgebra R B], Bialgebra S (S ⊗[R] B) :=
    fun R S B _ _ _ _ _ => inferInstance
  unfold twistObject
  exact @scalarExtension K K A _ _ _ (coefficientAlgebra K p r) ‹Bialgebra K A›

/-- The coalgebra parent of the canonical scalar-extension bialgebra. -/
instance instCoalgebra [Bialgebra K A] : Coalgebra K (twistObject K A p r) :=
  (instBialgebra K A p r).toCoalgebra

/-- The canonical scalar-extension Hopf algebra uses the given Hopf algebra on `A`. -/
instance (priority := 1100) instHopfAlgebra [HopfAlgebra K A] :
    HopfAlgebra K (twistObject K A p r) := by
  let scalarExtension :
      ∀ (R S : Type u) (B : Type v)
        [CommSemiring R] [CommSemiring S] [Semiring B]
        [Algebra R S] [HopfAlgebra R B], HopfAlgebra S (S ⊗[R] B) :=
    fun R S B _ _ _ _ _ => inferInstance
  unfold twistObject
  exact @scalarExtension K K A _ _ _ (coefficientAlgebra K p r) ‹HopfAlgebra K A›

/-- The scalar-extension bialgebra retains the coefficient-self algebra. -/
theorem instBialgebra_toAlgebra [Bialgebra K A] :
    (instBialgebra K A p r).toAlgebra = instAlgebra K A p r := rfl

/-- The bare coalgebra uses the coalgebra of the scalar-extension bialgebra. -/
theorem instBialgebra_toCoalgebra [Bialgebra K A] :
    (instBialgebra K A p r).toCoalgebra =
      (inferInstance : Coalgebra K (twistObject K A p r)) := rfl

/-- The scalar-extension Hopf algebra retains the scalar-extension bialgebra. -/
theorem instHopfAlgebra_toBialgebra [HopfAlgebra K A] :
    (instHopfAlgebra K A p r).toHopfAlgebraStruct.toBialgebra =
      instBialgebra K A p r := rfl

/-- The counit applies Frobenius to the original counit before multiplying by the coefficient. -/
@[simp]
theorem counit_tmul [Bialgebra K A] (c : K) (a : A) :
    Coalgebra.counit (R := K) (tmul K A p r c a) =
      c * (Coalgebra.counit (R := K) a) ^ (p ^ r) := by
  change (Coalgebra.counit (R := K) a) ^ (p ^ r) * c = _
  exact mul_comm _ _

/-- Comultiplication is the original comultiplication followed by tensor distribution. -/
theorem comul_tmul [Bialgebra K A] (c : K) (a : A) :
    Coalgebra.comul (R := K) (tmul K A p r c a) =
      distrib K A p r (tmul K (A ⊗[K] A) p r c (Coalgebra.comul (R := K) a)) := by
  have h := @baseChange_comul_tmul K K A _ _ _
    (coefficientAlgebra K p r) ‹Bialgebra K A› c a
  unfold distrib tmul instCoalgebra instBialgebra
  dsimp +instances only [baseChangeType, baseChangeDistrib, baseChangeTmul,
    twistObject, instSemiring, instCommSemiring, instModule,
    instDistribMulAction, instSMul, instAlgebra] at h ⊢
  exact h

/-- The antipode acts on the original algebra factor. -/
@[simp]
theorem antipode_tmul [HopfAlgebra K A] (c : K) (a : A) :
    HopfAlgebra.antipode K (tmul K A p r c a) =
      tmul K A p r c (HopfAlgebra.antipode K a) := rfl

end Algebra.FrobeniusTwist

namespace Algebra.FrobeniusTwist

variable (K : Type u) (A : Type v) [CommSemiring K] [CommSemiring A]
variable (p r : ℕ) [ExpChar K p]

/- The original counit splits the algebra map, so characteristic transport supplies
absolute Frobenius without an additional assumption on the caller. -/
private def relativeAlgHom [Bialgebra K A] : twistObject K A p r →ₐ[K] A :=
  let _ : ExpChar A p :=
    expChar_of_injective_algebraMap (R := K) (Bialgebra.algebraMap_injective (R := K) A) p
  lift K A p r A (iterateFrobenius A p r)
    (fun d => RingHom.congr_fun ((algebraMap K A).iterateFrobenius_comm p r).symm d)

private theorem relativeAlgHom_tmul [Bialgebra K A] (c : K) (a : A) :
    relativeAlgHom K A p r (tmul K A p r c a) =
      algebraMap K A c * a ^ (p ^ r) := by
  let _ : ExpChar A p :=
    expChar_of_injective_algebraMap (R := K) (Bialgebra.algebraMap_injective (R := K) A) p
  exact lift_tmul K A p r A (iterateFrobenius A p r)
    (fun d => RingHom.congr_fun ((algebraMap K A).iterateFrobenius_comm p r).symm d) c a

private theorem relativeAlgHom_counit [Bialgebra K A] :
    (Bialgebra.counitAlgHom K A).comp (relativeAlgHom K A p r) =
      Bialgebra.counitAlgHom K (twistObject K A p r) := by
  apply AlgHom.coe_addMonoidHom_injective
  apply Algebra.FrobeniusTwist.ext K A p r
  intro c a
  change (Bialgebra.counitAlgHom K A)
    (relativeAlgHom K A p r (tmul K A p r c a)) =
      Coalgebra.counit (R := K) (tmul K A p r c a)
  rw [relativeAlgHom_tmul, map_mul, map_pow,
    (Bialgebra.counitAlgHom K A).commutes]
  exact (counit_tmul K A p r c a).symm

private theorem relativeAlgHom_distrib [Bialgebra K A] (c : K) (t : A ⊗[K] A) :
    Algebra.TensorProduct.map (relativeAlgHom K A p r) (relativeAlgHom K A p r)
        (distrib K A p r (tmul K (A ⊗[K] A) p r c t)) =
      relativeAlgHom K (A ⊗[K] A) p r (tmul K (A ⊗[K] A) p r c t) := by
  let F := Algebra.TensorProduct.map (relativeAlgHom K A p r) (relativeAlgHom K A p r)
  let D := distrib K A p r
  let G := relativeAlgHom K (A ⊗[K] A) p r
  change F (D (tmul K (A ⊗[K] A) p r c t)) = G (tmul K (A ⊗[K] A) p r c t)
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
      calc
        _ = F (tmul K A p r c a ⊗ₜ[K] tmul K A p r 1 b) :=
          congrArg F (distrib_tmul K A p r c a b)
        _ = relativeAlgHom K A p r (tmul K A p r c a) ⊗ₜ[K]
            relativeAlgHom K A p r (tmul K A p r 1 b) :=
          Algebra.TensorProduct.map_tmul _ _ _ _
        _ = _ := by
          change relativeAlgHom K A p r (tmul K A p r c a) ⊗ₜ[K]
              relativeAlgHom K A p r (tmul K A p r 1 b) =
            relativeAlgHom K (A ⊗[K] A) p r (tmul K (A ⊗[K] A) p r c (a ⊗ₜ[K] b))
          simp only [relativeAlgHom_tmul, map_one, one_mul, Algebra.TensorProduct.tmul_pow,
            ← Algebra.smul_def, TensorProduct.smul_tmul']
  | add x y hx hy =>
      have hD := (congrArg D (tmul_add K (A ⊗[K] A) p r c x y)).trans (map_add D _ _)
      have hG := (congrArg G (tmul_add K (A ⊗[K] A) p r c x y)).trans (map_add G _ _)
      exact ((congrArg F hD).trans (map_add F _ _)).trans
        ((congrArg₂ (· + ·) hx hy).trans hG.symm)

private theorem relativeAlgHom_comul [Bialgebra K A] :
    (Algebra.TensorProduct.map (relativeAlgHom K A p r) (relativeAlgHom K A p r)).comp
        (Bialgebra.comulAlgHom K (twistObject K A p r)) =
      (Bialgebra.comulAlgHom K A).comp (relativeAlgHom K A p r) := by
  apply AlgHom.coe_addMonoidHom_injective
  apply Algebra.FrobeniusTwist.ext K A p r
  intro c a
  change Algebra.TensorProduct.map (relativeAlgHom K A p r) (relativeAlgHom K A p r)
      (Coalgebra.comul (R := K) (tmul K A p r c a)) =
    (Bialgebra.comulAlgHom K A) (relativeAlgHom K A p r (tmul K A p r c a))
  calc
    _ = Algebra.TensorProduct.map (relativeAlgHom K A p r) (relativeAlgHom K A p r)
        (distrib K A p r (tmul K (A ⊗[K] A) p r c (Coalgebra.comul (R := K) a))) :=
      congrArg (Algebra.TensorProduct.map (relativeAlgHom K A p r) (relativeAlgHom K A p r))
        (comul_tmul K A p r c a)
    _ = relativeAlgHom K (A ⊗[K] A) p r
        (tmul K (A ⊗[K] A) p r c (Coalgebra.comul (R := K) a)) :=
      relativeAlgHom_distrib K A p r c (Coalgebra.comul (R := K) a)
    _ = algebraMap K (A ⊗[K] A) c * ((Bialgebra.comulAlgHom K A) a) ^ (p ^ r) :=
      relativeAlgHom_tmul K (A ⊗[K] A) p r c ((Bialgebra.comulAlgHom K A) a)
    _ = (Bialgebra.comulAlgHom K A) (algebraMap K A c * a ^ (p ^ r)) := by
      rw [map_mul, map_pow, (Bialgebra.comulAlgHom K A).commutes]
    _ = _ := congrArg (Bialgebra.comulAlgHom K A) (relativeAlgHom_tmul K A p r c a).symm

private theorem relativeAlgHom_range_eq_span_pow [Bialgebra K A] :
    (relativeAlgHom K A p r).range.toSubmodule =
      Submodule.span K (Set.range fun a : A ↦ a ^ (p ^ r)) := by
  let N : Submodule K A := Submodule.span K (Set.range fun a : A ↦ a ^ (p ^ r))
  let f : @baseChangeType K K A _ _ _ (coefficientAlgebra K p r)
      (inferInstance : Module K A) →+ A :=
    (relativeAlgHom K A p r).toAddMonoidHom
  have hφ (x : twistObject K A p r) : relativeAlgHom K A p r x ∈ N := by
    change f x ∈ N
    induction x using TensorProduct.inductionOn with
    | tmul c a =>
        have h : algebraMap K A c * a ^ (p ^ r) ∈ N := by
          simpa only [Algebra.smul_def] using
            N.smul_mem c (Submodule.subset_span ⟨a, rfl⟩)
        change relativeAlgHom K A p r (tmul K A p r c a) ∈ N
        rw [relativeAlgHom_tmul]
        exact h
    | add x y hx hy =>
        rw [map_add]
        exact N.add_mem hx hy
  apply le_antisymm
  · intro b hb
    obtain ⟨x, hx⟩ :=
      (AlgHom.mem_range (relativeAlgHom K A p r)).mp
        ((Subalgebra.mem_toSubmodule _).mp hb)
    exact hx ▸ hφ x
  · refine Submodule.span_le.mpr ?_
    rintro b ⟨a, rfl⟩
    apply (Subalgebra.mem_toSubmodule _).mpr
    apply (AlgHom.mem_range (relativeAlgHom K A p r)).mpr
    refine ⟨tmul K A p r 1 a, ?_⟩
    simp only [relativeAlgHom_tmul, map_one, one_mul]

end Algebra.FrobeniusTwist

namespace Bialgebra

variable (K : Type u) (A : Type v) [CommSemiring K] [CommSemiring A] [Bialgebra K A]
variable (p r : ℕ) [ExpChar K p]

/-- The relative Frobenius from the coefficient-first scalar extension to the original
bialgebra. Its value on `c ⊗ a` is `algebraMap K A c * a ^ (p ^ r)`. -/
def relativeFrobenius : Algebra.FrobeniusTwist.twistObject K A p r →ₐc[K] A :=
  BialgHom.ofAlgHom (private_decl% (Algebra.FrobeniusTwist.relativeAlgHom K A p r))
    (by exact Algebra.FrobeniusTwist.relativeAlgHom_counit K A p r)
    (by exact Algebra.FrobeniusTwist.relativeAlgHom_comul K A p r)

private theorem relativeFrobenius_toAlgHom :
    (relativeFrobenius K A p r).toAlgHom =
      Algebra.FrobeniusTwist.relativeAlgHom K A p r := rfl

/-- The relative Frobenius retains the coefficient and powers the original algebra factor. -/
@[simp]
theorem relativeFrobenius_tmul (c : K) (a : A) :
    relativeFrobenius K A p r (Algebra.FrobeniusTwist.tmul K A p r c a) =
      algebraMap K A c * a ^ (p ^ r) := by
  exact (congrArg
    (fun f : Algebra.FrobeniusTwist.twistObject K A p r →ₐ[K] A =>
      f (Algebra.FrobeniusTwist.tmul K A p r c a))
    (relativeFrobenius_toAlgHom K A p r)).trans
      (Algebra.FrobeniusTwist.relativeAlgHom_tmul K A p r c a)

/-- Relative Frobenius after the right inclusion is the `p ^ r`th power on the
original bialgebra. -/
theorem relativeFrobenius_includeRight (a : A) :
    relativeFrobenius K A p r (Algebra.FrobeniusTwist.includeRight K A p r a) =
      a ^ (p ^ r) := by
  simp only [Algebra.FrobeniusTwist.includeRight_apply, relativeFrobenius_tmul,
    map_one, one_mul]

/-- The right inclusion after relative Frobenius is the `p ^ r`th power on the
same coefficient-first Frobenius twist. -/
theorem includeRight_relativeFrobenius
    (x : Algebra.FrobeniusTwist.twistObject K A p r) :
    Algebra.FrobeniusTwist.includeRight K A p r (relativeFrobenius K A p r x) =
      x ^ (p ^ r) := by
  let _ : ExpChar (Algebra.FrobeniusTwist.twistObject K A p r) p :=
    expChar_of_injective_algebraMap (R := K)
      (Bialgebra.algebraMap_injective (R := K)
        (Algebra.FrobeniusTwist.twistObject K A p r)) p
  -- Stock Frobenius is additive on all elements before the pure-tensor comparison.
  let powerMap :
      Algebra.FrobeniusTwist.twistObject K A p r →+
        Algebra.FrobeniusTwist.twistObject K A p r :=
    (iterateFrobenius (Algebra.FrobeniusTwist.twistObject K A p r) p r).toAddMonoidHom
  have h :
      (Algebra.FrobeniusTwist.includeRight K A p r).toAddMonoidHom.comp
          (relativeFrobenius K A p r).toAlgHom.toAddMonoidHom = powerMap := by
    apply Algebra.FrobeniusTwist.ext K A p r
    intro c a
    change Algebra.FrobeniusTwist.includeRight K A p r
        (relativeFrobenius K A p r (Algebra.FrobeniusTwist.tmul K A p r c a)) =
      (Algebra.FrobeniusTwist.tmul K A p r c a) ^ (p ^ r)
    rw [relativeFrobenius_tmul, Algebra.FrobeniusTwist.includeRight_apply]
    calc
      Algebra.FrobeniusTwist.tmul K A p r 1 (algebraMap K A c * a ^ (p ^ r)) =
          Algebra.FrobeniusTwist.tmul K A p r 1 (c • a ^ (p ^ r)) := by
        rw [Algebra.smul_def]
      _ = Algebra.FrobeniusTwist.tmul K A p r (c ^ (p ^ r)) (a ^ (p ^ r)) := by
        simpa only [mul_one] using
          (Algebra.FrobeniusTwist.balance K A p r c 1 (a ^ (p ^ r))).symm
      _ = (Algebra.FrobeniusTwist.tmul K A p r c a) ^ (p ^ r) := by
        -- Bind the stock power formula before the two scalar carriers coincide.
        let tensorPower :
            ∀ (R S : Type u) (B : Type v)
              [CommSemiring R] [CommSemiring S] [Semiring B]
              [Algebra R S] [Algebra R B] (c : S) (a : B) (n : ℕ),
              (c ⊗ₜ[R] a) ^ n = (c ^ n) ⊗ₜ[R] (a ^ n) :=
          fun R S B _ _ _ _ _ c a n =>
            Algebra.TensorProduct.tmul_pow (R := R) c a n
        exact (@tensorPower K K A _ _ _
          (Algebra.FrobeniusTwist.coefficientAlgebra K p r) (‹Bialgebra K A›).toAlgebra
          c a (p ^ r)).symm
  exact DFunLike.congr_fun h x

/-- Each element killed by relative Frobenius has vanishing `p ^ r`th power.
This is an elementwise assertion, not vanishing of a power of its kernel ideal. -/
theorem pow_eq_zero_of_relativeFrobenius_eq_zero
    {x : Algebra.FrobeniusTwist.twistObject K A p r}
    (hx : relativeFrobenius K A p r x = 0) :
    x ^ (p ^ r) = 0 := by
  rw [← includeRight_relativeFrobenius K A p r x, hx, map_zero]

/-- Each element killed by relative Frobenius is nilpotent. -/
theorem isNilpotent_of_relativeFrobenius_eq_zero
    {x : Algebra.FrobeniusTwist.twistObject K A p r}
    (hx : relativeFrobenius K A p r x = 0) :
    IsNilpotent x := by
  exact IsNilpotent.mk x (p ^ r)
    (pow_eq_zero_of_relativeFrobenius_eq_zero K A p r hx)

/-- The image of relative Frobenius is the scalar span of the `p ^ r`th powers.
Over an imperfect field this need not be the raw set of powers. -/
theorem relativeFrobenius_range_eq_span_pow :
    (relativeFrobenius K A p r).toAlgHom.range.toSubmodule =
      Submodule.span K (Set.range fun a : A ↦ a ^ (p ^ r)) := by
  rw [relativeFrobenius_toAlgHom]
  exact Algebra.FrobeniusTwist.relativeAlgHom_range_eq_span_pow K A p r

end Bialgebra
