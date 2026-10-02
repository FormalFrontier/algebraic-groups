/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.Vector
public import AlgebraicGroups.GroupScheme.AffineHomOver
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.LinearAlgebra.Dual.Basis

/-!
# Morphisms and products of vector group schemes

A linear map induces a morphism of affine group schemes by pullback of linear
polynomial coordinates. This construction does not require finite dimension.
Finite bases additionally identify a vector group with a categorical product
of additive groups, including the empty product.
-/

public section

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [Field K]
  (V : Type u) [AddCommGroup V] [Module K V]
  (W : Type u) [AddCommGroup W] [Module K W]

/-- Polynomial coordinates classify all maps to the underlying vector scheme. -/
@[expose] def vectorGroupHomOverEquiv (X : Over (Spec (.of K))) :
    (X ⟶ (vectorGroupScheme K V).X) ≃
      (Module.Dual K V →ₗ[K] ((algΓ (.of K)).obj X).unop) :=
  (affineSpecHomOverEquiv K X (vectorGroupCoordinateRing K V)).trans
    (SymmetricAlgebra.lift.symm)

/-- Pullback of polynomial coordinates as a morphism of bialgebras. -/
@[expose] def vectorGroupCoordinateBialgHom (f : V →ₗ[K] W) :
    vectorGroupCoordinateRing K W →ₐc[K] vectorGroupCoordinateRing K V :=
  BialgHom.ofAlgHom (vectorGroupCoordinateMap K V W f) (by
    apply SymmetricAlgebra.algHom_ext
    ext φ
    simp [vectorGroupCoordinateMap_ι, SymmetricAlgebra.algebraMapInv_ι]) (by
    apply SymmetricAlgebra.algHom_ext
    ext φ
    simp [vectorGroupCoordinateMap_ι,
      Algebra.TensorProduct.map_tmul])

@[simp]
theorem vectorGroupCoordinateBialgHom_ι (f : V →ₗ[K] W) (φ : Module.Dual K W) :
    vectorGroupCoordinateBialgHom K V W f (SymmetricAlgebra.ι K _ φ) =
      SymmetricAlgebra.ι K _ (φ.comp f) :=
  vectorGroupCoordinateMap_ι K V W f φ

@[simp]
theorem vectorGroupCoordinateBialgHom_id :
    vectorGroupCoordinateBialgHom K V V LinearMap.id =
      BialgHom.id K (vectorGroupCoordinateRing K V) := by
  apply BialgHom.coe_toAlgHom_injective
  apply SymmetricAlgebra.algHom_ext
  ext φ
  simp

@[simp]
theorem vectorGroupCoordinateBialgHom_comp
    (U : Type u) [AddCommGroup U] [Module K U]
    (f : V →ₗ[K] W) (g : W →ₗ[K] U) :
    vectorGroupCoordinateBialgHom K V U (g.comp f) =
      (vectorGroupCoordinateBialgHom K V W f).comp
        (vectorGroupCoordinateBialgHom K W U g) := by
  apply BialgHom.coe_toAlgHom_injective
  apply SymmetricAlgebra.algHom_ext
  ext φ
  simp [LinearMap.comp_assoc]

/-- The genuine group-scheme map associated to a linear map. -/
@[expose] def vectorGroupSchemeMap (f : V →ₗ[K] W) :
    vectorGroupScheme K V ⟶ vectorGroupScheme K W :=
  (hopfSpec (.of K)).map
    (CommHopfAlgCat.ofHom (vectorGroupCoordinateBialgHom K V W f)).op

@[simp]
theorem vectorGroupSchemeMap_left (f : V →ₗ[K] W) :
    (vectorGroupSchemeMap K V W f).hom.hom.left =
      Spec.map (CommRingCat.ofHom (vectorGroupCoordinateMap K V W f).toRingHom) :=
  rfl

@[simp]
theorem vectorGroupSchemeMap_id :
    vectorGroupSchemeMap K V V LinearMap.id = 𝟙 (vectorGroupScheme K V) := by
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  rw [vectorGroupSchemeMap_left]
  change Spec.map (CommRingCat.ofHom
      (vectorGroupCoordinateMap K V V LinearMap.id).toRingHom) = 𝟙 _
  rw [← Spec.map_id]
  congr 1
  exact congrArg (fun h : vectorGroupCoordinateRing K V →ₐc[K]
      vectorGroupCoordinateRing K V ↦
        CommRingCat.ofHom (h : vectorGroupCoordinateRing K V →ₐ[K]
          vectorGroupCoordinateRing K V).toRingHom)
    (vectorGroupCoordinateBialgHom_id K V)

@[simp]
theorem vectorGroupSchemeMap_comp
    (U : Type u) [AddCommGroup U] [Module K U]
    (f : V →ₗ[K] W) (g : W →ₗ[K] U) :
    vectorGroupSchemeMap K V U (g.comp f) =
      vectorGroupSchemeMap K V W f ≫ vectorGroupSchemeMap K W U g := by
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  rw [vectorGroupSchemeMap_left]
  change Spec.map (CommRingCat.ofHom
      (vectorGroupCoordinateMap K V U (g.comp f)).toRingHom) =
    (vectorGroupSchemeMap K V W f).hom.hom.left ≫
      (vectorGroupSchemeMap K W U g).hom.hom.left
  have h : Spec.map (CommRingCat.ofHom
      (vectorGroupCoordinateMap K V U (g.comp f)).toRingHom) =
      Spec.map (CommRingCat.ofHom (vectorGroupCoordinateMap K V W f).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (vectorGroupCoordinateMap K W U g).toRingHom) := by
    rw [← Spec.map_comp]
    congr 1
    exact congrArg (fun h : vectorGroupCoordinateRing K U →ₐc[K]
        vectorGroupCoordinateRing K V ↦
          CommRingCat.ofHom (h : vectorGroupCoordinateRing K U →ₐ[K]
            vectorGroupCoordinateRing K V).toRingHom)
      (vectorGroupCoordinateBialgHom_comp K V W U f g)
  convert h using 1
  simp only [vectorGroupSchemeMap_left]
  exact Iff.rfl

/-- The vector-group construction is covariant in arbitrary vector spaces. -/
@[expose] def vectorGroupSchemeFunctor : ModuleCat.{u} K ⥤ Grp (Over (Spec (.of K))) where
  obj M := vectorGroupScheme K M
  map f := vectorGroupSchemeMap K _ _ f.hom
  map_id M := by
    exact vectorGroupSchemeMap_id K M
  map_comp f g := by
    exact vectorGroupSchemeMap_comp K _ _ _ f.hom g.hom

/-- On finite-dimensional tensor points, a scheme map is tensoring the linear map
with the identity on the test algebra. This holds for the zero algebra too. -/
theorem vectorGroupSchemeMap_points [FiniteDimensional K V] [FiniteDimensional K W]
    (R : Type u) [CommRing R] [Algebra K R] (f : V →ₗ[K] W) (x : V ⊗[K] R) :
    (vectorGroupMulEquivPoints K V R (.ofAdd x)) ≫
      (vectorGroupSchemeMap K V W f).hom.hom =
      vectorGroupMulEquivPoints K W R (.ofAdd
        (TensorProduct.map f (LinearMap.id : R →ₗ[K] R) x)) := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, vectorGroupMulEquivPoints_apply_left, vectorGroupSchemeMap_left,
    vectorGroupMulEquivPoints_apply_left]
  have h : Spec.map (CommRingCat.ofHom
      (vectorGroupMulEquivAlgHom K V R (.ofAdd x)).ofConv.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (vectorGroupCoordinateMap K V W f).toRingHom) =
      Spec.map (CommRingCat.ofHom
        (vectorGroupMulEquivAlgHom K W R (.ofAdd
          (TensorProduct.map f (LinearMap.id : R →ₗ[K] R) x))).ofConv.toRingHom) := by
    rw [← Spec.map_comp]
    congr 1
    exact congrArg (fun h : vectorGroupCoordinateRing K W →ₐ[K] R ↦
        CommRingCat.ofHom h.toRingHom)
      (vectorGroupMulEquivAlgHom_linearMap K V R W f x).symm
  convert h using 1
  exact Iff.rfl

/-- The Hopf-algebra pullback of a chosen additive coordinate. -/
def vectorGroupProjectionBialgHom {i : Type u} (b : Module.Basis i K V) (j : i) :
    additiveGroupCoordinateRing K →ₐc[K] vectorGroupCoordinateRing K V :=
  BialgHom.ofAlgHom
    (SymmetricAlgebra.lift ((SymmetricAlgebra.ι K (Module.Dual K V)).comp
      ((LinearMap.ringLmapEquivSelf K K (Module.Dual K V)).symm (b.coord j)))) (by
    apply SymmetricAlgebra.algHom_ext
    ext; simp [SymmetricAlgebra.algebraMapInv_ι]) (by
    apply SymmetricAlgebra.algHom_ext
    ext; simp [Algebra.TensorProduct.map_tmul])

@[simp]
theorem vectorGroupProjectionBialgHom_coordinate {i : Type u}
    (b : Module.Basis i K V) (j : i) :
    vectorGroupProjectionBialgHom K V b j (additiveGroupCoordinate K) =
      SymmetricAlgebra.ι K (Module.Dual K V) (b.coord j) := by
  simp [vectorGroupProjectionBialgHom, additiveGroupCoordinate]

/-- A basis coordinate as a genuine group-scheme projection onto `Gₐ`. -/
@[expose] def vectorGroupProjection {i : Type u} (b : Module.Basis i K V) (j : i) :
    vectorGroupScheme K V ⟶ additiveGroupScheme K :=
  (hopfSpec (.of K)).map
    (CommHopfAlgCat.ofHom (vectorGroupProjectionBialgHom K V b j)).op

@[simp]
theorem vectorGroupProjection_left {i : Type u}
    (b : Module.Basis i K V) (j : i) :
    (vectorGroupProjection K V b j).hom.hom.left =
      Spec.map (CommRingCat.ofHom
        ((vectorGroupProjectionBialgHom K V b j :
          additiveGroupCoordinateRing K →ₐ[K] vectorGroupCoordinateRing K V)).toRingHom) :=
  rfl

/-- A projection reads off the corresponding dual-basis global coordinate, for
maps from any scheme over the base (not only affine test schemes). -/
theorem vectorGroupProjection_globalCoordinate {i : Type u}
    (b : Module.Basis i K V) (j : i) (X : Over (Spec (.of K)))
    (h : X ⟶ (vectorGroupScheme K V).X) :
    additiveGroupHomOverEquiv K X (h ≫ (vectorGroupProjection K V b j).hom.hom) =
      (vectorGroupHomOverEquiv K V X h) (b.coord j) := by
  have hp : (vectorGroupProjection K V b j).hom.hom =
      (algSpec (.of K)).map (CommAlgCat.ofHom
        (vectorGroupProjectionBialgHom K V b j :
          additiveGroupCoordinateRing K →ₐ[K] vectorGroupCoordinateRing K V)).op := rfl
  rw [hp]
  change (LinearMap.ringLmapEquivSelf K K ((algΓ (.of K)).obj X).unop)
      (SymmetricAlgebra.lift.symm
        (affineSpecHomOverEquiv K X (additiveGroupCoordinateRing K)
          (h ≫ (algSpec (.of K)).map (CommAlgCat.ofHom
            (vectorGroupProjectionBialgHom K V b j :
              additiveGroupCoordinateRing K →ₐ[K] vectorGroupCoordinateRing K V)).op))) =
      (SymmetricAlgebra.lift.symm
        (affineSpecHomOverEquiv K X (vectorGroupCoordinateRing K V) h)) (b.coord j)
  erw [affineSpecHomOverEquiv_comp]
  rw [LinearMap.ringLmapEquivSelf_apply]
  rw [AffineHomOver.symmetricAlgebra_lift_symm_ι K K,
    AffineHomOver.symmetricAlgebra_lift_symm_ι K (Module.Dual K V)]
  change (affineSpecHomOverEquiv K X (vectorGroupCoordinateRing K V) h)
      (vectorGroupProjectionBialgHom K V b j (additiveGroupCoordinate K)) = _
  rw [vectorGroupProjectionBialgHom_coordinate]

/-- The cone of genuine group morphisms onto the chosen basis coordinates. -/
@[expose] def vectorGroupBasisFan {i : Type u} (b : Module.Basis i K V) :
    Limits.Fan (fun _ : i ↦ additiveGroupScheme K) :=
  Limits.Fan.mk (vectorGroupScheme K V) (vectorGroupProjection K V b)

/-- The underlying cone is universal even for nonaffine schemes over the base. -/
@[expose] def vectorGroupBasisFan_forget_isLimit {i : Type u} [Finite i]
    (b : Module.Basis i K V) :
    Limits.IsLimit ((Grp.forget (Over (Spec (.of K)))).mapCone
      (vectorGroupBasisFan K V b)) := by
  classical
  change Limits.IsLimit (Limits.Fan.mk (vectorGroupScheme K V).X
    (fun j : i ↦ (vectorGroupProjection K V b j).hom.hom))
  have hb (j : i) : b.dualBasis j = b.coord j := by
    ext v
    exact b.dualBasis_apply j v
  refine Limits.Fan.IsLimit.mk _ (fun s ↦
    (vectorGroupHomOverEquiv K V s.pt).symm
      (b.dualBasis.constr K (fun j ↦ additiveGroupHomOverEquiv K s.pt (s.proj j)))) ?_ ?_
  · intro s j
    apply (additiveGroupHomOverEquiv K s.pt).injective
    change additiveGroupHomOverEquiv K s.pt
      ((vectorGroupHomOverEquiv K V s.pt).symm
        (b.dualBasis.constr K (fun j ↦ additiveGroupHomOverEquiv K s.pt (s.proj j))) ≫
          (vectorGroupProjection K V b j).hom.hom) =
        additiveGroupHomOverEquiv K s.pt (s.proj j)
    rw [vectorGroupProjection_globalCoordinate]
    rw [← hb]
    simp only [Equiv.apply_symm_apply, Module.Basis.constr_basis]
  · intro s m hm
    apply (vectorGroupHomOverEquiv K V s.pt).injective
    apply b.dualBasis.ext
    intro j
    rw [hb]
    change (vectorGroupHomOverEquiv K V s.pt m) (b.coord j) = _
    rw [← vectorGroupProjection_globalCoordinate K V b j s.pt m]
    have hfac : m ≫ (vectorGroupProjection K V b j).hom.hom = s.proj j := hm j
    rw [hfac]
    rw [← hb j]
    simp only [Module.Basis.constr_basis, Equiv.apply_symm_apply]

/-- Group objects inherit the finite-product universal property of the
underlying schemes. -/
def vectorGroupBasisFan_isLimit {i : Type u} [Finite i]
    (b : Module.Basis i K V) : Limits.IsLimit (vectorGroupBasisFan K V b) :=
  Limits.isLimitOfReflects (Grp.forget (Over (Spec (.of K))))
    (vectorGroupBasisFan_forget_isLimit K V b)

/-- A chosen finite basis identifies the vector group with the literal product
of its one-dimensional additive group factors. -/
def vectorGroupSchemeProductIso {i : Type u} [Finite i]
    (b : Module.Basis i K V) :
    vectorGroupScheme K V ≅ (∏ᶜ fun _ : i ↦ additiveGroupScheme K) :=
  (vectorGroupBasisFan_isLimit K V b).conePointUniqueUpToIso
    (Limits.productIsProduct fun _ : i ↦ additiveGroupScheme K)

@[simp]
theorem vectorGroupSchemeProductIso_hom_π {i : Type u} [Finite i]
    (b : Module.Basis i K V) (j : i) :
    (vectorGroupSchemeProductIso K V b).hom ≫
      Limits.Pi.π (fun _ : i ↦ additiveGroupScheme K) j =
        vectorGroupProjection K V b j :=
  (vectorGroupBasisFan_isLimit K V b).conePointUniqueUpToIso_hom_comp
    (Limits.productIsProduct fun _ : i ↦ additiveGroupScheme K) ⟨j⟩

@[simp]
theorem vectorGroupSchemeProductIso_inv_projection {i : Type u} [Finite i]
    (b : Module.Basis i K V) (j : i) :
    (vectorGroupSchemeProductIso K V b).inv ≫ vectorGroupProjection K V b j =
      Limits.Pi.π (fun _ : i ↦ additiveGroupScheme K) j :=
  (vectorGroupBasisFan_isLimit K V b).conePointUniqueUpToIso_inv_comp
    (Limits.productIsProduct fun _ : i ↦ additiveGroupScheme K) ⟨j⟩

/-- Every zero vector space is terminal as a group scheme, including when
the ambient field and test algebras have arbitrary cardinality. -/
def vectorGroupSchemeZeroIsTerminal [Subsingleton V] :
    Limits.IsTerminal (vectorGroupScheme K V) :=
  (Limits.isLimitEquivIsTerminalOfIsEmpty (Grp (Over (Spec (.of K))))
    (vectorGroupBasisFan K V (Module.Basis.empty V :
      Module.Basis PEmpty.{u+1} K V)))
    (vectorGroupBasisFan_isLimit K V (Module.Basis.empty V :
      Module.Basis PEmpty.{u+1} K V))

/-- The zero vector group is the terminal group object over `Spec K`. -/
def vectorGroupSchemeZeroIso [Subsingleton V] :
    vectorGroupScheme K V ≅ ⊤_ (Grp (Over (Spec (.of K)))) :=
  (vectorGroupSchemeZeroIsTerminal K V).uniqueUpToIso Limits.terminalIsTerminal

/-- The underlying zero-vector scheme is `Spec K` over itself. -/
def vectorGroupUnderlyingZeroIso [Subsingleton V] :
    (vectorGroupScheme K V).X ≅ Over.mk (𝟙 (Spec (.of K))) :=
  ((Limits.isLimitEquivIsTerminalOfIsEmpty (Over (Spec (.of K)))
    ((Grp.forget (Over (Spec (.of K)))).mapCone
      (vectorGroupBasisFan K V (Module.Basis.empty V :
        Module.Basis PEmpty.{u+1} K V))))
    (vectorGroupBasisFan_forget_isLimit K V (Module.Basis.empty V :
      Module.Basis PEmpty.{u+1} K V))).uniqueUpToIso Over.mkIdTerminal

/-- The pullback of a target basis coordinate is the formal polynomial linear
combination of source coordinates. This holds over finite fields as an equality
of polynomial-ring elements, not just of functions on field-valued points. -/
theorem vectorGroupCoordinateMap_basis {i j : Type u} [Fintype i]
    (b : Module.Basis i K V) (c : Module.Basis j K W)
    (f : V →ₗ[K] W) (k : j) :
    vectorGroupCoordinateMap K V W f
        (SymmetricAlgebra.ι K _ (c.coord k)) =
      ∑ s : i, (c.coord k (f (b s))) •
        SymmetricAlgebra.ι K _ (b.coord s) := by
  classical
  rw [vectorGroupCoordinateMap_ι]
  have h := b.sum_dual_apply_smul_coord ((c.coord k).comp f)
  rw [← h]
  simp only [map_sum, map_smul, LinearMap.comp_apply]

/-- The genuine projection after a linear scheme map pulls its additive
coordinate back to the indicated formal sum of source generators. -/
theorem vectorGroupSchemeMap_projection_coordinate {i j : Type u} [Fintype i]
    (b : Module.Basis i K V) (c : Module.Basis j K W)
    (f : V →ₗ[K] W) (k : j) :
    ((vectorGroupCoordinateBialgHom K V W f).comp
      (vectorGroupProjectionBialgHom K W c k)) (additiveGroupCoordinate K) =
      ∑ s : i, (c.coord k (f (b s))) •
        (vectorGroupProjectionBialgHom K V b s) (additiveGroupCoordinate K) := by
  rw [BialgHom.comp_apply, vectorGroupProjectionBialgHom_coordinate]
  simp only [vectorGroupCoordinateBialgHom_ι,
    vectorGroupProjectionBialgHom_coordinate]
  simpa only [vectorGroupCoordinateMap_ι] using
    (vectorGroupCoordinateMap_basis K V W b c f k)

/-- Evaluation of a linear map at target basis coordinate is the corresponding
finite linear combination of source coordinate values. -/
theorem vectorGroupTensorDualEquiv_basis
    [FiniteDimensional K V] [FiniteDimensional K W]
    {i j : Type u} [Fintype i]
    (b : Module.Basis i K V) (c : Module.Basis j K W)
    (f : V →ₗ[K] W) (R : Type u) [CommRing R] [Algebra K R]
    (x : V ⊗[K] R) (k : j) :
    vectorGroupTensorDualEquiv K W R
        (TensorProduct.map f (LinearMap.id : R →ₗ[K] R) x) (c.coord k) =
      ∑ s : i, (c.coord k (f (b s))) •
        vectorGroupTensorDualEquiv K V R x (b.coord s) := by
  classical
  rw [vectorGroupTensorDualEquiv_linearMap]
  have h := b.sum_dual_apply_smul_coord ((c.coord k).comp f)
  rw [← h]
  simp only [map_sum, map_smul, LinearMap.comp_apply]

/-- A coordinate of the represented tensor point transforms by the linear-map
coefficients in every commutative test algebra, including the zero algebra. -/
theorem vectorGroupMulEquivAlgHom_basis
    [FiniteDimensional K V] [FiniteDimensional K W]
    {i j : Type u} [Fintype i]
    (b : Module.Basis i K V) (c : Module.Basis j K W)
    (f : V →ₗ[K] W) (R : Type u) [CommRing R] [Algebra K R]
    (x : V ⊗[K] R) (k : j) :
    (vectorGroupMulEquivAlgHom K W R (.ofAdd
      (TensorProduct.map f (LinearMap.id : R →ₗ[K] R) x))).ofConv
        (SymmetricAlgebra.ι K _ (c.coord k)) =
      ∑ s : i, (algebraMap K R (c.coord k (f (b s)))) *
        (vectorGroupMulEquivAlgHom K V R (.ofAdd x)).ofConv
          (SymmetricAlgebra.ι K _ (b.coord s)) := by
  rw [vectorGroupMulEquivAlgHom_ι]
  classical
  simp only [vectorGroupTensorDualEquiv_basis K V W b c f R x k,
    vectorGroupMulEquivAlgHom_ι, Algebra.smul_def]

/-- The tensor-valued linear map commutes with arbitrary algebra base change,
without nonzero or flatness hypotheses on the algebra map. -/
theorem vectorGroupSchemeMap_tensor_naturality
    [FiniteDimensional K V] [FiniteDimensional K W]
    (R S : Type u) [CommRing R] [Algebra K R] [CommRing S] [Algebra K S]
    (f : V →ₗ[K] W) (g : R →ₐ[K] S) (x : V ⊗[K] R) :
    TensorProduct.map (LinearMap.id : W →ₗ[K] W) g.toLinearMap
        (TensorProduct.map f (LinearMap.id : R →ₗ[K] R) x) =
      TensorProduct.map f (LinearMap.id : S →ₗ[K] S)
        (TensorProduct.map (LinearMap.id : V →ₗ[K] V) g.toLinearMap x) := by
  apply (vectorGroupTensorDualEquiv K W S).injective
  ext φ
  rw [vectorGroupTensorDualEquiv_naturality,
    vectorGroupTensorDualEquiv_linearMap,
    vectorGroupTensorDualEquiv_linearMap,
    vectorGroupTensorDualEquiv_naturality]

theorem vectorGroupBasis_coordinate_tmul [FiniteDimensional K V]
    {i : Type u} (b : Module.Basis i K V)
    (R : Type u) [CommRing R] [Algebra K R] (v : V) (r : R) (s : i) :
    vectorGroupTensorDualEquiv K V R (v ⊗ₜ[K] r) (b.coord s) =
      (b.coord s v) • r :=
  vectorGroupTensorDualEquiv_tmul K V R v r (b.coord s)

/-- Coordinates of a linear scheme map, transported through the two chosen
literal-product isomorphisms. The vector-scheme map itself is basis-independent. -/
def vectorGroupBasisMap {i j : Type u} [Finite i] [Finite j]
    (b : Module.Basis i K V) (c : Module.Basis j K W) (f : V →ₗ[K] W) :
    (∏ᶜ fun _ : i ↦ additiveGroupScheme K) ⟶
      (∏ᶜ fun _ : j ↦ additiveGroupScheme K) :=
  (vectorGroupSchemeProductIso K V b).inv ≫
    vectorGroupSchemeMap K V W f ≫ (vectorGroupSchemeProductIso K W c).hom

@[simp]
theorem vectorGroupBasisMap_square {i j : Type u} [Finite i] [Finite j]
    (b : Module.Basis i K V) (c : Module.Basis j K W) (f : V →ₗ[K] W) :
    (vectorGroupSchemeProductIso K V b).hom ≫ vectorGroupBasisMap K V W b c f =
      vectorGroupSchemeMap K V W f ≫ (vectorGroupSchemeProductIso K W c).hom := by
  simp [vectorGroupBasisMap]

/-- The chosen-coordinate diagram read back at one actual product projection. -/
theorem vectorGroupBasisMap_projection {i j : Type u} [Finite i] [Finite j]
    (b : Module.Basis i K V) (c : Module.Basis j K W)
    (f : V →ₗ[K] W) (k : j) :
    vectorGroupBasisMap K V W b c f ≫
        Limits.Pi.π (fun _ : j ↦ additiveGroupScheme K) k =
      (vectorGroupSchemeProductIso K V b).inv ≫
        vectorGroupSchemeMap K V W f ≫ vectorGroupProjection K W c k := by
  simp [vectorGroupBasisMap, Category.assoc]

@[simp]
theorem vectorGroupBasisMap_id {i : Type u} [Finite i]
    (b : Module.Basis i K V) :
    vectorGroupBasisMap K V V b b LinearMap.id =
      𝟙 (∏ᶜ fun _ : i ↦ additiveGroupScheme K) := by
  simp [vectorGroupBasisMap]

theorem vectorGroupBasisMap_comp {i j l : Type u} [Finite i] [Finite j] [Finite l]
    (b : Module.Basis i K V) (c : Module.Basis j K W)
    (U : Type u) [AddCommGroup U] [Module K U] (d : Module.Basis l K U)
    (f : V →ₗ[K] W) (g : W →ₗ[K] U) :
    vectorGroupBasisMap K V U b d (g.comp f) =
      vectorGroupBasisMap K V W b c f ≫ vectorGroupBasisMap K W U c d g := by
  simp [vectorGroupBasisMap, Category.assoc]

/-- Successive changes of finite basis compose as native group-scheme maps. -/
theorem vectorGroupBasisMap_changeBasis_comp
    {i j l : Type u} [Finite i] [Finite j] [Finite l]
    (b : Module.Basis i K V) (c : Module.Basis j K V)
    (d : Module.Basis l K V) :
    vectorGroupBasisMap K V V b c LinearMap.id ≫
      vectorGroupBasisMap K V V c d LinearMap.id =
        vectorGroupBasisMap K V V b d LinearMap.id := by
  simpa using (vectorGroupBasisMap_comp K V V b c V d LinearMap.id LinearMap.id).symm

end AlgebraicGeometry
