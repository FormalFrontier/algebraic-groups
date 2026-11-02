/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.GeometricRepresentationBaseChange
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Normal

/-!
# Precomposition and normal-subgroup invariants

`GeometricRepresentation.comap` precomposes a geometric representation with a
morphism of group schemes. Its operators are the original operators evaluated
at the postcomposed points, and it respects identity and composition. For affine
groups, this operation corresponds to changing the coacting coalgebra along the
pullback on global sections.

Over a field, the image of the scalar-extended inclusion of the invariants of a
normal subgroup is preserved by every ambient point. The proof tests fixedness
after every further coefficient algebra, using naturality and normality of the
range of the original point homomorphism.

## Limitations

The coefficient algebras are all objects of `CommAlgCat.{u, u} K`; no comparison
with finitely generated test algebras is asserted. Precomposition and the
invariant-space results do not require affine schemes; the comodule comparison
assumes both groups affine. The module universe is independent of the base
universe. This file does not construct a representation on the invariant subtype
or a quotient action.

## References

* Mathlib's group-valued Yoneda functor, whiskering and normal subgroup objects.
* The all-algebra invariant and scalar-extension criterion for geometric
  representations in this library.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct CategoryTheory.GrpObj

-- These are the hom-group instances used by the group-valued Yoneda functor.
attribute [local instance] CategoryTheory.Hom.monoid CategoryTheory.Hom.group

universe u v

namespace AlgebraicGeometry.GeometricRepresentation

section Comap

variable {K : Type u} [CommRing K] {G N : Scheme.{u}}
  [G.Over (Spec (.of K))] [N.Over (Spec (.of K))]
  [GrpObj (G.asOver (Spec (.of K)))] [GrpObj (N.asOver (Spec (.of K)))]
  {V : Type v} [AddCommGroup V] [Module K V]

/-- Geometric representations are determined by their operators at every
point over every coefficient algebra. -/
@[ext] theorem ext {η ξ : GeometricRepresentation (K := K) G V}
    (h : ∀ (R : CommAlgCat.{u, u} K)
      (g : (Spec (.of R)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))),
      η.operator R g = ξ.operator R g) : η = ξ := by
  apply NatTrans.ext
  funext R
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  rintro ⟨g⟩
  exact (η.operator_eq_app R g).symm.trans
    ((h R g).trans (ξ.operator_eq_app R g))

/-- Precompose a geometric representation along a morphism of group schemes,
leaving its module and coefficient functor unchanged. -/
def comap (η : GeometricRepresentation (K := K) G V)
    (i : N.asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))) [IsMonHom i] :
    GeometricRepresentation (K := K) N V :=
  Functor.whiskerRight
    (Functor.whiskerLeft (algSpec (.of K)).rightOp
      ((yonedaGrp (C := Over (Spec (.of K)))).map (Grp.ofHom i)))
    GrpCat.uliftFunctor.{v, u} ≫ η

/-- A component of precomposition evaluates the given representation at the
postcomposition of the given point. -/
theorem comap_app_hom (η : GeometricRepresentation (K := K) G V)
    (i : N.asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))) [IsMonHom i]
    (R : CommAlgCat.{u, u} K)
    (n : (Spec (.of R)).asOver (Spec (.of K)) ⟶ N.asOver (Spec (.of K))) :
    ((η.comap i).app R).hom (ULift.up n) =
      (η.app R).hom (ULift.up (n ≫ i)) := rfl

/-- The operator of precomposition is the original operator at the
postcomposed point. -/
@[simp] theorem operator_comap (η : GeometricRepresentation (K := K) G V)
    (i : N.asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))) [IsMonHom i]
    (R : CommAlgCat.{u, u} K)
    (n : (Spec (.of R)).asOver (Spec (.of K)) ⟶ N.asOver (Spec (.of K))) :
    (η.comap i).operator R n = η.operator R (n ≫ i) := rfl

/-- Precomposition along the identity retains the representation. -/
@[simp] theorem comap_id (η : GeometricRepresentation (K := K) G V) :
    η.comap (𝟙 (G.asOver (Spec (.of K)))) = η := by
  apply GeometricRepresentation.ext
  intro R g
  simp only [operator_comap, Category.comp_id]

/-- Successive precomposition agrees with precomposition along the composite. -/
theorem comap_comp {H : Scheme.{u}} [H.Over (Spec (.of K))]
    [GrpObj (H.asOver (Spec (.of K)))]
    (η : GeometricRepresentation (K := K) G V)
    (i : N.asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K)))
    (j : H.asOver (Spec (.of K)) ⟶ N.asOver (Spec (.of K)))
    [IsMonHom i] [IsMonHom j] :
    η.comap (j ≫ i) = (η.comap i).comap j := by
  apply GeometricRepresentation.ext
  intro R g
  simp only [operator_comap, Category.assoc]

private theorem exists_point_mul_eq
    (i : N.asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))) [IsMonHom.Normal i]
    (S : CommAlgCat.{u, u} K)
    (g : (Spec (.of S)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K)))
    (n : (Spec (.of S)).asOver (Spec (.of K)) ⟶ N.asOver (Spec (.of K))) :
    ∃ n' : (Spec (.of S)).asOver (Spec (.of K)) ⟶ N.asOver (Spec (.of K)),
      (n ≫ i) * g = g * (n' ≫ i) := by
  have hnormal :
      (IsMonHom.monoidHom i ((Spec (.of S)).asOver (Spec (.of K)))).range.Normal :=
    (IsMonHom.normal_iff_normal_monoidHom (φ := i)).mp inferInstance _
  have hn : n ≫ i ∈
      (IsMonHom.monoidHom i ((Spec (.of S)).asOver (Spec (.of K)))).range :=
    MonoidHom.mem_range.mpr ⟨n, rfl⟩
  obtain ⟨n', hn'⟩ := MonoidHom.mem_range.mp (hnormal.conj_mem' (n ≫ i) hn g)
  change n' ≫ i = g⁻¹ * (n ≫ i) * g at hn'
  refine ⟨n', ?_⟩
  rw [hn']
  simp only [← mul_assoc, mul_inv_cancel, one_mul]

private theorem operator_mul_apply (η : GeometricRepresentation (K := K) G V)
    (R : CommAlgCat.{u, u} K)
    (g h : (Spec (.of R)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K)))
    (w : R ⊗[K] V) :
    (η.operator R (g * h)).val w =
      (η.operator R g).val ((η.operator R h).val w) := by
  rw [η.operator_mul]
  rfl

end Comap

section Affine

variable {K : Type u} [CommRing K] {G N : Scheme.{u}}
  [G.Over (Spec (.of K))] [N.Over (Spec (.of K))]
  [GrpObj (G.asOver (Spec (.of K)))] [GrpObj (N.asOver (Spec (.of K)))]
  [IsAffine G] [IsAffine N]
  {V : Type v} [AddCommGroup V] [Module K V]

/-- Precomposition along an affine group-scheme morphism changes the coacting
coalgebra by its canonical pullback on global sections, on the same module. -/
theorem rightComoduleEquiv_comap
    (ρ : GeometricRepresentation (K := K) G V)
    (i : N.asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))) [IsMonHom i] :
    rightComoduleEquiv (G := N) (V := V) (ρ.comap i) =
      (rightComoduleEquiv (G := G) (V := V) ρ).mapCoalgebra
        (((hopfSpec.fullyFaithful (R := .of K)).preimage
          ((affineGroupIsoSpec (K := K) N).inv ≫ Grp.ofHom i ≫
            (affineGroupIsoSpec (K := K) G).hom)).unop.hom.toCoalgHom) := by
  let κ : Γ(G, ⊤) →ₐc[K] Γ(N, ⊤) :=
    ((hopfSpec.fullyFaithful (R := .of K)).preimage
      ((affineGroupIsoSpec (K := K) N).inv ≫ Grp.ofHom i ≫
        (affineGroupIsoSpec (K := K) G).hom)).unop.hom
  let X : Coalgebra.RightComodule K Γ(G, ⊤) V :=
    rightComoduleEquiv (G := G) (V := V) ρ
  have hκ : CommRingCat.ofHom κ.toAlgHom.toRingHom = i.left.appTop :=
    affineCoordinateMap_toRingHom i
  apply (rightComoduleEquiv (G := N) (V := V)).symm.injective
  rw [Equiv.symm_apply_apply]
  apply GeometricRepresentation.ext
  intro R n
  have hpoint : affinePointMulEquiv G R (n ≫ i) =
      WithConv.toConv ((affinePointMulEquiv N R n).ofConv.comp κ.toAlgHom) := by
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro a
    have hring : CommRingCat.ofHom
        (affinePointMulEquiv G R (n ≫ i)).ofConv.toRingHom =
        CommRingCat.ofHom
          ((affinePointMulEquiv N R n).ofConv.comp κ.toAlgHom).toRingHom := by
      have hcomp :
          (CommRingCat.ofHom
            ((affinePointMulEquiv N R n).ofConv.comp κ.toAlgHom).toRingHom :
              Γ(G, ⊤) ⟶ CommRingCat.of R) =
            (CommRingCat.ofHom κ.toAlgHom.toRingHom : Γ(G, ⊤) ⟶ Γ(N, ⊤)) ≫
              (CommRingCat.ofHom (affinePointMulEquiv N R n).ofConv.toRingHom :
                Γ(N, ⊤) ⟶ CommRingCat.of R) := rfl
      have hpointRing :
          (CommRingCat.ofHom (affinePointMulEquiv G R (n ≫ i)).ofConv.toRingHom :
            Γ(G, ⊤) ⟶ CommRingCat.of R) =
          ((n ≫ i).left.appTop ≫ (Scheme.ΓSpecIso (.of R)).hom :
            Γ(G, ⊤) ⟶ CommRingCat.of R) :=
        affinePointMulEquiv_toRingHom G R (n ≫ i)
      have hpullback :
          ((n ≫ i).left.appTop ≫ (Scheme.ΓSpecIso (.of R)).hom :
            Γ(G, ⊤) ⟶ CommRingCat.of R) =
          (((i.left.appTop : Γ(G, ⊤) ⟶ Γ(N, ⊤)) ≫
            (n.left.appTop : Γ(N, ⊤) ⟶ Γ(Spec (.of R), ⊤))) ≫
              (Scheme.ΓSpecIso (.of R)).hom : Γ(G, ⊤) ⟶ CommRingCat.of R) := by
        have hbare :
            ((n ≫ i).left.appTop : Γ(G, ⊤) ⟶ Γ(Spec (.of R), ⊤)) =
              i.left.appTop ≫ n.left.appTop :=
          Eq.trans
            (congrArg (fun f : Spec (.of R) ⟶ G ↦ f.appTop)
              (Over.comp_left _ _ _ n i))
            (Scheme.Hom.comp_appTop n.left i.left)
        exact congrArg
          (fun f : Γ(G, ⊤) ⟶ Γ(Spec (.of R), ⊤) ↦
            (f ≫ (Scheme.ΓSpecIso (.of R)).hom :
              Γ(G, ⊤) ⟶ CommRingCat.of R)) hbare
      have hassoc :
          (((i.left.appTop : Γ(G, ⊤) ⟶ Γ(N, ⊤)) ≫
            (n.left.appTop : Γ(N, ⊤) ⟶ Γ(Spec (.of R), ⊤))) ≫
              (Scheme.ΓSpecIso (.of R)).hom : Γ(G, ⊤) ⟶ CommRingCat.of R) =
          ((i.left.appTop : Γ(G, ⊤) ⟶ Γ(N, ⊤)) ≫
            (n.left.appTop ≫ (Scheme.ΓSpecIso (.of R)).hom :
              Γ(N, ⊤) ⟶ CommRingCat.of R) : Γ(G, ⊤) ⟶ CommRingCat.of R) :=
        Category.assoc _ _ _
      have hcoordinates :
          ((i.left.appTop : Γ(G, ⊤) ⟶ Γ(N, ⊤)) ≫
            (n.left.appTop ≫ (Scheme.ΓSpecIso (.of R)).hom :
              Γ(N, ⊤) ⟶ CommRingCat.of R) : Γ(G, ⊤) ⟶ CommRingCat.of R) =
          ((CommRingCat.ofHom κ.toAlgHom.toRingHom : Γ(G, ⊤) ⟶ Γ(N, ⊤)) ≫
            (CommRingCat.ofHom (affinePointMulEquiv N R n).ofConv.toRingHom :
              Γ(N, ⊤) ⟶ CommRingCat.of R) : Γ(G, ⊤) ⟶ CommRingCat.of R) :=
        congrArg₂
          (fun (f : Γ(G, ⊤) ⟶ Γ(N, ⊤)) (g : Γ(N, ⊤) ⟶ CommRingCat.of R) ↦
            (f ≫ g : Γ(G, ⊤) ⟶ CommRingCat.of R))
          hκ.symm (affinePointMulEquiv_toRingHom N R n).symm
      exact Eq.trans hpointRing
        (Eq.trans hpullback (Eq.trans hassoc (Eq.trans hcoordinates hcomp.symm)))
    exact congrArg (fun f : Γ(G, ⊤) ⟶ CommRingCat.of R ↦ f a) hring
  have hG : ρ.operator R (n ≫ i) =
      (X.pointAction (affinePointMulEquiv G R (n ≫ i)) :
        LinearMap.GeneralLinearGroup R (R ⊗[K] V)) := by
    simpa only [X, Equiv.symm_apply_apply] using
      (((rightComoduleEquiv (G := G) (V := V)).symm X).operator_eq_app
        R (n ≫ i)).trans (rightComoduleEquiv_symm_app X R (n ≫ i))
  have hN : ((rightComoduleEquiv (G := N) (V := V)).symm
      (X.mapCoalgebra κ.toCoalgHom)).operator R n =
      ((X.mapCoalgebra κ.toCoalgHom).pointAction (affinePointMulEquiv N R n) :
        LinearMap.GeneralLinearGroup R (R ⊗[K] V)) :=
    (((rightComoduleEquiv (G := N) (V := V)).symm
      (X.mapCoalgebra κ.toCoalgHom)).operator_eq_app R n).trans
        (rightComoduleEquiv_symm_app (X.mapCoalgebra κ.toCoalgHom) R n)
  exact (operator_comap ρ i R n).trans
    (hG.trans ((congrArg X.pointAction hpoint).trans
      ((Coalgebra.RightComodule.pointAction_mapCoalgebra X κ
        (affinePointMulEquiv N R n)).symm.trans hN.symm)))

end Affine

section Field

variable {K : Type u} [Field K] {G N : Scheme.{u}}
  [G.Over (Spec (.of K))] [N.Over (Spec (.of K))]
  [GrpObj (G.asOver (Spec (.of K)))] [GrpObj (N.asOver (Spec (.of K)))]
  {V : Type v} [AddCommGroup V] [Module K V]

/-- For a normal subgroup, every ambient point preserves the image of the
scalar-extended invariant inclusion. Fixedness is tested after every further
coefficient algebra, not only at points over the given coefficient algebra. -/
theorem operator_mem_range_baseChange_comap_invariants
    (η : GeometricRepresentation (K := K) G V)
    (i : N.asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K))) [IsMonHom.Normal i]
    (R : CommAlgCat.{u, u} K)
    (g : (Spec (.of R)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K)))
    {w : R ⊗[K] V}
    (hw : w ∈ LinearMap.range ((η.comap i).invariants.subtype.baseChange R)) :
    (η.operator R g).val w ∈
      LinearMap.range ((η.comap i).invariants.subtype.baseChange R) := by
  apply ((η.comap i).mem_range_baseChange_invariants_iff R _).2
  intro S φ n
  rw [operator_comap]
  let gS : (Spec (.of S)).asOver (Spec (.of K)) ⟶ G.asOver (Spec (.of K)) :=
    ((affineGeometricPointFunctor (K := K) G).map (CommAlgCat.ofHom φ)).hom g
  let σ := TensorProduct.map φ.toLinearMap (LinearMap.id : V →ₗ[K] V)
  have hfix (n' : (Spec (.of S)).asOver (Spec (.of K)) ⟶ N.asOver (Spec (.of K))) :
      (η.operator S (n' ≫ i)).val (σ w) = σ w := by
    simpa only [operator_comap] using
      (η.comap i).apply_map_of_mem_range_baseChange_invariants R S φ n' hw
  have hnat (z : R ⊗[K] V) :
      (η.operator S gS).val (σ z) = σ ((η.operator R g).val z) :=
    η.naturality_apply φ g z
  obtain ⟨n', hn'⟩ := exists_point_mul_eq i S gS n
  calc
    (η.operator S (n ≫ i)).val (σ ((η.operator R g).val w)) =
        (η.operator S (n ≫ i)).val ((η.operator S gS).val (σ w)) :=
      congrArg (η.operator S (n ≫ i)).val (hnat w).symm
    _ = (η.operator S ((n ≫ i) * gS)).val (σ w) :=
      (operator_mul_apply η S (n ≫ i) gS (σ w)).symm
    _ = (η.operator S (gS * (n' ≫ i))).val (σ w) :=
      congrArg (fun a => (η.operator S a).val (σ w)) hn'
    _ = (η.operator S gS).val ((η.operator S (n' ≫ i)).val (σ w)) :=
      operator_mul_apply η S gS (n' ≫ i) (σ w)
    _ = (η.operator S gS).val (σ w) := congrArg (η.operator S gS).val (hfix n')
    _ = σ ((η.operator R g).val w) := hnat w

end Field

end AlgebraicGeometry.GeometricRepresentation
