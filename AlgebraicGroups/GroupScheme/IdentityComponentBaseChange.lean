/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.IdentityComponent
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import SchemeProperties.ComponentFibers

@[expose] public section

/-!
# The identity component as a component-scheme fibre

For a group scheme locally of finite type and quasi-compact over a field, the
identity component is the fibre of the component morphism over the component
selected by the unit section.
-/

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open TopologicalSpace

namespace AlgebraicGeometry

universe u

noncomputable section

/-- The identity component is the pullback of the component morphism along the
component selected by the unit section. -/
theorem isPullback_identityComponentι_toComponentScheme
    {K : Type u} [Field K]
    (G : Over (Spec (.of K))) [GrpObj G]
    [LocallyConnectedSpace G.left]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] :
    IsPullback
      (Scheme.identityComponentι G)
      (toUnit (Scheme.identityComponentOver G))
      (toComponentScheme G)
      (η[G] ≫ toComponentScheme G) := by
  let H := Scheme.identityComponentOver G
  let C := componentScheme G
  let f := (toComponentScheme G).left
  let i := (Scheme.identityComponentι G).left
  let q := (η[G] ≫ toComponentScheme G).left
  have hq : q ≫ C.hom = 𝟙 _ := by
    simpa [q, C] using (η[G] ≫ toComponentScheme G).w
  let A := componentSubalgebra G
  let _ : Module.Finite K A := (componentSubalgebra_isFiniteEtale G).1
  let _ : Algebra.Etale K A := (componentSubalgebra_isFiniteEtale G).2
  have hCEtale : Etale C.hom := by
    change Etale (Spec.map (CommRingCat.ofHom (algebraMap K A)))
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr inferInstance
  let _ : Etale C.hom := hCEtale
  have hcompEtale : Etale (q ≫ C.hom) := by
    rw [hq]
    infer_instance
  let _ : Etale (q ≫ C.hom) := hcompEtale
  have hqEtale : Etale q := Etale.of_comp q C.hom
  let _ : Etale q := hqEtale
  have hqMono : Mono q := mono_of_mono_fac hq
  let _ : Mono q := hqMono
  have hqOpen : IsOpenImmersion q := IsOpenImmersion.of_flat_of_mono q
  let _ : IsOpenImmersion q := hqOpen
  let s₀ : Spec (.of K) := Classical.choice inferInstance
  let x : C.left := q s₀
  let y : G.left := η[G].left s₀
  have hy : f y = x := by
    rfl
  have hfiber : Set.range (f.fiberι x) = connectedComponent y := by
    exact range_fiberι_toComponentScheme_eq_connectedComponent G x y hy
  have hrange : Set.range (i ≫ f) ⊆ Set.range q := by
    rintro _ ⟨z, rfl⟩
    refine ⟨s₀, ?_⟩
    change x = f (i z)
    have hzconn : i z ∈ connectedComponent y := by
      exact (Scheme.mem_identityComponent_iff G (i z) s₀).mp z.property
    have hzfiber : i z ∈ Set.range (f.fiberι x) := by
      rwa [hfiber]
    rw [f.range_fiberι] at hzfiber
    exact hzfiber.symm
  have hcomm : i ≫ f = H.hom ≫ q := by
    let l := IsOpenImmersion.lift q (i ≫ f) hrange
    have hl : l ≫ q = i ≫ f := IsOpenImmersion.lift_fac q (i ≫ f) hrange
    have hlH : l = H.hom := by
      rw [← Category.comp_id l, ← hq, ← Category.assoc, hl]
      change i ≫ (f ≫ C.hom) = H.hom
      rw [show f ≫ C.hom = G.hom from (toComponentScheme G).w]
      exact (Scheme.identityComponentι G).w
    rw [← hlH, hl]
  have hopen : f ⁻¹ᵁ q.opensRange = i.opensRange := by
    apply Opens.ext
    ext z
    change f z ∈ Set.range q ↔ z ∈ Set.range i
    constructor
    · rintro ⟨s, hs⟩
      have hss₀ : s = s₀ := by
        change (show Spec (.of K) from s) = s₀
        exact Subsingleton.elim _ _
      have hsx : q s = x := congrArg q hss₀
      have hzx : f z = x := hs.symm.trans hsx
      have hzfiber : z ∈ Set.range (f.fiberι x) := by
        rw [f.range_fiberι]
        exact hzx
      have hzconn : z ∈ connectedComponent y := by
        rwa [hfiber] at hzfiber
      refine ⟨⟨z, ?_⟩, rfl⟩
      exact (Scheme.mem_identityComponent_iff G z s₀).mpr hzconn
    · rintro ⟨z, rfl⟩
      exact hrange ⟨z, rfl⟩
  have hpull : IsPullback H.hom i q f :=
    IsOpenImmersion.isPullback H.hom i q f hcomm hopen
  have hpull' : IsPullback i H.hom f q := hpull.flip
  change IsPullback
    (Scheme.identityComponentι G).left
    (toUnit (Scheme.identityComponentOver G)).left
    (toComponentScheme G).left
    (η[G] ≫ toComponentScheme G).left at hpull'
  exact IsPullback.of_map_of_faithful
    (F := Over.forget (Spec (.of K))) hpull'

end

end AlgebraicGeometry

#lint- only unusedArguments docBlame
