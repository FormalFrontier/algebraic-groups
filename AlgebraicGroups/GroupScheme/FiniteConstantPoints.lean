/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.FiniteConstant
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.LocallyConstant.Algebra

/-!
# Points of finite constant group schemes

This file identifies points of a finite constant group scheme over an arbitrary
commutative algebra with locally constant functions from its prime spectrum to
the indexing finite group.  No reducedness or nontriviality assumption is
needed; in particular the result includes the zero ring.

## Main results

* `AlgebraicGeometry.FiniteGroupFunctions.locallyConstantMulEquivAlgHom`
  identifies locally constant labels with coordinate algebra maps, equipped
  with convolution.
* `AlgebraicGeometry.finiteConstantLocallyConstantMulEquivPoints` identifies
  locally constant labels with scheme-valued points.
* `AlgebraicGeometry.finiteConstantLocallyConstantMulEquivPoints_naturality`
  gives the base-algebra naturality square explicitly.
* `AlgebraicGeometry.finiteConstantMulEquivPointsOfTrivialIdempotents`
  specializes to one group element when the target ring is nontrivial and has
  no nontrivial idempotents.
-/

@[expose] public section

open CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct

namespace AlgebraicGeometry

universe u v

namespace FiniteGroupFunctions

variable {K : Type u} {Γ : Type v} {R S : Type*}
variable [CommRing K] [Fintype Γ]

namespace Points

/-- Implementation type for finite clopen/idempotent partitions. -/
abbrev IdempotentPartitions (Γ R : Type*) [Fintype Γ] [CommRing R] :=
  {e : Γ → R // CompleteOrthogonalIdempotents e}

/-- The characteristic function of the singleton `g`, as an element of the finite
function algebra on `Γ`. -/
noncomputable def delta (g : Γ) : FiniteGroupFunctions K Γ := by
  classical
  exact Pi.single g 1

/-- The complete orthogonal family obtained by evaluating an algebra homomorphism
on the singleton characteristic functions. -/
noncomputable def idempotentsOfAlgHom [CommRing R] [Algebra K R]
    (φ : FiniteGroupFunctions K Γ →ₐ[K] R) : Γ → R :=
  fun g ↦ φ (delta g)

theorem idempotentsOfAlgHom_complete [CommRing R] [Algebra K R]
    (φ : FiniteGroupFunctions K Γ →ₐ[K] R) :
    CompleteOrthogonalIdempotents (idempotentsOfAlgHom φ) := by
  classical
  unfold idempotentsOfAlgHom
  change CompleteOrthogonalIdempotents
    (φ.toRingHom ∘ fun g : Γ ↦ Pi.single g 1)
  exact (CompleteOrthogonalIdempotents.single (fun _ : Γ ↦ K)).map φ.toRingHom

/-- The algebra homomorphism associated to a complete orthogonal family of
idempotents, sending `f` to `∑ g, algebraMap K R (f g) * e g`. -/
noncomputable def algHomOfIdempotents [CommRing R] [Algebra K R]
    (e : Γ → R) (he : CompleteOrthogonalIdempotents e) :
    FiniteGroupFunctions K Γ →ₐ[K] R where
  toFun f := ∑ g, algebraMap K R (f g) * e g
  map_zero' := by
    change (∑ g, algebraMap K R (0 : K) * e g) = 0
    simp
  map_one' := by
    change (∑ g, algebraMap K R (1 : K) * e g) = 1
    simpa using he.complete
  map_add' f h := by
    change (∑ g, algebraMap K R (f g + h g) * e g) =
      (∑ g, algebraMap K R (f g) * e g) + ∑ g, algebraMap K R (h g) * e g
    simp only [map_add, add_mul, Finset.sum_add_distrib]
  map_mul' f h := by
    classical
    change (∑ g, algebraMap K R (f g * h g) * e g) =
      (∑ g, algebraMap K R (f g) * e g) * ∑ g, algebraMap K R (h g) * e g
    simp only [map_mul]
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g _
    rw [Finset.sum_eq_single g]
    · calc
        _ = algebraMap K R (f g) * algebraMap K R (h g) * (e g * e g) := by
          rw [(he.idem g).eq]
        _ = _ := by ring
    · intro j _ hne
      calc
        _ = (algebraMap K R (f g) * algebraMap K R (h j)) * (e g * e j) := by ring
        _ = 0 := by rw [he.ortho (Ne.symm hne), mul_zero]
    · simp
  commutes' r := by
    change (∑ g, algebraMap K R r * e g) = algebraMap K R r
    rw [← Finset.mul_sum]
    simp [he.complete]

@[simp]
theorem algHomOfIdempotents_single [CommRing R] [Algebra K R]
    (e : Γ → R) (he : CompleteOrthogonalIdempotents e) (g : Γ) :
    algHomOfIdempotents (K := K) e he (delta g) = e g := by
  classical
  change (∑ h, algebraMap K R ((Pi.single g 1 : Γ → K) h) * e h) = e g
  rw [Finset.sum_eq_single g]
  · simp
  · intro h _ hne
    simp [hne]
  · simp

/-- Algebra homomorphisms out of a finite function algebra are equivalent to
complete orthogonal idempotent partitions indexed by the function domain. -/
noncomputable def algHomEquivIdempotentPartitions [CommRing R] [Algebra K R] :
    (FiniteGroupFunctions K Γ →ₐ[K] R) ≃ IdempotentPartitions Γ R where
  toFun φ := ⟨idempotentsOfAlgHom φ, idempotentsOfAlgHom_complete φ⟩
  invFun e := algHomOfIdempotents e.1 e.2
  left_inv φ := by
    apply AlgHom.toLinearMap_injective
    apply (basis K Γ).ext
    intro g
    change algHomOfIdempotents (K := K) (idempotentsOfAlgHom φ)
      (idempotentsOfAlgHom_complete φ) (delta g) = φ (delta g)
    simp [idempotentsOfAlgHom]
  right_inv e := by
    ext g
    simp [idempotentsOfAlgHom]

/-- The clopen fibre of a locally constant function over a value `g`. -/
def fiberClopen [TopologicalSpace S] (f : LocallyConstant S Γ) (g : Γ) :
    TopologicalSpace.Clopens S :=
  ⟨{x | f x = g}, f.isLocallyConstant.isClopen_fiber g⟩

/-- The idempotent whose basic open in `PrimeSpectrum R` is the fibre of a locally
constant function over `g`. -/
noncomputable def idempotentOfLocallyConstant [CommRing R]
    (f : LocallyConstant (PrimeSpectrum R) Γ) (g : Γ) : R :=
  (PrimeSpectrum.isIdempotentElemEquivClopens.symm (fiberClopen f g)).1

omit [Fintype Γ] in
theorem idempotentOfLocallyConstant_isIdempotent [CommRing R]
    (f : LocallyConstant (PrimeSpectrum R) Γ) (g : Γ) :
    IsIdempotentElem (idempotentOfLocallyConstant f g) :=
  (PrimeSpectrum.isIdempotentElemEquivClopens.symm (fiberClopen f g)).2

omit [Fintype Γ] in
theorem mem_basicOpen_idempotentOfLocallyConstant_iff [CommRing R]
    (f : LocallyConstant (PrimeSpectrum R) Γ) (g : Γ) (p : PrimeSpectrum R) :
    p ∈ PrimeSpectrum.basicOpen (idempotentOfLocallyConstant f g) ↔ f p = g := by
  let E := PrimeSpectrum.isIdempotentElemEquivClopens (R := R)
  change p ∈ (PrimeSpectrum.basicOpen
    (E.symm (fiberClopen f g)).1 : Set (PrimeSpectrum R)) ↔ f p = g
  rw [← PrimeSpectrum.coe_isIdempotentElemEquivClopens_apply]
  rw [E.apply_symm_apply]
  rfl

theorem idempotentOfLocallyConstant_complete [CommRing R]
    (f : LocallyConstant (PrimeSpectrum R) Γ) :
    CompleteOrthogonalIdempotents (idempotentOfLocallyConstant f) := by
  classical
  let e : Γ → R := idempotentOfLocallyConstant f
  have heidem (g : Γ) : IsIdempotentElem (e g) :=
    idempotentOfLocallyConstant_isIdempotent f g
  have heortho : Pairwise (e · * e · = 0) := by
    intro g h hne
    let E := PrimeSpectrum.isIdempotentElemEquivClopens (R := R)
    have hcl : E ⟨e g * e h, (heidem g).mul (heidem h)⟩ = E ⟨0, .zero⟩ := by
      change PrimeSpectrum.isIdempotentElemEquivClopens
        ⟨e g * e h, (heidem g).mul (heidem h)⟩ = E ⟨0, .zero⟩
      have hmul := PrimeSpectrum.isIdempotentElemEquivClopens_mul
        (R := R) ⟨e g, heidem g⟩ ⟨e h, heidem h⟩
      rw [hmul]
      change E (E.symm (fiberClopen f g)) ⊓ E (E.symm (fiberClopen f h)) = E ⟨0, .zero⟩
      rw [E.apply_symm_apply, E.apply_symm_apply]
      have hzero : E ⟨(0 : R), .zero⟩ = ⊥ := by
        rw [← E.apply_symm_apply (⊥ : TopologicalSpace.Clopens (PrimeSpectrum R))]
        congr 1
        exact PrimeSpectrum.isIdempotentElemEquivClopens_symm_bot.symm
      rw [hzero]
      ext p
      change (f p = g ∧ f p = h) ↔ False
      exact ⟨fun hp ↦ hne (hp.1.symm.trans hp.2), False.elim⟩
    exact congrArg Subtype.val (E.injective hcl)
  refine ⟨⟨heidem, heortho⟩, ?_⟩
  let s : R := ∑ g, e g
  have hsidem : IsIdempotentElem s :=
    (show OrthogonalIdempotents e from ⟨heidem, heortho⟩).isIdempotentElem_sum
  let E := PrimeSpectrum.isIdempotentElemEquivClopens (R := R)
  have htop : E ⟨s, hsidem⟩ = ⊤ := by
    apply TopologicalSpace.Clopens.ext
    ext p
    change p ∈ PrimeSpectrum.basicOpen s ↔ p ∈ (Set.univ : Set (PrimeSpectrum R))
    simp only [Set.mem_univ, iff_true]
    rw [PrimeSpectrum.mem_basicOpen]
    intro hs
    let g := f p
    have hnot : e g ∉ p.asIdeal := by
      rw [← PrimeSpectrum.mem_basicOpen]
      exact (mem_basicOpen_idempotentOfLocallyConstant_iff f g p).2 rfl
    have hmem : e g ∈ p.asIdeal := by
      have hm : e g * s ∈ p.asIdeal := p.asIdeal.mul_mem_left (e g) hs
      rw [(show OrthogonalIdempotents e from ⟨heidem, heortho⟩).mul_sum_of_mem
        (Finset.mem_univ g)] at hm
      exact hm
    exact hnot hmem
  have hone : E ⟨(1 : R), .one⟩ = ⊤ := E.map_top
  exact congrArg Subtype.val (E.injective (htop.trans hone.symm))

theorem existsUnique_mem_basicOpen [CommRing R]
    (e : Γ → R) (he : CompleteOrthogonalIdempotents e) (p : PrimeSpectrum R) :
    ∃! g, p ∈ PrimeSpectrum.basicOpen (e g) := by
  classical
  have hex : ∃ g, p ∈ PrimeSpectrum.basicOpen (e g) := by
    by_contra h
    push Not at h
    have hall (g : Γ) : e g ∈ p.asIdeal := by
      simpa only [PrimeSpectrum.mem_basicOpen, not_not] using h g
    have hsum : (∑ g, e g) ∈ p.asIdeal := p.asIdeal.sum_mem fun g _ ↦ hall g
    rw [he.complete] at hsum
    exact p.2.ne_top ((Ideal.eq_top_iff_one p.asIdeal).2 hsum)
  obtain ⟨g, hg⟩ := hex
  refine ⟨g, hg, fun h hh ↦ ?_⟩
  by_contra hne
  have hprod : e g * e h ∈ p.asIdeal := by
    rw [he.ortho (Ne.symm hne)]
    exact p.asIdeal.zero_mem
  rcases p.2.mem_or_mem hprod with hmem | hmem
  · exact (PrimeSpectrum.mem_basicOpen _ _).mp hg hmem
  · exact (PrimeSpectrum.mem_basicOpen _ _).mp hh hmem

/-- The locally constant function that labels each prime by the unique member of a
complete orthogonal idempotent family whose basic open contains that prime. -/
noncomputable def locallyConstantOfIdempotents [CommRing R]
    (e : Γ → R) (he : CompleteOrthogonalIdempotents e) :
    LocallyConstant (PrimeSpectrum R) Γ where
  toFun p := Classical.choose (existsUnique_mem_basicOpen e he p)
  isLocallyConstant := IsLocallyConstant.iff_isOpen_fiber.2 fun g ↦ by
    have hset :
        {p : PrimeSpectrum R | Classical.choose (existsUnique_mem_basicOpen e he p) = g} =
          (PrimeSpectrum.basicOpen (e g) : Set (PrimeSpectrum R)) := by
      ext p
      let h := Classical.choose_spec (existsUnique_mem_basicOpen e he p)
      constructor
      · intro hp
        subst hp
        exact h.1
      · intro hp
        exact (h.2 g hp).symm
    change IsOpen {p | Classical.choose (existsUnique_mem_basicOpen e he p) = g}
    rw [hset]
    exact (PrimeSpectrum.basicOpen (e g)).2

theorem locallyConstantOfIdempotents_apply_eq_iff [CommRing R]
    (e : Γ → R) (he : CompleteOrthogonalIdempotents e)
    (p : PrimeSpectrum R) (g : Γ) :
    locallyConstantOfIdempotents e he p = g ↔
      p ∈ PrimeSpectrum.basicOpen (e g) := by
  let h := Classical.choose_spec (existsUnique_mem_basicOpen e he p)
  exact ⟨fun hp ↦ hp ▸ h.1, fun hp ↦ (h.2 g hp).symm⟩

/-- Locally constant functions on a prime spectrum are equivalent to complete
orthogonal idempotent partitions indexed by their codomain. -/
noncomputable def locallyConstantEquivIdempotentPartitions [CommRing R] :
    LocallyConstant (PrimeSpectrum R) Γ ≃ IdempotentPartitions Γ R where
  toFun f := ⟨idempotentOfLocallyConstant f, idempotentOfLocallyConstant_complete f⟩
  invFun e := locallyConstantOfIdempotents e.1 e.2
  left_inv f := by
    ext p
    apply (locallyConstantOfIdempotents_apply_eq_iff _ _ p (f p)).2
    exact (mem_basicOpen_idempotentOfLocallyConstant_iff f (f p) p).2 rfl
  right_inv e := by
    ext g
    let E := PrimeSpectrum.isIdempotentElemEquivClopens (R := R)
    let lhs : {x : R // IsIdempotentElem x} :=
      E.symm (fiberClopen (locallyConstantOfIdempotents e.1 e.2) g)
    have hsub : lhs = ⟨e.1 g, e.2.idem g⟩ := by
      apply E.injective
      rw [E.apply_symm_apply]
      apply TopologicalSpace.Clopens.ext
      ext p
      simp only [fiberClopen]
      exact locallyConstantOfIdempotents_apply_eq_iff e.1 e.2 p g
    exact congrArg Subtype.val hsub

/-- Locally constant functions on `PrimeSpectrum R` with finite codomain `Γ` are
equivalent to `K`-algebra homomorphisms from the finite function algebra on `Γ`. -/
noncomputable def locallyConstantEquivAlgHom [CommRing R] [Algebra K R] :
    LocallyConstant (PrimeSpectrum R) Γ ≃
      (FiniteGroupFunctions K Γ →ₐ[K] R) :=
  locallyConstantEquivIdempotentPartitions.trans algHomEquivIdempotentPartitions.symm

theorem locallyConstantEquivAlgHom_symm_apply_eq_iff [CommRing R] [Algebra K R]
    (φ : FiniteGroupFunctions K Γ →ₐ[K] R) (p : PrimeSpectrum R) (g : Γ) :
    locallyConstantEquivAlgHom.symm φ p = g ↔
      φ (delta g) ∉ p.asIdeal := by
  change locallyConstantOfIdempotents (idempotentsOfAlgHom φ)
      (idempotentsOfAlgHom_complete φ) p = g ↔ _
  rw [locallyConstantOfIdempotents_apply_eq_iff, PrimeSpectrum.mem_basicOpen]
  rfl

variable [Group Γ]

omit [Group Γ] in
theorem quotient_comp_algHom_eq_eval [CommRing R] [Algebra K R]
    (φ : FiniteGroupFunctions K Γ →ₐ[K] R) (p : PrimeSpectrum R) :
    (Ideal.Quotient.mkₐ K p.asIdeal).comp φ =
      (Algebra.ofId K (R ⧸ p.asIdeal)).comp
        (evalAlgHom K Γ (locallyConstantEquivAlgHom.symm φ p)) := by
  classical
  let g := locallyConstantEquivAlgHom.symm φ p
  apply AlgHom.toLinearMap_injective
  apply (basis K Γ).ext
  intro h
  change (Ideal.Quotient.mkₐ K p.asIdeal) (φ (delta h)) =
    algebraMap K (R ⧸ p.asIdeal) (delta h g)
  by_cases hh : h = g
  · subst h
    have hnot : φ (delta g) ∉ p.asIdeal :=
      (locallyConstantEquivAlgHom_symm_apply_eq_iff φ p g).1 rfl
    have hi : IsIdempotentElem
        ((Ideal.Quotient.mkₐ K p.asIdeal) (φ (delta g))) :=
      ((idempotentsOfAlgHom_complete φ).idem g).map
        (Ideal.Quotient.mkₐ K p.asIdeal).toRingHom
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp hi with hzero | hone
    · exact absurd ((Ideal.Quotient.eq_zero_iff_mem).mp hzero) hnot
    · simpa [delta] using hone
  · have hmem : φ (delta h) ∈ p.asIdeal := by
      by_contra hnot
      have heq := (locallyConstantEquivAlgHom_symm_apply_eq_iff φ p h).2 hnot
      exact hh heq.symm
    rw [show (Ideal.Quotient.mkₐ K p.asIdeal) (φ (delta h)) = 0 from
      Ideal.Quotient.eq_zero_iff_mem.mpr hmem]
    simp [delta, hh]

theorem evalAlgHom_convMul (g h : Γ) :
    (WithConv.toConv (evalAlgHom K Γ g) *
      WithConv.toConv (evalAlgHom K Γ h)).ofConv =
        evalAlgHom K Γ (g * h) := by
  ext f
  rw [AlgHom.convMul_apply]
  exact DFunLike.congr_fun (evalAlgHom_comp_comulAlgHom K Γ g h) f

theorem locallyConstantEquivAlgHom_symm_mul [CommRing R] [Algebra K R]
    (φ ψ : WithConv (FiniteGroupFunctions K Γ →ₐ[K] R)) :
    locallyConstantEquivAlgHom.symm (φ * ψ).ofConv =
      locallyConstantEquivAlgHom.symm φ.ofConv *
        locallyConstantEquivAlgHom.symm ψ.ofConv := by
  ext p
  let g := locallyConstantEquivAlgHom.symm φ.ofConv p
  let h := locallyConstantEquivAlgHom.symm ψ.ofConv p
  let q : R →ₐ[K] R ⧸ p.asIdeal := Ideal.Quotient.mkₐ K p.asIdeal
  let b : K →ₐ[K] R ⧸ p.asIdeal := Algebra.ofId K (R ⧸ p.asIdeal)
  have hφ : q.comp φ.ofConv = b.comp (evalAlgHom K Γ g) :=
    quotient_comp_algHom_eq_eval φ.ofConv p
  have hψ : q.comp ψ.ofConv = b.comp (evalAlgHom K Γ h) :=
    quotient_comp_algHom_eq_eval ψ.ofConv p
  have hconv : q.comp (φ * ψ).ofConv = b.comp (evalAlgHom K Γ (g * h)) := by
    calc
      q.comp (φ * ψ).ofConv =
          (WithConv.toConv (q.comp φ.ofConv) *
            WithConv.toConv (q.comp ψ.ofConv)).ofConv :=
        AlgHom.comp_convMul_distrib q φ ψ
      _ = (WithConv.toConv (b.comp (evalAlgHom K Γ g)) *
            WithConv.toConv (b.comp (evalAlgHom K Γ h))).ofConv := by rw [hφ, hψ]
      _ = b.comp
          (WithConv.toConv (evalAlgHom K Γ g) *
            WithConv.toConv (evalAlgHom K Γ h)).ofConv :=
        (AlgHom.comp_convMul_distrib b _ _).symm
      _ = b.comp (evalAlgHom K Γ (g * h)) := by rw [evalAlgHom_convMul]
  apply (locallyConstantEquivAlgHom_symm_apply_eq_iff (φ * ψ).ofConv p (g * h)).2
  intro hmem
  have hzero : q ((φ * ψ).ofConv (delta (g * h))) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  have hone : q ((φ * ψ).ofConv (delta (g * h))) = 1 := by
    change q.comp (φ * ψ).ofConv (delta (g * h)) = 1
    rw [hconv]
    change b (evalAlgHom K Γ (g * h) (delta (g * h))) = 1
    have hd : delta (K := K) (g * h) (g * h) = 1 := by
      classical
      simp [delta]
    change b (delta (K := K) (g * h) (g * h)) = 1
    rw [hd, map_one]
  exact one_ne_zero (hone.symm.trans hzero)

end Points

/-- Locally constant labels on a prime spectrum are multiplicatively equivalent
to coordinate algebra maps equipped with convolution. -/
noncomputable def locallyConstantMulEquivAlgHom (K : Type u) (Γ : Type v) (R : Type*)
    [CommRing K] [CommRing R] [Algebra K R] [Fintype Γ] [Group Γ] :
    LocallyConstant (PrimeSpectrum R) Γ ≃*
      WithConv (FiniteGroupFunctions K Γ →ₐ[K] R) where
  toEquiv := (Points.locallyConstantEquivAlgHom (K := K) (Γ := Γ) (R := R)).trans
    (WithConv.equiv (FiniteGroupFunctions K Γ →ₐ[K] R)).symm
  map_mul' f h := by
    apply WithConv.ofConv_injective
    apply (Points.locallyConstantEquivAlgHom (K := K) (Γ := Γ) (R := R)).symm.injective
    rw [Points.locallyConstantEquivAlgHom_symm_mul]
    simp

private theorem locallyConstantEquivAlgHom_symm_comp [CommRing R] [CommRing S]
    [Algebra K R] [Algebra K S] (a : R →ₐ[K] S)
    (φ : FiniteGroupFunctions K Γ →ₐ[K] R) :
    Points.locallyConstantEquivAlgHom.symm (a.comp φ) =
      LocallyConstant.comap
        ⟨PrimeSpectrum.comap a.toRingHom,
          PrimeSpectrum.continuous_comap a.toRingHom⟩
        (Points.locallyConstantEquivAlgHom.symm φ) := by
  ext p
  let g := Points.locallyConstantEquivAlgHom.symm φ (PrimeSpectrum.comap a.toRingHom p)
  apply (Points.locallyConstantEquivAlgHom_symm_apply_eq_iff (a.comp φ) p g).2
  have hnot := (Points.locallyConstantEquivAlgHom_symm_apply_eq_iff φ
    (PrimeSpectrum.comap a.toRingHom p) g).1 rfl
  change a (φ (Points.delta g)) ∉ p.asIdeal
  exact hnot

/-- Coordinate-algebra naturality of
`FiniteGroupFunctions.locallyConstantMulEquivAlgHom`. -/
theorem locallyConstantMulEquivAlgHom_naturality
    (K : Type u) (Γ : Type v) {R S : Type*}
    [CommRing K] [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    [Fintype Γ] [Group Γ] (a : R →ₐ[K] S)
    (f : LocallyConstant (PrimeSpectrum R) Γ) :
    locallyConstantMulEquivAlgHom K Γ S
        (LocallyConstant.comap
          ⟨PrimeSpectrum.comap a.toRingHom,
            PrimeSpectrum.continuous_comap a.toRingHom⟩ f) =
      WithConv.toConv (a.comp
        (locallyConstantMulEquivAlgHom K Γ R f).ofConv) := by
  apply WithConv.ofConv_injective
  change Points.locallyConstantEquivAlgHom
      (LocallyConstant.comap
        ⟨PrimeSpectrum.comap a.toRingHom,
          PrimeSpectrum.continuous_comap a.toRingHom⟩ f) =
    a.comp (Points.locallyConstantEquivAlgHom f)
  apply (Points.locallyConstantEquivAlgHom (K := K) (Γ := Γ) (R := S)).symm.injective
  rw [locallyConstantEquivAlgHom_symm_comp]
  simp

/-- A constant label gives the corresponding evaluation map on the coordinate
function algebra. -/
@[simp]
theorem locallyConstantMulEquivAlgHom_const
    (K : Type u) (Γ : Type v) [CommRing K] [Fintype Γ] [Group Γ] (g : Γ) :
    (locallyConstantMulEquivAlgHom K Γ K
      (LocallyConstant.const (PrimeSpectrum K) g)).ofConv =
        evalAlgHom K Γ g := by
  apply (Points.locallyConstantEquivAlgHom
    (K := K) (Γ := Γ) (R := K)).symm.injective
  change Points.locallyConstantEquivAlgHom.symm
      (Points.locallyConstantEquivAlgHom
        (LocallyConstant.const (PrimeSpectrum K) g)) =
    Points.locallyConstantEquivAlgHom.symm (evalAlgHom K Γ g)
  rw [Equiv.symm_apply_apply]
  ext p
  symm
  apply (Points.locallyConstantEquivAlgHom_symm_apply_eq_iff
    (evalAlgHom K Γ g) p g).2
  change Points.delta (K := K) g g ∉ p.asIdeal
  have hdelta : Points.delta (K := K) g g = 1 := by
    classical
    simp [Points.delta]
  rw [hdelta]
  intro hone
  exact p.2.ne_top ((Ideal.eq_top_iff_one p.asIdeal).2 hone)

/-- If the indexing type is unique, its finite function algebra is just the
base algebra. -/
def uniqueAlgEquiv (K : Type u) (Γ : Type v) [CommRing K] [Unique Γ] :
    FiniteGroupFunctions K Γ ≃ₐ[K] K :=
  (toPiAlgEquiv K Γ).trans (AlgEquiv.funUnique K Γ K)

end FiniteGroupFunctions

variable (K Γ R : Type u)
variable [CommRing K] [CommRing R] [Algebra K R] [Fintype Γ] [Group Γ]

/-- The points of a finite constant group scheme over an arbitrary algebra are
the locally constant labels on the algebra's prime spectrum. -/
noncomputable def finiteConstantLocallyConstantMulEquivPoints :
    LocallyConstant (PrimeSpectrum R) Γ ≃*
      ((Spec (.of R)).asOver (Spec (.of K)) ⟶
        (finiteConstantGroupScheme K Γ).X) :=
  (FiniteGroupFunctions.locallyConstantMulEquivAlgHom K Γ R).trans
    (Spec.mapMulEquiv
      (R := K) (S := FiniteGroupFunctions K Γ) (T := R))

@[simp]
theorem finiteConstantLocallyConstantMulEquivPoints_apply_left
    (f : LocallyConstant (PrimeSpectrum R) Γ) :
    (finiteConstantLocallyConstantMulEquivPoints K Γ R f).left =
      Spec.map (CommRingCat.ofHom
        (FiniteGroupFunctions.locallyConstantMulEquivAlgHom K Γ R f).ofConv.toRingHom) :=
  rfl

/-- Naturality of finite-constant points under a map of base algebras. -/
theorem finiteConstantLocallyConstantMulEquivPoints_naturality
    {S : Type u} [CommRing S] [Algebra K S] (a : R →ₐ[K] S)
    (f : LocallyConstant (PrimeSpectrum R) Γ) :
    finiteConstantLocallyConstantMulEquivPoints K Γ S
        (LocallyConstant.comap
          ⟨PrimeSpectrum.comap a.toRingHom,
            PrimeSpectrum.continuous_comap a.toRingHom⟩ f) =
      (Spec.map (CommRingCat.ofHom a.toRingHom)).asOver (Spec (.of K)) ≫
        finiteConstantLocallyConstantMulEquivPoints K Γ R f := by
  apply Over.OverMorphism.ext
  rw [finiteConstantLocallyConstantMulEquivPoints_apply_left]
  change Spec.map (CommRingCat.ofHom
      (FiniteGroupFunctions.locallyConstantMulEquivAlgHom K Γ S
        (LocallyConstant.comap
          ⟨PrimeSpectrum.comap a.toRingHom,
            PrimeSpectrum.continuous_comap a.toRingHom⟩ f)).ofConv.toRingHom) =
    Spec.map (CommRingCat.ofHom a.toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (FiniteGroupFunctions.locallyConstantMulEquivAlgHom K Γ R f).ofConv.toRingHom)
  rw [← Spec.map_comp]
  congr 1
  exact congrArg (fun h : FiniteGroupFunctions K Γ →ₐ[K] S ↦
      CommRingCat.ofHom h.toRingHom)
    (congrArg WithConv.ofConv
      (FiniteGroupFunctions.locallyConstantMulEquivAlgHom_naturality K Γ a f))

/-- At the base algebra, a constant label is the already constructed labelled
rational point. -/
@[simp]
theorem finiteConstantLocallyConstantMulEquivPoints_const (g : Γ) :
    (finiteConstantLocallyConstantMulEquivPoints K Γ K
        (LocallyConstant.const (PrimeSpectrum K) g)).left =
      (finiteConstantGroupSchemePoint K Γ g).left := by
  rw [finiteConstantLocallyConstantMulEquivPoints_apply_left,
    FiniteGroupFunctions.locallyConstantMulEquivAlgHom_const]
  rfl

/-- Evaluation at any point is a multiplicative equivalence from locally
constant functions on a connected space to their target group. -/
noncomputable def locallyConstantMulEquivOfConnected
    (X Γ : Type*) [TopologicalSpace X] [ConnectedSpace X] [Group Γ] :
    LocallyConstant X Γ ≃* Γ where
  toFun f := f (Classical.choice (inferInstance : Nonempty X))
  invFun := LocallyConstant.const X
  left_inv f := by
    let x₀ : X := Classical.choice (inferInstance : Nonempty X)
    ext x
    let U : Set X := {y | f y = f x₀}
    rcases (connectedSpace_iff_clopen.mp (by infer_instance)).2 U
        (f.isLocallyConstant.isClopen_fiber (f x₀)) with hU | hU
    · have hx₀ : x₀ ∈ U := rfl
      rw [hU] at hx₀
      exact False.elim hx₀
    · have hx : x ∈ U := by rw [hU]; trivial
      exact hx.symm
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- A prime spectrum is connected exactly when the ring is nontrivial and its
only idempotents are zero and one. -/
theorem connectedSpace_primeSpectrum_iff_trivialIdempotents (R : Type*) [CommRing R] :
    ConnectedSpace (PrimeSpectrum R) ↔
      Nontrivial R ∧ ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1 := by
  constructor
  · intro hR
    let _ : ConnectedSpace (PrimeSpectrum R) := hR
    refine ⟨PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance, fun e he ↦ ?_⟩
    let E := PrimeSpectrum.isIdempotentElemEquivClopens (R := R)
    let c := E ⟨e, he⟩
    rcases (connectedSpace_iff_clopen.mp hR).2 (c : Set (PrimeSpectrum R)) c.2 with hc | hc
    · left
      have hcbot : c = ⊥ := TopologicalSpace.Clopens.ext hc
      have hzero : E ⟨(0 : R), .zero⟩ = ⊥ := by
        rw [← E.apply_symm_apply (⊥ : TopologicalSpace.Clopens (PrimeSpectrum R))]
        congr 1
        exact PrimeSpectrum.isIdempotentElemEquivClopens_symm_bot.symm
      exact congrArg Subtype.val (E.injective (hcbot.trans hzero.symm))
    · right
      have hctop : c = ⊤ := TopologicalSpace.Clopens.ext hc
      have hone : E ⟨(1 : R), .one⟩ = ⊤ := E.map_top
      exact congrArg Subtype.val (E.injective (hctop.trans hone.symm))
  · rintro ⟨hR, hidem⟩
    rw [connectedSpace_iff_clopen]
    refine ⟨PrimeSpectrum.nonempty_iff_nontrivial.mpr hR, fun s hs ↦ ?_⟩
    let c : TopologicalSpace.Clopens (PrimeSpectrum R) := ⟨s, hs⟩
    let E := PrimeSpectrum.isIdempotentElemEquivClopens (R := R)
    let e := E.symm c
    rcases hidem e.1 e.2 with he | he
    · left
      have heq : e = E.symm ⊥ := by
        rw [PrimeSpectrum.isIdempotentElemEquivClopens_symm_bot]
        exact Subtype.ext he
      have hc : c = ⊥ := (E.apply_symm_apply c).symm.trans
        ((congrArg E heq).trans (E.apply_symm_apply ⊥))
      exact congrArg (fun d : TopologicalSpace.Clopens (PrimeSpectrum R) ↦
        (d : Set (PrimeSpectrum R))) hc
    · right
      have heq : e = E.symm ⊤ := by
        rw [PrimeSpectrum.isIdempotentElemEquivClopens_symm_top]
        exact Subtype.ext he
      have hc : c = ⊤ := (E.apply_symm_apply c).symm.trans
        ((congrArg E heq).trans (E.apply_symm_apply ⊤))
      exact congrArg (fun d : TopologicalSpace.Clopens (PrimeSpectrum R) ↦
        (d : Set (PrimeSpectrum R))) hc

/-- On a connected prime spectrum, finite-constant points are simply group
elements. -/
noncomputable def finiteConstantMulEquivPointsOfConnected
    [ConnectedSpace (PrimeSpectrum R)] :
    Γ ≃* ((Spec (.of R)).asOver (Spec (.of K)) ⟶
      (finiteConstantGroupScheme K Γ).X) :=
  (locallyConstantMulEquivOfConnected (PrimeSpectrum R) Γ).symm.trans
    (finiteConstantLocallyConstantMulEquivPoints K Γ R)

/-- If a nontrivial algebra has no nontrivial idempotents, its points in a
finite constant group scheme are exactly the elements of the indexing group. -/
noncomputable def finiteConstantMulEquivPointsOfTrivialIdempotents
    [Nontrivial R]
    (h : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1) :
    Γ ≃* ((Spec (.of R)).asOver (Spec (.of K)) ⟶
      (finiteConstantGroupScheme K Γ).X) := by
  letI : ConnectedSpace (PrimeSpectrum R) :=
    (connectedSpace_primeSpectrum_iff_trivialIdempotents R).2 ⟨inferInstance, h⟩
  exact finiteConstantMulEquivPointsOfConnected K Γ R

end AlgebraicGeometry
