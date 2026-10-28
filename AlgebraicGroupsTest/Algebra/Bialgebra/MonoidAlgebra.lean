/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Ring.Defs
import AlgebraicGroups.Algebra.Bialgebra.MonoidAlgebra
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
import Mathlib.RingTheory.HopfAlgebra.GroupLike
import Mathlib.Data.Int.Cast.Lemmas

/-!
# Doubling on the infinite cyclic monoid algebra

The stock Hopf algebra `R[Multiplicative ℤ]` has a doubling endomorphism, induced
by the monoid map sending the generator `t` to `t²`. Independently, the normalized
basis point at `t²` determines a homomorphism to its group-like elements by
integer powers in the group of group-like elements.

Over `ℕ`, doubling sends the two-term element supported at weights `1` and `-1`
to one supported at weights `2` and `-2`. The coefficient at weight `1` separates
the two elements, so doubling is not the identity. This same pair of maps
illustrates extraction, extension, both inverse identities and the characteristic
laws. A subsingleton scalar semiring gives the complementary boundary case.

## References

The monoid-algebra Hopf structure and antipode are from Amelia Livingston's
`Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra`. The group of group-like elements
is due to Yaël Dillies and Michał Mrugała in
`Mathlib.RingTheory.HopfAlgebra.GroupLike`. The cyclic maps use Mathlib's
`zpowersHom` from `Mathlib.Data.Int.Cast.Lemmas`. All model structures and maps
are these existing constructions.
-/

@[expose] public section

noncomputable section

universe uR uM uA

namespace MonoidAlgebra.CyclicWeights

private def generator : Multiplicative ℤ := Multiplicative.ofAdd 1

private def doubling : Multiplicative ℤ →* Multiplicative ℤ :=
  zpowersHom (Multiplicative ℤ) (generator ^ 2)

variable (R : Type uR) [CommSemiring R]

private def doublingBialgHom : R[Multiplicative ℤ] →ₐc[R] R[Multiplicative ℤ] :=
  mapDomainBialgHom R doubling

private def squarePoint : GroupLike R R[Multiplicative ℤ] where
  val := single (generator ^ 2) 1
  isGroupLikeElem_val := isGroupLikeElem_single_one _

private def squarePointHom : Multiplicative ℤ →* GroupLike R R[Multiplicative ℤ] :=
  zpowersHom (GroupLike R R[Multiplicative ℤ]) (squarePoint R)

private def symmetricPair : R[Multiplicative ℤ] :=
  single generator 1 + single generator⁻¹ 1

private theorem doubling_generator : doubling generator = generator ^ 2 := by
  simp [doubling, generator]

private theorem doubling_inverse : doubling generator⁻¹ = (generator ^ 2)⁻¹ := by
  rw [map_inv, doubling_generator]

private theorem squarePointHom_generator : squarePointHom R generator = squarePoint R := by
  simp [squarePointHom, generator]

private theorem squarePointHom_inverse : squarePointHom R generator⁻¹ = (squarePoint R)⁻¹ := by
  rw [map_inv, squarePointHom_generator]

private theorem doublingBialgHom_generator :
    doublingBialgHom R (single generator 1) = single (generator ^ 2) 1 := by
  simp only [doublingBialgHom, mapDomainBialgHom_single, doubling_generator]

private theorem doublingBialgHom_inverse :
    doublingBialgHom R (single generator⁻¹ 1) = single (generator ^ 2)⁻¹ 1 := by
  simp only [doublingBialgHom, mapDomainBialgHom_single, doubling_inverse]

private theorem doublingBialgHom_symmetricPair :
    doublingBialgHom R (symmetricPair R) =
      single (generator ^ 2) 1 + single (generator ^ 2)⁻¹ 1 := by
  simp only [symmetricPair, map_add, doublingBialgHom_generator, doublingBialgHom_inverse]

private theorem symmetricPair_coeff_generator : (symmetricPair R).coeff generator = 1 := by
  have hinv : generator⁻¹ ≠ generator := by decide
  simp [symmetricPair, hinv]

private theorem doublingBialgHom_symmetricPair_coeff_generator :
    (doublingBialgHom R (symmetricPair R)).coeff generator = 0 := by
  rw [doublingBialgHom_symmetricPair]
  have hsq : generator ^ 2 ≠ generator := by decide
  have hinvsq : (generator ^ 2)⁻¹ ≠ generator := by decide
  simp [hsq, hinvsq]

private theorem symmetricPair_ne_doubling [Nontrivial R] :
    symmetricPair R ≠ doublingBialgHom R (symmetricPair R) := by
  intro h
  have hc := congrArg (fun y : R[Multiplicative ℤ] => y.coeff generator) h
  rw [symmetricPair_coeff_generator, doublingBialgHom_symmetricPair_coeff_generator] at hc
  exact one_ne_zero hc

private theorem doublingBialgHom_ne_id [Nontrivial R] :
    doublingBialgHom R ≠ BialgHom.id R R[Multiplicative ℤ] := by
  intro h
  have hx := DFunLike.congr_fun h (symmetricPair R)
  exact symmetricPair_ne_doubling R hx.symm

/-- Both inverse identities and the characteristic laws on the same doubling map
and independently defined group-like-valued cyclic map over the nonring `ℕ`. -/
private theorem doubling_groupLike_extension :
    groupLikeHomOfBialgHom
        ((liftGroupLikeBialgHom (R := ℕ) (A := ℕ[Multiplicative ℤ])).comp
          (mapDomainBialgHom ℕ (squarePointHom ℕ))) = squarePointHom ℕ ∧
    (liftGroupLikeBialgHom (R := ℕ) (A := ℕ[Multiplicative ℤ])).comp
        (mapDomainBialgHom ℕ (groupLikeHomOfBialgHom (doublingBialgHom ℕ))) =
      doublingBialgHom ℕ ∧
    (∀ m, ((groupLikeHomOfBialgHom (doublingBialgHom ℕ)) m).val =
      doublingBialgHom ℕ (single m 1)) ∧
    (GroupLike.valMonoidHom ℕ ℕ[Multiplicative ℤ]).comp
        (groupLikeHomOfBialgHom (doublingBialgHom ℕ)) =
      (lift ℕ ℕ[Multiplicative ℤ] (Multiplicative ℤ)).symm
        (doublingBialgHom ℕ).toAlgHom ∧
    ((liftGroupLikeBialgHom (R := ℕ) (A := ℕ[Multiplicative ℤ])).comp
        (mapDomainBialgHom ℕ (squarePointHom ℕ))).toAlgHom =
      lift ℕ ℕ[Multiplicative ℤ] (Multiplicative ℤ)
        ((GroupLike.valMonoidHom ℕ ℕ[Multiplicative ℤ]).comp (squarePointHom ℕ)) ∧
    ((liftGroupLikeBialgHom (R := ℕ) (A := ℕ[Multiplicative ℤ])).comp
        (mapDomainBialgHom ℕ (squarePointHom ℕ))).toCoalgHom =
      liftGroupLikeCoalgHom (fun m => squarePointHom ℕ m) ∧
    (∀ m r, ((liftGroupLikeBialgHom (R := ℕ) (A := ℕ[Multiplicative ℤ])).comp
        (mapDomainBialgHom ℕ (squarePointHom ℕ))) (single m r) =
      r • (squarePointHom ℕ m).val) ∧
    ((liftGroupLikeBialgHom (R := ℕ) (A := ℕ[Multiplicative ℤ])).comp
        (mapDomainBialgHom ℕ (squarePointHom ℕ)) = doublingBialgHom ℕ ↔
      ∀ m, doublingBialgHom ℕ (single m 1) = (squarePointHom ℕ m).val) ∧
    (liftGroupLikeBialgHom (R := ℕ) (A := ℕ[Multiplicative ℤ])).comp
        (mapDomainBialgHom ℕ ((squarePointHom ℕ).comp doubling)) =
      ((liftGroupLikeBialgHom (R := ℕ) (A := ℕ[Multiplicative ℤ])).comp
        (mapDomainBialgHom ℕ (squarePointHom ℕ))).comp (mapDomainBialgHom ℕ doubling) ∧
    (liftGroupLikeBialgHom (R := ℕ) (A := ℕ[Multiplicative ℤ])).comp
        (mapDomainBialgHom ℕ
          ((TauCeti.GroupLike.map (doublingBialgHom ℕ)).comp (squarePointHom ℕ))) =
      (doublingBialgHom ℕ).comp
        ((liftGroupLikeBialgHom (R := ℕ) (A := ℕ[Multiplicative ℤ])).comp
          (mapDomainBialgHom ℕ (squarePointHom ℕ))) ∧
    (liftGroupLikeBialgHom (R := ℕ) (A := ℕ[Multiplicative ℤ])).comp
        (mapDomainBialgHom ℕ
          ((groupLikeHomOfBialgHom (BialgHom.id ℕ ℕ[Multiplicative ℤ])).comp doubling)) =
      mapDomainBialgHom ℕ doubling ∧
    (liftGroupLikeBialgHom (R := ℕ) (A := ℕ[Multiplicative ℤ])).comp
        (mapDomainBialgHom ℕ (squarePointHom ℕ)) = doublingBialgHom ℕ ∧
    groupLikeHomOfBialgHom (doublingBialgHom ℕ) = squarePointHom ℕ ∧
    squarePointHom ℕ generator = squarePoint ℕ ∧
    squarePointHom ℕ generator⁻¹ = (squarePoint ℕ)⁻¹ ∧
    doublingBialgHom ℕ (single generator 1) = single (generator ^ 2) 1 ∧
    doublingBialgHom ℕ (single generator⁻¹ 1) = single (generator ^ 2)⁻¹ 1 ∧
    doublingBialgHom ℕ (symmetricPair ℕ) =
      single (generator ^ 2) 1 + single (generator ^ 2)⁻¹ 1 ∧
    (symmetricPair ℕ).coeff generator = 1 ∧
    (doublingBialgHom ℕ (symmetricPair ℕ)).coeff generator = 0 ∧
    symmetricPair ℕ ≠ doublingBialgHom ℕ (symmetricPair ℕ) ∧
    doublingBialgHom ℕ ≠ BialgHom.id ℕ ℕ[Multiplicative ℤ] := by
  have hJ : groupLikeHomOfBialgHom (doublingBialgHom ℕ) = squarePointHom ℕ := by
    apply (zpowersHom (GroupLike ℕ ℕ[Multiplicative ℤ])).symm.injective
    change groupLikeHomOfBialgHom (doublingBialgHom ℕ) generator =
      squarePointHom ℕ generator
    rw [squarePointHom_generator]
    apply GroupLike.val_injective
    change (groupLikeHomOfBialgHom (doublingBialgHom ℕ) generator).val =
      single (generator ^ 2) 1
    rw [groupLikeHomOfBialgHom_apply_val, doublingBialgHom_generator]
  have hL : (liftGroupLikeBialgHom (R := ℕ) (A := ℕ[Multiplicative ℤ])).comp
      (mapDomainBialgHom ℕ (squarePointHom ℕ)) = doublingBialgHom ℕ := by
    rw [← hJ]
    exact groupLikeHomOfBialgHom_rightInverse (doublingBialgHom ℕ)
  exact ⟨groupLikeHomOfBialgHom_leftInverse (squarePointHom ℕ),
    groupLikeHomOfBialgHom_rightInverse (doublingBialgHom ℕ),
    fun m => groupLikeHomOfBialgHom_apply_val (doublingBialgHom ℕ) m,
    valMonoidHom_comp_groupLikeHomOfBialgHom (doublingBialgHom ℕ),
    liftGroupLikeBialgHom_mapDomain_toAlgHom (squarePointHom ℕ),
    liftGroupLikeBialgHom_mapDomain_toCoalgHom (squarePointHom ℕ),
    fun m r => liftGroupLikeBialgHom_mapDomain_single (squarePointHom ℕ) m r,
    liftGroupLikeBialgHom_mapDomain_eq_iff (squarePointHom ℕ) (doublingBialgHom ℕ),
    liftGroupLikeBialgHom_mapDomain_comp (squarePointHom ℕ) doubling,
    liftGroupLikeBialgHom_mapDomain_groupLikeMap (squarePointHom ℕ) (doublingBialgHom ℕ),
    liftGroupLikeBialgHom_mapDomain_groupLikeHomOfBialgHom_id doubling,
    hL, hJ, squarePointHom_generator ℕ, squarePointHom_inverse ℕ,
    doublingBialgHom_generator ℕ, doublingBialgHom_inverse ℕ,
    doublingBialgHom_symmetricPair ℕ, symmetricPair_coeff_generator ℕ,
    doublingBialgHom_symmetricPair_coeff_generator ℕ, symmetricPair_ne_doubling ℕ,
    doublingBialgHom_ne_id ℕ⟩

/-- The universal correspondence pairs the cyclic square-point map with doubling
in both directions. -/
private theorem liftGroupLikeBialgHomEquiv_squarePointHom :
    liftGroupLikeBialgHomEquiv (squarePointHom ℕ) = doublingBialgHom ℕ ∧
    liftGroupLikeBialgHomEquiv.symm (doublingBialgHom ℕ) = squarePointHom ℕ := by
  rcases doubling_groupLike_extension with
    ⟨_, _, _, _, _, _, _, _, _, _, _, hL, hJ, _⟩
  rw [liftGroupLikeBialgHomEquiv_apply, liftGroupLikeBialgHomEquiv_symm_apply]
  exact ⟨hL, hJ⟩

end MonoidAlgebra.CyclicWeights

namespace MonoidAlgebra

/-- The same two inverse identities hold at the zero-scalar boundary, without a
nontriviality assumption on the scalar semiring or the target bialgebra. -/
private theorem groupLike_extension_of_subsingleton
    {R : Type uR} {M : Type uM} {A : Type uA}
    [CommSemiring R] [Subsingleton R] [Monoid M] [Semiring A] [Bialgebra R A]
    (f : M →* GroupLike R A) (F : R[M] →ₐc[R] A) :
    (0 : R) = 1 ∧
    groupLikeHomOfBialgHom
        ((liftGroupLikeBialgHom (R := R) (A := A)).comp (mapDomainBialgHom R f)) = f ∧
    (liftGroupLikeBialgHom (R := R) (A := A)).comp
        (mapDomainBialgHom R (groupLikeHomOfBialgHom F)) = F := by
  exact ⟨Subsingleton.elim 0 1, groupLikeHomOfBialgHom_leftInverse f,
    groupLikeHomOfBialgHom_rightInverse F⟩

end MonoidAlgebra
