/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Group.Commutator
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.Data.List.OfFn
import Mathlib.Data.Set.Image

/-!
# Ordered commutator word maps

For a group object `G` in a Cartesian monoidal category, `GrpObj.commutatorWord P` is the
ordered product of the commutators of the pairs of projections of a supplied fan `P`.
The convention is `⁅a, b⁆ = a * b * a⁻¹ * b⁻¹`, and the pairs occur in increasing `Fin` order.
No commutativity assumption is made.

The definition and its characteristic formulas do not require the fan to be limiting.
For a limiting target fan, its universal property constructs an extension by a unit pair;
`GrpObj.range_commutatorWord_subset` then gives increasing ranges on generalized points.
These ranges are sets, with no subgroup assertion. The word maps need not be monoid morphisms.

## Implementation notes

The operations are those of Mathlib's group on `Hom(Y, G)`, using the given group object.
The supplied fan retains its point and projections; no product object is chosen here.
A differently indexed power can be used by reindexing its projections on the same point.

## References

* Mathlib, `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`, for the group on generalized
  points, its precomposition maps and the single commutator morphism.
* Mathlib, `Mathlib.CategoryTheory.Monoidal.Cartesian.Mon`, for postcomposition by monoid
  morphisms as monoid homomorphisms on generalized points.
* Mathlib, `Mathlib.Algebra.BigOperators.Group.List.Basic` and `Mathlib.Data.List.OfFn`,
  for ordered products and lists indexed by `Fin`.
* Mathlib, `Mathlib.CategoryTheory.Limits.Shapes.Products`, for lifts into a supplied
  limiting fan.
-/

@[expose] public section

universe u v

namespace CategoryTheory.GrpObj

open Limits CartesianMonoidalCategory
open scoped CategoryTheory.MonObj commutatorElement

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable {G H : C} [GrpObj G] [GrpObj H]

/-- The ordered product of commutators of the pairs of projections of a supplied fan.
The product uses increasing `Fin n` order in the group `Hom(P.pt, G)`. -/
def commutatorWord {n : ℕ} (P : Fan (fun _ : Fin n × Fin 2 => G)) : P.pt ⟶ G :=
  (List.ofFn (fun i : Fin n => ⁅P.proj (i, 0), P.proj (i, 1)⁆)).prod

/-- The characteristic ordered-product formula for a commutator word map. -/
theorem commutatorWord_eq {n : ℕ} (P : Fan (fun _ : Fin n × Fin 2 => G)) :
    commutatorWord P =
      (List.ofFn (fun i : Fin n => ⁅P.proj (i, 0), P.proj (i, 1)⁆)).prod :=
  rfl

/-- Evaluating a commutator word on an arbitrary generalized point gives the ordered
product of the commutators of its coordinates. -/
theorem comp_commutatorWord {n : ℕ} (P : Fan (fun _ : Fin n × Fin 2 => G))
    {Y : C} (f : Y ⟶ P.pt) :
    f ≫ commutatorWord P =
      (List.ofFn (fun i : Fin n =>
        ⁅f ≫ P.proj (i, 0), f ≫ P.proj (i, 1)⁆)).prod := by
  rw [commutatorWord_eq]
  calc
    _ = (List.ofFn (fun i : Fin n => f ≫ ⁅P.proj (i, 0), P.proj (i, 1)⁆)).prod := by
      let precomp : (P.pt ⟶ G) →* (Y ⟶ G) := ((yonedaGrpObj G).map f.op).hom
      have precomp_apply (g : P.pt ⟶ G) : precomp g = f ≫ g := rfl
      simpa [List.map_ofFn, Function.comp_def, precomp_apply] using
        (map_list_prod precomp
          (List.ofFn (fun i : Fin n => ⁅P.proj (i, 0), P.proj (i, 1)⁆)))
    _ = _ := by simp only [commutatorElement_def, MonObj.comp_mul, comp_inv]

/-- The empty commutator word is the unit generalized point. -/
@[simp]
theorem commutatorWord_zero (P : Fan (fun _ : Fin 0 × Fin 2 => G)) :
    commutatorWord P = (1 : P.pt ⟶ G) := by
  simp only [commutatorWord_eq, List.ofFn_zero, List.prod_nil]

/-- A word with one pair is the composite of that pair with the categorical commutator. -/
@[simp]
theorem commutatorWord_one (P : Fan (fun _ : Fin 1 × Fin 2 => G)) :
    commutatorWord P = lift (P.proj (0, 0)) (P.proj (0, 1)) ≫ commutator G := by
  rw [commutatorWord_eq, lift_commutator_eq_mul_mul_inv_inv, List.ofFn_succ]
  simp [commutatorElement_def]

/-- A monoid morphism between the given group objects commutes with the word maps along
any map of fans having the indicated coordinate equations. -/
theorem commutatorWord_naturality {n : ℕ}
    (P : Fan (fun _ : Fin n × Fin 2 => G))
    (Q : Fan (fun _ : Fin n × Fin 2 => H))
    (φ : G ⟶ H) [IsMonHom φ] (d : P.pt ⟶ Q.pt)
    (hd : ∀ j, d ≫ Q.proj j = P.proj j ≫ φ) :
    commutatorWord P ≫ φ = d ≫ commutatorWord Q := by
  rw [commutatorWord_eq P, comp_commutatorWord Q d]
  calc
    _ = (List.ofFn (fun i : Fin n => ⁅P.proj (i, 0), P.proj (i, 1)⁆ ≫ φ)).prod := by
      simpa [List.map_ofFn, Function.comp_def] using
        (map_list_prod (IsMonHom.monoidHom φ P.pt)
          (List.ofFn (fun i : Fin n => ⁅P.proj (i, 0), P.proj (i, 1)⁆)))
    _ = _ := by simp only [commutatorElement_def, MonObj.mul_comp, inv_comp, hd]

/-- Appending a pair of unit coordinates leaves the commutator word unchanged. -/
theorem comp_commutatorWord_extension {n : ℕ}
    (P : Fan (fun _ : Fin n × Fin 2 => G))
    (Q : Fan (fun _ : Fin (n + 1) × Fin 2 => G)) (e : P.pt ⟶ Q.pt)
    (hold : ∀ (i : Fin n) (j : Fin 2),
      e ≫ Q.proj (i.castSucc, j) = P.proj (i, j))
    (hlast : ∀ j : Fin 2, e ≫ Q.proj (Fin.last n, j) = (1 : P.pt ⟶ G)) :
    e ≫ commutatorWord Q = commutatorWord P := by
  rw [comp_commutatorWord, List.ofFn_succ', List.prod_concat]
  simp [hold, hlast, commutatorWord_eq, commutatorElement_def]

/-- If the next fan is limiting, appending a unit pair makes every value of the
commutator word a value of the next word, on generalized points from any object.
Only the target fan needs to be limiting. -/
theorem range_commutatorWord_subset {n : ℕ}
    (P : Fan (fun _ : Fin n × Fin 2 => G))
    (Q : Fan (fun _ : Fin (n + 1) × Fin 2 => G)) (hQ : IsLimit Q) (Y : C) :
    Set.range (fun f : Y ⟶ P.pt => f ≫ commutatorWord P) ⊆
      Set.range (fun f : Y ⟶ Q.pt => f ≫ commutatorWord Q) := by
  let e : P.pt ⟶ Q.pt := Fan.IsLimit.lift hQ (fun j =>
    Fin.snoc (α := fun _ : Fin (n + 1) => P.pt ⟶ G)
      (fun i => P.proj (i, j.2)) 1 j.1)
  have he : e ≫ commutatorWord Q = commutatorWord P := by
    apply comp_commutatorWord_extension P Q e
    · intro i j
      simp [e]
    · intro j
      simp [e]
  simpa only [Function.comp_def, Category.assoc, he] using
    (Set.range_comp_subset_range (fun f : Y ⟶ P.pt => f ≫ e)
      (fun f : Y ⟶ Q.pt => f ≫ commutatorWord Q))

end CategoryTheory.GrpObj
