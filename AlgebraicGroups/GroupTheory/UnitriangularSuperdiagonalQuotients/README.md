# Current publication and verification context (2026-09-28)

These whole-stage quotients and the central filtration are published in
official release `38b7ebdcb38bd0d1b3c9a72e266162718f4647c2`.
Native job 811 applies to their older 139-module, 35-root, 12-package graph.
The accepted sharpness transfer at
`172234b1ae20be037a781f0a105ae88dfbe3e856` passed native job 843 and fresh
independent destination review on the 141-module, 36-root, 13-package graph
with its direct official `general-linear-groups` dependency.
The [sharpness guide](../UnitriangularNilpotencyClass/README.md) describes
the separate native class result. Both default builds and the complete
private/generated-inclusive standard-three audit passed; see
[current build guidance](../../../docs/BUILDING.md). The G/Q release and
sharpness P7 have since been independently accepted and published; their
release decisions are distinct from accepted-code evidence. The native
point-group lower-central equality is separately
accepted on development main `d3c455d9adac06b5a873828ea7de57d5501c42f4`
after original native job 865 built both default targets and audited all
3,634 actual module-origin declarations across 143 modules/37 test roots/13
packages, including 1,128 private-named origins under only the standard
three axioms. Its separate release review, acceptance and publication remain
pending. The original guide below (including its then-pending G/Q publication) is
preserved as dated history, not a description of current release status.

---

# Successive superdiagonal quotients of unitriangular point groups

Import `AlgebraicGroups.GroupTheory.UnitriangularSuperdiagonalQuotients` for
the successive **whole-stage point-group** quotient of the native
`Matrix.UnitriangularGroup (Fin n) R`. Let `n r : ℕ`, `R : Type`,
`[CommRing R]`, and **`1 ≤ r`**. The coefficient universe follows the native
group's `Fin n` constraint; no field, positive dimension, reducedness,
nontriviality or characteristic restriction is imposed.

Write `F_t := Matrix.UnitriangularGroup.superdiagonalSubgroup n R t`.
`superdiagonalIndex n r` is the type of positions `(i,j) : Fin n × Fin n`
with `j.val = i.val + r`. The target
`Multiplicative (superdiagonalIndex n r → R)` uses **pointwise addition**
in `R` as its group multiplication, not ring multiplication.

## Quotient and coefficient maps

- `superdiagonalCoordinateHom n R r hr` evaluates each stage element on
  these matrix positions; `superdiagonalCoordinateHom_apply` gives the
  evaluation. Its kernel **inside `F_r`** is
  `(F_(r+1)).subgroupOf F_r`, by `superdiagonalCoordinateHom_ker`.
- `superdiagonalCoordinateHom_surjective` lifts every coordinate family
  to a genuine element of `F_r`. Therefore `superdiagonalQuotientEquiv`
  identifies the **actual** quotient
  `F_r ⧸ (F_(r+1)).subgroupOf F_r` with that additive coordinate group;
  `superdiagonalQuotientEquiv_mk` evaluates it on representatives. This
  is not a quotient of the entire unitriangular group.
- For any unital `f : R →+* S` with `S : Type` and `[CommRing S]`,
  `superdiagonalStageMap` restricts the native group map,
  `superdiagonalCoordinateMap` applies `f` pointwise and
  `superdiagonalQuotientMap` descends to the actual quotients.
  `superdiagonalCoordinateHom_natural` commutes at the stage level and
  `superdiagonalQuotientEquiv_natural` commutes on **every quotient element**.
  Neither map needs injectivity or surjectivity.

For the homomorphism law, the correction `(x-1)(y-1)` vanishes at distance
`r` when `r ≥ 1`. A surjectivity witness places the requested coordinates
on just the chosen superdiagonal of a strict-upper matrix `A`. The matrix
`1+A` has determinant one and is constructed as a genuine unit in the native
group, not merely a formal matrix or a **homomorphic** section.

For example:

```lean
import AlgebraicGroups.GroupTheory.UnitriangularSuperdiagonalQuotients

open Matrix.UnitriangularGroup

example (R : Type) [CommRing R]
    (a : Multiplicative (superdiagonalIndex 3 1 → R)) :
    ∃ x : superdiagonalSubgroup 3 R 1,
      superdiagonalCoordinateHom 3 R 1 (by omega) x = a :=
  superdiagonalCoordinateHom_surjective 3 R 1 (by omega) a
```

The statements include `n=0,1`, the zero ring, characteristic two,
nonreduced rings and `r ≥ n`; in the last case both the index type and
quotient are trivial. **`r=0` is excluded**: diagonal coordinates do not
describe `F_0/F_1`. This does not construct an individual-entry filtration,
group-scheme or `Gₐ` quotient, torus or Lie result, or an exact nilpotency
class.

`AlgebraicGroupsTest.UnitriangularSuperdiagonalQuotients` exercises the
kernel, lifts, quotient evaluation and naturality for general rings/maps,
`ZMod 1/2/4`, empty superdiagonals and a noninjective coefficient map.
With the repository-pinned Lean toolchain and manifest, fetch the matching
mathlib cache **before** building either module:

```sh
lake exe cache get
LAKE_JOBS=2 lake build AlgebraicGroups.GroupTheory.UnitriangularSuperdiagonalQuotients AlgebraicGroupsTest.UnitriangularSuperdiagonalQuotients
```

The original mathematical exposition, Lean implementation and independent
isolated-code review were separate agent contributions. Their source-specific
provenance belongs to the internal owning record and is not a prerequisite
for downstream use. The destination transfer passed fresh independent review
and the complete cache-first both-root native build/transitive standard-three
audit, and was accepted at `535d623443808796af231ed5761f837c13934cdd`.
The documentation-only release preparation preserves those computational
inputs. Independent release acceptance and verified publication remain
separate, still-pending steps.
