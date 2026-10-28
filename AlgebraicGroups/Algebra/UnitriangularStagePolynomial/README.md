<!-- SPDX-License-Identifier: Apache-2.0 -->

# Polynomial coordinates of closed unitriangular stages

Import `AlgebraicGroups.Algebra.UnitriangularStagePolynomial`. Closed stages impose their
additional vanishing ideal directly on `TauCeti.UpperUnitriangular.coordinateHopfAlgebra`. The
retained polynomial presentation removes precisely the forbidden strict upper variables; its
maps and entry formulas include empty and exhausted stages and zero rings. This is an algebra
presentation of the canonical stage quotient, not an additive or Hopf identification.

See the [migration guide](../../../docs/TAUCETIFY.md) for canonical foundations and the [build
guide](../../../docs/BUILDING.md) for the pinned environment.

## Historical methods and credits

The original method and source-credit paragraphs below describe the
pre-refactor implementation; their old API names are historical. The
[complete original guide](https://github.com/FormalFrontier/algebraic-groups/blob/91a72166fbd0703b83831f490c4f0d9c18bfc4b7/AlgebraicGroups/Algebra/UnitriangularStagePolynomial/README.md) preserves the full context.
Current APIs are described above.

Milne's polynomial presentation describes the full unitriangular group
functor over a field on all its commutative algebras; his finer filtration
removes individual entries. The equivalence here identifies the
whole-superdiagonal quotient over arbitrary base rings.

The proof uses the published `UnitriangularCoordinateRing.freeEquiv` to identify
full strict-upper coordinates with a multivariable polynomial ring. The pinned
mathlib `MvPolynomial.killCompl` projection kills exactly forbidden variables,
while `rename` includes surviving variables. The projection annihilates the
stage ideal, so `Ideal.Quotient.liftₐ` gives a map from the actual
quotient. In the reverse direction, the quotient applied after `freeEquiv` and
`rename` maps generators to their universal entries. The composites agree on
all polynomial generators, and `Ideal.Quotient.algHom_ext` descends the second
identity. No cancellation argument is used, so the construction also applies
to `ZMod 1`. At `n = 0` or `1`, and whenever `r ≥ n`, there are no surviving
variables; the result is an algebra equivalence to the empty-variable
polynomial algebra, not a definitional equality with `K`.

Formal Frontier Agents developed the stage-polynomial equivalence and its
coefficient formulas. The formulas use the canonical quotient-ring semiring
structure. See [credits](https://github.com/FormalFrontier/algebraic-groups/blob/91a72166fbd0703b83831f490c4f0d9c18bfc4b7/CREDITS.md) for contributor and dependency
attribution.

- J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
  over a Field*, Cambridge University Press, 2017, item 2.9 (the full
  unitriangular group's polynomial presentation) and §6.49 (the finer
  individual-entry field-case filtration).
- Mathlib contributors, `Mathlib.Algebra.MvPolynomial.Rename`
  (`MvPolynomial.killCompl` and `MvPolynomial.rename`) and the algebra-quotient
  lifting/extensionality API.
- The existing `UnitriangularCoordinateRing.freeEquiv` gives the full group's
  free strict-upper-coordinate presentation.

With the pinned toolchain available, successfully fetch the matching mathlib
cache before any build. Focused checks can then use:

```sh
lake exe cache get
lake build AlgebraicGroups.Algebra.UnitriangularStagePolynomial
lake build AlgebraicGroupsTest.Algebra.UnitriangularStagePolynomial
```
