# Common zeros over an algebraically closed field

Import `AlgebraicGroups.Algebra.AlgebraicallyClosedCommonZero`. All three theorems are
in `MvPolynomial`, accept independent universes for a field `K`, finite variable
type `σ` and finite equation type `ι`, and assume `[Field K] [IsAlgClosed K]`
and `[Fintype σ] [Fintype ι]`. Equations are an arbitrary family
`f : ι → MvPolynomial σ K`; a zero is a **K-valued tuple** `x : σ → K`.
There is no required decidable equality, distinctness or nonzero equation.

* `card_le_card_of_unique_common_zero f a` assumes
  `∀ x, (∀ i, eval x (f i) = 0) ↔ x = a` and proves
  `Fintype.card σ ≤ Fintype.card ι`. It needs no homogeneity.
* `exists_common_zero_ne f a` assumes `Fintype.card ι < Fintype.card σ`
  and `∀ i, eval a (f i) = 0`, and yields one tuple `x ≠ a` satisfying
  **all** equations. The known point is essential for arbitrary equations:
  a nonzero constant equation can have no zeros at all.
* `exists_nonzero_common_zero_of_isHomogeneous f d` assumes the same strict
  cardinality bound, `d : ι → ℕ`, `∀ i, 0 < d i` and
  `∀ i, (f i).IsHomogeneous (d i)`. It yields a nonzero common zero.
  The positive labels may differ and need not equal the actual `totalDegree`
  for zero polynomials, which are allowed.

The proof uses the strong affine Nullstellensatz to identify the radical of
the family's ideal with the vanishing ideal of its singleton zero locus.
That prime is **minimal over the original ideal**, not merely a prime containing
it. Krull's height theorem bounds its height by the cardinality of the finite
image of `f`, and the existing `height_ker_eval` identifies its height with the
number of variables. The second result contradicts uniqueness; positive
homogeneous polynomials vanish at the origin, so the third follows from the
second. The height helper is reused from
`AlgebraicGroups.Algebra.PolynomialRationalPointHeight`, not redeveloped here.

Zero variables satisfy the first inequality; the strict bound in the other
two then cannot hold. With no equations and at least one variable, both
existence results apply. Duplicates and identically zero equations are harmless.
The strict inequality is sharp: the coordinate equations `X i`, one per
variable, have only the origin as a common zero. No lower bound on the
dimension of a zero locus or assertion over non-algebraically-closed fields is
provided.

## Reproduction and status

### Accepted-code snapshot (2026-09-29, before its own release)

The three results and ordinary-import client are on protected-integrated main
`021cbd4ed92bc55704f401533846731a73079a8f` (tree
`0e9dcaf625161287c6423a76808a2ee741da195c`). Original destination H
native run 993 fetched the matching mathlib cache, built both default targets
and completed the transitive standard-three audit of all 3,803 declaration
origins, including 1,197 private origins, across 153 modules. H to accepted V
changed only documentary paths; Lean, dependency, build-root and checker inputs
are unchanged, not the documentary whole-file digests. Final author-distinct
worker-a review 4851 approved exact V after the earlier documentary objections
in reviews 4837 and 4843. Exact-V native run 1004 (job 1005) and its required
Lean CI context succeeded; Beacon separately accepted V and integrated it
into main on 2026-09-29. The diagonal predecessor is already published at P11,
but this common-zero addition has not yet received separate release acceptance
or verified official publication as of this snapshot. No source coverage is
inferred. Original proof, helper and transfer contributors remain credited below.

### Post-review correction snapshot (2026-09-29, before final-V approval)

At the 2026-09-29 post-review correction, original destination H
`94172e62b759894bd8d821a253aa3f08f68f58c2` had passed native run 993's
cache-first build of both default targets and complete transitive standard-axiom
audit, including private/generated declarations. Independent destination reviews
4837 on H and 4843 on the README-corrected U requested documentary corrections;
neither is approval of a final candidate. This correction changes no Lean,
dependency or checker input. Final-revision approval, applicable native required
checks, maintainer acceptance/integration and a separate reviewed official release
remain distinct prerequisites; no source coverage is claimed.

### Original preparation snapshot (2026-09-29, before run 993 and review 4837)

The following status and contributor account describes that original snapshot,
not the current availability of destination build or review evidence:

The isolated mathematical implementation was independently reviewed and accepted.
This addition is proposed on accepted Algebraic Groups I11
`e794bded47a4e36f830edc163f7b62892314f4cf`, whose diagonal predecessor
is separately published at verified official P11
`56c759fc12152a447e36249ee50218ce473d93ca`. The addition has **not** yet
received an applicable destination build, axiom audit, independent review or
responsible-maintainer acceptance; it is not integrated or published. Neither
stage establishes source coverage. In the
Algebraic Groups Lake project with `leanprover/lean4:v4.34.0-rc2`, mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5` and the unchanged official
published dependency pins in `lake-manifest.json`, fetch the matching cache
before building:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
LEAN_NUM_THREADS=2 lake build AlgebraicGroups.Algebra.AlgebraicallyClosedCommonZero
LEAN_NUM_THREADS=2 lake build AlgebraicGroupsTest.AlgebraicallyClosedCommonZero
```

The original common-zero proofs and ordinary-import tests are by Formal Frontier
Agents (worker-a), independently reviewed in isolation by another worker-b. The
unchanged point-height helper was first proved by Formal Frontier Agents
(worker-b) and independently reviewed separately. The earlier static packaging
and this actual-parent transfer are by distinct worker-b executions, neither an
independent destination reviewer. The destination still needs its own
exact-candidate review. The original project proofs do not
reproduce restricted source material, and a license label alone does not grant
redistribution clearance. Source-specific correspondence is recorded outside
this reusable library.
