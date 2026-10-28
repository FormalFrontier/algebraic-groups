# Commutators and derived series of finite unitriangular groups

Import `AlgebraicGroups.GroupTheory.UnitriangularDerivedSeries`. All statements use
`TauCeti.upperUnitriangularGroup (Fin n) R` and the canonical filtration in
`TauCeti.UpperUnitriangularGroup`.

The retained commutator-stage equality identifies the derived series with stages at powers of
two and computes its vanishing under the stated nontriviality hypotheses.

The focused source and regression client state the precise hypotheses and
degenerate-rank cases. Shared carriers and filtration definitions are imported
directly; no compatibility names are retained.

## Historical methods and credits

The original method and source-credit paragraphs below describe the
pre-refactor implementation; their old API names are historical. The
[complete original guide](https://github.com/FormalFrontier/algebraic-groups/blob/91a72166fbd0703b83831f490c4f0d9c18bfc4b7/AlgebraicGroups/GroupTheory/UnitriangularDerivedSeries/README.md) preserves the full context.
Current APIs are described above.

Import `AlgebraicGroups.GroupTheory.UnitriangularDerivedSeries` to work with the
native group `U = Matrix.UnitriangularGroup (Fin n) R`, where `n : ℕ`,
`R : Type` and `[CommRing R]` (the native matrix API uses a common universe
for the index and coefficient types). Write
`F_d = Matrix.UnitriangularGroup.superdiagonalSubgroup n R d` and use
mathlib's root-namespace `derivedSeries U t`, indexed from
`derivedSeries U 0 = ⊤`. Here `F_d` consists of matrices `g` for which
`(g - 1) i j = 0` whenever `j.val < i.val + d`. In particular,
`F_0 = F_1 = ⊤` and `F_n = ⊥`.

The import publicly exposes the existing lower-central-series module
(`UnitriangularLowerCentralSeries`), its native superdiagonal filtration
(`UnitriangularCentralFiltration`), the native elementary units and ordered
Steinberg commutator (`UnitriangularNilpotencyClass`), the coordinate quotient
(`UnitriangularSuperdiagonalQuotients`), and pinned mathlib's
`Mathlib.GroupTheory.Solvable`. The theorem
`superdiagonalSubgroup_commutator` proves
`⁅F_r,F_s⁆ ≤ F_(r+s)`. For the reverse inclusion, the lower-central-series
`superdiagonalSubgroup_le_of_elementary_mem` reduces it to all roots
`E_ij(a)` at distances at least `r+s`. Split each at `k=i+r`; then
`E_ik(a) ∈ F_r`, `E_kj(1) ∈ F_s`, and the *ordered* native identity
`⁅E_ik(a),E_kj(1)⁆ = E_ij(a)` places the root in the subgroup
commutator. The generation criterion itself uses an existing private
ordered-coordinate elimination; this module neither accesses nor duplicates
it. Induction on the native derived series uses its self-commutator successor
and `2^t+2^t=2^(t+1)`. For nontrivial coefficients, the preceding
lower-central-series theorem identifies `F_d=γ_(d-1)` and the exact-class
theorem gives the native nilpotency class `n-1`;
the pinned mathlib lower-central-series bot criterion gives the weak bounds
above, including dimensions zero and one.

- Mathlib contributors, `Mathlib.GroupTheory.Solvable` (native derived series),
  `Mathlib.GroupTheory.Commutator.Basic` (subgroup commutators) and
  `Mathlib.GroupTheory.Nilpotent` (lower central series and class criterion).
- General Linear Groups contributors, `GeneralLinearGroups.ElementaryCommutator`
  (the ordered elementary-unit relation used by the preceding point-group
  modules). The identities here concern point groups over commutative rings,
  not algebraic subgroup schemes.
