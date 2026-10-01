# Actual lower central series of finite unitriangular groups

Import `AlgebraicGroups.GroupTheory.UnitriangularLowerCentralSeries` to identify
the lower central series of the native matrix point group
`Matrix.UnitriangularGroup (Fin n) R`, for every `n : ℕ`, `R : Type`, and
`[CommRing R]`. The index and coefficient types use the same universe in the
underlying native group. No field, domain, nonzero-ring, reducedness,
characteristic, or invertibility hypothesis is needed.

Write `γ_t = (⊤ : Subgroup (Matrix.UnitriangularGroup (Fin n) R)).lowerCentralSeries t`
and `F_r = Matrix.UnitriangularGroup.superdiagonalSubgroup n R r`.
The stage `F_r` consists of matrices whose difference from the identity
vanishes at `(i,j)` whenever `j.val < i.val + r`. Thus `F_1 = ⊤` and
`F_n = ⊥`. The series starts at `γ_0 = ⊤`, so the shift is **`γ_t = F_(t+1)`**
for *every* `t`, including `n = 0,1`, late stages, and the zero ring.

## Public API

- `elementary_mem_lowerCentralSeries_of_distance n R i j hij a d hd`:
  the unit `E_ij(a)` lies in `γ_d` whenever `i < j` and
  `hd : j.val = i.val + d + 1`.
- `elementary_mem_superdiagonalSubgroup n R i j hij a r hr`:
  `E_ij(a)` lies in `F_r` whenever `hr : i.val + r ≤ j.val`.
- `superdiagonalSubgroup_le_of_elementary_mem n R d hd H hroot`:
  for `hd : 1 ≤ d`, any subgroup `H` containing every `E_ij(a)` at
  distance **at least** `d` contains `F_d`. Neither normality of `H` nor
  nontriviality of `R` is required; one exact-distance diagonal is not enough.
- `lowerCentralSeries_eq_superdiagonalSubgroup n R t`: `γ_t = F_(t+1)`.

```lean
import AlgebraicGroups.GroupTheory.UnitriangularLowerCentralSeries

example (R : Type) [CommRing R] :
    (⊤ : Subgroup (Matrix.UnitriangularGroup (Fin 4) R)).lowerCentralSeries 1 =
      Matrix.UnitriangularGroup.superdiagonalSubgroup 4 R 2 :=
  Matrix.UnitriangularGroup.lowerCentralSeries_eq_superdiagonalSubgroup 4 R 1
```

## Mathematics and dependencies

The module imports this library's native superdiagonal filtration and its
coordinate homomorphisms (`UnitriangularSuperdiagonalQuotients`) and its native
ordered elementary commutator (`UnitriangularNilpotencyClass`). The latter uses
the separately authored official GeneralLinearGroups elementary commutator.
Each root `E_ij(a)` of distance `d + 1` lies in `γ_d` by induction on `d`,
using `⁅E_ik(a), E_kj(1)⁆ = E_ij(a)` in that order. The filtration's
commutator bound proves `γ_t ≤ F_(t+1)`.

For `1 ≤ r`, take an **ordered list product** of elementary roots at each
`r`-superdiagonal coordinate of `x ∈ F_r`. If `d ≤ r` and an arbitrary
subgroup `H` contains all roots at distances at least `d`, each factor is
in `H`. In particular, the appropriate roots also lie in `γ_(r-1)`;
their images under the public coordinate homomorphism add to the complete
coordinate family of `x`. Products of those native elements need not commute.
The difference `p⁻¹*x` belongs to the exact kernel `F_(r+1)` *inside* `F_r`.
Descending from `F_n = ⊥` proves the arbitrary-subgroup generation criterion;
applying it to the actual lower central series recovers `F_r ≤ γ_(r-1)`.
This also handles empty coordinate sets. The construction uses neither division nor a chosen
homomorphic section of the coordinate quotient. This is a native point-group
equality, not a group-scheme quotient or an unconditional exact-class theorem.

`AlgebraicGroupsTest.UnitriangularLowerCentralSeries` checks these APIs by
ordinary import over generic rings and arbitrary subgroups, dimensions `0,1,3,4`,
symbolic positive, early and late stages, arbitrary coefficients, characteristic-two `ZMod 2`, nonreduced
`ZMod 4`, and the zero ring `ZMod 1`. To check the focused producer and client
from the repository root with the pinned toolchain and manifest, successfully
fetch the matching mathlib cache first:

```sh
lake exe cache get
lake build AlgebraicGroups.GroupTheory.UnitriangularLowerCentralSeries AlgebraicGroupsTest.UnitriangularLowerCentralSeries
```


For the pinned toolchain, matching mathlib cache and default-target commands,
see the [build guide](../../../docs/BUILDING.md). Contributor and third-party
credit appears in [CREDITS](../../../CREDITS.md).
