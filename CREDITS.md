# Credits and references

**Authors: Formal Frontier Agents.** The original project contributions in
this repository are licensed under [Apache-2.0](LICENSE). The collective
credit identifies contributors, not a verified legal copyright holder.
Formal Frontier's AI agents developed proofs and examples under human project
direction.

Lattice contributed original algebraic-group, group-object and scheme
infrastructure, including clopen-rank localization. Other Formal Frontier
agent contributions include unitriangular and triangular matrix/group-scheme
constructions, finite GL/SL
geometry and dimension proofs, diagonal products, split kernels and base-change
comparisons. Anchor integrated identity-component, characteristic-morphism,
Artin–Schreier and roots-of-unity work; the original proofs remain credited
to their contributors.

Formal Frontier Agents developed the closed unitriangular-stage Hopf quotients,
native stage schemes, polynomial coordinates and underlying affine-space
comparisons. Distinct agents contributed the mathematical arguments and Lean
proofs; Lattice contributed mathematical planning and corrections. The focused
[stage](AlgebraicGroups/GroupScheme/UnitriangularStages/README.md),
[polynomial](AlgebraicGroups/Algebra/UnitriangularStagePolynomial/README.md) and
[affine-space](AlgebraicGroups/GroupScheme/UnitriangularStageAffineSpace/README.md)
guides record their reusable mathematical interfaces.

Formal Frontier Agents also developed stage normality, primitive positive-stage
coordinates and the underlying over-scheme kernel pullback. Separate
contributors developed the filtration and authored the normality, coordinate and
kernel proofs. The
[normality](AlgebraicGroups/GroupScheme/UnitriangularStageNormality/README.md),
[coordinates](AlgebraicGroups/GroupScheme/UnitriangularStageCoordinates/README.md)
and [kernel](AlgebraicGroups/GroupScheme/UnitriangularStageKernel/README.md)
guides give the respective mathematical interfaces.

Formal Frontier Agents also developed the arbitrary-ring finite additive
product's underlying affine-space comparison and the positive-stage
projection and underlying over-scheme section. Distinct agents contributed
the original mathematical arguments and Lean proofs; Lattice contributed
mathematical planning and corrections. The
[product](AlgebraicGroups/GroupScheme/AdditiveProductAffineSpace/README.md)
and [stage-projection](AlgebraicGroups/GroupScheme/UnitriangularStageProjectionBridge/README.md)
guides document these mathematical interfaces.

The proofs reuse mathlib and separately maintained project dependencies; their
contributors and licenses remain distinct. In particular the determinant-section
module retains Chris Birkbeck's authentic 2021 Apache-2.0 notice, and the
finite-free special-linear development uses Antoine Chambert-Loir's mathlib
special-linear interface. Coordinate base change uses mathlib's scalar-extension
comparison, also credited to Antoine Chambert-Loir in its focused guide.

For mathematical background see James S. Milne, *Algebraic Groups* (2017).
This bibliography supplies context, not a claim to formalize the entire book,
reproduce its text or have its author's endorsement. See the
[mathematical introduction](README.md) and [formalization metadata](formalization.yaml)
for this library's scope.
