/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.AlgebraicallyClosedCommonZero
public import AlgebraicGroups.Algebra.Bialgebra.GroupLikeTensorProduct
public import AlgebraicGroups.Algebra.Bialgebra.MonoidAlgebra
public import AlgebraicGroups.Algebra.Bialgebra.Quotient
public import AlgebraicGroups.Algebra.Coalgebra.BaseChange
public import AlgebraicGroups.Algebra.Coalgebra.CoefficientMatrixUnit
public import AlgebraicGroups.Algebra.Coalgebra.Coefficients
public import AlgebraicGroups.Algebra.Coalgebra.ComoduleCoefficients
public import AlgebraicGroups.Algebra.Coalgebra.CounitRange
public import AlgebraicGroups.Algebra.Coalgebra.Equiv
public import AlgebraicGroups.Algebra.Coalgebra.FiniteSubcoalgebra
public import AlgebraicGroups.Algebra.Coalgebra.GroupLikeBaseChange
public import AlgebraicGroups.Algebra.Coalgebra.GroupLikeCardinality
public import AlgebraicGroups.Algebra.Coalgebra.GroupLikeCoefficients
public import AlgebraicGroups.Algebra.Coalgebra.GroupLikeCoordinates
public import AlgebraicGroups.Algebra.Coalgebra.GroupLikeHom
public import AlgebraicGroups.Algebra.Coalgebra.GroupLikeSpan
public import AlgebraicGroups.Algebra.Coalgebra.IdempotentIdeal
public import AlgebraicGroups.Algebra.Coalgebra.MonoidAlgebra
public import AlgebraicGroups.Algebra.Coalgebra.Quotient
public import AlgebraicGroups.Algebra.Coalgebra.TensorProductQuotient
public import AlgebraicGroups.Algebra.Coalgebra.RightComodule
public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.TensorProduct
public import AlgebraicGroups.Algebra.Coalgebra.RightComodule.Transport
public import AlgebraicGroups.Algebra.Coalgebra.SkewPrimitive
public import AlgebraicGroups.Algebra.Coalgebra.TensorProduct
public import AlgebraicGroups.Algebra.LocalizedCoordinateQuotient
public import AlgebraicGroups.Algebra.FinitePolynomialLocalizationDimension
public import AlgebraicGroups.Algebra.GeneralLinearCoordinateRing.Dimension
public import AlgebraicGroups.Algebra.TensorProduct.Pi
public import AlgebraicGroups.Algebra.TensorProduct.Split
public import AlgebraicGroups.Algebra.Smooth
public import AlgebraicGroups.Algebra.SymmetricAlgebra
public import AlgebraicGroups.Algebra.SymmetricAlgebraPoints
public import AlgebraicGroups.Algebra.HopfAlgebra.Hom
public import AlgebraicGroups.Algebra.PrimitivePowerHopfIdeal
public import AlgebraicGroups.Algebra.SpecialLinearCoordinateRing
public import AlgebraicGroups.Algebra.UnitriangularCoordinateRing
public import AlgebraicGroups.Algebra.UnitriangularStageCoordinateRing
public import AlgebraicGroups.Algebra.UnitriangularStagePolynomial
public import AlgebraicGroups.Algebra.UnitriangularBaseChange
public import AlgebraicGroups.Algebra.UnitriangularBaseChangeCoherence
public import AlgebraicGroups.Algebra.UnitriangularHopfBaseChange
public import AlgebraicGroups.Algebra.MonoidAlgebraPrimitive
public import AlgebraicGroups.Algebra.HopfAlgebra.Antipode
public import AlgebraicGroups.Algebra.HopfAlgebra.Comultiplication
public import AlgebraicGroups.Algebra.HopfAlgebra.GroupLike
public import AlgebraicGroups.Category.Extensive
public import AlgebraicGroups.Category.EquivalenceRelation
public import AlgebraicGroups.Category.Grp.FilteredColimits
public import AlgebraicGroups.FieldTheory.GeometricallyReduced
public import AlgebraicGroups.GroupObject.BaseChange
public import AlgebraicGroups.GroupObject.Characteristic
public import AlgebraicGroups.GroupObject.Commutative
public import AlgebraicGroups.GroupObject.Coset
public import AlgebraicGroups.GroupObject.EffectiveEpi
public import AlgebraicGroups.GroupObject.FunctorCategory
public import AlgebraicGroups.GroupObject.FunctorLimits
public import AlgebraicGroups.GroupObject.Hom
public import AlgebraicGroups.GroupObject.Kernel
public import AlgebraicGroups.GroupObject.MonoidKernel
public import AlgebraicGroups.GroupObject.PullbackMonoid
public import AlgebraicGroups.GroupObject.KernelTorsor
public import AlgebraicGroups.GroupObject.Quotient
public import AlgebraicGroups.GroupObject.SplitKernelProduct
public import AlgebraicGroups.GroupObject.SplitKernelSemidirect
public import AlgebraicGroups.GroupObject.Translation
public import AlgebraicGroups.GroupScheme.Additive
public import AlgebraicGroups.GroupScheme.AdditiveProductAffineSpace
public import AlgebraicGroups.GroupScheme.AffineHomOverConvolution
public import AlgebraicGroups.GroupScheme.Vector
public import AlgebraicGroups.GroupScheme.VectorProduct
public import AlgebraicGroups.GroupScheme.MatrixEndAdditive
public import AlgebraicGroups.GroupScheme.MatrixEndScheme
public import AlgebraicGroups.GroupScheme.AdditivePowerQuotient
public import AlgebraicGroups.GroupScheme.ArtinSchreierTwistedLine
public import AlgebraicGroups.GroupScheme.ClosedPoints
public import AlgebraicGroups.GroupScheme.Commutative
public import AlgebraicGroups.GroupScheme.ComponentGroup
public import AlgebraicGroups.GroupScheme.ComponentQuotient
public import AlgebraicGroups.GroupScheme.ComponentSchemeMap
public import AlgebraicGroups.GroupScheme.CosetDimension
public import AlgebraicGroups.GroupScheme.CosetQuotient
public import AlgebraicGroups.GroupScheme.Dimension
public import AlgebraicGroups.GroupScheme.FiniteConstant
public import AlgebraicGroups.GroupScheme.FiniteConstantPoints
public import AlgebraicGroups.GroupScheme.FiniteTriangularGeometry
public import AlgebraicGroups.GroupScheme.FiniteTypePoints
public import AlgebraicGroups.GroupScheme.FrobeniusTwistedLine
public import AlgebraicGroups.GroupScheme.FrobeniusTwistedLineBaseChange
public import AlgebraicGroups.GroupScheme.GeneralLinear
public import AlgebraicGroups.GroupScheme.GeometricallyIntegral
public import AlgebraicGroups.GroupScheme.Diagonal
public import AlgebraicGroups.GroupScheme.DiagonalDimension
public import AlgebraicGroups.GroupScheme.DiagonalProduct
public import AlgebraicGroups.GroupScheme.Unitriangular
public import AlgebraicGroups.GroupScheme.UnitriangularGeometry
public import AlgebraicGroups.GroupScheme.UnitriangularStages
public import AlgebraicGroups.GroupScheme.UnitriangularStageAffineSpace
public import AlgebraicGroups.Algebra.UnitriangularStageCoordinates
public import AlgebraicGroups.Algebra.UnitriangularStageKernel
public import AlgebraicGroups.GroupScheme.UnitriangularStageNormality
public import AlgebraicGroups.GroupScheme.UnitriangularStageCoordinates
public import AlgebraicGroups.GroupScheme.UnitriangularStageKernel
public import AlgebraicGroups.GroupScheme.UnitriangularStageProjectionBridge
public import AlgebraicGroups.GroupScheme.UnitriangularBaseChange
public import AlgebraicGroups.GroupScheme.UnitriangularBaseChangeCoherence
public import AlgebraicGroups.GroupTheory.UpperTriangular
public import AlgebraicGroups.GroupScheme.UpperTriangular
public import AlgebraicGroups.GroupScheme.UpperTriangularDimension
public import AlgebraicGroups.GroupScheme.UpperTriangularSplitKernel
public import AlgebraicGroups.GroupScheme.UpperTriangularSchemeProduct
public import AlgebraicGroups.LinearAlgebra.Matrix.UpperTriangularIndices
public import AlgebraicGroups.GroupTheory.UnitriangularCentralFiltration
public import AlgebraicGroups.GroupTheory.UnitriangularSuperdiagonalQuotients
public import AlgebraicGroups.GroupTheory.UnitriangularNilpotencyClass
public import AlgebraicGroups.GroupTheory.UnitriangularLowerCentralSeries
public import AlgebraicGroups.GroupTheory.UnitriangularDerivedSeries
public import AlgebraicGroups.GroupTheory.UnitriangularExponent
public import AlgebraicGroups.GroupScheme.GeneralLinearDeterminant
public import AlgebraicGroups.GroupScheme.GeneralLinearDeterminantProduct
public import AlgebraicGroups.GroupScheme.GeneralLinearDeterminantConjugation
public import AlgebraicGroups.GroupScheme.GeneralLinearDeterminantSection
public import AlgebraicGroups.GroupScheme.GeneralLinearModule
public import AlgebraicGroups.GroupScheme.GeneralSpecialLinearDimension
public import AlgebraicGroups.GroupScheme.GeneralSpecialLinearGeometricIntegral
public import AlgebraicGroups.GroupScheme.GeneralSpecialLinearSmooth
public import AlgebraicGroups.GroupScheme.IdentityComponent
public import AlgebraicGroups.GroupScheme.IdentityComponentBaseChange
public import AlgebraicGroups.GroupScheme.InfinitesimalAdditive
public import AlgebraicGroups.GroupScheme.InfinitesimalAdditiveNonisomorphism
public import AlgebraicGroups.GroupScheme.InfinitesimalAdditiveTranslation
public import AlgebraicGroups.GroupScheme.InfinitesimalAdditiveZero
public import AlgebraicGroups.GroupScheme.Multiplicative
public import AlgebraicGroups.GroupScheme.PointwiseSubgroup
public import AlgebraicGroups.GroupScheme.QuotientSheaf
public import AlgebraicGroups.GroupScheme.Reduction
public import AlgebraicGroups.GroupScheme.ReducedIdentityComponent
public import AlgebraicGroups.GroupScheme.RootsOfUnity
public import AlgebraicGroups.GroupScheme.Separated
public import AlgebraicGroups.GroupScheme.SpecialLinearKernel
public import AlgebraicGroups.GroupScheme.SpecialLinearModule
public import AlgebraicGroups.GroupScheme.Smooth
public import AlgebraicGroups.LinearAlgebra.Basis.Semilocal
public import AlgebraicGroups.LinearAlgebra.FiniteProjective.Charpoly
public import AlgebraicGroups.RingTheory.Equalizer
public import AlgebraicGroups.RingTheory.FaithfullyFlat
public import AlgebraicGroups.RingTheory.LocalInfiniteResidueExtension
public import AlgebraicGroups.RingTheory.Semilocal
public import AlgebraicGroups.Scheme.Artinian
public import AlgebraicGroups.Scheme.AffineRelationQuotient
public import AlgebraicGroups.Scheme.ClopenAffine
public import AlgebraicGroups.Scheme.EquivalenceRelationRank
public import AlgebraicGroups.Scheme.EquivalenceRelationRankAffine
public import AlgebraicGroups.Scheme.EquivalenceRelationRankEqualizer
public import AlgebraicGroups.Scheme.EquivalenceRelationIntegrality
public import SchemeProperties.ConnectedComponents
public import AlgebraicGroups.Scheme.FiniteCoproduct
public import AlgebraicGroups.Scheme.GeometricallyReduced
public import AlgebraicGroups.Scheme.GlobalSections
public import AlgebraicGroups.Scheme.JointlySchemeTheoreticallyDominant
public import AlgebraicGroups.Scheme.Reduction
public import AlgebraicGroups.Scheme.Smooth
public import AlgebraicGroups.Topology.KrullDimension
public import AlgebraicGroups.Algebra.Coalgebra.Subcoalgebra.Hom
public import AlgebraicGroups.Algebra.Coalgebra.Subcoalgebra.Map
public import AlgebraicGroups.Algebra.Coalgebra.Subcoalgebra.Finite
public import AlgebraicGroups.Algebra.Coalgebra.Subcoalgebra.Equiv

/-!
# Algebraic groups and group schemes

Right comodules specify linear coactions `ρ : M →ₗ[R] M ⊗[R] C` over arbitrary
commutative semirings, on modules with additive commutative monoid structures
and independent scalar, coalgebra and module universes. The definitions impose
no projectivity. Flatness of `C` gives induced subtype coactions from image
stability, subcomodule extensionality and unique colinear factorization.
Projectivity of `C` places every finite subset of `M` in a finitely generated
subcomodule with a subtype coaction and colinear inclusion, hence image stability
for every member. Neither module need be finitely generated; `M` need not be
projective or free, and the counit need not be surjective.

The regular coaction specializes this coefficient method to finite right-coideal
containment for projective coalgebras (including free ones). The distinct field
step gives two-factor tensor-image containment. Coalgebra APIs also include
coefficient spans and Hopf coefficient matrix units. The counit range is an
idempotent scalar ideal acting on the whole coalgebra, and idempotent principal
ideals have explicit coalgebra constructors. Split free presentations supply
finite tensor coordinates without freeness of the presented module.

Group-like elements of a coalgebra over a commutative semiring correspond to
coalgebra morphisms from the canonical scalar coalgebra. Scalar multiplication
constructs the morphism, and evaluation at `1` recovers the group-like element.

The aggregate exposes the finite upper-unitriangular Hopf quotient, affine
group scheme and underlying affine geometry, closed superdiagonal
stage Hopf quotients and underlying affine-space presentations, stage normality,
positive-stage additive coordinates and the underlying over-scheme kernel,
central filtration, successive quotients, exact nilpotency class under nontriviality, the
all-stage lower-central-series identification and the derived series
and sharp prime-power exponent bounds for the upper-unitriangular point group alongside
the general- and special-linear constructions.

The coalgebra API defines subcoalgebras over a field as subspaces closed under
comultiplication into the image of their tensor square. Each subtype carries
the restricted coalgebra, with a bundled inclusion and unique codomain
restriction for homomorphisms. Every finitely generated subspace lies in a
finite-dimensional subcoalgebra, without a finite-dimensionality assumption
on the ambient coalgebra.

## References

- M. E. Sweedler, *Hopf Algebras* (1969), for classical comodules, the field
  coalgebra theorem and coefficient method (bibliographic credit); Mathlib for
  coalgebra laws, antipodes, tensor coordinates, flatness, linear maps and split
  free presentations.
- J. S. Milne, *Algebraic Groups* (2017), selected items in §§1–2 and §6,
  for group functors, linear groups and unitriangular filtrations; and *Basic
  Theory of Affine Group Schemes* (2012), XI §16, Example 16.3 and XIII §3,
  item 3.14, for field-base special-linear dimension and determinant splitting.
- The Stacks Project, tags 03BH–03BJ and 03BM, for invariant rings of finite
  locally free relations; Mathlib for affine group schemes, matrix algebra
  and categorical limits; and SchemeProperties for finite-type point functors
  and connected components.

The [mathematical topic guide](docs/MATHEMATICS.md) locates the specific
antecedents and prior formalizations without identifying the general-base
constructions with their field-base sources.
-/

namespace AlgebraicGeometry

/-- The proposition that the local ring at the unit of a locally finite-type group
scheme over a field has Krull dimension equal to the scheme's topological Krull dimension. -/
private def unitStalkDimension.{u} : Prop :=
  type_of% (@AlgebraicGeometry.ringKrullDim_stalk_unit_eq_topologicalKrullDim.{u})

end AlgebraicGeometry
