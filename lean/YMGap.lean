/-
Root aggregator for the `YMGap` Lean library.

Each phase's constructivity-critical modules are imported here so
`lake build` covers the whole library.

Currently populated:

  * Milestone 1.1 — SU(2) Casimir spectrum (RepTheory).
  * Milestone 2.1 — Sheaf framework: site, bound-witness presheaf
    with flabbiness, summability-certificate record, domination
    gluing on the buffer overlap, and the named compatibility
    predicate type.  See `formal/sheaf-framework.tex` and
    `docs/sheaf-framework.md`.
-/
import YMGap.Constructive.Rationals
import YMGap.Constructive.RationalsMul
import YMGap.Constructive.AbsQ
import YMGap.Constructive.RationalTail
import YMGap.Constructive.Geometric
import YMGap.Constructive.GeometricTail
import YMGap.Constructive.HalfPow
import YMGap.Constructive.RatNat
import YMGap.Constructive.CRealLe
import YMGap.Constructive.Reals
import YMGap.Constructive.RegularCReal
import YMGap.Constructive.RegularCRealArith
import YMGap.Constructive.CRealMul
import YMGap.Constructive.FinSumAlg
import YMGap.Constructive.ExpNeg
import YMGap.Constructive.ExpPos
import YMGap.Constructive.CRealAdd
import YMGap.Constructive.CRealMulMono
import YMGap.Constructive.SumOfSquares
import YMGap.Constructive.QPoly
import YMGap.Constructive.Sqrt
import YMGap.Constructive.CRealAbs
import YMGap.Constructive.CRealComplete
import YMGap.Constructive.TrigBound
import YMGap.Constructive.Trig
import YMGap.Constructive.TrigAdd
import YMGap.Constructive.CauchyConv
import YMGap.Constructive.ExpAddConv
import YMGap.Constructive.ProductDecomp
import YMGap.Constructive.ProductDecompAdd
import YMGap.Constructive.CornerBound
import YMGap.Constructive.CornerBoundAdd
import YMGap.Constructive.ProductLaw
import YMGap.Constructive.ExpAdd
import YMGap.Constructive.CRealMulLe
import YMGap.Constructive.Soundness
import YMGap.Constructive.ExpGeomMaj
import YMGap.Constructive.CRealSum
import YMGap.Constructive.FinSumGeom
import YMGap.Constructive.CharacterTail
import YMGap.Constructive.ExpGeomBound
import YMGap.Constructive.ExpGeomSum
import YMGap.Constructive.GeomBeatsLinear
import YMGap.Constructive.CharacterTermBound
import YMGap.Constructive.ExpNegCongr
import YMGap.Constructive.SU3CharFactor
import YMGap.RepTheory.SU2
import YMGap.RepTheory.SU3
import YMGap.RepTheory.RepData
import YMGap.RepTheory.SimpleGroup
import YMGap.RepTheory.CasimirData
import YMGap.Sheaf.Site
import YMGap.Sheaf.BoundWitness
import YMGap.Sheaf.Summability
import YMGap.Sheaf.Gluing
import YMGap.Sheaf.PolymerDomination
import YMGap.Sheaf.SU2KP
import YMGap.Constructive.ExpBound
import YMGap.Constructive.ExpUBInstance
import YMGap.RG.InductiveState
import YMGap.RG.BlockSpin
import YMGap.RG.SigmaHatPilot
import YMGap.RG.SigmaHatPilotUV
import YMGap.RG.UniformBudget
import YMGap.RG.CharacterTailAntitone
import YMGap.RG.CharacterTailMajorant
import YMGap.RG.RankCollapse
import YMGap.RG.EtaPackaging
import YMGap.RG.PolylogTail
import YMGap.RG.PerAxisTail
import YMGap.RG.SUNWeylData
import YMGap.RG.TonelliFactor
import YMGap.RG.WeylCharacterBound
import YMGap.RG.WeylDimGeneral
import YMGap.Continuum.SigmaHatLimit
import YMGap.Continuum.ContinuumMeasure
import YMGap.Continuum.ObservableMeasure
import YMGap.Continuum.WilsonFunctional
import YMGap.Continuum.ReflectionPositivity
import YMGap.Continuum.Pivot2Defs
import YMGap.Continuum.Pivot2Identity
import YMGap.Continuum.Pivot2Moments
import YMGap.Continuum.Pivot2Nonneg
import YMGap.Continuum.Pivot2
import YMGap.Continuum.Pivot2Schur
import YMGap.Continuum.Pivot3Defs
import YMGap.Continuum.Pivot3Moments
import YMGap.Continuum.Pivot3Identity
import YMGap.Continuum.Pivot3Form
import YMGap.Continuum.Pivot3
import YMGap.Continuum.MomentPositivity
import YMGap.Continuum.E2ProductFunctional
import YMGap.Continuum.Favard
import YMGap.Continuum.QHankel
import YMGap.Continuum.FavardRec
import YMGap.Continuum.LGVPositivity
import YMGap.Continuum.HeatKernelPos
import YMGap.Continuum.TrigAverage
import YMGap.Continuum.GramReduction
import YMGap.Continuum.HeatKernelPos2
import YMGap.Continuum.Positivstellensatz
import YMGap.Continuum.MarkovLukacs
import YMGap.Continuum.ChebyshevBound
import YMGap.Continuum.ChebyshevU
import YMGap.Continuum.HeatKernelConv
import YMGap.Continuum.HeatKernelConvGen
import YMGap.Continuum.ThetaConv
import YMGap.Continuum.ThetaConvGen
import YMGap.Continuum.MomentBridge
import YMGap.Continuum.UTelescope
import YMGap.Continuum.GaussQBinom
import YMGap.Continuum.TsumDeriv
import YMGap.Continuum.DiffProduct
import YMGap.Continuum.JTPIdentity
import YMGap.Continuum.JTPInstance
import YMGap.Continuum.ThetaLimit
import YMGap.Continuum.ThetaParam
import YMGap.Continuum.RealTheta
import YMGap.Continuum.PNDeterminant
import YMGap.Continuum.ContinuumExistence
import YMGap.Continuum.PartitionPos
import YMGap.Continuum.KPIncrement
import YMGap.Continuum.FiniteVolume
import YMGap.Continuum.PNPaths
import YMGap.Continuum.PNInduction
import YMGap.Continuum.GramReduction3
import YMGap.Continuum.PlaquetteReweight
import YMGap.Continuum.KPLimit
import YMGap.Continuum.RGTransport
import YMGap.Continuum.OSAxioms
import YMGap.Continuum.OSReconstruction
import YMGap.Continuum.SpectralGap
import YMGap.Continuum.SpectralGapConverse
import YMGap.Continuum.SpectralGapGrowth
import YMGap.Continuum.LocatedSpectralGap
import YMGap.Continuum.HeatKernelGap
import YMGap.MassGap.SU2
import YMGap.MassGap.SimpleGroup
import YMGap.Continuum.SqrtBridge
import YMGap.Continuum.FiniteVolumeGNS
import YMGap.Continuum.OSContent
import YMGap.Continuum.CompactTransferGNS
import YMGap.Continuum.LocatedReconstruction
import YMGap.Continuum.FourDExistence
import YMGap.Continuum.CarrierPrecursors
import YMGap.Continuum.ContinuumGapLimit
import YMGap.Continuum.ClusterGapReduction
import YMGap.Continuum.ContinuumFunctional
import YMGap.Continuum.RegularFunctional
import YMGap.Continuum.ClusterBoundInstance
import YMGap.Continuum.SigmaGroundedFloor
import YMGap.Continuum.NonSaturatedFloor
import YMGap.Continuum.RegularContinuumPipeline
import YMGap.Continuum.RGGapPersistence
import YMGap.Continuum.ProductFloor
import YMGap.Continuum.HeatKernelPersistence
import YMGap.Continuum.PhysicalSeparator
import YMGap.Continuum.HeatKernelLinearBound
import YMGap.Continuum.HeatKernelRGStep
import YMGap.Continuum.PerScaleContraction
import YMGap.Continuum.PerScaleCompose
import YMGap.BufferShell
import YMGap.Codynamic
import YMGap.HigherCategorical
import YMGap.Categorical.Core
import YMGap.Categorical.RGCategory
import YMGap.Categorical.CodynCat
import YMGap.Categorical.BudgetDomination
import YMGap.Continuum.ReflectionDagger
import YMGap.Continuum.DynamicToStaticGap
import YMGap.Continuum.BareAFDiagnostic
import YMGap.Continuum.HierarchicalGap
import YMGap.Continuum.NonAbelianGapChain
-- NOTE: `YMGap.PolyAtlas` and `YMGap.ModuliAlgebra` are non-load-bearing
-- expository/design-closure scaffolding (their own headers state "NOT
-- load-bearing"); no other module imports them and nothing references their
-- contents.  They are intentionally EXCLUDED from the default build aggregator
-- to keep the load-bearing / axiom-audit surface honest.  The files remain on
-- disk and build on demand (`lake build YMGap.PolyAtlas YMGap.ModuliAlgebra`).
