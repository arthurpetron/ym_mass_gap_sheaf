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
import YMGap.Constructive.CRealMul
import YMGap.Constructive.FinSumAlg
import YMGap.Constructive.ExpNeg
import YMGap.Constructive.ExpPos
import YMGap.Constructive.CRealAdd
import YMGap.Constructive.CRealMulMono
import YMGap.Constructive.CauchyConv
import YMGap.Constructive.ProductDecomp
import YMGap.Constructive.CornerBound
import YMGap.Constructive.ProductLaw
import YMGap.Constructive.CharacterTail
import YMGap.RepTheory.SU2
import YMGap.RepTheory.RepData
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
import YMGap.Continuum.SigmaHatLimit
import YMGap.Continuum.ContinuumMeasure
import YMGap.Continuum.OSAxioms
import YMGap.Continuum.OSReconstruction
import YMGap.Continuum.SpectralGap
import YMGap.Continuum.SpectralGapConverse
import YMGap.Continuum.SpectralGapGrowth
import YMGap.MassGap.SU2
import YMGap.BufferShell
import YMGap.Codynamic
import YMGap.HigherCategorical
import YMGap.PolyAtlas
import YMGap.ModuliAlgebra
