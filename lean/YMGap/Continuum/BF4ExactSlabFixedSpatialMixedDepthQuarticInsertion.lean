/-
# Original mixed-depth selected quartic budget

The probe is the literal squared chord, independent of the heat cutoff.
The original one-window right-tail comparison transports its matched-source
profile bound to right depths n and n+1, with certified cap sixteen and
explicit error 32*mixRate^n. The depth cutoff is computed, independent of K
and the selected link. This is a quartic component, not the full filtered
noise-minus-drift or an OWN-variance/survival estimate.
-/

import YMGap.Continuum.SU2HeatJacobiOriginalHaarQuarticCutoff
import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowBracket
import YMGap.Continuum.BF4ExactSlabFixedSpatialLinkQuartic
import YMGap.Continuum.PositiveContractionResidual
import YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredRadialDrift

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialMixedDepthQuarticInsertion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (PolyQuaternion characterPolynomial OrientedBF4Link)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (polynomialProduct_perm)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionHeadChainComposition (chain)
open YMGap.Continuum.SU2QuaternionHeadWindowContraction (windowMessage_pairing)
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry (scalarAt heatAt)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals (productHeat heatAt_symm)
open YMGap.Continuum.SU2QuaternionProductHeatPositive (insertion)
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap (eraseIndex select_perm heatAt_eq_prefix)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight link orientedLink)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
  (activeBlocks activeBlocks_lt kineticWeight_eq_indexedProduct)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage terminalPair_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialGroundStateEnergy (endpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracket (massRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (edgeDensity)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (oddMass oddMass_positive terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredNoiseDrift
  (evenPartition evenPartition_middle_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredRadialDrift
  (mixedDensity mixedDensity_window_pairing terminalEdge_probe_pairing)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonKineticIncrement (upperOriented)
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace (haarNorm_coordinate)
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv)
open YMGap.Continuum.QuaternionHaarChordalDifference
open YMGap.Continuum.QuaternionHaarWordDifference (difference)
open YMGap.Continuum.SU2QuaternionHeatQuarticExpansion (defect)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialHeatNomeComparison (selectedInsertion)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2HeatJacobiFinitePrefixMargin (quarticProfileCoefficient)
open YMGap.Continuum.SU2HeatJacobiOriginalHaarQuarticBound
open YMGap.Continuum.SU2HeatJacobiOriginalHaarQuarticCutoff
open YMGap.Continuum.PositiveContractionResidual (geometricCutoff geometric_bound)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" blocks:arg => quaternionHaar blocks
attribute [local irreducible] baseLinks spatialWeight kineticWeight terminalMessage weightedMass oddMass
  mixRate windowRatio mixedDensity

/-- The actual squared chord probe, deliberately independent of q and K. -/
def selectedQuarticProbe (width i : Nat) : RatPoly :=
  let d := polySmul 2 (polyAdd polyOne (polyNeg (scalarAt (N width+i) i)))
  polyMul d d

/-- A certified cap of sixteen, not a supplied pointwise bound. -/
def selectedQuarticProbe_interval (width i : Nat) (hi : i<N width) :
    Interval (N width+N width) (selectedQuarticProbe width i) 16 := by
  let X := scalarAt (N width+i) i
  let P : SquareBound (N width+N width) X 1 :=
    relativeScalarSquare (by omega) (by omega)
  let D : SquareBound (N width+N width) (polySmul 2 (polyAdd polyOne (polyNeg X))) 16 :=
    SquareBound.changeCap (by decide : ((2 : Q')*2)*sumBound 1 1 ≈ 16)
      (((SquareBound.one _).add P.neg).smul 2)
  exact ⟨supported_polyMul D.support D.support, by decide, D.certificate,
    (Certificate.constant _ 16 (by decide)).add (Certificate.square _ D.support)⟩

private theorem matched_edge_window (w : Q') (K width n : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (N width+N width) p) :
    H (N width+N width) (polyMul (edgeDensity w K width (terminalMessage w K width n)) p) ≈
      weightedMass w K width (polyMul (observedMessage w K width n 1 p)
        (terminalMessage w K width n)) := by
  simpa only [edgeDensity, endpointSource] using
    (terminalEdge_probe_pairing w K width n n hp)

private theorem matched_selected_pin (w : Q') (K width n i : Nat)
    (hi : i∈activeBlocks width) :
    H (N width+N width) (polyMul (edgeDensity w K width (terminalMessage w K width n))
      (selectedQuarticProbe width i)) ≈
    selectedInsertion w K width n i (quarticChordInsertion w K (scalarAt (N width+i) i)) := by
  let a := endpointSource w K width (terminalMessage w K width n)
  let L := liftBoundary (N width) a
  let W := productHeat (N width) w K (eraseIndex i (activeBlocks width))
  let Q := heatPrefix w K (scalarAt (N width+i) i)
  let p := selectedQuarticProbe width i
  have hk : RatPolyCoeffEqv (kineticWeight w K width) (polyMul Q W) := by
    rw [kineticWeight_eq_indexedProduct]
    have hp := polynomialProduct_perm (fun j => heatAt j (N width+j) w K) (select_perm i hi)
    have hh := (heatAt_symm i (N width+i) w K).mul_right W
    rw [heatAt_eq_prefix (N width+i) i w K] at hh
    exact hp.trans hh
  have he : RatPolyCoeffEqv
      (polyMul (edgeDensity w K width (terminalMessage w K width n)) p)
      (polyMul (polyMul W (polyMul a L)) (polyMul p Q)) :=
    (((hk.mul_right a).mul_right L).mul_right p).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 3)) (.var 4))
        (.mul (.mul (.var 1) (.mul (.var 2) (.var 3))) (.mul (.var 4) (.var 0)))
        (by decide) (fun
          | 0 => Q
          | 1 => W
          | 2 => a
          | 3 => L
          | _ => p))
  exact haar_of_coeff he

private theorem matched_window_pin {w : Q'} (hw0 : (0 : Q')<w) (hw1 : w<(1 : Q'))
    (K width : Nat) (hK : headCutoff w≤K) (n i : Nat) (hi : i∈activeBlocks width) :
    windowRatio hw0 hw1 K width hK n 1 n (selectedQuarticProbe width i) ≈
      selectedInsertion w K width n i (quarticChordInsertion w K (scalarAt (N width+i) i))*
        Q'.recipPos (oddMass w K width n) (oddMass_positive hw0 hw1 K width hK n) := by
  have hp := Q'.eqv_trans _ _ _
    (Q'.eqv_symm (matched_edge_window w K width n (selectedQuarticProbe width i)
      (selectedQuarticProbe_interval width i (activeBlocks_lt width i hi)).support))
    (matched_selected_pin w K width n i hi)
  unfold windowRatio massRatio oddMass
  exact Q'.mul_eqv_congr_right _ _ _ hp

private theorem matched_profile_bound {w epsilon : Q'}
    (hw0 : (0 : Q')<w) (hw1 : w<(1 : Q'))
    (hw : Q'.mkPos 16 17 (by decide)≤w) (he : (0 : Q')<epsilon)
    (K width : Nat) (hK : headCutoff w≤K) (n i : Nat)
    (hi : i∈activeBlocks width) (hcut : quarticCutoff w epsilon≤K) :
    windowRatio hw0 hw1 K width hK n 1 n (selectedQuarticProbe width i) ≤
      quarticProfileCoefficient w+epsilon := by
  let Z := oddMass w K width n
  let hz := oddMass_positive hw0 hw1 K width hK n
  let c := quarticProfileCoefficient w+epsilon
  have hb := Q'.mul_le_mul_of_nonneg_right _ _ (Q'.recipPos Z hz)
    (selectedChordInsertion_le_tolerance hw0 hw1 hw he K width n i hcut hi)
    (Q'.le_of_lt (Q'.recipPos_pos Z hz))
  have hc : (c*Z)*Q'.recipPos Z hz ≈ c :=
    Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_recipPos_eqv Z hz))
        (Q'.mul_one_eqv c))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (matched_window_pin hw0 hw1 K width hK n i hi))
    (Q'.le_trans' _ _ _ hb (Q'.le_of_eqv hc))

/-- Explicit actual-transfer depth cutoff. It depends on nome, width and
tolerance, but not K, n or the chosen link. It is not uniformly bounded
along a changing physical family. -/
def mixedQuarticDepthCutoff {w : Q'} (hw0 : (0 : Q')<w) (hw1 : w<(1 : Q'))
    (width : Nat) (epsilon : Q') : Nat :=
  geometricCutoff (mixRate hw0 hw1 width) 32 epsilon

/-- The original mixed window, with no partition-floor inverse or mixed
bilinear nome-order assertion. Every error and regulator remains explicit. -/
theorem mixed_quartic_window_bound {w epsilon : Q'}
    (hw0 : (0 : Q')<w) (hw1 : w<(1 : Q'))
    (hw : Q'.mkPos 16 17 (by decide)≤w) (he : (0 : Q')<epsilon)
    (K width : Nat) (hK : headCutoff w≤K) (n i : Nat)
    (hi : i∈activeBlocks width) (hcut : quarticCutoff w epsilon≤K) :
    windowRatio hw0 hw1 K width hK n 1 (n+1) (selectedQuarticProbe width i) ≤
      (quarticProfileCoefficient w+epsilon)+mixRate hw0 hw1 width^n*32 := by
  let I := selectedQuarticProbe_interval width i (activeBlocks_lt width i hi)
  have hb := (windowRatio_right_commonTail hw0 hw1 K width hK n 1 n (n+1) n
    (by simpa only [Nat.one_add, Nat.two_mul] using I) (by omega) (Nat.le_refl n)).1
  have hm := matched_profile_bound hw0 hw1 hw he K width hK n i hi hcut
  have h32 : (16 : Q')+16 ≈ 32 := by decide
  have hc : (quarticProfileCoefficient w+epsilon)+mixRate hw0 hw1 width^n*((16 : Q')+16) ≈
      (quarticProfileCoefficient w+epsilon)+mixRate hw0 hw1 width^n*32 :=
    Q'.add_eqv_congr_left _ _ _
    (Q'.mul_eqv_congr_left _ _ _ h32)
  exact Q'.le_trans' _ _ _ hb (Q'.le_trans' _ _ _
    (Q'.add_le_add_right _ _ _ hm) (Q'.le_of_eqv hc))

/-- Both prefix and depth onsets are computed. The final coefficient is
width/depth independent; only its actual-transfer depth onset depends on width. -/
theorem mixed_quartic_window_tolerance_bound {w epsilon : Q'}
    (hw0 : (0 : Q')<w) (hw1 : w<(1 : Q'))
    (hw : Q'.mkPos 16 17 (by decide)≤w) (he : (0 : Q')<epsilon)
    (K width : Nat) (hK : headCutoff w≤K) (n i : Nat)
    (hi : i∈activeBlocks width) (hcut : quarticCutoff w epsilon≤K)
    (hn : mixedQuarticDepthCutoff hw0 hw1 width epsilon≤n) :
    windowRatio hw0 hw1 K width hK n 1 (n+1) (selectedQuarticProbe width i) ≤
      quarticProfileCoefficient w+2*epsilon := by
  have hb := geometric_bound (mixRate_nonnegative hw0 hw1 width)
    (mixRate_lt_one hw0 hw1 width) (by decide : (0 : Q')≤32) he n hn
  have hc : (quarticProfileCoefficient w+epsilon)+epsilon ≈ quarticProfileCoefficient w+2*epsilon :=
    poly_identity_of_normal_eq (.add (.add (.var 0) (.var 1)) (.var 1))
      (.add (.var 0) (.mul (.const 2) (.var 1))) (by decide) (fun
        | 0 => quarticProfileCoefficient w
        | _ => epsilon)
  exact Q'.le_trans' _ _ _ (mixed_quartic_window_bound hw0 hw1 hw he K width hK n i hi hcut)
    (Q'.le_trans' _ _ _ (Q'.add_le_add_left _ _ _ hb) (Q'.le_of_eqv hc))

private theorem clear_ratio_bound (M Z b : Q') (hz : (0 : Q')<Z)
    (h : M*Q'.recipPos Z hz≤b) : M≤b*Z := by
  have hb := Q'.mul_le_mul_of_nonneg_right _ _ Z h (Q'.le_of_lt hz)
  have hc : (M*Q'.recipPos Z hz)*Z ≈ M :=
    Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv Z hz)))
        (Q'.mul_one_eqv M))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm hc)) hb

private theorem mixed_mass_from_window {w : Q'} (hw0 : (0 : Q')<w) (hw1 : w<(1 : Q'))
    (K width : Nat) (hK : headCutoff w≤K) (n i : Nat) (hi : i<N width) (b : Q')
    (hb : windowRatio hw0 hw1 K width hK n 1 (n+1) (selectedQuarticProbe width i)≤b) :
    H (N width+N width) (polyMul (mixedDensity w K width n) (selectedQuarticProbe width i))≤
      b*evenPartition w K width n := by
  let Z := weightedMass w K width (polyMul (terminalMessage w K width (n+1))
    (terminalMessage w K width (n+1)))
  let M := weightedMass w K width (polyMul
    (observedMessage w K width n 1 (selectedQuarticProbe width i))
    (terminalMessage w K width (n+1)))
  let hz := terminalPair_positive hw0 hw1 K width hK (n+1) (n+1)
  have hh : M*Q'.recipPos Z hz≤b := by
    simpa only [windowRatio, massRatio] using hb
  have hZ : Z ≈ evenPartition w K width n := by
    have h := evenPartition_middle_pin w K width n
    rw [terminalMessage_next w K width n] at h
    exact Q'.eqv_symm h
  have hp := mixedDensity_window_pairing w K width n
    (selectedQuarticProbe_interval width i hi).support
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hp) (Q'.le_trans' _ _ _
    (clear_ratio_bound M Z b hz hh)
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ hZ)))

/-- Literal mixed-depth quartic mass, normalized by the SAME even partition.
All original terminal sources and inactive coordinates are retained. -/
theorem mixed_quartic_mass_bound {w epsilon : Q'}
    (hw0 : (0 : Q')<w) (hw1 : w<(1 : Q'))
    (hw : Q'.mkPos 16 17 (by decide)≤w) (he : (0 : Q')<epsilon)
    (K width : Nat) (hK : headCutoff w≤K) (n i : Nat)
    (hi : i∈activeBlocks width) (hcut : quarticCutoff w epsilon≤K) :
    H (N width+N width) (polyMul (mixedDensity w K width n) (selectedQuarticProbe width i))≤
      ((quarticProfileCoefficient w+epsilon)+mixRate hw0 hw1 width^n*32)*
        evenPartition w K width n :=
  mixed_mass_from_window hw0 hw1 K width hK n i (activeBlocks_lt width i hi) _
    (mixed_quartic_window_bound hw0 hw1 hw he K width hK n i hi hcut)

/-- Computed all-later heat-prefix and depth cutoffs; no partition floor in
the coefficient and no equality with the complete filtered increment. -/
theorem mixed_quartic_mass_tolerance_bound {w epsilon : Q'}
    (hw0 : (0 : Q')<w) (hw1 : w<(1 : Q'))
    (hw : Q'.mkPos 16 17 (by decide)≤w) (he : (0 : Q')<epsilon)
    (K width : Nat) (hK : headCutoff w≤K) (n i : Nat)
    (hi : i∈activeBlocks width) (hcut : quarticCutoff w epsilon≤K)
    (hn : mixedQuarticDepthCutoff hw0 hw1 width epsilon≤n) :
    H (N width+N width) (polyMul (mixedDensity w K width n) (selectedQuarticProbe width i))≤
      (quarticProfileCoefficient w+2*epsilon)*evenPartition w K width n :=
  mixed_mass_from_window hw0 hw1 K width hK n i (activeBlocks_lt width i hi) _
    (mixed_quartic_window_tolerance_bound hw0 hw1 hw he K width hK n i hi hcut hn)

private theorem oriented_chord_pin {width : Nat} {e : OrientedBF4Link}
    (he : e.link∈baseLinks width) :
    HaarCarrierEqv (N width+N width)
      (polyQuaternionNorm (difference (orientedLink width e) (upperOriented width e)))
      (polySmul 2 (polyAdd polyOne (polyNeg
        (scalarAt (N width+(baseLinks width).idxOf e.link) ((baseLinks width).idxOf e.link))))) := by
  let i := (baseLinks width).idxOf e.link
  have hi := List.idxOf_lt_length_of_mem he
  have hl := haarNorm_coordinate (by omega : i<N width+N width)
  have hu := haarNorm_coordinate (by omega : N width+i<N width+N width)
  have hbase := norm_difference_character hl hu
  have hc : HaarCarrierEqv (N width+N width)
      (polyQuaternionNorm (difference (orientedLink width e) (upperOriented width e)))
      (defect (scalarAt (N width+i) i)) := by
    unfold orientedLink link upperOriented
    rw [if_pos he]
    split
    · exact (RatPolyCoeffEqv.haarCarrier (blocks := N width+N width)
        (norm_difference_conj (PolyQuaternion.coordinateVariable i)
          (PolyQuaternion.coordinateVariable (N width+i)))).trans hbase
    · exact hbase
  have hr : RatPolyCoeffEqv (defect (scalarAt (N width+i) i))
      (polySmul 2 (polyAdd polyOne (polyNeg (scalarAt (N width+i) i)))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.const 2) (.neg (.mul (.const 2) (.var 0))))
      (.mul (.const 2) (.add (.const 1) (.neg (.var 0)))) (by decide)
      (fun _ => scalarAt (N width+i) i)
  exact hc.trans (RatPolyCoeffEqv.haarCarrier hr)

private theorem oriented_fourth_pin (w : Q') (K width n : Nat) (e : OrientedBF4Link)
    (he : e.link∈baseLinks width) :
    let D := polyQuaternionNorm (difference (orientedLink width e) (upperOriented width e))
    H (N width+N width) (polyMul (mixedDensity w K width n) (polyMul D D)) ≈
      H (N width+N width) (polyMul (mixedDensity w K width n)
        (selectedQuarticProbe width ((baseLinks width).idxOf e.link))) := by
  have hc := oriented_chord_pin he
  exact haar_of_carrier (HaarCarrierEqv.mul_left (mixedDensity w K width n)
    (HaarCarrierEqv.mul hc hc))

/-- Original physical oriented-link fourth moment, with explicit depth error. -/
theorem oriented_link_fourth_bound {w epsilon : Q'}
    (hw0 : (0 : Q')<w) (hw1 : w<(1 : Q'))
    (hw : Q'.mkPos 16 17 (by decide)≤w) (heps : (0 : Q')<epsilon)
    (K width : Nat) (hK : headCutoff w≤K) (n : Nat) (e : OrientedBF4Link)
    (he : e.link∈baseLinks width) (hi : (baseLinks width).idxOf e.link∈activeBlocks width)
    (hcut : quarticCutoff w epsilon≤K) :
    let D := polyQuaternionNorm (difference (orientedLink width e) (upperOriented width e))
    H (N width+N width) (polyMul (mixedDensity w K width n) (polyMul D D))≤
      ((quarticProfileCoefficient w+epsilon)+mixRate hw0 hw1 width^n*32)*
        evenPartition w K width n :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (oriented_fourth_pin w K width n e he))
    (mixed_quartic_mass_bound hw0 hw1 hw heps K width hK n _ hi hcut)

/-- The same physical fourth moment under both computed all-later cutoffs. -/
theorem oriented_link_fourth_tolerance_bound {w epsilon : Q'}
    (hw0 : (0 : Q')<w) (hw1 : w<(1 : Q'))
    (hw : Q'.mkPos 16 17 (by decide)≤w) (heps : (0 : Q')<epsilon)
    (K width : Nat) (hK : headCutoff w≤K) (n : Nat) (e : OrientedBF4Link)
    (he : e.link∈baseLinks width) (hi : (baseLinks width).idxOf e.link∈activeBlocks width)
    (hcut : quarticCutoff w epsilon≤K)
    (hn : mixedQuarticDepthCutoff hw0 hw1 width epsilon≤n) :
    let D := polyQuaternionNorm (difference (orientedLink width e) (upperOriented width e))
    H (N width+N width) (polyMul (mixedDensity w K width n) (polyMul D D))≤
      (quarticProfileCoefficient w+2*epsilon)*evenPartition w K width n :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (oriented_fourth_pin w K width n e he))
    (mixed_quartic_mass_tolerance_bound hw0 hw1 hw heps K width hK n _ hi hcut hn)

#print axioms selectedQuarticProbe
#print axioms selectedQuarticProbe_interval
#print axioms mixedQuarticDepthCutoff
#print axioms mixed_quartic_window_bound
#print axioms mixed_quartic_window_tolerance_bound
#print axioms mixed_quartic_mass_bound
#print axioms mixed_quartic_mass_tolerance_bound
#print axioms oriented_link_fourth_bound
#print axioms oriented_link_fourth_tolerance_bound

end YMGap.Continuum.BF4ExactSlabFixedSpatialMixedDepthQuarticInsertion
