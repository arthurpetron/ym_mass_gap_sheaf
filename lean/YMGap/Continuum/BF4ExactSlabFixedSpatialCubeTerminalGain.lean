/-
# Actual OWN-centered relative gain at every terminal depth

At fixed nome 1/16 and width two, the constructed original terminal
overlap and even-partition bounds give S/E >= 2^(-128), at every depth
and every cutoff satisfying both original guards. S is the square of the
EXISTING OWN-centered message b=T(g_n(F-c_n)), with the full original
spatial weight. The literal original gain at reference w^18 is at least
S/4 and is strictly positive. No S/E or favorable gain premise is supplied.

All-insertion source transport is used before fringe action peeling;
locality is proved only for the cube representative, never presumed for
the raw original message. Haar amplitude and odd/even partitions remain
distinct. This fixed-width, fixed-nome bent-loop result does not supply
growing-square or changing-family survival, nor continuum Yang--Mills.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalOverlap
import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalEvenBudget
import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentComplement
import YMGap.Continuum.BF4ExactSlabFixedSpatialOwnGainYoungBudget
import YMGap.Continuum.QuaternionHaarIntervalSecondMoment

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalGain

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (qpow poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder
  (spatialCertificate plaquette_supported plaquette_unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep transferStep_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferPositive (transferStep_eq_productMap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActiveTransfer (kineticMap_symmetric)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActiveSpatialWeight (spatialWeight_haar_active)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow
  (fringeBlocks_lt fringeBlocks_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks activeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported terminalMessage_certificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredCommutatorGain (centeredMessage commutatorGain)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredNoiseDrift
  (evenPartition evenPartition_middle_pin evenPartition_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentFusion (firstFaceTrace)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeBentComplement (first_face_square_haar)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeSmallFundamentalCap (smallNome smallNome_pos)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeAllCutoffInterval (cubeHalfCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalTransfer
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalOwnMean
  (originalOddMean originalOddMean_abs_le)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalOverlap
  (terminalTestRate originalOwn_tested_floor centeredInterval)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalEvenBudget
  (evenPartition_le_terminal_mass_square)
open YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalTerminalShape
  (original_haar_mass_pin original_haar_mass_positive)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionProductHeatMarginals (productMap productMap_supported)
open YMGap.Continuum.SU2QuaternionProductHeatPositiveOrder (haar_order)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted shifted_supported)
open YMGap.Continuum.QuaternionHaarSharpCharacterInterval (sharpCharacterInterval)
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.QuaternionHaarFamilySquare (haar_weighted_add)
open YMGap.Continuum.QuaternionHaarWordDifference (weighted_order weighted_scale)
open YMGap.Continuum.QuaternionHaarRelativePredictionFloor (weighted_square_young)

local notation "N" => List.length (baseLinks 2)
local notation:max "H" p:arg => quaternionHaar N p
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks spatialWeight transferStep weightedMass terminalMessage
  cubeWeight cubeTransfer cubeTerminal bentObservable centeredMessage commutatorGain
  originalOddMean evenPartition

def relativeSquareFloor : Q' := Q'.mkPos 1 (2^128) (by decide)

/-- The original filtered square; c is not replaced by a bare Haar center. -/
def originalSquare (K n : Nat) (c : Q') : Q' :=
  let b := centeredMessage smallNome K 2 n bentObservable c
  weightedMass smallNome K 2 (polyMul b b)

def originalYoungCost (K n : Nat) (c : Q') : Q' :=
  let u := polyMul (transferStep smallNome K 2 (terminalMessage smallNome K 2 n))
    (shifted bentObservable c)
  weightedMass smallNome K 2 (polyMul u u)

private theorem message_supported (K n : Nat) (c : Q') :
    SupportedQuaternionBlocks N (centeredMessage smallNome K 2 n bentObservable c) := by
  unfold centeredMessage
  exact transferStep_supported smallNome K 2
    (supported_polyMul (terminalMessage_supported smallNome K 2 n)
      (shifted_supported bentObservable_supported c))

private theorem shifted_independent (c : Q') (i : Nat) (hi : i < N) (hn : i ∉ cubeIndices) :
    QuaternionBlockIndependent i (shifted bentObservable c) := by
  unfold shifted
  exact quaternionBlockIndependent_polyAdd
    (quaternionBlockIndependent_polySmul 1 (bentObservable_cube_independent i hi hn))
    (quaternionBlockIndependent_polySmul (-c) (quaternionBlockIndependent_polyOne i))

private def reducedMessage (K n : Nat) (c : Q') : RatPoly :=
  cubeTransfer smallNome K (polyMul (cubeTerminal K n) (shifted bentObservable c))

private theorem reduced_supported (K n : Nat) (c : Q') :
    SupportedQuaternionBlocks N (reducedMessage K n c) :=
  cubeTransfer_supported smallNome K
    (supported_polyMul (cubeTerminal_supported K n) (shifted_supported bentObservable_supported c))

private theorem reduced_independent (K n : Nat) (c : Q') (i : Nat)
    (hi : i < N) (hn : i ∉ cubeIndices) : QuaternionBlockIndependent i (reducedMessage K n c) :=
  cubeTransfer_independent smallNome K i hi hn
    (supported_polyMul (cubeTerminal_supported K n) (shifted_supported bentObservable_supported c))

private theorem transfer_haar_congr (K : Nat) {f g : RatPoly}
    (hf : SupportedQuaternionBlocks N f) (hg : SupportedQuaternionBlocks N g)
    (hfg : SupportedHaarEqv N f g) :
    SupportedHaarEqv N (transferStep smallNome K 2 f) (transferStep smallNome K 2 g) := by
  intro p hp
  let V := spatialWeight smallNome K 2
  let Pp := productMap N smallNome K (activeBlocks 2) p
  have hV := spatialWeight_supported smallNome K 2
  have hPp := productMap_supported N smallNome K (activeBlocks 2) (activeBlocks_lt 2) hp
  have hleft : H (polyMul p (transferStep smallNome K 2 f)) ≈ H (polyMul (polyMul V f) Pp) := by
    rw [transferStep_eq_productMap]
    exact kineticMap_symmetric smallNome K 2 (supported_polyMul hV hf) hp
  have hright : H (polyMul p (transferStep smallNome K 2 g)) ≈ H (polyMul (polyMul V g) Pp) := by
    rw [transferStep_eq_productMap]
    exact kineticMap_symmetric smallNome K 2 (supported_polyMul hV hg) hp
  have hpolyF : RatPolyCoeffEqv (polyMul (polyMul V f) Pp) (polyMul (polyMul V Pp) f) :=
    (RatPolyCoeffEqv.mul_assoc V f Pp).trans
      (((RatPolyCoeffEqv.mul_comm f Pp).mul_left V).trans (RatPolyCoeffEqv.mul_assoc V Pp f).symm)
  have hpolyG : RatPolyCoeffEqv (polyMul (polyMul V g) Pp) (polyMul (polyMul V Pp) g) :=
    (RatPolyCoeffEqv.mul_assoc V g Pp).trans
      (((RatPolyCoeffEqv.mul_comm g Pp).mul_left V).trans (RatPolyCoeffEqv.mul_assoc V Pp g).symm)
  exact Q'.eqv_trans _ _ _ hleft (Q'.eqv_trans _ _ _ (haar_of_coeff (blocks := N) hpolyF)
    (Q'.eqv_trans _ _ _ (hfg (polyMul V Pp) (supported_polyMul hV hPp))
      (Q'.eqv_trans _ _ _ (haar_of_coeff (blocks := N) hpolyG.symm) (Q'.eqv_symm hright))))

/-- The raw original b is transported only under all supported insertions. -/
theorem original_centeredMessage_cube_pin (K n : Nat) (c : Q') :
    SupportedHaarEqv N (centeredMessage smallNome K 2 n bentObservable c) (reducedMessage K n c) := by
  let psi := shifted bentObservable c
  have hpsi := shifted_supported bentObservable_supported c
  have hinput := (terminalMessage_cubeTerminal K n).mul (SupportedHaarEqv.refl N psi)
    hpsi (cubeTerminal_supported K n)
  have hstep := transfer_haar_congr K
    (supported_polyMul (terminalMessage_supported smallNome K 2 n) hpsi)
    (supported_polyMul (cubeTerminal_supported K n) hpsi) hinput
  have hc := original_transfer_cube smallNome K
    (supported_polyMul (cubeTerminal_supported K n) hpsi)
    (fun i hi hn => quaternionBlockIndependent_polyMul (cubeTerminal_independent K n i hi hn)
      (shifted_independent c i hi hn))
  unfold centeredMessage reducedMessage
  exact hstep.trans hc

/-- Full-action square transport followed by reverse tested source recoding.
The final integrand still contains the ORIGINAL centered message. -/
theorem originalSquare_cube_pin (K n : Nat) (c : Q') :
    originalSquare K n c ≈ H (polyMul (cubeWeight smallNome K)
      (polyMul (centeredMessage smallNome K 2 n bentObservable c)
        (centeredMessage smallNome K 2 n bentObservable c))) := by
  let b := centeredMessage smallNome K 2 n bentObservable c
  let r := reducedMessage K n c
  have hb := message_supported K n c
  have hr := reduced_supported K n c
  have hpair := (original_centeredMessage_cube_pin K n c).mul
    (original_centeredMessage_cube_pin K n c) hb hr
  have h0 := hpair (spatialWeight smallNome K 2) (spatialWeight_supported smallNome K 2)
  have h1 := spatialWeight_haar_active smallNome K 2 (polyMul r r) (supported_polyMul hr hr)
    (fun i hf => quaternionBlockIndependent_polyMul
      (reduced_independent K n c i (fringeBlocks_lt 2 i hf)
        (fun hc => ((fringeBlocks_mem_iff 2 i).mp hf).2 (cubeIndices_active i hc)))
      (reduced_independent K n c i (fringeBlocks_lt 2 i hf)
        (fun hc => ((fringeBlocks_mem_iff 2 i).mp hf).2 (cubeIndices_active i hc))))
  have h2 := haar_of_coeff (blocks := N) ((activeSpatialWeight_cube smallNome K).mul_right (polyMul r r))
  have hV : SupportedQuaternionBlocks N (cubeWeight smallNome K) := by
    unfold cubeWeight
    exact YMGap.Continuum.BF4ExactSlabFixedSpatialFaceIndependence.heatProduct_supported smallNome K 2 cubeFaces
  have h3 := hpair (cubeWeight smallNome K) hV
  unfold originalSquare weightedMass
  exact Q'.eqv_trans _ _ _ h0 (Q'.eqv_trans _ _ _ h1
    (Q'.eqv_trans _ _ _ h2 (Q'.eqv_symm h3)))

private theorem projection_square_bound (K n : Nat) (c : Q') :
    H (polyMul firstFaceTrace (centeredMessage smallNome K 2 n bentObservable c)) *
      H (polyMul firstFaceTrace (centeredMessage smallNome K 2 n bentObservable c)) ≤
    H (polyMul (centeredMessage smallNome K 2 n bentObservable c)
      (centeredMessage smallNome K 2 n bentObservable c)) := by
  have hP : SupportedQuaternionBlocks N firstFaceTrace :=
    (sharpCharacterInterval (SquareBound.scalar
      (plaquette_supported 2 N (Nat.le_refl _) ((0,0,0,0),.p01))
      (plaquette_unit 2 N (Nat.le_refl _) ((0,0,0,0),.p01))) 1).support
  let b := centeredMessage smallNome K 2 n bentObservable c
  have h := weighted_cauchySchwarz N polyOne firstFaceTrace b (Certificate.one N) hP
    (message_supported K n c)
  have hx : weightedPair N polyOne firstFaceTrace b ≈ H (polyMul firstFaceTrace b) :=
    haar_of_coeff (blocks := N) (RatPolyCoeffEqv.mul_one _)
  have hy : weightedPair N polyOne firstFaceTrace firstFaceTrace ≈ 1 :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (blocks := N) (RatPolyCoeffEqv.mul_one _)) first_face_square_haar
  have hz : weightedPair N polyOne b b ≈ H (polyMul b b) :=
    haar_of_coeff (blocks := N) (RatPolyCoeffEqv.mul_one _)
  have hl := Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hx) (Q'.mul_eqv_congr_left _ _ _ hx)
  have hr := Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hy)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hz) (Q'.one_mul_eqv _))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hl) (Q'.le_trans' _ _ _ h (Q'.le_of_eqv hr))

private theorem square_projection_lower (K : Nat) (hK : 1 ≤ K) (n : Nat) (c : Q') :
    HalfPow.half*(H (polyMul firstFaceTrace (centeredMessage smallNome K 2 n bentObservable c)) *
      H (polyMul firstFaceTrace (centeredMessage smallNome K 2 n bentObservable c))) ≤
    originalSquare K n c := by
  let b := centeredMessage smallNome K 2 n bentObservable c
  have hraw := Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half (projection_square_bound K n c)
    HalfPow.half_nonneg
  have hfloor := haar_order (cubeHalfCertificate K hK) (Certificate.square b (message_supported K n c))
  have hcap : H (polyMul (cap HalfPow.half) (polyMul b b)) ≈ HalfPow.half*H (polyMul b b) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (blocks := N) (cap_mul_left HalfPow.half _))
      (quaternionHaar_polySmul N HalfPow.half _)
  exact Q'.le_trans' _ _ _ hraw (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hcap)
    (Q'.le_trans' _ _ _ hfloor (Q'.ge_of_eqv (originalSquare_cube_pin K n c))))

attribute [local irreducible] originalSquare originalYoungCost

/-- Actual square floor relative to the ORIGINAL positive Haar amplitude. -/
theorem originalOwn_square_floor (K : Nat) (hK : 1 ≤ K)
    (hhead : headCutoff smallNome ≤ K) (n : Nat) :
    (HalfPow.half*(terminalTestRate*terminalTestRate))*
      (H (terminalMessage smallNome K 2 n)*H (terminalMessage smallNome K 2 n)) ≤
    originalSquare K n (originalOddMean K hK hhead n) := by
  let a := H (terminalMessage smallNome K 2 n)
  let z := terminalTestRate*a
  let c := originalOddMean K hK hhead n
  let p := H (polyMul firstFaceTrace (centeredMessage smallNome K 2 n bentObservable c))
  have hz : (0 : Q') ≤ z := Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ terminalTestRate)
    (Q'.le_of_lt (original_haar_mass_positive K hK hhead n))
  have hzp : z ≤ p := originalOwn_tested_floor K hK hhead n
  have hp : (0 : Q') ≤ p := Q'.le_trans' _ _ _ hz hzp
  have hsq : z*z ≤ p*p := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ z hzp hz)
    (Q'.mul_le_mul_of_nonneg_right _ _ p hzp hp)
  have he : (HalfPow.half*(terminalTestRate*terminalTestRate))*(a*a) ≈ HalfPow.half*(z*z) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2)))
      (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 2))))
      (by decide) (fun | 0 => HalfPow.half | 1 => terminalTestRate | _ => a)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half hsq HalfPow.half_nonneg)
      (square_projection_lower K hK n c))

/-- S >= 2^(-128) E, with the actual EVEN partition unchanged. -/
theorem originalOwn_relative_square_floor (K : Nat) (hK : 1 ≤ K)
    (hhead : headCutoff smallNome ≤ K) (n : Nat) :
    relativeSquareFloor*evenPartition smallNome K 2 n ≤
      originalSquare K n (originalOddMean K hK hhead n) := by
  let a := H (cubeTerminal K n)
  let o := H (terminalMessage smallNome K 2 n)
  have hE := Q'.mul_le_mul_of_nonneg_left _ _ relativeSquareFloor
    (evenPartition_le_terminal_mass_square K hK hhead n) (by decide)
  have hmass := original_haar_mass_pin K n
  have hsquare : a*a ≈ o*o := Q'.eqv_symm (Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ hmass) (Q'.mul_eqv_congr_left _ _ _ hmass))
  have he : relativeSquareFloor*(2*(a*a)) ≈
      (HalfPow.half*(terminalTestRate*terminalTestRate))*(o*o) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
        (by decide : relativeSquareFloor*2 ≈ HalfPow.half*(terminalTestRate*terminalTestRate)))
        (Q'.mul_eqv_congr_left _ _ _ hsquare))
  exact Q'.le_trans' _ _ _ hE (Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
    (originalOwn_square_floor K hK hhead n))

theorem originalOwn_normalized_square_floor (K : Nat) (hK : 1 ≤ K)
    (hhead : headCutoff smallNome ≤ K) (n : Nat) :
    relativeSquareFloor ≤ Q'.divPos (originalSquare K n (originalOddMean K hK hhead n))
      (evenPartition smallNome K 2 n) (evenPartition_positive smallNome_pos (by decide) K 2 hhead n) :=
  Q'.le_divPos_of_mul_le _ _ (evenPartition_positive smallNome_pos (by decide) K 2 hhead n)
    (originalOwn_relative_square_floor K hK hhead n)

private theorem endpoint_supported (K n : Nat) (c : Q') :
    SupportedQuaternionBlocks N (polyMul
      (transferStep smallNome K 2 (terminalMessage smallNome K 2 n)) (shifted bentObservable c)) :=
  supported_polyMul (transferStep_supported smallNome K 2 (terminalMessage_supported smallNome K 2 n))
    (shifted_supported bentObservable_supported c)

/-- A constructed cap on the actual full-action endpoint cost. -/
theorem originalYoungCost_le_sixteen_evenPartition (K : Nat)
    (hhead : headCutoff smallNome ≤ K) (n : Nat) (c : Q')
    (hc : Q'.abs c ≤ Q'.mkPos 1 4 (by decide)) :
    originalYoungCost K n c ≤ 16*evenPartition smallNome K 2 n := by
  let V := spatialWeight smallNome K 2
  let A := transferStep smallNome K 2 (terminalMessage smallNome K 2 n)
  let psi := shifted bentObservable c
  let R := polyMul V (polyMul A A)
  have hA := transferStep_supported smallNome K 2 (terminalMessage_supported smallNome K 2 n)
  have P := QuaternionHaarIntervalSecondMoment.Interval.squareBound
    ((centeredInterval c hc).weaken (by decide : Q'.mkPos 9 4 (by decide) ≤ (4 : Q')))
  have h := weighted_order
    ((spatialCertificate smallNome_pos (by decide) K 2 N (Nat.le_refl _) hhead).mul
      (Certificate.square A hA)) P.certificate
  have hl : RatPolyCoeffEqv (polyMul R (polyMul psi psi))
      (polyMul V (polyMul (polyMul A psi) (polyMul A psi))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2)))
      (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 2))))
      (by decide) (fun | 0 => V | 1 => A | _ => psi)
  have hr : H (polyMul R (cap (4*4 : Q'))) ≈ (4*4)*H R :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (blocks := N)
      ((RatPolyCoeffEqv.mul_comm R _).trans (cap_mul_left (4*4) R)))
      (quaternionHaar_polySmul N (4*4) R)
  have hbound : H (polyMul V (polyMul (polyMul A psi) (polyMul A psi))) ≤ 16*H R :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (haar_of_coeff (blocks := N) hl))
      (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hr
        (Q'.mul_eqv_congr_right _ _ _ (by decide : (4 : Q')*4 ≈ (16 : Q'))))))
  have he := evenPartition_middle_pin smallNome K 2 n
  unfold weightedMass at he
  unfold originalYoungCost weightedMass
  exact Q'.le_trans' _ _ _ hbound (Q'.le_of_eqv
    (Q'.mul_eqv_congr_left 16 _ _ (Q'.eqv_symm he)))

private theorem young_collect (s q j g a : Q') (h : 2*a*j ≤ (a*a)*q+s)
    (hg : g ≈ s+(-a)*j) : s-(a*a)*q ≤ 2*g := by
  have he : ((a*a)*q+s)-(2*a*j) ≈ 2*(s+(-a)*j)-(s-(a*a)*q) :=
    poly_identity_of_normal_eq
      (.add (.add (.mul (.mul (.var 4) (.var 4)) (.var 1)) (.var 0))
        (.neg (.mul (.mul (.const 2) (.var 4)) (.var 2))))
      (.add (.mul (.const 2) (.add (.var 0) (.mul (.neg (.var 4)) (.var 2))))
        (.neg (.add (.var 0) (.neg (.mul (.mul (.var 4) (.var 4)) (.var 1))))))
      (by decide) (fun | 0 => s | 1 => q | 2 => j | _ => a)
  have ht := Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_left 2 _ _ (Q'.eqv_symm hg)) (Q'.eqv_refl (-(s-(a*a)*q)))
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ (Q'.sub_nonneg_of_le h)
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ he ht)))

/-- Original weighted Young square, with arbitrary signed reference a. -/
theorem original_gain_young_lower (K : Nat) (hhead : headCutoff smallNome ≤ K)
    (n : Nat) (c a : Q') :
    originalSquare K n c-(a*a)*originalYoungCost K n c ≤
      2*commutatorGain smallNome K 2 n bentObservable c a := by
  let V := spatialWeight smallNome K 2
  let b := centeredMessage smallNome K 2 n bentObservable c
  let u := polyMul (transferStep smallNome K 2 (terminalMessage smallNome K 2 n))
    (shifted bentObservable c)
  let s := H (polyMul V (polyMul b b))
  let q := H (polyMul V (polyMul u u))
  let j := H (polyMul V (polyMul u b))
  have hy : 2*a*j ≤ (a*a)*q+s := weighted_square_young
    (spatialCertificate smallNome_pos (by decide) K 2 N (Nat.le_refl _) hhead)
    (endpoint_supported K n c) (message_supported K n c) a
  have hp : RatPolyCoeffEqv (polyMul b (polyAdd b (polySmul (-a) u)))
      (polyAdd (polyMul b b) (polySmul (-a) (polyMul u b))) :=
    (RatPolyCoeffEqv.mul_add_right b b _).trans ((RatPolyCoeffEqv.refl _).add
      ((RatPolyCoeffEqv.polyMul_smul_right (-a) b u).trans
        ((RatPolyCoeffEqv.mul_comm b u).smul (-a))))
  have hg : commutatorGain smallNome K 2 n bentObservable c a ≈ s+(-a)*j := by
    unfold commutatorGain weightedMass
    exact Q'.eqv_trans _ _ _ (haar_of_coeff (blocks := N) (hp.mul_left V))
      (Q'.eqv_trans _ _ _ (haar_weighted_add N V _ _)
        (Q'.add_eqv_congr' (Q'.eqv_refl s) (weighted_scale N V (polyMul u b) (-a))))
  have h := young_collect s q j (commutatorGain smallNome K 2 n bentObservable c a) a hy hg
  unfold originalSquare originalYoungCost weightedMass
  exact h

/-- The formerly unpaid S/E floor is supplied here, not a hypothesis. -/
theorem originalOwn_gain_relative_lower (K : Nat) (hK : 1 ≤ K)
    (hhead : headCutoff smallNome ≤ K) (n : Nat) :
    (Q'.mkPos 1 4 (by decide))*originalSquare K n (originalOddMean K hK hhead n) ≤
      commutatorGain smallNome K 2 n bentObservable (originalOddMean K hK hhead n) (qpow smallNome 18) := by
  let c := originalOddMean K hK hhead n
  let S := originalSquare K n c
  let Q := originalYoungCost K n c
  let E := evenPartition smallNome K 2 n
  let G := commutatorGain smallNome K 2 n bentObservable c (qpow smallNome 18)
  let a := qpow smallNome 18
  have hE : (0 : Q') ≤ E := Q'.le_of_lt (evenPartition_positive smallNome_pos (by decide) K 2 hhead n)
  have hcost := originalYoungCost_le_sixteen_evenPartition K hhead n c
    (originalOddMean_abs_le K hK hhead n)
  have hS : relativeSquareFloor*E ≤ S := originalOwn_relative_square_floor K hK hhead n
  have hscalar : (a*a)*16 ≤ HalfPow.half*relativeSquareFloor := by decide
  have hQ : (a*a)*Q ≤ HalfPow.half*S :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ (a*a) hcost
      (SumOfSquares.q_mul_self_nonneg a))
      (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_assoc_eqv _ _ _))
        (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ E hscalar hE)
          (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _))
            (Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half hS HalfPow.half_nonneg))))
  have hid : HalfPow.half*S ≈ S+ -(HalfPow.half*S) :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq (.var 0)
      (.add (.add (.var 0) (.var 0)) (.neg (.var 0))) (by decide) (fun _ => HalfPow.half*S))
      (Q'.add_eqv_congr' (ExpNeg.two_halves S) (Q'.eqv_refl _))
  have hhalf : HalfPow.half*S ≤ 2*G := Q'.le_trans' _ _ _ (Q'.le_of_eqv hid)
    (Q'.le_trans' _ _ _ (Q'.add_le_add_left S _ _ (Q'.neg_le_neg hQ))
      (original_gain_young_lower K hhead n c a))
  have hs := Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half hhalf HalfPow.half_nonneg
  have hl : HalfPow.half*(HalfPow.half*S) ≈ (Q'.mkPos 1 4 (by decide))*S :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.mul_eqv_congr_right _ _ S (by decide : HalfPow.half*HalfPow.half ≈ Q'.mkPos 1 4 (by decide)))
  have hr : HalfPow.half*(2*G) ≈ G :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ G (by decide : HalfPow.half*2 ≈ (1 : Q')))
        (Q'.one_mul_eqv G))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hl) (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv hr))

theorem originalOwn_gain_positive (K : Nat) (hK : 1 ≤ K)
    (hhead : headCutoff smallNome ≤ K) (n : Nat) :
    (0 : Q') < commutatorGain smallNome K 2 n bentObservable
      (originalOddMean K hK hhead n) (qpow smallNome 18) := by
  have hS : (0 : Q') < originalSquare K n (originalOddMean K hK hhead n) :=
    HeatKernelRGStep.lt_of_lt_of_le
      (Q'.mul_pos (by decide : (0 : Q') < HalfPow.half*(terminalTestRate*terminalTestRate))
        (Q'.mul_pos (original_haar_mass_positive K hK hhead n)
          (original_haar_mass_positive K hK hhead n))) (originalOwn_square_floor K hK hhead n)
  exact HeatKernelRGStep.lt_of_lt_of_le
    (Q'.mul_pos (by decide : (0 : Q') < Q'.mkPos 1 4 (by decide)) hS)
    (originalOwn_gain_relative_lower K hK hhead n)

theorem originalOwn_normalized_gain_floor (K : Nat) (hK : 1 ≤ K)
    (hhead : headCutoff smallNome ≤ K) (n : Nat) :
    (Q'.mkPos 1 4 (by decide))*relativeSquareFloor ≤ Q'.divPos
      (commutatorGain smallNome K 2 n bentObservable (originalOddMean K hK hhead n) (qpow smallNome 18))
      (evenPartition smallNome K 2 n) (evenPartition_positive smallNome_pos (by decide) K 2 hhead n) := by
  have hs := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.mkPos 1 4 (by decide))
    (originalOwn_relative_square_floor K hK hhead n) (by decide)
  have hcleared : ((Q'.mkPos 1 4 (by decide))*relativeSquareFloor)*evenPartition smallNome K 2 n ≤
      commutatorGain smallNome K 2 n bentObservable (originalOddMean K hK hhead n) (qpow smallNome 18) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _))
      (Q'.le_trans' _ _ _ hs (originalOwn_gain_relative_lower K hK hhead n))
  exact Q'.le_divPos_of_mul_le _ _ (evenPartition_positive smallNome_pos (by decide) K 2 hhead n) hcleared

end YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalGain

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalGain.relativeSquareFloor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalGain.originalSquare
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalGain.originalYoungCost
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalGain.original_centeredMessage_cube_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalGain.originalSquare_cube_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalGain.originalOwn_square_floor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalGain.originalOwn_relative_square_floor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalGain.originalOwn_normalized_square_floor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalGain.originalYoungCost_le_sixteen_evenPartition
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalGain.original_gain_young_lower
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalGain.originalOwn_gain_relative_lower
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalGain.originalOwn_gain_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalGain.originalOwn_normalized_gain_floor
