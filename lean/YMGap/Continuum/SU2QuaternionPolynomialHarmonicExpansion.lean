/-
# Actual finite harmonic expansion and original heat pairing

An arbitrary supported signed polynomial is padded only inside its declared
carrier, split by exact head degree, and constructively Fischer-decomposed.
Radius factors disappear only under the proved sphere/Haar relation. The
resulting computed finite list is consumed by the original heat packet.
No input harmonicity or decomposition certificate is assumed. This is an
exact finite formula, not a cutoff-uniform estimate on a changing source.
-/

import YMGap.Continuum.SU2QuaternionFischerDecomposition
import YMGap.Continuum.SU2QuaternionHeadHomogeneousComponents
import YMGap.Continuum.SU2QuaternionSelectedHarmonicHeatTransmission
import YMGap.Continuum.QuaternionHaarAngularCarrier

namespace YMGap.Continuum.SU2QuaternionPolynomialHarmonicExpansion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionTranslationCoordinateCoefficients
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.SU2QuaternionFischerRadial
open YMGap.Continuum.SU2QuaternionFischerDecomposition
open YMGap.Continuum.SU2QuaternionHeadHomogeneousComponents
open YMGap.Continuum.SU2QuaternionRelativeCharacterSelection
open YMGap.Continuum.SU2QuaternionRelativeHeatTransmission
open YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct
open YMGap.Continuum.SU2QuaternionHarmonicHeatInsertion
open YMGap.Continuum.RGTransport (qpow)

local infix:50 " ≈ " => Q'.eqv

private theorem sumValues_append {blocks : Nat} : ∀ xs ys : List (Mode blocks),
    sumValues (xs ++ ys) = polyAdd (sumValues xs) (sumValues ys)
  | [], _ => rfl
  | x::xs, ys => by
      simp only [List.cons_append, sumValues, sumValues_append xs ys, polyAdd, List.append_assoc]

def modesOfDegrees (blocks : Nat) (hb : 0 < blocks) (p : RatPoly)
    (hs : SupportedQuaternionBlocks blocks p) (hp : HeadPadded p) : List Nat → List (Mode blocks)
  | [] => []
  | n::ns =>
      (decomposeHomogeneous blocks hb n (headComponent n p) (headComponent_degree n p)
        (headComponent_supported hs) (headComponent_min_length hp)).modes ++
      modesOfDegrees blocks hb p hs hp ns

theorem modesOfDegrees_reassembly (blocks : Nat) (hb : 0 < blocks) (p : RatPoly)
    (hs : SupportedQuaternionBlocks blocks p) (hp : HeadPadded p) : ∀ ns,
    RatPolyCoeffEqv (sumValues (modesOfDegrees blocks hb p hs hp ns))
      (polySum (ns.map fun n => headComponent n p))
  | [] => RatPolyCoeffEqv.refl _
  | n::ns => by
      simp only [modesOfDegrees, sumValues_append, List.map_cons, polySum]
      exact (decomposeHomogeneous blocks hb n (headComponent n p) (headComponent_degree n p)
        (headComponent_supported hs) (headComponent_min_length hp)).reassembly.add
          (modesOfDegrees_reassembly blocks hb p hs hp ns)

theorem modesOfDegrees_degree_bound (blocks : Nat) (hb : 0 < blocks) (p : RatPoly)
    (hs : SupportedQuaternionBlocks blocks p) (hp : HeadPadded p) (bound : Nat) : ∀ ns,
    (∀ n, n ∈ ns → n ≤ bound) →
    ∀ m, m ∈ modesOfDegrees blocks hb p hs hp ns → m.degree ≤ bound
  | [], _, _, hm => by contradiction
  | n::ns, hn, m, hm => by
      rcases List.mem_append.mp hm with hm | hm
      · have hd := (decomposeHomogeneous blocks hb n (headComponent n p)
          (headComponent_degree n p) (headComponent_supported hs)
          (headComponent_min_length hp)).degrees m hm
        have hbound := hn n List.mem_cons_self
        unfold Mode.totalDegree at hd
        omega
      · exact modesOfDegrees_degree_bound blocks hb p hs hp bound ns
          (fun k hk => hn k (List.mem_cons_of_mem n hk)) m hm

/-- Padding is the existing finite identity reindexing, not a truncation license. -/
def paddedInput (blocks : Nat) (p : RatPoly) : RatPoly :=
  reindexQuaternionPolynomial (identityQuaternionBlockInvolution blocks) p

theorem paddedInput_supported (blocks : Nat) (p : RatPoly) :
    SupportedQuaternionBlocks blocks (paddedInput blocks p) :=
  reindex_supported _ p

theorem paddedInput_padded {blocks : Nat} (hb : 0 < blocks) (p : RatPoly) :
    HeadPadded (paddedInput blocks p) := by
  intro t ht
  rw [reindex_term_length _ p t ht]
  omega

theorem paddedInput_carrier {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) : HaarCarrierEqv blocks (paddedInput blocks p) p :=
  carrierOfPrefix (paddedInput_supported blocks p) hp (identityReindexQuaternionPolynomial_prefix blocks p)

/-- Computed finite modes of any supported input; no harmonicity premise. -/
def modes (blocks : Nat) (hb : 0 < blocks) (p : RatPoly) : List (Mode blocks) :=
  modesOfDegrees blocks hb (paddedInput blocks p) (paddedInput_supported blocks p)
    (paddedInput_padded hb p) (headDegrees (paddedInput blocks p))

theorem modes_reassembly (blocks : Nat) (hb : 0 < blocks) (p : RatPoly) :
    RatPolyCoeffEqv (sumValues (modes blocks hb p)) (paddedInput blocks p) :=
  (modesOfDegrees_reassembly _ _ _ _ _ _).trans (headComponent_reassembly _)

/-- Explicit finite-input cutoff; it may grow when the input itself changes. -/
def modeCutoff (blocks : Nat) (p : RatPoly) : Nat := headDegreeBound (paddedInput blocks p)

theorem modes_degree_le_cutoff (blocks : Nat) (hb : 0 < blocks) (p : RatPoly) :
    ∀ m, m ∈ modes blocks hb p → m.degree ≤ modeCutoff blocks p := by
  apply modesOfDegrees_degree_bound
  intro n hn
  have h := List.mem_range.mp hn
  exact Nat.le_of_lt_succ h

def harmonicPart {blocks : Nat} (m : Mode blocks) : RatPoly := polySmul m.coefficient m.polynomial

theorem harmonicPart_degree {blocks : Nat} (m : Mode blocks) :
    HasQuaternionBlockDegree 0 m.degree (harmonicPart m) := m.homogeneous.smul _

theorem harmonicPart_harmonic {blocks : Nat} (m : Mode blocks) :
    RatPolyCoeffEqv (headLaplacian (harmonicPart m)) polyZero :=
  (headLaplacian_smul _ _).trans ((m.harmonic.smul _).trans (RatPolyCoeffEqv.smul_zero _))

theorem harmonicPart_supported {blocks : Nat} (m : Mode blocks) :
    SupportedQuaternionBlocks blocks (harmonicPart m) := polySmul_supported m.support _

theorem mode_value_carrier {blocks : Nat} (hb : 0 < blocks) (m : Mode blocks) :
    HaarCarrierEqv blocks m.value (harmonicPart m) :=
  HaarCarrierEqv.smul m.coefficient
    (fun r => quaternionHaar_radiusIter_pair_right blocks 0 hb r m.polynomial m.radial)

def sumHarmonics {blocks : Nat} : List (Mode blocks) → RatPoly
  | [] => polyZero
  | m::ms => polyAdd (harmonicPart m) (sumHarmonics ms)

theorem sumHarmonics_supported {blocks : Nat} : ∀ ms : List (Mode blocks),
    SupportedQuaternionBlocks blocks (sumHarmonics ms)
  | [] => by intro t ht; contradiction
  | m::ms => polyAdd_supported (harmonicPart_supported m) (sumHarmonics_supported ms)

theorem sumValues_carrier {blocks : Nat} (hb : 0 < blocks) : ∀ ms : List (Mode blocks),
    HaarCarrierEqv blocks (sumValues ms) (sumHarmonics ms)
  | [] => .refl _ _
  | m::ms => HaarCarrierEqv.add (mode_value_carrier hb m) (sumValues_carrier hb ms)

/-- Arbitrary insertions survive the entire computed decomposition. -/
theorem polynomial_harmonic_carrier {blocks : Nat} (hb : 0 < blocks) (p : RatPoly)
    (hp : SupportedQuaternionBlocks blocks p) :
    HaarCarrierEqv blocks p (sumHarmonics (modes blocks hb p)) :=
  (paddedInput_carrier hp).symm.trans
    ((RatPolyCoeffEqv.haarCarrier (modes_reassembly blocks hb p).symm).trans
      (sumValues_carrier hb _))

/-- One exact signed mode contribution, with its genuine cutoff guard. -/
def heatContribution {blocks : Nat} (w : Q') (K : Nat) (r : RatPoly) (m : Mode blocks) : Q' :=
  if m.degree ≤ K then qpow w (m.degree*(m.degree+2)) *
    quaternionHaar blocks (polyMul (retainedImage (harmonicPart m)) r) else 0

private theorem heat_pairing_sum (tail : Nat) (hb : 0 < tail) (w : Q') (K : Nat)
    (r : RatPoly) (hr : HeadQuaternionIndependent r) : ∀ ms : List (Mode (tail+1)),
    quaternionHaar (tail+1) (polyMul (polyMul (relativeHeat w K) (sumHarmonics ms)) r) ≈
      qListSum (ms.map (heatContribution w K r))
  | [] => haar_of_coeff (((RatPolyCoeffEqv.mul_zero_right _).mul_right r).trans
      (RatPolyCoeffEqv.mul_zero_left r))
  | m::ms => by
      have hsplit : RatPolyCoeffEqv
          (polyMul (polyMul (relativeHeat w K) (sumHarmonics (m::ms))) r)
          (polyAdd (polyMul (polyMul (relativeHeat w K) (harmonicPart m)) r)
            (polyMul (polyMul (relativeHeat w K) (sumHarmonics ms)) r)) := by
        apply ((RatPolyCoeffEqv.mul_add_right _ _ _).mul_right r).trans
        rw [polyMul_add_left_exact]
        exact RatPolyCoeffEqv.refl _
      exact Q'.eqv_trans _ _ _ (haar_of_coeff hsplit)
        (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
          (Q'.add_eqv_congr'
            (harmonic_transmission_same_carrier tail hb w K m.degree (harmonicPart m) r
              (harmonicPart_degree m) (harmonicPart_harmonic m) hr)
            (heat_pairing_sum tail hb w K r hr ms)))

private theorem pairing_reorder (a p r : RatPoly) :
    RatPolyCoeffEqv (polyMul (polyMul a p) r) (polyMul (polyMul a r) p) :=
  (RatPolyCoeffEqv.mul_assoc a p r).trans
    (((RatPolyCoeffEqv.mul_comm p r).mul_left a).trans (RatPolyCoeffEqv.mul_assoc a r p).symm)

/-- The original packet on ANY supported signed input, not an assumed mode.
All remaining head-independent factors are retained in r. -/
theorem polynomial_heat_pairing (tail : Nat) (hb : 0 < tail) (w : Q') (K : Nat)
    (p r : RatPoly) (hp : SupportedQuaternionBlocks (tail+1) p)
    (hr : HeadQuaternionIndependent r) :
    quaternionHaar (tail+1) (polyMul (polyMul (relativeHeat w K) p) r) ≈
      qListSum ((modes (tail+1) (by omega) p).map (heatContribution w K r)) := by
  have hc := polynomial_harmonic_carrier (by omega : 0 < tail+1) p hp
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (pairing_reorder _ p r))
    (Q'.eqv_trans _ _ _ (hc (polyMul (relativeHeat w K) r))
      (Q'.eqv_trans _ _ _ (haar_of_coeff (pairing_reorder _ _ r).symm)
        (heat_pairing_sum tail hb w K r hr _)))

/-- Every mode of this FIXED input survives above its computed cutoff.
This does not give uniformity for K-dependent weighted source families. -/
theorem polynomial_heat_pairing_above_cutoff (tail : Nat) (hb : 0 < tail)
    (w : Q') (K : Nat) (p r : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) (hr : HeadQuaternionIndependent r)
    (hK : modeCutoff (tail+1) p ≤ K) :
    quaternionHaar (tail+1) (polyMul (polyMul (relativeHeat w K) p) r) ≈
      qListSum ((modes (tail+1) (by omega) p).map fun m =>
        qpow w (m.degree*(m.degree+2)) *
          quaternionHaar (tail+1) (polyMul (retainedImage (harmonicPart m)) r)) := by
  have he : (modes (tail+1) (by omega) p).map (heatContribution w K r) =
      (modes (tail+1) (by omega) p).map (fun m =>
        qpow w (m.degree*(m.degree+2)) *
          quaternionHaar (tail+1) (polyMul (retainedImage (harmonicPart m)) r)) := by
    apply List.map_congr_left
    intro m hm
    exact if_pos (Nat.le_trans (modes_degree_le_cutoff _ _ _ m hm) hK)
  exact he ▸ polynomial_heat_pairing tail hb w K p r hp hr

end YMGap.Continuum.SU2QuaternionPolynomialHarmonicExpansion

#print axioms YMGap.Continuum.SU2QuaternionPolynomialHarmonicExpansion.modesOfDegrees_reassembly
#print axioms YMGap.Continuum.SU2QuaternionPolynomialHarmonicExpansion.modesOfDegrees_degree_bound
#print axioms YMGap.Continuum.SU2QuaternionPolynomialHarmonicExpansion.paddedInput_supported
#print axioms YMGap.Continuum.SU2QuaternionPolynomialHarmonicExpansion.paddedInput_padded
#print axioms YMGap.Continuum.SU2QuaternionPolynomialHarmonicExpansion.paddedInput_carrier
#print axioms YMGap.Continuum.SU2QuaternionPolynomialHarmonicExpansion.modes_reassembly
#print axioms YMGap.Continuum.SU2QuaternionPolynomialHarmonicExpansion.modes_degree_le_cutoff
#print axioms YMGap.Continuum.SU2QuaternionPolynomialHarmonicExpansion.harmonicPart_degree
#print axioms YMGap.Continuum.SU2QuaternionPolynomialHarmonicExpansion.harmonicPart_harmonic
#print axioms YMGap.Continuum.SU2QuaternionPolynomialHarmonicExpansion.harmonicPart_supported
#print axioms YMGap.Continuum.SU2QuaternionPolynomialHarmonicExpansion.mode_value_carrier
#print axioms YMGap.Continuum.SU2QuaternionPolynomialHarmonicExpansion.sumHarmonics_supported
#print axioms YMGap.Continuum.SU2QuaternionPolynomialHarmonicExpansion.sumValues_carrier
#print axioms YMGap.Continuum.SU2QuaternionPolynomialHarmonicExpansion.polynomial_harmonic_carrier
#print axioms YMGap.Continuum.SU2QuaternionPolynomialHarmonicExpansion.polynomial_heat_pairing
#print axioms YMGap.Continuum.SU2QuaternionPolynomialHarmonicExpansion.polynomial_heat_pairing_above_cutoff
