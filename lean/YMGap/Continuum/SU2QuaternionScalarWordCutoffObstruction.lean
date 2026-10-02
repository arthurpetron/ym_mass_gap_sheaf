/-
# A scalar two-link word obstruction at retained heat cutoff two

For x=(a,b,c,d), y=(e,f,g,h), use the ACTUAL ordered word F=x*y and
q=(a^2-b^2)*(e^2-f^2)+4*a*b*e*f. Product Haar gives H[q^2]=1/18.
At nome 1/2 and retained label cutoff 2 the original product kernel keeps
q, with weight w^16, but kills all four components of q*F.

This is a finite-cutoff obstruction only. It is NOT an original Wilson
source, does NOT meet the original head-cutoff guard, and says nothing
against an all-cutoff or full-heat word estimate or the Yang--Mills target.
-/

import YMGap.Continuum.SU2QuaternionProductHeatMarginals
import YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
import YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval
import YMGap.Continuum.SU2HeatCutoffCasimirBound

namespace YMGap.Continuum.SU2QuaternionScalarWordCutoffObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval
open YMGap.Continuum.RGTransport (qpow)

local infix:50 " ≈ " => Q'.eqv

def half : Q' := Q'.mkPos 1 2 (by decide)

/-- Five literal monomials; the signed cross term is retained. -/
def source : RatPoly :=
  [([2,0,0,0,2,0,0,0],1), ([2,0,0,0,0,2,0,0],-1),
   ([0,2,0,0,2,0,0,0],-1), ([0,2,0,0,0,2,0,0],1),
   ([1,1,0,0,1,1,0,0],4)]

/-- Hamilton multiplication of the two actual coordinate quaternions. -/
def word : PolyQuaternion :=
  PolyQuaternion.mul (PolyQuaternion.coordinateVariable 0)
    (PolyQuaternion.coordinateVariable 1)

private def channels : List RatPoly :=
  [word.scalar, word.iPart, word.jPart, word.kPart]

/-- The existing lower-integration/upper-drop product heat map, not a surrogate. -/
def P (p : RatPoly) : RatPoly := productMap 2 half 2 [0,1] p

def pair (p : RatPoly) : Q' := quaternionHaar 2 (polyMul (P p) p)

def wordPair (p : RatPoly) : Q' :=
  qListSum (channels.map fun f => pair (polyMul p f))

theorem source_supported : SupportedQuaternionBlocks 2 source := by
  intro t ht
  have h : source.all (fun s => decide (s.1.length ≤ 4*2)) = true := by decide
  exact of_decide_eq_true ((List.all_eq_true.mp h) t ht)

private theorem degree_of_check (slot : Nat)
    (h : source.all (fun t => decide (quaternionBlockDegree t.1 slot = 2)) = true) :
    HasQuaternionBlockDegree slot 2 source := by
  intro t ht
  exact of_decide_eq_true ((List.all_eq_true.mp h) t ht)

theorem source_degree :
    HasQuaternionBlockDegree 0 2 source ∧ HasQuaternionBlockDegree 1 2 source :=
  ⟨degree_of_check 0 (by decide), degree_of_check 1 (by decide)⟩

/-- The elementary guard used by scalar one-link alignment is satisfied. -/
theorem scalar_cutoff_guard : SU2HeatCutoffCasimirBound.sufficientCutoff half ≤ 2 := by
  decide

/-- Pin to the original doubled-carrier kernel pairing with the SAME source. -/
theorem pair_original (p : RatPoly) :
    pair p ≈ quaternionHaar 4
      (polyMul (productHeat 2 half 2 [0,1]) (polyMul p (liftBoundary 2 p))) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
    (productMap_pairing 2 half 2 [0,1] p p)

private theorem pair_collected (p : RatPoly) :
    pair p ≈ quaternionHaar 2 (polyMul (canonRat (P p)) p) :=
  Q'.eqv_symm (quaternionHaar_canonRat_mul 2 (P p) p)

theorem source_norm : quaternionHaar 2 (polyMul source source) ≈
    Q'.mkPos 1 18 (by decide) := by decide

theorem source_pair : pair source ≈ Q'.mkPos 1 1179648 (by decide) :=
  Q'.eqv_trans _ _ _ (pair_collected source) (by decide +kernel)

/-- All four actual q*F outputs have empty exact rational normal form. -/
theorem source_word_outputs :
    channels.all (fun f => decide (canonRat (P (polyMul source f)) = [])) = true := by
  decide +kernel

private theorem list_pair_zero : ∀ fs : List RatPoly,
    (∀ f, f ∈ fs → canonRat (P (polyMul source f)) = []) →
    qListSum (fs.map fun f => pair (polyMul source f)) ≈ 0
  | [], _ => Q'.eqv_refl 0
  | f::fs, hz => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (quaternionHaar_mul_eq_zero_of_canonRat_eq_nil 2 _ _ (hz f List.mem_cons_self))
        (list_pair_zero fs (fun g hg => hz g (List.mem_cons_of_mem f hg))))
      (by decide)

theorem source_word_pair : wordPair source ≈ 0 :=
  list_pair_zero channels (fun f hf =>
    of_decide_eq_true ((List.all_eq_true.mp source_word_outputs) f hf))

/-- Exact negative slack for the proposed two-link w^(3*2) floor. -/
theorem scalar_alignment_defect :
    wordPair source - qpow half 6 * pair source ≈
      Q'.mkPos (-1) 75497472 (by decide) :=
  Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' source_word_pair
      (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left _ _ _ source_pair)))
    (by decide)

theorem scalar_alignment_fails : ¬ qpow half 6 * pair source ≤ wordPair source := by
  intro h
  have hs : qpow half 6 * pair source ≈ Q'.mkPos 1 75497472 (by decide) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ source_pair) (by decide)
  have hbad : Q'.mkPos 1 75497472 (by decide) ≤ (0 : Q') :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hs)
      (Q'.le_trans' _ _ _ h (Q'.le_of_eqv source_word_pair))
  exact (by decide : ¬ Q'.mkPos 1 75497472 (by decide) ≤ (0 : Q')) hbad

def epsilon : Q' := Q'.mkPos 1 50 (by decide)

/-- A positive perturbation of the vacuum; no original-action identification. -/
def positiveSource : RatPoly := polyAdd polyOne (polySmul epsilon source)

theorem positiveSource_supported : SupportedQuaternionBlocks 2 positiveSource := by
  intro t ht
  have h : positiveSource.all (fun s => decide (s.1.length ≤ 4*2)) = true := by decide
  exact of_decide_eq_true ((List.all_eq_true.mp h) t ht)

/-- Explicit square certificate for positiveSource >= 1/2, under insertions. -/
def positiveSource_floor : Certificate 2
    (polyAdd positiveSource (polyNeg (cap half))) := by
  let I := Interval.changeCap (by decide : polynomialCap source ≈ (25 : Q'))
    (polynomialInterval 2 source source_supported)
  exact .ofCoeff (RatPolyCoeffEqv.of_canon_termwise (by decide))
    (.smul epsilon (by decide) I.lower)

theorem positiveSource_haar_mass : quaternionHaar 2 positiveSource ≈ 1 := by decide

theorem positiveSource_pair : pair positiveSource ≈
    Q'.mkPos 2949120001 2949120000 (by decide) :=
  Q'.eqv_trans _ _ _ (pair_collected positiveSource) (by decide +kernel)

private theorem output_zero (f : RatPoly) (hf : f ∈ channels) :
    RatPolyCoeffEqv (P (polyMul source f)) polyZero := by
  have hz : canonRat (P (polyMul source f)) = [] :=
    of_decide_eq_true ((List.all_eq_true.mp source_word_outputs) f hf)
  intro weight
  have h := ratWeightedSum_canon weight (P (polyMul source f))
  rw [hz] at h
  exact Q'.eqv_symm h

private theorem positive_component_map (f : RatPoly) (hf : f ∈ channels) :
    RatPolyCoeffEqv (P (polyMul positiveSource f)) (P f) := by
  have hfac : RatPolyCoeffEqv (polyMul positiveSource f)
      (polyAdd f (polySmul epsilon (polyMul source f))) := by
    simp only [channels, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    all_goals exact RatPolyCoeffEqv.of_canon_termwise (by decide)
  have hs : RatPolyCoeffEqv (P (polySmul epsilon (polyMul source f)))
      (polySmul epsilon (P (polyMul source f))) :=
    SU2QuaternionHaarKernelBound.kernelMap_smul 2 (productHeat 2 half 2 [0,1])
      epsilon (polyMul source f)
  exact (productMap_congr 2 half 2 [0,1] hfac).trans
    ((productMap_add 2 half 2 [0,1] f (polySmul epsilon (polyMul source f))).trans
      (((RatPolyCoeffEqv.refl (P f)).add
        (hs.trans (((output_zero f hf).smul epsilon).trans
          (RatPolyCoeffEqv.smul_zero epsilon)))).trans
        (RatPolyCoeffEqv.add_zero (P f))))

private theorem positive_component_pair (f : RatPoly) (hf : f ∈ channels) :
    pair (polyMul positiveSource f) ≈ Q'.mkPos 1 256 (by decide) := by
  have h := haar_of_coeff (blocks := 2)
    ((positive_component_map f hf).mul_right (polyMul positiveSource f))
  refine Q'.eqv_trans _ _ _ h (Q'.eqv_trans _ _ _
    (Q'.eqv_symm (quaternionHaar_canonRat_mul 2 (P f) (polyMul positiveSource f))) ?_)
  simp only [channels, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  all_goals decide +kernel

theorem positiveSource_word_pair : wordPair positiveSource ≈
    Q'.mkPos 1 64 (by decide) := by
  have h0 := positive_component_pair word.scalar (by simp only [channels, List.mem_cons, true_or])
  have h1 := positive_component_pair word.iPart (by simp only [channels, List.mem_cons, true_or, or_true])
  have h2 := positive_component_pair word.jPart (by simp only [channels, List.mem_cons, true_or, or_true])
  have h3 := positive_component_pair word.kPart (by simp only [channels, List.mem_cons, true_or, or_true])
  exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' h0
    (Q'.add_eqv_congr' h1 (Q'.add_eqv_congr' h2 (Q'.add_eqv_congr' h3 (Q'.eqv_refl 0)))))
    (by decide)

theorem positive_alignment_defect :
    wordPair positiveSource - qpow half 6 * pair positiveSource ≈
      Q'.mkPos (-1) 188743680000 (by decide) :=
  Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' positiveSource_word_pair
      (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left _ _ _ positiveSource_pair)))
    (by decide)

theorem positive_alignment_fails :
    ¬ qpow half 6 * pair positiveSource ≤ wordPair positiveSource := by
  intro h
  have hs : qpow half 6 * pair positiveSource ≈
      Q'.mkPos 2949120001 188743680000 (by decide) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ positiveSource_pair) (by decide)
  have hbad : Q'.mkPos 2949120001 188743680000 (by decide) ≤ Q'.mkPos 1 64 (by decide) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hs)
      (Q'.le_trans' _ _ _ h (Q'.le_of_eqv positiveSource_word_pair))
  exact (by decide : ¬ Q'.mkPos 2949120001 188743680000 (by decide) ≤
    Q'.mkPos 1 64 (by decide)) hbad

/-- The universal finite-cutoff scalar floor fails even with a supplied
strict positive square certificate and normalized Haar mass. -/
theorem no_positive_scalar_word_alignment :
    ¬ (∀ p : RatPoly, SupportedQuaternionBlocks 2 p →
      Certificate 2 (polyAdd p (polyNeg (cap half))) →
      quaternionHaar 2 p ≈ 1 → qpow half 6 * pair p ≤ wordPair p) := by
  intro h
  exact positive_alignment_fails
    (h positiveSource positiveSource_supported positiveSource_floor positiveSource_haar_mass)

#print axioms source_supported
#print axioms source_degree
#print axioms scalar_cutoff_guard
#print axioms pair_original
#print axioms source_norm
#print axioms source_pair
#print axioms source_word_outputs
#print axioms source_word_pair
#print axioms scalar_alignment_defect
#print axioms scalar_alignment_fails
#print axioms positiveSource_supported
#print axioms positiveSource_floor
#print axioms positiveSource_haar_mass
#print axioms positiveSource_pair
#print axioms positiveSource_word_pair
#print axioms positive_alignment_defect
#print axioms positive_alignment_fails
#print axioms no_positive_scalar_word_alignment

end YMGap.Continuum.SU2QuaternionScalarWordCutoffObstruction
