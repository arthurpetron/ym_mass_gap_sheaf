/-
# The scalar heat alignment does not extend to arbitrary quaternion vectors

For x=(a,b,c,d), the supported source A=(0,b,-c,0) has degree one.
The ACTUAL ordered product x*A=(c^2-b^2,ab+cd,-ac+bd,-2bc) has
four harmonic degree-two components. Both Haar squared norms are 1/2.
The original relative heat packet therefore gives weights w^3 and w^8.
At w=1/2, EVERY cutoff K>=2 violates the proposed vector alignment.

This prunes a matrix-order induction shortcut only. It does not refute the
existing scalar one-link theorem, a scalar-source whole-word inequality,
an original interacting Wilson estimate, or the Yang--Mills target.
-/

import YMGap.Continuum.SU2QuaternionRelativeHarmonicReproduction
import YMGap.Continuum.SU2QuaternionProductHeatPositive
import YMGap.Continuum.QuaternionHaarUnitScalarSquare

namespace YMGap.Continuum.SU2QuaternionVectorAlignmentObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionRelativeHeatTransmission
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionDroppedHeadSubstitution
open YMGap.Continuum.SU2QuaternionRelativeHarmonicReproduction
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.QuaternionHaarUnitScalarSquare (Supported)
open YMGap.Continuum.RGTransport (qpow)

local infix:50 " ≈ " => Q'.eqv

def half : Q' := Q'.mkPos 1 2 (by decide)

/-- A literal, signed quaternion vector on the original one-link carrier.
Exponent lists have four entries so the two constant Laplacian terms cancel
at coefficient-probe strength, not merely after Haar integration. -/
def source : PolyQuaternion :=
  ⟨polyZero, [([0,1,0,0],1)], [([0,0,1,0],-1)], polyZero⟩

/-- Ordered Hamilton multiplication, not componentwise or commuting multiplication. -/
def leftMultiply (p : PolyQuaternion) : PolyQuaternion :=
  PolyQuaternion.mul (PolyQuaternion.coordinateVariable 0) p

private def channels (p : PolyQuaternion) : List RatPoly :=
  [p.scalar, p.iPart, p.jPart, p.kPart]

/-- Actual lower/upper heat pairing; both copies use the SAME scalar component. -/
def componentPair (w : Q') (K : Nat) (p : RatPoly) : Q' :=
  quaternionHaar 2
    (polyMul (polyMul (heatAt 0 1 w K) p) (liftBoundary 1 p))

/-- Sum of the four actual original-kernel component pairings. -/
def vectorPair (w : Q') (K : Nat) (p : PolyQuaternion) : Q' :=
  qListSum ((channels p).map (componentPair w K))

private theorem degree_of_check (d : Nat) (p : RatPoly)
    (h : p.all (fun t => decide (quaternionBlockDegree t.1 0 = d)) = true) :
    HasQuaternionBlockDegree 0 d p := by
  intro t ht
  exact of_decide_eq_true ((List.all_eq_true.mp h) t ht)

theorem source_supported : Supported 1 source := by
  constructor
  · intro t ht; cases ht
  · intro t ht
    have he := List.mem_singleton.mp ht
    subst t
    decide
  · intro t ht
    have he := List.mem_singleton.mp ht
    subst t
    decide
  · intro t ht; cases ht

theorem multiplied_supported : Supported 1 (leftMultiply source) :=
  (Supported.coordinate (by decide : 0 < 1)).mul source_supported

private theorem component_harmonic (w : Q') (K d : Nat) (hK : d ≤ K)
    (p : RatPoly) (hd : HasQuaternionBlockDegree 0 d p)
    (hh : RatPolyCoeffEqv (headLaplacian p) polyZero)
    (hs : quaternionHaar 1 (polyMul (substituteRetained p) p) ≈
      quaternionHaar 1 (polyMul p p)) :
    componentPair w K p ≈ qpow w (d*(d+2)) * quaternionHaar 1 (polyMul p p) := by
  have h := heat_harmonic_reproduction 1 (by decide) w K d p hd hh p
  rw [if_pos hK] at h
  exact Q'.eqv_trans _ _ _ h
    (Q'.mul_eqv_congr_left _ _ _ hs)

private theorem list_harmonic (w : Q') (K d : Nat) (hK : d ≤ K) :
    ∀ ps : List RatPoly,
      (∀ p, p ∈ ps → HasQuaternionBlockDegree 0 d p) →
      (∀ p, p ∈ ps → RatPolyCoeffEqv (headLaplacian p) polyZero) →
      (∀ p, p ∈ ps → quaternionHaar 1 (polyMul (substituteRetained p) p) ≈
        quaternionHaar 1 (polyMul p p)) →
      qListSum (ps.map (componentPair w K)) ≈
        qpow w (d*(d+2)) * qListSum (ps.map fun p => quaternionHaar 1 (polyMul p p))
  | [], _, _, _ => Q'.eqv_symm (Q'.mul_zero_eqv _)
  | p::ps, hd, hh, hs =>
      Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (component_harmonic w K d hK p (hd p List.mem_cons_self)
            (hh p List.mem_cons_self) (hs p List.mem_cons_self))
          (list_harmonic w K d hK ps
            (fun q hq => hd q (List.mem_cons_of_mem p hq))
            (fun q hq => hh q (List.mem_cons_of_mem p hq))
            (fun q hq => hs q (List.mem_cons_of_mem p hq))))
        (Q'.eqv_symm (Q'.mul_add_eqv _ _ _))

/-- Exact input heat pairing at arbitrary nome and every retained quadratic cutoff. -/
theorem source_heat (w : Q') (K : Nat) (hK : 2 ≤ K) :
    vectorPair w K source ≈ qpow w 3 * half := by
  have hd : ∀ p, p ∈ channels source → HasQuaternionBlockDegree 0 1 p := by
    intro p hp
    simp only [channels, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    all_goals exact degree_of_check 1 _ (by decide)
  have hh : ∀ p, p ∈ channels source → RatPolyCoeffEqv (headLaplacian p) polyZero := by
    intro p hp
    simp only [channels, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    all_goals exact RatPolyCoeffEqv.of_canon_termwise (by decide)
  have hs : ∀ p, p ∈ channels source →
      quaternionHaar 1 (polyMul (substituteRetained p) p) ≈
        quaternionHaar 1 (polyMul p p) := by
    intro p hp
    simp only [channels, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    all_goals decide
  exact Q'.eqv_trans _ _ _ (list_harmonic w K 1 (by omega) _ hd hh hs)
    (Q'.mul_eqv_congr_left _ _ _ (by decide))

/-- Actual multiplication changes all four components to the degree-two channel. -/
theorem multiplied_heat (w : Q') (K : Nat) (hK : 2 ≤ K) :
    vectorPair w K (leftMultiply source) ≈ qpow w 8 * half := by
  have hd : ∀ p, p ∈ channels (leftMultiply source) → HasQuaternionBlockDegree 0 2 p := by
    intro p hp
    simp only [channels, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    all_goals exact degree_of_check 2 _ (by decide)
  have hh : ∀ p, p ∈ channels (leftMultiply source) →
      RatPolyCoeffEqv (headLaplacian p) polyZero := by
    intro p hp
    simp only [channels, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    all_goals exact RatPolyCoeffEqv.of_canon_termwise (by decide)
  have hs : ∀ p, p ∈ channels (leftMultiply source) →
      quaternionHaar 1 (polyMul (substituteRetained p) p) ≈
        quaternionHaar 1 (polyMul p p) := by
    intro p hp
    simp only [channels, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    all_goals decide
  exact Q'.eqv_trans _ _ _ (list_harmonic w K 2 hK _ hd hh hs)
    (Q'.mul_eqv_congr_left _ _ _ (by decide))

theorem source_at_half (K : Nat) (hK : 2 ≤ K) :
    vectorPair half K source ≈ Q'.mkPos 1 16 (by decide) :=
  Q'.eqv_trans _ _ _ (source_heat half K hK) (by decide)

theorem multiplied_at_half (K : Nat) (hK : 2 ≤ K) :
    vectorPair half K (leftMultiply source) ≈ Q'.mkPos 1 512 (by decide) :=
  Q'.eqv_trans _ _ _ (multiplied_heat half K hK) (by decide)

/-- Exact negative comparison slack, at EVERY K>=2, not just a short prefix. -/
theorem alignment_defect (K : Nat) (hK : 2 ≤ K) :
    vectorPair half K (leftMultiply source) - qpow half 3 * vectorPair half K source ≈
      Q'.mkPos (-3) 512 (by decide) :=
  Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (multiplied_at_half K hK)
      (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left _ _ _ (source_at_half K hK))))
    (by decide)

theorem vector_alignment_fails (K : Nat) (hK : 2 ≤ K) :
    ¬ qpow half 3 * vectorPair half K source ≤ vectorPair half K (leftMultiply source) := by
  intro h
  have hs : qpow half 3 * vectorPair half K source ≈ Q'.mkPos 1 128 (by decide) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (source_at_half K hK)) (by decide)
  have hbad : Q'.mkPos 1 128 (by decide) ≤ Q'.mkPos 1 512 (by decide) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hs)
      (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (multiplied_at_half K hK)))
  exact (by decide : ¬ Q'.mkPos 1 128 (by decide) ≤ Q'.mkPos 1 512 (by decide)) hbad

/-- A supported explicit witness refutes universal quaternion-vector alignment. -/
theorem no_vector_alignment (K : Nat) (hK : 2 ≤ K) :
    ¬ (∀ p : PolyQuaternion, Supported 1 p →
      qpow half 3 * vectorPair half K p ≤ vectorPair half K (leftMultiply p)) := by
  intro h
  exact vector_alignment_fails K hK (h source source_supported)

#print axioms source_supported
#print axioms multiplied_supported
#print axioms source_heat
#print axioms multiplied_heat
#print axioms source_at_half
#print axioms multiplied_at_half
#print axioms alignment_defect
#print axioms vector_alignment_fails
#print axioms no_vector_alignment

end YMGap.Continuum.SU2QuaternionVectorAlignmentObstruction
