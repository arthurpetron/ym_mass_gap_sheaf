/-
# Uniform original-action error of the pure block conditional approximant

The finite inverse iterate is applied to the actual inserted numerator and
contains no unchanged copy of the input polynomial.  At fixed finite cutoff,
the error against the constructed original-action conditional projection is
bounded uniformly over input degree.  The coefficient depends on nome and
block size; this is not a spatial- or cutoff-uniform gap estimate.
-/

import YMGap.Continuum.BF4ExactSlabBlockConditionalProjection
import YMGap.Continuum.RCDistBridge
import YMGap.Constructive.QPoly

namespace YMGap.Continuum.BF4ExactSlabBlockConditionalApproximationError

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabBlockComparisonConstants
open YMGap.Continuum.BF4ExactSlabBlockNormalizerMap
open YMGap.Continuum.BF4ExactSlabBlockInverseApproximation
open YMGap.Continuum.BF4ExactSlabBlockConditionalApproximation
open YMGap.Continuum.BF4ExactSlabBlockCompletedInverse
open YMGap.Continuum.BF4ExactSlabBlockOriginalConditional
open YMGap.Continuum.BF4ExactSlabBlockConditionalProjection
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
private def rat (q : Q') : RC := Quotient.mk crealSetoid (ofQ' q)

private theorem rat_mono {a b : Q'} (h : a ≤ b) : RCle (rat a) (rat b) :=
  leEv_le_ofQ'_of_approx_le (fun _ => h)

private theorem limit_le_of_eventually {s : Nat → CReal} {L : CReal}
    (hs : ConvergesTo s L) (b : Q') (base : Nat)
    (h : ∀ n, base ≤ n → leEv (s n) (ofQ' b)) : leEv L (ofQ' b) := by
  have ht : ConvergesTo (fun n => s (max n base)) L := by
    intro epsilon hepsilon
    obtain ⟨N, hN⟩ := hs epsilon hepsilon
    exact ⟨N, fun n hn => hN (max n base)
      (Nat.le_trans hn (Nat.le_max_left _ _))⟩
  exact leEv_of_convergesTo_le ht (convergesTo_const (ofQ' b))
    (fun n => h (max n base) (Nat.le_max_right _ _))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K) (links : List Z4Link)
  (hl : ∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks extent)

local notation "G" => backgroundData hw0 hw1 K extent hK links
local notation "F" => fullData hw0 hw1 K extent hK
local notation "M" => normalizerMap hw0 hw1 K extent hK links
local notation "A" => approximateInverse hw0 hw1 K extent hK links
local notation "U" => blockUpper w links.length
local notation "L2" => blockLower w links.length * blockLower w links.length

private def divideFloor (v : Q') : Q' :=
  Q'.divPos v L2
    (Q'.mul_pos (blockLower_positive hw0 hw1 links.length)
      (blockLower_positive hw0 hw1 links.length))

private theorem divideFloor_congr {a b : Q'} (h : a ≈ b) :
    divideFloor hw0 hw1 links a ≈ divideFloor hw0 hw1 links b := by
  unfold divideFloor Q'.divPos
  exact Q'.mul_eqv_congr_right _ _ _ h

private theorem divideFloor_mul (a b : Q') :
    divideFloor hw0 hw1 links (a * b) ≈
      divideFloor hw0 hw1 links a * b := by
  unfold divideFloor Q'.divPos
  let z := Q'.recipPos L2
    (Q'.mul_pos (blockLower_positive hw0 hw1 links.length)
      (blockLower_positive hw0 hw1 links.length))
  change (a * b) * z ≈ (a * z) * b
  exact Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv a b z)
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left a _ _ (Q'.mul_comm_eqv b z))
      (Q'.eqv_symm (Q'.mul_assoc_eqv a z b)))

private theorem four_mul (a b : Q') :
    ((a * b + a * b) + (a * b + a * b)) ≈
      ((a + a) + (a + a)) * b := by
  have h : (a * b + a * b) ≈ (a + a) * b :=
    Q'.eqv_symm (QPoly.q_add_mul a a b)
  exact Q'.eqv_trans _ _ _ (QPoly.q_add_congr h h)
    (Q'.eqv_symm (QPoly.q_add_mul (a + a) (a + a) b))

/-- The explicit relative error coefficient; it depends on nome and block
size but not on the input observable, cutoff or slab extent. -/
def projectionErrorCoefficient (epsilon : Q') : Q' :=
  divideFloor hw0 hw1 links
    (U * ((epsilon + epsilon) + (epsilon + epsilon)))

private def fourOne : Q' := (((1 : Q') + 1) + (1 + 1))

/-- Input-independent precision paid to the block inverse iteration.  The
one-over-one-plus factor avoids any unproved division or reciprocal estimate. -/
def projectionTolerance (w : Q') (size : Nat) (delta : Q') : Q' :=
  (delta * (blockLower w size * blockLower w size)) *
    ExpUBInstance.oneOver1p (blockUpper w size * fourOne)

/-- One iteration cutoff for every supported input polynomial at fixed nome
and block size. -/
def projectionCutoff (w : Q') (size : Nat) (delta : Q') : Nat :=
  relativeCutoff w size (projectionTolerance w size delta)

include hw0 hw1 in
private theorem projectionTolerance_pos (delta : Q') (hdelta : (0 : Q') < delta) :
    (0 : Q') < projectionTolerance w links.length delta := by
  unfold projectionTolerance
  exact Q'.mul_pos
    (Q'.mul_pos hdelta
      (Q'.mul_pos (blockLower_positive hw0 hw1 links.length)
        (blockLower_positive hw0 hw1 links.length)))
    (oneOver1p_pos _)

private theorem four_as_mul (z : Q') :
    ((z + z) + (z + z)) ≈ fourOne * z := by
  have hz : z ≈ (1 : Q') * z := Q'.eqv_symm (Q'.one_mul_eqv z)
  have hzz : z + z ≈ (1 : Q') * z + 1 * z :=
    QPoly.q_add_congr hz hz
  exact Q'.eqv_trans _ _ _ (QPoly.q_add_congr hzz hzz)
    (four_mul 1 z)

/-- The coefficient is at most the requested tolerance with the explicit
input-independent iteration cutoff. -/
theorem projectionErrorCoefficient_le (delta : Q')
    (hdelta : (0 : Q') < delta) :
    projectionErrorCoefficient hw0 hw1 links
      (projectionTolerance w links.length delta) ≤ delta := by
  let eta := projectionTolerance w links.length delta
  let t := U * fourOne
  have hL : (0 : Q') < L2 :=
    Q'.mul_pos (blockLower_positive hw0 hw1 links.length)
      (blockLower_positive hw0 hw1 links.length)
  have ht : (0 : Q') ≤ t :=
    Q'.mul_nonneg _ _ (Q'.le_of_lt (blockUpper_positive hw0 links.length))
      (by decide : (0 : Q') ≤ fourOne)
  have hdeltaL : (0 : Q') ≤ delta * L2 :=
    Q'.mul_nonneg _ _ (Q'.le_of_lt hdelta) (Q'.le_of_lt hL)
  have hbudget : t * eta ≤ delta * L2 :=
    key_bound t (delta * L2) ht hdeltaL
  have hnum : U * ((eta + eta) + (eta + eta)) ≈ t * eta :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left U _ _ (four_as_mul eta))
      (Q'.eqv_symm (Q'.mul_assoc_eqv U fourOne eta))
  have hnumle : U * ((eta + eta) + (eta + eta)) ≤ delta * L2 :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hnum) hbudget
  change Q'.divPos (U * ((eta + eta) + (eta + eta))) L2 hL ≤ delta
  exact Q'.divPos_le_of_le_mul _ _ _ hnumle

include hl in
/-- The literal finite inverse rows obey an original-action bound after the
relative cutoff.  No degree or norm of the input appears in the cutoff. -/
private theorem finite_error_bound (p : (F).V) (epsilon : Q')
    (hepsilon : (0 : Q') < epsilon) (n m : Nat)
    (hn : relativeCutoff w links.length epsilon ≤ n) (hm : n ≤ m) :
    let e := epsilon * (F).B p p
    let b := divideFloor hw0 hw1 links (U * ((e + e) + (e + e)))
    (F).distSqQ
      (A (numeratorVector hw0 hw1 K extent hK links p.val p.property) m)
      (A (numeratorVector hw0 hw1 K extent hK links p.val p.property) n) ≤ b := by
  let r := numeratorVector hw0 hw1 K extent hK links p.val p.property
  let a := A r n
  let e := epsilon * (F).B p p
  let four := (e + e) + (e + e)
  have hL : (0 : Q') < L2 :=
    Q'.mul_pos (blockLower_positive hw0 hw1 links.length)
      (blockLower_positive hw0 hw1 links.length)
  have hU : (0 : Q') ≤ U := Q'.le_of_lt (blockUpper_positive hw0 links.length)
  have hn0 : (G).distSqQ r (M a) ≤ e :=
    conditionalApproximation_relative_error hw0 hw1 K extent hK links hl
      p.val p.property epsilon hepsilon n hn
  have hm0 : (G).distSqQ r (M (A r m)) ≤ e :=
    conditionalApproximation_relative_error hw0 hw1 K extent hK links hl
      p.val p.property epsilon hepsilon m (Nat.le_trans hn hm)
  have hm1 : (G).distSqQ (M (A r m)) r ≤ e :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv ((G).distSqQ_comm _ _)) hm0
  have htri := (G).distSqQ_triangle (M (A r m)) r (M a)
  have hfour : (G).distSqQ (M (A r m)) (M a) ≤ four :=
    Q'.le_trans' _ _ _ htri
      (Q'.add_le_add (Q'.add_le_add hm1 hm1) (Q'.add_le_add hn0 hn0))
  have hG : L2 * (G).distSqQ (A r m) a ≤ four :=
    Q'.le_trans' _ _ _
      (normalizer_distance_bounds hw0 hw1 K extent hK links hl (A r m) a).1 hfour
  have hF : (F).distSqQ (A r m) a ≤ U * (G).distSqQ (A r m) a := by
    exact toFull_distance_bound hw0 hw1 K extent hK links hl (A r m) a
  have hswap (d : Q') : L2 * (U * d) ≈ U * (L2 * d) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv L2 U d))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (L2 * U) (U * L2) d (Q'.mul_comm_eqv L2 U))
        (Q'.mul_assoc_eqv U L2 d))
  have hscaled : L2 * (F).distSqQ (A r m) a ≤ U * four :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hF (Q'.le_of_lt hL))
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv (hswap _))
        (Q'.mul_le_mul_of_nonneg_left _ _ _ hG hU))
  change (F).distSqQ (A r m) a ≤ Q'.divPos (U * four) L2 hL
  apply Q'.le_divPos_of_mul_le
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_comm_eqv ((F).distSqQ (A r m) a) L2)) hscaled

/-- Uniform-in-input completed squared error for the pure polynomial block
conditional map.  The displayed rational numerator is four copies of
`epsilon * originalNormSq`; division uses the proved positive collar floor. -/
theorem conditionalProjection_error_bound (p : (F).V) (epsilon : Q')
    (hepsilon : (0 : Q') < epsilon) (n : Nat)
    (hn : relativeCutoff w links.length epsilon ≤ n) :
    let e := epsilon * (F).B p p
    let b := divideFloor hw0 hw1 links (U * ((e + e) + (e + e)))
    RCle
      ((F).cinnerCompl
        ((F).cSub
          (conditionalProjection hw0 hw1 K extent hK links hl (embedV F p))
          (embedV F (conditionalApproximation hw0 hw1 K extent hK links
            p.val p.property n)))
        ((F).cSub
          (conditionalProjection hw0 hw1 K extent hK links hl (embedV F p))
          (embedV F (conditionalApproximation hw0 hw1 K extent hK links
            p.val p.property n))))
      (rat b) := by
  let r := numeratorVector hw0 hw1 K extent hK links p.val p.property
  let X := conditionalRep hw0 hw1 K extent hK links hl p
  let a := conditionalApproximation hw0 hw1 K extent hK links p.val p.property n
  let Y := constCauchy F a
  let e := epsilon * (F).B p p
  let b := divideFloor hw0 hw1 links (U * ((e + e) + (e + e)))
  have hrows (m : Nat) (hm : n ≤ m) :
      (F).distSqQ (X.seq m) (Y.seq m) ≤ b :=
    finite_error_bound hw0 hw1 K extent hK links hl p epsilon hepsilon n m hn hm
  rw [conditionalProjection_embed]
  change RCle
    ((F).cinnerCompl
      ((F).cSub (Quotient.mk (cauchySetoid F) X) (Quotient.mk (cauchySetoid F) Y))
      ((F).cSub (Quotient.mk (cauchySetoid F) X) (Quotient.mk (cauchySetoid F) Y)))
    (rat b)
  rw [(F).cinnerCompl_cSub X Y]
  change leEv
    (ofQ'CauchySeq (fun m => (F).distSqQ (X.seq m) (Y.seq m))
      ((F).distSqSeqCauchy X Y)) (ofQ' b)
  apply limit_le_of_eventually
    (convergesTo_ofQ'CauchySeq _ ((F).distSqSeqCauchy X Y)) b n
  intro m hm
  exact leEv_le_ofQ'_of_approx_le (fun _ => hrows m hm)

/-- The bound is a genuine uniform operator-error coefficient times the
original full-action norm, not a per-input cutoff. -/
theorem conditionalProjection_error_relative (p : (F).V) (epsilon : Q')
    (hepsilon : (0 : Q') < epsilon) (n : Nat)
    (hn : relativeCutoff w links.length epsilon ≤ n) :
    let a := conditionalApproximation hw0 hw1 K extent hK links
      p.val p.property n
    RCle
      ((F).cinnerCompl
        ((F).cSub
          (conditionalProjection hw0 hw1 K extent hK links hl (embedV F p))
          (embedV F a))
        ((F).cSub
          (conditionalProjection hw0 hw1 K extent hK links hl (embedV F p))
          (embedV F a)))
      (rat ((projectionErrorCoefficient hw0 hw1 links epsilon) * (F).B p p)) := by
  let E := (F).B p p
  let e := epsilon * E
  let four := (e + e) + (e + e)
  have hbase := conditionalProjection_error_bound hw0 hw1 K extent hK links hl
    p epsilon hepsilon n hn
  have hnum : U * four ≈
      (U * ((epsilon + epsilon) + (epsilon + epsilon))) * E :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left U _ _ (four_mul epsilon E))
      (Q'.eqv_symm (Q'.mul_assoc_eqv U
        ((epsilon + epsilon) + (epsilon + epsilon)) E))
  have hfactor :
      divideFloor hw0 hw1 links (U * four) ≈
        projectionErrorCoefficient hw0 hw1 links epsilon * E :=
    Q'.eqv_trans _ _ _ (divideFloor_congr hw0 hw1 links hnum)
      (divideFloor_mul hw0 hw1 links _ E)
  have hRC : rat (divideFloor hw0 hw1 links (U * four)) =
      rat (projectionErrorCoefficient hw0 hw1 links epsilon * E) :=
    Quotient.sound (ofQ'_equiv_of_eqv hfactor)
  change RCle
    ((F).cinnerCompl
      ((F).cSub
        (conditionalProjection hw0 hw1 K extent hK links hl (embedV F p))
        (embedV F (conditionalApproximation hw0 hw1 K extent hK links
          p.val p.property n)))
      ((F).cSub
        (conditionalProjection hw0 hw1 K extent hK links hl (embedV F p))
        (embedV F (conditionalApproximation hw0 hw1 K extent hK links
          p.val p.property n))))
    (rat (divideFloor hw0 hw1 links (U * four))) at hbase
  rw [hRC] at hbase
  exact hbase

/-- Uniform original-action squared operator error, including zero-norm
inputs.  The cutoff depends only on nome, selected-block size and delta. -/
theorem conditionalProjection_error_tolerance (p : (F).V) (delta : Q')
    (hdelta : (0 : Q') < delta) (n : Nat)
    (hn : projectionCutoff w links.length delta ≤ n) :
    let a := conditionalApproximation hw0 hw1 K extent hK links
      p.val p.property n
    RCle
      ((F).cinnerCompl
        ((F).cSub
          (conditionalProjection hw0 hw1 K extent hK links hl (embedV F p))
          (embedV F a))
        ((F).cSub
          (conditionalProjection hw0 hw1 K extent hK links hl (embedV F p))
          (embedV F a)))
      (rat (delta * (F).B p p)) := by
  let eta := projectionTolerance w links.length delta
  have hbase := conditionalProjection_error_relative hw0 hw1 K extent hK links hl
    p eta (projectionTolerance_pos hw0 hw1 links delta hdelta)
      n hn
  have hcoef := projectionErrorCoefficient_le hw0 hw1 links delta hdelta
  have hnorm : (0 : Q') ≤ (F).B p p := (F).self_nonneg p
  have hmul :
      projectionErrorCoefficient hw0 hw1 links eta * (F).B p p ≤
        delta * (F).B p p :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hcoef hnorm
  exact RCle_trans hbase (rat_mono hmul)

#print axioms conditionalProjection_error_bound
#print axioms projectionErrorCoefficient
#print axioms conditionalProjection_error_relative
#print axioms projectionCutoff
#print axioms projectionErrorCoefficient_le
#print axioms conditionalProjection_error_tolerance

end YMGap.Continuum.BF4ExactSlabBlockConditionalApproximationError
