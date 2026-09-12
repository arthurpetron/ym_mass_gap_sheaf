/-
# Exact cutoff limit for fixed original signed slab observables

The entire twenty-four-face interface pairing stabilizes at its explicit
degree bound. The proof filters the ORIGINAL bounded-label enumeration,
kills exactly the discarded terms, and preserves every retained heat weight.

Together with the boundary recoding this gives an explicitly evaluated
rational CReal limit of the ORIGINAL signed bilinear at extent one. The
quadratic limit is nonnegative for w >= 0. This removes representation
cutoff dependence for each fixed finite boundary observable; it does not
construct a common completed cutoff-limit carrier, geometric time, a strict
gap, arbitrary-volume positivity, or thermodynamic/continuum limits.
-/

import YMGap.Continuum.BF4ExactSlabInterfaceCutoffSelection

namespace YMGap.Continuum.BF4ExactSlabAnchoredCutoffLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactPhysicalPerronReroute
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumMomentExpansion
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabSelectedFaceFold
open YMGap.Continuum.BF4ExactSlabWeightedFaceFactorization
open YMGap.Continuum.BF4ExactSlabObservableHaarForm
open YMGap.Continuum.BF4ExactSlabReflectedObservableHaarForm
open YMGap.Continuum.BF4ExactSlabBoundaryCutoffRecoding
open YMGap.Continuum.BF4ExactSlabInterfaceCutoffSelection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem range_nodup : ∀ n : Nat, (List.range n).Nodup
  | 0 => List.nodup_nil
  | n + 1 => by
    rw [List.range_succ]
    refine List.nodup_append.mpr ⟨range_nodup n,
      List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
    intro x hx y hy hxy
    have hy' := List.mem_singleton.mp hy
    subst y
    subst x
    exact Nat.lt_irrefl n (List.mem_range.mp hx)

theorem fixedFaceIds_nodup (half : Nat) : (centralFixedFaceIds half).Nodup := by
  have hfull : (slabPhysicalFaceEdges (centralExtent half)).Nodup := range_nodup _
  have hparts := (centralSlabFaceIdParts_perm half).symm.nodup hfull
  exact (List.nodup_append.mp (List.nodup_append.mp hparts).1).2.1

theorem centralBoundaryChannels_filter {anchor later : Nat} (hcut : anchor ≤ later) (half : Nat) :
    (centralBoundaryChannels later half).filter (labelWithinB anchor (centralFixedFaceIds half)) =
      centralBoundaryChannels anchor half :=
  boundedEdgeLabellings_filter_cutoff hcut _ (fixedFaceIds_nodup half)

private theorem haar_weighted (blocks : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks p = ratWeightedSum (quaternionHaarMono blocks) p
  | [] => rfl
  | _ :: p => by simp only [quaternionHaar, ratWeightedSum, haar_weighted blocks p]

private theorem mul_sum {A : Type} (p : RatPoly) (f : A → RatPoly) : ∀ xs : List A,
    RatPolyCoeffEqv (polyMul p (finitePolySum f xs)) (finitePolySum (fun a => polyMul p (f a)) xs)
  | [] => RatPolyCoeffEqv.mul_zero_right p
  | _ :: xs => (RatPolyCoeffEqv.mul_add_right _ _ _).trans
      ((RatPolyCoeffEqv.refl _).add (mul_sum p f xs))

private theorem sum_filter {A : Type} (f : A → Q') (test : A → Bool)
    (hz : ∀ a, test a = false → f a ≈ 0) : ∀ xs : List A,
    listQSum f xs ≈ listQSum f (xs.filter test)
  | [] => Q'.eqv_refl _
  | a :: xs => by
    cases ht : test a with
    | false =>
      simp only [List.filter_cons, ht, Bool.false_eq_true, ↓reduceIte]
      exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (hz a ht) (sum_filter f test hz xs))
        (Q'.eqv_of_eq (Q'.zero_add' _))
    | true =>
      simp only [List.filter_cons, ht, ↓reduceIte]
      exact Q'.add_eqv_congr' (Q'.eqv_refl _) (sum_filter f test hz xs)

private theorem sum_congr {A : Type} (f g : A → Q') : ∀ xs : List A,
    (∀ a, a ∈ xs → f a ≈ g a) → listQSum f xs ≈ listQSum g xs
  | [], _ => Q'.eqv_refl _
  | a :: xs, h => Q'.add_eqv_congr' (h a List.mem_cons_self)
      (sum_congr f g xs (fun b hb => h b (List.mem_cons_of_mem a hb)))

/-- Pairing with the ORIGINAL full interface heat insertion. -/
def interfacePairing (w : Q') (K : Nat) (p : RatPoly) : Q' :=
  quaternionHaar 116 (polyMul p (interfaceHeatInsertion w K))

theorem interfacePairing_sum (w : Q') (K : Nat) (p : RatPoly) :
    interfacePairing w K p ≈ listQSum
      (fun boundary => quaternionHaar 116 (polyMul p (interfacePolynomial w K boundary)))
      (centralBoundaryChannels K 0) := by
  refine Q'.eqv_trans _ _ _ ?_ (quaternionHaar_finitePolySum 116 _ _)
  rw [interfacePairing, interfaceHeatInsertion, haar_weighted, haar_weighted]
  exact mul_sum p _ _ (quaternionHaarMono 116)

/-- Joint stabilization: all twenty-four cutoff-dependent heat factors
vary together. The only fixed input is the supported polynomial P. -/
theorem interfacePairing_stable (w : Q') (K : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks 116 p) (hK : interfaceDegreeBound p ≤ K) :
    interfacePairing w K p ≈ interfacePairing w (interfaceDegreeBound p) p := by
  have hfilter := sum_filter
    (fun boundary => quaternionHaar 116 (polyMul p (interfacePolynomial w K boundary)))
    (labelWithinB (interfaceDegreeBound p) (centralFixedFaceIds 0))
    (fun boundary hb => interfacePolynomial_insert_zero w K boundary p hp hb)
    (centralBoundaryChannels K 0)
  rw [centralBoundaryChannels_filter hK 0] at hfilter
  refine Q'.eqv_trans _ _ _ (interfacePairing_sum w K p) ?_
  refine Q'.eqv_trans _ _ _ hfilter ?_
  refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm (interfacePairing_sum w (interfaceDegreeBound p) p))
  apply sum_congr
  intro boundary hb
  rw [interfacePolynomial_cutoff_eq w hK boundary
    (boundedEdgeLabellings_sound _ _ boundary hb).1]
  exact Q'.eqv_refl _

/-- Computed rational limit; the degree bound is an exact modulus. -/
def interfacePairingLimit (w : Q') (p : RatPoly) : CReal :=
  CReal.ofQ' (interfacePairing w (interfaceDegreeBound p) p)

theorem interfacePairingLimit_exact (w : Q') (K : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks 116 p) (hK : interfaceDegreeBound p ≤ K) (precision : Nat) :
    interfacePairing w K p ≈ (interfacePairingLimit w p).approx precision :=
  interfacePairing_stable w K p hp hK

private theorem fold_supported {A : Type} (f : A → RatPoly)
    (h : ∀ a, SupportedQuaternionBlocks 116 (f a)) : ∀ xs : List A,
    SupportedQuaternionBlocks 116 (xs.foldr (fun a p => polyMul (f a) p) polyOne)
  | [] => by
    intro t ht
    have he := List.mem_singleton.mp ht
    subst t
    exact Nat.zero_le _
  | a :: xs => supported_polyMul (h a) (fold_supported f h xs)

private theorem sum_supported {A : Type} (f : A → RatPoly)
    (h : ∀ a, SupportedQuaternionBlocks 116 (f a)) : ∀ xs : List A,
    SupportedQuaternionBlocks 116 (finitePolySum f xs)
  | [] => fun _ hm => False.elim (List.not_mem_nil hm)
  | a :: xs => fun t ht => (List.mem_append.mp ht).elim (h a t) (sum_supported f h xs t)

private theorem smul_supported {p : RatPoly} (hp : SupportedQuaternionBlocks 116 p) (a : Q') :
    SupportedQuaternionBlocks 116 (polySmul a p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem weighted_supported (w : Q') (K : Nat) (state : EdgeLabelling) (id : Nat) :
    SupportedQuaternionBlocks 116 (weightedFacePolynomial w K state id) := by
  apply smul_supported
  have h := correctedSlabPlaquetteSpinFactor_support 1 (fun _ => state id) (slabPlaquetteAt 1 id)
  rw [correctedSlabLinks_extent_one_length] at h
  exact h

theorem upperObservable_support (w : Q') (K : Nat) (c : EdgeLabelling → Q') :
    SupportedQuaternionBlocks 116 (upperObservable w K c) := by
  apply sum_supported
  intro state
  apply smul_supported
  rw [upperPolynomial_eq_fold]
  exact fold_supported _ (weighted_supported w K _) _

/-- Both ORIGINAL boundary polynomials, at their fixed anchor cutoff. -/
def boundaryMultiplier (w : Q') (anchor : Nat) (a b : EdgeLabelling → Q') : RatPoly :=
  polyMul (lowerObservable w anchor a) (upperObservable w anchor b)

theorem boundaryMultiplier_support (w : Q') (anchor : Nat) (a b : EdgeLabelling → Q') :
    SupportedQuaternionBlocks 116 (boundaryMultiplier w anchor a b) :=
  supported_polyMul (lowerObservable_support w anchor a) (upperObservable_support w anchor b)

theorem anchoredIntegrand_haar_eq_interfacePairing (w : Q') (anchor later : Nat)
    (a b : EdgeLabelling → Q') :
    quaternionHaar 116 (anchoredIntegrand w anchor later a b) ≈
      interfacePairing w later (boundaryMultiplier w anchor a b) :=
  Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_middle_comm 116 _ _ _)
    (Q'.eqv_symm (quaternionHaar_polyMul_assoc 116 _ _ _))

/-- The original finite signed bilinear evaluated on the fixed boundary
observable's explicit zero extension. No new kernel is introduced. -/
def exactCutoffPairing (w : Q') (anchor later : Nat) (a b : EdgeLabelling → Q') : Q' :=
  finiteJointBilinear (centralHalfStates later 0) (boundaryExtension anchor 0 a) (boundaryExtension anchor 0 b)
    (exactCorrectedSlabReflectedKernel w later 0)

def exactCutoffPairingModulus (w : Q') (anchor : Nat) (a b : EdgeLabelling → Q') : Nat :=
  max anchor (interfaceDegreeBound (boundaryMultiplier w anchor a b))

def exactCutoffPairingValue (w : Q') (anchor : Nat) (a b : EdgeLabelling → Q') : Q' :=
  interfacePairing w (interfaceDegreeBound (boundaryMultiplier w anchor a b)) (boundaryMultiplier w anchor a b)

theorem exactCutoffPairing_stable (w : Q') (anchor later : Nat) (a b : EdgeLabelling → Q')
    (hlater : exactCutoffPairingModulus w anchor a b ≤ later) :
    exactCutoffPairing w anchor later a b ≈ exactCutoffPairingValue w anchor a b := by
  have ha : anchor ≤ later := Nat.le_trans (Nat.le_max_left _ _) hlater
  have hi : interfaceDegreeBound (boundaryMultiplier w anchor a b) ≤ later :=
    Nat.le_trans (Nat.le_max_right _ _) hlater
  exact Q'.eqv_trans _ _ _ (exact_bilinear_anchored w ha a b)
    (Q'.eqv_trans _ _ _ (anchoredIntegrand_haar_eq_interfacePairing w anchor later a b)
      (interfacePairing_stable w later _ (boundaryMultiplier_support w anchor a b) hi))

/-- Explicit CReal with exact stabilization modulus, for the SAME signed
bilinear and fixed finite boundary observables. -/
def exactCutoffPairingLimit (w : Q') (anchor : Nat) (a b : EdgeLabelling → Q') : CReal :=
  CReal.ofQ' (exactCutoffPairingValue w anchor a b)

theorem exactCutoffPairingLimit_exact (w : Q') (anchor later : Nat) (a b : EdgeLabelling → Q')
    (hlater : exactCutoffPairingModulus w anchor a b ≤ later) (precision : Nat) :
    exactCutoffPairing w anchor later a b ≈ (exactCutoffPairingLimit w anchor a b).approx precision :=
  exactCutoffPairing_stable w anchor later a b hlater

/-- Positivity passes through an exact equality at the computed cutoff;
no limit-order principle or analytic positivity premise is required. -/
theorem exactCutoffPairingValue_nonnegative {w : Q'} (hw : (0 : Q') ≤ w)
    (anchor : Nat) (c : EdgeLabelling → Q') :
    (0 : Q') ≤ exactCutoffPairingValue w anchor c c := by
  let K := exactCutoffPairingModulus w anchor c c
  have ha : anchor ≤ K := Nat.le_max_left _ _
  have hq := anchored_quadratic_nonnegative hw ha c
  have he := Q'.eqv_trans _ _ _ (anchoredIntegrand_haar_eq_interfacePairing w anchor K c c)
    (interfacePairing_stable w K _ (boundaryMultiplier_support w anchor c c) (Nat.le_max_right _ _))
  exact Q'.le_trans' _ _ _ hq (Q'.le_of_eqv he)

end YMGap.Continuum.BF4ExactSlabAnchoredCutoffLimit

#print axioms YMGap.Continuum.BF4ExactSlabAnchoredCutoffLimit.fixedFaceIds_nodup
#print axioms YMGap.Continuum.BF4ExactSlabAnchoredCutoffLimit.centralBoundaryChannels_filter
#print axioms YMGap.Continuum.BF4ExactSlabAnchoredCutoffLimit.interfacePairing
#print axioms YMGap.Continuum.BF4ExactSlabAnchoredCutoffLimit.interfacePairing_sum
#print axioms YMGap.Continuum.BF4ExactSlabAnchoredCutoffLimit.interfacePairing_stable
#print axioms YMGap.Continuum.BF4ExactSlabAnchoredCutoffLimit.interfacePairingLimit
#print axioms YMGap.Continuum.BF4ExactSlabAnchoredCutoffLimit.interfacePairingLimit_exact
#print axioms YMGap.Continuum.BF4ExactSlabAnchoredCutoffLimit.upperObservable_support
#print axioms YMGap.Continuum.BF4ExactSlabAnchoredCutoffLimit.boundaryMultiplier
#print axioms YMGap.Continuum.BF4ExactSlabAnchoredCutoffLimit.boundaryMultiplier_support
#print axioms YMGap.Continuum.BF4ExactSlabAnchoredCutoffLimit.anchoredIntegrand_haar_eq_interfacePairing
#print axioms YMGap.Continuum.BF4ExactSlabAnchoredCutoffLimit.exactCutoffPairing
#print axioms YMGap.Continuum.BF4ExactSlabAnchoredCutoffLimit.exactCutoffPairingModulus
#print axioms YMGap.Continuum.BF4ExactSlabAnchoredCutoffLimit.exactCutoffPairingValue
#print axioms YMGap.Continuum.BF4ExactSlabAnchoredCutoffLimit.exactCutoffPairing_stable
#print axioms YMGap.Continuum.BF4ExactSlabAnchoredCutoffLimit.exactCutoffPairingLimit
#print axioms YMGap.Continuum.BF4ExactSlabAnchoredCutoffLimit.exactCutoffPairingLimit_exact
#print axioms YMGap.Continuum.BF4ExactSlabAnchoredCutoffLimit.exactCutoffPairingValue_nonnegative
