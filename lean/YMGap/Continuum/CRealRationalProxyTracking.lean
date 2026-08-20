/-
Constructive bridge from rational proxy dynamics to eventual step control for
a sequence of constructive reals.

The bridge deliberately separates two statements that are often conflated:

* a modulus-carrying identification of each represented real with its rational
  proxy; and
* a two-sided rational one-step estimate.

Each proxy identification is used at tolerance `epsilon/2`.  The maximum of
the two computed approximation thresholds handles a consecutive pair, and
the two half-errors recombine to `epsilon`.  No modulus is extracted from a
`Prop`-level existential.
-/

import YMGap.Constructive.CRealInnerRegularity
import YMGap.Continuum.SummableCRealEventualStepVariation

namespace YMGap.Continuum.CRealRationalProxyTracking

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.SummableCRealEventualStepVariation
open YMGap.Continuum.SummableCRealStepVariation

/-- Type-level, modulus-carrying identification of each constructive real in
`s` with a rational proxy. -/
structure CRealRationalProxyIdentification
    (s : Nat -> CReal) (proxy : Nat -> Q') : Type 1 where
  proxyRate : Nat -> Q' -> Nat
  approximates : forall j : Nat, forall epsilon : Q',
    (0 : Q') < epsilon -> forall k : Nat, proxyRate j epsilon <= k ->
      (s j).approx k <= proxy j + epsilon /\
      proxy j <= (s j).approx k + epsilon

/-- Type-level, modulus-carrying comparison of a represented real with a
rational proxy up to an explicit finite-spacing error.  The error is kept
outside the requested approximation tolerance so that it can later be
charged to its own summable budget. -/
structure CRealRationalProxyApproximation
    (s : Nat -> CReal) (proxy error : Nat -> Q') : Type 1 where
  proxyRate : Nat -> Q' -> Nat
  approximates : forall j : Nat, forall epsilon : Q',
    (0 : Q') < epsilon -> forall k : Nat, proxyRate j epsilon <= k ->
      (s j).approx k <= (proxy j + error j) + epsilon /\
      proxy j <= ((s j).approx k + error j) + epsilon

/-- A rational proxy moves by at most `variation` in either direction at one
cutoff step. -/
structure RationalTwoSidedStep
    (proxy variation : Nat -> Q') : Type where
  step : forall j : Nat,
    proxy (j + 1) <= proxy j + variation j /\
    proxy j <= proxy (j + 1) + variation j

/-- The variation seen by represented reals when both endpoint proxy errors
and the rational-proxy step variation are exposed. -/
def proxyErrorVariation (proxyVariation error : Nat -> Q') (j : Nat) : Q' :=
  error j + (proxyVariation j + error (j + 1))

namespace CRealRationalProxyIdentification

variable {s : Nat -> CReal} {proxy variation : Nat -> Q'}

/-- Approximation tolerance assigned to each endpoint of a rational-proxy
comparison. -/
def endpointTolerance (epsilon : Q') : Q' :=
  HalfPow.half * epsilon

/-- Both endpoint approximation thresholds are met after their finite maximum. -/
def consecutiveRate
    (I : CRealRationalProxyIdentification s proxy)
    (j : Nat) (epsilon : Q') : Nat :=
  max
    (I.proxyRate j (endpointTolerance epsilon))
    (I.proxyRate (j + 1) (endpointTolerance epsilon))

/-- Reassociate two endpoint half-errors around an intervening variation. -/
theorem two_endpoint_tolerances_eqv
    (a variation epsilon : Q') :
    (((a + endpointTolerance epsilon) + variation) +
        endpointTolerance epsilon).eqv
      ((a + variation) + epsilon) := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv
      (a + endpointTolerance epsilon) variation
      (endpointTolerance epsilon)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_swap_inner a (endpointTolerance epsilon) variation
      (endpointTolerance epsilon)) ?_
  exact Q'.add_eqv_congr_left (a + variation)
    (endpointTolerance epsilon + endpointTolerance epsilon) epsilon
    (ExpNeg.two_halves epsilon)

/-- Modulus-carrying proxy identification plus a two-sided rational step bound
constructs the eventual consecutive-step tracking required by cutoff removal.
The inner regularity of the represented reals remains independently supplied
as computable data. -/
def toCRealEventualStepTracking
    (I : CRealRationalProxyIdentification s proxy)
    (inner : forall j : Nat, CReal.InnerRegularity (s j))
    (step : RationalTwoSidedStep proxy variation) :
    CRealEventualStepTracking s variation where
  innerRate j := (inner j).rate
  innerRegular := by
    intro j epsilon hepsilon p q hp hq
    exact (inner j).regular epsilon hepsilon p q hp hq
  stepRate := I.consecutiveRate
  stepBound := by
    intro j epsilon hepsilon k hk
    let q := endpointTolerance epsilon
    have hq : (0 : Q') < q := ExpNeg.half_mul_pos epsilon hepsilon
    have hj : I.proxyRate j q <= k :=
      Nat.le_trans (Nat.le_max_left _ _) hk
    have hnext : I.proxyRate (j + 1) q <= k :=
      Nat.le_trans (Nat.le_max_right _ _) hk
    obtain ⟨hjUpper, hjLower⟩ := I.approximates j q hq k hj
    obtain ⟨hnextUpper, hnextLower⟩ :=
      I.approximates (j + 1) q hq k hnext
    obtain ⟨hstepBack, hstepForward⟩ := step.step j
    constructor
    · have hproxy : proxy (j + 1) + q <=
          (proxy j + variation j) + q :=
        Q'.add_le_add_right _ _ q hstepBack
      have hjWithVariation : proxy j + variation j <=
          ((s j).approx k + q) + variation j :=
        Q'.add_le_add_right _ _ (variation j) hjLower
      have hjWithVariationAndSlack :
          (proxy j + variation j) + q <=
            (((s j).approx k + q) + variation j) + q :=
        Q'.add_le_add_right _ _ q hjWithVariation
      exact Q'.le_trans' _ _ _ hnextUpper
        (Q'.le_trans' _ _ _ hproxy
          (Q'.le_trans' _ _ _ hjWithVariationAndSlack
            (Q'.le_of_eqv
              (two_endpoint_tolerances_eqv
                ((s j).approx k) (variation j) epsilon))))
    · have hproxy : proxy j + q <=
          (proxy (j + 1) + variation j) + q :=
        Q'.add_le_add_right _ _ q hstepForward
      have hnextWithVariation : proxy (j + 1) + variation j <=
          ((s (j + 1)).approx k + q) + variation j :=
        Q'.add_le_add_right _ _ (variation j) hnextLower
      have hnextWithVariationAndSlack :
          (proxy (j + 1) + variation j) + q <=
            (((s (j + 1)).approx k + q) + variation j) + q :=
        Q'.add_le_add_right _ _ q hnextWithVariation
      exact Q'.le_trans' _ _ _ hjUpper
        (Q'.le_trans' _ _ _ hproxy
          (Q'.le_trans' _ _ _ hnextWithVariationAndSlack
            (Q'.le_of_eqv
              (two_endpoint_tolerances_eqv
                ((s (j + 1)).approx k) (variation j) epsilon))))

end CRealRationalProxyIdentification

namespace CRealRationalProxyApproximation

variable {s : Nat -> CReal} {proxy proxyVariation error : Nat -> Q'}

/-- Replace a rational proxy by a pointwise equivalent representative without
changing either the approximation modulus or the explicit error stream. -/
def proxyEqv
    (I : CRealRationalProxyApproximation s proxy error)
    {proxy' : Nat -> Q'}
    (hproxy : forall j : Nat, (proxy j).eqv (proxy' j)) :
    CRealRationalProxyApproximation s proxy' error where
  proxyRate := I.proxyRate
  approximates := by
    intro j epsilon hepsilon k hk
    obtain ⟨hupper, hlower⟩ := I.approximates j epsilon hepsilon k hk
    have hsum :
        ((proxy j + error j) + epsilon).eqv
          ((proxy' j + error j) + epsilon) :=
      Q'.add_eqv_congr_right _ _ epsilon
        (Q'.add_eqv_congr_right _ _ (error j) (hproxy j))
    exact ⟨
      Q'.le_trans' _ _ _ hupper (Q'.le_of_eqv hsum),
      Q'.le_trans' _ _ _ (Q'.ge_of_eqv (hproxy j)) hlower⟩

/-- A quarter of the global tail tolerance, assigned to each endpoint error
stream. -/
def endpointTailTolerance (epsilon : Q') : Q' :=
  HalfPow.half * (HalfPow.half * epsilon)

theorem endpointTailTolerance_pos (epsilon : Q')
    (hepsilon : (0 : Q') < epsilon) :
    (0 : Q') < endpointTailTolerance epsilon :=
  ExpNeg.half_mul_pos (HalfPow.half * epsilon)
    (ExpNeg.half_mul_pos epsilon hepsilon)

/-- The two endpoint quarters and proxy-step half exactly refill the global
tail tolerance, up to rational representation equivalence. -/
theorem endpoint_half_endpoint_eqv (epsilon : Q') :
    (endpointTailTolerance epsilon +
      ((HalfPow.half * epsilon) + endpointTailTolerance epsilon)).eqv
    epsilon := by
  let q := endpointTailTolerance epsilon
  let h := HalfPow.half * epsilon
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv q h q)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_comm_eqv (q + h) q) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv q q h)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right (q + q) h h
      (ExpNeg.two_halves h)) ?_
  exact ExpNeg.two_halves epsilon

/-- Constructive antitone tail control for the combined represented-real
variation.  Half of the requested tail tolerance is assigned to the rational
proxy step, and one quarter to each occurrence of the endpoint proxy error.
The same error modulus controls the shifted endpoint because `start + 1` is
later than `start`. -/
def proxyErrorTailControl
    (proxyControl : AntitoneTailControl proxyVariation)
    (errorControl : AntitoneTailControl error) :
    AntitoneTailControl (proxyErrorVariation proxyVariation error) where
  tailRate epsilon :=
    max
      (proxyControl.tailRate (HalfPow.half * epsilon))
      (errorControl.tailRate (endpointTailTolerance epsilon))
  tailRate_antitone := by
    intro epsilon delta hdelta hde
    have hhalfDelta : (0 : Q') < HalfPow.half * delta :=
      ExpNeg.half_mul_pos delta hdelta
    have hquarterDelta : (0 : Q') < endpointTailTolerance delta :=
      endpointTailTolerance_pos delta hdelta
    have hhalfMono : HalfPow.half * delta <= HalfPow.half * epsilon :=
      Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half hde
        HalfPow.half_nonneg
    have hquarterMono : endpointTailTolerance delta <=
        endpointTailTolerance epsilon := by
      unfold endpointTailTolerance
      exact Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half hhalfMono
        HalfPow.half_nonneg
    exact Nat.max_le.mpr ⟨
      Nat.le_trans
        (proxyControl.tailRate_antitone
          (HalfPow.half * epsilon) (HalfPow.half * delta)
          hhalfDelta hhalfMono)
        (Nat.le_max_left _ _),
      Nat.le_trans
        (errorControl.tailRate_antitone
          (endpointTailTolerance epsilon) (endpointTailTolerance delta)
          hquarterDelta hquarterMono)
        (Nat.le_max_right _ _)⟩
  tailBound := by
    intro epsilon hepsilon start hstart length
    let halfEpsilon := HalfPow.half * epsilon
    let quarterEpsilon := endpointTailTolerance epsilon
    have hhalf : (0 : Q') < halfEpsilon :=
      ExpNeg.half_mul_pos epsilon hepsilon
    have hquarter : (0 : Q') < quarterEpsilon :=
      endpointTailTolerance_pos epsilon hepsilon
    have hproxyStart : proxyControl.tailRate halfEpsilon <= start :=
      Nat.le_trans (Nat.le_max_left _ _) hstart
    have herrorStart : errorControl.tailRate quarterEpsilon <= start :=
      Nat.le_trans (Nat.le_max_right _ _) hstart
    have herrorStartShift : errorControl.tailRate quarterEpsilon <= start + 1 :=
      Nat.le_trans herrorStart (by omega)
    have hproxy := proxyControl.tailBound halfEpsilon hhalf
      start hproxyStart length
    have herrorNow := errorControl.tailBound quarterEpsilon hquarter
      start herrorStart length
    have herrorNextRaw := errorControl.tailBound quarterEpsilon hquarter
      (start + 1) herrorStartShift length
    have herrorNext :
        finSum (fun offset => error ((start + offset) + 1)) length <=
          quarterEpsilon := by
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        herrorNextRaw
    have hsplit :
        finSum
            (fun offset =>
              proxyErrorVariation proxyVariation error (start + offset))
            length <=
          finSum (fun offset => error (start + offset)) length +
            (finSum (fun offset => proxyVariation (start + offset)) length +
              finSum (fun offset => error ((start + offset) + 1)) length) := by
      refine Q'.le_of_eqv ?_
      refine Q'.eqv_trans _ _ _
        (finSum_add
          (fun offset => error (start + offset))
          (fun offset =>
            proxyVariation (start + offset) + error ((start + offset) + 1))
          length) ?_
      exact Q'.add_eqv_congr_left _ _ _
        (finSum_add
          (fun offset => proxyVariation (start + offset))
          (fun offset => error ((start + offset) + 1)) length)
    have hboundErrorNow :
        finSum (fun offset => error (start + offset)) length +
            (finSum (fun offset => proxyVariation (start + offset)) length +
              finSum (fun offset => error ((start + offset) + 1)) length) <=
          quarterEpsilon +
            (finSum (fun offset => proxyVariation (start + offset)) length +
              finSum (fun offset => error ((start + offset) + 1)) length) :=
      Q'.add_le_add_right _ _ _ herrorNow
    have hboundProxyInner :
        finSum (fun offset => proxyVariation (start + offset)) length +
            finSum (fun offset => error ((start + offset) + 1)) length <=
          halfEpsilon +
            finSum (fun offset => error ((start + offset) + 1)) length :=
      Q'.add_le_add_right _ _ _ hproxy
    have hboundProxy :
        quarterEpsilon +
            (finSum (fun offset => proxyVariation (start + offset)) length +
              finSum (fun offset => error ((start + offset) + 1)) length) <=
          quarterEpsilon +
            (halfEpsilon +
              finSum (fun offset => error ((start + offset) + 1)) length) :=
      Q'.add_le_add_left _ _ _ hboundProxyInner
    have hboundErrorNextInner :
        halfEpsilon +
            finSum (fun offset => error ((start + offset) + 1)) length <=
          halfEpsilon + quarterEpsilon :=
      Q'.add_le_add_left _ _ _ herrorNext
    have hboundErrorNext :
        quarterEpsilon +
            (halfEpsilon +
              finSum (fun offset => error ((start + offset) + 1)) length) <=
          quarterEpsilon + (halfEpsilon + quarterEpsilon) :=
      Q'.add_le_add_left _ _ _ hboundErrorNextInner
    exact Q'.le_trans' _ _ _ hsplit
      (Q'.le_trans' _ _ _ hboundErrorNow
        (Q'.le_trans' _ _ _ hboundProxy
          (Q'.le_trans' _ _ _ hboundErrorNext
            (Q'.le_of_eqv (endpoint_half_endpoint_eqv epsilon)))))

/-- Both error-aware endpoint approximation thresholds are met after their
finite maximum. -/
def consecutiveRate
    (I : CRealRationalProxyApproximation s proxy error)
    (j : Nat) (epsilon : Q') : Nat :=
  max
    (I.proxyRate j
      (CRealRationalProxyIdentification.endpointTolerance epsilon))
    (I.proxyRate (j + 1)
      (CRealRationalProxyIdentification.endpointTolerance epsilon))

/-- Reassociate the two endpoint proxy errors and the two half-tolerances into
the explicit combined variation plus one requested tolerance. -/
theorem two_endpoint_errors_eqv
    (a errorNow variation errorNext epsilon : Q') :
    (((((a + errorNow) +
          CRealRationalProxyIdentification.endpointTolerance epsilon) +
        variation) + errorNext) +
      CRealRationalProxyIdentification.endpointTolerance epsilon).eqv
    ((a + (errorNow + (variation + errorNext))) + epsilon) := by
  let q := CRealRationalProxyIdentification.endpointTolerance epsilon
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv (((a + errorNow) + q) + variation) errorNext q) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv ((a + errorNow) + q) variation (errorNext + q)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left ((a + errorNow) + q) _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv variation errorNext q))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_swap_inner (a + errorNow) q (variation + errorNext) q) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ (q + q)
      (Q'.add_assoc_eqv a errorNow (variation + errorNext))) ?_
  exact Q'.add_eqv_congr_left
    (a + (errorNow + (variation + errorNext))) (q + q) epsilon
    (ExpNeg.two_halves epsilon)

/-- The same endpoint-error reassociation with the endpoint errors presented
in the opposite order, as occurs in the reverse step inequality. -/
theorem two_endpoint_errors_swapped_eqv
    (a errorNow variation errorNext epsilon : Q') :
    (((((a + errorNext) +
          CRealRationalProxyIdentification.endpointTolerance epsilon) +
        variation) + errorNow) +
      CRealRationalProxyIdentification.endpointTolerance epsilon).eqv
    ((a + (errorNow + (variation + errorNext))) + epsilon) := by
  refine Q'.eqv_trans _ _ _
    (two_endpoint_errors_eqv a errorNext variation errorNow epsilon) ?_
  refine Q'.add_eqv_congr_right _ _ epsilon ?_
  refine Q'.add_eqv_congr_left a _ _ ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv errorNext variation errorNow)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_comm_eqv (errorNext + variation) errorNow) ?_
  exact Q'.add_eqv_congr_left errorNow _ _
    (Q'.add_comm_eqv errorNext variation)

/-- An error-aware proxy comparison and a two-sided rational proxy step bound
construct eventual represented-real step tracking.  The resulting variation
records both endpoint proxy errors explicitly; only the arbitrarily requested
slack is absorbed into `epsilon`. -/
def toCRealEventualStepTracking
    (I : CRealRationalProxyApproximation s proxy error)
    (inner : forall j : Nat, CReal.InnerRegularity (s j))
    (step : RationalTwoSidedStep proxy proxyVariation) :
    CRealEventualStepTracking s
      (proxyErrorVariation proxyVariation error) where
  innerRate j := (inner j).rate
  innerRegular := by
    intro j epsilon hepsilon p q hp hq
    exact (inner j).regular epsilon hepsilon p q hp hq
  stepRate := I.consecutiveRate
  stepBound := by
    intro j epsilon hepsilon k hk
    let q := CRealRationalProxyIdentification.endpointTolerance epsilon
    have hq : (0 : Q') < q := ExpNeg.half_mul_pos epsilon hepsilon
    have hj : I.proxyRate j q <= k :=
      Nat.le_trans (Nat.le_max_left _ _) hk
    have hnext : I.proxyRate (j + 1) q <= k :=
      Nat.le_trans (Nat.le_max_right _ _) hk
    obtain ⟨hjUpper, hjLower⟩ := I.approximates j q hq k hj
    obtain ⟨hnextUpper, hnextLower⟩ :=
      I.approximates (j + 1) q hq k hnext
    obtain ⟨hstepBack, hstepForward⟩ := step.step j
    constructor
    · have hproxyWithError :
          proxy (j + 1) + error (j + 1) <=
            (proxy j + proxyVariation j) + error (j + 1) :=
        Q'.add_le_add_right _ _ _ hstepBack
      have hproxyWithErrorAndSlack :
          (proxy (j + 1) + error (j + 1)) + q <=
            ((proxy j + proxyVariation j) + error (j + 1)) + q :=
        Q'.add_le_add_right _ _ q hproxyWithError
      have hjWithVariation :
          proxy j + proxyVariation j <=
            (((s j).approx k + error j) + q) + proxyVariation j :=
        Q'.add_le_add_right _ _ (proxyVariation j) hjLower
      have hjWithErrors :
          (proxy j + proxyVariation j) + error (j + 1) <=
            ((((s j).approx k + error j) + q) + proxyVariation j) +
              error (j + 1) :=
        Q'.add_le_add_right _ _ (error (j + 1)) hjWithVariation
      have hjWithErrorsAndSlack :
          ((proxy j + proxyVariation j) + error (j + 1)) + q <=
            (((((s j).approx k + error j) + q) + proxyVariation j) +
              error (j + 1)) + q :=
        Q'.add_le_add_right _ _ q hjWithErrors
      exact Q'.le_trans' _ _ _ hnextUpper
        (Q'.le_trans' _ _ _ hproxyWithErrorAndSlack
          (Q'.le_trans' _ _ _ hjWithErrorsAndSlack
            (Q'.le_of_eqv
              (two_endpoint_errors_eqv ((s j).approx k) (error j)
                (proxyVariation j) (error (j + 1)) epsilon))))
    · have hproxyWithError :
          proxy j + error j <=
            (proxy (j + 1) + proxyVariation j) + error j :=
        Q'.add_le_add_right _ _ _ hstepForward
      have hproxyWithErrorAndSlack :
          (proxy j + error j) + q <=
            ((proxy (j + 1) + proxyVariation j) + error j) + q :=
        Q'.add_le_add_right _ _ q hproxyWithError
      have hnextWithVariation :
          proxy (j + 1) + proxyVariation j <=
            (((s (j + 1)).approx k + error (j + 1)) + q) +
              proxyVariation j :=
        Q'.add_le_add_right _ _ (proxyVariation j) hnextLower
      have hnextWithErrors :
          (proxy (j + 1) + proxyVariation j) + error j <=
            ((((s (j + 1)).approx k + error (j + 1)) + q) +
              proxyVariation j) + error j :=
        Q'.add_le_add_right _ _ (error j) hnextWithVariation
      have hnextWithErrorsAndSlack :
          ((proxy (j + 1) + proxyVariation j) + error j) + q <=
            (((((s (j + 1)).approx k + error (j + 1)) + q) +
              proxyVariation j) + error j) + q :=
        Q'.add_le_add_right _ _ q hnextWithErrors
      exact Q'.le_trans' _ _ _ hjUpper
        (Q'.le_trans' _ _ _ hproxyWithErrorAndSlack
          (Q'.le_trans' _ _ _ hnextWithErrorsAndSlack
            (Q'.le_of_eqv
              (two_endpoint_errors_swapped_eqv ((s (j + 1)).approx k)
                (error j) (proxyVariation j) (error (j + 1)) epsilon))))

/-- Complete the error-aware proxy route to a summable represented-real step
package.  Pointwise nonnegativity and antitone tail controls remain visibly
separate for the rational proxy variation and the finite-spacing proxy error;
the local comparison is supplied by `toCRealEventualStepTracking`. -/
def toSummableCRealEventualStepVariation
    (I : CRealRationalProxyApproximation s proxy error)
    (inner : forall j : Nat, CReal.InnerRegularity (s j))
    (step : RationalTwoSidedStep proxy proxyVariation)
    (proxyVariation_nonnegative : forall j : Nat,
      (0 : Q') <= proxyVariation j)
    (error_nonnegative : forall j : Nat, (0 : Q') <= error j)
    (proxyControl : AntitoneTailControl proxyVariation)
    (errorControl : AntitoneTailControl error) :
    SummableCRealEventualStepVariation s := by
  let localTracking := I.toCRealEventualStepTracking inner step
  let tailControl := proxyErrorTailControl proxyControl errorControl
  exact
    { variation := proxyErrorVariation proxyVariation error
      variation_nonnegative := by
        intro j
        exact Q'.zero_le_add _ _ (error_nonnegative j)
          (Q'.zero_le_add _ _ (proxyVariation_nonnegative j)
            (error_nonnegative (j + 1)))
      tailRate := tailControl.tailRate
      tailRate_antitone := tailControl.tailRate_antitone
      tailBound := tailControl.tailBound
      innerRate := localTracking.innerRate
      innerRegular := localTracking.innerRegular
      stepRate := localTracking.stepRate
      stepBound := localTracking.stepBound }

end CRealRationalProxyApproximation

end YMGap.Continuum.CRealRationalProxyTracking

#print axioms YMGap.Continuum.CRealRationalProxyTracking.CRealRationalProxyIdentification.two_endpoint_tolerances_eqv
#print axioms YMGap.Continuum.CRealRationalProxyTracking.CRealRationalProxyIdentification.toCRealEventualStepTracking
#print axioms YMGap.Continuum.CRealRationalProxyTracking.CRealRationalProxyApproximation.proxyEqv
#print axioms YMGap.Continuum.CRealRationalProxyTracking.CRealRationalProxyApproximation.two_endpoint_errors_eqv
#print axioms YMGap.Continuum.CRealRationalProxyTracking.CRealRationalProxyApproximation.two_endpoint_errors_swapped_eqv
#print axioms YMGap.Continuum.CRealRationalProxyTracking.CRealRationalProxyApproximation.proxyErrorTailControl
#print axioms YMGap.Continuum.CRealRationalProxyTracking.CRealRationalProxyApproximation.toCRealEventualStepTracking
#print axioms YMGap.Continuum.CRealRationalProxyTracking.CRealRationalProxyApproximation.toSummableCRealEventualStepVariation
