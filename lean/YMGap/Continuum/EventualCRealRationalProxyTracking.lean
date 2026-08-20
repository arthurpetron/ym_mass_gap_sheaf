/-
M4d -- tail-local rational proxy tracking for constructive-real sequences.

The direct logarithmic comparison is available once a physical separator has
entered its eventual half-window.  Cutoff convergence is likewise a tail
property.  This module makes that match explicit: it shifts every analytic
stream to the named tail, applies the global proxy engine there, and then
transports the resulting modulus-Cauchy datum back to the original sequence.

No finite prefix is assigned an artificial bound, and no Prop-level witness is
converted into modulus data.
-/

import YMGap.Continuum.CRealRationalProxyTracking

namespace YMGap.Continuum.EventualCRealRationalProxyTracking

open YMGap.Constructive
open YMGap.Continuum.CRealRationalProxyTracking
open YMGap.Continuum.SummableCRealEventualStepVariation
open YMGap.Continuum.SummableCRealStepVariation

/-- A modulus-carrying proxy approximation that is required only from a named
outer cutoff onward. -/
structure EventualCRealRationalProxyApproximation
    (s : Nat -> CReal) (proxy error : Nat -> Q') (start : Nat) : Type 1 where
  proxyRate : Nat -> Q' -> Nat
  approximates : forall j : Nat, start <= j -> forall epsilon : Q',
    (0 : Q') < epsilon -> forall k : Nat, proxyRate j epsilon <= k ->
      (s j).approx k <= (proxy j + error j) + epsilon /\
      proxy j <= ((s j).approx k + error j) + epsilon

/-- A two-sided rational proxy step required only on a named cutoff tail. -/
structure RationalTwoSidedTailStep
    (proxy variation : Nat -> Q') (start : Nat) : Type where
  step : forall j : Nat, start <= j ->
    proxy (j + 1) <= proxy j + variation j /\
    proxy j <= proxy (j + 1) + variation j

namespace EventualCRealRationalProxyApproximation

variable {s : Nat -> CReal} {proxy error : Nat -> Q'} {start : Nat}

/-- Reindex an eventual proxy comparison so that its valid tail begins at
index zero. -/
def shifted
    (I : EventualCRealRationalProxyApproximation s proxy error start) :
    CRealRationalProxyApproximation
      (fun j => s (start + j))
      (fun j => proxy (start + j))
      (fun j => error (start + j)) where
  proxyRate := fun j epsilon => I.proxyRate (start + j) epsilon
  approximates := by
    intro j epsilon hepsilon k hk
    exact I.approximates (start + j) (by omega) epsilon hepsilon k hk

/-- Replace the tail proxy by an equivalent rational representative. -/
def proxyEqv
    (I : EventualCRealRationalProxyApproximation s proxy error start)
    {proxy' : Nat -> Q'}
    (hproxy : forall j : Nat, start <= j -> (proxy j).eqv (proxy' j)) :
    EventualCRealRationalProxyApproximation s proxy' error start where
  proxyRate := I.proxyRate
  approximates := by
    intro j hj epsilon hepsilon k hk
    obtain ⟨hupper, hlower⟩ := I.approximates j hj epsilon hepsilon k hk
    have hsum :
        ((proxy j + error j) + epsilon).eqv
          ((proxy' j + error j) + epsilon) :=
      Q'.add_eqv_congr_right _ _ epsilon
        (Q'.add_eqv_congr_right _ _ (error j) (hproxy j hj))
    exact ⟨
      Q'.le_trans' _ _ _ hupper (Q'.le_of_eqv hsum),
      Q'.le_trans' _ _ _ (Q'.ge_of_eqv (hproxy j hj)) hlower⟩

end EventualCRealRationalProxyApproximation

namespace RationalTwoSidedTailStep

variable {proxy variation : Nat -> Q'} {start : Nat}

/-- Shift a tail-local rational step estimate to an all-index estimate. -/
def shifted (step : RationalTwoSidedTailStep proxy variation start) :
    RationalTwoSidedStep
      (fun j => proxy (start + j))
      (fun j => variation (start + j)) where
  step j := step.step (start + j) (by omega)

end RationalTwoSidedTailStep

/-- An antitone tail control remains valid after dropping a finite prefix. -/
def shiftedTailControl
    {variation : Nat -> Q'} (control : AntitoneTailControl variation)
    (start : Nat) :
    AntitoneTailControl (fun j => variation (start + j)) where
  tailRate := control.tailRate
  tailRate_antitone := control.tailRate_antitone
  tailBound := by
    intro epsilon hepsilon tailStart htail length
    have hshiftedRate : control.tailRate epsilon <= start + tailStart :=
      Nat.le_trans htail (by omega)
    have hbound := control.tailBound epsilon hepsilon
      (start + tailStart) hshiftedRate length
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hbound

namespace CReal.ModCauchyEv

/-- A modulus-Cauchy datum for a shifted tail gives one for the original
sequence.  The new outer modulus includes the finite starting offset, while
inner regularity is supplied for the original sequence at every index. -/
def ofShift
    {s : Nat -> CReal} (start : Nat)
    (cauchy : CReal.ModCauchyEv (fun j => s (start + j)))
    (inner : forall j : Nat, CReal.InnerRegularity (s j)) :
    CReal.ModCauchyEv s where
  M := fun epsilon => start + cauchy.M epsilon
  reg := fun j => (inner j).rate
  boundK := fun epsilon m n =>
    cauchy.boundK epsilon (m - start) (n - start)
  bound := by
    intro epsilon hepsilon m n hm hn k hk
    have hstartM : start <= m := Nat.le_trans (Nat.le_add_right _ _) hm
    have hstartN : start <= n := Nat.le_trans (Nat.le_add_right _ _) hn
    have hmTail : cauchy.M epsilon <= m - start := by omega
    have hnTail : cauchy.M epsilon <= n - start := by omega
    have hbound := cauchy.bound epsilon hepsilon
      (m - start) (n - start) hmTail hnTail k hk
    have hmEq : start + (m - start) = m := Nat.add_sub_of_le hstartM
    have hnEq : start + (n - start) = n := Nat.add_sub_of_le hstartN
    simpa only [hmEq, hnEq] using hbound
  regular := by
    intro j epsilon hepsilon p q hp hq
    exact (inner j).regular epsilon hepsilon p q hp hq
  Mmono := by
    intro epsilon delta hdelta hde
    exact Nat.add_le_add_left
      (cauchy.Mmono epsilon delta hdelta hde) start

end CReal.ModCauchyEv

namespace EventualCRealRationalProxyApproximation

variable {s : Nat -> CReal} {proxy proxyVariation error : Nat -> Q'}
    {start : Nat}

/-- Tail-local proxy approximation, tail-local rational dynamics, and
summable full-stream controls construct a modulus-Cauchy datum for the
original unshifted constructive-real sequence. -/
def toModCauchyEv
    (I : EventualCRealRationalProxyApproximation s proxy error start)
    (inner : forall j : Nat, CReal.InnerRegularity (s j))
    (step : RationalTwoSidedTailStep proxy proxyVariation start)
    (proxyVariation_nonnegative : forall j : Nat,
      (0 : Q') <= proxyVariation j)
    (error_nonnegative : forall j : Nat, (0 : Q') <= error j)
    (proxyControl : AntitoneTailControl
      (fun j => proxyVariation (start + j)))
    (errorControl : AntitoneTailControl
      (fun j => error (start + j))) :
    CReal.ModCauchyEv s := by
  let shiftedVariation := I.shifted.toSummableCRealEventualStepVariation
    (fun j => inner (start + j)) step.shifted
    (fun j => proxyVariation_nonnegative (start + j))
    (fun j => error_nonnegative (start + j))
    proxyControl errorControl
  exact CReal.ModCauchyEv.ofShift start shiftedVariation.toModCauchyEv inner

end EventualCRealRationalProxyApproximation

end YMGap.Continuum.EventualCRealRationalProxyTracking

#print axioms YMGap.Continuum.EventualCRealRationalProxyTracking.EventualCRealRationalProxyApproximation.shifted
#print axioms YMGap.Continuum.EventualCRealRationalProxyTracking.shiftedTailControl
#print axioms YMGap.Continuum.EventualCRealRationalProxyTracking.CReal.ModCauchyEv.ofShift
#print axioms YMGap.Continuum.EventualCRealRationalProxyTracking.EventualCRealRationalProxyApproximation.toModCauchyEv
