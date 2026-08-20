/-
M2m -- constructive finite-prefix / asymptotic-tail gluing for the exact
full-range logarithmic rate ceiling.

The lower BF4 route is now uniform at every cutoff.  For the independent upper
bound, the natural proof architecture is different: certify the finitely many
early cutoffs by an exact finite argument and prove one uniform estimate on
the asymptotic tail.  Their rational ceilings can then be joined by the
located maximum in `Q'`.

This module formalizes precisely that last gluing step.  It does not manufacture
either analytic input.  In particular, the tail record is the genuine uniform
weak-coupling/log-rate obligation, while the prefix record is finite but still
must refer to the same exact rate family.
-/

import YMGap.Continuum.PhysicalSeparatorFullLogComparison

namespace YMGap.Continuum.PhysicalSeparatorFullLogComparison

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.PhysicalSeparatorFullLogRate

variable {P : PhysicalSeparator}
    {F : FullRangeExactPhysicalLogRateFamily P}

/-- One rational ceiling for all exact rates strictly before `start`.  This is
the finite, kernel-checkable side of the upper-bound proof. -/
structure PrefixFullRangeLogRateCeiling
    (F : FullRangeExactPhysicalLogRateFamily P) (start : Nat) : Type where
  ceiling : Q'
  prefix_bound : forall j : Nat, j < start ->
    CReal.leEv (F.rate j) (CReal.ofQ' ceiling)

/-- One rational ceiling for all exact rates from `start` onward.  This is the
uniform analytic tail side of the upper-bound proof. -/
structure TailFullRangeLogRateCeiling
    (F : FullRangeExactPhysicalLogRateFamily P) (start : Nat) : Type where
  ceiling : Q'
  tail_bound : forall j : Nat, start <= j ->
    CReal.leEv (F.rate j) (CReal.ofQ' ceiling)

namespace PrefixFullRangeLogRateCeiling

variable {start : Nat}

/-- The located rational maximum of the finite-prefix and tail ceilings. -/
def gluedCeiling
    (H : PrefixFullRangeLogRateCeiling F start)
    (T : TailFullRangeLogRateCeiling F start) : Q' :=
  Q'.max' H.ceiling T.ceiling

/-- **Prefix/tail upper-bound gluing.**  Exact bounds on the two decidable
regions combine into a single finite ceiling for the whole rate family. -/
def glue
    (H : PrefixFullRangeLogRateCeiling F start)
    (T : TailFullRangeLogRateCeiling F start) :
    FullRangeLogRateCeiling F where
  ceiling := H.gluedCeiling T
  ceiling_bound := fun j => by
    rcases Nat.lt_or_ge j start with hj | hj
    · have hprefix := H.prefix_bound j hj
      have hlift :
          CReal.leEv (CReal.ofQ' H.ceiling)
            (CReal.ofQ' (Q'.max' H.ceiling T.ceiling)) :=
        CReal.leEv_of_le
          (CReal.ofQ'_le_ofQ' (Q'.le_max'_left H.ceiling T.ceiling))
      exact CReal.leEv_trans hprefix hlift
    · have htail := T.tail_bound j hj
      have hlift :
          CReal.leEv (CReal.ofQ' T.ceiling)
            (CReal.ofQ' (Q'.max' H.ceiling T.ceiling)) :=
        CReal.leEv_of_le
          (CReal.ofQ'_le_ofQ' (Q'.le_max'_right H.ceiling T.ceiling))
      exact CReal.leEv_trans htail hlift

@[simp] theorem glue_ceiling
    (H : PrefixFullRangeLogRateCeiling F start)
    (T : TailFullRangeLogRateCeiling F start) :
    (H.glue T).ceiling = Q'.max' H.ceiling T.ceiling := rfl

theorem prefix_ceiling_le_glue
    (H : PrefixFullRangeLogRateCeiling F start)
    (T : TailFullRangeLogRateCeiling F start) :
    H.ceiling <= (H.glue T).ceiling :=
  Q'.le_max'_left H.ceiling T.ceiling

theorem tail_ceiling_le_glue
    (H : PrefixFullRangeLogRateCeiling F start)
    (T : TailFullRangeLogRateCeiling F start) :
    T.ceiling <= (H.glue T).ceiling :=
  Q'.le_max'_right H.ceiling T.ceiling

end PrefixFullRangeLogRateCeiling

end YMGap.Continuum.PhysicalSeparatorFullLogComparison

#print axioms YMGap.Continuum.PhysicalSeparatorFullLogComparison.PrefixFullRangeLogRateCeiling.glue
#print axioms YMGap.Continuum.PhysicalSeparatorFullLogComparison.PrefixFullRangeLogRateCeiling.prefix_ceiling_le_glue
#print axioms YMGap.Continuum.PhysicalSeparatorFullLogComparison.PrefixFullRangeLogRateCeiling.tail_ceiling_le_glue
