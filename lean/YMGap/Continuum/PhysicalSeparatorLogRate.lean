/-
M2a — the exact physical logarithmic rate carried by a physical separator.

For a physical gauge-invariant transfer separator `q_j` and a positive lattice
spacing `a_j`, the dimensionful mass is

    M_j = -log(q_j) / a_j.

`PhysicalSeparator.lean` deliberately used the rational proxy `1 - q_j`.
That proxy is useful for algebraic comparison, but it is not the exact physical
rate.  This module restores the exact `CRealLog.logRat` expression and proves
constructive strict positivity at every supplied scale (on the current direct
artanh window).

What is closed here:

* exact `CReal` definitions of `-log(q_j)` and `-log(q_j) / a_j`;
* constructive positivity of `-log(q_j)` from `0 < q_j < 1`;
* eventual strict positivity of the dimensionful rate after multiplication by
  the exact positive reciprocal spacing;
* a Type-level uniform two-sided rate-band interface and a bundled exact
  physical-separator certificate.

What remains open:

* producing `PhysicalSeparator` from the plaquette-coupled Gibbs/transfer
  object (rather than postulating its gauge-invariant correlator control);
* supplying the artanh range reduction when `q_j < 1/2`;
* inhabiting the uniform rate band through all cutoff and spacing scales;
* connecting that band to the same constructive OS Hamiltonian after cutoff
  removal.

Thus this file closes the exact log-rate extraction layer, not physical BF4,
the continuum bridge, or the Clay problem.
-/

import YMGap.Continuum.PhysicalSeparator
import YMGap.Continuum.GNSHamiltonian
import YMGap.Continuum.TuranPositivity
import YMGap.Continuum.ArtanhMonotone
import YMGap.Continuum.RCScaleClose
import YMGap.Continuum.EffMassConvergence
import YMGap.Constructive.CRealAlg

namespace YMGap.Continuum.PhysicalSeparatorLogRate

open YMGap.Constructive
open YMGap.Constructive.CRealLog
open YMGap.Continuum
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.TuranPositivity

/-! ## 1. Positive physical spacing and the direct logarithm window -/

/-- The positive physical lattice spacing at each scale.  This is deliberately
smaller than an RG-flow record: exact rate extraction only needs `a_j > 0`. -/
structure PhysicalSpacing : Type where
  spacing : Nat -> Q'
  spacing_pos : forall j : Nat, (0 : Q') < spacing j

/-- `0 < q_j + 1`, derived from the located physical one-mode separator. -/
theorem separatorPlusOne_pos (P : PhysicalSeparator) (j : Nat) :
    (0 : Q') < P.sep j + 1 :=
  YMGap.Continuum.sepPlusOne_pos (physLocatedGap P j)

/-- The current directly-reducible artanh window for every physical separator.
This is Type-level supplied data, not a hidden decidability or range-reduction
assumption.  Separators below `1/2` require the named logarithm range reduction
already isolated by `GNSHamiltonian`. -/
structure PhysicalLogWindow (P : PhysicalSeparator) : Type where
  inWindow : forall j : Nat,
    Q'.abs (yOf (P.sep j) (separatorPlusOne_pos P j)) <= recipOdd 1

/-! ## 2. The exact logarithmic mass and dimensionful rate -/

/-- The exact transfer mass `-log(q_j)` as a constructive real. -/
def logMass (P : PhysicalSeparator) (W : PhysicalLogWindow P) (j : Nat) : CReal :=
  CReal.neg (logRat (P.sep j) (separatorPlusOne_pos P j) (W.inWindow j))

/-- The exact transfer mass is strictly positive at every scale. -/
theorem logMass_isPositive (P : PhysicalSeparator) (W : PhysicalLogWindow P)
    (j : Nat) : CReal.IsPositive (logMass P W j) :=
  YMGap.Continuum.isPositive_neg_logRat
    (P.sep j) (separatorPlusOne_pos P j) (P.sep_lt_one j) (W.inWindow j)

/-- The rational margin is bounded by the first two artanh terms:
`1 - q_j <= -2 y(q_j)`.  Since the remaining odd terms have the same sign,
this is the constructive rational core of `1 - q <= -log q`. -/
theorem margin_le_neg_two_y (P : PhysicalSeparator) (j : Nat) :
    P.physMargin j <=
      -(term (yOf (P.sep j) (separatorPlusOne_pos P j)) 0
        + term (yOf (P.sep j) (separatorPlusOne_pos P j)) 0) := by
  have hdpos : (0 : Q') < P.physMargin j := P.physMargin_pos j
  have hdnonneg : (0 : Q') <= P.physMargin j := Q'.le_of_lt hdpos
  have hsepTwo : P.sep j + 1 <= (2 : Q') := by
    exact Q'.add_le_add_right _ _ 1 (Q'.le_of_lt (P.sep_lt_one j))
  have hrecip :
      Q'.recipPos (2 : Q') (by decide) <=
        Q'.recipPos (P.sep j + 1) (separatorPlusOne_pos P j) :=
    ArtanhMonotone.recipPos_antitone (P.sep j + 1) (2 : Q')
      (separatorPlusOne_pos P j) (by decide) hsepTwo
  have hmul :
      P.physMargin j * Q'.recipPos (2 : Q') (by decide) <=
        P.physMargin j * Q'.recipPos (P.sep j + 1) (separatorPlusOne_pos P j) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hrecip hdnonneg
  have hsum :
      P.physMargin j * Q'.recipPos (2 : Q') (by decide)
          + P.physMargin j * Q'.recipPos (2 : Q') (by decide) <=
        P.physMargin j * Q'.recipPos (P.sep j + 1) (separatorPlusOne_pos P j)
          + P.physMargin j * Q'.recipPos (P.sep j + 1) (separatorPlusOne_pos P j) :=
    Q'.add_le_add hmul hmul
  have htwo :
      (Q'.recipPos (2 : Q') (by decide) + Q'.recipPos (2 : Q') (by decide)).eqv 1 := by
    decide
  have hmarginEq :
      (P.physMargin j).eqv
        (P.physMargin j * Q'.recipPos (2 : Q') (by decide)
          + P.physMargin j * Q'.recipPos (2 : Q') (by decide)) := by
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_one_eqv (P.physMargin j))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (P.physMargin j) 1
        (Q'.recipPos (2 : Q') (by decide) + Q'.recipPos (2 : Q') (by decide))
        (Q'.eqv_symm htwo)) ?_
    exact Q'.mul_add_eqv (P.physMargin j)
      (Q'.recipPos (2 : Q') (by decide)) (Q'.recipPos (2 : Q') (by decide))
  have hmarginSum :
      P.physMargin j <=
        P.physMargin j * Q'.recipPos (P.sep j + 1) (separatorPlusOne_pos P j)
          + P.physMargin j * Q'.recipPos (P.sep j + 1) (separatorPlusOne_pos P j) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hmarginEq) hsum
  have hnum : (P.sep j + -1).eqv (-(P.physMargin j)) := by
    unfold PhysicalSeparator.physMargin
    refine Q'.eqv_symm (Q'.eqv_trans _ _ _ (Q'.neg_add_eqv 1 (-(P.sep j))) ?_)
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (-1) (-(-(P.sep j))) (P.sep j)
        (Q'.neg_neg_eqv (P.sep j))) ?_
    exact Q'.add_comm_eqv (-1) (P.sep j)
  have hy :
      (yOf (P.sep j) (separatorPlusOne_pos P j)).eqv
        (-(P.physMargin j
          * Q'.recipPos (P.sep j + 1) (separatorPlusOne_pos P j))) := by
    show ((P.sep j + -1)
        * Q'.recipPos (P.sep j + 1) (separatorPlusOne_pos P j)).eqv _
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (P.sep j + -1) (-(P.physMargin j))
        (Q'.recipPos (P.sep j + 1) (separatorPlusOne_pos P j)) hnum) ?_
    exact Q'.neg_mul_eqv (P.physMargin j)
      (Q'.recipPos (P.sep j + 1) (separatorPlusOne_pos P j))
  have hterm := term_zero_eqv_self (yOf (P.sep j) (separatorPlusOne_pos P j))
  have htarget :
      (-(term (yOf (P.sep j) (separatorPlusOne_pos P j)) 0
          + term (yOf (P.sep j) (separatorPlusOne_pos P j)) 0)).eqv
        (P.physMargin j * Q'.recipPos (P.sep j + 1) (separatorPlusOne_pos P j)
          + P.physMargin j * Q'.recipPos (P.sep j + 1) (separatorPlusOne_pos P j)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.neg_eqv_congr _ _ (Q'.add_eqv_congr' hterm hterm)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.neg_eqv_congr _ _ (Q'.add_eqv_congr' hy hy)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.neg_add_eqv
        (-(P.physMargin j * Q'.recipPos (P.sep j + 1) (separatorPlusOne_pos P j)))
        (-(P.physMargin j * Q'.recipPos (P.sep j + 1) (separatorPlusOne_pos P j)))) ?_
    exact Q'.add_eqv_congr'
      (Q'.neg_neg_eqv
        (P.physMargin j * Q'.recipPos (P.sep j + 1) (separatorPlusOne_pos P j)))
      (Q'.neg_neg_eqv
        (P.physMargin j * Q'.recipPos (P.sep j + 1) (separatorPlusOne_pos P j)))
  exact Q'.le_trans' _ _ _ hmarginSum (Q'.ge_of_eqv htarget)

/-- The standard exact inequality `1 - q_j <= -log(q_j)`, stated in the
regularity-free eventual order used by the constructive real layer. -/
theorem margin_le_logMass (P : PhysicalSeparator) (W : PhysicalLogWindow P)
    (j : Nat) : CReal.leEv (CReal.ofQ' (P.physMargin j)) (logMass P W j) := by
  have hyneg : yOf (P.sep j) (separatorPlusOne_pos P j) <= (0 : Q') :=
    Q'.le_of_lt (YMGap.Continuum.yOf_sep_neg
      (P.sep j) (separatorPlusOne_pos P j) (P.sep_lt_one j))
  have hlog := logRat_leRat_of_arg_nonpos
    (P.sep j) (separatorPlusOne_pos P j) (W.inWindow j) hyneg
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := hlog epsilon hepsilon
  refine ⟨N, fun n hn => ?_⟩
  show P.physMargin j <=
    -((logRat (P.sep j) (separatorPlusOne_pos P j) (W.inWindow j)).approx n)
      + epsilon
  exact Q'.le_trans' _ _ _ (margin_le_neg_two_y P j) (Q'.neg_le_neg_add (hN n hn))

/-- The exact rational reciprocal `1/a_j`. -/
def reciprocalSpacing (A : PhysicalSpacing) (j : Nat) : Q' :=
  Q'.recipPos (A.spacing j) (A.spacing_pos j)

/-- The reciprocal spacing is strictly positive. -/
theorem reciprocalSpacing_pos (A : PhysicalSpacing) (j : Nat) :
    (0 : Q') < reciprocalSpacing A j := by
  exact Q'.recipPos_pos _ (A.spacing_pos j)

/-- Convert the repo's one-slack `IsPositive` witness into the eventual-order
positivity used for multiplication and uniform lower certificates. -/
theorem posEv_of_isPositive {x : CReal} (hx : CReal.IsPositive x) : PosEv x := by
  obtain ⟨epsilon, hepsilon, N, hN⟩ := CReal.eventually_ge_of_isPositive hx
  exact posEv_of_eventually hepsilon ⟨N, hN⟩

/-- The exact reciprocal spacing, embedded in `CReal`, is eventually strictly
positive. -/
theorem reciprocalSpacing_posEv (A : PhysicalSpacing) (j : Nat) :
    PosEv (CReal.ofQ' (reciprocalSpacing A j)) := by
  refine posEv_of_eventually (reciprocalSpacing_pos A j) ⟨0, ?_⟩
  intro n hn
  exact Q'.le_refl' _

/-- The exact dimensionful physical rate
`M_j = (-log(q_j)) * (1/a_j)`. -/
def massRate (P : PhysicalSeparator) (A : PhysicalSpacing)
    (W : PhysicalLogWindow P) (j : Nat) : CReal :=
  CReal.mul (logMass P W j) (CReal.ofQ' (reciprocalSpacing A j))

/-- The rational proxy rate `(1 - q_j)/a_j`.  This is retained only as a
certified lower bound on `massRate`, not identified with the exact rate. -/
def marginRate (P : PhysicalSeparator) (A : PhysicalSpacing) (j : Nat) : Q' :=
  Q'.divPos (P.physMargin j) (A.spacing j) (A.spacing_pos j)

/-- Scaling `1 - q <= -log q` by the positive reciprocal spacing gives
`(1 - q_j)/a_j <= M_j`. -/
theorem marginRate_le_massRate (P : PhysicalSeparator) (A : PhysicalSpacing)
    (W : PhysicalLogWindow P) (j : Nat) :
    CReal.leEv (CReal.ofQ' (marginRate P A j)) (massRate P A W j) := by
  have hscaled := CReal.leEv_smul_nonneg
    (Q'.le_of_lt (reciprocalSpacing_pos A j)) (margin_le_logMass P W j)
  have hleft :
      CReal.Equiv (CReal.ofQ' (marginRate P A j))
        (CReal.mul (CReal.ofQ' (reciprocalSpacing A j))
          (CReal.ofQ' (P.physMargin j))) := by
    refine CReal.Equiv.trans ?_ (CRealAlg.cmul_comm
      (CReal.ofQ' (P.physMargin j)) (CReal.ofQ' (reciprocalSpacing A j)))
    unfold marginRate reciprocalSpacing Q'.divPos
    exact CRealAlg.ofQ'_mul (P.physMargin j)
      (Q'.recipPos (A.spacing j) (A.spacing_pos j))
  have hright :
      CReal.Equiv (massRate P A W j)
        (CReal.mul (CReal.ofQ' (reciprocalSpacing A j)) (logMass P W j)) := by
    exact CRealAlg.cmul_comm (logMass P W j) (CReal.ofQ' (reciprocalSpacing A j))
  exact (CReal.leEv_congr hleft hright).mpr hscaled

/-- For `q_j < 1`, the absolute displacement from one is exactly the physical
margin: `|q_j - 1| = 1 - q_j` up to `Q'` equivalence. -/
theorem abs_sep_sub_one_eqv_margin (P : PhysicalSeparator) (j : Nat) :
    (Q'.abs (P.sep j + -1)).eqv (P.physMargin j) := by
  have hnum : (P.sep j + -1).eqv (-(P.physMargin j)) := by
    unfold PhysicalSeparator.physMargin
    refine Q'.eqv_symm (Q'.eqv_trans _ _ _ (Q'.neg_add_eqv 1 (-(P.sep j))) ?_)
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (-1) (-(-(P.sep j))) (P.sep j)
        (Q'.neg_neg_eqv (P.sep j))) ?_
    exact Q'.add_comm_eqv (-1) (P.sep j)
  refine Q'.eqv_trans _ _ _ (Q'.abs_eqv_congr hnum) ?_
  refine Q'.eqv_trans _ _ _ (Q'.abs_neg' (P.physMargin j)) ?_
  have habs : Q'.abs (P.physMargin j) = P.physMargin j := by
    unfold Q'.abs
    rw [if_pos (Q'.le_of_lt (P.physMargin_pos j))]
  exact Q'.eqv_of_eq habs

/-- On the direct artanh window, the exact logarithmic mass has the explicit
finiteness estimate `-log(q_j) <= (9/4) * (1 - q_j)`. -/
theorem logMass_le_c94_margin (P : PhysicalSeparator) (W : PhysicalLogWindow P)
    (j : Nat) :
    CReal.leEv (logMass P W j)
      (CReal.ofQ' (EffMassConvergence.c94 * P.physMargin j)) := by
  have hsepNonnegative : (0 : Q') <= P.sep j := P.sep_nonneg j
  have hsepOne : (1 : Q') <= P.sep j + 1 := by
    have h := Q'.add_le_add_left 1 0 (P.sep j) hsepNonnegative
    rw [Q'.add_zero'] at h
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.add_comm_eqv 1 (P.sep j)))
  refine CReal.leEv_le_ofQ'_of_approx_le (fun n => ?_)
  show -((logRat (P.sep j) (separatorPlusOne_pos P j) (W.inWindow j)).approx n) <=
    EffMassConvergence.c94 * P.physMargin j
  have hnegAbs :
      -((logRat (P.sep j) (separatorPlusOne_pos P j) (W.inWindow j)).approx n) <=
        Q'.abs (-((logRat (P.sep j) (separatorPlusOne_pos P j) (W.inWindow j)).approx n)) :=
    Q'.le_abs_self _
  have habsNeg :
      Q'.abs (-((logRat (P.sep j) (separatorPlusOne_pos P j) (W.inWindow j)).approx n)) <=
        Q'.abs ((logRat (P.sep j) (separatorPlusOne_pos P j) (W.inWindow j)).approx n) :=
    Q'.le_of_eqv (Q'.abs_neg' _)
  have hlog := EffMassConvergence.logRat_approx_abs_le
    (P.sep j) (separatorPlusOne_pos P j) (W.inWindow j) n
  have hy := EffMassConvergence.absYOf_le
    (P.sep j) (separatorPlusOne_pos P j) hsepOne
  have hscale :
      EffMassConvergence.c94 *
          Q'.abs (yOf (P.sep j) (separatorPlusOne_pos P j)) <=
        EffMassConvergence.c94 * Q'.abs (P.sep j + -1) :=
    Q'.mul_le_mul_of_nonneg_left _ _ EffMassConvergence.c94 hy (by decide)
  have hmargin :
      EffMassConvergence.c94 * Q'.abs (P.sep j + -1) <=
        EffMassConvergence.c94 * P.physMargin j :=
    Q'.mul_le_mul_of_nonneg_left _ _ EffMassConvergence.c94
      (Q'.le_of_eqv (abs_sep_sub_one_eqv_margin P j)) (by decide)
  exact Q'.le_trans' _ _ _ hnegAbs
    (Q'.le_trans' _ _ _ habsNeg
      (Q'.le_trans' _ _ _ hlog (Q'.le_trans' _ _ _ hscale hmargin)))

/-- The exact dimensionful rate is at most `9/4` times the rational margin
rate.  Together with `marginRate_le_massRate`, this proves quantitative
equivalence of the exact and proxy rates on the direct window. -/
theorem massRate_le_c94_marginRate (P : PhysicalSeparator) (A : PhysicalSpacing)
    (W : PhysicalLogWindow P) (j : Nat) :
    CReal.leEv (massRate P A W j)
      (CReal.ofQ' (EffMassConvergence.c94 * marginRate P A j)) := by
  have hscaled := CReal.leEv_smul_nonneg
    (Q'.le_of_lt (reciprocalSpacing_pos A j)) (logMass_le_c94_margin P W j)
  have hleft :
      CReal.Equiv (massRate P A W j)
        (CReal.mul (CReal.ofQ' (reciprocalSpacing A j)) (logMass P W j)) :=
    CRealAlg.cmul_comm (logMass P W j) (CReal.ofQ' (reciprocalSpacing A j))
  have hright :
      CReal.Equiv (CReal.ofQ' (EffMassConvergence.c94 * marginRate P A j))
        (CReal.mul (CReal.ofQ' (reciprocalSpacing A j))
          (CReal.ofQ' (EffMassConvergence.c94 * P.physMargin j))) := by
    refine SumOfSquares.Equiv_of_approx_eqv (fun _ => ?_)
    unfold marginRate reciprocalSpacing Q'.divPos
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv EffMassConvergence.c94 (P.physMargin j)
        (Q'.recipPos (A.spacing j) (A.spacing_pos j)))) ?_
    exact Q'.mul_comm_eqv
      (EffMassConvergence.c94 * P.physMargin j)
      (Q'.recipPos (A.spacing j) (A.spacing_pos j))
  exact (CReal.leEv_congr hleft hright).mpr hscaled

/-- Every supplied exact physical rate is constructively strictly positive in
the eventual order.  This is per-scale positivity, not yet a uniform floor. -/
theorem massRate_posEv (P : PhysicalSeparator) (A : PhysicalSpacing)
    (W : PhysicalLogWindow P) (j : Nat) : PosEv (massRate P A W j) :=
  posEv_mul (posEv_of_isPositive (logMass_isPositive P W j))
    (reciprocalSpacing_posEv A j)

/-! ## 3. Exact rate families and the uniform physical-rate obligation -/

/-- A bundled exact logarithmic physical-rate family.  An inhabitant selects
the actual spacing and supplies the currently required logarithm window; the
rates themselves are then definitions, not independent fields. -/
structure ExactPhysicalLogRateFamily (P : PhysicalSeparator) : Type where
  physicalSpacing : PhysicalSpacing
  logWindow : PhysicalLogWindow P

namespace ExactPhysicalLogRateFamily

/-- The exact mass rate carried by a bundled family. -/
def rate {P : PhysicalSeparator} (F : ExactPhysicalLogRateFamily P) (j : Nat) : CReal :=
  massRate P F.physicalSpacing F.logWindow j

/-- Per-scale constructive strict positivity of the bundled exact rate. -/
theorem rate_posEv {P : PhysicalSeparator} (F : ExactPhysicalLogRateFamily P)
    (j : Nat) : PosEv (F.rate j) :=
  massRate_posEv P F.physicalSpacing F.logWindow j

end ExactPhysicalLogRateFamily

/-- The exact-rate family built from an explicit spacing sequence and direct
logarithm-window certificate. -/
def exactRateFamilyOfPhysicalData (P : PhysicalSeparator) (a : Nat -> Q')
    (ha : forall j : Nat, (0 : Q') < a j) (W : PhysicalLogWindow P) :
    ExactPhysicalLogRateFamily P where
  physicalSpacing := ⟨a, ha⟩
  logWindow := W

/-- A uniform positive lower certificate for an exact logarithmic rate family.
This separates the lower mass-gap statement from the independent finiteness
ceiling. -/
structure UniformPhysicalLogRateFloor {P : PhysicalSeparator}
    (F : ExactPhysicalLogRateFamily P) : Type where
  floor : Q'
  floor_pos : (0 : Q') < floor
  floor_bound : forall j : Nat, CReal.leEv (CReal.ofQ' floor) (F.rate j)

/-- Any rational `PhysicalGapFloor` for the margin proxy canonically supplies a
uniform floor for the exact logarithmic mass rate, because
`(1 - q_j)/a_j <= -log(q_j)/a_j`.  This transfers only the lower bound; the
exact-rate finiteness ceiling remains a separate obligation. -/
def exactLogRateFloorOfPhysicalGapFloor
    (P : PhysicalSeparator) (a : Nat -> Q')
    (ha : forall j : Nat, (0 : Q') < a j) (W : PhysicalLogWindow P)
    (G : PhysicalGapFloor P a ha) :
    UniformPhysicalLogRateFloor (exactRateFamilyOfPhysicalData P a ha W) where
  floor := G.c
  floor_pos := G.c_pos
  floor_bound := fun j => by
    have hproxy :
        CReal.leEv (CReal.ofQ' G.c)
          (CReal.ofQ' (marginRate P ⟨a, ha⟩ j)) := by
      refine CReal.leEv_ofQ'_of_approx_ge (fun _ => ?_)
      exact G.floor j
    exact CReal.leEv_trans hproxy (marginRate_le_massRate P ⟨a, ha⟩ W j)

/-- The genuine uniform, finite physical mass-scale obligation for the exact
logarithmic rate.  There is no unconditional physical inhabitant here; below,
an already-supplied two-sided `PhysicalGapFloor` is transported into this exact
band.  The lower bound is the mass-gap content; the upper bound excludes a
trivial divergent mass as `a_j -> 0`. -/
structure UniformPhysicalLogRateBand {P : PhysicalSeparator}
    (F : ExactPhysicalLogRateFamily P) : Type where
  floor : Q'
  floor_pos : (0 : Q') < floor
  floor_bound : forall j : Nat, CReal.leEv (CReal.ofQ' floor) (F.rate j)
  ceiling : Q'
  ceiling_bound : forall j : Nat, CReal.leEv (F.rate j) (CReal.ofQ' ceiling)

/-- On the direct logarithm window, a two-sided rational `PhysicalGapFloor`
canonically yields the full exact logarithmic rate band.  The floor is unchanged
and the ceiling is multiplied by the explicit series constant `9/4`. -/
def exactLogRateBandOfPhysicalGapFloor
    (P : PhysicalSeparator) (a : Nat -> Q')
    (ha : forall j : Nat, (0 : Q') < a j) (W : PhysicalLogWindow P)
    (G : PhysicalGapFloor P a ha) :
    UniformPhysicalLogRateBand (exactRateFamilyOfPhysicalData P a ha W) where
  floor := G.c
  floor_pos := G.c_pos
  floor_bound := fun j => by
    change CReal.leEv (CReal.ofQ' G.c) (massRate P ⟨a, ha⟩ W j)
    exact (exactLogRateFloorOfPhysicalGapFloor P a ha W G).floor_bound j
  ceiling := EffMassConvergence.c94 * G.ceil
  ceiling_bound := fun j => by
    change CReal.leEv (massRate P ⟨a, ha⟩ W j)
      (CReal.ofQ' (EffMassConvergence.c94 * G.ceil))
    have hmargin : marginRate P ⟨a, ha⟩ j <= G.ceil := G.finiteness j
    have hscaled :
        EffMassConvergence.c94 * marginRate P ⟨a, ha⟩ j <=
          EffMassConvergence.c94 * G.ceil :=
      Q'.mul_le_mul_of_nonneg_left _ _ EffMassConvergence.c94 hmargin (by decide)
    have hconstants :
        CReal.leEv
          (CReal.ofQ' (EffMassConvergence.c94 * marginRate P ⟨a, ha⟩ j))
          (CReal.ofQ' (EffMassConvergence.c94 * G.ceil)) :=
      CReal.leEv_ofQ'_of_approx_ge (fun _ => hscaled)
    exact CReal.leEv_trans (massRate_le_c94_marginRate P ⟨a, ha⟩ W j) hconstants

/-- The exact M2 certificate interface: one physical gauge-invariant separator,
its derived exact log-rate family, and one uniform finite positive rate band.
No certificate from the actual plaquette-coupled Gibbs object is claimed; that
producer is the next seam. -/
structure ExactPhysicalSeparatorCertificate : Type 1 where
  separator : PhysicalSeparator
  rateFamily : ExactPhysicalLogRateFamily separator
  uniformBand : UniformPhysicalLogRateBand rateFamily

/-- Package an already-supplied physical separator and two-sided margin floor as
an exact logarithmic M2 certificate.  This is a reduction constructor: its
`P` and `G` arguments contain the still-open physical analytic content. -/
def exactPhysicalSeparatorCertificateOfPhysicalGapFloor
    (P : PhysicalSeparator) (a : Nat -> Q')
    (ha : forall j : Nat, (0 : Q') < a j) (W : PhysicalLogWindow P)
    (G : PhysicalGapFloor P a ha) : ExactPhysicalSeparatorCertificate where
  separator := P
  rateFamily := exactRateFamilyOfPhysicalData P a ha W
  uniformBand := exactLogRateBandOfPhysicalGapFloor P a ha W G

end YMGap.Continuum.PhysicalSeparatorLogRate

#print axioms YMGap.Continuum.PhysicalSeparatorLogRate.separatorPlusOne_pos
#print axioms YMGap.Continuum.PhysicalSeparatorLogRate.logMass_isPositive
#print axioms YMGap.Continuum.PhysicalSeparatorLogRate.margin_le_neg_two_y
#print axioms YMGap.Continuum.PhysicalSeparatorLogRate.margin_le_logMass
#print axioms YMGap.Continuum.PhysicalSeparatorLogRate.reciprocalSpacing_pos
#print axioms YMGap.Continuum.PhysicalSeparatorLogRate.posEv_of_isPositive
#print axioms YMGap.Continuum.PhysicalSeparatorLogRate.reciprocalSpacing_posEv
#print axioms YMGap.Continuum.PhysicalSeparatorLogRate.marginRate_le_massRate
#print axioms YMGap.Continuum.PhysicalSeparatorLogRate.abs_sep_sub_one_eqv_margin
#print axioms YMGap.Continuum.PhysicalSeparatorLogRate.logMass_le_c94_margin
#print axioms YMGap.Continuum.PhysicalSeparatorLogRate.massRate_le_c94_marginRate
#print axioms YMGap.Continuum.PhysicalSeparatorLogRate.massRate_posEv
#print axioms YMGap.Continuum.PhysicalSeparatorLogRate.ExactPhysicalLogRateFamily.rate_posEv
#print axioms YMGap.Continuum.PhysicalSeparatorLogRate.exactLogRateFloorOfPhysicalGapFloor
#print axioms YMGap.Continuum.PhysicalSeparatorLogRate.exactLogRateBandOfPhysicalGapFloor
#print axioms YMGap.Continuum.PhysicalSeparatorLogRate.exactPhysicalSeparatorCertificateOfPhysicalGapFloor
