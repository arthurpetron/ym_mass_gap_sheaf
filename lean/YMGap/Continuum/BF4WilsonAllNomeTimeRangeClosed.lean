/-
# Constructive closedness of the original witnessed time-range sector

For a convergent sequence of original states with explicit T(1)-range
witnesses, sample the nth witness to invSucc(n) accuracy. The supplied
outer modulus and a squared triangle estimate give a range witness for
the original limit. No uniform preimage cap or choice of representatives
is needed. Applying this to the existing represented Cauchy-row limit
establishes represented completeness of this sector in the original norm.

This supplies the closedness step needed by the scoped adjoint construction,
not a full Hilbert-sector package, physical OS identification, or scaling
estimate. The ambient boundary kernel is retained.
-/

import YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosure
import YMGap.Continuum.BF4WilsonAllNomeCauchyRows

namespace YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosed

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosure
  (RangeLimit quarter quarter_positive four_quarters)
open YMGap.Continuum.BF4WilsonAllNomeCauchyRows
  (RepresentedCauchy rowPoint limit limitRate limit_bound limit_unique limit_orthogonal)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "T" => completedTime hw0 hw1
local notation "B" => completedInner hw0 hw1
local notation "dist" => completedDist hw0 hw1
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

/-- Sample only the supplied nth witness; its preimages need not themselves
converge or have a uniform norm bound. -/
def diagonalPreimage {x : Nat → V} (R : ∀ n, RangeLimit hw0 hw1 (x n))
    (n : Nat) : (D).Cauchy :=
  (R n).preimage ((R n).modulus (Q'.invSucc n))

theorem diagonalPreimage_close {x : Nat → V} (R : ∀ n, RangeLimit hw0 hw1 (x n))
    (n : Nat) :
    RCle (dist (T 1 (Class (diagonalPreimage hw0 hw1 R n))) (x n))
      (rat (Q'.invSucc n)) :=
  (R n).bound (Q'.invSucc n) (Q'.invSucc_pos n) _ (Nat.le_refl _)

/-- Closedness with an explicit outer convergence modulus and a computed
original preimage sequence, not a Prop-level existence statement. -/
def ofLimit {x : Nat → V} (R : ∀ n, RangeLimit hw0 hw1 (x n))
    (z : V) (modulus : Q' → Nat)
    (bound : ∀ e : Q', (0 : Q') < e → ∀ n, modulus e ≤ n →
      RCle (dist (x n) z) (rat e)) : RangeLimit hw0 hw1 z where
  preimage := diagonalPreimage hw0 hw1 R
  modulus := fun e => max (modulus (quarter e)) (quarter e).den
  bound := by
    intro e he n hn
    let delta := quarter e
    have hd : (0 : Q') < delta := quarter_positive he
    have hdelta : Q'.invSucc n ≤ delta :=
      Q'.le_trans' _ _ _
        (ExpNeg.invSucc_le_of_le (Nat.le_trans (Nat.le_max_right _ _) hn))
        (HalfPow.invSucc_den_le delta hd)
    have hfirst : RCle
        (dist (T 1 (Class (diagonalPreimage hw0 hw1 R n))) (x n)) (rat delta) :=
      RCle_trans (diagonalPreimage_close hw0 hw1 R n)
        (leEv_le_ofQ'_of_approx_le (fun _ => hdelta))
    have hsecond := bound delta hd n (Nat.le_trans (Nat.le_max_left _ _) hn)
    have h := RCle_trans (completedDist_triangle hw0 hw1 _ (x n) z)
      (RCadd_le_add (RCadd_le_add hfirst hfirst) (RCadd_le_add hsecond hsecond))
    rwa [four_quarters] at h

/-- The existing original completion's computed limit stays in the witnessed
sector. Inner and outer representatives and moduli are supplied explicitly. -/
def representedLimit (rows : RepresentedCauchy hw0 hw1 (width := width))
    (R : ∀ n, RangeLimit hw0 hw1 (rowPoint hw0 hw1 rows n)) :
    RangeLimit hw0 hw1 (limit hw0 hw1 rows) :=
  ofLimit hw0 hw1 R (limit hw0 hw1 rows) (limitRate hw0 hw1 rows)
    (limit_bound hw0 hw1 rows)

/-- Simultaneous completeness of the witnessed sector and original vacuum
complement, with the SAME already constructed limit and both witnesses. -/
def centeredRepresentedLimit (rows : RepresentedCauchy hw0 hw1 (width := width))
    (R : ∀ n, RangeLimit hw0 hw1 (rowPoint hw0 hw1 rows n))
    (centered : ∀ n, B (unitState hw0 hw1 width) (rowPoint hw0 hw1 rows n) = RCzero) :
    Σ' z : VacuumComplement hw0 hw1 (width := width),
      (RangeLimit hw0 hw1 z.val) ×' (z.val = limit hw0 hw1 rows) :=
  ⟨⟨limit hw0 hw1 rows,limit_orthogonal hw0 hw1 rows centered⟩,
    representedLimit hw0 hw1 rows R,rfl⟩

/-- A range witness itself constructs represented Cauchy rows of original
time images; no representative of its target is assumed. -/
def rangeRows {x : V} (R : RangeLimit hw0 hw1 x) :
    RepresentedCauchy hw0 hw1 (width := width) where
  row := fun n => (timeNonexpansive hw0 hw1 1).mapCauchy (R.preimage n)
  modulus := fun e => R.modulus (quarter e)
  isCauchy := by
    intro e he m n hm hn
    change RCle (dist (T 1 (Class (R.preimage m))) (T 1 (Class (R.preimage n)))) _
    have hd : (0 : Q') < quarter e := quarter_positive he
    have hleft := R.bound (quarter e) hd m hm
    have hright : RCle (dist x (T 1 (Class (R.preimage n)))) (rat (quarter e)) := by
      rw [completedDist_symm]
      exact R.bound (quarter e) hd n hn
    have h := RCle_trans (completedDist_triangle hw0 hw1 _ x _)
      (RCadd_le_add (RCadd_le_add hleft hleft) (RCadd_le_add hright hright))
    rwa [four_quarters] at h

theorem rangeRows_point {x : V} (R : RangeLimit hw0 hw1 x) (n : Nat) :
    rowPoint hw0 hw1 (rangeRows hw0 hw1 R) n = T 1 (Class (R.preimage n)) := rfl

theorem rangeRows_limit {x : V} (R : RangeLimit hw0 hw1 x) :
    limit hw0 hw1 (rangeRows hw0 hw1 R) = x :=
  limit_unique hw0 hw1 (rangeRows hw0 hw1 R) x R.modulus R.bound

/-- The existing diagonal extracts an original representative FROM the
supplied range witness. This is not selection from an arbitrary quotient. -/
def representative {x : V} (R : RangeLimit hw0 hw1 x) : (D).Cauchy :=
  CRealSeminormCauchyRows.diagonalCauchy (distanceData hw0 hw1)
    (rangeRows hw0 hw1 R)

theorem representative_pin {x : V} (R : RangeLimit hw0 hw1 x) :
    Class (representative hw0 hw1 R) = x :=
  rangeRows_limit hw0 hw1 R

#print axioms diagonalPreimage
#print axioms diagonalPreimage_close
#print axioms ofLimit
#print axioms representedLimit
#print axioms centeredRepresentedLimit
#print axioms rangeRows
#print axioms rangeRows_point
#print axioms rangeRows_limit
#print axioms representative
#print axioms representative_pin

end YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosed
