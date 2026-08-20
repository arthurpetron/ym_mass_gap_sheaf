/-
M2j -- global comparison of the physical margin with the exact range-reduced
logarithmic rate.

For every positive rational physical separator `q_j < 1`, the binary reduction
from `PhysicalSeparatorFullLogRate` and the estimates in `FullLogMarginLower`
give

    1 - q_j <= -log(q_j),
    (1 - q_j) / a_j <= -log(q_j) / a_j.

There is no direct-artanh or `q_j >= 1/2` hypothesis.  Consequently any
two-sided rational `PhysicalGapFloor` supplies a uniform lower bound for the
full-range exact logarithmic family.  A finite exact upper bound remains an
independent obligation: away from the near-one regime it does not follow from
the rational margin ceiling alone.
-/

import YMGap.Continuum.FullLogMarginLower
import YMGap.Continuum.UnifiedContinuumFloor

namespace YMGap.Continuum.PhysicalSeparatorFullLogComparison

open YMGap.Constructive
open YMGap.Constructive.CRealLog
open YMGap.Constructive.CRealAlg
open YMGap.Continuum
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.PhysicalSeparatorLogRate
open YMGap.Continuum.PhysicalSeparatorFullLogRate
open YMGap.Continuum.FullLogMarginLower
open YMGap.Continuum.HamiltonianAllSep
open YMGap.Continuum.UnifiedContinuumFloor

/-! ## 1. Unscaled global logarithm comparison -/

/-- A positive natural embeds as a positive `Q'`. -/
theorem ofNat_pos_of_pos (n : Nat) (hn : 0 < n) :
    (0 : Q') < Q'.ofNat n := by
  show (0 : Int) * ((Q'.ofNat n).den : Int) <
    (Q'.ofNat n).num * (1 : Int)
  rw [Q'.ofNat_num_cast, Q'.ofNat_den_cast]
  have hcast : (0 : Int) < (n : Int) := by exact_mod_cast hn
  simpa only [Int.zero_mul, Int.mul_one] using hcast

/-- Every reduced physical mantissa is nonnegative. -/
theorem reducedMantissa_nonnegative (P : PhysicalSeparator) (j : Nat) :
    (0 : Q') <= reducedMantissa P j := by
  exact Q'.le_of_lt (Q'.mul_pos (P.sep_pos j)
    (ofNat_pos_of_pos (2 ^ (separatorBinExp P j).k)
      (Nat.two_pow_pos (separatorBinExp P j).k)))

/-- **Global exact-log lower comparison.**  The physical margin is below the
range-reduced exact logarithmic mass at every scale, with no half-window
assumption. -/
theorem margin_le_fullLogMass (P : PhysicalSeparator) (j : Nat) :
    CReal.leEv (CReal.ofQ' (P.physMargin j)) (fullLogMass P j) := by
  let be := separatorBinExp P j
  let m := reducedMantissa P j
  have hrat :
      rationalMargin (P.sep j) <=
        binaryHalfLower be.k + rationalMargin m := by
    exact rationalMargin_le_binaryHalf_add_mantMargin
      (P.sep j) (P.sep_nonneg j) be
  have hconst :
      CReal.leEv (CReal.ofQ' (P.physMargin j))
        (CReal.ofQ' (binaryHalfLower be.k + rationalMargin m)) := by
    apply CReal.leEv_ofQ'_of_approx_ge
    intro n
    change P.physMargin j <= binaryHalfLower be.k + rationalMargin m
    change rationalMargin (P.sep j) <=
      binaryHalfLower be.k + rationalMargin m
    exact hrat
  have hbinary :
      CReal.leEv (CReal.ofQ' (binaryHalfLower be.k)) (kLog2 be.k) :=
    binaryHalfLower_le_kLog2 be.k
  have hmant :
      CReal.leEv (CReal.ofQ' (rationalMargin m))
        (CReal.neg (logRat m (reducedMantissaPlusOne_pos P j)
          (reducedMantissa_window P j))) := by
    exact rationalMargin_le_negLogRat m
      (reducedMantissa_nonnegative P j) (reducedMantissa_lt_one P j)
      (reducedMantissaPlusOne_pos P j) (reducedMantissa_window P j)
  have hsum := CReal.leEv_add hbinary hmant
  have hcombined :
      CReal.leEv (CReal.ofQ' (binaryHalfLower be.k + rationalMargin m))
        (fullLogMass P j) := by
    change CReal.leEv
      (CReal.add (CReal.ofQ' (binaryHalfLower be.k))
        (CReal.ofQ' (rationalMargin m)))
      (CReal.add (kLog2 be.k)
        (CReal.neg (logRat m (reducedMantissaPlusOne_pos P j)
          (reducedMantissa_window P j))))
    exact hsum
  exact CReal.leEv_trans hconst hcombined

/-! ## 2. Dimensionful comparison after positive reciprocal spacing -/

/-- Scaling the global mass inequality by the positive reciprocal spacing gives
`(1-q_j)/a_j <= -log(q_j)/a_j` on the full binary range. -/
theorem marginRate_le_fullMassRate (P : PhysicalSeparator) (A : PhysicalSpacing)
    (j : Nat) :
    CReal.leEv (CReal.ofQ' (marginRate P A j)) (fullMassRate P A j) := by
  have hscaled := CReal.leEv_smul_nonneg
    (Q'.le_of_lt (reciprocalSpacing_pos A j)) (margin_le_fullLogMass P j)
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
      CReal.Equiv (fullMassRate P A j)
        (CReal.mul (CReal.ofQ' (reciprocalSpacing A j))
          (fullLogMass P j)) :=
    CRealAlg.cmul_comm (fullLogMass P j)
      (CReal.ofQ' (reciprocalSpacing A j))
  exact (CReal.leEv_congr hleft hright).mpr hscaled

/-! ## 3. Uniform full-range lower certificate -/

/-- A uniform lower certificate for a full-range exact physical log family. -/
structure UniformFullRangeLogRateFloor {P : PhysicalSeparator}
    (F : FullRangeExactPhysicalLogRateFamily P) : Type where
  floor : Q'
  floor_pos : (0 : Q') < floor
  floor_bound : forall j : Nat, CReal.leEv (CReal.ofQ' floor) (F.rate j)

namespace UniformFullRangeLogRateFloor

/-- The exact full-range physical-rate floor is an inhabitant of the
repository's canonical spacing-uniform `CRealFloor` interface, with no loss of
data or change of currency. -/
def toCRealFloor
    {P : PhysicalSeparator} {F : FullRangeExactPhysicalLogRateFamily P}
    (G : UniformFullRangeLogRateFloor F) : CRealFloor F.rate where
  floor := G.floor
  floor_pos := G.floor_pos
  bound := G.floor_bound

end UniformFullRangeLogRateFloor

/-- A rational two-sided physical gap floor supplies the full-range exact
logarithmic lower rate, without a half-window. -/
def fullRangeLogRateFloorOfPhysicalGapFloor
    (P : PhysicalSeparator) (a : Nat -> Q')
    (ha : forall j : Nat, (0 : Q') < a j)
    (G : PhysicalGapFloor P a ha) :
    UniformFullRangeLogRateFloor (fullRangeRateFamilyOfPhysicalData P a ha) where
  floor := G.c
  floor_pos := G.c_pos
  floor_bound := fun j => by
    have hproxy :
        CReal.leEv (CReal.ofQ' G.c)
          (CReal.ofQ' (marginRate P ⟨a, ha⟩ j)) :=
      CReal.leEv_ofQ'_of_approx_ge (fun _ => G.floor j)
    exact CReal.leEv_trans hproxy (marginRate_le_fullMassRate P ⟨a, ha⟩ j)

/-- The still-independent finite upper bound for the exact full-range rate. -/
structure FullRangeLogRateCeiling {P : PhysicalSeparator}
    (F : FullRangeExactPhysicalLogRateFamily P) : Type where
  ceiling : Q'
  ceiling_bound : forall j : Nat,
    CReal.leEv (F.rate j) (CReal.ofQ' ceiling)

/-- A complete full-range exact physical separator certificate.  The lower
field is now reducible from `PhysicalGapFloor`; the finite exact upper field is
kept explicit. -/
structure FullRangeExactPhysicalSeparatorCertificate : Type 1 where
  separator : PhysicalSeparator
  rateFamily : FullRangeExactPhysicalLogRateFamily separator
  uniformFloor : UniformFullRangeLogRateFloor rateFamily
  finiteCeiling : FullRangeLogRateCeiling rateFamily

namespace FullRangeExactPhysicalSeparatorCertificate

/-- The certificate's exact logarithmic physical rates carry the canonical
uniform constructive-real floor used by the continuum frontier. -/
def exactRateCRealFloor
    (C : FullRangeExactPhysicalSeparatorCertificate) :
    CRealFloor C.rateFamily.rate :=
  C.uniformFloor.toCRealFloor

end FullRangeExactPhysicalSeparatorCertificate

/-- Package a rational physical gap floor and an independent exact upper rate
into the full-range certificate. -/
def fullRangeExactCertificateOfPhysicalGapFloor
    (P : PhysicalSeparator) (a : Nat -> Q')
    (ha : forall j : Nat, (0 : Q') < a j)
    (G : PhysicalGapFloor P a ha)
    (U : FullRangeLogRateCeiling (fullRangeRateFamilyOfPhysicalData P a ha)) :
    FullRangeExactPhysicalSeparatorCertificate where
  separator := P
  rateFamily := fullRangeRateFamilyOfPhysicalData P a ha
  uniformFloor := fullRangeLogRateFloorOfPhysicalGapFloor P a ha G
  finiteCeiling := U

end YMGap.Continuum.PhysicalSeparatorFullLogComparison

#print axioms YMGap.Continuum.PhysicalSeparatorFullLogComparison.reducedMantissa_nonnegative
#print axioms YMGap.Continuum.PhysicalSeparatorFullLogComparison.margin_le_fullLogMass
#print axioms YMGap.Continuum.PhysicalSeparatorFullLogComparison.marginRate_le_fullMassRate
#print axioms YMGap.Continuum.PhysicalSeparatorFullLogComparison.fullRangeLogRateFloorOfPhysicalGapFloor
#print axioms YMGap.Continuum.PhysicalSeparatorFullLogComparison.UniformFullRangeLogRateFloor.toCRealFloor
#print axioms YMGap.Continuum.PhysicalSeparatorFullLogComparison.FullRangeExactPhysicalSeparatorCertificate.exactRateCRealFloor
#print axioms YMGap.Continuum.PhysicalSeparatorFullLogComparison.fullRangeExactCertificateOfPhysicalGapFloor
