/-
Exact physical scaling from cubic mode cells to the polynomial cleared cells.
No division is introduced: every identity is stated after multiplication by
the positive harmonic denominator to the sixth power.
-/

import YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFullEndpointClosure

namespace YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFullEndpointPhysical

set_option maxHeartbeats 2400000
set_option maxRecDepth 30000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicMovingDeterminantThetaDirichlet
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubic
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicCrossing
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicCarrierSuffix
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFullEndpoint
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFullEndpointClosure
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private abbrev PE := RingNormaliser.PolyExpr
private def pc (n : Int) : PE := .const n
private def padd (a b : PE) : PE := .add a b
private def pmul (a b : PE) : PE := .mul a b
private def pneg (a : PE) : PE := .neg a
private def psub (a b : PE) : PE := padd a (pneg b)
private def ppow (a : PE) (n : Nat) : PE := .pow a n

private theorem polyEval_eqv_congr (e : PE) {rho sigma : Nat → Q'}
    (h : ∀ i, rho i ≈ sigma i) :
    RingNormaliser.eval rho e ≈ RingNormaliser.eval sigma e := by
  induction e with
  | const c => exact Q'.eqv_refl _
  | var i => exact h i
  | add a b iha ihb => exact Q'.add_eqv_congr' iha ihb
  | mul a b iha ihb =>
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ iha) ?_
      exact Q'.mul_eqv_congr_left _ _ _ ihb
  | neg a ih => exact Q'.neg_eqv_congr _ _ ih
  | pow a n ih => exact RingNormaliser.qpow_eqv_congr ih n

private theorem harmU_mul_den (k : Nat) :
    harmU k * Q'.ofNat (k + 2) ≈ (1 : Q') := by
  unfold harmU SummableInverseSquare.unit
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.mkPos_num, Q'.mkPos_den,
    Q'.ofNat_num_cast, Q'.ofNat_den_cast, Int.mul_one, Int.one_mul]
  have h1n : (1 : Q').num = 1 := rfl
  have h1d : ((1 : Q').den : Int) = 1 := rfl
  rw [h1n, h1d, Int.mul_one, Int.one_mul]

private def pProfileScaleL : PE :=
  let U : PE := .var 0
  let D : PE := .var 1
  pmul (pmul U (padd (padd (pc 12) U) (pmul U U)))
    (pmul (pmul D D) D)

private def pProfileFactored : PE :=
  let U : PE := .var 0
  let D : PE := .var 1
  let T := pmul U D
  padd (pmul (pmul (pc 12) T) (pmul D D))
    (padd (pmul (pmul T T) D) (pmul T (pmul T T)))

private def pProfileInT : PE :=
  let T : PE := .var 0
  let D : PE := .var 1
  padd (pmul (pmul (pc 12) T) (pmul D D))
    (padd (pmul (pmul T T) D) (pmul T (pmul T T)))

private def pProfileTarget : PE :=
  let D : PE := .var 0
  padd (padd (pmul (pc 12) (pmul D D)) D) (pc 1)

private def pProfileOne : PE :=
  let D : PE := .var 0
  let T := pc 1
  padd (pmul (pmul (pc 12) T) (pmul D D))
    (padd (pmul (pmul T T) D) (pmul T (pmul T T)))

private theorem pProfile_regroup :
    RingNormaliser.normalize pProfileScaleL =
      RingNormaliser.normalize pProfileFactored := by decide

private theorem pProfile_target :
    RingNormaliser.normalize pProfileOne =
      RingNormaliser.normalize pProfileTarget := by decide

private theorem profileFactored_eq_inT (U D : Q') :
    RingNormaliser.eval (fun | 0 => U | _ => D) pProfileFactored ≈
      RingNormaliser.eval (fun | 0 => U * D | _ => D) pProfileInT := by
  unfold pProfileFactored pProfileInT pc padd pmul RingNormaliser.eval
  exact Q'.eqv_refl _

/-- The physical profile has the exact cubic-denominator numerator used by
the cleared cell. -/
theorem sevenDirichletProfile_mul_denCube (k : Nat) :
    sevenDirichletProfile k * qcube (Q'.ofNat (k + 2)) ≈
      (Q'.ofNat 12 *
          (Q'.ofNat (k + 2) * Q'.ofNat (k + 2)) +
        Q'.ofNat (k + 2)) + 1 := by
  let U := harmU k
  let D := Q'.ofNat (k + 2)
  have hregroup := RingNormaliser.poly_identity_of_normal_eq
    pProfileScaleL pProfileFactored pProfile_regroup
    (fun | 0 => U | _ => D)
  have hstart : sevenDirichletProfile k * qcube D ≈
      RingNormaliser.eval (fun | 0 => U | _ => D) pProfileScaleL := by
    unfold sevenDirichletProfile qcube pProfileScaleL U D pc padd pmul
      RingNormaliser.eval
    exact Q'.eqv_refl _
  have hfact := profileFactored_eq_inT U D
  have hreplace := polyEval_eqv_congr pProfileInT
    (rho := fun | 0 => U * D | _ => D)
    (sigma := fun | 0 => 1 | _ => D)
    (by
      intro i
      rcases i with _ | i
      · exact harmU_mul_den k
      · exact Q'.eqv_refl D)
  have htarget := RingNormaliser.poly_identity_of_normal_eq
    pProfileOne
    pProfileTarget pProfile_target (fun _ => D)
  have hone : RingNormaliser.eval (fun | 0 => 1 | _ => D) pProfileInT ≈
      RingNormaliser.eval (fun _ => D) pProfileOne := by
    unfold pProfileInT pProfileOne pc padd pmul RingNormaliser.eval
    exact Q'.eqv_refl _
  have hout : RingNormaliser.eval (fun _ => D) pProfileTarget ≈
      (Q'.ofNat 12 * (D * D) + D) + 1 := by
    unfold pProfileTarget pc padd pmul RingNormaliser.eval
    exact Q'.eqv_refl _
  exact Q'.eqv_trans _ _ _ hstart
    (Q'.eqv_trans _ _ _ hregroup
      (Q'.eqv_trans _ _ _ hfact
        (Q'.eqv_trans _ _ _ hreplace
          (Q'.eqv_trans _ _ _ hone
            (Q'.eqv_trans _ _ _ htarget hout)))))

private def pModeScaled : PE :=
  let P : PE := .var 0
  let R : PE := .var 1
  let C : PE := .var 2
  let N : PE := .var 3
  pmul (padd (pmul P (pmul N N))
    (pneg (pmul (pc 4) (pmul R R)))) (pmul C C)

private def pModeFactored : PE :=
  let P : PE := .var 0
  let R : PE := .var 1
  let C : PE := .var 2
  let N : PE := .var 3
  let A := pmul P C
  let S := pmul R C
  padd (pmul (pmul A (pmul N N)) C)
    (pneg (pmul (pc 4) (pmul S S)))

private def pAbstractCleared : PE :=
  let A : PE := .var 0
  let S : PE := .var 1
  let C : PE := .var 2
  let N : PE := .var 3
  padd (pmul (pmul A (pmul N N)) C)
    (pneg (pmul (pc 4) (pmul S S)))

private theorem pMode_scale_normal :
    RingNormaliser.normalize pModeScaled =
      RingNormaliser.normalize pModeFactored := by decide

private theorem modeFactored_eq_abstract (P R C N : Q') :
    RingNormaliser.eval (fun | 0 => P | 1 => R | 2 => C | _ => N)
        pModeFactored ≈
      RingNormaliser.eval
        (fun | 0 => P * C | 1 => R * C | 2 => C | _ => N)
        pAbstractCleared := by
  unfold pModeFactored pAbstractCleared pc padd pmul pneg
    RingNormaliser.eval
  exact Q'.eqv_refl _

private def pSlopeLocal (D N : PE) : PE :=
  padd (pmul N (ppow D 3))
    (pneg (pmul (padd N (pc 1))
      (pmul (psub D (pc 1)) (ppow (psub D N) 2))))

private def pCellLocal (D N : PE) : PE :=
  padd
    (pmul (pmul
      (padd (padd (pmul (pc 12) (ppow D 2)) D) (pc 1))
      (ppow N 2)) (ppow D 3))
    (pneg (pmul (pc 4) (ppow (pSlopeLocal D N) 2)))

private def pSlopeExplicit (D N : PE) : PE :=
  padd (pmul N (pmul (pmul D D) D))
    (pneg (pmul (padd N (pc 1))
      (pmul (psub D (pc 1))
        (pmul (psub D N) (psub D N)))))

private def pCellInstantiated (D N : PE) : PE :=
  let A := padd (padd (pmul (pc 12) (pmul D D)) D) (pc 1)
  let S := pSlopeExplicit D N
  let C := pmul (pmul D D) D
  padd (pmul (pmul A (pmul N N)) C)
    (pneg (pmul (pc 4) (pmul S S)))

private theorem pCell_instantiated_normal :
    RingNormaliser.normalize (pCellInstantiated (.var 0) (.var 1)) =
      RingNormaliser.normalize (pCellLocal (.var 0) (.var 1)) := by decide

private theorem cleared_eq_local (D N : Q') :
    RingNormaliser.eval
        (fun
          | 0 => (Q'.ofNat 12 * (D * D) + D) + 1
          | 1 => thetaCubicSlopePolynomial D N
          | 2 => qcube D
          | _ => N)
        pAbstractCleared ≈ thetaCubicClearedCell D N := by
  have hleft : RingNormaliser.eval
        (fun
          | 0 => (Q'.ofNat 12 * (D * D) + D) + 1
          | 1 => thetaCubicSlopePolynomial D N
          | 2 => qcube D
          | _ => N)
        pAbstractCleared ≈
      RingNormaliser.eval (fun | 0 => D | _ => N)
        (pCellInstantiated (.var 0) (.var 1)) := by
    unfold pAbstractCleared pCellInstantiated pSlopeExplicit
      thetaCubicSlopePolynomial qcube pc padd pmul pneg psub
      RingNormaliser.eval
    exact Q'.eqv_refl _
  have hpoly := RingNormaliser.poly_identity_of_normal_eq
    (pCellInstantiated (.var 0) (.var 1))
    (pCellLocal (.var 0) (.var 1)) pCell_instantiated_normal
    (fun | 0 => D | _ => N)
  have himport : RingNormaliser.eval (fun | 0 => D | _ => N)
        (pCellLocal (.var 0) (.var 1)) ≈ thetaCubicClearedCell D N := by
    unfold thetaCubicClearedCell pCellLocal pSlopeLocal
    exact Q'.eqv_refl _
  exact Q'.eqv_trans _ _ _ hleft (Q'.eqv_trans _ _ _ hpoly himport)

/-- Exact physical-to-cleared identity for one mode cell. -/
theorem thetaCubicModeCell_mul_denSix (k n : Nat) :
    let D := Q'.ofNat (k + 2)
    thetaCubicModeCell k n * (qcube D * qcube D) ≈
      thetaCubicClearedCell D (Q'.ofNat n) := by
  dsimp only
  let D := Q'.ofNat (k + 2)
  let N := Q'.ofNat n
  let P := sevenDirichletProfile k
  let R := thetaCubicRightCarrier k n
  let C := qcube D
  have hscale := RingNormaliser.poly_identity_of_normal_eq
    pModeScaled pModeFactored pMode_scale_normal
    (fun | 0 => P | 1 => R | 2 => C | _ => N)
  have hstart : thetaCubicModeCell k n * (C * C) ≈
      RingNormaliser.eval
        (fun | 0 => P | 1 => R | 2 => C | _ => N) pModeScaled := by
    unfold thetaCubicModeCell pModeScaled P R C N pc padd pmul pneg
      RingNormaliser.eval
    exact Q'.eqv_refl _
  have habstract := modeFactored_eq_abstract P R C N
  have hprofile := sevenDirichletProfile_mul_denCube k
  have hslope := thetaCubicRightCarrier_mul_denCube k n
  have hreplace := polyEval_eqv_congr pAbstractCleared
    (rho := fun | 0 => P * C | 1 => R * C | 2 => C | _ => N)
    (sigma := fun
      | 0 => (Q'.ofNat 12 * (D * D) + D) + 1
      | 1 => thetaCubicSlopePolynomial D N
      | 2 => C
      | _ => N)
    (by
      intro i
      rcases i with _ | i
      · exact hprofile
      rcases i with _ | i
      · exact hslope
      rcases i with _ | i
      · exact Q'.eqv_refl C
      · exact Q'.eqv_refl N)
  exact Q'.eqv_trans _ _ _ hstart
    (Q'.eqv_trans _ _ _ hscale
      (Q'.eqv_trans _ _ _ habstract
        (Q'.eqv_trans _ _ _ hreplace (cleared_eq_local D N))))

theorem thetaCubicClearedCell_eqv_congr {D D' N N' : Q'}
    (hD : D ≈ D') (hN : N ≈ N') :
    thetaCubicClearedCell D N ≈ thetaCubicClearedCell D' N' := by
  unfold thetaCubicClearedCell
  apply polyEval_eqv_congr
  intro i
  rcases i with _ | i
  · exact hD
  · exact hN

def thetaCubicModeBlock (k start count : Nat) : Q' :=
  fsum (fun j => thetaCubicModeCell k (start + j)) count

/-- Exact `D^6` scaling for a consecutive physical mode block. -/
theorem thetaCubicModeBlock_mul_denSix (k start count : Nat) :
    let D := Q'.ofNat (k + 2)
    thetaCubicModeBlock k start count * (qcube D * qcube D) ≈
      thetaCubicClearedBlock D (Q'.ofNat start) count := by
  dsimp only
  let D := Q'.ofNat (k + 2)
  have hpull := YMGap.Continuum.CubeRatioBounds.fsum_mul_const
    (fun j => thetaCubicModeCell k (start + j))
    (qcube D * qcube D) count
  have hterms := YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
    (fun j => thetaCubicModeCell k (start + j) * (qcube D * qcube D))
    (fun j => thetaCubicClearedCell D
      (Q'.ofNat start + Q'.ofNat j))
    (fun j =>
      Q'.eqv_trans _ _ _ (thetaCubicModeCell_mul_denSix k (start + j))
        (thetaCubicClearedCell_eqv_congr (Q'.eqv_refl D)
          (Q'.ofNat_add_eqv start j))) count
  unfold thetaCubicModeBlock thetaCubicClearedBlock
  exact Q'.eqv_trans _ _ _ hpull hterms

#print axioms sevenDirichletProfile_mul_denCube
#print axioms thetaCubicModeCell_mul_denSix
#print axioms thetaCubicClearedCell_eqv_congr
#print axioms thetaCubicModeBlock
#print axioms thetaCubicModeBlock_mul_denSix

end YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFullEndpointPhysical
