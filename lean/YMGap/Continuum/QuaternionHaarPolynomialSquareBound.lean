/-
# Computed polynomial square bounds on the ORIGINAL quaternion Haar carrier

A bound is an explicit rational cap and an existing sum-of-squares
certificate for cap - p^2, valid under every Haar insertion. Addition,
multiplication and arbitrary rational scaling construct the certificates.
The scalar of an actual Haar-unit quaternion has cap one. The character
recurrence then gives a computable (not sharp) cap at every spin, independent
of the number of Haar blocks. No probability law or spectral bound is assumed.
-/

import YMGap.Continuum.QuaternionHaarUnitScalarSquare

namespace YMGap.Continuum.QuaternionHaarPolynomialSquareBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarUnitScalarSquare

def cap (c : Q') : RatPoly := polySmul c polyOne
def gap (c : Q') (p : RatPoly) : RatPoly := polyAdd (cap c) (polyNeg (polyMul p p))

/-- Constructed positive-polynomial evidence, not an analytic hypothesis. -/
structure SquareBound (blocks : Nat) (p : RatPoly) (c : Q') : Type where
  support : SupportedQuaternionBlocks blocks p
  nonnegative : (0 : Q') ≤ c
  certificate : Certificate blocks (gap c p)

private theorem support_smul {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) (c : Q') : SupportedQuaternionBlocks blocks (polySmul c p) := by
  intro t ht
  obtain ⟨s, hs, he⟩ := List.mem_map.mp ht
  rw [← he]
  exact hp s hs

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) : SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, he⟩ := List.mem_map.mp ht
  rw [← he]
  exact hp s hs

theorem cap_add (a b : Q') : RatPolyCoeffEqv (polyAdd (cap a) (cap b)) (cap (a+b)) :=
  RatPolyCoeffEqv.add_smul_same a b polyOne

theorem cap_mul_left (a : Q') (p : RatPoly) : RatPolyCoeffEqv (polyMul (cap a) p) (polySmul a p) :=
  (RatPolyCoeffEqv.polyMul_smul_left a polyOne p).trans ((RatPolyCoeffEqv.one_mul p).smul a)

theorem cap_mul (a b : Q') : RatPolyCoeffEqv (polyMul (cap a) (cap b)) (cap (a*b)) :=
  (cap_mul_left a (cap b)).trans (RatPolyCoeffEqv.smul_assoc a b polyOne)

private theorem cancel (p : RatPoly) : RatPolyCoeffEqv (polyAdd p (polyNeg p)) (cap 0) :=
  coeffEvalExpr_eqv_of_normalize_eq (.add (.var 0) (.neg (.var 0))) (.const 0) (by decide) (fun _ => p)

private def halveDouble {blocks : Nat} {p q : RatPoly}
    (h : RatPolyCoeffEqv (polyAdd p p) q) (Q : Certificate blocks q) : Certificate blocks p := by
  have he : RatPolyCoeffEqv (polySmul HalfPow.half (polyAdd p p)) p :=
    (RatPolyCoeffEqv.smul_add _ _ _).trans ((RatPolyCoeffEqv.add_smul_same _ _ _).trans
      ((RatPolyCoeffEqv.smul_coefficient (by decide) p).trans (RatPolyCoeffEqv.one_smul p)))
  exact .ofCoeff he.symm (.smul HalfPow.half HalfPow.half_nonneg (.ofCoeff h Q))

private def sq (p : PolyExpr) : PolyExpr := .mul p p
private def diff (p q : PolyExpr) : PolyExpr := .add p (.neg q)
private def twice (p : PolyExpr) : PolyExpr := .add p p
private def env4 (a b p q : RatPoly) : Nat → RatPoly
  | 0 => a | 1 => b | 2 => p | 3 => q | _ => polyZero

def sumBound (a b : Q') : Q' := (a+a)+(b+b)

namespace SquareBound

def ofCoeff {blocks : Nat} {p q : RatPoly} {c : Q'}
    (hp : SupportedQuaternionBlocks blocks p) (h : RatPolyCoeffEqv p q) (Q : SquareBound blocks q c) :
    SquareBound blocks p c where
  support := hp
  nonnegative := Q.nonnegative
  certificate := .ofCoeff ((RatPolyCoeffEqv.refl (cap c)).add (RatPolyCoeffEqv.neg (h.mul h))) Q.certificate

def changeCap {blocks : Nat} {p : RatPoly} {c d : Q'} (h : Q'.eqv c d) (P : SquareBound blocks p c) :
    SquareBound blocks p d where
  support := P.support
  nonnegative := Q'.le_trans' _ _ _ P.nonnegative (Q'.le_of_eqv h)
  certificate := .ofCoeff ((RatPolyCoeffEqv.smul_coefficient (Q'.eqv_symm h) polyOne).add
    (RatPolyCoeffEqv.refl _)) P.certificate

def constant (blocks : Nat) (c : Q') : SquareBound blocks (cap c) (c*c) where
  support := support_smul (supported_one blocks) c
  nonnegative := SumOfSquares.q_mul_self_nonneg c
  certificate := .ofCoeff
    (((cap_mul c c).symm.add (RatPolyCoeffEqv.refl _)).trans (cancel _))
    (.constant blocks 0 (Q'.le_refl' _))

def one (blocks : Nat) : SquareBound blocks polyOne 1 :=
  ofCoeff (supported_one blocks) (RatPolyCoeffEqv.one_smul polyOne).symm
    (changeCap (by decide : Q'.eqv ((1 : Q')*1) 1) (constant blocks 1))

/-- 2(a+b)-(p+q)^2 = 2(a-p^2)+2(b-q^2)+(p-q)^2. -/
def add {blocks : Nat} {p q : RatPoly} {a b : Q'} (P : SquareBound blocks p a) (Q : SquareBound blocks q b) :
    SquareBound blocks (polyAdd p q) (sumBound a b) where
  support := supported_add P.support Q.support
  nonnegative := Q'.zero_le_add _ _ (Q'.zero_le_add _ _ P.nonnegative P.nonnegative)
    (Q'.zero_le_add _ _ Q.nonnegative Q.nonnegative)
  certificate := by
    have hc := ((cap_add a a).add (cap_add b b)).trans (cap_add (a+a) (b+b))
    have he := coeffEvalExpr_eqv_of_normalize_eq
      (diff (.add (twice (.var 0)) (twice (.var 1))) (sq (.add (.var 2) (.var 3))))
      (.add (.add (twice (diff (.var 0) (sq (.var 2)))) (twice (diff (.var 1) (sq (.var 3)))))
        (sq (diff (.var 2) (.var 3)))) (by decide) (env4 (cap a) (cap b) p q)
    exact .ofCoeff ((hc.symm.add (RatPolyCoeffEqv.refl _)).trans he)
      (.add (.add (.add P.certificate P.certificate) (.add Q.certificate Q.certificate))
        (.square (polyAdd p (polyNeg q)) (supported_add P.support (support_neg Q.support))))

/-- ab-(pq)^2 = b(a-p^2)+p^2(b-q^2), retaining all shared variables. -/
def mul {blocks : Nat} {p q : RatPoly} {a b : Q'} (P : SquareBound blocks p a) (Q : SquareBound blocks q b) :
    SquareBound blocks (polyMul p q) (a*b) where
  support := supported_polyMul P.support Q.support
  nonnegative := Q'.mul_nonneg _ _ P.nonnegative Q.nonnegative
  certificate := by
    have he := coeffEvalExpr_eqv_of_normalize_eq
      (diff (.mul (.var 0) (.var 1)) (sq (.mul (.var 2) (.var 3))))
      (.add (.mul (.var 1) (diff (.var 0) (sq (.var 2))))
        (.mul (sq (.var 2)) (diff (.var 1) (sq (.var 3)))))
      (by decide) (env4 (cap a) (cap b) p q)
    exact .ofCoeff (((cap_mul a b).symm.add (RatPolyCoeffEqv.refl _)).trans he)
      (.add ((Certificate.constant blocks b Q.nonnegative).mul P.certificate)
        (Certificate.multiplySquare p P.support Q.certificate))

def smul {blocks : Nat} {p : RatPoly} {a : Q'} (c : Q') (P : SquareBound blocks p a) :
    SquareBound blocks (polySmul c p) ((c*c)*a) :=
  ofCoeff (support_smul P.support c) (cap_mul_left c p).symm ((constant blocks c).mul P)

def neg {blocks : Nat} {p : RatPoly} {c : Q'} (P : SquareBound blocks p c) :
    SquareBound blocks (polyNeg p) c where
  support := support_neg P.support
  nonnegative := P.nonnegative
  certificate := .ofCoeff ((RatPolyCoeffEqv.refl (cap c)).add (RatPolyCoeffEqv.neg
    (coeffEvalExpr_eqv_of_normalize_eq (sq (.neg (.var 0))) (sq (.var 0)) (by decide) (fun _ => p)))) P.certificate

def raise {blocks : Nat} {p : RatPoly} {c : Q'} (P : SquareBound blocks p c) (d : Q') (hd : (0 : Q') ≤ d) :
    SquareBound blocks p (c+d) where
  support := P.support
  nonnegative := Q'.zero_le_add _ _ P.nonnegative hd
  certificate := .ofCoeff (((cap_add c d).symm.add (RatPolyCoeffEqv.refl _)).trans
    (coeffEvalExpr_eqv_of_normalize_eq (diff (.add (.var 0) (.var 1)) (sq (.var 2)))
      (.add (diff (.var 0) (sq (.var 2))) (.var 1)) (by decide) (env4 (cap c) (cap d) p polyZero)))
    (.add P.certificate (.constant blocks d hd))

/-- 2(c-pq) = (c-p^2)+(c-q^2)+(p-q)^2; no disjoint-support premise. -/
def cross {blocks : Nat} {p q : RatPoly} {c : Q'} (P : SquareBound blocks p c) (Q : SquareBound blocks q c) :
    Certificate blocks (polyAdd (cap c) (polyNeg (polyMul p q))) :=
  halveDouble
    (coeffEvalExpr_eqv_of_normalize_eq (twice (diff (.var 0) (.mul (.var 2) (.var 3))))
      (.add (.add (diff (.var 0) (sq (.var 2))) (diff (.var 0) (sq (.var 3))))
        (sq (diff (.var 2) (.var 3)))) (by decide) (env4 (cap c) polyZero p q))
    (.add (.add P.certificate Q.certificate)
      (.square (polyAdd p (polyNeg q)) (supported_add P.support (support_neg Q.support))))

/-- A square-root-free linear cap, sufficient for uniform moment bounds. -/
def linear {blocks : Nat} {p : RatPoly} {c : Q'} (P : SquareBound blocks p c) :
    Certificate blocks (polyAdd (cap (c+1)) (polyNeg p)) :=
  .ofCoeff ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg (RatPolyCoeffEqv.mul_one p).symm))
    ((P.raise 1 Q'.zero_le_one).cross
      (changeCap (Q'.add_comm_eqv 1 c) ((one blocks).raise c P.nonnegative)))

/-- The three remaining quaternion components certify 1-scalar^2. -/
def scalar {blocks : Nat} {p : PolyQuaternion} (hp : Supported blocks p)
    (hnorm : HaarCarrierEqv blocks (polyQuaternionNorm p) polyOne) : SquareBound blocks p.scalar 1 where
  support := hp.scalar
  nonnegative := Q'.zero_le_one
  certificate := by
    have he : RatPolyCoeffEqv
        (polyAdd (polyQuaternionNorm p) (polyNeg (polyMul p.scalar p.scalar)))
        (polyAdd (polyMul p.iPart p.iPart) (polyAdd (polyMul p.jPart p.jPart) (polyMul p.kPart p.kPart))) :=
      coeffEvalExpr_eqv_of_normalize_eq
        (diff (.add (sq (.var 0)) (.add (sq (.var 1)) (.add (sq (.var 2)) (sq (.var 3))))) (sq (.var 0)))
        (.add (sq (.var 1)) (.add (sq (.var 2)) (sq (.var 3)))) (by decide)
        (env4 p.scalar p.iPart p.jPart p.kPart)
    exact .transport
      ((HaarCarrierEqv.add (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.one_smul polyOne)) (HaarCarrierEqv.refl blocks _)).trans
        ((HaarCarrierEqv.add hnorm.symm (HaarCarrierEqv.refl blocks _)).trans (RatPolyCoeffEqv.haarCarrier he)))
      (.add (.square p.iPart hp.iPart) (.add (.square p.jPart hp.jPart) (.square p.kPart hp.kPart)))

end SquareBound

/-- A deliberately coarse rational cap computed solely from the spin. -/
def characterBound : Nat → Q'
  | 0 => 1
  | 1 => (2*2)*1
  | n+2 => sumBound (((2*2)*1)*characterBound (n+1)) (((-1)*(-1))*characterBound n)

def character_squareBound {blocks : Nat} {p : RatPoly} (P : SquareBound blocks p 1) :
    ∀ spin, SquareBound blocks (characterPolynomial p spin) (characterBound spin)
  | 0 => .one blocks
  | 1 => P.smul 2
  | n+2 => ((P.smul 2).mul (character_squareBound P (n+1))).add ((character_squareBound P n).smul (-1))

end YMGap.Continuum.QuaternionHaarPolynomialSquareBound

#print axioms YMGap.Continuum.QuaternionHaarPolynomialSquareBound.cap
#print axioms YMGap.Continuum.QuaternionHaarPolynomialSquareBound.gap
#print axioms YMGap.Continuum.QuaternionHaarPolynomialSquareBound.SquareBound
#print axioms YMGap.Continuum.QuaternionHaarPolynomialSquareBound.cap_add
#print axioms YMGap.Continuum.QuaternionHaarPolynomialSquareBound.cap_mul_left
#print axioms YMGap.Continuum.QuaternionHaarPolynomialSquareBound.cap_mul
#print axioms YMGap.Continuum.QuaternionHaarPolynomialSquareBound.sumBound
#print axioms YMGap.Continuum.QuaternionHaarPolynomialSquareBound.SquareBound.ofCoeff
#print axioms YMGap.Continuum.QuaternionHaarPolynomialSquareBound.SquareBound.changeCap
#print axioms YMGap.Continuum.QuaternionHaarPolynomialSquareBound.SquareBound.constant
#print axioms YMGap.Continuum.QuaternionHaarPolynomialSquareBound.SquareBound.one
#print axioms YMGap.Continuum.QuaternionHaarPolynomialSquareBound.SquareBound.add
#print axioms YMGap.Continuum.QuaternionHaarPolynomialSquareBound.SquareBound.mul
#print axioms YMGap.Continuum.QuaternionHaarPolynomialSquareBound.SquareBound.smul
#print axioms YMGap.Continuum.QuaternionHaarPolynomialSquareBound.SquareBound.neg
#print axioms YMGap.Continuum.QuaternionHaarPolynomialSquareBound.SquareBound.raise
#print axioms YMGap.Continuum.QuaternionHaarPolynomialSquareBound.SquareBound.cross
#print axioms YMGap.Continuum.QuaternionHaarPolynomialSquareBound.SquareBound.linear
#print axioms YMGap.Continuum.QuaternionHaarPolynomialSquareBound.SquareBound.scalar
#print axioms YMGap.Continuum.QuaternionHaarPolynomialSquareBound.characterBound
#print axioms YMGap.Continuum.QuaternionHaarPolynomialSquareBound.character_squareBound
