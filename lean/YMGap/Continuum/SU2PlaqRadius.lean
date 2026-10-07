/-
# Plaquette radius relation and the plaquette character-square bound

(YM Group Realizer.)  Euler four-square identity for polynomial quaternions
(`norm_mul : N(pq) ≅ N(p)N(q)`, `norm_conj : N(q*) ≅ N(q)`, reflective
normaliser), iterated over the plaquette word `q₁q₂q₃*q₄*`.  Each link's block
sphere (`block_radius_carrier`) makes `N(word)` Haar-trivial
(`plaqWord_radius_carrier`), so `character_square_haar_le` gives

  `plaq_character_square_le : (multiLinkHaar links.length).h (χ_s(plaqWord)²) ≤ (s+1)²`

for every spin, with only `LinksCover` (no distinctness needed: repeated
links just reuse the same sphere relation).
-/

import YMGap.Continuum.SU2CharacterHaarBound
import YMGap.Continuum.SU2PlaqWordHolonomy

namespace YMGap.Continuum.SU2PlaqRadius

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction (HaarCarrierEqv HaarCarrierEqv.refl
  HaarCarrierEqv.trans HaarCarrierEqv.symm)
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2QuaternionGlobalFaceRatPolySupport
open YMGap.Continuum.SU2CharacterSquareIdentity
open YMGap.Continuum.SU2CharacterHaarBound
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TorusGeometry
open YMGap.Continuum.SU2TorusMultiLinkPolyGibbs

local infix:50 " ≅ " => RatPolyCoeffEqv

/-- Quaternion norm `N(q) = s² + i² + j² + k²`. -/
abbrev Nq (q : PolyQuaternion) : RatPoly := radius q.scalar q.iPart q.jPart q.kPart

private def env8 (q r : PolyQuaternion) : Nat → RatPoly :=
  ev [q.scalar, q.iPart, q.jPart, q.kPart, r.scalar, r.iPart, r.jPart, r.kPart]

private def sq (e : PolyExpr) : PolyExpr := .mul e e
private def nE (a b c d : PolyExpr) : PolyExpr := .add (.add (.add (sq a) (sq b)) (sq c)) (sq d)
private def mS : PolyExpr :=
  .add (.mul (v 0) (v 4)) (.neg (.add (.mul (v 1) (v 5)) (.add (.mul (v 2) (v 6)) (.mul (v 3) (v 7)))))
private def mI : PolyExpr :=
  .add (.mul (v 0) (v 5)) (.add (.mul (v 1) (v 4)) (.add (.mul (v 2) (v 7)) (.neg (.mul (v 3) (v 6)))))
private def mJ : PolyExpr :=
  .add (.mul (v 0) (v 6)) (.add (.mul (v 2) (v 4)) (.add (.mul (v 3) (v 5)) (.neg (.mul (v 1) (v 7)))))
private def mK : PolyExpr :=
  .add (.mul (v 0) (v 7)) (.add (.mul (v 3) (v 4)) (.add (.mul (v 1) (v 6)) (.neg (.mul (v 2) (v 5)))))

/-- **Euler four-square identity**: `N(qr) ≅ N(q) N(r)`. -/
theorem norm_mul (q r : PolyQuaternion) :
    Nq (PolyQuaternion.mul q r) ≅ polyMul (Nq q) (Nq r) :=
  norm (env := env8 q r) (nE mS mI mJ mK)
    (.mul (nE (v 0) (v 1) (v 2) (v 3)) (nE (v 4) (v 5) (v 6) (v 7))) (by decide)

/-- `N(q*) ≅ N(q)`. -/
theorem norm_conj (q : PolyQuaternion) : Nq (PolyQuaternion.conj q) ≅ Nq q :=
  norm (env := env8 q q) (nE (v 0) (.neg (v 1)) (.neg (v 2)) (.neg (v 3)))
    (nE (v 0) (v 1) (v 2) (v 3)) (by decide)

private theorem one_one : polyMul polyOne polyOne ≅ polyOne := RatPolyCoeffEqv.one_mul polyOne

/-- Word radius: `N(ab(c*)(d*))` is Haar-trivial when each factor's is. -/
theorem word_radius_carrier {n : Nat} (a b c d : PolyQuaternion)
    (ha : HaarCarrierEqv n (Nq a) polyOne) (hb : HaarCarrierEqv n (Nq b) polyOne)
    (hc : HaarCarrierEqv n (Nq c) polyOne) (hd : HaarCarrierEqv n (Nq d) polyOne) :
    HaarCarrierEqv n
      (Nq (PolyQuaternion.mul (PolyQuaternion.mul a b)
        (PolyQuaternion.mul (PolyQuaternion.conj c) (PolyQuaternion.conj d)))) polyOne := by
  have e : Nq (PolyQuaternion.mul (PolyQuaternion.mul a b)
        (PolyQuaternion.mul (PolyQuaternion.conj c) (PolyQuaternion.conj d))) ≅
      polyMul (polyMul (Nq a) (Nq b)) (polyMul (Nq c) (Nq d)) :=
    (norm_mul _ _).trans (RatPolyCoeffEqv.mul (norm_mul a b)
      ((norm_mul _ _).trans (RatPolyCoeffEqv.mul (norm_conj c) (norm_conj d))))
  refine (RatPolyCoeffEqv.haarCarrier e).trans ?_
  refine (HaarCarrierEqv.mul (HaarCarrierEqv.mul ha hb) (HaarCarrierEqv.mul hc hd)).trans ?_
  exact RatPolyCoeffEqv.haarCarrier ((RatPolyCoeffEqv.mul one_one one_one).trans one_one)

/-! ## Supports -/

def SuppQ (n : Nat) (q : PolyQuaternion) : Prop :=
  SupportedCoordinates (4 * n) q.scalar ∧ SupportedCoordinates (4 * n) q.iPart ∧
    SupportedCoordinates (4 * n) q.jPart ∧ SupportedCoordinates (4 * n) q.kPart

theorem suppQ_mul {n : Nat} {q r : PolyQuaternion} (hq : SuppQ n q) (hr : SuppQ n r) :
    SuppQ n (PolyQuaternion.mul q r) := by
  obtain ⟨q0, q1, q2, q3⟩ := hq
  obtain ⟨r0, r1, r2, r3⟩ := hr
  have m := fun {a b : RatPoly} (ha : SupportedCoordinates (4 * n) a)
    (hb : SupportedCoordinates (4 * n) b) => supportedCoordinates_polyMul ha hb
  have ad := fun {a b : RatPoly} (ha : SupportedCoordinates (4 * n) a)
    (hb : SupportedCoordinates (4 * n) b) => supportedCoordinates_polyAdd ha hb
  have ng := fun {a : RatPoly} (ha : SupportedCoordinates (4 * n) a) => supportedCoordinates_polyNeg ha
  exact ⟨ad (m q0 r0) (ng (ad (m q1 r1) (ad (m q2 r2) (m q3 r3)))),
    ad (m q0 r1) (ad (m q1 r0) (ad (m q2 r3) (ng (m q3 r2)))),
    ad (m q0 r2) (ad (m q2 r0) (ad (m q3 r1) (ng (m q1 r3)))),
    ad (m q0 r3) (ad (m q3 r0) (ad (m q1 r2) (ng (m q2 r1))))⟩

theorem suppQ_conj {n : Nat} {q : PolyQuaternion} (hq : SuppQ n q) : SuppQ n (PolyQuaternion.conj q) :=
  ⟨hq.1, supportedCoordinates_polyNeg hq.2.1, supportedCoordinates_polyNeg hq.2.2.1,
    supportedCoordinates_polyNeg hq.2.2.2⟩

theorem suppQ_var {n k : Nat} (hk : k < n) : SuppQ n (PolyQuaternion.coordinateVariable k) :=
  ⟨supportedCoordinates_polyVar (by omega), supportedCoordinates_polyVar (by omega),
    supportedCoordinates_polyVar (by omega), supportedCoordinates_polyVar (by omega)⟩

/-! ## Plaquette -/

theorem idxOf_lt {ℓ : Z4Link} {l : List Z4Link} (h : ℓ ∈ l) : l.idxOf ℓ < l.length := by
  have hg := YMGap.Continuum.SU2PlaqWordHolonomy.getElem?_idxOf h
  rcases Nat.lt_or_ge (l.idxOf ℓ) l.length with h1 | h1
  · exact h1
  · rw [List.getElem?_eq_none h1] at hg; exact absurd hg (fun h => nomatch h)

theorem linkVar_carrier (links : List Z4Link) {ℓ : Z4Link} (h : ℓ ∈ links) :
    HaarCarrierEqv links.length (Nq (linkVar links ℓ)) polyOne :=
  block_radius_carrier (idxOf_lt h)

theorem plaqWord_radius_carrier (links : List Z4Link) (N : Nat) (p : Z4Plaq)
    (hc : YMGap.Continuum.SU2PlaqWordHolonomy.LinksCover links N p) :
    HaarCarrierEqv links.length (Nq (plaqWord links N p)) polyOne :=
  word_radius_carrier _ _ _ _ (linkVar_carrier links hc.1) (linkVar_carrier links hc.2.1)
    (linkVar_carrier links hc.2.2.1) (linkVar_carrier links hc.2.2.2)

theorem plaqWord_supp (links : List Z4Link) (N : Nat) (p : Z4Plaq)
    (hc : YMGap.Continuum.SU2PlaqWordHolonomy.LinksCover links N p) :
    SuppQ links.length (plaqWord links N p) :=
  suppQ_mul (suppQ_mul (suppQ_var (idxOf_lt hc.1)) (suppQ_var (idxOf_lt hc.2.1)))
    (suppQ_mul (suppQ_conj (suppQ_var (idxOf_lt hc.2.2.1)))
      (suppQ_conj (suppQ_var (idxOf_lt hc.2.2.2))))

/-- **Plaquette character-square bound, all spins.** -/
theorem plaq_character_square_le (links : List Z4Link) (N : Nat) (p : Z4Plaq)
    (hc : YMGap.Continuum.SU2PlaqWordHolonomy.LinksCover links N p) (s : Nat) :
    (multiLinkHaar links.length).h
        (polyMul (plaqCharacter links N p s) (plaqCharacter links N p s)) ≤
      Q'.ofInt (((s : Int) + 1) * ((s : Int) + 1)) :=
  have hs := plaqWord_supp links N p hc
  character_square_haar_le (plaqWord_radius_carrier links N p hc) hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 s

end YMGap.Continuum.SU2PlaqRadius

#print axioms YMGap.Continuum.SU2PlaqRadius.norm_mul
#print axioms YMGap.Continuum.SU2PlaqRadius.norm_conj
#print axioms YMGap.Continuum.SU2PlaqRadius.idxOf_lt
#print axioms YMGap.Continuum.SU2PlaqRadius.plaqWord_radius_carrier
#print axioms YMGap.Continuum.SU2PlaqRadius.plaq_character_square_le
