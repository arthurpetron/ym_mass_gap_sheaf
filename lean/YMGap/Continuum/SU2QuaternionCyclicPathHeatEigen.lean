/-
# Original full heat on one actual cyclic path leaf

The per-output-block literal Casimir eigenpins separate distinct full degree
paths under the original Haar pairing.  Reassembling the computed test tree
then gives the exact action of the original full product map on a valid path
leaf.  The statement uses supported tests; it introduces no spectral premise.
-/

import YMGap.Continuum.SU2QuaternionCyclicPathBlockCasimir
import YMGap.Continuum.SU2QuaternionLiteralCasimirPairing
import YMGap.Continuum.SU2QuaternionProductHeatDualForm

namespace YMGap.Continuum.SU2QuaternionCyclicPathHeatEigen

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare
open YMGap.Continuum.SU2QuaternionCyclicHeatModeExpansion
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor
open YMGap.Continuum.SU2QuaternionCyclicDiagonalRemainder
open YMGap.Continuum.SU2QuaternionCyclicPathReassembly
open YMGap.Continuum.SU2QuaternionCyclicPathBlockCasimir
open YMGap.Continuum.SU2QuaternionLiteralCasimirPairing
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatDualForm
open YMGap.Continuum.SU2HeatProductTaylorRemainder
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

/-- The exact polynomial at any computed path endpoint remains on its
original carrier, whether or not the path is valid. -/
theorem path_supported (tail : Nat) :
    ∀ (ds : List Nat) (p : RatPoly),
      SupportedQuaternionBlocks (tail+1) p →
      SupportedQuaternionBlocks (tail+1) (pathPiece tail p ds)
  | [], _, hp => hp
  | d::ds, p, _hp =>
      path_supported tail ds (nextPiece tail p d)
        (nextPiece_supported tail p d)

private theorem distinct_slot : ∀ (left right : List Nat),
    left.length = right.length → left ≠ right →
      ∃ s, s < left.length ∧ left.getD s 0 ≠ right.getD s 0
  | [], [], _, hne => False.elim (hne rfl)
  | [], _::_, hlen, _ => by contradiction
  | _::_, [], hlen, _ => by contradiction
  | d::ds, e::es, hlen, hne => by
      by_cases hde : d = e
      · have htlen : ds.length = es.length := Nat.succ.inj hlen
        have htne : ds ≠ es := by
          intro he
          exact hne (by rw [hde, he])
        obtain ⟨s, hs, hd⟩ := distinct_slot ds es htlen htne
        exact ⟨s+1, by simpa only [List.length_cons] using Nat.succ_lt_succ hs,
          by simpa only [List.getD_cons_succ] using hd⟩
      · exact ⟨0, by simp only [List.length_cons]; omega,
          by simpa only [List.getD_cons_zero] using hde⟩

private theorem casimirNat_strict {d e : Nat} (h : d < e) :
    d*(d+2) < e*(e+2) := by
  have hfirst : d*(d+2) ≤ d*(e+2) := Nat.mul_le_mul_left d (by omega)
  have hsecond : d*(e+2) < e*(e+2) :=
    Nat.mul_lt_mul_of_pos_right h (by omega)
  exact Nat.lt_of_le_of_lt hfirst hsecond

private theorem casimirNat_injective {d e : Nat}
    (h : d*(d+2) = e*(e+2)) : d = e := by
  by_cases hde : d < e
  · exact False.elim (Nat.ne_of_lt (casimirNat_strict hde) h)
  by_cases hed : e < d
  · exact False.elim (Nat.ne_of_gt (casimirNat_strict hed) h)
  omega

private theorem ofNat_mul_eqv_zero_of_ne {a b : Nat} {x : Q'}
    (hab : a ≠ b) (h : (Q'.ofNat a * x) ≈ (Q'.ofNat b * x)) : x ≈ 0 := by
  have hnum : (Int.ofNat a) * x.num = (Int.ofNat b) * x.num := by
    change ((Int.ofNat a) * x.num) * ((1 : Int) * (x.den : Int)) =
      ((Int.ofNat b) * x.num) * ((1 : Int) * (x.den : Int)) at h
    exact Int.eq_of_mul_eq_mul_right
      (Int.ne_of_gt (Int.ofNat_lt.mpr (Q'.den_pos x))) (by
        simpa only [Int.one_mul] using h)
  by_cases hx : x.num = 0
  · change x.num * ((0 : Q').den : Int) = (0 : Q').num * (x.den : Int)
    rw [hx]
    change (0 : Int)*1 = 0*(x.den : Int)
    simp only [Int.zero_mul]
  · have heq : (Int.ofNat a) = (Int.ofNat b) :=
      Int.eq_of_mul_eq_mul_right hx hnum
    exact False.elim (hab (Int.ofNat.inj heq))

/-- Distinct actual complete path labels are orthogonal in the original Haar
pairing.  This is a derived lemma: the only eigeninput is the proved literal
per-block Casimir action on each valid leaf. -/
private theorem different_paths_pair_zero (tail : Nat) (p q : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p)
    (hq : SupportedQuaternionBlocks (tail+1) q)
    (ds es : List Nat) (hdlen : ds.length = tail+1)
    (helen : es.length = tail+1)
    (hdpath : ValidPath tail p ds) (hepath : ValidPath tail q es)
    (hne : ds ≠ es) :
    H (tail+1) (polyMul (pathPiece tail q es) (pathPiece tail p ds)) ≈ 0 := by
  obtain ⟨s, hs, hdegree⟩ := distinct_slot ds es (hdlen.trans helen.symm) hne
  have hs' : s < tail+1 := by rwa [hdlen] at hs
  let u := pathPiece tail p ds
  let v := pathPiece tail q es
  let a := Q'.ofNat ((ds.getD s 0)*((ds.getD s 0)+2))
  let b := Q'.ofNat ((es.getD s 0)*((es.getD s 0)+2))
  have hcas : (ds.getD s 0)*((ds.getD s 0)+2) ≠
      (es.getD s 0)*((es.getD s 0)+2) :=
    fun he => hdegree (casimirNat_injective he)
  have hu := full_path_blockCasimir_carrier tail p hp ds hdlen hdpath s hs'
  have hv := full_path_blockCasimir_carrier tail q hq es helen hepath s hs'
  have hleft : H (tail+1) (polyMul v (activeCasimirPolynomial [s] u)) ≈
      a * H (tail+1) (polyMul v u) :=
    Q'.eqv_trans _ _ _ (hu v)
      (quaternionHaar_polyMul_smul_right (tail+1) a v u)
  have hright : H (tail+1) (polyMul u (activeCasimirPolynomial [s] v)) ≈
      b * H (tail+1) (polyMul u v) :=
    Q'.eqv_trans _ _ _ (hv u)
      (quaternionHaar_polyMul_smul_right (tail+1) b u v)
  have hcomm : H (tail+1) (polyMul u v) ≈ H (tail+1) (polyMul v u) :=
    haar_of_coeff (RatPolyCoeffEqv.mul_comm u v)
  have heigen : a * H (tail+1) (polyMul v u) ≈
      b * H (tail+1) (polyMul v u) :=
    Q'.eqv_trans _ _ _ hleft.symm
      (Q'.eqv_trans _ _ _
        (literalPair_symm (tail+1) [s]
          (fun i hi => by
            simp only [List.mem_singleton] at hi
            subst i
            exact hs') u v)
        (Q'.eqv_trans _ _ _ hright
          (Q'.mul_eqv_congr_left _ _ _ hcomm)))
  exact ofNat_mul_eqv_zero_of_ne hcas heigen

/-- The literal full product heat acts diagonally on a proved valid cyclic
path leaf when tested against any supported original-carrier polynomial. -/
theorem full_path_heat_pairing (tail : Nat) (w : Q') (K : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) (ds : List Nat)
    (hlen : ds.length = tail+1) (hpath : ValidPath tail p ds)
    (test : RatPoly) (ht : SupportedQuaternionBlocks (tail+1) test) :
    H (tail+1) (polyMul test
      (productMap (tail+1) w K (List.range (tail+1)) (pathPiece tail p ds))) ≈
      productAttenuation w K ds *
        H (tail+1) (polyMul test (pathPiece tail p ds)) := by
  let u := pathPiece tail p ds
  let a := productAttenuation w K ds
  have hu : SupportedQuaternionBlocks (tail+1) u :=
    path_supported tail ds p hp
  have hsymm := kineticPair_symm (tail+1) w K (List.range (tail+1))
    (fun i hi => List.mem_range.mp hi) test u ht hu
  have hexp : H (tail+1) (polyMul u
      (productMap (tail+1) w K (List.range (tail+1)) test)) ≈
      leafSum tail (tail+1) test u (productAttenuation w K) :=
    Q'.eqv_trans _ _ _ ((productMap_modeFold tail w K test ht) u)
      (leafSum_modeFold tail (tail+1) test u (productAttenuation w K))
  have hterms : leafSum tail (tail+1) test u (productAttenuation w K) ≈
      leafSum tail (tail+1) test u (fun _ => a) := by
    apply leafSum_pairing_congr
    intro es helen hepath
    by_cases heq : es = ds
    · subst es
      exact Q'.eqv_refl _
    · have hz := different_paths_pair_zero tail p test hp ht ds es hlen helen
        hpath hepath (Ne.symm heq)
      have hz' : H (tail+1) (polyMul u (pathPiece tail test es)) ≈ 0 :=
        Q'.eqv_trans _ _ _
          (haar_of_coeff (RatPolyCoeffEqv.mul_comm u (pathPiece tail test es))) hz
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _ hz')
        (Q'.eqv_trans _ _ _ (Q'.mul_zero_eqv _)
          (Q'.eqv_symm (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left _ _ _ hz')
            (Q'.mul_zero_eqv _))))
  have hconst : leafSum tail (tail+1) test u (fun _ => a) ≈
      a * H (tail+1) (polyMul u test) :=
    Q'.eqv_trans _ _ _
      (leafSum_congr tail (tail+1) test u _ _
        (fun _ _ => Q'.eqv_symm (Q'.mul_one_eqv a)))
      (Q'.eqv_trans _ _ _
        (leafSum_smul tail (tail+1) test u a (fun _ => (1 : Q')))
        (Q'.mul_eqv_congr_left _ _ _ (full_leafSum_one tail test u ht)))
  exact Q'.eqv_trans _ _ _ hsymm
    (Q'.eqv_trans _ _ _ hexp
      (Q'.eqv_trans _ _ _ hterms
        (Q'.eqv_trans _ _ _ hconst
          (Q'.mul_eqv_congr_left _ _ _
            (haar_of_coeff (RatPolyCoeffEqv.mul_comm u test))))))

end YMGap.Continuum.SU2QuaternionCyclicPathHeatEigen

#print axioms YMGap.Continuum.SU2QuaternionCyclicPathHeatEigen.path_supported
#print axioms YMGap.Continuum.SU2QuaternionCyclicPathHeatEigen.full_path_heat_pairing
