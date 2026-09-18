/-
# Reversal of a finite chronological quaternion carrier

The explicit involution reverses slice order and preserves all four real
coordinates of every link. A lifted subwindow is carried to its reflected
location, with its internal slice order reversed. All prefix/padding uses
retain explicit support bounds. This is coordinate algebra, not positivity.
-/

import YMGap.Continuum.SU2QuaternionHaarCertificateReindex
import YMGap.Continuum.SU2QuaternionTwoSliceSwap

namespace YMGap.Continuum.SU2QuaternionSliceReversal

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer

private theorem quotient_le {blocks L i : Nat} (hi : i < (L+1)*blocks) :
    i / blocks ≤ L := by
  have hdivision : i/blocks*blocks+i%blocks=i := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod i blocks
  by_cases h : i/blocks ≤ L
  · exact h
  · have hm := Nat.mul_le_mul_right blocks (show L+1 ≤ i/blocks by omega)
    omega

/-- Every finite slice is retained, including the zero-block case. -/
def sliceReverse (blocks L : Nat) : QuaternionBlockInvolution ((L+1)*blocks) where
  map i := blocks*(L-i/blocks)+i%blocks
  map_lt := by
    intro i hi
    have hn : 0 < blocks := by
      by_cases hz : blocks=0
      · simp only [hz, Nat.mul_zero] at hi
        omega
      · omega
    have hr := Nat.mod_lt i hn
    have hm := Nat.mul_le_mul_left blocks (Nat.sub_le L (i/blocks))
    rw [Nat.mul_comm (L+1) blocks, Nat.mul_succ]
    omega
  involutive := by
    intro i hi
    have hn : 0 < blocks := by
      by_cases hz : blocks=0
      · simp only [hz, Nat.mul_zero] at hi
        omega
      · omega
    have hr := Nat.mod_lt i hn
    have hq := quotient_le hi
    have hd : (blocks*(L-i/blocks)+i%blocks)/blocks = L-i/blocks := by
      rw [Nat.mul_add_div hn, Nat.div_eq_of_lt hr, Nat.add_zero]
    have hm : (blocks*(L-i/blocks)+i%blocks)%blocks = i%blocks := by
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
    rw [hd, hm, Nat.sub_sub_self hq]
    exact Nat.div_add_mod i blocks

theorem sliceReverse_slice (blocks L j r : Nat) (hj : j ≤ L) (hr : r < blocks) :
    (sliceReverse blocks L).map (blocks*j+r) = blocks*(L-j)+r := by
  change blocks*(L-(blocks*j+r)/blocks)+(blocks*j+r)%blocks = _
  rw [Nat.mul_add_div (by omega : 0<blocks), Nat.div_eq_of_lt hr, Nat.add_zero,
    Nat.mul_add_mod, Nat.mod_eq_of_lt hr]

def reversePolynomial (blocks L : Nat) (p : RatPoly) : RatPoly :=
  reindexQuaternionPolynomial (sliceReverse blocks L) p

theorem reversePolynomial_supported (blocks L : Nat) (p : RatPoly) :
    SupportedQuaternionBlocks ((L+1)*blocks) (reversePolynomial blocks L p) :=
  reindex_supported _ p

theorem reversePolynomial_twice (blocks L : Nat) (p : RatPoly) :
    QuaternionPrefixPolynomialEqv ((L+1)*blocks)
      (reversePolynomial blocks L (reversePolynomial blocks L p)) p :=
  reindex_twice_prefix _ p

private theorem exponent_zero : ∀ (m : List Nat) (c : Nat),
    m.length ≤ c → exponentAt m c = 0
  | [], _, _ => rfl
  | _::_, 0, h => by simp at h
  | _::m, c+1, h => by
      simp only [exponentAt, List.getD_cons_succ]
      exact exponent_zero m c (by simp only [List.length_cons] at h; omega)

private theorem lift_list : ∀ (n : Nat) (p : RatPoly),
    liftBoundary n p = p.map (fun t => (List.replicate (4*n) 0 ++ t.1,t.2))
  | 0, p => by
      simpa only [liftBoundary, Nat.mul_zero, List.replicate_zero,
        List.nil_append] using (List.map_id p).symm
  | n+1, p => by
      rw [liftBoundary, lift_list]
      simp only [liftHead, List.map_map]
      apply List.map_congr_left
      intro t _
      rw [show 4*(n+1)=4*n+1+1+1+1 by omega]
      rfl

private theorem exponent_lift : ∀ (n c : Nat) (m : List Nat),
    exponentAt (List.replicate n 0 ++ m) c =
      if c<n then 0 else exponentAt m (c-n)
  | 0, c, m => by simp only [List.replicate_zero, List.nil_append,
      Nat.not_lt_zero, if_false, Nat.sub_zero]
  | n+1, 0, m => by simp only [List.replicate_succ, List.cons_append,
      exponentAt, List.getD_cons_zero, Nat.zero_lt_succ, if_true]
  | n+1, c+1, m => by
      rw [List.replicate_succ, List.cons_append]
      change exponentAt (List.replicate n 0 ++ m) c = _
      rw [exponent_lift]
      by_cases h : c<n
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]
        exact congrArg (exponentAt m) (by omega)

/-- A general involution carries a complete embedded block interval to
another one. The outside case uses involutivity, not a locality assumption. -/
theorem reindex_lift_of_map {source target : Nat}
    (s : QuaternionBlockInvolution target) (t : QuaternionBlockInvolution source)
    (a b : Nat) (ha : a+source ≤ target) (hb : b+source ≤ target)
    (hmap : ∀ i, i<source → s.map (a+i)=b+t.map i)
    (p : RatPoly) (hp : SupportedQuaternionBlocks source p) :
    QuaternionPrefixPolynomialEqv target
      (reindexQuaternionPolynomial s (liftBoundary a p))
      (liftBoundary b (reindexQuaternionPolynomial t p)) := by
  rw [lift_list, lift_list]
  simp only [reindexQuaternionPolynomial, List.map_map]
  induction p with
  | nil => exact .nil
  | cons term rest ih =>
      apply QuaternionPrefixPolynomialEqv.cons
      · refine ⟨Q'.eqv_refl _, ?_⟩
        intro c hc
        have hx : c/4 < target := by omega
        have hs := s.map_lt (c/4) hx
        have hm := hp term List.mem_cons_self
        change exponentAt
            (reindexQuaternionExponents s (List.replicate (4*a) 0 ++ term.1)) c =
          exponentAt (List.replicate (4*b) 0 ++ reindexQuaternionExponents t term.1) c
        rw [exponentAt_reindexQuaternionExponents s _ hc, exponent_lift, exponent_lift]
        by_cases hlow : b ≤ c/4
        · rw [if_neg (by omega : ¬ c<4*b)]
          by_cases hhigh : c/4 < b+source
          · have hi : c/4-b < source := by omega
            have hti := t.map_lt _ hi
            have hback := hmap (t.map (c/4-b)) hti
            rw [t.involutive _ hi] at hback
            have hin : a+t.map (c/4-b) < target := by omega
            have hpin := congrArg s.map hback
            rw [s.involutive _ hin, show b+(c/4-b)=c/4 by omega] at hpin
            rw [← hpin, if_neg (by omega)]
            have hsmall : c-4*b < 4*source := by omega
            rw [exponentAt_reindexQuaternionExponents t _ hsmall]
            have hd : (c-4*b)/4=c/4-b := by omega
            have hr : (c-4*b)%4=c%4 := by omega
            rw [hd, hr]
            exact congrArg (exponentAt term.1) (by omega)
          · rw [exponent_zero (reindexQuaternionExponents t term.1) (c-4*b)
              (by rw [reindexQuaternionExponents_length]; omega)]
            by_cases hsa : s.map (c/4)<a
            · rw [if_pos (by omega)]
            · rw [if_neg (by omega)]
              have hout : source ≤ s.map (c/4)-a := by
                by_cases hi : s.map (c/4)-a < source
                · have hp' := hmap (s.map (c/4)-a) hi
                  rw [show a+(s.map (c/4)-a)=s.map (c/4) by omega,
                    s.involutive _ hx] at hp'
                  have ht' := t.map_lt _ hi
                  omega
                · omega
              exact exponent_zero term.1 _ (by omega)
        · rw [if_pos (by omega : c<4*b)]
          by_cases hsa : s.map (c/4)<a
          · rw [if_pos (by omega)]
          · rw [if_neg (by omega)]
            have hout : source ≤ s.map (c/4)-a := by
              by_cases hi : s.map (c/4)-a < source
              · have hp' := hmap (s.map (c/4)-a) hi
                rw [show a+(s.map (c/4)-a)=s.map (c/4) by omega,
                  s.involutive _ hx] at hp'
                omega
              · omega
            exact exponent_zero term.1 _ (by omega)
      · exact ih (fun u hu => hp u (List.mem_cons_of_mem term hu))

/-- Reversal places the WHOLE subwindow at L-j-r, including all its
spectator coordinates. The source support is not inferred from its syntax. -/
theorem reversePolynomial_lift (blocks L j r : Nat) (hfit : j+r ≤ L)
    (p : RatPoly) (hp : SupportedQuaternionBlocks ((r+1)*blocks) p) :
    QuaternionPrefixPolynomialEqv ((L+1)*blocks)
      (reversePolynomial blocks L (liftBoundary (j*blocks) p))
      (liftBoundary ((L-j-r)*blocks) (reversePolynomial blocks r p)) := by
  apply reindex_lift_of_map
  · have hh := Nat.mul_le_mul_right blocks (show j+(r+1) ≤ L+1 by omega)
    simpa only [Nat.add_mul] using hh
  · have hh := Nat.mul_le_mul_right blocks (show (L-j-r)+(r+1) ≤ L+1 by omega)
    simpa only [Nat.add_mul] using hh
  · intro i hi
    have hn : 0<blocks := by
      by_cases hz : blocks=0
      · simp only [hz, Nat.mul_zero] at hi
        omega
      · omega
    have hq := quotient_le hi
    have hm := Nat.mod_lt i hn
    have hd : blocks*(i/blocks)+i%blocks=i := Nat.div_add_mod i blocks
    have hinput : j*blocks+i=blocks*(j+i/blocks)+i%blocks := by
      rw [Nat.mul_add, Nat.mul_comm blocks j, Nat.add_assoc, hd]
    rw [hinput, sliceReverse_slice blocks L (j+i/blocks) (i%blocks) (by omega) hm]
    change blocks*(L-(j+i/blocks))+i%blocks =
      (L-j-r)*blocks+(blocks*(r-i/blocks)+i%blocks)
    rw [← Nat.add_assoc, Nat.mul_comm (L-j-r) blocks, ← Nat.mul_add]
    exact congrArg (fun v => blocks*v+i%blocks) (by omega)
  · exact hp

theorem reversePolynomial_zero (blocks : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks blocks p) :
    QuaternionPrefixPolynomialEqv blocks (reversePolynomial blocks 0 p) p := by
  induction p with
  | nil => exact .nil
  | cons t ts ih =>
      apply QuaternionPrefixPolynomialEqv.cons
      · refine ⟨Q'.eqv_refl _, ?_⟩
        intro c hc
        change exponentAt (reindexQuaternionExponents (sliceReverse blocks 0) t.1) c = _
        rw [exponentAt_reindexQuaternionExponents _ _ (by simpa using hc)]
        have hq : c/4<blocks := by omega
        change exponentAt t.1 (4*(blocks*(0-(c/4)/blocks)+(c/4)%blocks)+c%4) = _
        rw [Nat.zero_sub, Nat.mul_zero, Nat.zero_add, Nat.mod_eq_of_lt hq]
        exact congrArg (exponentAt t.1) (by omega)
      · exact ih (fun u hu => hp u (List.mem_cons_of_mem t hu))

end YMGap.Continuum.SU2QuaternionSliceReversal

#print axioms YMGap.Continuum.SU2QuaternionSliceReversal.sliceReverse
#print axioms YMGap.Continuum.SU2QuaternionSliceReversal.sliceReverse_slice
#print axioms YMGap.Continuum.SU2QuaternionSliceReversal.reversePolynomial
#print axioms YMGap.Continuum.SU2QuaternionSliceReversal.reversePolynomial_supported
#print axioms YMGap.Continuum.SU2QuaternionSliceReversal.reversePolynomial_twice
#print axioms YMGap.Continuum.SU2QuaternionSliceReversal.reindex_lift_of_map
#print axioms YMGap.Continuum.SU2QuaternionSliceReversal.reversePolynomial_lift
#print axioms YMGap.Continuum.SU2QuaternionSliceReversal.reversePolynomial_zero
