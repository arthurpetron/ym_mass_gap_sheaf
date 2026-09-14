/-
# Encoding bounded uniform continuity without a monotone oscillation modulus

A bounded rational value map with a positive monotone epsilon-to-delta
selector is encoded in the existing CtsMod/MonotoneOmegaVanishing types.
At radius d the oscillation bound is a finite minimum of certified bounds
at reciprocal tolerances, with the global bound as fallback. The search
ends at d.den; positivity and d <= 1/(n+1) ensure that n is in this window.

The output selector uses the value-antitone reciprocal level, not the raw
denominator of epsilon. No monotonicity of an input oscillation bound is
assumed. This is rational representation data, not a spectral premise.
-/

import YMGap.Continuum.BernsteinStageData
import YMGap.Constructive.RegularCRealArith
import YMGap.Constructive.SelfSimilarFlow

namespace YMGap.Continuum.UniformSymbolEncoding

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BernsteinUniformConvergence
open YMGap.Continuum.BernsteinStageData

theorem min_mono {a b c d : Q'} (h : a≤c) (k : b≤d) : Q'.min' a b≤Q'.min' c d :=
  (Q'.le_min'_iff _ _ _).mpr
    ⟨Q'.le_trans' _ _ _ (Q'.min_le_left' _ _) h,Q'.le_trans' _ _ _ (Q'.min_le_right' _ _) k⟩

theorem min_pos {a b : Q'} (ha : (0 : Q')<a) (hb : (0 : Q')<b) : (0 : Q')<Q'.min' a b := by
  unfold Q'.min'
  split <;> assumption

theorem runningMin_le_at (f : Nat → Q') (n k : Nat) (h : k≤n) : Q'.runningMin f n≤f k := by
  induction n with
  | zero =>
      have hk : k=0 := by omega
      subst k
      exact Q'.le_refl' _
  | succ n ih =>
      by_cases hk : k≤n
      · exact Q'.le_trans' _ _ _ (Q'.runningMin_succ_le f n) (ih hk)
      · have he : k=n+1 := by omega
        subst k
        exact Q'.runningMin_le f (n+1)

theorem reciprocal_index_le_den (d : Q') (hd : (0 : Q')<d) (n : Nat)
    (h : d≤Q'.invSucc n) : n≤d.den := by
  have hnum : (1 : Int)≤d.num := num_pos_of_pos hd
  have hcross : d.num*(n+1 : Nat)≤(d.den : Int) := by
    change d.num*((Q'.invSucc n).den : Int)≤(Q'.invSucc n).num*(d.den : Int) at h
    simpa only [Q'.invSucc_num,Q'.invSucc_den,Int.one_mul] using h
  have hlower := Int.mul_le_mul_of_nonneg_right hnum (Int.natCast_nonneg (n+1))
  omega

def oscillationTerm (B : Q') (D : Q' → Q') (d : Q') (n : Nat) : Q' :=
  if d≤D (Q'.invSucc n) then Q'.invSucc n else B+B

def oscillation (B : Q') (D : Q' → Q') (d : Q') : Q' :=
  Q'.runningMin (oscillationTerm B D d) d.den

theorem oscillation_nonnegative (B : Q') (hB : (0 : Q')≤B) (D : Q' → Q') (d : Q') :
    (0 : Q')≤oscillation B D d := by
  apply Q'.le_runningMin_of_le
  intro n
  unfold oscillationTerm
  split
  · exact Q'.le_of_lt (Q'.invSucc_pos n)
  · exact Q'.zero_le_add _ _ hB hB

theorem oscillation_bound (f : Q' → Q') (B : Q') (hf : ∀ t,Q'.abs (f t)≤B)
    (D : Q' → Q')
    (hD : ∀ e : Q',(0 : Q')<e → ∀ s t,Q'.abs (s-t)≤D e → Q'.abs (f s-f t)≤e)
    (s t d : Q') (h : Q'.abs (s-t)≤d) : Q'.abs (f s-f t)≤oscillation B D d := by
  apply Q'.le_runningMin_of_le
  intro n
  unfold oscillationTerm
  split
  · rename_i hd
    exact hD _ (Q'.invSucc_pos n) s t (Q'.le_trans' _ _ _ h hd)
  · exact Q'.le_trans' _ _ _ (Q'.abs_add_le' _ _)
      (Q'.add_le_add (hf s) (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_neg' _)) (hf t)))

def selectedDelta (D : Q' → Q') (epsilon : Q') : Q' :=
  if (0 : Q')<epsilon then
    Q'.min' (D (Q'.invSucc (lv epsilon))) (Q'.invSucc (lv epsilon))
  else 0

theorem selectedDelta_pos (D : Q' → Q') (hD : ∀ e : Q',(0 : Q')<e → (0 : Q')<D e)
    (e : Q') (he : (0 : Q')<e) : (0 : Q')<selectedDelta D e := by
  rw [selectedDelta,if_pos he]
  exact min_pos (hD _ (Q'.invSucc_pos _)) (Q'.invSucc_pos _)

theorem selectedDelta_mono (D : Q' → Q')
    (hmono : ∀ a b : Q',a≤b → D a≤D b)
    (hpos : ∀ e : Q',(0 : Q')<e → (0 : Q')<D e)
    (a b : Q') (hab : a≤b) : selectedDelta D a≤selectedDelta D b := by
  by_cases ha : (0 : Q')<a
  · have hb := Q'.pos_of_lt_of_le ha hab
    rw [selectedDelta,if_pos ha,selectedDelta,if_pos hb]
    have hr := ExpNeg.invSucc_le_of_le (lv_antitone ha hab)
    exact min_mono (hmono _ _ hr) hr
  · rw [selectedDelta,if_neg ha]
    by_cases hb : (0 : Q')<b
    · exact Q'.le_of_lt (selectedDelta_pos D hpos b hb)
    · rw [selectedDelta,if_neg hb]; exact Q'.le_refl' _

theorem selectedDelta_small (B : Q') (D : Q' → Q')
    (hpos : ∀ e : Q',(0 : Q')<e → (0 : Q')<D e)
    (e : Q') (he : (0 : Q')<e) : oscillation B D (selectedDelta D e)≤e := by
  have hd := selectedDelta_pos D hpos e he
  have hl : selectedDelta D e≤D (Q'.invSucc (lv e)) := by
    rw [selectedDelta,if_pos he]; exact Q'.min_le_left' _ _
  have hr : selectedDelta D e≤Q'.invSucc (lv e) := by
    rw [selectedDelta,if_pos he]; exact Q'.min_le_right' _ _
  have hk := reciprocal_index_le_den _ hd (lv e) hr
  have h := runningMin_le_at (oscillationTerm B D (selectedDelta D e)) _ _ hk
  rw [oscillationTerm,if_pos hl] at h
  exact Q'.le_trans' _ _ _ h (invSucc_lv_le he)

/-- The value map and global bound are retained literally. -/
def encodedSymbol (f : Q' → Q') (B : Q') (hB : (0 : Q')≤B)
    (hf : ∀ t,Q'.abs (f t)≤B) (D : Q' → Q')
    (hD : ∀ e : Q',(0 : Q')<e → ∀ s t,Q'.abs (s-t)≤D e → Q'.abs (f s-f t)≤e) : CtsMod where
  f := f
  bound := B
  ω := oscillation B D
  f_le := hf
  ω_nn := oscillation_nonnegative B hB D
  mod := oscillation_bound f B hf D hD

def encodedVanishing (f : Q' → Q') (B : Q') (hB : (0 : Q')≤B)
    (hf : ∀ t,Q'.abs (f t)≤B) (D : Q' → Q')
    (hD : ∀ e : Q',(0 : Q')<e → ∀ s t,Q'.abs (s-t)≤D e → Q'.abs (f s-f t)≤e)
    (hmono : ∀ a b : Q',a≤b → D a≤D b)
    (hpos : ∀ e : Q',(0 : Q')<e → (0 : Q')<D e) :
    MonotoneOmegaVanishing (encodedSymbol f B hB hf D hD) where
  delta := selectedDelta D
  mono := selectedDelta_mono D hmono hpos
  pos := selectedDelta_pos D hpos
  small := selectedDelta_small B D hpos

end YMGap.Continuum.UniformSymbolEncoding

#print axioms YMGap.Continuum.UniformSymbolEncoding.min_mono
#print axioms YMGap.Continuum.UniformSymbolEncoding.min_pos
#print axioms YMGap.Continuum.UniformSymbolEncoding.runningMin_le_at
#print axioms YMGap.Continuum.UniformSymbolEncoding.reciprocal_index_le_den
#print axioms YMGap.Continuum.UniformSymbolEncoding.oscillationTerm
#print axioms YMGap.Continuum.UniformSymbolEncoding.oscillation
#print axioms YMGap.Continuum.UniformSymbolEncoding.oscillation_nonnegative
#print axioms YMGap.Continuum.UniformSymbolEncoding.oscillation_bound
#print axioms YMGap.Continuum.UniformSymbolEncoding.selectedDelta
#print axioms YMGap.Continuum.UniformSymbolEncoding.selectedDelta_pos
#print axioms YMGap.Continuum.UniformSymbolEncoding.selectedDelta_mono
#print axioms YMGap.Continuum.UniformSymbolEncoding.selectedDelta_small
#print axioms YMGap.Continuum.UniformSymbolEncoding.encodedSymbol
#print axioms YMGap.Continuum.UniformSymbolEncoding.encodedVanishing
