/-
# Multi-plaquette activity bound `h(∏ f_p)² ≤ ∏ B_p²`

(YM Group Realizer, R1 activity, part 2.)  For a polymer `X` (list of
plaquettes, each with a spin expansion `f_p = Σ c_s χ_s(plaq_p)`, links may be
shared) and `B_p = Σ |c_s|(s+1)`:

* `bnd_charSum`   : `H((f_p G)²) ≤ B_p² H(G²)` for every supported `G`
  (induction on terms; cross terms by the scaled Cauchy–Schwarz
  `2bβ H(XY) ≤ β²H(X²) + b²H(Y²)`; needs `c_s ≠ 0` i.e. `0 < |c_s|`).
* `bnd_polyProd`  : `H((F G)²) ≤ (∏B_p)² H(G²)`, `F = ∏ f_p` (no independence).
* `polymer_activity_sq_le` : `h(F)² ≤ h(F²) ≤ (∏ B_p)²` under `multiLinkHaar`.
-/

import YMGap.Continuum.SU2PlaqWeightedCharacterBound

namespace YMGap.Continuum.SU2PolymerActivityBound

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2QuaternionGlobalFaceRatPolySupport
open YMGap.Continuum.SU2CharacterSquareIdentity
open YMGap.Continuum.SU2CharacterHaarBound
open YMGap.Continuum.SU2CharacterCauchySchwarz (haar_pull haar_cs_pos)
open YMGap.Continuum.SU2PlaqWeightedCharacterBound
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2TorusMultiLinkPolyGibbs

local infix:50 " ≅ " => RatPolyCoeffEqv
local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

/-! ## Q' helpers -/

theorem abs_mul_abs (q : Q') : Q'.abs q * Q'.abs q ≈ q * q := by
  unfold Q'.abs
  split
  · exact Q'.eqv_refl _
  · exact Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv _ _)
      (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (Q'.mul_neg_eqv _ _)) (Q'.neg_neg_eqv _))

theorem sq_nonneg' (q : Q') : (0 : Q') ≤ q * q :=
  Q'.le_trans' _ _ _ (Q'.mul_nonneg _ _ (Q'.abs_nonneg q) (Q'.abs_nonneg q))
    (Q'.le_of_eqv (abs_mul_abs q))

theorem two_mul_q (z : Q') : Q'.ofInt 2 * z ≈ z + z := by
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast, Q'.mul_den_cast]
  show (2 * z.num) * ((z.den : Int) * (z.den : Int)) = (z.num * z.den + z.num * z.den) * ((0 + 1 : Nat) * (z.den : Int))
  simp only [Nat.zero_add, Int.natCast_one, Int.one_mul, Int.add_mul, Int.two_mul, Int.mul_assoc]

theorem pos_of_pos_le {a b : Q'} (ha : (0 : Q') < a) (hab : a ≤ b) : (0 : Q') < b := by
  have hn : 0 < a.num := Q'.num_pos_of_pos ha
  have e : a.num * (b.den : Int) ≤ b.num * (a.den : Int) := hab
  have hbd : (0 : Int) < (b.den : Int) := by exact_mod_cast b.den_pos
  have had : (0 : Int) < (a.den : Int) := by exact_mod_cast a.den_pos
  have h1 : (0 : Int) * (a.den : Int) < b.num * (a.den : Int) := by
    rw [Int.zero_mul]; exact Int.lt_of_lt_of_le (Int.mul_pos hn hbd) e
  have h2 : (0 : Int) < b.num := Int.lt_of_mul_lt_mul_right h1 (Int.le_of_lt had)
  show (0 : Int) * (b.den : Int) < b.num * (1 : Int)
  rw [Int.zero_mul, Int.mul_one]; exact h2

theorem add_neg_cancel_q (p q : Q') : (p + q) + -q ≈ p :=
  Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _)
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl p) (Q'.add_neg_self_eqv q))
      (QPoly.q_add_zero_eqv p))

/-! ## `Bnd` calculus -/

theorem bnd_congr {n : Nat} {f f' : RatPoly} {B B' : Q'} (h : Bnd n f B) (hf : f ≅ f') (hB : B ≈ B') :
    Bnd n f' B' := by
  intro G hG
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (haar_coeff (RatPolyCoeffEqv.mul
    (RatPolyCoeffEqv.mul hf.symm (RatPolyCoeffEqv.refl G))
    (RatPolyCoeffEqv.mul hf.symm (RatPolyCoeffEqv.refl G))) n)) ?_
  exact Q'.le_trans' _ _ _ (h G hG) (Q'.le_of_eqv
    (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hB)
      (Q'.mul_eqv_congr_left _ _ _ hB))))

theorem haar_smul (n : Nat) (q : Q') (P : RatPoly) : H n (polySmul q P) ≈ q * H n P :=
  YMGap.Continuum.BF4CompactActionCPOrder.quaternionHaar_polySmul n q P

theorem smul_prod (q r : Q') (X Y : RatPoly) :
    polyMul (polySmul q X) (polySmul r Y) ≅ polySmul (q * r) (polyMul X Y) :=
  (RatPolyCoeffEqv.polyMul_smul_left q X _).trans
    ((RatPolyCoeffEqv.smul q (RatPolyCoeffEqv.polyMul_smul_right r X Y)).trans
      (RatPolyCoeffEqv.smul_assoc q r _))

theorem bnd_smul {n : Nat} {f : RatPoly} {B : Q'} (h : Bnd n f B) (q : Q') :
    Bnd n (polySmul q f) (Q'.abs q * B) := by
  intro G hG
  have e : H n (polyMul (polyMul (polySmul q f) G) (polyMul (polySmul q f) G)) ≈
      (q * q) * H n (polyMul (polyMul f G) (polyMul f G)) :=
    Q'.eqv_trans _ _ _ (haar_coeff ((RatPolyCoeffEqv.mul (RatPolyCoeffEqv.polyMul_smul_left q f G)
      (RatPolyCoeffEqv.polyMul_smul_left q f G)).trans (smul_prod q q _ _)) n) (haar_smul n _ _)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv e) ?_
  refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ (h G hG) (sq_nonneg' q)) ?_
  refine Q'.le_of_eqv ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (abs_mul_abs q))) ?_
  q_ring

/-- Polynomial `0` is `0`-bounded. -/
theorem bnd_zero (n : Nat) : Bnd n polyZero 0 := fun G _ =>
  Q'.le_of_eqv (Q'.eqv_symm (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (by decide))
    (Q'.zero_mul_eqv _)))

private def env3 (f f' G : RatPoly) : Nat → RatPoly := ev [f, f', G]

/-- **Sum rule** (`0 < b`, `0 < β`). -/
theorem bnd_add {n : Nat} {f f' : RatPoly} {b β : Q'} (hf : Bnd n f b) (hf' : Bnd n f' β)
    (hb : (0 : Q') < b) (hβ : (0 : Q') < β)
    (sf : SupportedCoordinates (4 * n) f) (sf' : SupportedCoordinates (4 * n) f') :
    Bnd n (polyAdd f f') (b + β) := by
  intro G hG
  let X := polyMul f G
  let Y := polyMul f' G
  have sX : SupportedCoordinates (4 * n) X := supportedCoordinates_polyMul sf hG
  have sY : SupportedCoordinates (4 * n) Y := supportedCoordinates_polyMul sf' hG
  let g := H n (polyMul G G)
  have hX := hf G hG
  have hY := hf' G hG
  -- expansion
  have hexp : H n (polyMul (polyMul (polyAdd f f') G) (polyMul (polyAdd f f') G)) ≈
      (H n (polyMul X X) + H n (polyMul Y Y)) + (H n (polyMul X Y) + H n (polyMul X Y)) :=
    Q'.eqv_trans _ _ _
      (haar_coeff (norm (env := env3 f f' G)
        (.mul (.mul (.add (v 0) (v 1)) (v 2)) (.mul (.add (v 0) (v 1)) (v 2)))
        (.add (.add (.mul (.mul (v 0) (v 2)) (.mul (v 0) (v 2))) (.mul (.mul (v 1) (v 2)) (.mul (v 1) (v 2))))
          (.mul (c 2) (.mul (.mul (v 0) (v 2)) (.mul (v 1) (v 2))))) (by decide)) n)
      (Q'.eqv_trans _ _ _ (haar_add n _ _)
        (Q'.add_eqv_congr' (haar_add n _ _)
          (Q'.eqv_trans _ _ _ (haar_pull n _ _) (two_mul_q _))))
  -- scaled Cauchy–Schwarz
  have hcs := haar_cs_pos (n := n) 1 (polySmul β X) (polySmul b Y)
    (supportedCoordinates_polySmul _ sX) (supportedCoordinates_polySmul _ sY)
  have e1 : H n (polyMul (polySmul β X) (polySmul b Y)) ≈ (β * b) * H n (polyMul X Y) :=
    Q'.eqv_trans _ _ _ (haar_coeff (smul_prod _ _ _ _) n) (haar_smul n _ _)
  have e2 : H n (polyMul (polySmul β X) (polySmul β X)) ≈ (β * β) * H n (polyMul X X) :=
    Q'.eqv_trans _ _ _ (haar_coeff (smul_prod _ _ _ _) n) (haar_smul n _ _)
  have e3 : H n (polyMul (polySmul b Y) (polySmul b Y)) ≈ (b * b) * H n (polyMul Y Y) :=
    Q'.eqv_trans _ _ _ (haar_coeff (smul_prod _ _ _ _) n) (haar_smul n _ _)
  have hβb : (0 : Q') < β * b := Q'.mul_pos hβ hb
  have hcross : (β * b) * (H n (polyMul X Y) + H n (polyMul X Y)) ≤
      (β * b) * ((β * b) * g + (β * b) * g) := by
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) (Q'.le_trans' _ _ _ hcs ?_)
    · refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm (Q'.eqv_trans _ _ _
        (two_mul_q _) (Q'.add_eqv_congr' (Q'.one_mul_eqv _) (Q'.one_mul_eqv _))))
      refine Q'.eqv_trans _ _ _ ?_ (Q'.add_eqv_congr' (Q'.eqv_symm e1) (Q'.eqv_symm e1))
      exact Q'.mul_add_eqv _ _ _
    · refine Q'.le_trans' _ _ _ (Q'.add_le_add
        (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) e2)))
        (Q'.le_of_eqv e3)) ?_
      refine Q'.le_trans' _ _ _ (Q'.add_le_add
        (Q'.mul_le_mul_of_nonneg_left _ _ _ hX (sq_nonneg' β))
        (Q'.mul_le_mul_of_nonneg_left _ _ _ hY (sq_nonneg' b))) ?_
      exact Q'.le_of_eqv (by q_ring)
  have hc2 := Q'.le_of_mul_le_mul_left hcross hβb
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hexp) ?_
  refine Q'.le_trans' _ _ _ (Q'.add_le_add (Q'.add_le_add hX hY) hc2) ?_
  exact Q'.le_of_eqv (by q_ring)

/-- **Product rule** (no independence; shared links allowed). -/
theorem bnd_mul {n : Nat} {f F : RatPoly} {B B' : Q'} (hf : Bnd n f B) (hF : Bnd n F B')
    (sF : SupportedCoordinates (4 * n) F) : Bnd n (polyMul f F) (B * B') := by
  intro G hG
  have e : polyMul (polyMul (polyMul f F) G) (polyMul (polyMul f F) G) ≅
      polyMul (polyMul f (polyMul F G)) (polyMul f (polyMul F G)) :=
    RatPolyCoeffEqv.mul (RatPolyCoeffEqv.mul_assoc _ _ _) (RatPolyCoeffEqv.mul_assoc _ _ _)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (haar_coeff e n)) ?_
  refine Q'.le_trans' _ _ _ (hf _ (supportedCoordinates_polyMul sF hG)) ?_
  refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ (hF G hG) (sq_nonneg' B)) ?_
  exact Q'.le_of_eqv (by q_ring)

theorem bnd_one (n : Nat) : Bnd n polyOne 1 := fun G _ =>
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (haar_coeff (RatPolyCoeffEqv.mul (RatPolyCoeffEqv.one_mul G)
    (RatPolyCoeffEqv.one_mul G)) n)) (Q'.le_of_eqv (Q'.eqv_symm (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (by decide)) (Q'.one_mul_eqv _))))

/-! ## Spin expansions and polymers -/

section
variable (links : List Z4Link) (N : Nat)

/-- `f_p = Σ c_s χ_s(plaq_p)` over a list of `(c_s, s)`. -/
def charSum (p : Z4Plaq) : List (Q' × Nat) → RatPoly
  | [] => polyZero
  | t :: ts => polyAdd (polySmul t.1 (plaqCharacter links N p t.2)) (charSum p ts)

/-- `B_p = Σ |c_s| (s+1)`. -/
def bSum : List (Q' × Nat) → Q'
  | [] => 0
  | t :: ts => Q'.abs t.1 * Q'.ofInt ((t.2 : Int) + 1) + bSum ts

/-- Polymer product `F = ∏_p f_p`. -/
def polyProd : List (Z4Plaq × List (Q' × Nat)) → RatPoly
  | [] => polyOne
  | q :: rest => polyMul (charSum links N q.1 q.2) (polyProd rest)

/-- `∏_p B_p`. -/
def bProd : List (Z4Plaq × List (Q' × Nat)) → Q'
  | [] => 1
  | q :: rest => bSum q.2 * bProd rest

end

variable {links : List Z4Link} {N : Nat}

private theorem ofInt_succ_pos (s : Nat) : (0 : Q') < Q'.ofInt ((s : Int) + 1) := by
  show (0 : Int) * ((0 + 1 : Nat) : Int) < ((s : Int) + 1) * ((0 + 1 : Nat) : Int)
  omega

theorem bSum_nonneg : ∀ cs : List (Q' × Nat), (0 : Q') ≤ bSum cs
  | [] => Q'.le_of_eqv (Q'.eqv_refl _)
  | t :: ts => Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ (Q'.abs_nonneg _)
      (Q'.le_of_lt (ofInt_succ_pos t.2))) (bSum_nonneg ts)

theorem supp_charSum {p : Z4Plaq} (hc : YMGap.Continuum.SU2PlaqWordHolonomy.LinksCover links N p) :
    ∀ cs, SupportedCoordinates (4 * links.length) (charSum links N p cs)
  | [] => supportedCoordinates_polyZero _
  | t :: ts => supportedCoordinates_polyAdd (supportedCoordinates_polySmul _
      (supported_U _ _ (YMGap.Continuum.SU2PlaqRadius.plaqWord_supp links N p hc).1 t.2))
      (supp_charSum hc ts)

private theorem term_bnd {p : Z4Plaq} (hc : YMGap.Continuum.SU2PlaqWordHolonomy.LinksCover links N p)
    (t : Q' × Nat) :
    Bnd links.length (polySmul t.1 (plaqCharacter links N p t.2))
      (Q'.abs t.1 * Q'.ofInt ((t.2 : Int) + 1)) :=
  bnd_smul (plaq_weighted_le links N p hc t.2) t.1

/-- **Spin-expansion bound** `H((f_p G)²) ≤ B_p² H(G²)` (all `c_s ≠ 0`). -/
theorem bnd_charSum {p : Z4Plaq} (hc : YMGap.Continuum.SU2PlaqWordHolonomy.LinksCover links N p) :
    ∀ cs : List (Q' × Nat), (∀ t ∈ cs, (0 : Q') < Q'.abs t.1) →
      Bnd links.length (charSum links N p cs) (bSum cs)
  | [], _ => bnd_zero _
  | [t], _ => bnd_congr (term_bnd hc t) (RatPolyCoeffEqv.add_zero _).symm
      (Q'.eqv_symm (QPoly.q_add_zero_eqv _))
  | t :: u :: us, hpos =>
      bnd_add (term_bnd hc t) (bnd_charSum hc (u :: us) (fun w hw => hpos w (List.mem_cons_of_mem t hw)))
        (Q'.mul_pos (hpos t List.mem_cons_self) (ofInt_succ_pos t.2))
        (pos_of_pos_le (Q'.mul_pos (hpos u (List.mem_cons_of_mem t List.mem_cons_self))
            (ofInt_succ_pos u.2))
          (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (QPoly.q_add_zero_eqv _)))
            (Q'.add_le_add_left _ _ _ (bSum_nonneg us))))
        (supportedCoordinates_polySmul _
          (supported_U _ _ (YMGap.Continuum.SU2PlaqRadius.plaqWord_supp links N p hc).1 t.2))
        (supp_charSum hc (u :: us))

/-- Polymer hypotheses: every plaquette covered, every coefficient nonzero. -/
def PolymerOK (links : List Z4Link) (N : Nat) (X : List (Z4Plaq × List (Q' × Nat))) : Prop :=
  ∀ q ∈ X, YMGap.Continuum.SU2PlaqWordHolonomy.LinksCover links N q.1 ∧ ∀ t ∈ q.2, (0 : Q') < Q'.abs t.1

theorem supp_polyProd : ∀ X, PolymerOK links N X →
    SupportedCoordinates (4 * links.length) (polyProd links N X)
  | [], _ => supportedCoordinates_polyOne _
  | q :: rest, h => supportedCoordinates_polyMul (supp_charSum (h q List.mem_cons_self).1 q.2)
      (supp_polyProd rest (fun r hr => h r (List.mem_cons_of_mem q hr)))

/-- **Polymer bound** `H((F G)²) ≤ (∏B_p)² H(G²)`. -/
theorem bnd_polyProd : ∀ X, PolymerOK links N X → Bnd links.length (polyProd links N X) (bProd X)
  | [], _ => bnd_one _
  | q :: rest, h =>
      bnd_mul (bnd_charSum (h q List.mem_cons_self).1 q.2 (h q List.mem_cons_self).2)
        (bnd_polyProd rest (fun r hr => h r (List.mem_cons_of_mem q hr)))
        (supp_polyProd rest (fun r hr => h r (List.mem_cons_of_mem q hr)))

/-- **Activity bound**: `h(F²) ≤ (∏B_p)²` and `h(F)² ≤ (∏B_p)²` under `multiLinkHaar`. -/
theorem polymer_activity_sq_le (X : List (Z4Plaq × List (Q' × Nat))) (hX : PolymerOK links N X) :
    let h := (multiLinkHaar links.length).h
    let F := polyProd links N X
    h (polyMul F F) ≤ bProd X * bProd X ∧ h F * h F ≤ bProd X * bProd X := by
  intro h F
  have hone : H links.length polyOne ≈ 1 := quaternionHaar_polyOne _
  have hsq : H links.length (polyMul F F) ≤ bProd X * bProd X := by
    have := bnd_polyProd X hX polyOne (supportedCoordinates_polyOne _)
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (haar_coeff (RatPolyCoeffEqv.mul
      (RatPolyCoeffEqv.mul_one F) (RatPolyCoeffEqv.mul_one F)).symm _)) (Q'.le_trans' _ _ _ this ?_)
    exact Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_trans _ _ _ (haar_coeff (RatPolyCoeffEqv.one_mul polyOne) _) hone)) (Q'.mul_one_eqv _))
  refine ⟨hsq, ?_⟩
  -- h(F)² ≤ h(F²): Cauchy–Schwarz against the constant `h(F)·1`
  let a := H links.length F
  have sF := supp_polyProd X hX
  have hcs := haar_cs_pos (n := links.length) 1 F (polySmul a polyOne) sF
    (supportedCoordinates_polySmul _ (supportedCoordinates_polyOne _))
  have e1 : H links.length (polyMul F (polySmul a polyOne)) ≈ a * a :=
    Q'.eqv_trans _ _ _ (haar_coeff ((RatPolyCoeffEqv.polyMul_smul_right a F polyOne).trans
      (RatPolyCoeffEqv.smul a (RatPolyCoeffEqv.mul_one F))) _) (haar_smul _ _ _)
  have e2 : H links.length (polyMul (polySmul a polyOne) (polySmul a polyOne)) ≈ a * a :=
    Q'.eqv_trans _ _ _ (haar_coeff ((smul_prod a a _ _).trans
      (RatPolyCoeffEqv.smul _ (RatPolyCoeffEqv.one_mul polyOne))) _)
      (Q'.eqv_trans _ _ _ (haar_smul _ _ _)
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hone) (Q'.mul_one_eqv _)))
  -- 2 a² ≤ h(F²) + a²
  have h2 : (a * a) + (a * a) ≤ H links.length (polyMul F F) + a * a :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (Q'.eqv_trans _ _ _ (two_mul_q _)
      (Q'.add_eqv_congr' (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) e1)
        (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) e1)))))
      (Q'.le_trans' _ _ _ hcs (Q'.le_of_eqv (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) (Q'.one_mul_eqv _)) e2)))
  have h3 : a * a ≤ H links.length (polyMul F F) := by
    have h4 := Q'.add_le_add_right _ _ (-(a * a)) h2
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) (Q'.le_trans' _ _ _ h4 (Q'.le_of_eqv ?_))
    · exact Q'.eqv_symm (add_neg_cancel_q _ _)
    · exact add_neg_cancel_q _ _
  exact Q'.le_trans' _ _ _ h3 hsq

end YMGap.Continuum.SU2PolymerActivityBound

#print axioms YMGap.Continuum.SU2PolymerActivityBound.bnd_add
#print axioms YMGap.Continuum.SU2PolymerActivityBound.bnd_charSum
#print axioms YMGap.Continuum.SU2PolymerActivityBound.bnd_polyProd
#print axioms YMGap.Continuum.SU2PolymerActivityBound.polymer_activity_sq_le
