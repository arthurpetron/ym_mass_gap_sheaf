/-
Track B / R2 — a CONCRETE RATIONAL INHABITANT of `AFTrajectoryCertificate`, and
the resulting UNCONDITIONAL non-vacuity of the O(4)-restoration bridge.

# What this module delivers

`AFTrajectoryCertificate` (see `AFTrajectoryCertificate.lean`) packages the named
two-loop asymptotic-freedom running as a `Type`-level record; the total bridge
`rubricO4Restoration_of_AFCertificate` fires the open O(4)-restoration Clay clause
from ANY inhabitant of that record.  This module exhibits one such inhabitant
built from a fully decidable, one-loop **reciprocal trajectory**

      τ_k := 1/(k+2),      β := 1,   E := 1,   k0 := 0,   A' := 1,

whose every certificate field reduces to `Q'` order facts — none needs a physics
oracle.  The load-bearing field is the cubic recurrence.  For the one-loop
reciprocal `τ_k = 1/x` (`x = k+2`) the discretization defect is exactly

      τ_{k+1} − (τ_k − τ_k²)  =  1 / (x²(x+1))  >  0,

which is `≤ E·τ_k³ = 1/x³` iff `x ≤ x+1` — true uniformly.  We prove this defect
identity (as an exact `Q'` equivalence, via `defect·x²(x+1) ≃ 1`) and close the
`|·| ≤ E·τ³` bound by reciprocal antitonicity `1/(x²(x+1)) ≤ 1/x³`.

# Honest scope (load-bearing, not cosmetic)

Because the bridge is a TOTAL function and a decidable rational model inhabits the
certificate, `RubricO4Restoration` is inhabited UNCONDITIONALLY here — the
O(4)-rubric clause, as currently wired, carries no analytic content beyond "some
reciprocal AF trajectory exists".  The genuine physics is NOT in firing the
bridge; it is entirely in whether the TRUE lattice SU(N) rotation-breaking
coupling satisfies the certificate fields (its `recurrence` remainder constant).
This module isolates that: the ONLY certificate input not decidable from literals
for the parametric reciprocal model `τ_k = 1/(β(k+B))`, `E = β²`, is the sign
`β > 0` (the one-loop coefficient `b₀ > 0`); a genuine `b₁τ³` two-loop term folds
into `E` without touching the sign structure, since the `E·τ³` budget already
absorbs the `O(1/x³)` discretization remainder.  This is a SHARP reduction, not a
closure of the physical O(4) restoration.

# Axiom-gate (AGENTS.md Rules 1, 8)

Pure `Q'` order/`eqv` arithmetic (the positivity-guarded `divPos` and its quotient
characterizations, `Q'.abs_le`, reused order/`eqv` lemmas) plus `decide` on closed
rational facts.  Every load-bearing declaration is gated with `#print axioms`;
permitted output is `propext` / `Quot.sound` only.  No `Classical.*`, no
`native_decide`, no `sorry`.  All witnesses are `Type`-level data.
-/

import YMGap.Continuum.AFTrajectoryCertificate
import YMGap.Continuum.O4H4Homomorphism

namespace YMGap.Continuum.AFCertificateModel

open YMGap.Constructive
open YMGap.Constructive.Q'
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.AFReciprocalRate
open YMGap.Continuum.AFTrajectoryCertificate

/-! ## 0. Reciprocal-arithmetic helpers (pure `Q'`, axiom-clean)

Four elementary reciprocal facts:
  * `prodMul_eqv_one` — from `a·x ≃ 1` and `b·y ≃ 1`, `(a·b)·(x·y) ≃ 1`;
  * `eqv_recip` — the reciprocal is characterized by its defining product;
  * `recipAnti` — reciprocal antitonicity `D ≤ D' → 1/D' ≤ 1/D`;
  * `negNonpos` — `-x ≤ 0` for `0 ≤ x`. -/

/-- From `a·x ≃ 1` and `b·y ≃ 1`, the cross product `(a·b)·(x·y) ≃ 1`.  Pure
associative–commutative rearrangement to `(a·x)·(b·y) ≃ 1·1 ≃ 1`. -/
theorem prodMul_eqv_one {a b x y : Q'} (h1 : (a * x).eqv 1) (h2 : (b * y).eqv 1) :
    ((a * b) * (x * y)).eqv 1 := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv a b (x * y)) ?_
  have hbxy : (b * (x * y)).eqv (x * (b * y)) := by
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv b x y)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right (b * x) (x * b) y (Q'.mul_comm_eqv b x)) ?_
    exact Q'.mul_assoc_eqv x b y
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left a _ _ hbxy) ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv a x (b * y))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right (a * x) 1 (b * y) h1) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left 1 (b * y) 1 h2) ?_
  exact Q'.one_mul_eqv 1

/-- The reciprocal is characterized by its defining product: if `v·D ≃ 1` then
`v ≃ 1/D`.  (Both `≤` directions from the quotient characterizations, then
antisymmetry.) -/
theorem eqv_recip {v D : Q'} (hD : (0 : Q') < D) (h : (v * D).eqv 1) :
    v.eqv (Q'.divPos 1 D hD) := by
  -- `.eqv` and `≤` on `Q'` are the `Int` cross-products; antisymmetry closes it.
  have h1 : v ≤ Q'.divPos 1 D hD := Q'.le_divPos_of_mul_le 1 D hD (Q'.le_of_eqv h)
  have h2 : Q'.divPos 1 D hD ≤ v := Q'.divPos_le_of_le_mul 1 D hD (Q'.ge_of_eqv h)
  exact Int.le_antisymm h1 h2

/-- **Reciprocal antitonicity.**  `D ≤ D'` (both positive) gives `1/D' ≤ 1/D`.
By `divPos_le_of_le_mul` it suffices that `1 ≤ (1/D)·D'`, which follows from
`(1/D)·D ≃ 1` and `D ≤ D'`. -/
theorem recipAnti {D D' : Q'} (hD : (0 : Q') < D) (hD' : (0 : Q') < D')
    (hle : D ≤ D') : Q'.divPos 1 D' hD' ≤ Q'.divPos 1 D hD := by
  refine Q'.divPos_le_of_le_mul 1 D' hD' ?_
  have hpos : (0 : Q') ≤ Q'.divPos 1 D hD := Q'.le_of_lt (Q'.divPos_pos 1 D hD (by decide))
  have hmul : Q'.divPos 1 D hD * D ≤ Q'.divPos 1 D hD * D' :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hle hpos
  have h1 : (Q'.divPos 1 D hD * D).eqv 1 := Q'.divPos_mul_eqv 1 D hD
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv h1) hmul

/-- `-x ≤ 0` for `0 ≤ x` (cross-product form). -/
theorem negNonpos {x : Q'} (h : (0 : Q') ≤ x) : -x ≤ (0 : Q') := by
  show (-x).num * ((0 : Q').den : Int) ≤ (0 : Q').num * ((-x).den : Int)
  have hh : (0 : Q').num * (x.den : Int) ≤ x.num * ((0 : Q').den : Int) := h
  have h0n : (0 : Q').num = 0 := rfl
  have h0d : ((0 : Q').den : Int) = 1 := rfl
  have hxn : (-x).num = -x.num := rfl
  have hxd : ((-x).den : Int) = (x.den : Int) := rfl
  rw [h0n, h0d] at hh
  rw [h0n, h0d, hxn, hxd]
  omega

/-! ## 1. The load-bearing cubic recurrence bound (abstract reciprocal)

For ANY reciprocal `a = 1/x`, `b = 1/xp1` with `xp1 ≃ x+1`, the one-loop defect
`b − (a − a²)` equals `1/(x·(x·xp1))` and is bounded by `a·(a·a) = 1/(x·(x·x))`,
because the cube denominator `x·(x·x)` is `≤ x·(x·xp1)`.  The absolute value is
handled by nonnegativity of the defect. -/

/-- **The cubic recurrence bound.**  With `a := 1/x`, `b := 1/xp1` (`xp1 ≃ x+1`),

      | b − (a − 1·a²) |  ≤  1·(a·a²).

Proof: the defect `b − (a − a²)` is `≃ 1/(x·(x·xp1))` (via `defect·(x·(x·xp1)) ≃ 1`),
which is `≥ 0` and `≤ a·a² ≃ 1/(x·(x·x))` by reciprocal antitonicity
(`x·(x·x) ≤ x·(x·xp1)`). -/
theorem recurrence_bound (a b x xp1 : Q')
    (hx : (0 : Q') < x) (hxp1 : (0 : Q') < xp1) (ha_pos : (0 : Q') < a)
    (ha : (a * x).eqv 1) (hb : (b * xp1).eqv 1) (hxrel : xp1.eqv (x + 1)) :
    Q'.abs (b - (a - 1 * (a * a))) ≤ 1 * (a * (a * a)) := by
  -- Denominators.
  have hDbig : (0 : Q') < x * (x * xp1) := Q'.mul_pos hx (Q'.mul_pos hx hxp1)
  have hDcube : (0 : Q') < x * (x * x) := Q'.mul_pos hx (Q'.mul_pos hx hx)
  have ha_nn : (0 : Q') ≤ a := Q'.le_of_lt ha_pos
  -- (a·a²)·(x·x²) ≃ 1, hence a·a² ≃ 1/(x·x²).
  have cubeMul : ((a * (a * a)) * (x * (x * x))).eqv 1 :=
    prodMul_eqv_one ha (prodMul_eqv_one ha ha)
  have hQcube : (a * (a * a)).eqv (Q'.divPos 1 (x * (x * x)) hDcube) :=
    eqv_recip hDcube cubeMul
  -- x ≤ xp1, so x·x² ≤ x·(x·xp1).
  have hx_le : x ≤ xp1 := by
    have h1 : x + 0 ≤ x + 1 := Q'.add_le_add_left x 0 1 (by decide)
    have h2 : x + 0 = x := Q'.add_zero' x
    rw [h2] at h1
    exact Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv (Q'.eqv_symm hxrel))
  have hxx_le : x * x ≤ x * xp1 :=
    Q'.mul_le_mul_of_nonneg_left x xp1 x hx_le (Q'.le_of_lt hx)
  have hDc_le : x * (x * x) ≤ x * (x * xp1) :=
    Q'.mul_le_mul_of_nonneg_left (x * x) (x * xp1) x hxx_le (Q'.le_of_lt hx)
  have hPle : Q'.divPos 1 (x * (x * xp1)) hDbig ≤ Q'.divPos 1 (x * (x * x)) hDcube :=
    recipAnti hDcube hDbig hDc_le
  have hPQ : Q'.divPos 1 (x * (x * xp1)) hDbig ≤ a * (a * a) :=
    Q'.le_trans' _ _ _ hPle (Q'.ge_of_eqv hQcube)
  -- The exact defect identity: defect ≃ 1/(x·(x·xp1)).
  -- First simplify the subtraction structure: defect ≃ b + (-a + a²).
  have hdef_S : (b - (a - 1 * (a * a))).eqv (b + (-a + (a * a))) := by
    show (b + -(a + -(1 * (a * a)))).eqv (b + (-a + (a * a)))
    refine Q'.add_eqv_congr_left b _ _ ?_
    refine Q'.eqv_trans _ _ _ (Q'.neg_add_eqv a (-(1 * (a * a)))) ?_
    refine Q'.add_eqv_congr_left (-a) _ _ ?_
    exact Q'.eqv_trans _ _ _ (Q'.neg_neg_eqv (1 * (a * a))) (Q'.one_mul_eqv (a * a))
  -- The three summand collapses over the big denominator D = x·(x·xp1).
  have T1 : (b * (x * (x * xp1))).eqv (x * x) := by
    have hxr : (x * (x * xp1)).eqv (xp1 * (x * x)) := by
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv x x xp1)) ?_
      exact Q'.mul_comm_eqv (x * x) xp1
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left b _ _ hxr) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv b xp1 (x * x))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right (b * xp1) 1 (x * x) hb) ?_
    exact Q'.one_mul_eqv (x * x)
  have T2 : ((-a) * (x * (x * xp1))).eqv (-(x * xp1)) := by
    refine Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv a (x * (x * xp1))) ?_
    refine Q'.neg_eqv_congr _ _ ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv a x (x * xp1))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right (a * x) 1 (x * xp1) ha) ?_
    exact Q'.one_mul_eqv (x * xp1)
  have T3 : ((a * a) * (x * (x * xp1))).eqv xp1 := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (a * a) _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv x x xp1))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv (a * a) (x * x) xp1)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right ((a * a) * (x * x)) 1 xp1 (prodMul_eqv_one ha ha)) ?_
    exact Q'.one_mul_eqv xp1
  -- Polynomial closure: x·x + (−(x·xp1) + xp1) ≃ 1.
  have step_poly : ((x * x) + ((-(x * xp1)) + xp1)).eqv 1 := by
    have hxxp1 : (x * xp1).eqv (x * x + x) := by
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left x xp1 (x + 1) hxrel) ?_
      refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv x x 1) ?_
      exact Q'.add_eqv_congr_left (x * x) (x * 1) x (Q'.mul_one_eqv x)
    have hnegxx : (-(x * xp1)).eqv (-(x * x) + -x) := by
      refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr (x * xp1) (x * x + x) hxxp1) ?_
      exact Q'.neg_add_eqv (x * x) x
    have hinner : ((-(x * xp1)) + xp1).eqv ((-(x * x) + -x) + (x + 1)) := by
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right (-(x * xp1)) (-(x * x) + -x) xp1 hnegxx) ?_
      exact Q'.add_eqv_congr_left (-(x * x) + -x) xp1 (x + 1) hxrel
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left (x * x) _ _ hinner) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv (x * x) (-(x * x) + -x) (x + 1))) ?_
    have hcancel1 : ((x * x) + (-(x * x) + -x)).eqv (-x) := by
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.add_assoc_eqv (x * x) (-(x * x)) (-x))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right ((x * x) + -(x * x)) 0 (-x) (Q'.add_neg_self_eqv (x * x))) ?_
      exact Q'.eqv_of_eq (Q'.zero_add' (-x))
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right ((x * x) + (-(x * x) + -x)) (-x) (x + 1) hcancel1) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv (-x) x 1)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right ((-x) + x) 0 1 (Q'.neg_add_self_eqv x)) ?_
    exact Q'.eqv_of_eq (Q'.zero_add' 1)
  -- Assemble S·D ≃ 1.
  have hSbig : ((b + (-a + (a * a))) * (x * (x * xp1))).eqv 1 := by
    refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv b (-a + (a * a)) (x * (x * xp1))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (b * (x * (x * xp1))) _ _
        (Q'.add_mul_eqv (-a) (a * a) (x * (x * xp1)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right (b * (x * (x * xp1))) (x * x)
        ((-a) * (x * (x * xp1)) + (a * a) * (x * (x * xp1))) T1) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (x * x)
        ((-a) * (x * (x * xp1)) + (a * a) * (x * (x * xp1)))
        ((-(x * xp1)) + xp1)
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_right ((-a) * (x * (x * xp1))) (-(x * xp1))
            ((a * a) * (x * (x * xp1))) T2)
          (Q'.add_eqv_congr_left (-(x * xp1)) ((a * a) * (x * (x * xp1))) xp1 T3))) ?_
    exact step_poly
  -- defect·D ≃ 1, hence defect ≃ 1/D.
  have hdefbig : ((b - (a - 1 * (a * a))) * (x * (x * xp1))).eqv 1 := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (b - (a - 1 * (a * a))) (b + (-a + (a * a)))
        (x * (x * xp1)) hdef_S) ?_
    exact hSbig
  have hdefP : (b - (a - 1 * (a * a))).eqv (Q'.divPos 1 (x * (x * xp1)) hDbig) :=
    eqv_recip hDbig hdefbig
  -- Nonnegativity of the defect (it is a positive quotient).
  have hdef_nn : (0 : Q') ≤ (b - (a - 1 * (a * a))) :=
    Q'.le_trans' _ _ _
      (Q'.le_of_lt (Q'.divPos_pos 1 (x * (x * xp1)) hDbig (by decide)))
      (Q'.ge_of_eqv hdefP)
  -- Right-hand side nonnegativity.
  have hRHS_nn : (0 : Q') ≤ 1 * (a * (a * a)) :=
    Q'.mul_nonneg 1 (a * (a * a)) (by decide)
      (Q'.mul_nonneg a (a * a) ha_nn (Q'.mul_nonneg a a ha_nn ha_nn))
  -- Upper bound:  defect ≃ 1/D ≤ a·a² ≃ 1·(a·a²).
  have hle_final : (b - (a - 1 * (a * a))) ≤ 1 * (a * (a * a)) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hdefP)
      (Q'.le_trans' _ _ _ hPQ (Q'.ge_of_eqv (Q'.one_mul_eqv (a * (a * a)))))
  -- Lower bound:  −RHS ≤ 0 ≤ defect.
  have hge_final : -(1 * (a * (a * a))) ≤ (b - (a - 1 * (a * a))) :=
    Q'.le_trans' _ _ _ (negNonpos hRHS_nn) hdef_nn
  exact Q'.abs_le hge_final hle_final

/-! ## 2. The concrete reciprocal model `τ_k = 1/(k+2)`

Every certificate field for `β = E = 1`, `k0 = 0`, `A' = 1` reduces to `Q'`
order facts.  The offset `B_cert = (2/β)·(1/τ_{k0}) = 4 ≥ 2` closes `τ_lower`. -/

/-- The reciprocal trajectory `τ_k := 1/(k+2)`. -/
def tauModel (k : Nat) : Q' :=
  Q'.divPos 1 (harmDen 2 k) (harmDen_pos (by decide) k)

/-- `2 ≤ harmDen 2 k = (k+2)`, from `harmDen 2 0 ≃ 2` and monotonicity. -/
theorem two_le_harmDen (k : Nat) : (2 : Q') ≤ harmDen 2 k := by
  have h20 : (harmDen 2 0).eqv 2 := by decide
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv h20) (harmDen_mono 2 (Nat.zero_le k))

/-- **The concrete AF trajectory certificate** `τ_k = 1/(k+2)`, fully rational and
axiom-clean.  Non-vacuity witness: an inhabitant of `AFTrajectoryCertificate`. -/
def O4Model : AFTrajectoryCertificate where
  τ := tauModel
  β := 1
  E := 1
  k0 := 0
  β_pos := by decide
  E_nonneg := by decide
  τ_pos := fun k => Q'.divPos_pos 1 (harmDen 2 k) (harmDen_pos (by decide) k) (by decide)
  τ_small := fun k _ => by
    -- 1·τ_k ≤ halfBeta 1:  τ_k = 1/(k+2) ≤ 1/2 = halfBeta 1.
    have hle : tauModel k ≤ Q'.divPos 1 (2 : Q') (by decide) :=
      recipAnti (by decide) (harmDen_pos (by decide) k) (two_le_harmDen k)
    have hd2half : (Q'.divPos 1 (2 : Q') (by decide)).eqv (halfBeta 1) := by decide
    have hτhalf : tauModel k ≤ halfBeta 1 :=
      Q'.le_trans' _ _ _ hle (Q'.le_of_eqv hd2half)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv (tauModel k))) hτhalf
  τ_lt_one := fun k _ => by
    -- τ_k = 1/(k+2) ≤ 1/2 < 1.
    have hle : tauModel k ≤ Q'.divPos 1 (2 : Q') (by decide) :=
      recipAnti (by decide) (harmDen_pos (by decide) k) (two_le_harmDen k)
    have hlt : Q'.divPos 1 (2 : Q') (by decide) < (1 : Q') := by decide
    exact Q'.lt_of_le_of_lt hle hlt
  recurrence := fun k _ => by
    -- The load-bearing cubic bound, at a = τ_k, b = τ_{k+1}, x = k+2, xp1 = k+3.
    have hxrel : (harmDen 2 (k + 1)).eqv (harmDen 2 k + 1) := by
      show (Q'.ofNat (k + 1) + 2).eqv ((Q'.ofNat k + 2) + 1)
      have hofnat : (Q'.ofNat (k + 1)).eqv (Q'.ofNat k + 1) :=
        Q'.eqv_trans _ _ _ (ofNat_add_eqv k 1)
          (Q'.add_eqv_congr_left (Q'.ofNat k) (Q'.ofNat 1) 1 (by decide))
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right (Q'.ofNat (k + 1)) (Q'.ofNat k + 1) 2 hofnat) ?_
      refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (Q'.ofNat k) 1 2) ?_
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left (Q'.ofNat k) (1 + 2) (2 + 1) (Q'.add_comm_eqv 1 2)) ?_
      exact Q'.eqv_symm (Q'.add_assoc_eqv (Q'.ofNat k) 2 1)
    exact recurrence_bound (tauModel k) (tauModel (k + 1)) (harmDen 2 k) (harmDen 2 (k + 1))
      (harmDen_pos (by decide) k) (harmDen_pos (by decide) (k + 1))
      (Q'.divPos_pos 1 (harmDen 2 k) (harmDen_pos (by decide) k) (by decide))
      (Q'.divPos_mul_eqv 1 (harmDen 2 k) (harmDen_pos (by decide) k))
      (Q'.divPos_mul_eqv 1 (harmDen 2 (k + 1)) (harmDen_pos (by decide) (k + 1)))
      hxrel
  A' := 1
  A'_pos := by decide
  τ_lower := fun d => by
    -- 1/(d + B_cert) ≤ 1/(d+2) = τ_{0+d}, since B_cert = 4 ≥ 2.
    have hBc2 : (2 : Q') ≤
        recip (halfBeta 1) (halfBeta_pos (by decide))
          * recip (tauModel 0) (Q'.divPos_pos 1 (harmDen 2 0) (harmDen_pos (by decide) 0) (by decide)) := by
      decide
    have hle : harmDen 2 (0 + d)
        ≤ harmDen (recip (halfBeta 1) (halfBeta_pos (by decide))
            * recip (tauModel 0) (Q'.divPos_pos 1 (harmDen 2 0) (harmDen_pos (by decide) 0) (by decide))) d := by
      show Q'.ofNat (0 + d) + 2
          ≤ Q'.ofNat d
            + (recip (halfBeta 1) (halfBeta_pos (by decide))
                * recip (tauModel 0) (Q'.divPos_pos 1 (harmDen 2 0) (harmDen_pos (by decide) 0) (by decide)))
      have h0d : 0 + d = d := Nat.zero_add d
      rw [h0d]
      exact Q'.add_le_add_left (Q'.ofNat d) 2 _ hBc2
    exact recipAnti (harmDen_pos (by decide) (0 + d)) _ hle

/-! ## 3. The unconditional firing of the O(4)-restoration Clay clause

The total bridge `rubricO4Restoration_of_AFCertificate` consumes the concrete
certificate to inhabit the open O(4)-restoration clause.  This is UNCONDITIONAL:
no hypothesis, no physics oracle.  It exhibits that the O(4) clause, as wired,
carries no analytic content beyond "some reciprocal AF trajectory exists"; the
genuine physics is the certificate `recurrence` for the TRUE lattice coupling. -/

/-- **The concrete O(4)-restoration witness.**  `RubricO4Restoration` is inhabited
unconditionally by firing the total bridge on the reciprocal model. -/
def o4Restoration_witness : YMGap.Rubric.ClayScorecard.RubricO4Restoration :=
  O4H4Homomorphism.rubricO4Restoration_of_AFCertificate O4Model

end YMGap.Continuum.AFCertificateModel

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.AFCertificateModel.prodMul_eqv_one
#print axioms YMGap.Continuum.AFCertificateModel.eqv_recip
#print axioms YMGap.Continuum.AFCertificateModel.recipAnti
#print axioms YMGap.Continuum.AFCertificateModel.negNonpos
#print axioms YMGap.Continuum.AFCertificateModel.recurrence_bound
#print axioms YMGap.Continuum.AFCertificateModel.two_le_harmDen
#print axioms YMGap.Continuum.AFCertificateModel.O4Model
#print axioms YMGap.Continuum.AFCertificateModel.o4Restoration_witness
