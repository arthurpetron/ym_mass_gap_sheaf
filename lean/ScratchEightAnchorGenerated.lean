import YMGap.Continuum.SevenAnchorWindowRetune

namespace ScratchEightAnchorGenerated

set_option maxHeartbeats 30000000
set_option maxRecDepth 200000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CircleFourierPowerModel
open YMGap.Continuum.ThreeAnchorWindowRetune

def chooseFast (n : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => chooseFast n k * (n - k) / (k + 1)

def qsum : List Q' → Q'
  | [] => 0
  | x :: xs => x + qsum xs

def generatedBernCoeff (cap : Q') (p : Poly) (degree i : Nat) : Q' :=
  qsum ((List.range (i + 1)).map (fun j =>
    Q'.ofNat (chooseFast (degree - j) (i - j)) *
      ((p.getD j 0) * qpow cap j)))

def generatedBernTerms (cap : Q') (p : Poly) (degree : Nat) :
    List (Nat × Q') :=
  (List.range (degree + 1)).map
    (fun i => (i, generatedBernCoeff cap p degree i))

def cap : Q' := Q'.mkPos 21 22 (by decide)
def nineEighths : Q' := Q'.mkPos 9 8 (by decide)

def headP : Poly :=
  psub (pmul retuneP (prefixDP 7)) (prefixAP 8)
def short1P : Poly := psub (pmul retuneP (prefixDP 1)) (prefixAP 1)
def short2P : Poly := psub (pmul retuneP (prefixDP 2)) (prefixAP 2)
def short3P : Poly := psub (pmul retuneP (prefixDP 3)) (prefixAP 3)
def short4P : Poly := psub (pmul retuneP (prefixDP 4)) (prefixAP 4)
def short5P : Poly := psub (pmul retuneP (prefixDP 5)) (prefixAP 5)
def short6P : Poly := psub (pmul retuneP (prefixDP 6)) (prefixAP 6)
def ratioP : Poly := psub retuneP (monoP nineEighths 17)

example : allZero (psub (scaleVar cap headP)
    (bernTermsP 143 (generatedBernTerms cap headP 143))) := by decide

example : ∀ t ∈ generatedBernTerms cap headP 143,
    (0 : Q') ≤ t.2 := by decide

example : allZero (psub (scaleVar cap short1P)
    (bernTermsP 10 (generatedBernTerms cap short1P 10))) := by decide
example : ∀ t ∈ generatedBernTerms cap short1P 10,
    (0 : Q') ≤ t.2 := by decide

example : allZero (psub (scaleVar cap short2P)
    (bernTermsP 20 (generatedBernTerms cap short2P 20))) := by decide
example : ∀ t ∈ generatedBernTerms cap short2P 20,
    (0 : Q') ≤ t.2 := by decide

example : allZero (psub (scaleVar cap short3P)
    (bernTermsP 35 (generatedBernTerms cap short3P 35))) := by decide
example : ∀ t ∈ generatedBernTerms cap short3P 35,
    (0 : Q') ≤ t.2 := by decide

example : allZero (psub (scaleVar cap short4P)
    (bernTermsP 54 (generatedBernTerms cap short4P 54))) := by decide
example : ∀ t ∈ generatedBernTerms cap short4P 54,
    (0 : Q') ≤ t.2 := by decide

example : allZero (psub (scaleVar cap short5P)
    (bernTermsP 74 (generatedBernTerms cap short5P 74))) := by decide
example : ∀ t ∈ generatedBernTerms cap short5P 74,
    (0 : Q') ≤ t.2 := by decide

example : allZero (psub (scaleVar cap short6P)
    (bernTermsP 99 (generatedBernTerms cap short6P 99))) := by decide
example : ∀ t ∈ generatedBernTerms cap short6P 99,
    (0 : Q') ≤ t.2 := by decide

example : allZero (psub (scaleVar cap ratioP)
    (bernTermsP 17 (generatedBernTerms cap ratioP 17))) := by decide
example : ∀ t ∈ generatedBernTerms cap ratioP 17,
    (0 : Q') ≤ t.2 := by decide

end ScratchEightAnchorGenerated
