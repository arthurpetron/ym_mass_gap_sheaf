/-
# A reversible two-anchor code for four paired spatial projections

The code returns one of three pairings, two literal anchor faces, and two
times relative to an explicit base. Its decoder recovers the original
ordered list. Time lower bounds are essential because Nat subtraction
alone does not retain an arbitrary time. No counting or weight is assumed.
-/

import YMGap.Continuum.Z4FourFaceClosedPairing
import YMGap.Continuum.Z4SpatialPlaquetteProjection

namespace YMGap.Continuum.Z4FourProjectedFaceCode

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4SpatialPlaquetteProjection

local instance : DecidableEq Z4Plaq := inferInstanceAs (DecidableEq (Z4Vertex × Z4Plane))

abbrev Code := Nat × Z4Plaq × Z4Plaq × Nat × Nat

def encode (base : Nat) (a b c d : Z4Plaq) : Code :=
  if faceAt 0 a=faceAt 0 b then (0,a,c,b.1.2.2.2-base,d.1.2.2.2-base)
  else if faceAt 0 a=faceAt 0 c then (1,a,b,c.1.2.2.2-base,d.1.2.2.2-base)
  else (2,a,b,d.1.2.2.2-base,c.1.2.2.2-base)

def decode (base : Nat) (code : Code) : List Z4Plaq :=
  let (tag,a,b,s,t) := code
  if tag=0 then [a,faceAt (s+base) a,b,faceAt (t+base) b]
  else if tag=1 then [a,b,faceAt (s+base) a,faceAt (t+base) b]
  else [a,b,faceAt (t+base) b,faceAt (s+base) a]

theorem retime_recovers (base : Nat) (a b : Z4Plaq)
    (hp : faceAt 0 a=faceAt 0 b) (ht : base ≤ b.1.2.2.2) :
    faceAt (b.1.2.2.2-base+base) a=b := by
  apply projection_and_time_injective
  · exact hp
  · change b.1.2.2.2-base+base=b.1.2.2.2
    omega

theorem decode_encode (base : Nat) (a b c d : Z4Plaq)
    (hp : (faceAt 0 a=faceAt 0 b ∧ faceAt 0 c=faceAt 0 d) ∨
      (faceAt 0 a=faceAt 0 c ∧ faceAt 0 b=faceAt 0 d) ∨
      (faceAt 0 a=faceAt 0 d ∧ faceAt 0 b=faceAt 0 c))
    (hb : base ≤ b.1.2.2.2) (hc : base ≤ c.1.2.2.2) (hd : base ≤ d.1.2.2.2) :
    decode base (encode base a b c d)=[a,b,c,d] := by
  by_cases hab : faceAt 0 a=faceAt 0 b
  · have hcd : faceAt 0 c=faceAt 0 d := by
      rcases hp with h | h | h
      · exact h.2
      · exact h.1.symm.trans (hab.trans h.2)
      · exact h.2.symm.trans (hab.symm.trans h.1)
    rw [encode,if_pos hab]
    change [a,faceAt (b.1.2.2.2-base+base) a,c,faceAt (d.1.2.2.2-base+base) c]=[a,b,c,d]
    rw [retime_recovers base a b hab hb,retime_recovers base c d hcd hd]
  · by_cases hac : faceAt 0 a=faceAt 0 c
    · have hbd : faceAt 0 b=faceAt 0 d := by
        rcases hp with h | h | h
        · exact False.elim (hab h.1)
        · exact h.2
        · exact h.2.trans (hac.symm.trans h.1)
      rw [encode,if_neg hab,if_pos hac]
      change [a,b,faceAt (c.1.2.2.2-base+base) a,faceAt (d.1.2.2.2-base+base) b]=[a,b,c,d]
      rw [retime_recovers base a c hac hc,retime_recovers base b d hbd hd]
    · have hp' : faceAt 0 a=faceAt 0 d ∧ faceAt 0 b=faceAt 0 c := by
        rcases hp with h | h | h
        · exact False.elim (hab h.1)
        · exact False.elim (hac h.1)
        · exact h
      rw [encode,if_neg hab,if_neg hac]
      change [a,b,faceAt (c.1.2.2.2-base+base) b,faceAt (d.1.2.2.2-base+base) a]=[a,b,c,d]
      rw [retime_recovers base b c hp'.2 hc,retime_recovers base a d hp'.1 hd]

theorem encode_recover (base : Nat) (a b c d a' b' c' d' : Z4Plaq)
    (hl : decode base (encode base a b c d)=[a,b,c,d])
    (hr : decode base (encode base a' b' c' d')=[a',b',c',d'])
    (he : encode base a b c d=encode base a' b' c' d') : [a,b,c,d]=[a',b',c',d'] :=
  hl.symm.trans ((congrArg (decode base) he).trans hr)

end YMGap.Continuum.Z4FourProjectedFaceCode

#print axioms YMGap.Continuum.Z4FourProjectedFaceCode.encode
#print axioms YMGap.Continuum.Z4FourProjectedFaceCode.decode
#print axioms YMGap.Continuum.Z4FourProjectedFaceCode.retime_recovers
#print axioms YMGap.Continuum.Z4FourProjectedFaceCode.decode_encode
#print axioms YMGap.Continuum.Z4FourProjectedFaceCode.encode_recover
