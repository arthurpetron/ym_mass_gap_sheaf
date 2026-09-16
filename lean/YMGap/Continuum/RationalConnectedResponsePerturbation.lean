/-
# Exact activity of an affine insertion in a covariance response

For insertion 1+tR, the partition-cleared covariance response has one
factor t. Its remaining cofactor is affine in t: the old partition times
the third connected moment, plus t times the response to R alone.
In particular the third moment is a linear contribution; vanishing of
the two probe-insertion covariances does not remove it.

This is exact rational algebra with all signs and both endpoint
partitions retained. It supplies no bound on the cofactor.
-/

import YMGap.Continuum.RationalConnectedResponse

namespace YMGap.Continuum.RationalConnectedResponsePerturbation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

/-- The old partition-cubed third connected numerator for R. -/
def third (z a b c ab ac bc abc : Q') : Q' :=
  abc*(z*z) + -(ab*c*z) + -(ac*b*z) + -(bc*a*z) + 2*a*b*c

/-- Explicit signed cofactor, affine in the insertion strength t. -/
def cofactor (z a b c ab ac bc abc t : Q') : Q' :=
  let T := third z a b c ab ac bc abc
  z*T + t*(c*T + -((ac*z + -(a*c))*(bc*z + -(b*c))))

/-- No division or positivity is needed; t may also be zero. -/
theorem affine_response (z a b c ab ac bc abc t : Q') :
    (((ab+t*abc)*(z+t*c) + -((a+t*ac)*(b+t*bc)))*(z*z) +
      -((ab*z + -(a*b))*((z+t*c)*(z+t*c)))) ≈
      t*cofactor z a b c ab ac bc abc t := by
  let Z : PolyExpr := .var 0
  let A : PolyExpr := .var 1
  let B : PolyExpr := .var 2
  let C : PolyExpr := .var 3
  let AB : PolyExpr := .var 4
  let AC : PolyExpr := .var 5
  let BC : PolyExpr := .var 6
  let ABC : PolyExpr := .var 7
  let tau : PolyExpr := .var 8
  let T : PolyExpr :=
    .add (.add (.add (.add (.mul ABC (.mul Z Z))
      (.neg (.mul (.mul AB C) Z))) (.neg (.mul (.mul AC B) Z)))
      (.neg (.mul (.mul BC A) Z))) (.mul (.mul (.mul (.const 2) A) B) C)
  let newZ : PolyExpr := .add Z (.mul tau C)
  let newA : PolyExpr := .add A (.mul tau AC)
  let newB : PolyExpr := .add B (.mul tau BC)
  let newAB : PolyExpr := .add AB (.mul tau ABC)
  exact poly_identity_of_normal_eq
    (.add (.mul (.add (.mul newAB newZ) (.neg (.mul newA newB))) (.mul Z Z))
      (.neg (.mul (.add (.mul AB Z) (.neg (.mul A B))) (.mul newZ newZ))))
    (.mul tau (.add (.mul Z T) (.mul tau (.add (.mul C T)
      (.neg (.mul (.add (.mul AC Z) (.neg (.mul A C)))
        (.add (.mul BC Z) (.neg (.mul B C)))))))))
    (by decide)
    (fun | 0 => z | 1 => a | 2 => b | 3 => c | 4 => ab | 5 => ac | 6 => bc | 7 => abc | _ => t)

end YMGap.Continuum.RationalConnectedResponsePerturbation

#print axioms YMGap.Continuum.RationalConnectedResponsePerturbation.third
#print axioms YMGap.Continuum.RationalConnectedResponsePerturbation.cofactor
#print axioms YMGap.Continuum.RationalConnectedResponsePerturbation.affine_response
