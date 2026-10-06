from guards import I
import math
print("beta  w      l   x=w^{4l}  k=2x^3-1-x^8  (1-w)*4l [alpha-window<=0.4]  (1-w)*128l [proven<=1]")
for beta in [2.3,2.4,2.5,2.6]:
    w=(I(2,beta)/I(1,beta))**(1/3)
    for l in [1,2,3,4,8]:
        x=w**(4*l); k=2*x**3-1-x**8
        print(f"{beta:4.1f} {w:.4f} {l:2d}  {x:.4f}   {k:+.4f}        {(1-w)*4*l:.3f}                 {(1-w)*128*l:.1f}")
