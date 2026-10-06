import numpy as np, sys
import os; sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from analyze import load, jk
def fmt(x,e):
    if not np.isfinite(x) or not np.isfinite(e): return '   nan    '
    if abs(x)<0.01 and abs(x)>0: return f'{x:+.2e}±{e:.1e}'
    return f'{x:+.3f}±{e:.3f}'
def run(path,binsize=50):
    hdr,L,sides,smear,tmax,per,a=load(path)
    nb=len(a)//binsize; b=a[:nb*binsize].reshape(nb,binsize,-1).mean(1); n=3*L**3
    beta=hdr.split('beta=')[1].split()[0]
    rows=[]
    for si,lev in enumerate(smear):
        for li,side in enumerate(sides):
            off=1+(si*len(sides)+li)*per
            for kind in ('loc','zm'):
                def corr(v):
                    m=v[off]; loc=v[off+1:off+per:2]; zm=v[off+2:off+per:2]
                    return (loc-m*m) if kind=='loc' else (zm-n*m*m)
                l=side
                def obs(v):
                    c=corr(v)
                    target=c[2*l]/c[l]            # R(2 side)/R(side)  = R(4u)/R(2u)
                    surv=c[l]/c[0]                # R(side)/R(0)  (log-convex lower bound)
                    jens=(c[1]/c[0])**l           # (R(1)/R(0))^side (Jensen lower bound, needs T>=0)
                    eps=1-c[1]/c[0]               # relative one-step energy
                    if l%2==0:
                        u=l//2; s=sum(c[2*t]-c[2*t+1] for t in range(u,2*u)); kb=1-2*s/c[2*u]
                    else: kb=np.nan
                    return np.array([target,surv,jens,eps,kb])
                val,err=jk(b,obs)
                rows.append((beta,lev,side,kind,val,err))
    return hdr,len(a),rows
if __name__=='__main__':
    allrows=[]
    for p in sys.argv[1:]:
        hdr,nc,rows=run(p); allrows+=rows
        print(hdr.strip(),' nconf',nc)
    print('\nbeta smear side kind | R(2s)/R(s) [target]  | R(s)/R(0) [CS floor] | (R1/R0)^s [Jensen] | eps=1-R1/R0 | window kappa_b (even s)')
    for beta,lev,side,kind,v,e in allrows:
        print(f'{beta:>4} {lev:>4} {side:>3} {kind:>4} | '+' | '.join(fmt(x,y) for x,y in zip(v,e)))
