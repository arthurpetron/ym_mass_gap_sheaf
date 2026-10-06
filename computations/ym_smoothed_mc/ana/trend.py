import numpy as np
s=np.array([2,3,4,6.]); 
data={'eps*s rho=1':([1.420,1.819,2.085,2.401],[.012,.021,.028,.036]),
      'eps*s rho=0.7':([1.536,2.047,2.420,2.926],[.011,.021,.030,.034]),
      'eps*s rho=0.5':([1.612,2.212,2.665,3.326],[.011,.021,.031,.033]),
      'eps_shift*s rho=1':([1.17,1.50,1.59,2.07],[.10,.24,.26,.33]),
      'eps_half*s rho=1':([1.263,1.598,1.58,1.97],[.037,.048,.10,.11]),
      'eps*(1.5sqrt(t0)/a) rho=1':([0.7100*2.034,0.6062*2.816,0.5212*3.861,0.4002*6.176],[.0059*2.034,.0070*2.816,.0070*3.861,.0060*6.176])}
def wls(X,y,e):
    W=1/e**2; A=X.T@(X*W[:,None]); b=X.T@(W*y); p=np.linalg.solve(A,b); cov=np.linalg.inv(A)
    chi=((y-X@p)**2*W).sum(); return p,np.sqrt(np.diag(cov)),chi
for k,(y,e) in data.items():
    y=np.array(y); e=np.array(e); out=[k]
    for nm,X,msk in [('A-B/s all',np.c_[np.ones(4),1/s],slice(None)),('A-B/s s>=3',np.c_[np.ones(3),1/s[1:]],slice(1,None)),
                     ('A-B/s+C/s^2 all',np.c_[np.ones(4),1/s,1/s**2],slice(None)),('a+b ln s all',np.c_[np.ones(4),np.log(s)],slice(None))]:
        p,pe,chi=wls(X,y[msk],e[msk]); dof=len(y[msk])-X.shape[1]
        out.append(f"{nm}: A={p[0]:.2f}({pe[0]:.2f}) chi2/dof={chi:.1f}/{dof}" if 'ln' not in nm else f"{nm}: b={p[1]:.2f}({pe[1]:.2f}) chi2/dof={chi:.1f}/{dof}")
    print(' | '.join(out))
