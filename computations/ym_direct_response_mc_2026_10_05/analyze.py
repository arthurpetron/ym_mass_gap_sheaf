import numpy as np, sys, re, json
def load(path):
    raw=open(path,'rb').read()
    nl=raw.index(b'\n'); hdr=raw[:nl].decode(); body=raw[nl+1:]
    L=int(re.search(r'L=(\d+)',hdr).group(1))
    sides=[int(s) for s in re.search(r'sides=\[([^\]]*)\]',hdr).group(1).split(',')]
    smear=[int(s) for s in re.search(r'smear=\[([^\]]*)\]',hdr).group(1).split(',')]
    tmax=L//2; per=1+2*(tmax+1); reclen=1+len(smear)*len(sides)*per
    a=np.frombuffer(body[:(len(body)//(8*reclen))*8*reclen],dtype='<f8').reshape(-1,reclen)
    return hdr,L,sides,smear,tmax,per,a
def jk(binsmeans, fn):
    nb=len(binsmeans); full=fn(binsmeans.mean(0))
    js=np.array([fn((binsmeans.sum(0)-binsmeans[i])/(nb-1)) for i in range(nb)])
    err=np.sqrt((nb-1)/nb*((js-js.mean(0))**2).sum(0))
    return full,err
def analyze(path, binsize=50, skip=0):
    hdr,L,sides,smear,tmax,per,a=load(path)
    a=a[skip:]
    nb=len(a)//binsize; b=a[:nb*binsize].reshape(nb,binsize,-1).mean(1)
    n=3*L**3
    out={'hdr':hdr,'nconf':len(a),'nbins':nb,'plaq':float(a[:,0].mean()),'res':{}}
    for si,lev in enumerate(smear):
        for li,side in enumerate(sides):
            off=1+(si*len(sides)+li)*per
            def corr(v,kind):
                m=v[off]; loc=v[off+1:off+per:2]; zm=v[off+2:off+per:2]
                return (loc-m*m) if kind=='loc' else (zm-n*m*m)
            for kind in ('loc','zm'):
                C,Ce=jk(b,lambda v:corr(v,kind))
                Cn,Cne=jk(b,lambda v:corr(v,kind)/corr(v,kind)[0])
                def ratio(v):
                    c=corr(v,kind); return np.array([c[2*l]/c[l] for l in range(1,tmax//2+1)])
                R,Re=jk(b,ratio)
                def budget(v):
                    c=corr(v,kind); res=[]
                    for u in range(1,tmax//4+1):
                        s=sum(c[2*t]-c[2*t+1] for t in range(u,2*u))
                        res.append(1-2*s/c[2*u])
                    return np.array(res)
                K,Ke=jk(b,budget)
                def meff(v):
                    c=corr(v,kind); return np.log(np.abs(c[:-1]/c[1:]))
                M,Me=jk(b,meff)
                out['res'][f'{lev}/{side}/{kind}']=dict(C=C.tolist(),Ce=Ce.tolist(),Cn=Cn.tolist(),Cne=Cne.tolist(),
                    ratio=R.tolist(),ratioe=Re.tolist(),budget=K.tolist(),budgete=Ke.tolist(),meff=M.tolist(),meffe=Me.tolist())
    return out
if __name__=='__main__':
    for p in sys.argv[1:]:
        o=analyze(p)
        print(o['hdr'].strip(),'nconf',o['nconf'],'plaq %.5f'%o['plaq'])
        for k,v in o['res'].items():
            lev,side,kind=k.split('/')
            if kind!='loc' and lev!='20': pass
            s=' '.join('%.3f(%.0f)'%(x,1000*e) for x,e in zip(v['ratio'],v['ratioe']))
            kb=' '.join('%.3f(%.0f)'%(x,1000*e) for x,e in zip(v['budget'],v['budgete']))
            print(f'  smear{lev:>2} l={side} {kind:3}  R(2t)/R(t),t=1..4: {s} | kb u=1,2: {kb}')
