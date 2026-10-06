import numpy as np, sys, json
def load(path):
    raw=open(path,'rb').read(); nl=raw.index(b'\n'); h=json.loads(raw[:nl]); body=raw[nl+1:]
    return h, body
for d in sys.argv[1:]:
    h,body=load(d+'/data.bin'); x=np.frombuffer(body,dtype='<f8')
    nb=20; b=x[:len(x)//nb*nb].reshape(nb,-1).mean(1)
    print(d, h['beta'], h['Ls'], h['Lt'], 'N',len(x),'plaq %.5f +- %.5f'%(x.mean(), b.std(ddof=1)/np.sqrt(nb)))
