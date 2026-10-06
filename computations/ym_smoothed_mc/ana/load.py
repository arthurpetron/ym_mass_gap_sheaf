import numpy as np, json
def load(path):
    raw=open(path,'rb').read(); nl=raw.index(b'\n'); h=json.loads(raw[:nl]); body=raw[nl+1:]
    Lt=h['Lt']; ns=len(h['sides']); nl_=len(h['tflow'])
    per=1+ns*3*Lt; reclen=1+nl_*per
    a=np.frombuffer(body[:len(body)//(8*reclen)*8*reclen],dtype='<f8').reshape(-1,reclen)
    plaq=a[:,0]; Es=np.empty((len(a),nl_)); O=np.empty((len(a),nl_,ns,3,Lt))
    for k in range(nl_):
        off=1+k*per; Es[:,k]=a[:,off]; O[:,k]=a[:,off+1:off+per].reshape(-1,ns,3,Lt)
    return h,plaq,Es,O
