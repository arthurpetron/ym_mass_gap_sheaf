import numpy as np, json
def _parse(path):
    raw=open(path,'rb').read(); nl=raw.index(b'\n'); h=json.loads(raw[:nl]); body=raw[nl+1:]
    Lt=h['Lt']; ns=len(h['sides']); nl_=len(h['tflow'])+len(h.get('linear_steps',[])); npoly=h.get('poly',0)
    per=1+ns*3*Lt; reclen=1+nl_*per+nl_*npoly
    a=np.frombuffer(body[:len(body)//(8*reclen)*8*reclen],dtype='<f8').reshape(-1,reclen)
    return h,a,Lt,ns,nl_,per,npoly
def load(path):
    """returns h, plaq[N], Es[N,nlev], O[N,nlev,nside,3,Lt]; nlev = flow levels then linear-smearing levels (P7+)."""
    h,a,Lt,ns,nl_,per,npoly=_parse(path)
    plaq=a[:,0]; Es=np.empty((len(a),nl_)); O=np.empty((len(a),nl_,ns,3,Lt))
    for k in range(nl_):
        off=1+k*per; Es[:,k]=a[:,off]; O[:,k]=a[:,off+1:off+per].reshape(-1,ns,3,Lt)
    return h,plaq,Es,O
def load_poly(path):
    """P7+: spatial Polyakov loops on the smoothed links, shape [N,nlev,6] = (P_x,P_y,P_z, P_x^2,P_y^2,P_z^2) line means."""
    h,a,Lt,ns,nl_,per,npoly=_parse(path)
    if not npoly: return None
    return a[:,1+nl_*per:].reshape(len(a),nl_,npoly)
