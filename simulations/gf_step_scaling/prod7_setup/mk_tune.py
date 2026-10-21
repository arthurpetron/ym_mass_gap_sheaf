F='--twist 1 --therm 300 --sep 10 --nor 4 --eps 0.1 --alt-eps 0 --start cold --ckpt-every 50 --c 0.3,0.4'
pts=[(8,b) for b in (2.92,2.98,2.70,2.80)]+[(12,b) for b in (3.07,3.13,2.85,2.95)]+[(16,b) for b in (3.18,3.24,2.96,3.06,4.66,4.74,4.00,4.08,3.70,3.77,3.40,3.48)]
s=97000
with open('jobs7_tune.txt','w') as f:
    for L,b in sorted(pts,key=lambda x:-x[0]):
        s+=1; n=200 if L==16 else 300
        f.write(f'tune_L{L}_b{b:.2f}_tw|su2gf --L {L} --beta {b:.2f} {F} --nmeas {n} --seed {s}\n')
