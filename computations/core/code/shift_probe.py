import os
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
from triple_probe import *

def shifted_job(args):
    line,L,ngrid,count=args;rec=expand_root(json.loads(line));out=[]
    for ht in ('inside','outside'):
        if ht not in rec:continue
        for path,inp in leaves(rec[ht]):
            new=input_with_third(inp,L);before=new['first'];new=use_shifted(new,L);val=sample(new,ngrid,count)
            out.append(dict(id=rec['id'],height=ht,path=path,value=val,case=inp['case'],gap=inp.get('gap'),second=inp['second'],extension=inp['extension'],first_saving=(before-new['first'])/S,third_lower=new['third_lower']))
    return out
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--L',default='4.30');ap.add_argument('--workers',type=int,default=4);ap.add_argument('--grid',type=int,default=31);ap.add_argument('--count',action='store_true');ap.add_argument('--ids',default='');a=ap.parse_args();ids=set(map(int,a.ids.split(','))) if a.ids else None
 with gzip.open(ROOT/'results/certificate_4.33.jsonl.gz','rt') as f:lines=[l for i,l in enumerate(f) if ids is None or i in ids]
 tt=time.time();out=[];fn=ROOT/'results'/f'shift_{a.L}.jsonl'
 with fn.open('w') as f,ProcessPoolExecutor(max_workers=a.workers) as pool:
  for j,rr in enumerate(pool.map(shifted_job,[(l,a.L,a.grid,a.count) for l in lines],chunksize=1)):
   out+=rr
   for r in rr:f.write(json.dumps(r)+'\n')
   if j%100==0:print('SHIFT',j,'n',len(out),'max',max(r['value'][0] for r in out),'fails',sum(r['value'][0]>=1 for r in out),'sec',time.time()-tt,flush=True)
 sm=dict(L=a.L,leaves=len(out),fails=int(sum(r['value'][0]>=1 for r in out)),max=max(out,key=lambda r:r['value'][0]),seconds=time.time()-tt)
 fn.with_suffix('.summary.json').write_text(json.dumps(sm,indent=2));print(json.dumps(sm,indent=2))
