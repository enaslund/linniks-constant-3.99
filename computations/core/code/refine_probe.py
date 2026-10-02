import os
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
from triple_probe import *
from refinement_cover import compact_spec,with_height,split_specs
from two_test_enclosures import wgt

def spec_from_input(inp):
 return {'case':inp['case'],'ordinary_lower':inp['ordinary_lower'],'second':({k:inp['second'][k] for k in ('lo','hi','n')} if inp.get('second') else None),'gap':inp.get('gap'),'method':'single','height':inp['height']}

def par_from_input(inp):
 e=inp['extension'];return dict(method=e['variant'],gg=e['gG'],gz=e['gZ'],mix=e.get('mix','0'),zeta=e.get('zeta','3'))

def refined_second_input(old,newlo,newhi,L):
    out=copy.deepcopy(old);gG,gZ=Q(old['gamma_gram']),Q(old['gamma']);s=Q(old['shift']);e=old['extension'];sec=copy.deepcopy(old['second']);n2=sec['n'];w=wgt(L)
    sec.update(lo=str(newlo),hi=str(newhi),v=(mixfeature(gG,gZ,s,Q(e['mix']),newhi,n2==1) if e['variant']=='mixture' else feat(gG,gZ,s,newhi,n2==1)),contribution=n2*upper(w.G(newlo,n2==1)))
    oldlo,oldhi=Q(old['second']['lo']),Q(old['second']['hi']);out['far_budget']+=n2*lower(w.w(oldhi))-n2*lower(w.w(newhi));out['second']=sec;out['ordinary_lower']=str(newlo)
    out['rows']=[r for r in old['rows'] if r[1]=='infinity' or Q(r[1])>newlo]
    return input_with_third(out,L)

def job2(args):
 line,L,nsub=args;rec=expand_root(json.loads(line));res=[]
 for ht in ('inside','outside'):
  if ht not in rec:continue
  for path,inp in leaves(rec[ht]):
   if inp['second']:
    lo,hi=Q(inp['second']['lo']),Q(inp['second']['hi']);vv=[]
    for j in range(nsub):
     new=refined_second_input(inp,lo+(hi-lo)*j/nsub,lo+(hi-lo)*(j+1)/nsub,L)
     vv.append(sample(new,21,False))
    w=max(vv);m=j
   else:w=sample(input_with_third(inp,L),31,False)
   res.append(dict(id=rec['id'],height=ht,path=path,value=w,case=inp['case'],gap=inp.get('gap'),second=inp['second'],extension=inp['extension']))
 return res
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--L',default='4.30');ap.add_argument('--sub',type=int,default=4);ap.add_argument('--workers',type=int,default=4);ap.add_argument('--ids',default='428,2421,1301');ap.add_argument('--all',action='store_true');a=ap.parse_args();ids=set(map(int,a.ids.split(',')))
 with gzip.open(ROOT/'results/certificate_4.33.jsonl.gz','rt') as f:lines=[l for i,l in enumerate(f) if a.all or i in ids]
 tt=time.time();out=[]
 with ProcessPoolExecutor(max_workers=a.workers) as pool:
  for j,rr in enumerate(pool.map(job2,[(l,a.L,a.sub) for l in lines])):
   out+=rr
   if j%100==0:print('REFINE',j,len(out),'max',max(x['value'][0] for x in out),'fails',sum(x['value'][0]>=1 for x in out),'sec',time.time()-tt,flush=True)
 p=ROOT/'results'/f'refine_{a.L}_{a.sub}.json';p.write_text(json.dumps(out));print(json.dumps(sorted(out,key=lambda x:x['value'][0],reverse=True)[:20],indent=2))
