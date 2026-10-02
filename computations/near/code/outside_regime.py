"""Attempt/verify complete outside-buffer first-zero regime. NOT all-modulus L.
All source ids and inherited subdivisions are accounted for. Verification regenerates inputs.
"""
from first_outside_blocks import *
from certificate_io import load_outside,validate_outside_records
from endgame import specs,with_height,split_new,parse_params,positivity_proof,reduced_spec
from concurrent.futures import ProcessPoolExecutor,as_completed
import time,traceback,hashlib

MENU=[dict(method='mixture',gg='1.7504',gz='1.09006',mix='.1385',zeta='3'),dict(method='mixture',gg='1.6',gz='1.08',mix='.18',zeta='3'),dict(method='single',gg='1.6',gz='1.18',mix='0',zeta='3')]

def follow(sp,node,L):
 if 'split'in node:
  aa,bb=split_new(sp,node['split'],node['mid'])
  return dict(split=node['split'],mid=node['mid'],children=[follow(aa,node['children'][0],L),follow(bb,node['children'][1],L)])
 if 'positivity'in node or 'second_exclusion'in node:return node
 record=node['record'];par=record['parameters'] if 'input_sha256'in record else parameters_of(record['input'])
 if par['method']=='pair':par['method']='single'
 last=None
 for par0 in [par]+MENU:
  try:
   inp=first_out_input(sp,L,'outside_buffer',par0,200);cc=first_cert(inp,minwidth=4);rep=first_verify(inp,cc)
   return dict(buffered_first=dict(input=inp,certificate=cc),maximum=rep['maximum'])
  except RuntimeError as e:last=e
 raise RuntimeError(('outside-buffer unresolved',sp,repr(last)))

def task(arg):
 line,L,dest=arg;old=json.loads(line);i=old['id'];sp=specs()[i];t=time.time()
 if sp['case']['kind']=='rr':assert 'outside'not in old;return dict(id=i,skip=True,ok=True)
 fn=Path(dest)/f'{i:04d}.json.gz'
 if fn.exists():return dict(id=i,ok=True,cached=True)
 try:
  tree=follow(with_height(sp,'outside'),old['outside'],L);rt=dict(id=i,L=L,outside_buffer=tree)
  with gzip.open(fn,'wt')as f:json.dump(rt,f,separators=(',',':'))
  return dict(id=i,ok=True,seconds=time.time()-t)
 except Exception as e:
  out=dict(id=i,ok=False,error=repr(e),seconds=time.time()-t)
  (Path(dest)/f'{i:04d}.failure.json').write_text(json.dumps(out,indent=2));return out

def verify_tree(sp,node,L):
 if 'split'in node:
  assert set(node)=={'split','mid','children'}and len(node['children'])==2
  aa,bb=split_new(sp,node['split'],node['mid']);return verify_tree(aa,node['children'][0],L)+verify_tree(bb,node['children'][1],L)
 if 'positivity'in node:
  assert positivity_proof(sp,Q(node['positivity']['g']))==node['positivity'];return []
 if 'second_exclusion'in node:
  red,proof=reduced_spec(sp);assert red is None and proof==node['second_exclusion'];return []
 assert set(node)=={'buffered_first','maximum'}
 rec=node['buffered_first'];old=rec['input'];par=parameters_of(old);assert par['method']in('single','mixture')
 inp=first_out_input(sp,L,'outside_buffer',par,old['lambda_den']);check_input(inp,old)
 rep=first_verify(inp,rec['certificate']);assert rep['maximum']==node['maximum'];rep['input']=input_summary(inp);return [rep]

def verify_job(arg):
 rt,L=arg;i=rt['id'];sp=specs()[i]
 assert sp['case']['kind']!='rr'
 assert rt['id']==i and rt['L']==L and set(rt)=={'id','L','outside_buffer'}
 reps=verify_tree(with_height(sp,'outside'),rt['outside_buffer'],L)
 best=max(reps,key=lambda r:r['maximum'])if reps else None
 return dict(id=i,maximum=best['maximum']if best else-1,leaves=len(reps),branches=sum(r['branches']for r in reps),checks=sum(r['checks']for r in reps),excluded=sum(r['excluded']for r in reps),binding=best)

if __name__=='__main__':
 import argparse
 ap=argparse.ArgumentParser();ap.add_argument('--L',default='4.30');ap.add_argument('--workers',type=int,default=3);ap.add_argument('--verify',action='store_true');ap.add_argument('--limit',type=int,default=0);a=ap.parse_args();start=time.time();dest=PROJECT/'results'/f'outside_regime_{a.L}';dest.mkdir(exist_ok=True) if not a.verify else None
 if not a.verify:
  source=ROOT/'results/certificate_4.33.jsonl.gz'
  with gzip.open(source,'rt')as f:lines=list(f)
  jobs=[(l,a.L,str(dest))for l in lines if specs()[json.loads(l)['id']]['case']['kind']!='rr']
  if a.limit:jobs=jobs[:a.limit]
  ans=[];bad=[]
  with ProcessPoolExecutor(max_workers=a.workers)as pool:
   futures={pool.submit(task,j):j for j in jobs}
   for k,fu in enumerate(as_completed(futures)):
    r=fu.result();ans.append(r)
    if not r['ok']:bad.append(r)
    if k%50==0 or not r['ok']:print('BUILD',k,'id',r['id'],'failed',len(bad),'sec',time.time()-start,r.get('error','')[:150],flush=True)
  out=dict(L=a.L,status='SEARCH, not verified',attempted=len(jobs),failures=bad,complete_requested_cover=(not a.limit),all_pass=not bad,seconds=time.time()-start)
 else:
  ids=[i for i,sp in enumerate(specs())if sp['case']['kind']!='rr'];ans=[]
  records=load_outside(a.L);assert validate_outside_records(records,a.L)==ids
  with ProcessPoolExecutor(max_workers=a.workers)as pool:
   for k,r in enumerate(pool.map(verify_job,[(r,a.L)for r in records])):
    ans.append(r)
    if k%50==0:print('VERIFIED',k,r['id'],max(t['maximum']for t in ans)/S,'sec',time.time()-start,flush=True)
  best=max(ans,key=lambda r:r['maximum']);out=dict(L=a.L,status='PASS entire FINITE outside-buffer first-zero regime; NOT an all-case exponent',source_records=len(ids),regenerated_inputs=True,maximum_numerator=best['maximum'],scale=S,margin_numerator=S-best['maximum'],binding=best,seconds=time.time()-start)
  for k in ('leaves','branches','checks','excluded'):out[k]=sum(r[k]for r in ans)
 (PROJECT/'results'/f'outside_regime_{a.L}_{"verified"if a.verify else"build"}.json').write_text(json.dumps(out,indent=2));print('DONE',time.time()-start,flush=True)
