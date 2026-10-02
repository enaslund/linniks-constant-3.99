"""Complete local cover: refine the LOCAL second interval and HIDDEN global interval.
The ordinary first-zero cell is fixed, so this cannot establish a global Linnik exponent.
"""
from separated_blocks import *
from concurrent.futures import ProcessPoolExecutor
import time,traceback
PAR=dict(method='mixture',gg='1.7504',gz='1.09006',mix='.1385',zeta='3')

def base_for(j,parts):
 b=load_data('selected_inputs.json')['2063'][0][1]
 lo,hi=Q('1.14'),Q('1.54');a=lo+(hi-lo)*j/parts;c=lo+(hi-lo)*(j+1)/parts
 b['ordinary_lower']=str(a);b['second']=dict(b['second'],lo=str(a),hi=str(c))
 return b

def tree_build(base,L,br,depth=0):
 inp=make_block_input(base,L,br,PAR,400)
 try:
  cert=cert_block(inp,target=Q('.9985'),width=4)
  rep=verify_block(inp,cert)
  return dict(branch=br,record=dict(input=inp,certificate=cert),maximum=rep['maximum'])
 except RuntimeError as err:
  if br['hi']=='infinity' or depth>=10 or Q(br['hi'])-Q(br['lo'])<=Q('.0025'):raise
  mid=(Q(br['lo'])+Q(br['hi']))/2
  left=dict(br,hi=str(mid));right=dict(br,lo=str(mid))
  aa=tree_build(base,L,left,depth+1);bb=tree_build(base,L,right,depth+1)
  return dict(branch=br,split=str(mid),children=[aa,bb],maximum=max(aa['maximum'],bb['maximum']))

def roots_for(base):
 lo=max(Q(base['case']['source_l2']),Q(base['case']['lo']));hi=Q(base['ordinary_lower']);ans=[]
 if lo<hi:
  for n,ident in [(1,'distinct'),(2,'distinct'),(2,'same_reserved')]:ans.append(dict(lo=str(lo),hi=str(hi),ng=n,real=n==1,identity=ident))
 ans.append(dict(lo=str(max(lo,hi)),hi='infinity',ng=0,real=False,identity='unhidden'))
 return ans

def job(arg):
 j,parts,L=arg;b=base_for(j,parts);fn=PROJECT/'results'/f'local_split_{L}_{parts}_{j}.json.gz';start=time.time()
 try:
  trees=[]
  for k,br in enumerate(roots_for(b)):
   tr=tree_build(b,L,br);trees.append(tr);print('ROOT',j,k,tr['maximum']/S,'sec',time.time()-start,flush=True)
  result=dict(part=j,parts=parts,L=L,base=b,trees=trees,maximum=max(t['maximum']for t in trees))
  with gzip.open(fn,'wt')as f:json.dump(result,f,separators=(',',':'))
  return dict(part=j,ok=True,maximum=result['maximum'],seconds=time.time()-start)
 except Exception as e:
  r=dict(part=j,ok=False,error=repr(e),trace=traceback.format_exc(),seconds=time.time()-start)
  (PROJECT/'results'/f'local_split_{L}_{parts}_{j}.failure.json').write_text(json.dumps(r,indent=2));return r

def verify_tree(base,L,br,tree):
 assert tree['branch']==br
 if 'split'in tree:
  mid=Q(tree['split']);assert Q(br['lo'])<mid<Q(br['hi']);assert len(tree['children'])==2
  a=verify_tree(base,L,dict(br,hi=str(mid)),tree['children'][0]);b=verify_tree(base,L,dict(br,lo=str(mid)),tree['children'][1]);return a+b
 assert 'record'in tree
 inp=make_block_input(base,L,br,PAR,400);check_input(inp,tree['record']['input'])
 r=verify_block(inp,tree['record']['certificate']);assert r['maximum']==tree['maximum'];r['global_branch']=br;r['input']=input_summary(inp)
 return [r]

def verify_job(arg):
 j,parts,L=arg;b=base_for(j,parts);fn=PROJECT/'results'/f'local_split_{L}_{parts}_{j}.json.gz'
 with gzip.open(fn,'rt')as f:rec=json.load(f)
 assert rec['base']==b and rec['part']==j and rec['parts']==parts and rec['L']==L;roots=roots_for(b);assert len(rec['trees'])==len(roots)
 reports=[]
 for root,tree in zip(roots,rec['trees']):reports+=verify_tree(b,L,root,tree)
 best=max(reports,key=lambda r:r['maximum']);return dict(part=j,ok=True,maximum=best['maximum'],leaves=len(reports),branches=sum(r['branches']for r in reports),checks=sum(r['checks']for r in reports),excluded=sum(r['excluded']for r in reports),binding=best)

if __name__=='__main__':
 import argparse
 ap=argparse.ArgumentParser();ap.add_argument('--L',default='4.15');ap.add_argument('--parts',type=int,default=8);ap.add_argument('--workers',type=int,default=3);ap.add_argument('--only',type=int,default=-1);ap.add_argument('--verify',action='store_true');aa=ap.parse_args();start=time.time()
 jobs=[(j,aa.parts,aa.L)for j in range(aa.parts)if aa.only<0 or j==aa.only];results=[]
 with ProcessPoolExecutor(max_workers=aa.workers)as pool:
  for r in pool.map(verify_job if aa.verify else job,jobs):results.append(r);print('DONE_PART',r['part'],r['ok'],r.get('maximum',0)/S,r.get('error',''),flush=True)
 rep=dict(L=aa.L,scope='Fixed first-family scenario; local second interval [1.14,1.54] and every global-second alternative',complete_local_second_cover=aa.only<0,all_pass=all(r['ok']for r in results),parts=aa.parts,regenerated_and_verified=aa.verify,results=results,seconds=time.time()-start)
 if rep['all_pass']:
  rep['maximum_numerator']=max(r['maximum']for r in results);rep['scale']=S;rep['margin_numerator']=S-rep['maximum_numerator']
  if aa.verify:
   for k in ('leaves','branches','checks','excluded'):rep[k]=sum(r[k]for r in results)
 (PROJECT/'results'/f'local_split_{aa.L}_{aa.parts}_{"verified"if aa.verify else "build"}.json').write_text(json.dumps(rep,indent=2));print('FINISH',time.time()-start,flush=True)
