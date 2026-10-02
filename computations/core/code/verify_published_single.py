"""Independent exact verifier: published height-one single-zero far density.
No optimizer, no capacity table, no high-height far estimate are used here.
Analytic source lemmas are mathematical inputs, not formalized by this code.
"""
import sys,math,json,gzip,time,hashlib,argparse
from pathlib import Path
from fractions import Fraction as Q
from two_test_enclosures import BASE,OLD,S,TAU_SCALE as TS,DUAL_SCALE as DS
import verify_v5 as inherited
from cover_v5 import roots,cell,check_first_cover
if not __debug__:raise RuntimeError('Assertions must be enabled')
REGENERATE=False

def ceildiv(a,b):
 assert b>0
 return -((-a)//b)

def scenario(rec,c,L,regen=False):
 inp=rec['input'];assert inp['case']==c and inp['L']==L
 assert inp['method']=='single' and inp['column_model']=='two-test-published-single-far'
 assert inp['representative']=='height-one'
 assert inp['S']==S and inp['tau_scale']==TS and inp['dual_scale']==DS
 assert Q(inp['gamma_gram'])>Q(inp['gamma'])>0
 n=0 if c is None else (2 if c['kind']=='complex' else 1)
 assert inp['n']==n
 l2=Q(inp['ordinary_lower']);sec=inp['second'];height=inp['height']
 if c is None:
  assert height=='all' and inp['shift_rule']=='large-zero-free'
  assert inp['shift']=='3/2' and l2==Q('1.5') and sec is None and inp['gap'] is None
  assert inp['v_first']==0 and inp['first']==0 and inp['first_bounds']=={}
 else:
  assert height in ('inside','outside') and (c['kind']!='rr' or height=='inside')
  assert inp['shift_rule']=='source-global-lambda2'
  assert Q(c['source_l2'])<=l2<=3
  p=Q(inp['gap']['lo']) if inp['gap'] is not None else Q(c['lp'])
  assert Q(inp['shift'])==min(Q('1.9'),p,Q(c['source_l2'])),'unsafe local-to-global shift'
  if sec:assert Q(sec['lo'])==l2<Q(sec['hi'])<=2 and sec['n'] in (1,2)
  assert set(inp['first_bounds'])=={height}
  assert inp['first']==inp['first_bounds'][height]+(sec['contribution'] if sec else 0)
 if regen:
  from published_single_inputs import make_single,make_large
  gen=make_large(L,Q(inp['gamma_gram']),Q(inp['gamma']),inp['lambda_den']) if c is None else make_single(inp,L,Q(inp['gamma_gram']),Q(inp['gamma']),inp['lambda_den'],height)
  assert gen==inp,'regenerated single-far input mismatch'
 rows=inp['rows'];assert len(rows)>=1;pos=l2
 for row in rows[:-1]:
  assert len(row)==5 and Q(row[0])==pos<Q(row[1])<=3
  assert isinstance(row[2],int) and isinstance(row[3],int) and row[2]>0 and row[3]>=0 and isinstance(row[4],int)
  pos=Q(row[1])
 end=max(Q(3),l2);tail=rows[-1]
 assert pos==end and tail[0]==str(end) and tail[1]=='infinity' and tail[2]==S and tail[4]==-S
 assert inp['final']==5*10**10
 d,D,Df,vf=inp['d'],inp['D'],inp['Df'],inp['v_first'];assert min(d,D,Df)>0
 k=math.isqrt(d*TS*TS//S);end=k if k*k*S>=d*TS*TS else k+1
 F=inp['far_budget'];pos=count=excluded=checks=0;mx=-1;binding=None
 for br in rec['certificate']['branches']:
  a,b=br['a'],br['b'];assert a==pos and a<b<=end;pos=b;count+=1
  shift=b*(S//TS);df=max(vf-shift,0);n2=sec['n'] if sec else 0;df2=max(sec['v']-shift,0) if sec else 0
  denominator=TS*TS*d*Df*S
  numerator=D*denominator-D*a*a*Df*S*S-n*D*df*df*TS*TS*d-n2*df2*df2*TS*TS*d*Df
  B=ceildiv(numerator,denominator)
  if br.get('excluded'):assert B<0 and br['budget']==B;excluded+=1;continue
  if br.get('excluded_far'):assert F<0 and br['budget']==F;excluded+=1;continue
  assert min(F,B)>=0
  Y,Z=br['Y'],br['Z'];assert isinstance(Y,int) and isinstance(Z,int) and min(Y,Z)>=0
  for row in rows:
   C=max(row[4]-shift,0)**2//S
   assert Y*row[2]+Z*C>=row[3]*DS,('invalid column',c,height,a,b)
  checks+=len(rows)
  val=ceildiv(Y*F+Z*B,DS)+inp['first']+inp['final']
  assert val==br['upper'] and val<S,('failed objective',c,height,a,b,val)
  if val>mx:
   mx=val;binding={'case':c,'height':height,'second':sec,'ordinary_lower':str(l2),'gamma_gram':inp['gamma_gram'],'gamma_zero':inp['gamma'],'shift':inp['shift'],'branch':br,'first':inp['first'],'first_bounds':inp['first_bounds'],'far_budget':F,'near_budget':B,'final':inp['final'],'norm_certificate':inp['norm_certificate'],'spec_id':rec.get('spec_id')}
 assert pos==end and mx==rec['certificate']['maximum']
 return {'maximum':mx,'branches':count,'excluded':excluded,'checks':checks,'binding':binding}

def check_record(rec,c,L,unused=False):
 assert rec['input']['height']=='inside'
 rr=[scenario(rec,c,L,REGENERATE)]
 out=rec.get('outside')
 if c['kind']=='rr':assert out is None
 else:
  assert isinstance(out,dict),'missing outside-first-zero scenario'
  ii,oi=rec['input'],out['input']
  assert oi['height']=='outside' and rec['spec_id']==out['spec_id']
  for key in ['case','L','gap','ordinary_lower']:
   assert ii[key]==oi[key]
  assert (ii['second'] is None)==(oi['second'] is None)
  if ii['second']:
   for key in ['lo','hi','n']:assert ii['second'][key]==oi['second'][key]
  rr.append(scenario(out,c,L,REGENERATE))
 best=max(rr,key=lambda t:t['maximum'])
 return {'maximum':best['maximum'],'branches':sum(t['branches'] for t in rr),'excluded':sum(t['excluded'] for t in rr),'checks':sum(t['checks'] for t in rr),'binding':best['binding'],'scenarios':len(rr),'scenario_maxima':{('inside' if j==0 else 'outside'):t['maximum'] for j,t in enumerate(rr)}}

inherited.check_record=check_record

def full(path,L,regen=False):
 global REGENERATE
 REGENERATE=regen;t=time.time();expected=roots();cs=[];ids=[];nr=ng=nc=ns=nb=ne=nk=0;mx=-1;binding=None;stats={};hstats={}
 with gzip.open(path,'rt') as f:
  for i,text in enumerate(f):
   rt=json.loads(text);assert i<len(expected) and rt['root']==expected[i];nr+=1;pos=Q(rt['root']['lo'])
   for leaf in rt['leaves']:
    c=leaf['case'];assert c==cell(c['parent'],c['lo'],c['hi']) and c['parent']==rt['root']['parent'] and Q(c['lo'])==pos
    pos=Q(c['hi']);assert pos<=Q(rt['root']['hi']);cs.append(c);ng+=len(leaf['proofs'])
    for pr in leaf['proofs']:
     assert pr['method']=='single'
     ids.extend(rec['spec_id'] for rec in pr['records'])
    for r in inherited.check_leaf(leaf,L,False):
     nc+=1;ns+=r['scenarios'];nb+=r['branches'];ne+=r['excluded'];nk+=r['checks'];stats[c['kind']]=max(stats.get(c['kind'],-1),r['maximum'])
     for h,val in r['scenario_maxima'].items():hstats[h]=max(hstats.get(h,-1),val)
     if r['maximum']>mx:mx=r['maximum'];binding=r['binding']
   assert pos==Q(rt['root']['hi'])
   if nr%50==0:print('ROOTS',nr,'MAX',mx/S,'SECONDS',round(time.time()-t,1),flush=True)
 assert nr==len(expected) and ids==list(range(2768));check_first_cover(cs)
 bigpath=BASE/'results/certificate_published_large.json';br=json.loads(bigpath.read_text())
 big=scenario(br,None,L,True)
 from small_exception import check
 small=check(L)
 from two_test_enclosures import wgt,lower
 w=wgt(L);support=lower(w.A-3);decay=lower(w.A-2*w.x);assert min(support,decay)>0
 result={'L':L,'status':'PASS: exact finite reduction using published single-zero height-one far density','regenerated_all_inputs':regen,'regenerated_large_input':True,'roots':nr,'first_zero_cells':len(cs),'gap_cases':ng,'density_cases':nc,'height_scenarios':ns,'threshold_branches':nb,'excluded_branches':ne,'exact_dual_column_checks':nk,'paired_near_cases':0,'capacity_blocks_used':0,'maxima_by_kind':stats,'maxima_by_height':hstats,'maximum_numerator':mx,'scale':S,'margin_numerator':S-mx,'binding':binding,'large_case':big,'small_exception':small,'support_margin':support,'decay_margin':decay,'certificate_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'large_certificate_sha256':hashlib.sha256(bigpath.read_bytes()).hexdigest(),'seconds':time.time()-t,'scope':'Verifies the finite arithmetic reduction, not a formalization of source lemmas or the new two-test analytic argument. Uses no two-zero far-block or high-height far extension. Imported zero-location implications remain mathematical inputs.'}
 return result

if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('certificate',type=Path);ap.add_argument('--L',default='4.40');ap.add_argument('--regenerate',action='store_true');a=ap.parse_args()
 r=full(a.certificate,a.L,a.regenerate);out=BASE/'results/verification_published_4_40.json';out.write_text(json.dumps(r,indent=2));print(json.dumps(r,indent=2),flush=True)
