"""Exact configuration cover for the new near refinements. No optimizer.
The source tables are accepted analytic inputs, not independently reproved.
"""
import json,gzip,copy
from pathlib import Path
from fractions import Fraction as Q
from two_test_enclosures import BASE
import verify_v5 as inherited
from cover_v5 import roots,cell,check_first_cover

def compact_spec(inp):
 return dict(case=inp['case'],ordinary_lower=inp['ordinary_lower'],gap=inp.get('gap'),second=({k:inp['second'][k] for k in ('lo','hi','n')} if inp.get('second') else None),method='single')

def validate_source_cover(path=None):
 path=path or BASE/'results/source_cover.json.gz'
 with gzip.open(path,'rt') as f: cover=json.load(f)
 expected=roots();assert len(cover)==len(expected)
 allcells=[];specs=[];ngaps=0
 def checkrecord(rec,c,L,unused=False):
  assert rec['spec_id']==len(specs)
  inp=rec['input'];assert inp['case']==c and inp['method']=='single'
  r=Q(inp['ordinary_lower']);assert Q(c['source_l2'])<=r<=3
  sec=inp['second']
  if sec:assert Q(sec['lo'])==r<Q(sec['hi'])<=2 and sec['n'] in (1,2)
  specs.append(inp)
  return {'binding':None}
 old=inherited.check_record;inherited.check_record=checkrecord
 try:
  for rt,ex in zip(cover,expected):
   assert rt['root']==ex;pos=Q(ex['lo'])
   for leaf in rt['leaves']:
    c=leaf['case'];assert c==cell(c['parent'],c['lo'],c['hi']) and c['parent']==ex['parent'] and Q(c['lo'])==pos
    pos=Q(c['hi']);assert pos<=Q(ex['hi']);allcells.append(c);ngaps+=len(leaf['proofs'])
    for pr in leaf['proofs']:assert pr['method']=='single'
    inherited.check_leaf(leaf,'unused',False)
   assert pos==Q(ex['hi'])
 finally:inherited.check_record=old
 assert len(specs)==2768;check_first_cover(allcells)
 return specs,dict(roots=len(cover),first_zero_cells=len(allcells),source_gap_cases=ngaps,source_density_cases=len(specs))

def with_height(sp,h):
 sp=copy.deepcopy(sp);assert h in ('inside','outside') and (sp['case']['kind']!='rr' or h=='inside');sp['height']=h;return sp

def split_specs(sp,axis,mid):
 """Both children exhaust the parent's second/gap interval exactly."""
 mid=Q(mid);aa=copy.deepcopy(sp);bb=copy.deepcopy(sp)
 if axis=='second':
  assert sp['second'] is not None
  lo=Q(sp['ordinary_lower']);hi=Q(sp['second']['hi']);assert lo<mid<hi
  aa['second']['hi']=str(mid);bb['ordinary_lower']=str(mid);bb['second']['lo']=str(mid)
 elif axis=='gap':
  assert sp['case']['kind']=='complex'
  gap=sp.get('gap');lo=Q(gap['lo']) if gap else Q(sp['case']['lp']);hi=Q(gap['hi']) if gap and gap['hi']!='infinity' else None
  assert lo<mid and (hi is None or mid<hi)
  aa['gap']={'lo':str(lo),'hi':str(mid)};bb['gap']={'lo':str(mid),'hi':str(hi) if hi is not None else 'infinity'}
 else:raise AssertionError('unknown refinement axis')
 return aa,bb
