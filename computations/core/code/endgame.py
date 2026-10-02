"""Analytic-model construction. No optimizer imported here.
New: third-family location constraints, a local second-zero row, shifted first envelopes.
"""
from triple_inputs import *
from refinement_cover import validate_source_cover,with_height,split_specs

@lru_cache(None)
def specs():return validate_source_cover()[0]

@lru_cache(None)
def location_proof():
 from new_positivity import lambda2_row
 return lambda2_row()

def reduced_spec(sp):
    sp=copy.deepcopy(sp);c=sp['case'];updates=[]
    a,b=Q(c['lo']),Q(c['hi'])
    if c['kind']=='rr' and Q('.7')<=a<=b<=Q('.7025'):
        location_proof();r=Q('.762');updates.append({'rule':'new_real_first_second_zero_row','lower':str(r)})
        if sp['second'] and Q(sp['second']['hi'])<=r:return None,updates
        c['source_l2']=str(max(Q(c['source_l2']),r))
        sp['ordinary_lower']=str(max(Q(sp['ordinary_lower']),r))
        if sp['second']:sp['second']['lo']=sp['ordinary_lower']
    if c['kind']=='complex':
        from poly_rows import applicable_polynomials
        for row in applicable_polynomials(a,b):
            p=row['proof'];updates.append({'rule':'complex_positive_polynomial','row_id':row['id'],'type':row['type']})
            if row['type']=='second':
                r=Q(p['h'])
                if sp['second'] and Q(sp['second']['hi'])<=r:return None,updates
                c['source_l2']=str(max(Q(c['source_l2']),r))
                sp['ordinary_lower']=str(max(Q(sp['ordinary_lower']),r))
                if sp['second']:sp['second']['lo']=sp['ordinary_lower']
            else:
                r=Q(p['new_lower']);c['lp']=str(max(Q(c['lp']),r))
                gap=sp.get('gap')
                if gap:
                    if gap['hi']!='infinity' and Q(gap['hi'])<=r:return None,updates
                    gap['lo']=str(max(Q(gap['lo']),r))
    return sp,(updates if updates else None)

def make_endgame(sp,L,par,den=200):
    source=copy.deepcopy(sp);sp,loc=reduced_spec(sp)
    if sp is None:return None
    inp=make_extended(sp,L,par,den)
    inp=input_with_third(inp,L)
    inp=use_shifted(inp,L)
    inp['location_update']=loc
    return inp

def split_new(sp,axis,mid):
    if axis!='first':return split_specs(sp,axis,mid)
    mid=Q(mid);a,b=Q(sp['case']['lo']),Q(sp['case']['hi']);assert a<mid<b
    left=copy.deepcopy(sp);right=copy.deepcopy(sp)
    left['case']['hi']=str(mid);right['case']['lo']=str(mid)
    # Keep all old lower bounds rather than implicitly interpolating/rebuilding them.
    return left,right

def parse_params(inp):
    e=inp['extension'];assert set(e)=={'variant','gG','gZ','mix','zeta'}
    assert e['variant'] in ('single','mixture','pair') and Q(e['gG'])>Q(e['gZ'])>0
    assert Q(e['mix'])>=0 and Q(e['zeta'])>0
    if e['variant']!='mixture':assert Q(e['mix'])==0
    return dict(method=e['variant'],gg=e['gG'],gz=e['gZ'],mix=e['mix'],zeta=e['zeta'])
