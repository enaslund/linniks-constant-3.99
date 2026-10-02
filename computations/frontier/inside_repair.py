"""Exact numerical repair of unresolved inside leaves, with exhaustive partitions.

Imports analytic premises and interval enclosures from retained core/near code.
Stores compact input hashes; verification regenerates inputs and checks rational
column inequalities, every threshold, and every source/identity subdivision.
"""
from root_store import read_root,has_root,root_ids
from inside_model import *
from build_progress import solve, CannotCertify
from verify_progress import scenario as verify_core
from compact_records import compact_certificate, expand_certificate, input_digest
from far_enclosures import CANDIDATE, replace_far, verify_far_record
from concurrent.futures import ProcessPoolExecutor, as_completed
import argparse, time, traceback

SINGLE_PAR = dict(method='single',gg='1.6',gz='1.18',mix='0',zeta='3')
RR_PAR = dict(method='mixture',gg='1.761626',gz='1.072176',mix='.119742',zeta='3')
RC_PAR = dict(method='mixture',gg='1.688162',gz='1.054813',mix='.126521',zeta='3')
COMPLEX_PAR = dict(method='mixture',gg='1.642553',gz='1.080907',mix='.172298',zeta='3')
COMPLEX_HIGH_PAR = dict(method='mixture',gg='1.841479',gz='1.094694',mix='.102485',zeta='3')
PAIRED_WIDE_PAR = dict(method='pair',gg='1.7',gz='1.18',mix='0',zeta='3')
MENU = [PAR,
    dict(method='mixture',gg='1.6',gz='1.08',mix='.18',zeta='3'),
    SINGLE_PAR]


def unique_parameters(parameters):
    answer=[];seen=set()
    for par in parameters:
        key=(par['method'],)+(tuple(Q(par[k]) for k in ('gg','gz','mix','zeta')))
        if key not in seen:answer.append(par);seen.add(key)
    return answer


def branch_build(base, L, br, parameters, depth=0):
    parameters=unique_parameters(parameters)
    last = None
    for par,den in [(p,200)for p in parameters]+[(p,400)for p in parameters]+[(parameters[0],800),(parameters[0],2000)]:
        inp = make_inside_input(base,L,br,par,den)
        for changed in (False,True):
            if changed:
                from inside_far import replace_inside_far
                ii=replace_inside_far(inp)
            else: ii=inp
            try:
                cc = cert_block(ii,target=Q('.999999'),width=4)
                rep = verify_block(ii,cc)
                record=dict(branch=br, parameters=par, input=input_summary(ii), certificate=cc, maximum=rep['maximum'])
                if changed:record['far_parameters']=copy.deepcopy(CANDIDATE)
                return record
            except RuntimeError as e: last=e
    if br['hi'] != 'infinity' and depth < 8 and Q(br['hi'])-Q(br['lo']) > Q('.005'):
        mid=(Q(br['lo'])+Q(br['hi']))/2
        aa=branch_build(base,L,dict(br,hi=str(mid)),parameters[:1],depth+1)
        bb=branch_build(base,L,dict(br,lo=str(mid)),parameters[:1],depth+1)
        return dict(branch=br,split=str(mid),children=[aa,bb],maximum=max(aa['maximum'],bb['maximum']))
    raise RuntimeError(dict(reason='unresolved identity',spec=spec_from_input(base),branch=br,parameters=parameters,last=repr(last)))


def regenerate_location_row(row):
    if row.get('kind')=='degree5-conductor':
        from polynomial5_rows import regenerate_row5
        return regenerate_row5(row)
    from inside_real_rows import certify_row
    return certify_row(row['a'],row['b'],row['lower'],row['gamma'],row['t'],saving=Q(row.get('generic_saving','0')))


@lru_cache(None)
def real_rows():
    from inside_real_rows import certify_row
    rows=[]
    paths=list(Path(__file__).resolve().parent.glob('inside_real_rows_*.json'))+list(Path(__file__).resolve().parent.glob('inside_conductor_rows_*.json'))+list(Path(__file__).resolve().parent.glob('inside_polynomial5_rows_*.json'))
    for path in sorted(paths):
        data=json.loads(path.read_text())
        for row in data['rows']:
            generated=regenerate_location_row(row)
            assert generated==row
            rows.append(row)
    return tuple(rows)


def real_update(sp,row):
    assert sp['case']['kind']=='rr'
    assert Q(row['a'])<=Q(sp['case']['lo'])<=Q(sp['case']['hi'])<=Q(row['b'])
    h=Q(row['lower']);new=copy.deepcopy(sp)
    if new.get('second') and Q(new['second']['hi'])<=h:return None
    new['case']['source_l2']=str(max(Q(new['case']['source_l2']),h))
    new['ordinary_lower']=str(max(Q(new['ordinary_lower']),h))
    if new.get('second'):new['second']['lo']=new['ordinary_lower']
    return new


def build_leaf(sp,L,sourcepar,depth=0):
    if sp['case']['kind']=='complex':
        from inside_complex_rows import propose_complex_row,complex_update
        row=propose_complex_row(sp['case']['lo'],sp['case']['hi'])
        if row is not None and Q(row['h'])>Q(sp['case']['source_l2']):
            new=complex_update(sp,row)
            if new is None:return dict(complex_location=row,excluded=True,maximum=-1)
            child=build_leaf(new,L,sourcepar,depth)
            return dict(complex_location=row,child=child,maximum=child.get('maximum',-1))
    if sp['case']['kind']=='rr':
        applicable=[r for r in real_rows() if Q(r['a'])<=Q(sp['case']['lo'])<=Q(sp['case']['hi'])<=Q(r['b']) and Q(r['lower'])>Q(sp['case']['source_l2'])]
        if applicable:
            row=max(applicable,key=lambda r:Q(r['lower']));new=real_update(sp,row)
            if new is None:return dict(real_location=row,excluded=True,maximum=-1)
            child=build_leaf(new,L,sourcepar,depth)
            return dict(real_location=row,child=child,maximum=child.get('maximum',-1))
    par0=dict(sourcepar)
    if par0['method']=='pair': par0=dict(SINGLE_PAR)
    complex_menu=([COMPLEX_HIGH_PAR,COMPLEX_PAR] if Q(sp['case']['lo'])>=Q('.74') else [COMPLEX_PAR,COMPLEX_HIGH_PAR])+MENU
    menu=([RC_PAR]+MENU) if sp['case']['kind']=='rc' else ([RR_PAR]+MENU) if sp['case']['kind']=='rr' else complex_menu
    params=unique_parameters(menu+[par0])
    gap=sp.get('gap')
    finite_pair=sp['case']['kind']=='complex' and gap is not None and gap['hi']!='infinity'
    source_pair=sourcepar['method']=='pair' and finite_pair
    paired=([dict(sourcepar)] if source_pair else [])
    if finite_pair:paired.extend([dict(SINGLE_PAR,method='pair'),PAIRED_WIDE_PAR])
    ordinary_params=unique_parameters(paired+params)
    # Cheap alternatives can close a leaf without adding hidden-family structure.
    # Keep the paired first-family test in this ordinary stage. Its conversion
    # to a single test above is needed only by the hidden-family constructor.
    trials=[(p,200)for p in ordinary_params]+[(p,400)for p in ordinary_params]
    dense_params=unique_parameters(paired+[params[0]])
    trials += [(p,den) for den in (800,2000) for p in dense_params]
    for par,den in trials:
        inp=make_endgame(sp,L,par,den)
        if inp is None:
            red, proof=reduced_spec(sp); assert red is None
            return dict(second_exclusion=proof)
        for changed in (False,True):
            ii=replace_far(inp) if changed else inp
            try:
                cc=solve(ii,target=Q('.999999'),accept=Q('.999999'),min_width=4)
                rep=verify_core(dict(input=ii,certificate=cc))
                if changed:
                    record=dict(parameters=par,lambda_den=den,far_parameters=copy.deepcopy(CANDIDATE),input_sha256=input_digest(ii),certificate=compact_certificate(cc))
                    return dict(far=record,maximum=rep['maximum'])
                return dict(core=dict(parameters=par,input=input_summary(ii),certificate=compact_certificate(cc)),maximum=rep['maximum'])
            except CannotCertify: pass
    base=make_endgame(sp,'4.33',par0,200)
    try:
        plan=roots(base)
        # The unhidden alternative is often the obstruction. Check it before
        # spending time on hidden covers that a source split would discard.
        unhidden=branch_build(base,L,plan[-1],params)
        trees=[branch_build(base,L,br,params) for br in plan[:-1]]+[unhidden]
        return dict(identities=trees, maximum=max(t['maximum'] for t in trees))
    except RuntimeError as e:
        if depth>=5: raise
        sec=sp.get('second'); options=[]
        if sec and Q(sec['hi'])-Q(sp['ordinary_lower'])>Q('.005'):
            options.append((float(Q(sec['hi'])-Q(sp['ordinary_lower'])),'second',(Q(sec['hi'])+Q(sp['ordinary_lower']))/2))
        if finite_pair and Q(gap['hi'])-Q(gap['lo'])>Q('.0125'):
            options.append((float(Q(gap['hi'])-Q(gap['lo'])),'gap',(Q(gap['hi'])+Q(gap['lo']))/2))
        if sp['case']['kind']=='complex' and (gap is None or gap['hi']=='infinity'):
            lo=Q(gap['lo']) if gap else Q(sp['case']['lp'])
            mid=max(lo+Q('.25'),Q('1.166'))
            options.append((float(mid-lo),'gap',mid))
        a,b=Q(sp['case']['lo']),Q(sp['case']['hi'])
        if b-a>Q('.0003125'): options.append((float(b-a)*3,'first',(a+b)/2))
        if not options: raise
        _,axis,mid=max(options); sa,sb=split_new(sp,axis,str(mid))
        aa=build_leaf(sa,L,sourcepar,depth+1); bb=build_leaf(sb,L,sourcepar,depth+1)
        return dict(split=axis,mid=str(mid),children=[aa,bb],maximum=max(aa.get('maximum',-1),bb.get('maximum',-1)))


def verify_branch(base,L,br,node):
    assert node['branch']==br
    if 'split'in node:
        assert set(node)=={'branch','split','children','maximum'} and len(node['children'])==2
        mid=Q(node['split']); assert Q(br['lo'])<mid<Q(br['hi'])
        aa=verify_branch(base,L,dict(br,hi=str(mid)),node['children'][0])
        bb=verify_branch(base,L,dict(br,lo=str(mid)),node['children'][1])
        assert node['maximum']==max(t['maximum'] for t in aa+bb)
        return aa+bb
    expected={'branch','parameters','input','certificate','maximum'}
    if 'far_parameters'in node:expected.add('far_parameters')
    assert set(node)==expected
    inp=make_inside_input(base,L,br,node['parameters'],node['input']['lambda_den'])
    if 'far_parameters'in node:
        from inside_far import replace_inside_far
        inp=replace_inside_far(inp,node['far_parameters'])
    check_input(inp,node['input'])
    rep=verify_block(inp,node['certificate']); assert rep['maximum']==node['maximum']; return [rep]


def verify_leaf(sp,L,sourcepar,node):
    if 'complex_location'in node:
        from inside_complex_rows import regenerate_complex_row,complex_update
        row=node['complex_location'];assert regenerate_complex_row(row)==row
        new=complex_update(sp,row)
        if new is None:
            assert node==dict(complex_location=row,excluded=True,maximum=-1);return []
        assert set(node)=={'complex_location','child','maximum'}
        out=verify_leaf(new,L,sourcepar,node['child'])
        assert node['maximum']==max((r['maximum']for r in out),default=-1)
        return out
    if 'real_location'in node:
        from inside_real_rows import certify_row
        row=node['real_location'];assert regenerate_location_row(row)==row
        new=real_update(sp,row)
        if new is None:
            assert node==dict(real_location=row,excluded=True,maximum=-1);return []
        assert set(node)=={'real_location','child','maximum'}
        out=verify_leaf(new,L,sourcepar,node['child'])
        assert node['maximum']==max((r['maximum']for r in out),default=-1)
        return out
    if 'second_exclusion'in node:
        red, proof=reduced_spec(sp); assert red is None and proof==node['second_exclusion']; return []
    if 'split'in node:
        assert set(node)=={'split','mid','children','maximum'} and len(node['children'])==2
        aa,bb=split_new(sp,node['split'],node['mid'])
        out=verify_leaf(aa,L,sourcepar,node['children'][0])+verify_leaf(bb,L,sourcepar,node['children'][1])
        assert node['maximum']==max((r['maximum']for r in out),default=-1)
        return out
    if 'far'in node:
        assert set(node)=={'far','maximum'}
        rep=verify_far_record(sp,node['far'],L);assert rep['maximum']==node['maximum'];return [rep]
    if 'core'in node:
        assert set(node)=={'core','maximum'}
        rec=node['core']; inp=make_endgame(sp,L,rec['parameters'],rec['input']['lambda_den']);check_input(inp,rec['input'])
        cc=expand_certificate(rec['certificate'],inp);rep=verify_core(dict(input=inp,certificate=cc)); assert rep['maximum']==node['maximum'];return [rep]
    assert set(node)=={'identities','maximum'}
    par0=dict(sourcepar)
    if par0['method']=='pair':par0=dict(SINGLE_PAR)
    base=make_endgame(sp,'4.33',par0,200);plan=roots(base);assert len(plan)==len(node['identities'])
    out=[]
    for br,tree in zip(plan,node['identities']):out+=verify_branch(base,L,br,tree)
    assert node['maximum']==max(r['maximum']for r in out);return out


def job(arg):
    idx,L,verify=arg; start=time.time();root=Path(__file__).resolve().parent
    source=root/f'core_{L}';repairs=root/f'inside_repairs_{L}';dest=repairs/f'{idx:04d}.json.gz'
    old=read_root(source,idx)
    ans=[]
    if verify:
        saved=read_root(repairs,idx)
        assert saved['id']==idx and saved['L']==L and len(saved['repairs'])==len(old['failures'])
    elif has_root(repairs,idx):return dict(id=idx,ok=True,cached=True)
    records=[]
    for j,fail in enumerate(old['failures']):
        try:
            if verify:
                rec=saved['repairs'][j];assert rec['path']==fail['path'] and rec['source']==fail
                tree=rec['tree']
            else:tree=build_leaf(fail['spec'],L,fail['parameters'])
            reps=verify_leaf(fail['spec'],L,fail['parameters'],tree)
            records.append(dict(path=fail['path'],source=fail,tree=tree));ans+=reps
        except Exception as e:
            return dict(id=idx,path=fail['path'],ok=False,error=repr(e),model=(e.args[0] if e.args and isinstance(e.args[0],dict) else None),trace=traceback.format_exc(limit=2,chain=False),seconds=time.time()-start)
    if not verify:
        with gzip.open(dest,'wt')as f:json.dump(dict(id=idx,L=L,repairs=records),f,separators=(',',':'))
    return dict(id=idx,ok=True,maximum=max((r['maximum']for r in ans),default=-1),leaves=len(ans),branches=sum(r['branches']for r in ans),checks=sum(r['checks']for r in ans),seconds=time.time()-start)

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--L',default='4.30');ap.add_argument('--ids',default='71,73,75,76,77,78');ap.add_argument('--workers',type=int,default=2);ap.add_argument('--verify',action='store_true');aa=ap.parse_args()
    dest=Path(__file__).resolve().parent/f'inside_repairs_{aa.L}';dest.mkdir(exist_ok=True);out=[];start=time.time()
    if aa.ids == 'pending':
        ids=[]
        source=Path(__file__).resolve().parent/f'core_{aa.L}'
        for idx in root_ids(source):
            record=read_root(source,idx)
            if record['failures'] and not has_root(dest,idx): ids.append(idx)
    else: ids=list(map(int,aa.ids.split(',')))
    assert ids, 'No selected unresolved roots'
    with ProcessPoolExecutor(max_workers=aa.workers)as pool:
        fs=[pool.submit(job,(i,aa.L,aa.verify))for i in ids]
        for fu in as_completed(fs):
            result=fu.result();out.append(result);print(json.dumps(result),flush=True)
            (dest/f'{"verify"if aa.verify else "build"}_{min(ids)}_{max(ids)}.json').write_text(json.dumps(dict(L=aa.L,ids=ids,regenerated=aa.verify,seconds=time.time()-start,results=out),indent=2))
