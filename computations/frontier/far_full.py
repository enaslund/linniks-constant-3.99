"""Complete inherited inside cover with core/far and checked repair leaves.

Leaves already certified by the independent core run at4.30 may retain that
smaller exponent. Higher-exponent witnesses supply proposal plans only. The verification
mode regenerates every input and checks every source and threshold partition.
"""
import os
os.environ.setdefault('OPENBLAS_NUM_THREADS','1');os.environ.setdefault('OMP_NUM_THREADS','1')
import argparse,ast,copy,gzip,hashlib,json,time,traceback
from datetime import datetime,timezone
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor,as_completed
from far_enclosures import make_endgame,replace_far,CANDIDATE,verify_far_record,far_weights
from endgame import specs,with_height,split_new,Q,wgt,location_proof
from compact_records import compact_node,compact_certificate,input_digest,regenerate_record
from verify_progress import scenario,verify_tree
from base_enclosures import S,lower
from far_storage import load_root,load_roots,corpus_digest,root_digest,digest_rows,CANONICAL_RULE,pack_corpus
from root_store import read_root,has_root
HERE=Path(__file__).resolve().parent;CORE=HERE.parent/'core'
SOURCE=CORE/'results/certificate_4.33.jsonl.gz'
MENU=[dict(method='mixture',gg='1.7504',gz='1.09006',mix='.1385',zeta='3'),
      dict(method='mixture',gg='1.6',gz='1.08',mix='.18',zeta='3'),
      dict(method='single',gg='1.6',gz='1.18',mix='0',zeta='3')]


def original_roots():
    with gzip.open(SOURCE,'rt')as f:roots=[json.loads(s)for s in f]
    assert [r['id']for r in roots]==list(range(len(specs())))
    return roots


def parameter_key(p):
    return (p['method'],)+(tuple(Q(p[k])for k in ('gg','gz','mix','zeta')))


def menu_for(sp):
    kind=sp['case']['kind']
    if kind=='rr':
        tuned=[dict(method='mixture',gg='1.761626',gz='1.072176',mix='.119742',zeta='3')]
    elif kind=='rc':
        tuned=[dict(method='mixture',gg='1.688162',gz='1.054813',mix='.126521',zeta='3')]
    else:
        assert kind=='complex'
        tuned=[dict(method='mixture',gg='1.841479',gz='1.094694',mix='.102485',zeta='3'),
               dict(method='mixture',gg='1.642553',gz='1.080907',mix='.172298',zeta='3')]
        if Q(sp['case']['lo'])<Q('.74'):tuned.reverse()
    return tuned+MENU


def eligible_exponent(L,target):
    assert type(L)==str and Q('4.30')<=Q(L)<=Q(target)


def proposal_seeds(node):
    """Extract parameters only; no higher-exponent assertion is inherited."""
    if node is None:return []
    out=[]
    for kind in ('core','far','kernel'):
        if kind in node:
            rec=node[kind]
            if 'record'in rec:rec=rec['record']
            if 'parameters'in rec:out.append((rec['parameters'],kind=='far'))
    if 'parameters'in node and set(node['parameters'])=={'method','gg','gz','mix','zeta'}:
        out.append((node['parameters'],False))
    if 'repair'in node:out+=proposal_seeds(node['repair']['tree'])
    if 'child'in node:out+=proposal_seeds(node['child'])
    for field in ('children','identities'):
        for child in node.get(field,[]):out+=proposal_seeds(child)
    unique=[]
    for item in out:
        if not any(parameter_key(item[0])==parameter_key(old[0])for old in unique):unique.append(item)
    return unique


def build_tree(sp,old,baseline,L,path,failures,seed=None):
    if 'split'in old:
        assert baseline is None or all(baseline[k]==old[k]for k in ('split','mid'))
        aa=split_new(sp,old['split'],old['mid'])
        return dict(split=old['split'],mid=old['mid'],children=[
            build_tree(s,n,None if baseline is None else baseline['children'][j],L,path+str(j),failures,
                       None if seed is None else seed['children'][j])
            for j,(s,n)in enumerate(zip(aa,old['children']))])
    if 'record'not in old:
        assert baseline is None or baseline==old
        verify_tree(sp,old,L)
        return copy.deepcopy(old)
    if baseline is not None and 'record'in baseline:
        return dict(core=dict(L='4.30',record=copy.deepcopy(baseline['record'])))
    if baseline is not None:assert 'unresolved'in baseline
    from build_progress import solve,CannotCertify
    sourcepar=old['record']['parameters'];den=old['record']['lambda_den'];attempts=[]
    if seed is not None and 'repair'in seed:
        repair=seed['repair']
        try:
            from inside_repair import verify_leaf
            assert set(seed)=={'repair'}and set(repair)=={'L','parameters','tree'}
            if Q(repair['L'])<=Q(L):
                eligible_exponent(repair['L'],L)
                verify_leaf(sp,repair['L'],repair['parameters'],repair['tree'])
                return copy.deepcopy(seed)
            from retarget_repair import retarget_plan
            tree=retarget_plan(sp,L,repair['parameters'],repair['tree'])
            verify_leaf(sp,L,repair['parameters'],tree)
            return dict(repair=dict(L=L,parameters=repair['parameters'],tree=tree))
        except (CannotCertify,RuntimeError,AssertionError)as ex:
            attempts.append(dict(retarget_repair=repair['L'],error=repr(ex)))
    seeds=proposal_seeds(seed)
    params=[]
    for p in [p for p,_ in seeds]+[sourcepar]+menu_for(sp):
        if not any(parameter_key(p)==parameter_key(old)for old in params):params.append(p)
    for par in params:
        try:inp=make_endgame(sp,L,par,den)
        except AssertionError as ex:
            attempts.append(dict(parameters=par,error=repr(ex)));continue
        assert inp is not None
        prefer_far=next((flag for p,flag in seeds if parameter_key(p)==parameter_key(par)),False)
        for changed in ((True,False)if prefer_far else (False,True)):
            ii=replace_far(inp)if changed else inp
            try:
                cc=solve(ii,target=Q('.999999'),accept=Q('.999999'),min_width=1)
                scenario(dict(input=ii,certificate=cc))
                if changed:
                    record=dict(parameters=par,lambda_den=den,far_parameters=CANDIDATE,
                                input_sha256=input_digest(ii),certificate=compact_certificate(cc))
                    return dict(far=dict(L=L,record=record))
                record=compact_node(dict(record=dict(input=ii,certificate=cc)))['record']
                return dict(core=dict(L=L,record=record))
            except CannotCertify as ex:
                attempts.append(dict(parameters=par,far=changed,failure=ex.args[0]))
    failure=dict(path=path,spec=sp,parameters=sourcepar,lambda_den=den,attempts=attempts)
    failures.append(failure);return dict(unresolved=failure)


def counts(tree):
    if 'split'in tree:
        result=[]
        for t in tree['children']:result+=counts(t)
        return result
    if 'repair'in tree:
        r=tree['repair']
        return [dict(kind='repair',L=r['L'],maximum=r['tree'].get('maximum',-1))]
    for kind in ('core','far'):
        if kind in tree:
            q=tree[kind];return [dict(kind=kind,L=q['L'],maximum=q['record']['certificate']['maximum'])]
    return []


def build_job(arg):
    old,L=arg;idx=old['id'];start=time.time();baseline=None
    baseline_directory=HERE/'core_4.30'
    if has_root(baseline_directory,idx):
        try:
            br=read_root(baseline_directory,idx)
            assert br['id']==idx and br['L']=='4.30';baseline=br['inside']
        except (EOFError,OSError,json.JSONDecodeError):pass
    seed=None
    for previous_L in ('4.32','4.328'):
        if Q(L)<Q(previous_L):
            try:
                previous=load_root(idx,previous_L)
            except (EOFError,OSError,json.JSONDecodeError):continue
            assert previous['id']==idx and previous['target']==previous_L
            seed=previous['inside'];break
    failures=[]
    tree=build_tree(with_height(specs()[idx],'inside'),old['inside'],baseline,L,'',failures,seed)
    scope=counts(tree)
    return dict(id=idx,target=L,inside=tree,all_pass=not failures,failures=failures,
                maximum=max((x['maximum']for x in scope),default=-1),
                kinds={k:sum(x['kind']==k for x in scope)for k in ('core','far','repair')},
                reused_4_30=sum(x['L']=='4.30'for x in scope),seconds=time.time()-start)


def verify_tree_new(sp,node,target):
    if 'split'in node:
        assert set(node)=={'split','mid','children'}and len(node['children'])==2
        aa,bb=split_new(sp,node['split'],node['mid'])
        return verify_tree_new(aa,node['children'][0],target)+verify_tree_new(bb,node['children'][1],target)
    if 'repair'in node:
        assert set(node)=={'repair'}
        repair=node['repair'];assert set(repair)=={'L','parameters','tree'}
        eligible_exponent(repair['L'],target)
        from inside_repair import verify_leaf
        reports=verify_leaf(sp,repair['L'],repair['parameters'],repair['tree'])
        for r in reports:r.update(kind='repair',L=repair['L'])
        return reports
    if 'core'in node or 'far'in node:
        assert len(node)==1;kind=next(iter(node));record=node[kind]
        assert set(record)=={'L','record'}
        eligible_exponent(record['L'],target)
        if kind=='far':rep=verify_far_record(sp,record['record'],record['L'])
        else:rep=scenario(regenerate_record(sp,record['record'],record['L']))
        rep.update(kind=kind,L=record['L']);return [rep]
    assert 'unresolved'not in node, 'Unresolved source scope'
    return verify_tree(sp,node,target)


def verify_job(arg):
    idx,L=arg;start=time.time()
    r=load_root(idx,L)
    assert r['id']==idx and r['target']==L and r['all_pass']and not r['failures']
    reps=verify_tree_new(with_height(specs()[idx],'inside'),r['inside'],L)
    maximum=max((x['maximum']for x in reps),default=-1);assert maximum==r['maximum']
    return dict(id=idx,maximum=maximum,leaves=len(reps),branches=sum(x['branches']for x in reps),
                checks=sum(x['checks']for x in reps),seconds=time.time()-start,
                root_sha256=root_digest(r))


def global_checks(target):
    from poly_rows import verify_polynomial_table
    from alias_check import check as check_alias
    from refinement_cover import validate_source_cover
    polynomials=verify_polynomial_table()
    alias=check_alias()
    location=location_proof()
    _,cover=validate_source_cover()
    margins=[]
    for L in sorted({'4.30',target}):
        old=wgt(L)
        row=dict(L=L,support=lower(old.A-3),old_far_decay=lower(old.A-2*old.x),
                 new_far_decay=lower(old.A-2*far_weights().x))
        assert min(row[k]for k in ('support','old_far_decay','new_far_decay'))>0
        margins.append(row)
    return dict(polynomials=polynomials,alias=alias,new_real_row=location,
                source_cover=cover,support_and_decay=margins,
                polynomial_table_sha256=hashlib.sha256((CORE/'results/polynomial_table.json').read_bytes()).hexdigest())


def verification_commitments():
    """Bind retained math code, local import dependencies, and dynamic rows."""
    repo=HERE.parents[1]
    files={p for base in (CORE/'code',HERE.parent/'near/code')for p in base.glob('*.py')}
    pending=[HERE/'far_full.py'];frontier=set()
    while pending:
        path=pending.pop()
        if path in frontier:continue
        frontier.add(path)
        for node in ast.walk(ast.parse(path.read_text())):
            modules=([node.module]if isinstance(node,ast.ImportFrom)and node.module else
                     [alias.name for alias in node.names]if isinstance(node,ast.Import)else [])
            for module in modules:
                dependency=HERE/(module.split('.')[0]+'.py')
                if dependency.exists()and dependency not in frontier:pending.append(dependency)
    files.update(frontier)
    files.update({SOURCE,CORE/'results/polynomial_table.json',CORE/'results/source_cover.json.gz'})
    for pattern in ('inside_real_rows_*.json','inside_conductor_rows_*.json','inside_polynomial5_rows_*.json'):
        files.update(HERE.glob(pattern))
    return {str(p.relative_to(repo)):hashlib.sha256(p.read_bytes()).hexdigest()for p in sorted(files)}


def carry_corpus(source,target):
    """Retain all leaf exponents and unresolved scopes at a larger common target."""
    assert Q('4.30')<=Q(source)<Q(target)
    roots=load_roots(source);digest=corpus_digest(source)
    dest=HERE/f'far_full_{target}';dest.mkdir(exist_ok=True)
    assert not(HERE/f'far_full_{target}.jsonl.gz').exists()
    assert not list(dest.glob('[0-9]*.json.gz')),'Target already has working roots'
    for old in roots:
        root=copy.deepcopy(old);root['target']=target
        file=dest/f"{root['id']:04d}.json.gz";tmp=file.with_suffix('.tmp')
        with gzip.open(tmp,'wt')as stream:json.dump(root,stream,separators=(',',':'),allow_nan=False)
        tmp.replace(file)
    assert corpus_digest(source)==digest,'Source corpus changed during carry'
    report=dict(date=datetime.now(timezone.utc).date().isoformat(),source=source,target=target,source_roots=len(roots),source_corpus_sha256=digest,
                corpus_hash_rule=CANONICAL_RULE,leaf_exponents_unchanged=True,
                unresolved_roots=sum(not r['all_pass']for r in roots),
                unresolved_leaves=sum(len(r['failures'])for r in roots),
                status='Proposal corpus only; complete fresh verification is required')
    (dest/'carry.json').write_text(json.dumps(report,indent=2)+'\n')
    return report


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--L',default='4.328');ap.add_argument('--workers',type=int,default=2)
    ap.add_argument('--verify',action='store_true');ap.add_argument('--ids',default='');ap.add_argument('--retry-failures',action='store_true')
    ap.add_argument('--pack',action='store_true')
    ap.add_argument('--carry-from',default='')
    args=ap.parse_args();assert Q(args.L)>=Q('4.30')
    if args.pack:
        assert not args.verify and not args.ids and not args.retry_failures and not args.carry_from
        print(json.dumps(pack_corpus(args.L)),flush=True);return
    if args.carry_from:
        assert not args.verify and not args.ids and not args.retry_failures
        print(json.dumps(carry_corpus(args.carry_from,args.L)),flush=True);return
    dest=HERE/f'far_full_{args.L}';dest.mkdir(exist_ok=True)
    roots=original_roots();ids=set(map(int,args.ids.split(',')))if args.ids else set(range(len(roots)))
    start=time.time();results=[];todo=[]
    commitments_before=verification_commitments()if args.verify else None
    source_checks=global_checks(args.L)if args.verify else None
    for old in roots:
        idx=old['id']
        if idx not in ids:continue
        fn=dest/f'{idx:04d}.json.gz'
        if args.verify:todo.append((idx,args.L));continue
        if fn.exists()or(HERE/f'far_full_{args.L}.jsonl.gz').exists():
            r=load_root(idx,args.L)
            if not args.retry_failures or r['all_pass']:results.append(r);continue
        todo.append((old,args.L))
    with ProcessPoolExecutor(max_workers=args.workers)as pool:
        fs=[pool.submit(verify_job if args.verify else build_job,arg)for arg in todo]
        for future in as_completed(fs):
            r=future.result();results.append(r)
            if not args.verify:
                fn=dest/f"{r['id']:04d}.json.gz"
                temporary=fn.with_suffix(fn.suffix+'.tmp')
                with gzip.open(temporary,'wt')as f:json.dump(r,f,separators=(',',':'),allow_nan=False)
                temporary.replace(fn)
            if len(results)%50==0 or r.get('failures'):
                print(json.dumps(dict(done=len(results),id=r['id'],maximum=r['maximum']/S,
                    failures=len(r.get('failures',[])),seconds=round(time.time()-start,1))),flush=True)
    results.sort(key=lambda r:r['id']);complete=[r['id']for r in results]==list(range(len(roots)))
    summary=dict(date=datetime.now(timezone.utc).date().isoformat(),target=args.L,scope='Complete inherited inside source cover with regenerated core/far or independently checked repair leaves',
                 verified=args.verify,complete_source_enumeration=complete,source_roots=len(results),
                 maximum=max((r['maximum']for r in results),default=-1)/S,
                 maximum_numerator=max((r['maximum']for r in results),default=-1),scale=S,
                 source_sha256=hashlib.sha256(SOURCE.read_bytes()).hexdigest(),seconds=time.time()-start)
    if args.verify:
        commitments_after=verification_commitments()
        assert commitments_before==commitments_after,'Proof code or dynamic source rows changed during replay'
        summary.update(all_pass=complete,leaves=sum(r['leaves']for r in results),
                       branches=sum(r['branches']for r in results),checks=sum(r['checks']for r in results),
                       source_input_checks=source_checks,
                       certificate_corpus_sha256=digest_rows((r['id'],r['root_sha256'])for r in results),
                       corpus_hash_rule=CANONICAL_RULE,
                       commitments_before=commitments_before,commitments_after=commitments_after,
                       commitments_unchanged=True)
    else:
        failures=[dict(id=r['id'],**f)for r in results for f in r['failures']]
        summary.update(all_pass=complete and not failures,failed_roots=sum(not r['all_pass']for r in results),
                       failed_leaves=len(failures),reused_4_30=sum(r['reused_4_30']for r in results),
                       kinds={k:sum(r['kinds'].get(k,0)for r in results)for k in ('core','far','repair')},failures=failures)
    (dest/('verification.json'if args.verify else 'summary.json')).write_text(json.dumps(summary,indent=2,allow_nan=False)+'\n')
    print(json.dumps({k:v for k,v in summary.items()if k!='failures'}),flush=True)
if __name__=='__main__':main()
