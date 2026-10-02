"""Install checked leaves from a bounded pilot, preserving every source split.

The packed source corpus is untouched. A record is usable only against its
exact committed source root; each accepted path and numerical witness is
regenerated before an atomic loose overlay is written. Partial improvements
retain all unresolved scopes. This does not replace a complete corpus replay.
"""
import argparse,copy,gzip,hashlib,json,time
from concurrent.futures import ProcessPoolExecutor,as_completed
from far_full import HERE,load_root,load_roots,root_digest,specs,with_height,split_new,verify_tree_new,counts
from far_storage import digest_rows,CANONICAL_RULE


def unresolved_sources(root):
    """Derive unresolved paths from the actual tree, not its failure summary."""
    found={}
    def visit(sp,node,path):
        if 'split'in node:
            assert set(node)=={'split','mid','children'}and len(node['children'])==2
            children=split_new(sp,node['split'],node['mid'])
            for digit,(child,scope)in enumerate(zip(node['children'],children)):
                visit(scope,child,path+str(digit))
        elif 'unresolved'in node:
            assert set(node)=={'unresolved'}
            failure=node['unresolved']
            assert failure['path']==path and failure['spec']==sp and path not in found
            found[path]=(sp,failure)
    visit(with_height(specs()[root['id']],'inside'),root['inside'],'')
    assert root['failures']==[failure for _,failure in found.values()]
    assert root['all_pass']==(not found)
    return found


def checked_overlay(root,record):
    assert record['id']==root['id']and record['L']==root['target']
    assert record['source_root_sha256']==root_digest(root),'Source root changed since the pilot'
    sources=unresolved_sources(root);attempts=record['attempts'];seen=set();replacements={};reports=[]
    assert record['source_failed_leaves']==len(sources)
    assert record['attempted_leaves']==len(attempts)
    for attempt in attempts:
        path=attempt['path'];assert path in sources and path not in seen;seen.add(path)
        sp,failure=sources[path]
        assert attempt['spec']==sp and attempt['parameters']==failure['parameters']
        assert type(attempt['passed'])is bool
        if not attempt['passed']:continue
        wrapper=attempt['node'];assert set(wrapper)=={'repair'}
        repair=wrapper['repair'];assert set(repair)=={'L','parameters','tree'}
        assert repair['L']==record['L']and repair['parameters']==failure['parameters']
        checked=verify_tree_new(sp,wrapper,record['L'])
        maximum=max((r['maximum']for r in checked),default=-1)
        assert maximum==attempt['maximum']==repair['tree'].get('maximum',-1)
        assert attempt['intervals']==sum(r['branches']for r in checked)
        assert attempt['checks']==sum(r['checks']for r in checked)
        replacements[path]=wrapper;reports.extend(checked)
    assert record['repaired_leaves']==len(replacements)
    assert record['all_original_failures_repaired']==(len(replacements)==len(sources))
    def replace(node,path):
        if path in replacements:return copy.deepcopy(replacements[path])
        if 'split'in node:
            return dict(split=node['split'],mid=node['mid'],
                        children=[replace(child,path+str(i))for i,child in enumerate(node['children'])])
        return copy.deepcopy(node)
    tree=replace(root['inside'],'');remaining=[f for path,(_,f)in sources.items()if path not in replacements]
    scope=counts(tree)
    result=dict(root,inside=tree,failures=remaining,all_pass=not remaining,
                maximum=max((r['maximum']for r in scope),default=-1),
                kinds={k:sum(r['kind']==k for r in scope)for k in ('core','far','repair')},
                reused_4_30=sum(r['L']=='4.30'for r in scope))
    assert list(unresolved_sources(result))==[p for p in sources if p not in replacements]
    report=dict(id=root['id'],L=record['L'],source_root_sha256=root_digest(root),
                result_root_sha256=root_digest(result),repaired_leaves=len(replacements),
                repaired_paths=sorted(replacements),remaining_leaves=len(remaining),all_pass=not remaining,
                intervals=sum(r['branches']for r in reports),checks=sum(r['checks']for r in reports))
    return result,report


def integrate_file(path,install=False):
    start=time.time()
    with gzip.open(path,'rt')as stream:record=json.load(stream)
    root=load_root(record['id'],record['L']);result,report=checked_overlay(root,record)
    report.update(record_file=str(path.relative_to(HERE)),installed=False)
    if install and report['repaired_leaves']:
        # Reject a concurrent writer even after the potentially long replay.
        assert root_digest(load_root(root['id'],record['L']))==report['source_root_sha256']
        dest=HERE/f"far_full_{record['L']}"/f"{root['id']:04d}.json.gz";tmp=dest.with_suffix('.integrating.tmp')
        with gzip.open(tmp,'wt')as stream:json.dump(result,stream,separators=(',',':'),allow_nan=False)
        tmp.replace(dest);report['installed']=True
        assert root_digest(load_root(root['id'],record['L']))==report['result_root_sha256']
    report['seconds']=time.time()-start
    return report


def save_pending(destination,L='4.30'):
    """Commit current unresolved scopes without treating them as obstructions."""
    roots=load_roots(L);pending=[];digests=[]
    for root in roots:
        digest=root_digest(root);digests.append((root['id'],digest))
        for path,(sp,failure)in unresolved_sources(root).items():
            pending.append(dict(id=root['id'],path=path,source_root_sha256=digest,spec=sp,
                                parameters=failure['parameters'],lambda_den=failure['lambda_den']))
    report=dict(L=L,source_roots=len(roots),completed_roots=sum(r['all_pass']for r in roots),
                pending_roots=len({r['id']for r in pending}),pending_leaves=len(pending),
                current_corpus_sha256=digest_rows(digests),corpus_hash_rule=CANONICAL_RULE,
                scope='Unresolved source scopes; search failures do not prove a mathematical obstruction')
    transport=json.loads((HERE/f'far_full_{L}/transport.json').read_text())
    packed=HERE/transport['packed_file']
    assert hashlib.sha256(packed.read_bytes()).hexdigest()==transport['packed_sha256']
    report.update(frozen_scan_corpus_sha256=transport['canonical_corpus_sha256'],
                  frozen_scan_packed_sha256=transport['packed_sha256'])
    with gzip.open(destination,'wt')as stream:json.dump(dict(report,scopes=pending),stream,separators=(',',':'),allow_nan=False)
    return report


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--directory',default='far_repair_pilot_4.30')
    ap.add_argument('--ids',default='');ap.add_argument('--install',action='store_true')
    ap.add_argument('--workers',type=int,default=1)
    a=ap.parse_args();directory=HERE/a.directory;wanted=set(map(int,a.ids.split(',')))if a.ids else None
    assert a.workers>0
    destination=directory/('integration.json'if a.install else 'integration_check.json')
    assert not destination.exists(),'Keep previous integration evidence; select a fresh output directory or combine reports explicitly'
    files=[p for p in sorted(directory.glob('[0-9]*.json.gz'))if wanted is None or int(p.name.split('.')[0])in wanted]
    assert files
    ids=[int(path.name.split('.')[0])for path in files]
    assert len(set(ids))==len(ids)and all(path.name==f'{idx:04d}.json.gz'for path,idx in zip(files,ids))
    output=[]
    with ProcessPoolExecutor(max_workers=a.workers)as pool:
        for future in as_completed([pool.submit(integrate_file,path,a.install)for path in files]):
            report=future.result();output.append(report);print(json.dumps(report),flush=True)
    output.sort(key=lambda r:r['id'])
    summary=dict(records=len(output),installed_roots=sum(r['installed']for r in output),
                 repaired_leaves=sum(r['repaired_leaves']for r in output),
                 completed_roots=sum(r['all_pass']for r in output),reports=output,
                 scope='Source-matched component integration; complete fresh corpus replay still required')
    if a.install:
        assert len({r['L']for r in output})==1
        summary['pending']=save_pending(directory/'pending.json.gz',output[0]['L'])
    destination.write_text(json.dumps(summary,indent=2,allow_nan=False)+'\n')
    print(json.dumps({k:v for k,v in summary.items()if k!='reports'}),flush=True)


if __name__=='__main__':main()
