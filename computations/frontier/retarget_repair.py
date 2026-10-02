"""Reuse an earlier repair as a proposal plan at a different exponent.

Only source/identity subdivisions and analytic witnesses are retained. Every
L-dependent input and every numerical dual certificate is rebuilt. The existing
source-based verifier checks the resulting tree without trusting this proposer.
"""
from inside_repair import *


def far_proposals(previous):
    result=[previous]
    if previous!=CANDIDATE:result.append(CANDIDATE)
    return result


def retarget_branch(base,L,br,node):
    assert node['branch']==br
    if 'split' in node:
        assert set(node)=={'branch','split','children','maximum'} and len(node['children'])==2
        mid=Q(node['split']);assert Q(br['lo'])<mid<Q(br['hi'])
        a=retarget_branch(base,L,dict(br,hi=str(mid)),node['children'][0])
        b=retarget_branch(base,L,dict(br,lo=str(mid)),node['children'][1])
        return dict(branch=br,split=str(mid),children=[a,b],maximum=max(a['maximum'],b['maximum']))
    keys={'branch','parameters','input','certificate','maximum'}
    if 'far_parameters' in node:keys.add('far_parameters')
    assert set(node)==keys
    par=node['parameters'];den=node['input']['lambda_den']
    last=None
    for d in sorted({den,min(2*den,2000)}):
        for fp in far_proposals(node.get('far_parameters')):
            if fp is not None:
                from inside_far import make_inside_far_input
                inp=make_inside_far_input(base,L,br,par,d,fp)
            else:inp=make_inside_input(base,L,br,par,d)
            try:
                cc=cert_block(inp,target=Q('.999999'),width=4);rep=verify_block(inp,cc)
                result=dict(branch=br,parameters=par,input=input_summary(inp),certificate=cc,maximum=rep['maximum'])
                if fp is not None:result['far_parameters']=copy.deepcopy(fp)
                return result
            except RuntimeError as exc:last=exc
    raise last


def retarget_plan(sp,L,sourcepar,node):
    if 'complex_location' in node:
        from inside_complex_rows import regenerate_complex_row,complex_update
        row=node['complex_location'];assert regenerate_complex_row(row)==row
        new=complex_update(sp,row)
        if new is None:return dict(complex_location=row,excluded=True,maximum=-1)
        assert set(node)=={'complex_location','child','maximum'}
        child=retarget_plan(new,L,sourcepar,node['child'])
        return dict(complex_location=row,child=child,maximum=child.get('maximum',-1))
    if 'real_location' in node:
        row=node['real_location'];assert regenerate_location_row(row)==row
        new=real_update(sp,row)
        if new is None:return dict(real_location=row,excluded=True,maximum=-1)
        assert set(node)=={'real_location','child','maximum'}
        child=retarget_plan(new,L,sourcepar,node['child'])
        return dict(real_location=row,child=child,maximum=child.get('maximum',-1))
    if 'second_exclusion' in node:
        red,proof=reduced_spec(sp);assert red is None and proof==node['second_exclusion']
        return copy.deepcopy(node)
    if 'split' in node:
        assert set(node)=={'split','mid','children','maximum'} and len(node['children'])==2
        ss=split_new(sp,node['split'],node['mid'])
        children=[retarget_plan(s,L,sourcepar,n) for s,n in zip(ss,node['children'])]
        return dict(split=node['split'],mid=node['mid'],children=children,
                    maximum=max(ch.get('maximum',-1) for ch in children))
    if 'core' in node or 'far' in node:
        kind='far' if 'far' in node else 'core';assert set(node)=={kind,'maximum'}
        rec=node[kind];par=rec['parameters']
        den=rec['lambda_den'] if kind=='far' else rec['input']['lambda_den']
        last=None
        for d in sorted({den,min(2*den,2000)}):
            original=make_endgame(sp,L,par,d);assert original is not None
            for fp in far_proposals(rec.get('far_parameters')):
                inp=original if fp is None else replace_far(original,fp)
                try:
                    cc=solve(inp,target=Q('.999999'),accept=Q('.999999'),min_width=4)
                    rep=verify_core(dict(input=inp,certificate=cc))
                    if fp is not None:
                        record=dict(parameters=par,lambda_den=d,far_parameters=copy.deepcopy(fp),
                                    input_sha256=input_digest(inp),certificate=compact_certificate(cc))
                        return dict(far=record,maximum=rep['maximum'])
                    return dict(core=dict(parameters=par,input=input_summary(inp),certificate=compact_certificate(cc)),maximum=rep['maximum'])
                except CannotCertify as exc:last=exc
        raise last
    assert set(node)=={'identities','maximum'}
    par0=dict(sourcepar)
    if par0['method']=='pair':par0=dict(SINGLE_PAR)
    base=make_endgame(sp,'4.33',par0,200);plan=roots(base)
    assert len(plan)==len(node['identities'])
    # The unhidden case is often the cheap obstruction. Fail before rebuilding
    # expensive hidden branches, but preserve the verifier's required order.
    trees=[None]*len(plan)
    for j in sorted(range(len(plan)),key=lambda j:plan[j]['identity']!='unhidden'):
        trees[j]=retarget_branch(base,L,plan[j],node['identities'][j])
    return dict(identities=trees,maximum=max(t['maximum'] for t in trees))
