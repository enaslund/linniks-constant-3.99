"""Regenerate and check the fixed relaxed feasible point without optimization.
This is NOT a possible configuration of actual Dirichlet zeros or a bound from below
for Linnik's exponent. Its significance is limited to the specified relaxation.
"""
from adaptive_local_blocks import base_for, make_block_input, PAR, PROJECT, Q, S, TS, near_block
import json
from certificate_io import check_input

def verify():
    rec=json.loads((PROJECT/'results/relaxation_at_four.json').read_text())
    base=base_for(7,8)
    expected=dict(lo='37/50',hi='297/400',ng=2,real=False,identity='distinct')
    assert rec['L']=='4.00' and rec['base']==base and rec['global_branch']==expected and rec['parameters']==PAR
    inp=make_block_input(base,'4.00',expected,PAR,400)
    check_input(inp,rec['input']);tau=Q(rec['tau'])*TS;assert tau.denominator==1
    C,CH,B=near_block(inp,int(tau),int(tau));cost=[Q(0),Q(0),Q(0)];objective=Q(inp['first']+inp['final'],S)
    seen=set()
    for pt in rec['points']:
        assert pt['kind'] in ('ordinary','hidden_local')
        assert isinstance(pt['numerator'],int) and isinstance(pt['denominator'],int) and pt['numerator']>=0 and pt['denominator']>0
        key=(pt['kind'],tuple(pt['bin']));assert key not in seen;seen.add(key)
        rr=inp['rows'] if pt['kind']=='ordinary' else inp['hidden_rows']
        cc=C if pt['kind']=='ordinary' else CH
        ind=[j for j,r in enumerate(rr) if r[:2]==pt['bin']];assert len(ind)==1;j=ind[0];r=rr[j]
        mass=Q(pt['numerator'],pt['denominator']);nc=0 if pt['kind']=='ordinary' else r[5]
        cost[0]+=mass*Q(r[2],S);cost[1]+=mass*Q(cc[j],S);cost[2]+=mass*Q(nc,S)
        objective+=mass*Q(r[3],S)
    budgets=[Q(inp['far_budget'],S),Q(B,S),Q(inp['shadow']['ng'])]
    assert all(c<=b for c,b in zip(cost,budgets))
    assert objective==Q(rec['objective']) and objective>1
    report=dict(status='PASS exact feasible point in FIXED RELAXATION; not actual zeros',regenerated=True,L='4.00',objective=str(objective),slacks=[str(b-c)for b,c in zip(budgets,cost)])
    (PROJECT/'results/relaxation_at_four_verified.json').write_text(json.dumps(report,indent=2));return report
if __name__=='__main__':print(json.dumps(verify(),indent=2))
