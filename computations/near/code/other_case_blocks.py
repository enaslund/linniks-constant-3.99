from separated_blocks import *
import argparse,time
ap=argparse.ArgumentParser();ap.add_argument('--L',default='4.25');ap.add_argument('--id',type=int,default=412);ap.add_argument('--step',default='.02');ap.add_argument('--den',type=int,default=200);ap.add_argument('--verify',action='store_true');aa=ap.parse_args()
items=load_data('selected_global_scan_inputs.json');item=next(r for r in items if r['id']==aa.id);base=item['input']
assert base is not None
par=dict(method='mixture',gg='1.7504',gz='1.09006',mix='.1385',zeta='3')
plan=scenarios(base,Q(aa.step));tt=time.time();reports=[];mx=-1;binding=None;fn=PROJECT/'results'/f'case_{aa.id}_local_{aa.L}.jsonl.gz'
if aa.verify:
 with gzip.open(fn,'rt')as f:records=[json.loads(l)for l in f]
 assert len(records)==len(plan)
else:out=gzip.open(fn,'wt')
for j,br in enumerate(plan):
 inp=make_block_input(base,aa.L,br,par,aa.den)
 if aa.verify:
  rec=records[j];assert rec['branch']==br;check_input(inp,rec['input']);cc=rec['certificate']
 else:
  cc=cert_block(inp);out.write(json.dumps(dict(branch=br,input=inp,certificate=cc),separators=(',',':'))+'\n');out.flush()
 rr=verify_block(inp,cc);reports.append(rr)
 if rr['maximum']>mx:mx=rr['maximum'];binding=dict(case=br,input=input_summary(inp),report=rr)
 print('CASE',j,'source',aa.id,br,rr['maximum']/S,'sec',time.time()-tt,flush=True)
if not aa.verify:out.close()
rep=dict(source_case=aa.id,L=aa.L,complete_global_second_cover=True,status='PASS only for one conditional configuration; NOT a global exponent',cases=len(plan),branches=sum(r['branches']for r in reports),checks=sum(r['checks']for r in reports),excluded=sum(r['excluded']for r in reports),maximum=mx,scale=S,margin=S-mx,binding=binding,seconds=time.time()-tt)
(PROJECT/'results'/f'case_{aa.id}_local_{aa.L}_report.json').write_text(json.dumps(rep,indent=2));print('DONE',mx/S,time.time()-tt,flush=True)
