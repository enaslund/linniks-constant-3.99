"""Fail-closed tests of the NEW numerical certificate paths, without optimization."""
import copy,gzip,json,subprocess,sys,time
from pathlib import Path
import adaptive_local_blocks as al
import outside_regime as out
from setup_local import PROJECT
from certificate_io import expand_local_tree,expand_outside_tree,load_outside,validate_outside_records


def rejected(name,call):
    try:call()
    except (AssertionError,ValueError,KeyError,TypeError,RuntimeError):return name
    raise AssertionError('corruption was accepted: '+name)

def leaf(tree):
    while 'children' in tree:tree=tree['children'][0]
    return tree

def main():
    t=time.time();done=[]
    base=al.base_for(0,8)
    with gzip.open(PROJECT/'results/local_split_4.20_8_0.json.gz','rt')as f:r=json.load(f)
    compact=r['trees'][0]
    bad=copy.deepcopy(compact);leaf(bad)['record']['input']['sha256']='0'*64
    done.append(rejected('tampered compact input hash',lambda:al.verify_tree(base,'4.20',al.roots_for(base)[0],bad)))
    bad=copy.deepcopy(compact);leaf(bad)['record']['input']['parameters']['mix']='.9'
    done.append(rejected('tampered compact parameters',lambda:al.verify_tree(base,'4.20',al.roots_for(base)[0],bad)))
    bad=copy.deepcopy(compact);leaf(bad)['record']['input']['lambda_den']=201
    done.append(rejected('tampered compact grid denominator',lambda:al.verify_tree(base,'4.20',al.roots_for(base)[0],bad)))
    compact_out=load_outside('4.30')
    done.append(rejected('missing compact source record',lambda:validate_outside_records(compact_out[:-1],'4.30')))
    done.append(rejected('reordered compact source records',lambda:validate_outside_records(compact_out[::-1],'4.30')))
    done.append(rejected('duplicated compact source record',lambda:validate_outside_records(compact_out+[compact_out[0]],'4.30')))
    tr=expand_local_tree(base,'4.20',compact);bad=copy.deepcopy(tr);bad['branch']['ng']=2
    done.append(rejected('wrong hidden-family cardinality',lambda:al.verify_tree(base,'4.20',al.roots_for(base)[0],bad)))
    inp=leaf(tr)['record']['input'];cc=leaf(tr)['record']['certificate'];al.verify_block(inp,cc)
    bad=copy.deepcopy(cc);bad.pop(0)
    done.append(rejected('missing threshold beginning',lambda:al.verify_block(inp,bad)))
    bad=copy.deepcopy(cc);bad.pop()
    done.append(rejected('missing threshold tail',lambda:al.verify_block(inp,bad)))
    bad=copy.deepcopy(cc);b=next(x for x in bad if not x.get('excluded'));b['Y']=b['Z']=b['U']=0
    done.append(rejected('zeroed dual certificate',lambda:al.verify_block(inp,bad)))
    bad=copy.deepcopy(tr);leaf(bad)['record']['input']['shadow']['v_global']+=10**10
    done.append(rejected('inflated hidden-global feature',lambda:al.verify_tree(base,'4.20',al.roots_for(base)[0],bad)))
    bad=copy.deepcopy(tr);leaf(bad)['record']['input']['hidden_rows'].pop()
    done.append(rejected('deleted infinite hidden-local tail',lambda:al.verify_tree(base,'4.20',al.roots_for(base)[0],bad)))
    bad=copy.deepcopy(tr);leaf(bad)['record']['input']['hidden_rows'][0][3]=float('nan')
    done.append(rejected('NaN objective enclosure',lambda:al.verify_tree(base,'4.20',al.roots_for(base)[0],bad)))
    r=next(r for r in load_outside('4.30')if r['id']==1492)
    sp=out.with_height(out.specs()[1492],'outside');rt=expand_outside_tree(sp,'4.30',r['outside_buffer'])
    bad=copy.deepcopy(rt);leaf(bad)['buffered_first']['input']['far_budget']-=10**15
    done.append(rejected('unjustified extra far subtraction',lambda:out.verify_tree(sp,bad,'4.30')))
    bad=copy.deepcopy(rt);leaf(bad)['buffered_first']['input']['first_block']['global_centers']=2
    done.append(rejected('incorrect first-family center multiplicity',lambda:out.verify_tree(sp,bad,'4.30')))
    q=subprocess.run([sys.executable,'-O','-c','import setup_local'],cwd=PROJECT/'code',capture_output=True,text=True)
    assert q.returncode!=0 and 'requires Python assertions enabled' in q.stderr
    done.append('disabled-assertion invocation')
    result=dict(status='PASS all deliberate corruptions rejected',count=len(done),tests=done,seconds=time.time()-t)
    (PROJECT/'results/corruption_tests.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
if __name__=='__main__':main()
