import os
os.environ['OPENBLAS_NUM_THREADS']='1'
from build_progress import *
from published_single_inputs import make_large
from certify_v4 import solve_input
import certify_v4
from dual_fast import dual_bound
certify_v4.dual_bound=dual_bound
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--L',required=True);a=ap.parse_args();directory=ROOT/'results'/('records_'+a.L)
 paths=[directory/f'{i:04d}.json.gz' for i in range(2768)]
 assert all(p.exists() for p in paths),[i for i,p in enumerate(paths) if not p.exists()]
 dest=ROOT/'results'/f'certificate_{a.L}.jsonl.gz'
 with gzip.open(dest,'wt') as f:
  for i,p in enumerate(paths):
   with gzip.open(p,'rt') as g:rec=json.load(g)
   assert rec['id']==i and rec['L']==a.L
   f.write(json.dumps(rec,separators=(',',':'))+'\n')
 inp=make_large(a.L);large=dict(input=inp,certificate=solve_input(inp));(ROOT/'results'/f'large_{a.L}.json').write_text(json.dumps(large,separators=(',',':')))
 print('ASSEMBLED',dest,'bytes',dest.stat().st_size)
