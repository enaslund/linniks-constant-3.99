"""Recheck the inherited small-real-exceptional and large-first-zero components.
Does not address the middle inside-buffer first-zero regime.
"""
from setup_local import *
from small_exception_399 import check as check_small
from verify_published_single import scenario as check_large
import time
if __name__=='__main__':
 t=time.time();rec=json.loads((ROOT/'results/large_branch_3.99.json').read_text())
 large=check_large(rec,None,'3.99',True);small=check_small()
 report=dict(status='PASS inherited exterior-component numerical implications, not full Linnik exponent',L='3.99',large=large,small=small,seconds=time.time()-t)
 (PROJECT/'results/exterior_399_verified.json').write_text(json.dumps(report,indent=2));print('PASS',large['maximum'],time.time()-t)
