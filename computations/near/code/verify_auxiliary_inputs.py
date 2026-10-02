"""Regenerate the inherited elementary source-interface tables.
Published analytic implications and original source tables remain premises.
"""
from setup_local import *
import time,hashlib
from endgame import validate_source_cover,location_proof
from poly_rows import verify_polynomial_table
from alias_check import check as alias_check
if __name__=='__main__':
 t=time.time();_,cover=validate_source_cover();p=verify_polynomial_table();a=alias_check();l=location_proof()
 out=dict(status='PASS inherited elementary polynomial/alias enclosures and source-case cover',source_cover=cover,polynomials=p,alias=a,real_first_second_exclusion=l,seconds=time.time()-t,scope='Does not recertify original published zero-location computations or formalize analytic deductions.')
 (PROJECT/'results/auxiliary_regeneration.json').write_text(json.dumps(out,indent=2));print('PASS auxiliary',time.time()-t,flush=True)
