"""A common-anchor envelope applied to disjoint finite ordinary cohorts.

Each fixed convex combination of the old individual envelope and the new
affine collective envelope gives an ordinary linear objective. Existing exact
core dual checks apply after these changed inputs have been regenerated.
This standalone component verifier is not yet part of a global cover verifier.
"""
import copy
from far_enclosures import make_endgame, replace_far, parse_params, Q, S, I, upper
from base_enclosures import iv
from config_v4 import T
from collective_enclosures import tangent
from compact_records import input_digest, expand_certificate
from verify_progress import scenario


COHORT_KEYS = {'lo', 'hi', 'gamma', 'n0', 'blend', 'error', 'steps'}


def apply_collective(inp, cohorts):
    assert 'collective_envelope' not in inp
    assert not any(k in inp for k in ('hidden_rows', 'shadow', 'separated_block', 'kernel_parameters'))
    assert inp['column_model'] == 'two-test-published-single-far'
    assert inp['case'] is not None
    assert type(cohorts) is list and cohorts
    out = copy.deepcopy(inp)
    shift = Q(inp['case']['lo'])
    used = set()
    constants = 0
    reports = []
    for cohort in cohorts:
        assert set(cohort) == COHORT_KEYS
        lo, hi, blend = map(Q, (cohort['lo'], cohort['hi'], cohort['blend']))
        assert 0 < lo < hi and 0 <= blend < 1
        indices = [j for j, row in enumerate(inp['rows'])
                   if row[1] != 'infinity' and lo <= Q(row[0]) < Q(row[1]) <= hi]
        assert indices and not used.intersection(indices)
        used.update(indices)
        bound = tangent(str(lo), str(shift), cohort['gamma'], cohort['n0'], inp['L'],
                        cohort['error'], cohort['steps'])
        weight = 1-blend
        constant = -((-weight*bound['intercept']).__floor__())
        constants += constant
        for j in indices:
            # Weight this character by exp(-A*(bin_left-anchor)) in the
            # common-detector Gram sum. Its square is no larger than itself.
            decay = iv.exp(-I((Q(inp['L'])-2*T)*(Q(inp['rows'][j][0])-lo)))
            slope = upper(decay*I(Q(bound['slope'], S)))
            cost = blend*inp['rows'][j][3]+weight*slope
            out['rows'][j][3] = -((-cost).__floor__())
        reports.append(dict(parameters=copy.deepcopy(cohort), bound=bound,
                            indices=indices, fixed_cost=constant))
    out['first'] += constants
    out['first_bounds'] = {k: v+constants for k, v in inp['first_bounds'].items()}
    out['collective_envelope'] = dict(shift=str(shift), cohorts=reports, fixed_cost=constants,
        rule='Disjoint finite height-one cohorts; exponential bin weights; common-center Gram; fixed convex envelope combination')
    return out


def make_collective(sp, L, parameters, den, far_parameters, cohorts):
    assert type(parameters) is dict and set(parameters) == {'method', 'gg', 'gz', 'mix', 'zeta'}
    assert parse_params({'extension': dict(variant=parameters['method'],
        gG=parameters['gg'], gZ=parameters['gz'], mix=parameters['mix'],
        zeta=parameters['zeta'])}) == parameters
    assert type(den) is int and 50 <= den <= 10000
    inp = make_endgame(sp, L, parameters, den)
    assert inp is not None
    if far_parameters is not None:
        inp = replace_far(inp, far_parameters)
    return apply_collective(inp, cohorts)


def verify_record(sp, L, record):
    assert set(record) == {'parameters', 'lambda_den', 'far_parameters', 'cohorts',
                           'input_sha256', 'certificate'}
    inp = make_collective(sp, L, record['parameters'], record['lambda_den'],
                          record['far_parameters'], record['cohorts'])
    assert input_digest(inp) == record['input_sha256']
    return scenario(dict(input=inp, certificate=expand_certificate(record['certificate'], inp)))
