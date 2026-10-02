"""Coherent eligible far-weight replacement for separated hidden-family models.

This numerical model adapter keeps the retained near blocks, all-zero envelopes,
and source/identity partition. No second far representative is introduced.
"""
from inside_model import *
from far_enclosures import far_weights, CANDIDATE


def replace_inside_far(inp, parameters=None):
    """Rebuild every far resource after the hidden identity has been fixed."""
    assert 'far_parameters' not in inp and 'kernel_parameters' not in inp
    assert inp['height'] == 'inside'
    identity = inp['identity']
    assert identity in ('distinct', 'same_reserved', 'unhidden')
    assert 'hidden_rows' in inp and 'shadow' in inp
    if identity == 'unhidden':
        assert not inp['hidden_rows'] and inp['shadow']['ng'] == 0
        assert 'same_family_adjustment' not in inp
    else:
        assert inp['hidden_rows'] and 'separated_block' in inp
        assert (identity == 'same_reserved') == ('same_family_adjustment' in inp)
    p = CANDIDATE if parameters is None else parameters
    f, prime = far_weights(p), wgt(inp['L'])
    decay = lower(prime.A - 2*f.x)
    assert lower(prime.A - 3) > 0 and decay > 0
    out = copy.deepcopy(inp)
    budget = upper((1 + I(ETA))*f.V)
    budget -= inp['n']*lower(f.w(Q(inp['case']['hi'])))
    sec = inp['second']
    if sec and identity != 'same_reserved':
        budget -= sec['n']*lower(f.w(Q(sec['hi'])))
    if identity == 'same_reserved':
        assert sec is not None and sec['n'] == inp['shadow']['ng']
        out['same_family_adjustment']['restored_far'] = sec['n']*lower(f.w(Q(sec['hi'])))
    for row in out['rows']:
        if row[1] == 'infinity':
            row[2] = S
            row[3] = upper(prime.G(Q(row[0]))*f.winv(Q(row[0])))
        else:
            row[2] = lower(f.w(Q(row[1])))
    if out['hidden_rows']:
        anchor = Q(inp['separated_block']['anchor'])
        envelope = prime.B(anchor, inp['shadow']['real'])
        for row in out['hidden_rows']:
            if row[1] == 'infinity':
                endpoint = Q(row[0])
                row[2] = S
                row[3] = upper(iv.exp(-prime.A*I(endpoint))*envelope*f.winv(endpoint))
                # The tail occupancy variable is normalized by its far weight.
                # Its character-count coefficient must change with that weight.
                row[5] = lower(f.winv(endpoint))
            else:
                row[2] = lower(f.w(Q(row[1])))
    out.update(far_budget=budget, far_parameters=copy.deepcopy(p), far_decay_margin=decay)
    return out


def make_inside_far_input(base, L, branch, parameters=PAR, den=200, far_parameters=None):
    return replace_inside_far(make_inside_input(base, L, branch, parameters, den), far_parameters)
