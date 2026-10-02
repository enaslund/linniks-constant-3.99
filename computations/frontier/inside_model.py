"""General inside-buffer identity cover using retained separated near blocks.

Numerical implication only. The existing analytic near-block premises are imported.
The only model extension here builds the same-reserved family's local grid separately
when the ordinary third-family cutoff lies above its allowed local lower bound.
"""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'near' / 'code'))
from separated_blocks import *
from compact_records import regenerate_record
from refine_probe import spec_from_input

PAR = dict(method='mixture', gg='1.7504', gz='1.09006', mix='.1385', zeta='3')

def roots(base):
    lo = max(Q(base['case']['source_l2']), Q(base['case']['lo']))
    hi = Q(base['ordinary_lower'])
    ans = []
    if lo < hi:
        for ng in (1, 2):
            ans.append(dict(lo=str(lo), hi=str(hi), ng=ng, real=ng == 1, identity='distinct'))
            if base.get('second') and base['second']['n'] == ng:
                ans.append(dict(lo=str(lo), hi=str(hi), ng=ng, real=ng == 1, identity='same_reserved'))
    ans.append(dict(lo=str(max(lo, hi)), hi='infinity', ng=0, real=False, identity='unhidden'))
    return ans

def make_inside_input(base, L, br, par=PAR, den=200):
    # Keep the original implementation byte-for-byte when its grid condition holds.
    if br['identity'] == 'unhidden':
        inp = input_for(base, L, br, par, den); inp['hidden_rows'] = []; return inp
    if Q(base['rows'][0][0]) == Q(base['ordinary_lower']):
        return make_block_input(base, L, br, par, den)
    inp = input_for(base, L, br, par, den)
    sec = inp['second']; w = wgt(L); r = Q(base['ordinary_lower'])
    ng, real = br['ng'], br['real']
    if br['identity'] == 'same_reserved':
        inp['first'] -= sec['contribution']
        restored = sec['n'] * lower(w.w(Q(sec['hi'])))
        inp['far_budget'] += restored
        inp['same_family_adjustment'] = dict(removed_objective=sec['contribution'], restored_far=restored)
    K = int((1 + ETA) * S); D = inp['D']; m = 2 if real else 1
    assert K > 0 and (m + 1) * D - m * K > 0
    inp['separated_block'] = dict(K=K, D=D, global_centers=m, characters=ng,
        anchor=str(r), matrix_minimum=(m + 1) * D - m * K)
    # Distinct hidden family's local representative is among ordinary families and
    # may retain their lambda3 restriction. A same-reserved representative cannot.
    start = r if br['identity'] == 'same_reserved' else Q(inp['rows'][0][0])
    end = max(Q(3), r); grid = [start]
    edge = math.floor(start * den) + 1
    while Q(edge, den) < end:
        grid.append(Q(edge, den)); edge += 1
    if grid[-1] != end: grid.append(end)
    gg, gz, mix, shift = Q(par['gg']), Q(par['gz']), Q(par['mix']), Q(inp['shift'])
    Ba = w.B(r, real)
    hh = []
    for a, b in zip(grid, grid[1:]):
        hh.append([str(a), str(b), lower(w.w(b)), upper(iv.exp(-w.A * I(a)) * Ba),
                   mixfeature(gg, gz, shift, mix, b, real), S])
    hh.append([str(end), 'infinity', S, upper(iv.exp(-w.A * I(end)) * Ba * w.winv(end)),
               -S, lower(w.winv(end))])
    inp['hidden_rows'] = hh
    inp['hidden_grid_rule'] = 'same-reserved starts at local anchor; distinct retains ordinary cutoff'
    return inp

def inherited_leaves(sp, node, path=''):
    if 'split' in node:
        left, right = split_new(sp, node['split'], node['mid'])
        yield from inherited_leaves(left, node['children'][0], path + '0')
        yield from inherited_leaves(right, node['children'][1], path + '1')
    elif 'record' in node:
        yield path, sp, node['record']


def sample_block(inp, nt=31):
    # Floating threshold sampling is a diagnostic, never a certificate.
    end = threshold_end(inp); best = dict(value=-1.)
    for tau in sorted(set(round(j * end / (nt - 1)) for j in range(nt))):
        row = proposal_block(inp, tau, tau)
        if 'upper' in row and row['upper'] / S > best['value']:
            best = dict(value=row['upper'] / S, tau=tau / TS, dual={k:row[k] for k in ('Y', 'Z', 'U')})
    return best
