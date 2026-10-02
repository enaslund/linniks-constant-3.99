"""Re-evaluate retained complex-second inequalities on the actual first cell.

The four retained parameter tuples and one nearby optimized tuple are tried.
The search proposes a rational second-family bound; acceptance recomputes both
zero-type inequalities and both all-height principal-alias bounds in poly_rows.
"""
from inside_model import *
from poly_rows import applicable_polynomials, polynomial_table, complex_second_row, coefficients


def regenerate_complex_row(row):
    assert all(Q(row[k]) > 0 for k in ('gamma', 't', 'real_gamma', 'real_t'))
    return complex_second_row(row['a'], row['b'], row['h'], row['gamma'], row['t'],
                              row['real_gamma'], row['real_t'])


@lru_cache(None)
def propose_complex_row(a, b):
    a, b = Q(a), Q(b)
    accepted = []
    applicable=[source['proof'] for source in applicable_polynomials(a,b) if source['type']=='second']
    templates=applicable+[source['proof'] for source in polynomial_table()['rows'] if source['type']=='second']
    # This fixed proposal comes from inside_complex_optimized.json. It carries
    # no row assertion; every accepted first cell is enclosed again below.
    templates.append(dict(gamma='1.266166',t='.922751',real_gamma='1.1',real_t='.85'))
    seen=set()
    for p in templates:
        key=tuple(Q(p[k]) for k in ('gamma','t','real_gamma','real_t'))
        if key in seen:continue
        seen.add(key)
        g, t, gr, tr = [Q(p[k]) for k in ('gamma', 't', 'real_gamma', 'real_t')]
        f, fr = test(g), test(gr)
        c1, c2 = coefficients(t); r1, r2 = coefficients(tr)

        def positive(h):
            generic = lower((I(c1)*(f.F(b-a)+f.F(h-a))-f.F(-a))/f.f0
                            - I(((1+c1+c2)**2-1)/6))
            real = lower((I(r1)*fr.F(b-a)+fr.F(h-a)-fr.F(-a))/fr.f0
                         - I(Q(1,8)+(r1+r2)/3))
            return generic > 0 and real > 0

        # The formula is evaluated anew, so a template's old first-cell domain
        # does not restrict the new one. Its parameter tuple carries no bound.
        baseline=max(b,Q(p['h'])) if p in applicable else b
        lo = math.ceil(baseline*10000)
        hi = math.floor(max(baseline+Q('.03'),b+Q('.08'))*10000)
        if not positive(Q(lo, 10000)): continue
        while lo < hi:
            mid = (lo+hi+1)//2
            if positive(Q(mid, 10000)): lo = mid
            else: hi = mid-1
        # Scalar positivity is only a proposal. The all-height alias checks are
        # independently regenerated before a row can enter a certificate tree.
        for tick in range(lo, max(lo-4, math.floor(baseline*10000)), -1):
            h = Q(tick, 10000)
            try:
                row = complex_second_row(a, b, h, g, t, gr, tr)
            except AssertionError:
                continue
            accepted.append(row); break
    return max(accepted, key=lambda row: Q(row['h']), default=None)


def complex_update(spec, row):
    assert spec['case']['kind'] == 'complex'
    assert Q(row['a']) <= Q(spec['case']['lo']) <= Q(spec['case']['hi']) <= Q(row['b'])
    h = Q(row['h']); out = copy.deepcopy(spec)
    if out.get('second') and Q(out['second']['hi']) <= h: return None
    out['case']['source_l2'] = str(max(Q(out['case']['source_l2']), h))
    out['ordinary_lower'] = str(max(Q(out['ordinary_lower']), h))
    if out.get('second'): out['second']['lo'] = out['ordinary_lower']
    return out
