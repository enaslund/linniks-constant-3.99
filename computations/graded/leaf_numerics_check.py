"""Exact reproduction of the graded leaves' stored integers from their numeric metadata.

Reads the JSON lines written by `graded_lean_export.py --numerics` and recomputes, from the metadata
alone, every stored integer of every leaf: per column G, W, C, NH, E; the far budget F; the first-family
charge `first`; `final`.  The functions are those of research/notes/leaf-data-semantics-2026-09-29.md
§1, evaluated with mpmath at 50 digits from closed forms derived here (not the builders' code):

  B_phi(lam) = H0^-1 [2 int_0^T psi(u) e^{-2 lam u} int_u^T psi  +  phi int_0^T psi^2 e^{-2 lam u}]
  h(lam)     = Psi(lam)^2 / H0,  Psi(lam) = int_0^T psi(t) e^{-lam t} dt
  C(p,a)     = (2/H0) int_0^T psi(u) e^{-2pu} int_u^T psi(v) e^{-a(v-u)} dv du       (cell sums)
  w(lam)^-1  = int_u^x e^{(2 lam - theta) t} sqrt(min(t-u, c2) + eps) dt            (erf/erfi)
  V          = 100/(c1 c2^2) sum_i alpha_i^2 int_u^x e^{theta t} min((t-u-ih)_+, h)/sqrt(min(t-u,c2)+eps) dt

At start, each closed form is compared with direct mpmath quadrature of its defining integral.  Rounding
follows the builders: floor(S x) for a lower bound (W, NH), ceil(S x) for an upper bound (G, the far
constant, the first-family charges), with J_old's inner ceiling ceil_S(B_t(a) - alpha h(a)).

Each recomputed integer is classified: exact; safe off-by-one (the stored integer is on the safe side and
differs by at most one per rounding whose S x lies within 1e-20 of an integer, where a 50-digit outward
enclosure may legitimately round the other way); or mismatch.  The report also gives the smallest
distance of any S x to an integer.  Structural checks confirm the column layout (bin grids, deletions, tails, hidden and
second-family grids) and the metadata's own consistency (n, alpha, phi, p, J_new) against the note.

  python3 computations/graded/leaf_numerics_check.py numerics_outside.jsonl.gz [--report out.json]
"""
import sys, json, gzip, math, argparse, time
from fractions import Fraction as Q
from functools import lru_cache
import mpmath
from mpmath import mp, mpf

DPS = 50
GUARD = 30          # extra digits inside the closed forms that cancel (Q0, the r-integrals)
mp.dps = DPS
S = 10**16
NEAR = mpf(10)**-20  # |S x - integer| below this: an outward 50-digit enclosure may round either way

# ------------------------------------------------------------------ constants (the note §1; config_v4)
T = Q('0.416829')
BETA = tuple(Q(x) for x in (
    '.02318741', '.07159337', '.12265085', '.17627704', '.23237155', '.29081583', '.35147264', '.41418551',
    '.47877833', '.54505502', '.61279917', '.68177389', '.75172165', '.82236428', '.89340300', '.96451862'))
KAPPA = T/16
ETA = Q(1, 10**6)
FINAL = 5*ETA
R_TAIL = Q(3)
_inh = tuple(Q(x) for x in ('.0788827218', '.0849386148', '.0895629779', '.0938231516', '.0979710491',
                             '.1021284916', '.1063732939', '.1107651869', '.1153565492'))
PROFILES = {
    'inherited': dict(c1=Q('.09035'), c2=Q('.235968'), theta=Q('1.28683'), eps=Q(1, 10**7),
                      alpha=_inh+(1-sum(_inh),)),
    'retuned': dict(c1=Q('0.0821922'), c2=Q('0.2170903'), theta=Q('1.4964274'), eps=Q(1, 10**7),
                    alpha=tuple(Q(x) for x in (
                        '0.0806195583', '0.0862705300', '0.0905489307', '0.0944644867', '0.0982543287',
                        '0.1020315591', '0.1058668825', '0.1098131140', '0.1139152197', '0.1182153903'))),
}
assert all(sum(p['alpha']) == 1 and len(p['alpha']) == 10 for p in PROFILES.values())
H0Q = (KAPPA*sum(BETA))**2             # H0 = Psi(0)^2 = (kappa sum beta)^2, an exact rational
SUFFIX = tuple(sum(BETA[i+1:], Q(0)) for i in range(16))


def M(x):
    """An exact rational as an mpf (one rounding)."""
    x = Q(x)
    return mpf(x.numerator)/x.denominator


# ------------------------------------------------------------------ kernel functions
def B(phi, lam):
    return _B(Q(phi), Q(lam))


@lru_cache(maxsize=None)
def _B(phi, lam):
    """B_phi(lam), lam > 0.  With E = e^{-2 kappa lam}, U = (1-E)/lam = int_0^kappa 2 e^{-2 lam s} ds and
    Q0 = 2 int_0^kappa (kappa-s) e^{-2 lam s} ds = (2 kappa lam - (1-E))/(2 lam^2):
    H0 B = sum_i E^i [beta_i^2 (Q0 + (phi/2) U) + kappa U beta_i sum_{j>i} beta_j]."""
    assert lam > 0
    with mp.workdps(DPS+GUARD):
        l = M(lam); em = mp.expm1(M(-2*KAPPA*lam))       # E - 1
        E = em+1; U = -em/l
        Q0 = (M(2*KAPPA*lam)+em)/(2*l*l)
        s = mpf(0); P = mpf(1)
        for i in range(16):
            s += P*(M(BETA[i]**2)*(Q0+M(phi/2)*U)+M(KAPPA*BETA[i]*SUFFIX[i])*U)
            P *= E
        out = s/M(H0Q)
    return +out


def Psi(lam):
    return _Psi(Q(lam))


@lru_cache(maxsize=None)
def _Psi(lam):
    assert lam > 0
    with mp.workdps(DPS+GUARD):
        e = mp.exp(M(-KAPPA*lam))
        s = mpf(0); P = mpf(1)
        for i in range(16):
            s += M(BETA[i])*P; P *= e
        out = s*(-mp.expm1(M(-KAPPA*lam)))/M(lam)
    return +out


def h(lam):
    return Psi(lam)**2/M(H0Q)


def expA(L, lam):
    """e^{-A lam}, A = L - 2T."""
    return mp.exp(M(-(Q(L)-2*T)*Q(lam)))


def Gphi(L, phi, lam):
    return expA(L, lam)*B(phi, lam)


def _cell_exp(r, j):
    """int_{j kappa}^{(j+1) kappa} e^{-r u} du."""
    r = Q(r)
    if r == 0:
        return M(KAPPA)
    return mp.exp(M(-r*j*KAPPA))*(-mp.expm1(M(-r*KAPPA)))/M(r)


def Cpa(p, a):
    return _Cpa(Q(p), Q(a))


@lru_cache(maxsize=None)
def _Cpa(p, a):
    """C(p,a) by cells: pairs of cells j < k give beta_j beta_k I(2p-a, j) I(a, k); a cell with itself
    gives beta_j^2 int_cell e^{-(2p-a)u} (e^{-au} - e^{-a(j+1)kappa})/a du."""
    assert p > 0 and a > 0
    with mp.workdps(DPS+GUARD):
        tot = mpf(0)
        Ia = [_cell_exp(a, k) for k in range(16)]
        for j in range(16):
            Ipa = _cell_exp(2*p-a, j)
            cross = sum((M(BETA[k])*Ia[k] for k in range(j+1, 16)), mpf(0))
            same = M(BETA[j])/M(a)*(_cell_exp(2*p, j)-mp.exp(M(-a*(j+1)*KAPPA))*Ipa)
            tot += M(BETA[j])*(same+cross*Ipa)
        out = 2*tot/M(H0Q)
    return +out


# ------------------------------------------------------------------ far weight
def _geom(prof):
    c1, c2 = prof['c1'], prof['c2']
    u = Q(1, 3)+2*c1
    return u, u+c2, Q(2, 3)+3*c1+c2


def _R0(a, r0sq, r1sq):
    """int_{r0}^{r1} e^{a r^2} dr (erf/erfi), a an exact rational; endpoints given by their squares."""
    r0, r1 = mp.sqrt(M(r0sq)), mp.sqrt(M(r1sq))
    if a == 0:
        return r1-r0
    sa = mp.sqrt(abs(M(a)))
    f = mp.erfi if a > 0 else mp.erf
    return mp.sqrt(mp.pi)/(2*sa)*(f(sa*r1)-f(sa*r0))


def _R2(a, r0sq, r1sq):
    """int_{r0}^{r1} r^2 e^{a r^2} dr = [r e^{a r^2}]/(2a) - R0/(2a); series near a = 0."""
    r0, r1 = mp.sqrt(M(r0sq)), mp.sqrt(M(r1sq))
    if abs(a) < Q(1, 1000):
        s = mpf(0); k = 0; term = mpf(1)
        while True:
            t = term*(r1**(2*k+3)-r0**(2*k+3))/(2*k+3)
            s += t
            if k > 3 and abs(t) < mpf(10)**(-(DPS+GUARD+5)):
                return s
            k += 1; term *= M(a)/k
    return ((r1*mp.exp(M(a*r1sq))-r0*mp.exp(M(a*r0sq)))-_R0(a, r0sq, r1sq))/(2*M(a))


def _Iexp(a, lo, hi):
    """int_lo^hi e^{a t} dt."""
    if a == 0:
        return M(hi-lo)
    return mp.exp(M(a*lo))*mp.expm1(M(a*(hi-lo)))/M(a)


def winv(pname, lam):
    return _winv(pname, Q(lam))


@lru_cache(maxsize=None)
def _winv(pname, lam):
    """w(lam)^-1 = 2 e^{a(u-eps)} int_{sqrt eps}^{sqrt(c2+eps)} r^2 e^{a r^2} dr + sqrt(c2+eps) int_v^x e^{at} dt,
    a = 2 lam - theta (substitution t = u - eps + r^2 on [u, v])."""
    prof = PROFILES[pname]
    u, v, x = _geom(prof)
    eps, c2 = prof['eps'], prof['c2']
    a = 2*lam-prof['theta']
    with mp.workdps(DPS+GUARD):
        out = (2*mp.exp(M(a*(u-eps)))*_R2(a, eps, c2+eps)+mp.sqrt(M(c2+eps))*_Iexp(a, v, x))
    return +out


def w(pname, lam):
    return 1/winv(pname, lam)


def _J(prof, i):
    """J_i = int_u^x e^{theta t} min((t-u-ih)_+, h)/sqrt(min(t-u, c2)+eps) dt, h = c2/10, by the
    substitution r^2 = t - u + eps on [u, v]."""
    u, v, x = _geom(prof)
    eps, c2, th = prof['eps'], prof['c2'], prof['theta']
    hh = c2/10; s = i*hh
    first = (_R2(th, s+eps, s+hh+eps)-M(s+eps)*_R0(th, s+eps, s+hh+eps)+M(hh)*_R0(th, s+hh+eps, c2+eps))
    return 2*mp.exp(M(th*(u-eps)))*first+M(hh)/mp.sqrt(M(c2+eps))*_Iexp(th, v, x)


@lru_cache(maxsize=None)
def V(pname):
    prof = PROFILES[pname]
    with mp.workdps(DPS+GUARD):
        out = M(Q(100)/(prof['c1']*prof['c2']**2))*sum(M(al**2)*_J(prof, i) for i, al in enumerate(prof['alpha']))
    return +out


# ------------------------------------------------------------------ quadrature cross-checks
def selftest(verbose=True):
    """Each closed form against direct quadrature of its defining integral (at 40 digits)."""
    worst = {}
    with mp.workdps(40):
        def psi_cells():
            return [(M(i*KAPPA), M((i+1)*KAPPA), M(BETA[i])) for i in range(16)]
        for lam in (Q(1, 3), Q(763, 1000), Q(29, 10)):
            l = M(lam)
            # B_phi from its definition, cell by cell: int_u^T psi = beta_i((i+1)kappa - u) + kappa sum_{j>i} beta_j
            for phi in (Q(1, 3), Q(1, 4)):
                tot = mpf(0)
                for i, (c0, c1_, b) in enumerate(psi_cells()):
                    tail = M(KAPPA*SUFFIX[i])
                    tot += 2*mp.quad(lambda t: b*mp.exp(-2*l*t)*(b*(c1_-t)+tail), [c0, c1_])
                    tot += M(phi)*mp.quad(lambda t: b*b*mp.exp(-2*l*t), [c0, c1_])
                ref = tot/M(H0Q)
                worst['B'] = max(worst.get('B', 0), abs(ref/B(phi, lam)-1))
            ref = sum(mp.quad(lambda t: b*mp.exp(-l*t), [c0, c1_]) for c0, c1_, b in psi_cells())
            worst['Psi'] = max(worst.get('Psi', 0), abs(ref/Psi(lam)-1))
        for p, a in ((Q(51, 50), Q(33, 50)), (Q(3, 2), Q(7, 5))):
            pp, aa = M(p), M(a)
            tot = mpf(0)
            cells = psi_cells()
            for j, (u0, u1, bj) in enumerate(cells):
                tot += bj*bj*mp.quad(lambda uu: mp.exp(-2*pp*uu)*mp.quad(lambda vv: mp.exp(-aa*(vv-uu)), [uu, u1]), [u0, u1])
                for k in range(j+1, 16):
                    v0, v1, bk = cells[k]
                    tot += bj*bk*mp.quad(lambda uu: mp.exp(-(2*pp-aa)*uu), [u0, u1])*mp.quad(lambda vv: mp.exp(-aa*vv), [v0, v1])
            ref = 2*tot/M(H0Q)
            worst['C'] = max(worst.get('C', 0), abs(ref/Cpa(p, a)-1))
        for pname, prof in PROFILES.items():
            u, v, x = _geom(prof)
            eps, c2, th = prof['eps'], prof['c2'], prof['theta']
            for lam in (Q(1, 2), th/2+Q(1, 10**9), Q(3)):
                a = M(2*lam-th)
                ref = (mp.quad(lambda t: mp.exp(a*t)*mp.sqrt(t-M(u)+M(eps)), mp.linspace(M(u), M(v), 9))
                       + mp.quad(lambda t: mp.exp(a*t)*mp.sqrt(M(c2+eps)), [M(v), M(x)]))
                worst['winv'] = max(worst.get('winv', 0), abs(ref/winv(pname, lam)-1))
            hh = c2/10; tot = mpf(0)
            for i, al in enumerate(prof['alpha']):
                s = i*hh
                pieces = [(u+s, u+s+hh, lambda t: mp.exp(M(th)*t)*(t-M(u+s))/mp.sqrt(t-M(u)+M(eps)))]
                if s+hh < c2:
                    pieces.append((u+s+hh, v, lambda t: mp.exp(M(th)*t)*M(hh)/mp.sqrt(t-M(u)+M(eps))))
                pieces.append((v, x, lambda t: mp.exp(M(th)*t)*M(hh)/mp.sqrt(M(c2+eps))))
                J = sum(mp.quad(f, mp.linspace(M(lo), M(hi), 5)) for lo, hi, f in pieces)
                tot += M(al**2)*J
            ref = M(Q(100)/(prof['c1']*c2**2))*tot
            worst['V'] = max(worst.get('V', 0), abs(ref/V(pname)-1))
    # values cached above were rounded to the test's 40 digits: recompute them at DPS when needed
    for f in (_B, _Psi, _Cpa, _winv, V):
        f.cache_clear()
    ok = all(e < mpf(10)**-30 for e in worst.values())
    if verbose:
        print('selftest (relative difference, closed form vs quadrature):',
              {k: mpmath.nstr(e, 3) for k, e in worst.items()}, 'PASS' if ok else 'FAIL', flush=True)
    return ok, {k: float(e) for k, e in worst.items()}


# ------------------------------------------------------------------ rounding and classification
GAP = [mpf(1)]       # smallest |S x - integer| met by rnd: how far every rounding was from ambiguity


def rnd(x, up):
    """(ceil or floor of S x, near): near when S x is within NEAR of an integer."""
    y = x*S
    n = int(mp.ceil(y) if up else mp.floor(y))
    g = abs(y-mp.nint(y))
    GAP[0] = min(GAP[0], g)
    return n, g < NEAR


class Tally:
    def __init__(self):
        self.count = {}; self.safe = []; self.bad = []; self.near = []

    def check(self, leaf, what, stored, expected, up, true=None, near=0):
        """up: the stored integer is an upper bound (safe when larger), False: a lower bound, None: exact.
        near: how far the stored integer may legitimately differ, one per rounding (times its
        multiplicity) whose S x lies within NEAR of an integer."""
        k = what.split('[')[0]
        c = self.count.setdefault(k, [0, 0])
        c[0] += 1
        if stored == expected:
            c[1] += 1
            if near:
                self.near.append(dict(leaf=leaf, what=what, stored=stored,
                                      true=None if true is None else mpmath.nstr(true*S, 45)))
            return
        safe_side = up is not None and ((stored > expected) if up else (stored < expected))
        rec = dict(leaf=leaf, what=what, stored=stored, expected=expected, safe_side=safe_side,
                   true_times_S=None if true is None else mpmath.nstr(true*S, 45))
        if near and safe_side and abs(stored-expected) <= near:
            self.safe.append(rec)
        else:
            self.bad.append(rec)


# ------------------------------------------------------------------ the leaf check
def profile_of(meta):
    name = meta['profile']
    assert name in PROFILES, ('unknown far profile', name)
    ref = PROFILES[name]
    got = dict(c1=Q(meta['c1']), c2=Q(meta['c2']), theta=Q(meta['theta']), eps=Q(meta['eps']),
               alpha=tuple(Q(x) for x in meta['alpha']))
    assert got == ref, ('far profile constants differ from the note', name)
    return name


def layout_errors(d):
    """The columns' intervals and fixed coefficients against the builders' grids (note §2)."""
    errs = []
    cs = d['case']; cols = d['columns']
    fam = [c['family'] for c in cols]
    if fam != sorted(fam, key=('ordinary', 'hidden', 'second').index):
        errs.append('column families out of order')
    ordc = [c for c in cols if c['family'] == 'ordinary']
    hid = [c for c in cols if c['family'] == 'hidden']
    sec = [c for c in cols if c['family'] == 'second']
    r0, den, lam3 = Q(cs['ordinary_lower']), cs['den'], Q(cs['third_lower'])
    R = max(R_TAIL, r0)
    pts = [r0]+[Q(j, den) for j in range(math.floor(r0*den)+1, math.floor(R*den)+1)]
    if pts[-1] != R:
        pts.append(R)
    bins = [(l, r) for l, r in zip(pts, pts[1:]) if not (cs['second'] and r <= lam3)]
    got = [(Q(c['lo']), Q(c['hi'])) for c in ordc if c['kind'] == 'bin']
    if got != bins:
        errs.append('ordinary bins differ from the grid')
    tails = [c for c in ordc if c['kind'] == 'tail']
    if len(tails) != 1 or ordc[-1]['kind'] != 'tail' or Q(tails[0]['lo']) != R:
        errs.append('ordinary tail')
    for c in ordc:
        if c['obj'] != {'G': '1/3'} or c['w'] != d['far_profile']['profile']:
            errs.append('ordinary objective/profile'); break
    if cs['height'] == 'outside':
        fo = d['first']['outside']
        a, lp = Q(cs['lo']), Q(cs['lp'])
        ph = max(a, lp, Q(cs['gap']['lo'])) if cs['gap'] else max(a, lp)
        if Q(fo['p_h']) != ph:
            errs.append('hidden anchor p_h')
        end = max(R_TAIL, ph)
        grid = [ph]; e = math.floor(ph*den)+1
        while Q(e, den) < end:
            grid.append(Q(e, den)); e += 1
        if grid[-1] != end:
            grid.append(end)
        got = [(Q(c['lo']), Q(c['hi'])) for c in hid if c['kind'] == 'bin']
        if got != list(zip(grid, grid[1:])) or len(hid) != len(grid) or hid[-1]['kind'] != 'tail' \
                or Q(hid[-1]['lo']) != end:
            errs.append('hidden grid')
        phi = '1/4' if cs['type'] == 'rc' else '1/3'
        if any(c['obj'] != {'hidden': {'phi': phi, 'p': str(ph)}} or c['w'] != 'inherited' for c in hid) \
                or fo['phi'] != phi or fo['hidden_columns'] != len(hid):
            errs.append('hidden objective')
    elif hid:
        errs.append('hidden columns on an inside leaf')
    if sec:
        s2 = cs['second']; lo2, hi2 = Q(s2['lo']), Q(s2['hi']); g = cs['second_columns_den']
        pts = [lo2]+[Q(k, g) for k in range(math.floor(lo2*g)+1, math.ceil(hi2*g)) if lo2 < Q(k, g) < hi2]+[hi2]
        if [(Q(c['lo']), Q(c['hi'])) for c in sec] != list(zip(pts, pts[1:])):
            errs.append('second-family grid')
        phi2 = '1/4' if s2['n'] == 1 else '1/3'
        if any(c['obj'] != {'G': phi2} or c['kind'] != 'bin' or c['w'] != d['far_profile']['profile'] for c in sec):
            errs.append('second-family objective')
    return errs


def semantic_errors(d):
    """The metadata's first-family and budget components against the note's rules."""
    errs = []
    cs, far, fi = d['case'], d['far'], d['first']
    typ = cs['type']; n = 2 if typ == 'complex' else 1
    if cs['height'] == 'inside':
        f = fi['inside']
        p = Q(cs['gap']['lo']) if cs['gap'] else Q(cs['lp'])
        exp = dict(n=n, alpha=2 if typ == 'rc' else 1, phi_t='1/4' if typ in ('rr', 'rc') else '1/3',
                   a=cs['lo'], b=cs['hi'], p=str(p), J_new=p >= Q(cs['hi']))
        if f != exp or fi['outside'] is not None:
            errs.append(('inside first-family metadata', f, exp))
        if far['inside'] != dict(n=n, b=cs['hi']):
            errs.append('far inside term')
    else:
        if fi['inside'] is not None or far['inside'] is not None or fi['outside']['n'] != n:
            errs.append('outside first-family metadata')
    s2 = cs['second']; ncols = sum(c['family'] == 'second' for c in d['columns'])
    if s2 is None:
        if fi['J2'] is not None or far['reserved'] is not None or ncols:
            errs.append('J2/reserved without a reserved family')
    else:
        if s2['lo'] != cs['ordinary_lower']:
            errs.append('lo2 != ordinary_lower')
        if fi['J2'] != dict(n2=s2['n'], phi2='1/4' if s2['n'] == 1 else '1/3', lo2=s2['lo'],
                            removed_for_columns=ncols > 0):
            errs.append('J2 metadata')
        if far['reserved'] != dict(n2=s2['n'], hi2=s2['hi'], added_back=ncols > 0):
            errs.append('reserved far metadata')
    if far['V'] != d['far_profile']['profile'] or Q(far['eta']) != ETA:
        errs.append('far constant metadata')
    return errs


def check_leaf(d, tally):
    name = d['name']
    L = Q(d['L'])
    pname = profile_of(d['far_profile'])
    cs = d['case']
    errs = layout_errors(d)+semantic_errors(d)
    st = tally.count.setdefault('structure', [0, 0])
    st[0] += 1; st[1] += not errs
    for e in errs:
        tally.bad.append(dict(leaf=name, what='structure', error=str(e)))
    lam3 = Q(cs['third_lower'])
    for i, c in enumerate(d['columns']):
        fam, tail = c['family'], c['kind'] == 'tail'
        lo = Q(c['lo'])
        wp = c['w']
        if wp != 'inherited':
            assert wp == pname
        if 'G' in c['obj']:
            val = Gphi(L, c['obj']['G'], lo)
        else:
            hd = c['obj']['hidden']
            val = expA(L, lo)*B(hd['phi'], hd['p'])
        if tail:
            val = val*winv(wp, lo)
        g, near = rnd(val, True)
        tally.check(name, f'G[{i}]', c['G'], g, True, val, near)
        if tail:
            tally.check(name, f'W[{i}]', c['W'], S, None)
        else:
            x = w(wp, Q(c['hi']))
            ww, near = rnd(x, False)
            tally.check(name, f'W[{i}]', c['W'], ww, False, x, near)
        cnt = S if (fam == 'ordinary' and not tail and cs['second'] is None and Q(c['hi']) <= lam3) else 0
        tally.check(name, f'C[{i}]', c['C'], cnt, None)
        if fam == 'hidden' and tail:
            x = winv('inherited', lo)
            nh, near = rnd(x, False)
            tally.check(name, f'NH[{i}]', c['NH'], nh, False, x, near)
        else:
            tally.check(name, f'NH[{i}]', c['NH'], S if fam == 'hidden' else 0, None)
        tally.check(name, f'E[{i}]', c['E'], S if fam == 'second' else 0, None)

    # far budget
    far = d['far']
    x = (1+M(ETA))*V(pname)
    F, nr = rnd(x, True)
    nearF = int(nr); trueF = x
    if far['inside']:
        y = w(pname, Q(far['inside']['b'])); k, nr = rnd(y, False)
        F -= far['inside']['n']*k; nearF += far['inside']['n']*nr
        trueF -= far['inside']['n']*y
    rs = far['reserved']
    if rs and not rs['added_back']:           # added back for columns: the two terms cancel exactly
        y = w(pname, Q(rs['hi2'])); k, nr = rnd(y, False)
        F -= rs['n2']*k; nearF += rs['n2']*nr
        trueF -= rs['n2']*y
    tally.check(name, 'F', far['F'], F, True, trueF, nearF)

    # first-family charge
    fi = d['first']
    tot = 0; nearJ = 0; trueJ = mpf(0)
    if fi['inside']:
        f = fi['inside']
        n, al, phi, a, b, p = f['n'], f['alpha'], f['phi_t'], Q(f['a']), Q(f['b']), Q(f['p'])
        ha = h(a)
        k, nr = rnd(B(phi, a)-al*ha, True)                 # the inner ceiling of J_old
        nearJ += 2*nr
        Jold = n*(expA(L, p)*M(Q(max(0, k), S))+al*expA(L, a)*ha)
        c_old, nr = rnd(Jold, True); nearJ += nr
        charge, trueJ = c_old, Jold
        if f['J_new'] and p < b:           # J_new is valid only for p >= b (triple_inputs.shifted_first)
            tally.bad.append(dict(leaf=name, what='structure', error='J_new claimed with p < b'))
        elif f['J_new']:
            Jnew = n*(al*expA(L, a)*ha+expA(L, p)*(B(phi, p)-al*Cpa(p, a)))
            c_new, nr = rnd(Jnew, True); nearJ += nr
            if c_new < c_old:
                charge, trueJ = c_new, Jnew
        tot += charge
    J2 = fi['J2']
    if J2 and not J2['removed_for_columns']:
        y = Gphi(L, J2['phi2'], Q(J2['lo2'])); k, nr = rnd(y, True)
        tot += J2['n2']*k; nearJ += J2['n2']*nr; trueJ += J2['n2']*y
    tally.check(name, 'first', fi['first'], tot, True, trueJ, nearJ)
    tally.check(name, 'final', fi['final'], int(FINAL*S), None)


def read_lines(paths):
    for p in paths:
        op = gzip.open if p.endswith('.gz') else open
        with op(p, 'rt') as f:
            for line in f:
                if line.strip():
                    yield json.loads(line)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('files', nargs='+', help='JSON lines of graded_lean_export.py --numerics')
    ap.add_argument('--report', default=None, help='write a JSON report here')
    ap.add_argument('--no-selftest', action='store_true')
    a = ap.parse_args()
    t0 = time.time()
    st = (True, {}) if a.no_selftest else selftest()
    tally = Tally(); leaves = 0; roots = set(); kinds = {}
    for d in read_lines(a.files):
        check_leaf(d, tally)
        leaves += 1; roots.add((d['kind'], d['root']))
        key = (d['kind'], d['far_profile']['profile'], d['case']['type'])
        kinds[key] = kinds.get(key, 0)+1
    total = sum(c[0] for k, c in tally.count.items() if k != 'structure')
    exact = sum(c[1] for k, c in tally.count.items() if k != 'structure')
    rep = dict(files=a.files, roots=len(roots), leaves=leaves, integers=total, exact=exact,
               by_field={k: dict(checked=v[0], exact=v[1]) for k, v in sorted(tally.count.items())},
               leaf_types={f'{k[0]}/{k[1]}/{k[2]}': v for k, v in sorted(kinds.items())},
               safe_off_by_one=tally.safe, near_integer_exact=tally.near, mismatches=tally.bad,
               min_distance_to_integer=mpmath.nstr(GAP[0], 3),
               selftest=dict(ok=st[0], worst_relative=st[1]), dps=DPS, seconds=round(time.time()-t0, 1),
               status='PASS' if (st[0] and not tally.bad) else 'FAIL')
    print(json.dumps({k: v for k, v in rep.items() if k not in ('mismatches', 'safe_off_by_one', 'near_integer_exact')}))
    print('safe off-by-one', len(tally.safe), 'near-integer exact', len(tally.near), 'mismatches', len(tally.bad))
    for r in tally.bad[:20]:
        print('MISMATCH', r)
    for r in tally.safe[:20]:
        print('SAFE', r)
    if a.report:
        with open(a.report, 'w') as f:
            json.dump(rep, f, indent=1)
    return 0 if rep['status'] == 'PASS' else 1


if __name__ == '__main__':
    sys.exit(main())
