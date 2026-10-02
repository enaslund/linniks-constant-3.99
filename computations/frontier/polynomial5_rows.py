"""Real-first second-zero rows using a nonnegative degree-five polynomial.

The generic branch uses the weighted Heath-Brown conductor saving. All possible
principal aliases (orders 2, 4, 5, 10) have separate inequalities. This is an
analytic source-input deduction, not a complete Linnik exponent.
"""
from inside_real_rows import *
from new_positivity import _finite

COEFFICIENTS = {1: Q('1.41866466') / Q('1.000001'),
                2: Q('.43287503') / Q('1.000001'),
                5: Q('.01421037') / Q('1.000001')}


@lru_cache(None)
def polynomial_check(coefficients):
    c1, c2, c5 = coefficients
    assert min(coefficients) > 0 and sum(coefficients) >= Q(1, 9)
    # P(x)=1+c1*T1(x)+c2*T2(x)+c5*T5(x), -1<=x<=1.
    # |P''(x)| <= 4*c2+440*c5; interpolation error <= M*h^2/8.
    den = 2000
    minimum = min(1+c1*x+c2*(2*x*x-1)+c5*(16*x**5-20*x**3+5*x)
                  for x in (Q(j, den) for j in range(-den, den+1)))
    error = (4*c2+440*c5)/Q(8*den*den)
    assert minimum > error
    return dict(variable='cos(theta)',denominator=den,
                sample_minimum=str(minimum),interpolation_error=str(error),
                lower=str(minimum-error))


def certify_row5(a,b,h,g,coefficients=None,Y=30,den=200):
    a,b,h,g=map(Q,(a,b,h,g));assert 0<a<=b<=h and g>0
    cs=COEFFICIENTS if coefficients is None else {int(k):Q(v) for k,v in coefficients.items()}
    assert set(cs)=={1,2,5};c1,c2,c5=(cs[k] for k in (1,2,5))
    poly=polynomial_check((c1,c2,c5))
    f=test(g);f0=f.f0;lhs=f.F(b-a)+I(c1)*f.F(h-a)-f.F(-a)
    generic=lower(lhs/f0-I(Q(1,8)+(c1+c2+c5)/3-Q(1,108)))
    # Order four: exactly the retained coupled correlation, with the extra
    # fifth-frequency pair treated as nonprincipal and its zero terms omitted.
    P=vector_transform(g,-a,Y,den);corners=[]
    for ll in (a,b):
        for rr in (a,h):
            R=vi.sub(vi.mul(fq(c2),vi.sub(P,vector_transform(g,ll-a,Y,den))),
                     vi.mul(fq(c1),vector_transform(g,rr-a,Y,den)))
            _finite(R);corners.append(float(np.max(R[1])))
    sample=ceil_fraction(Q.from_float(max(corners))*S)
    moment=f.exponential_moment(2,Q(0))
    he=upper((I(c2)*f.exponential_moment(2,a)+I(c2+c1)*moment)*I(Q(1,8*den*den)))
    pe=upper(I(c2*(b-a)**2+c1*(h-a)**2)*moment/8)
    def tailbox(lo,hi):
        yi=I(Y);gi=I(g);ee=iv.exp(-2*gi*I(lo));sig=max(abs(lo),abs(hi))
        return f0*I(sig)/yi**2+8*gi**3/(3*yi**3)+4*gi**2*(1+ee)/yi**4+4*(1+ee)/yi**6+8*gi*ee/yi**5
    tail=upper(I(c2)*(real_tail(f,-a,Q(Y))+tailbox(0,b-a))+I(c1)*tailbox(0,h-a))
    bound=max(0,tail,sample+he+pe)
    alias4=lower((lhs-I((1+c2)/8+(c1+c5)/3)*f0-I(Q(bound,S)))/f0)
    # Orders five and ten: one fifth-frequency principal term; all remaining
    # characters have bounded order. Re F(-a+i*y)<=F(-a) suffices here.
    alias5_10=lower(lhs/f0-I((1+c5)/8+(c1+c2)/4)-I(c5)*f.F(-a)/f0)
    fr=test(Q('.82'))
    real=lower((fr.F(b-a)+fr.F(h-a)-fr.F(-a))/fr.f0-I(Q(3,8)))
    assert min(generic,alias4,alias5_10,real)>10**10, (generic,alias4,alias5_10,real)
    return dict(kind='degree5-conductor',a=str(a),b=str(b),lower=str(h),gamma=str(g),
                coefficients={str(k):str(cs[k]) for k in (1,2,5)},polynomial=poly,
                generic_saving='1/108',generic_margin=generic,order4_margin=alias4,
                order5_10_margin=alias5_10,real_second_margin=real,real_gamma='41/50',scale=S,
                correlation=dict(sample=sample,height_error=he,parameter_error=pe,tail=tail,bound=bound,Y=Y,den=den))


def regenerate_row5(row):
    return certify_row5(row['a'],row['b'],row['lower'],row['gamma'],row['coefficients'],
                        row['correlation']['Y'],row['correlation']['den'])


def propose5(a,b):
    c1,c2,c5=(float(COEFFICIENTS[k]) for k in (1,2,5));aa,bb=float(a),float(b)
    def h_for(g):
        def margin(h):
            return trans(g,bb-aa)+c1*trans(g,h-aa)-trans(g,-aa)-(1/8+(c1+c2+c5)/3-1/108)
        if margin(bb)<=0:return bb-abs(margin(bb))
        return brentq(margin,bb,1.5)
    from scipy.optimize import minimize_scalar
    opt=minimize_scalar(lambda g:-h_for(g),bounds=(.8,1.3),method='bounded')
    g=Q(f'{opt.x:.6f}');h=Q(math.floor((-opt.fun-.00005)*10000),10000)
    while h>b:
        try:return certify_row5(a,b,h,g)
        except AssertionError:h-=Q('.0001')
    return None


if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--start',default='.700');ap.add_argument('--stop',default='.755')
    ap.add_argument('--step',default='.0025');ap.add_argument('--verify',action='store_true');args=ap.parse_args()
    path=Path(__file__).resolve().parent/f'inside_polynomial5_rows_{args.start}_{args.stop}.json'
    if args.verify:
        data=json.loads(path.read_text())
        for row in data['rows']:assert regenerate_row5(row)==row
        print('PASS',len(data['rows']),'complete row inequalities',flush=True)
    else:
        a=Q(args.start);rows=[]
        while a<Q(args.stop):
            b=min(a+Q(args.step),Q(args.stop));row=propose5(a,b)
            if row is None:break
            rows.append(row);print(json.dumps({k:row[k] for k in ('a','b','lower','generic_margin','order4_margin','order5_10_margin','real_second_margin')}),flush=True);a=b
        path.write_text(json.dumps(dict(scope='Real-first second-zero exclusions; no complete Linnik exponent',rows=rows),indent=2)+'\n')
