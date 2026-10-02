"""Two targeted positivity lemmas for a complex first character.
Only elementary continuous transform inequalities are verified here. The source
explicit formula and the separately written character-index matching proof are premises.
No optimizer is used; all accepted parameters are rational.
"""
from endgame import *
from extension_enclosures import vector_transform,_finite,vi,fq
from pair_bounds import real_tail
from base_enclosures import ceil_fraction

@lru_cache(None)
def alias_sup(a,h,g,t,Y=30,den=200):
 a,h,g,t=map(Q,(a,h,g,t));assert 0<a<=h and 0<t
 f=test(g);P=vector_transform(g,-a,Y,den);c=4*t
 mx=-math.inf
 for z in (Q(0),h-a):
  vv=_finite(vi.sub(P,vi.mul(fq(c),vector_transform(g,z,Y,den))))
  mx=max(mx,float(np.max(vv[1])))
 sample=ceil_fraction(Q.from_float(mx)*S)
 m0=f.exponential_moment(2,Q(0));ma=f.exponential_moment(2,a)
 he=upper((ma+I(c)*m0)*I(Q(1,8*den*den)))
 pe=upper(I(c*(h-a)**2)*m0/8)
 tail=upper(real_tail(f,-a,Q(Y))) # negative transform term has Re >= 0
 bound=max(sample+he+pe,tail)
 margin=lower((f.f0/6-I(Q(bound,S)))/f.f0)
 return dict(bound=bound,normalized_margin=margin,sample_upper=sample,height_error=he,parameter_error=pe,tail_upper=tail,Y=Y,den=den,scale=S)

def coefficients(t):
 t=Q(t);return 2*t/(t*t+Q(1,2)),Q(1,2)/(t*t+Q(1,2))

def complex_second_row(a='.685',b='.6875',h='.745',g='1.3',t='.9',gr='1.125',tr='.85'):
 a,b,h,g,t,gr,tr=map(Q,(a,b,h,g,t,gr,tr));assert 0<a<=b<=h
 f=test(g);c1,c2=coefficients(t)
 margin=lower((I(c1)*(f.F(b-a)+f.F(h-a))-f.F(-a))/f.f0- I(((1+c1+c2)**2-1)/6))
 alias=alias_sup(a,h,g,t)
 fr=test(gr);r1,r2=coefficients(tr)
 mr=lower((I(r1)*fr.F(b-a)+fr.F(h-a)-fr.F(-a))/fr.f0-I(Q(1,8)+(r1+r2)/3))
 ar=alias_sup(a,b,gr,tr) # inward alias target is always first character
 assert margin>0 and alias['normalized_margin']>0 and mr>0 and ar['normalized_margin']>0,(margin,alias,mr,ar)
 return dict(status='PASS: elementary second-family exclusion, complex first character',a=str(a),b=str(b),h=str(h),gamma=str(g),t=str(t),real_gamma=str(gr),real_t=str(tr),generic_normalized_margin=margin,real_normalized_margin=mr,alias=alias,real_alias=ar,scale=S,scope='New positive-polynomial deduction for every second-family type. Distinct-family conventions and the injective principal-index matching proof remain analytic premises. Not an exponent theorem.')

@lru_cache(None)
def same_corr(a,b,p,h,g,t,Y=30,den=200):
 a,b,p,h,g,t=map(Q,(a,b,p,h,g,t));assert 0<a<=b and a<=p<=h
 f=test(g);c1,c2=coefficients(t);P1=c1*c1/2;P2=c2*c2/2;Q1=c1*(1+c2/2);Q2=c1*c2/2
 def v(sig):return vector_transform(g,sig,2*Y,den)
 pp=v(-a)
 base=vi.add(vi.mul(fq(P1),(pp[0][:Y*den+1],pp[1][:Y*den+1])),vi.mul(fq(P2),(pp[0][::2],pp[1][::2])))
 mx=-math.inf
 for xx in (Q(0),b-a):
  for yy in (p-a,h-a):
   ww=vi.add(v(xx),v(yy));w1=(ww[0][:Y*den+1],ww[1][:Y*den+1]);w2=(ww[0][::2],ww[1][::2])
   vv=_finite(vi.sub(base,vi.add(vi.mul(fq(Q1),w1),vi.mul(fq(Q2),w2))))
   mx=max(mx,float(np.max(vv[1])))
 sample=ceil_fraction(Q.from_float(mx)*S);m0=f.exponential_moment(2,Q(0));ma=f.exponential_moment(2,a)
 he=upper((I(P1+4*P2)*ma+I(2*(Q1+4*Q2))*m0)*I(Q(1,8*den*den)))
 pe=upper(I((Q1+Q2)*((b-a)**2+(h-p)**2))*m0/8)
 tail=upper(I(P1)*real_tail(f,-a,Q(Y))+I(P2)*real_tail(f,-a,Q(2*Y)))
 return dict(bound=max(sample+he+pe,tail),sample_upper=sample,height_error=he,parameter_error=pe,tail_upper=tail,Y=Y,den=den,scale=S)

def additional_row(a='.755',b='.7575',p='.89',h='.915',g='1.125',t='.9'):
 a,b,p,h,g,t=map(Q,(a,b,p,h,g,t));assert a<=p and b<=Q('.86') and h<Q('1.35')
 f=test(g);c1,c2=coefficients(t);mass=(1+c1+c2)**2-1-(c1*c1+c2*c2)/2
 corr=same_corr(a,b,p,h,g,t)
 margin=lower((I(c1)*(f.F(b-a)+f.F(h-a))-f.F(-a)-I(Q(corr['bound'],S)))/f.f0-I(mass/6))
 assert margin>0,(margin,corr)
 return dict(status='PASS: elementary additional-zero exclusion, complex first character',a=str(a),b=str(b),old_lower=str(p),new_lower=str(h),gamma=str(g),t=str(t),normalized_margin=margin,correlation=corr,low_order_source='X Table 3, lambda1<=.86 implies lambda-prime>1.35 for orders 2,3,4',scale=S,scope='Orders >=5 use the new nonnegative product; orders 3,4 use the published source row. Finite-zero-selection and character conventions remain analytic inputs.')

if __name__=='__main__':
 out={'second_row':complex_second_row(),'additional_row':additional_row()}
 (ROOT/'results/new_complex_rows.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))

@lru_cache(None)
def polynomial_table():
 data=json.loads((ROOT/'results/polynomial_table.json').read_text())
 assert data['scale']==S and len(data['rows'])==data['row_count']
 for i,row in enumerate(data['rows']):assert row['id']==i
 return data

def verify_polynomial_table():
 data=polynomial_table()
 for row in data['rows']:
  p=row['proof']
  if row['type']=='second':
   gen=complex_second_row(p['a'],p['b'],p['h'],p['gamma'],p['t'],p['real_gamma'],p['real_t'])
  else:
   assert row['type']=='additional';gen=additional_row(p['a'],p['b'],p['old_lower'],p['new_lower'],p['gamma'],p['t'])
  assert gen==p,('polynomial proof regeneration mismatch',row['id'])
 return dict(status='PASS: all elementary polynomial rows regenerated',rows=data['row_count'],second_rows=sum(r['type']=='second' for r in data['rows']),additional_rows=sum(r['type']=='additional' for r in data['rows']),minimum_normalized_margin=min(r['proof'].get('generic_normalized_margin',r['proof'].get('normalized_margin',S)) for r in data['rows']),scale=S)

@lru_cache(None)
def applicable_polynomials(a,b):
 a,b=Q(a),Q(b)
 return tuple(r for r in polynomial_table()['rows'] if Q(r['proof']['a'])<=a<=b<=Q(r['proof']['b']))
