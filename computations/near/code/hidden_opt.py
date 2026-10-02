from hidden_global_height_probe import *
from scipy.optimize import minimize
D=load_data('selected_inputs.json');inp=D['2063'][0][1]
from triple_inputs import input_with_third,use_shifted
out=[]
for L in ['4.25','4.24','4.20']:
 new=use_shifted(input_with_third(inp,L),L);sec=new['second'];a,b=map(float,(Q(new['case']['lo']),Q(new['case']['hi'])));r=float(Q(new['ordinary_lower']));s=.74
 h2=float(Q(sec['hi']));n2=sec['n'];kind=2
 hs=np.array([float(Q(row[1])) if row[1]!='infinity' else 30. for row in new['rows']]);W=np.array([row[2]/S for row in new['rows']]);G=np.array([row[3]/S for row in new['rows']]);F=new['far_budget']/S;first=new['first']/S
 def fun(x):
  if x[0]<=x[1]:return 1e5
  return model(*x,a,b,s,kind,h2,n2,hs,W,G,F,first,.7425,r,2,False,61)
 op=minimize(fun,[1.85,1.22,.02],bounds=[(1.,2.8),(.6,1.6),(0.,1.5)],method='Nelder-Mead',options={'maxiter':180,'fatol':1e-7,'xatol':1e-5})
 p=[round(x,5)for x in op.x];check=probe(inp,L,.005,p);ans=dict(L=L,point_initial=fun([1.85,1.22,0]),point_optimized=fun(p),params=p,max_over_global_branches=check['improved'],optimizer_success=bool(op.success));out.append(ans);print(json.dumps(ans),flush=True)
(PACKAGE/'results/hidden_opt.json').write_text(json.dumps(out,indent=2))
