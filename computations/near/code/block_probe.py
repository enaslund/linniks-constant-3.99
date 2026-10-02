"""Experimental near Gram blocks with real shifts; no new number-theoretic claim."""
from start import *
from optimize_near import hull_n
from scipy.optimize import minimize_scalar
from itertools import combinations


def setup(inp,shifts=(0.,.5,1.),L='4.33'):
    from triple_inputs import input_with_third,use_shifted
    inp=use_shifted(input_with_third(inp,L),L)
    gg,gz=map(float,(Q(inp['extension']['gG']),Q(inp['extension']['gZ'])))
    s=float(Q(inp['shift']));mix=float(Q(inp['extension'].get('mix','0')))
    if inp['extension']['variant']=='pair':raise ValueError('paired first not yet in probe')
    N,RG=norm0(gg,gz,s,mix,0.,0.);d0=1/(6*RG)
    corr=inp['D']/S/1.000001-1+d0
    shifts=np.array(shifts)
    K=1.000001*(np.array([[trans(gg,r+t-s)/RG for r in shifts]for t in shifts])+corr-d0)
    eig=np.linalg.eigvalsh(K)
    if eig.min()<=1e-9: raise ValueError(('not sufficiently pd',eig))
    rows=inp['rows'];hh=np.array([float(Q(r[1])) if r[1]!='infinity' else 30 for r in rows]);hh[-1]=30
    v=np.array([[(trans(gz,h-s+r)+mix*trans(gg,h-s+r)-(1+mix)/6)/N-1e-6 for r in shifts]for h in hh]);v[-1]=-1
    arrays=dict(inp=inp,K=K,shifts=shifts,eigenvalues=eig,v=v,W=np.array([r[2]/S for r in rows]),G=np.array([r[3]/S for r in rows]),F=inp['far_budget']/S)
    return arrays


def cone_cost(b,K):
    best=np.zeros(len(b));arg=np.zeros(len(b),dtype=int)
    for mask in range(1,1<<K.shape[0]):
        ids=[j for j in range(K.shape[0]) if mask&(1<<j)]
        sub=K[np.ix_(ids,ids)];coeff=b[:,ids]@np.linalg.inv(sub)
        val=np.einsum('ij,ij->i',coeff,b[:,ids]);val[np.any(coeff<0,axis=1)]=0
        ii=val>best;best[ii]=val[ii];arg[ii]=mask
    return best,arg


def eval_tau(t,a):
    inp=a['inp'];D=inp['D']/S;Df=inp['Df']/S;d=inp['d']/S;sec=inp['second']
    B=D*(1-t*t/d)-inp['n']*D/Df*max(inp['v_first']/S-t,0)**2
    if sec: B-=sec['n']*max(sec['v']/S-t,0)**2
    if B<0:return -1,None
    cost,arg=cone_cost(a['v']-t,a['K']);C=D*cost
    y,z=hull_n(a['W'],C,a['G'],a['F'],B)
    return inp['first']/S+y*a['F']+z*B+inp['final']/S, dict(tau=t,y=y,z=z,budget=B,mask_counts=dict(zip(*[x.tolist() for x in np.unique(arg,return_counts=True)])))


def probe(inp,shifts,L):
    a=setup(inp,shifts,L);end=np.sqrt(inp['d']/S);grid=np.linspace(0,end,161)
    vals=np.array([eval_tau(t,a)[0]for t in grid]);i=vals.argmax();best=float(vals[i]);bt=grid[i]
    for j in np.argsort(vals)[-3:]:
        op=minimize_scalar(lambda t:-eval_tau(t,a)[0],bounds=(grid[max(0,j-1)],grid[min(len(grid)-1,j+1)]),method='bounded',options={'xatol':1e-11})
        if -op.fun>best:best=-op.fun;bt=op.x
    _,detail=eval_tau(bt,a)
    return dict(L=L,shifts=list(shifts),value=best,detail=detail,min_eigenvalue=float(a['eigenvalues'].min()),scope='floating exploratory, not interval proof'),a

if __name__=='__main__':
    data=load_data('selected_inputs.json');out=[]
    for id in ['2063','428','2421','1850']:
      if not data[id]:continue
      inp=data[id][0][1]
      for L in ['4.33','4.25','4.00']:
       for shifts in [[0.],[0.,.5],[0.,.5,1.],[0.,1.,2.]]:
        try:
          ans,a=probe(inp,shifts,L);ans['id']=id;out.append(ans);print(json.dumps(ans),flush=True)
        except Exception as e: print(id,L,shifts,repr(e),flush=True)
    (PACKAGE/'results/real_shift_probe.json').write_text(json.dumps(out,indent=2))
