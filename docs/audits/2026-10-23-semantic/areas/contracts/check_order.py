from itertools import product

def subs(x): return [y for y in range(x+1) if y & ~x == 0]
def parts(mask):
    if not mask: return [()]
    bit=mask & -mask
    return [(g,)+p for g in subs(mask) if g & bit for p in parts(mask ^ g)]
def local_choices(group):
    menus=subs(group)
    out=[]
    for cs in product(*(subs(m) for m in menus)):
        c=dict(zip(menus,cs))
        sub=all(c[v]&w & ~c[w] == 0 for v in menus for w in subs(v))
        if not sub: continue
        cons=all(c[w]==c[v] for v in menus for w in subs(v) if c[v] & ~w == 0)
        load=all(bin(c[w]).count("1")<=bin(c[v]).count("1") for v in menus for w in subs(v))
        out.append((c,cons,load))
    return out

for n in range(4):
    full=(1<<n)-1; menus=range(full+1); states=list(product(menus,repeat=2))
    groups=parts(full); models={}
    for partition in groups:
        agents=[]
        for g in partition: agents.append(local_choices(g))
        models[partition]=[]
        for choices in product(*agents):
            C=tuple(sum(c[m & g] for g,(c,_,_) in zip(partition,choices)) for m in menus)
            models[partition].append((C,all(c for _,c,_ in choices),all(l for _,_,l in choices)))
    checked=stable_checks=order_checks=loadchecks=0
    for bp,sp in product(groups,repeat=2):
      for (B,bc,bl),(S,sc,sl) in product(models[bp],models[sp]):
        checked+=1
        accB=tuple(sum(1<<i for i in range(n) if B[m | (1<<i)] & (1<<i)) for m in menus)
        accS=tuple(sum(1<<i for i in range(n) if S[m | (1<<i)] & (1<<i)) for m in menus)
        F=lambda p:(accB[p[1]],accS[p[0]])
        le=lambda p,q:(p[0] & ~q[0] == 0 and q[1] & ~p[1] == 0)
        fixed=[p for p in states if F(p)==p]
        for initial,greater in [((full,0),True),((0,full),False)]:
            p=initial
            for t in range(len(states)+1):
                q=F(p)
                if q==p: break
                p=q
            else: raise AssertionError(('nonconvergence',n,bp,sp,B,S))
            assert (all(le(q,p) for q in fixed) if greater else all(le(p,q) for q in fixed))
        if not (bc and sc): continue
        stable=[]
        for a in menus:
            ir=(B[a]==a and S[a]==a)
            blocks=any(z & ~B[a|z] == 0 and z & ~S[a|z] == 0 for z in subs(full^a) if z)
            if ir and not blocks: stable.append(a)
        outcomes=[p[0]&p[1] for p in fixed]
        assert len(outcomes)==len(set(outcomes)) and set(outcomes)==set(stable)
        assert all(F((a,a)) in fixed and (accB[a]&accS[a])==a for a in stable)
        stable_checks+=1
        for p,q in product(fixed,repeat=2):
            a=p[0]&p[1]; d=q[0]&q[1]
            # q is seller-chosen over p, p is buyer-chosen over q.
            assert le(p,q)==(S[a|d]==d)==(B[a|d]==a)
            order_checks+=1
        if bl and sl:
            assert all(bin(a&g).count("1")==bin(d&g).count("1") for a,d in product(stable,repeat=2) for g in bp+sp)
            loadchecks+=1
    print({'n':n,'market_instances':checked,'irc_bijection_checks':stable_checks,'order_pair_checks':order_checks,'rural_hospitals_instances':loadchecks})
