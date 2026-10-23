"""Exact bounded audit of the encoded 0..3-contract one-buyer/one-seller markets.
No inference beyond these finite instances. Integers represent subsets by bit masks.
Every table is contractive. Check predicates are direct set-level translations,
independently of Lean proof code.
"""
from itertools import product
import json

def subset(a,b): return (a & ~b)==0

def submasks(a):
    return tuple(b for b in range(a+1) if subset(b,a))

def tables(n):
    return product(*(submasks(a) for a in range(1<<n)))

def substitutable(c,n):
    return all(subset(c[b]&a,c[a]) for a in range(1<<n) for b in range(1<<n) if subset(a,b))

def irc(c,n):
    return all(c[a]==c[b] for a in range(1<<n) for b in range(1<<n) if subset(c[b],a) and subset(a,b))

def block(cb,cs,a,z):
    return z != 0 and a&z==0 and subset(z,cb[a|z]) and subset(z,cs[a|z])

def stable(cb,cs,a,n):
    return cb[a]==a and cs[a]==a and not any(block(cb,cs,a,z) for z in range(1<<n))

def pairwise(cb,cs,a,n):
    return cb[a]==a and cs[a]==a and not any(block(cb,cs,a,1<<i) for i in range(n))

def accepted(c,a,n):
    return sum(1<<i for i in range(n) if c[a|(1<<i)] & (1<<i))

out=[]
for n in range(4):
    all_c=list(tables(n))
    sc=[c for c in all_c if substitutable(c,n)]
    src=[c for c in sc if irc(c,n)]
    stable_checks=0
    point_checks=0
    # All substitutable tables, with IRC intentionally absent: Proposition 2.
    for cb,cs in product(sc,repeat=2):
        for a in range(1<<n):
            assert stable(cb,cs,a,n)==pairwise(cb,cs,a,n)
            stable_checks+=1
    # All substitutable + IRC tables: every state and every outcome, both maps.
    for cb,cs in product(src,repeat=2):
        def phi(p): return (accepted(cb,p[1],n),accepted(cs,p[0],n))
        fixed=[(s,b) for s,b in product(range(1<<n),repeat=2) if phi((s,b))==(s,b)]
        stable_sets=[a for a in range(1<<n) if stable(cb,cs,a,n)]
        assert sorted(s&b for s,b in fixed)==stable_sets # injective and surjective
        for s,b in fixed:
            assert phi((s&b,s&b))==(s,b)
        for a in stable_sets:
            p=phi((a,a))
            assert phi(p)==p and p[0]&p[1]==a
        assert fixed # finite Tarski consequence, no welfare interpretation used
        point_checks+=(1<<n)**2
    out.append(dict(contracts=n,contractive_tables=len(all_c),substitutable_tables=len(sc),substitutable_irc_tables=len(src),stable_pairwise_checks=stable_checks,fixed_state_checks=point_checks))

# Necessity control: a pairwise-stable but blocked complementary-choice outcome.
cb=cs=(0,0,0,3)
assert pairwise(cb,cs,0,2) and not stable(cb,cs,0,2)
assert block(cb,cs,0,3) and not substitutable(cb,2)

# Support need not imply own-menu locality: a belongs to buyer 0, b to buyer 1.
# Buyer 0 takes a iff b is present too. Outputs are always in Y ∩ {a}.
b0=lambda y: 1 if y==3 else 0
assert all(subset(b0(y), y&1) for y in range(4))
assert b0(3)==1 and b0(3&1)==0

# Adding contract x to its menu is essential: accept-all choices are stable only
# at the full set, and their canonical fixed point is (univ, univ).
identity=(0,1,2,3)
assert (accepted(identity,0,2),accepted(identity,0,2))==(3,3)
assert [a for a in range(4) if stable(identity,identity,a,2)]==[3]

print(json.dumps({'finite_exhaustion':out,'boundary_controls':['pairwise_without_substitutability','support_without_locality','acceptance_operator_uses_insert'],'result':'PASS'},indent=2))
