"""Exact finite checks. General analytic claims are proved in affiliation.md."""
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import json

P = tuple(product((0, 1), repeat=2))
def meet(x, y): return tuple(map(min, x, y))
def join(x, y): return tuple(map(max, x, y))
def le(x, y): return all(a <= b for a, b in zip(x, y))
def affiliated(f): return all(f[meet(x,y)] * f[join(x,y)] >= f[x] * f[y] for x in P for y in P)
def monotone(g): return all(not le(x,y) or g[x] <= g[y] for x in P for y in P)
def ce(f, g, event):
    mass = sum(f[x] for x in event)
    return Q(sum(f[x]*g[x] for x in event), mass) if mass else Q(0)

modified = dict(zip(P, (2,1,1,1)))
assert affiliated(modified)
determinant = modified[0,0]*modified[1,1]-modified[0,1]*modified[1,0]
assert determinant == 1

counts = dict(affiliated_weight_vectors=0, monotone_observables=0, comparisons=0)
Gs = [dict(zip(P, vals)) for vals in product((-1,0,1), repeat=4)]
Gs = [g for g in Gs if monotone(g)]
counts['monotone_observables'] = len(Gs)
for vals in product((1,2,3), repeat=4):
    f = dict(zip(P, vals))
    if not affiliated(f): continue
    counts['affiliated_weight_vectors'] += 1
    for g in Gs:
        for i in (0,1):
            slices = {t: [x for x in P if x[i]==t] for t in (0,1)}
            assert ce(f,g,slices[0]) <= ce(f,g,slices[1])
            counts['comparisons'] += 1
            for t in (0,1):
                winning = [x for x in slices[t] if all(xj<=t for xj in x)]
                assert winning
                assert ce(f,g,winning) <= ce(f,g,slices[t])
                counts['comparisons'] += 1

# An interior null modification destroys pointwise affiliation.
c = (Q(1,2),Q(1,2))
y = (Q(1),Q(0))
def interior_density(x):
    if x == c: return Q(2)
    return Q(1) if all(0 <= z <= 1 for z in x) else Q(0)
aff_lhs = interior_density(meet(c,y))*interior_density(join(c,y))
aff_rhs = interior_density(c)*interior_density(y)
assert (aff_lhs, aff_rhs) == (Q(1), Q(2))
# At own signal zero exp(0)=1; rival coordinates 1,2 produce values 1,2.
private_values = [Q(1)+max(Q(0),r-Q(1)) for r in (Q(1),Q(2))]
assert private_values == [Q(1), Q(2)]

# Independent false-negative bound under zero mass: f=0 is not a probability mass.
assert sum(0 for x in P) == 0
result = {
  'pointwise_factorization_obstruction': {
    'f00':2,'f01':1,'f10':1,'f11':1,
    'rectangle_determinant':determinant,'affiliated_on_corners':True,
    'note':'Analytic density is 1 on [0,1]^2 with f(0,0)=2; corner checks do not establish general claims.'},
  'pointwise_affiliation_obstruction': {'x':['1/2','1/2'],'y':[1,0],'meet':['1/2',0],'join':[1,'1/2'],'left_product':int(aff_lhs),'right_product':int(aff_rhs)},
  'private_values_off_support_obstruction':{'own_signal':0,'rival_signals':[1,2],'values':[int(v) for v in private_values]},
  'finite_comparison_checks':counts,
  'arithmetic':'fractions.Fraction; no floating-point calculations',
  'scope':'Finite exhaustive checks only; independent analytic proofs in affiliation.md.'}
out=Path(__file__).with_name('check_finite.output.json')
out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
