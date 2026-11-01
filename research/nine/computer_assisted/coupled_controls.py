from fractions import Fraction as F
from itertools import combinations
from square_pose_independent import require,CELLS
from test_hex_root_emitter import K
def ka(x):return x if x>=0 else -x

def witness_checks(g,perms):
    m=g['m'];k=g['k'];states={(t,o):v for v,(c,t,o) in enumerate(g['states'])}
    by_cell=[[] for c in CELLS]
    vertices=[]
    for t,(c,tri) in enumerate(g['triangles']):
        by_cell[c].append(t)
        vertices.append([(K(F(49*X,200*m)),K(0,F(49*Y,200*m))) for X,Y in tri])
    def contained(p,t):
        signs=[]
        for i in range(3):
            a,b=vertices[t][i],vertices[t][(i+1)%3]
            signs.append(((b[0]-a[0])*(p[1]-a[1])-(b[1]-a[1])*(p[0]-a[0])).sign())
        return min(signs)>=0 or max(signs)<=0
    def locate(pose,cell=None):
        x,y,a,b=pose
        for _ in range(4):
            if a>=0 and b>=0:break
            a,b=-b,a
        require(a>=0 and b>=0 and a*a+b*b==1,'normalized frame')
        angles=[o for o in range(k) if K(o)*(1+a)<=k*b<=K(o+1)*(1+a)]
        require(angles,'uncovered angle')
        if cell is None:
            X=x*F(200,49);Y=y*K(0,F(200,147))
            choices=[c for c,(q,r) in enumerate(CELLS)
                     if ka(Y-(q+2*r))<=1 and ka(X+Y-(4*q+2*r))<=2 and ka(X-Y-(2*q-2*r))<=2]
        else:choices=[cell]
        require(choices,'uncovered center cell')
        selected=[]
        for c in choices:
            for t in by_cell[c]:
                if contained((x,y),t):
                    for o in angles:
                        require((t,o) in states,'valid pose removed by unary filter')
                        require(g['groups'][c] >> states[t,o] & 1,'valid pose removed by contraction')
                        selected.append(states[t,o])
        require(selected,'uncovered actual pose')
        return min(selected)
    def check_pose(p):
        x,y,a,b=p
        require(a*a+b*b==1,'nonunit witness')
        for s in (-1,1):
            for t in (-1,1):
                X=x+F(1,2)*(s*a-t*b);Y=y+F(1,2)*(s*b+t*a)
                require(X*X+Y*Y<=K(F(1105,256)),'escaped witness corner')
    centers=[(F(x,2),F(1,16)) for x in (-3,-1,1,3)]
    centers += [(F(x),-F(15,16)) for x in (-1,0,1)]
    centers += [(F(x,20),F(19,16)) for x in (-11,11)]
    poses=[tuple(map(K,(x,y,F(1) if i<7 else F(99,101),F(0) if i<7 else F(20,101))))
           for i,(x,y) in enumerate(centers)]
    occupied=[1,5,14,17,3,8,12,6,15]
    def rot(x,y):return F(1,2)*x-K(0,F(1,2))*y,K(0,F(1,2))*x+F(1,2)*y
    for si,perm in enumerate(perms):
        chosen=[]
        for cell,pose in zip(occupied,poses):
            x,y,a,b=pose
            if si>=6:y,b=-y,-b
            for _ in range(si%6):x,y=rot(x,y);a,b=rot(a,b)
            check_pose((x,y,a,b));chosen.append(locate((x,y,a,b),perm[cell]))
        for v,w in combinations(chosen,2):require(g['adjacency'][v]>>w&1,'equality witness edge removed')
    touching=0
    for t in [F(i,2*k) for i in range(2*k+1)]:
        a,b=K((1-t*t)/(1+t*t)),K(2*t/(1+t*t))
        p=(-F(1,2)*a,-F(1,2)*b,a,b);q=(F(1,2)*a,F(1,2)*b,a,b)
        check_pose(p);check_pose(q)
        v,w=locate(p),locate(q)
        require(g['adjacency'][v]>>w&1,'weak touching pair removed')
        touching+=1
    oblique=0
    for i in range(k+1):
        t=F(i,k);w=F((i+3)%(k+1),k)
        a,b=K((1-t*t)/(1+t*t)),K(2*t/(1+t*t))
        A,B=K((1-w*w)/(1+w*w)),K(2*w/(1+w*w))
        h=(K(1)+ka(a*A+b*B)+ka(a*B-b*A))*F(1,2)
        p=(-F(1,2)*h*a,-F(1,2)*h*b,a,b)
        q=( F(1,2)*h*a, F(1,2)*h*b,A,B)
        check_pose(p);check_pose(q)
        v,z=locate(p),locate(q)
        require(g['adjacency'][v]>>z&1,'nonparallel weak pair removed')
        oblique+=1
    return {'nonparallel_touching_pair_controls':oblique,'equality_symmetries':12,'equality_pair_controls':432,
            'touching_pair_controls':touching,'all_angle_endpoints_retained':True}
