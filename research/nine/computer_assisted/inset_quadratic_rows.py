"""Exact affine consequences of the universal quadratic inset-separation family.

Every supplied interval must be proved for the same original pair.
No optimizer is imported. All arithmetic is rational.
"""
from fractions import Fraction as F
from itertools import combinations

PARAMETERS=tuple(map(F,('-7/8','-3/4','-1/2','-1/4','0','1/4','1/2','3/4','7/8')))

def inset_ellipse_rows(positions,scalar,differences=None,parameters=PARAMETERS):
    positions=tuple(tuple(map(F,x)) for x in positions)
    scalar=tuple(tuple(map(F,x)) for x in scalar)
    assert len(positions)==18 and len(scalar)==36
    assert all(l<=u for l,u in positions+scalar)
    rows=[]
    for i,j in combinations(range(9),2):
        if differences is None:
            dr=[(positions[2*j+k][0]-positions[2*i+k][1],positions[2*j+k][1]-positions[2*i+k][0]) for k in (0,1)]
        else:dr=[tuple(map(F,x)) for x in differences[(i,j)]]
        (xl,xu),(yl,yu)=dr
        gl=scalar[27+i][0]+scalar[27+j][0]
        gu=scalar[27+i][1]+scalar[27+j][1]
        assert 0<gl<=gu
        tangents=sorted({gl,(gl+gu)/2,gu,F(1)})
        for t in map(F,parameters):
            assert -1<=t<=1
            rad=1-t*t
            # q = (1-t)/2 * (dx+dy)^2 + (1+t)/2 * (dx-dy)^2.
            ul,uu=xl+yl,xu+yu;vl,vu=xl-yu,xu-yl
            a,b=(1-t)/2,(1+t)/2
            upper=[(a*(ul+uu)+b*(vl+vu),a*(ul+uu)-b*(vl+vu),-a*ul*uu-b*vl*vu,'rotated')]
            # Direct secants for dx^2,dy^2 plus either product envelope.
            if t>=0:
                products=[(yl,xl,-xl*yl),(yu,xu,-xu*yu)]
            else:
                products=[(yl,xu,-xu*yl),(yu,xl,-xl*yu)]
            for k,(px,py,pc) in enumerate(products):
                upper.append((xl+xu-2*t*px,yl+yu-2*t*py,-xl*xu-yl*yu-2*t*pc,'product'+str(k)))
            for c in tangents:
                for ux,uy,constant,kind in upper:
                    co={2*i:ux,2*j:-ux,2*i+1:uy,2*j+1:-uy,45+i:2*rad*c,45+j:2*rad*c}
                    row=tuple((k,v) for k,v in sorted(co.items()) if v)
                    rhs=rad*c*c+constant
                    name=f'inset_ellipse_{i}_{j}_{t}_{c}_{kind}'
                    rows.append((row,rhs,name))
    return rows
