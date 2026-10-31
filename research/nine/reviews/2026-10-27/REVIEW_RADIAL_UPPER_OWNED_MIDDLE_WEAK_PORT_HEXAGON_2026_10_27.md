# Independent review: the radial-upper owned-middle weak port theorem

Date: October 27, 2026. Reviewer: hexagon.

**Result: ACCEPTED in its full stated local scope, with no correction.**

Reviewed in full:

    RADIAL_BOUNDARY_UPPER_CONTACT_OWNED_MIDDLE_PORT_EXCLUSION.md
    SHA256 5c53db2bd1d275a80a36abed3a17f0428af76e6f33dfe516f4de74f26d8d833e.

I independently derived the complete support and circle-mask cover,
the weak equality endpoint and the final cubic inequality. I also
read the complete original local proper-concurrence statements in
FIVE_CYCLE_FORCE_POLYGON_DOMAIN.md, Lemma1.1,
TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md, Lemma2.1, and the relevant
full rectangle proofs in C7_FORCE_POLYGON.md, Sections2--5.
The theorem expressly assumes the actual nonparallel proper M2
star rather than assigning a false degree or shortening a neighbor.

## 1. Exact hypotheses and original means

The genuine radial C is [d,d+1]n+[-1/2,1/2]f in the strict-high
window. Its actual CM point is either the inner-upper vertex or
an arbitrary original upper-side mean, including both endpoints.
M is true loaded degree two with actual boundary neighbors B,C.
The actual B-to-M normal g is genuinely M-owned, has positive n
and negative f components, and its original application Q has
positive coordinates and the weak norm bound
|Q|^2<=d^2+1/4.

No force-line length is assumed strictly positive. No conclusion
that a radial M concurrence lies inside M is imported. The source
also keeps either individual radial-C or radial-M corner weight
equal to zero. These distinctions are essential at the weak endpoint.

## 2. Full support cover at the strict C-inner point

I checked the actual frame g=(c,-y),j=(y,c), including the signs
c,y>0. Since g dot h<0, the actual C point has maximum g
coordinate H+1. Its j coordinate K=Xy+c/2 is strictly above
1/2, using X>=d>1 and c+y>1.

For h dot j>0, the minimum-h support is exactly the far-g,
lower-j vertex. Thus the complete original M box and incoming
mean are [H,H+1]g+[K,K+1]j and Q=P-g+beta j,
0<=beta<=1. Both coordinates of P-g and j are strictly
positive. The weak norm bound consequently forces P dot g>=1/2.

If that inequality is strict, H>-1/2 and K>1/2 make P+j
the sole farthest physical corner. I rederived

    R^2-|P+j|^2=2d(1-y)-c>0

from 2dc>1+y. All four corners are therefore clear, with
no omitted orientation or mean endpoint.

At equality the complete chain forces beta=0, Q=P-g and
K=d. This gives the actual radial M rectangle in the source.
The original B proper line keeps q_M dot j=d; the original
C proper line and h dot j>0 force its proper length to be
zero. Hence q_M=P=(1/2,d) in this actual frame. Its ratio
1/(2d) strictly exceeds the full physical radial-M circle-cone
bound 1/[2(d+1)]. This is a valid contradiction for every pair
of nonnegative physical circle weights of positive total.
It does not replace the two-corner resultant by its midpoint.

For h dot j<0, the actual box is the upper-j version.
If H>=-1/2 the farthest corner is P; otherwise it is P-g.
The source's bound P dot g>-1/2 gives
|P-g|^2<d^2+9/4<R^2. I checked both equality support
boundaries, which merely give two equally distant clear corners.
For h dot j=0 the actual normals are opposite and parallel,
contradicting the explicitly retained true-M2 hypothesis.
These are all strict-inner C contact features.

## 3. Full C-owned upper-side interval

The actual point is P=(X,1/2), d<=X<=d+1. Its g,j feature
is the same lower-j vertex. When H<=-1/2, the complete weak
norm chain forces X=d,H=-1/2,beta=0, so it is exactly the
already excluded radial equality endpoint. Otherwise H>-1/2
and K>1/2 make Z=P+j the unique physical circle corner.

Only after that mask has been established does the source use
q_M=XZ/(X+y), and the genuine C proper length is
(Xc-y/2)/(X+y)>0. The original B line preserves j, giving
beta=rho c. I independently obtained the unchanged mean identity

    Q_f=1/2+y+c^2*(Xc-y/2)/(X+y).

The fraction increases with X, with derivative
y(c+1/2)/(X+y)^2>0. For y>=3/4 its first two terms already
give5/4 and the last is positive. For0<y<=3/4 I checked
sqrt(1-y^2)>=1-(2/3)y^2 by its positive squared reserve.
The resulting strict lower comparison is

    Q_f>3/2-y/2-y^2/6+(2/3)y^3>5/4.

The final polynomial really is

    3-6y-2y^2+8y^3
       =1/2-2z+z^2(10+8z),       z=y-1/2.

It is positive on the whole interval -1/2<z<=1/4,
including z=0 and the upper endpoint. The upper bound from
the original weak norm is Q_f<23/20, with exact squared
reserve7/180 against d^2+1/4. The contradiction includes
the entire original X interval and all beta endpoints.

## 4. Scope conclusion

The full local theorem is sound. It includes every actual M
frame and physical mask, the weak radial-inner-corner norm
endpoint, both C physical corner weights, both original proper
lengths and all actual side means. Its use of a genuine incoming
M owner is essential and is correctly left to each caller.
It does not assert that an arbitrary point normal may be changed
to an M axis, or that the signs and weak norm hold at an
arbitrary contact.

This review accepts the complete stated theorem, not an unstated
whole S123 caller. No proof text, shared metadata, normal choice,
compiled artifact or remote state was changed during the audit.
