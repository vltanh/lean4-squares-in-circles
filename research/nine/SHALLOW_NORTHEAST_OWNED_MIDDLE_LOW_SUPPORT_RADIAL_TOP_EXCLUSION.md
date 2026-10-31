# A shallow Northeast owned side at low support cannot return to the radial upper face

Date: October 29, 2026 UTC. Author: root continuation.

**Status: complete proposed force-free hand theorem, frozen for a separate
complete independent review.** This is an actual-unit statement, at arbitrary
true degree and with no equilibrium or circle-weight premise. It includes the
horizontal incoming direction, both endpoints of the slope bound, every
original side mean and both physical circle-mask sizes. The entire closed
support and radius intervals in the statement are retained.

## 1. Exact whole-unit statement

Use one unchanged orthonormal frame n,f about the actual circle origin O.
Let

    1<=d<=61/60,
    R^2=(d+1)^2+1/4,
    C=[d,d+1]n+[-1/2,1/2]f.

Let M be another actual unit square contained in the same closed disk,
with its open interior disjoint from C. Suppose M physically touches
the containing circle. No positivity assumption is made on either body's
circle coefficients; no degree or force equation is assumed at either body.

Suppose an unchanged actual incoming unit normal g is owned by M and
points into M at its actual application or full side mean Q. Write

    g=c*n+s*f,
    c>0, s>=0, c^2+s^2=1, 0<=s/c<=1/3,
    H=min_{z in M} z.g=Q.g,
    0<=H<=1/7.                                           (1)

The ownership says exactly that g is one of M's inward own axes at its
whole minimum-g face. No original point is moved along that face.

Assume the actual C--M contact has its unchanged unit common normal h,
directed from C into M, with

    h_f>0, h_n<=0.                                       (2)

Its original point or full shared-side mean P is consequently in the
complete actual C support

    h_n<0: P=(d,1/2);
    h_n=0: h=f, P=(X,1/2), d<=X<=d+1.                   (3)

**Theorem.** These actual physical data are impossible.

The conclusion is independent of any actual B that supplied g, all other
neighbors and all other units. Such units and every original force may
remain. The only use of circle contact at M will be to contradict a whole
four-corner bound; no unique-mask assumption or inside concurrence is used.

## 2. The complete own-frame support cover

Put j=-s*n+c*f. This is the other proper own axis of M. The complete
closed cone in (1) gives

    c>=3/sqrt(10)>9/10,
    0<=s<=1/sqrt(10)<1/3,
    c>s.                                                (4)

For the strict comparisons, 9/10<3/sqrt(10) follows by squaring
81/100<9/10, and 1/sqrt(10)<1/3 follows from 9<10.
The source slope s/c=1/3 therefore remains inside all later estimates.

From (2),

    h.j=-h_n*s+h_f*c>0.                                 (5)

Thus P is always on the lower-j face of M. The complete possibilities
are h.g<0, h.g>0 and h.g=0. The first two force P to the far-g or
near-g endpoint of that face; equality retains its whole actual interval.
These are support consequences of the original normal, not a new choice.

## 3. A negative h.g makes the whole actual M circle-clear

If h.g<0, then h_n cannot be zero, since h=f would give h.g=s>=0.
Consequently P=(d,1/2) is the original strict C inner corner. Define

    D=P.g=d*c+s/2,
    K=P.j=-d*s+c/2.

The full bounds (4) and 1<=d<=61/60 give

    D>9/10>1/2,
    1/9<K<=1/2.                                        (6)

Indeed K>-(61/60)/3+(9/10)/2=1/9. The maximum-support
coordinates of the actual square are fixed by (5) and h.g<0:

    M=[D-1,D]g+[K,K+1]j.

Since D>1/2 and K>0, the unique farthest corner is P+j. Its norm
satisfies the whole bound

    |P+j|^2=|P|^2+1+2K
             <=d^2+9/4
             =R^2-(2d-1)
             <=R^2-1.                                (7)

All four actual corners lie strictly inside the circle. Convexity puts
the whole square strictly inside as well, contradicting the physical
circle contact. This covers every actual Q on its complete owned side.

## 4. A positive h.g puts an actual M corner outside the circle

If h.g>0, the same original support makes P the near-g, lower-j vertex:

    M=P+[0,1]g+[0,1]j,
    P=(X,1/2), d<=X<=d+1.

Here X=d in the strict C-inner case, and the entire X interval is retained
in the C-owned upper-side case. The actual opposite corner is

    Z=P+g+j=(X+c-s,1/2+s+c).

Since c>s and X>=d>0, its squared norm increases with X. Therefore

    |Z|^2-R^2
       >=1-2d+(2d+1)c+(1-2d)s
       >-31/30+27/10-31/90
       =119/90>0.                                    (8)

The strict middle comparison uses d<=61/60, 2d+1>=3,
c>9/10 and s<1/3. In particular the coefficient 1-2d is
negative; its lower estimate is -(31/30)(1/3), in the correct
direction. Every displayed bound includes d=1, d=61/60 and s=0.

Thus this actual corner of M is outside the unchanged containing circle.
No assumption on M's circle mask or selected circle weights was needed.

## 5. The exact perpendicular endpoint retains the entire side mean

If h.g=0, (5) and unit normalization force the original h=j. If s>0,
then h_n=-s<0, so P=(d,1/2). If s=0, then c=1, h=f and P may be
any original (X,1/2) with d<=X<=d+1. In both cases its actual j
coordinate K satisfies

    1/9<K<=1/2,

by (6) when s>0 and by K=1/2 when s=0. Since h is the original
inward j axis at P, the whole actual square is exactly

    M=[H,H+1]g+[K,K+1]j.                              (9)

The original P may lie anywhere on its lower-j side. Neither that mean
nor the original incoming mean Q is fixed to an endpoint. The hypothesis
0<=H<=1/7 and K>0 makes the far-g, far-j corner farthest in norm. The
entire four-corner bound is

    max_{z in M}|z|^2
       =(H+1)^2+(K+1)^2
       <=64/49+9/4
       =697/196
       =17/4-34/49
       <=R^2-34/49.                                  (10)

This contradicts physical circle contact at M. In particular the equality
h.g=0 is proved directly on the whole actual mean interval. It is not
discarded as a parallel or limiting case and does not require a force
nonparallelity premise.

## 6. Complete preservation and dependency boundary

Sections 3--5 exhaust the sign of the unchanged original h.g. They prove
the theorem throughout the continuous closed domains in (1)--(3). The
only algebraic bounds are (4), (6)--(8) and (10), printed with explicit
strict reserves. No numerical pose, angle mesh or exclusion tree is used.

This proof is self-contained from the exact actual-unit and support
hypotheses in Section 1. It imports no smaller star, physical corner-mask
classification, concurrence, finite certificate or original graph-family
conclusion. Arbitrary additional actual neighbors, all their full forces
and every individual zero circle coefficient remain. A literal original
caller must establish the small actual minimum-g support, the original
M owner and the complete C support; none is inferred for an arbitrary
contact merely because it has a similar drawing.

This is a new local hand exclusion, not a whole original fine or coarse
flag closure. It declares no computational packet retired by itself.
No normal reselection, replaced mean, force deletion, graph contraction,
Lean/Lake, CI/workflow, metadata edit, staging, commit or remote operation
is used. These exact proposed bytes require a separate complete independent
review and full root adoption before they become an operative new input.
