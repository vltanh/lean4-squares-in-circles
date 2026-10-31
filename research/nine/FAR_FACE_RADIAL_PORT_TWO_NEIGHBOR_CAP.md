# Two radial proper ports on a face of height at least 59/60 are impossible

Date: October 27, 2026.

**Status: complete hand geometric cap theorem, submitted for full root
and separate independent review.** The exact aligned S-side C4 caller
below closes its whole common-far-face domain. Its opposite-vertex
domain remains explicitly separate.

All original unit squares are interior-disjoint and contained in the
original radius window R<=sqrt(1105)/16. Put

    d=sqrt(R^2-1/4)-1<61/60,       M_*=91/60.

Every actual unit center has norm less than M_*, and an actual unit
beyond support h requires h<=d. Keep every physical square, normal,
contact application, circle mask and individual zero weight.

## 1. A uniform cap for one actual supported neighbor

Suppose an actual unit T lies beyond an actual unit normal n=(c,s),
where c>0, at a support of height h satisfying

    h>=A/c,       A=59/60.                              (1)

Write C=(x,y) for T's actual center. Its halfwidth in direction n
is at least 1/2, so

    C.n>=h+1/2,       |C|<M_*.                          (2)

**Claim.** With L_0=sqrt(M_*^2-1/4), necessarily x>L_0.

Indeed h<=d and (1) give c>59/61. Reflect vertically for this
calculation so s>=0; the conclusion about x is unchanged. If x<=L_0,
the maximum of the linear functional n.C over the closed disk
|C|<=M_* cut by x<=L_0 occurs at (L_0,1/2). The unconstrained disk
maximizer has first coordinate M_*c>L_0, and the positive second
component picks the upper cut endpoint. This argument includes s=0.
Consequently (1)--(2) imply

    A <= c(C.n-1/2)
       <= L_0 c^2+(s-1)c/2.                            (3)

Here is a short exact bound excluding (3), with no numerical sign
certificate. Set

    L=179/125>L_0,       K=61/240.

The first strict comparison follows from
L^2-L_0^2=779/2250000. Since c>=59/61 and c^2+s^2=1,

    c=1-s^2/(1+c) >= 1-(61/120)s^2.

Multiplying this lower bound by the nonpositive (s-1)/2 and using
c^2=1-s^2 gives

    L_0 c^2+(s-1)c/2
       <L-1/2+s/2-(L-K)s^2-Ks^3.                     (4)

For every s>=0 the elementary factorization

    s^3-(3/25)s+2/125=(s-1/5)^2(s+2/5)>=0

bounds (4) above by the concave quadratic

    14041/15000 +(939/2000)s -(7067/6000)s^2.

Completing its square bounds it by

    833499421/848040000
       =59/60-406579/848040000 <A.                      (5)

This contradicts (3), proving the claim. For completeness the
unconstrained maximizer comparison used above follows from
M_*c>(91/60)(59/61)>179/125>L_0; thus no additional angular
subcase was omitted.

## 2. Two such actual centers cannot coexist

The circular cap

    {C: |C|<M_*, C_x>L_0}

has diameter strictly less than one. Its limiting chord has endpoints
(L_0,1/2),(L_0,-1/2) and length one. Since L_0>M_*/sqrt(2), the
cap's circular arc is shorter than a semicircle; its most distant
boundary pair is precisely those chord endpoints. One can see this
directly by maximizing a convex distance function first on the two
boundary pieces: on the straight chord its maximum is at an endpoint,
and on the short circle arc any two points subtend no greater angle
than the endpoints. The actual strict cap omits those extremizers.

Thus any two actual neighbors satisfying (1), with their respective
normals c>0, have center distance less than one. This is impossible
for two interior-disjoint unit squares: their open incircles of
radius 1/2 would overlap.

This is a uniform geometric theorem. The actual normals need not
be equal or side axes; the units need not carry circle force. Only
their original support inequalities and their actual containment
were used.

## 3. The radial proper-port hypothesis supplies exactly (1)

Let K have a face x=A_0 with A_0>=59/60. Suppose two distinct actual
neighbors have ports P_i=(A_0,y_i), outward normals n_i=(c_i,s_i)
with c_i>0, and actual force lines passing through the point

    q=(-t,0),       t>=0,

with proper ports P_i=q+l_i n_i, l_i>0. These are real geometric
applications and directions, not chosen replacement normals.
Then l_i c_i=A_0+t and y_i=l_i s_i. The support of K at that port is

    h_i=A_0 c_i+y_i s_i
        =A_0/c_i+t s_i^2/c_i >=(59/60)/c_i.

Both actual neighboring units therefore satisfy (1). Sections 1--2
give a contradiction. This proves the stated two-port theorem,
including t=0, horizontal normals and actual side-mean endpoints.

For two equal side-axis normals the same conclusion is even more
direct: both centers have x>=59/60+1/2=89/60, and the corresponding
disk cap has limiting chord length
2sqrt((91/60)^2-(89/60)^2)=2/sqrt(10)<1.

## 4. Exact aligned S-side four-cycle arm consequence

Keep the original C4 H--B--C--D--H and arm H--X--L of
FOUR_CYCLE_SIDE_ARM_TILTED_ROOT_EXCLUSION.md. Its private-load
alternatives are LBD or LBCD, and its true root keeps all three
positive forces. The remaining S-side arm has

    d=1+epsilon, 0<=epsilon<1/60,
    p_HX=epsilon e_x,
    H=[epsilon-1,epsilon] times [h-1,h], 0<=h<=1.

The complete local C4 concurrence theorem and the actual arm point
give strict properness at both root ports, as proved in Section 1
of that source. In the nonparallel case their actual concurrence is
q=(s,0), s>0. If both original ports lie on H's left face with
negative first normal components, reflect the horizontal coordinate.
The hypotheses of Section 3 then hold with A_0=1-epsilon>59/60
and t=s>0. This entire common-far-face family is impossible.

The opposite parallel root normals are already excluded by the
actual private-block equations. Equal parallel normals are both
west, and their distinct actual ports make west an H-owned side;
the direct cap at the end of Section 3 excludes them as well.

The genuine aligned opposite-vertex alternative, including its
possible own-axis endpoint, is outside this common-face hypothesis.
It has not been deleted, replaced by a triangle, or declared closed
here. No whole LBD/LBCD S-side gate or larger coarse cell is claimed.

No Lean compilation, CI, numerical pose, post-certificate normal
change, remote action or shared-ledger edit is used.
