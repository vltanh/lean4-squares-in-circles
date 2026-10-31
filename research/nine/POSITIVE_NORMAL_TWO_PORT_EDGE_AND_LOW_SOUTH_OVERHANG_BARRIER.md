# A positive-normal two-port edge lemma and a complete low southern overhang barrier

Date: October 28, 2026 UTC. Author: root continuation, with the
preliminary c<=s application identified jointly with roof_resume.

**Status: complete new hand theorems, frozen for full separate independent
review.** The first theorem is a radius-free support fact for any actual
unit square. The second controls the entire possible overhang of an actual
hub whose two original supports are Southwest. It excludes a whole
parameter domain without choosing a hub owner or reducing its degree.
No whole original family, fine flag or coarse flag is declared closed.

All physical squares and support points below are actual unchanged units
and actual points of the same packing. An original shared mean remains
that point in its whole support face. No pair force, other neighbor or
circle coefficient is discarded. The geometric lemmas themselves do not
use force or torque equations.

## 1. Radius-free positive-normal two-port edge theorem

Let K be an actual unit square. Let m,j be nonzero directions, P,Q
actual points of K, and suppose

    P minimizes m on K,
    Q minimizes j on K,
    m dot j>0,
    j dot(P-Q)>0.                                  (1)

Then Q is a unique minimum-j vertex of K. The point P lies on one
of the two actual unit edges issuing from Q, at a strictly positive
distance at most one. This includes P at the far vertex and every
relative interior point of that edge.

Here is the full own-axis cover. If j were an own-axis direction,
the positive component m dot j would force every minimum-m point
to be on the same minimum-j side as Q. That contradicts the last
inequality in (1), so j is not an own-axis direction. Its minimum
is consequently a unique actual vertex Q. Write the two actual
inward orthonormal edges there as u,w. Then

    j dot u>0, j dot w>0.

If both m components in this basis were nonpositive, with at least
one negative, m dot j would be negative. This is excluded by (1).
If both m components were positive, its minimum would be Q,
contrary to j dot(P-Q)>0. The complete remaining cases are:

* One m component is negative and the other is positive. Its
  actual minimum is the far endpoint of the edge in the negative
  component's direction.
* One m component is zero and the other is positive. Its entire
  minimum side is the corresponding edge from Q. The last
  condition in (1) excludes Q itself but retains all other points.

These cases cover every nonzero m, including its own-axis endpoints.
In particular the opposite vertex and both opposite sides are excluded
by the positive dot product; an actual side mean is not replaced by
a chosen endpoint. This proves the theorem for every frame.

## 2. The literal low southern-page domain

Use the unchanged actual squares and the complete closed chart

    2<=R<=sqrt(17)/2,
    d=sqrt(R^2-1/4)-1, e=d-1,
    29/50<=a<=2/3, b=a-1,
    X=[e,d] times [b,a],
    L=[d,d+1] times [-1/2,1/2].                    (2)

Let an actual physical boundary square D be contained in y<=b and
touch X at its unchanged point Q_D=(x_D,b), e<=x_D<=d. Its
degree, load and all other neighbors are unrestricted.

The exact accepted physical theorem

    LOW_ALIGNED_S_ROOT_NINE_TWENTY_FIFTHS_DEPTH_AND_ONE_THIRD_RETURN_BOUND.md
    SHA256 2ec526fdeac85ff3949bfa891932a9a229b2cc464267dbbd7d874cc6f33cdd7e

proves throughout this complete domain

    14/15<d<=1, -1/15<e<=0,
    x_D>2/5,
    D=Q_D+[0,1](r,-s_D)+[0,1](-s_D,-r),
    r,s_D>0, r^2+s_D^2=1, q=r/s_D>9/10.           (3)

That theorem already covers every physical D frame and original
side-mean endpoint. It retains all physical circle masks, including
zero individual coefficients. No degree-two assertion about D is
used in the present proof.

Its literal radius-free wall-span input, used separately here, is

    LOW_ALIGNED_S_ROOT_SOUTH_BOUNDARY_DEPTH_AND_WALL_SPAN_BARRIER.md
    SHA256 4e4967d248c5d0d7375622297913fa9c166cbd8a8328c798bae7680a84bcb2ce

Section 5. For every actual unit K contained in x<=E and every
actual M in K it gives

    min_K y>=M_x+M_y-E-1.                          (4)

This inequality is weak at aligned frames, so no tilted strictness
is assumed for a general caller.

One immediate extension of (3), needed below, holds for every
epsilon with 0<=epsilon<2/5. Every actual Y in D with
Y_x<=e+epsilon obeys

    Y_y<b-9/25+(9/10)epsilon.                     (5)

Indeed, writing Y=Q_D+u(r,-s_D)+v_D(-s_D,-r) with
0<=u,v_D<=1 yields

    Y_y<=b-q(x_D-Y_x)-u/s_D
        <=b-q(x_D-e-epsilon).

The factor x_D-e-epsilon>2/5-epsilon>0. By q>9/10 and
x_D-e>2/5 the last expression is strictly less than the right
side of (5). This is an assertion about the whole closed part of D,
including every contact point, endpoint or original mean there.

## 3. Complete original two-support hub statement

Set N=(e,a) and P=(e,b). Let K be any actual unit square in
the original packing, with two unchanged supports as follows:

    m=(-xi,-eta), xi,eta>0, xi^2+eta^2=1,
    P belongs to K and minimizes m on K;

    n=(-c,s), j=(-s,-c),
    c,s>=0, c^2+s^2=1,
    0<=t<=1, 0<=v<1/8, c>v,
    M=N+t*n+v*j belongs to K and minimizes j on K. (6)

The point P may be a relative interior side point or a vertex of K.
No owner or free-normal class is prescribed. M is its original actual
minimum-j application, including any potential support mean. Suppose
also that K physically touches the actual D in (2)--(3).

**Preliminary theorem.** These hypotheses alone imply c>s.

**Complete barrier theorem.** If in addition the unchanged scalar
parameters satisfy

    t<1/3,
    whenever k=c-s>=0, v<=(1-k)/4,                 (7)

then the entire feature (6) is impossible.

The scalar conditions (6)--(7) are literal premises. This theorem
does not supply an upper page's force equation, an equality t=ell,
or a missing inequality for v. It preserves all original K forces
and allows arbitrary true degree, other neighbors and circle masks.
It also does not assume K is wholly left of x=e. The complete
possible overhang will be computed from its actual frame.

## 4. The same adjacent-edge frame covers every hub owner and mean

The two directions in (6) have

    m dot j=xi*s+eta*c>0,
    j dot(P-M)=c-v>0.                             (8)

Thus Section 1 applies to this actual K: M is its unique
minimum-j vertex, and P belongs to one adjacent unit edge.
Put

    S=tc+vs>=0,
    H=1+ts-vc>7/8,
    zeta=sqrt(S^2+H^2).

The exact contact difference is

    M-P=(-S,H), 0<zeta<=1.                        (9)

The inward edge at M directed toward P is (S,-H)/zeta.
Its dot product with j is (c-v)/zeta>0, as it must be.
The perpendicular candidate (H,S)/zeta has negative dot product
with j, so cannot be the other inward edge at a minimum-j vertex.
The complete actual frame of K is therefore exactly

    K=M+[0,1](S,-H)/zeta+[0,1](-H,-S)/zeta.       (10)

This includes S=0, all frame axes, zeta=1 and every 0<zeta<1
side position of the unchanged P. It was derived from the two actual
supports, with no assumption of a K-owned root contact.

Its whole maximum x coordinate is

    max_K x=M_x+S/zeta=e+epsilon,
    epsilon=S(1/zeta-1)>=0.                      (11)

Let

    delta=1-H=vc-ts,
    k=c-s, w=c+s,
    B_0=tk+vw=S+delta.                           (12)

Since H<=zeta<=1, one has

    0<=delta<=vc<=v<1/8,
    epsilon<=S*delta/(1-delta).                  (13)

The equality delta=vc-ts retains all original t and v endpoints.
The full wall bound (4) at E=e+epsilon, applied to the actual
point M, now yields

    min_K y>=M_x+M_y-(e+epsilon)-1
            =b-B_0-epsilon.                     (14)

Whenever epsilon<2/5 and

    B_0+(19/10)epsilon<9/25,                     (15)

every K point has height greater than b-9/25+(9/10)epsilon.
But every D point with x<=max_K x has strictly smaller height
by (5). Then K and D cannot meet. Thus it suffices to prove
(15) on each complete domain below. This argument retains the
whole actual overhang, rather than applying (4) at a false wall.

## 5. The entire c<=s range is impossible before any one-third force bound

Suppose c<=s. Then s>0, and (12)--(13) give

    ts<=vc, hence 0<=t<=v*c/s<=v.

Consequently

    B_0=tk+vw<=v*w<=v*sqrt(2),
    S=tc+vs<=v*w<=v*sqrt(2),
    0<=delta<=v.

It follows from (13) that

    epsilon<=v^2*sqrt(2)/(1-v)<sqrt(2)/56<2/5.     (16)

Moreover

    B_0+(19/10)epsilon
       <=v*sqrt(2)*(1+(19/10)*v/(1-v))
       <(sqrt(2)/8)*(1+19/70)
        =89*sqrt(2)/560<9/25.                    (17)

For a fully rational last comparison use sqrt(2)<17/12:
89*sqrt(2)/560<1513/6720<9/25, with reserve
4531/33600. The rational function of v is increasing on
0<=v<1, so its strict bound at v=1/8 covers every endpoint,
including v=0. Then (15) contradicts the actual KD contact.

This proves the preliminary theorem c>s. It did not require
t<1/3, a proper-concurrence formula, any original equation at K,
or any statement about the upper page's additional neighbor.

## 6. The complete remaining interval with the one-third bound

Now impose (7) and retain the already necessary c>s, so
0<k<=1 and 0<=v<1/8. The general overhang estimate is harmless:

    S<=t+v<11/24,
    0<=delta<=v<1/8,
    epsilon<=S*delta/(1-delta)<11/168<2/5.        (18)

If s=0, then c=k=1 and (7) gives v=0. The exact zeta in (9)
is sqrt(1+t^2)<=1, so t=0. Thus B_0=epsilon=0 and (15) holds.
This covers the complete axis endpoint.

Assume henceforth s>0, so 0<k<1. The exact identities in (12)
give, with no division by an unknown sign,

    t=(vc-delta)/s,
    S=(v-c*delta)/s,
    B_0=(v-k*delta)/s.                            (19)

### 6.1. The whole range k>=(19/10)v

Substituting (19) into (13) yields

    B_0+(19/10)epsilon
       <=v/s
         +delta*[(19/10)v-k-((19/10)c-k)*delta]
                    /[s*(1-delta)]
       <=v/s.                                    (20)

The last numerator is nonpositive: its first two terms satisfy
(19/10)v-k<=0 and its remaining coefficient is

    (19/10)c-k=(9/10)c+s>0.

This includes delta=0 and equality k=(19/10)v.

For 0<k<=1/2,

    s=(sqrt(2-k^2)-k)/2
      >=(sqrt(7)-1)/4,
    v/s< (sqrt(7)+1)/12<1/3.                      (21)

The strict first ratio bound uses v<1/8, and sqrt(7)<3 proves
the last comparison.

For 1/2<=k<1 use the extra v condition in (7):

    v/s<=(1-k)/(2*(w-k))
         =(w+k)/(4*(1+k)), w=sqrt(2-k^2).         (22)

The final function has exact derivative

    (w-2-k)/(4*w*(1+k)^2)<0.

Thus its maximum on that whole interval is its value at k=1/2,
namely (sqrt(7)+1)/12<1/3. Combining (20)--(22) gives

    B_0+(19/10)epsilon<1/3<9/25.                  (23)

The overlap at k=1/2, the equality in (7), and the v=0 endpoint
remain. The complete axis k=1 was already covered directly.

### 6.2. The whole range 0<k<(19/10)v

Here v>0 and k<19/80. Since w<=sqrt(2)<17/12,

    s^2=(1-k*w)/2>637/1920>16/49,
    s>4/7, c<6/7.                                (24)

The middle exact reserve is 493/94080. The upper c bound follows
from c^2<33/49<36/49.

The positive k in this range and (19) give

    B_0<=v/s<7v/4,
    S<=v/s<7v/4,
    delta<=vc<6v/7,
    1/(1-delta)<8/7.

Using (13),

    epsilon<12v^2/7.

Therefore throughout the full range,

    B_0+(19/10)epsilon
       <7v/4+(114/35)v^2
       <=(151/70)v
       <151/560<9/25.                            (25)

The quadratic relaxation uses v<=1/8 and the final exact reserve
is 253/2800. The dividing boundary k=(19/10)v belongs to the
previous closed range, so no case is omitted.

The two complete ranges establish (15). With (5), (14) and the
actual KD contact this is the required contradiction. The complete
barrier theorem is proved for every stated parameter, frame,
support face, original side mean and endpoint.

## 7. Literal uses, dependencies and preservation

The radius-free first theorem can be used independently of the low
chart, without any circle, degree or contact-graph assumptions. Its
positive dot product and strict j separation are actual hypotheses,
not consequences of a diagram.

For the low barrier, a caller must establish the actual complete chart
(2), physical southern page D, both actual minimum supports in (6),
c>v, and the indicated scalar conditions. The preliminary c>s theorem
needs only (6) and the KD contact; the complete contradiction also needs
(7). An application to a higher-degree loaded upper page must prove its
own t bound from that entire original star. This source does not replace
it by a true degree-two star.

The following are the only operative earlier inputs:

| Exact source | SHA256 | Literal use |
| --- | --- | --- |
| LOW_ALIGNED_S_ROOT_NINE_TWENTY_FIFTHS_DEPTH_AND_ONE_THIRD_RETURN_BOUND.md | 2ec526fdeac85ff3949bfa891932a9a229b2cc464267dbbd7d874cc6f33cdd7e | Whole physical southern-page chart, actual tilt, x_D>2/5 and q>9/10; no force-bound assertion is imported without a caller |
| LOW_ALIGNED_S_ROOT_SOUTH_BOUNDARY_DEPTH_AND_WALL_SPAN_BARRIER.md | 4e4967d248c5d0d7375622297913fa9c166cbd8a8328c798bae7680a84bcb2ce | Complete radius-free wall-span inequality, including aligned frames and arbitrary actual points |

The new positive-normal edge cover, exact full K frame, all overhang
estimates and complete scalar interval proofs are written above. The
actual West-hub and strict-Southwest fan proofs are not inputs; there
is no circular use of a caller. The preliminary no-t-bound estimate
in Section 5 was recognized jointly with the roof author; its independent
review must be supplied by a reviewer who did not help discover it.

No numerical pose, angular sample, optimization, replacement square,
changed normal, moved mean, deleted force, Lean/Lake build, CI, workflow,
old-source edit, metadata change or original gate change was used.
Whole original-family closure and its separate reviewed union remain
additional work.

