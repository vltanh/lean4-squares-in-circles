# The high-square chord barrier allows a signed small right support

Date: October 28, 2026 UTC. Author: roof_uniform continuation.

**Status: complete proposed force-free strengthening, frozen for separate
full independent and root review.** The former h<=0 barrier stays at its
original bytes. The present proof allows every h<=epsilon in the entire
high/critical radius window. It changes no original family flag.

## 1. Complete actual statement

Let actual unit squares H,B have disjoint open interiors and be contained
in the same circle about the unchanged origin, with

    R^2=(2+epsilon)^2+1/4<=1105/256,
    0<=epsilon<1/60.

Suppose

    H=[h-1,h] times [g-1,g],
    h<=epsilon, 37/50<=g<=1.                         (1)

Then the same actual B cannot contain points P,V with

    P_x<h, P_y<7/10,
    h-1<=V_x<=h, V_y>=g.                            (2)

Both horizontal V endpoints and equality V_y=g are retained. There is
no degree, circle-load, physical circle-contact, mask or original HB
edge premise. The proof moves no body or application and selects no
new force normal.

## 2. A full unit cap at support at least 1-epsilon

The complete force-free high-strip theorem gives, for any actual unit
T lying in x>=1-epsilon,

    89/60<(c_T)_x<91/60, |(c_T)_y|<3/25.             (3)

Its full proof is Section 1 of the exact source pinned below. It keeps
both signs of tilt, the aligned case, every physical mask and every
original side point. No conclusion from its separate two-unit theorem
is imported here.

The actual horizontal width w of T satisfies

    w/2=(c_T)_x-min_T x
           <=(d+1/2)-(1-epsilon)
            =1/2+2*epsilon<8/15,
    d=1+epsilon.

A unit square has equal widths in two orthogonal coordinate directions:
both equal |cos(theta)|+|sin(theta)| in its own frame. Hence (3) implies
the stronger whole-unit cap

    |T_y|<3/25+8/15=49/75<7/10.                    (4)

Reflection and rotation preserve this statement. In particular a unit
in x<=-(1-epsilon) has every actual height below 7/10. The cap concerns
the actual whole square, not just its center or circle resultant.

## 3. Complete actual separating-axis cover

Put A0=1-h>59/60 and U=(-A0,g), the actual top-left H corner.
The actual chord PV belongs to B. If P_x>-A0, that chord would enter
int H just below height g. Both of its abscissas are in [-A0,h], with
P strictly inside the right endpoint, and P_y<7/10<g. This includes
either V side endpoint and V_y=g. Therefore

    P_x<=-A0.                                       (5)

Two interior-disjoint rectangles admit a closed separating axis owned
by one rectangle: the edges of their Minkowski difference have the
own-axis normals of the two rectangles. Separating the origin from
its open interior supplies the same weak separator at a touching
endpoint. This is an auxiliary physical line, not a selected force.

No H-axis separation works. P rules out right and above, V rules out
below, and an entire B to the left would satisfy
x<=h-1<=-(1-epsilon). Equation (4) would then contradict V_y>=g.

Choose the remaining B-owned unit separator n from H to B. Northeast
is excluded by P being strictly left of h and below g. Southwest and
Southeast are excluded by V being strictly above H's bottom and in
its closed horizontal strip. All axis endpoints were already excluded.
Thus the whole possible direction is

    n=(-s,c), s,c>0, s^2+c^2=1,
    t=(c,s).

Write the entire actual B in this own frame:

    B=[k,k+1] n+[ell,ell+1] t,
    H0=U.n=A0*s+g*c,
    T0=U.t=-A0*c+g*s,
    k>=H0>0.                                        (6)

Equations (2),(5) give P.t<T0<=V.t. In particular T0 belongs to
B's actual t interval, even when V=U.

## 4. Uniform separator and actual far-corner bounds

The actual far-side point (k+1)n+T0*t belongs to B, so

    R^2>=(k+1)^2+T0^2
        >=A0^2+g^2+2H0+1.

It follows that

    H0<91/100,                                      (7)

because

    (59/60)^2+(37/50)^2+1+2*(91/100)-1105/256
        =26119/1440000>0.

The complete direction interval consequently obeys

    0<s<1/3, c>9/10.                               (8)

Indeed the concave function
(59/60)s+(37/50)sqrt(1-s^2) on [1/3,1] has its minimum at an
endpoint. Its right endpoint is 59/60>91/100 and its left endpoint
is greater than

    (59/60)/3+(37/50)*(14/15)=4583/4500>91/100.

This contradicts (7) if s>=1/3; then c^2>8/9 proves (8). Also
T0<-(59/60)(9/10)+1/3<0, using g<=1.

Put eta=g-7/10>=1/25. From P.n>=k>=H0 and P_y<7/10,

    P_y-g=c*(P.n-H0)+s*(P.t-T0)<-eta,
    ell<=P.t<T0-eta/s<0.

Thus B's actual far corner Z=(k+1)n+ell*t satisfies

    |Z|^2>(H0+1)^2+(T0-eta/s)^2.                   (9)

Both positive square roots on the right increase with A0 and g.
For the second one use the exact expression

    -T0+eta/s=A0*c+g*c^2/s-(7/10)/s.

Its comparison value at A0=59/60, g=37/50 is positive by (8).
Therefore (9) gives

    |Z|^2>
      [1+(59/60)s+(37/50)c]^2
       +[(59/60)c-(37/50)s+1/(25s)]^2.

Write K=1+(59/60)^2+(37/50)^2-2*(37/50)*(1/25). Expanding,
the last expression is exactly

    K+(59/30)s+(37/25)c+(59/750)(c/s)+1/(625s^2).

Because c>9/10,

    (59/30)s+(59/750)(c/s)
       >(59/30)s+177/(2500s)
       >=2 sqrt((59/30)*(177/2500))>37/50.          (10)

The final squared reserve is
4*(59/30)*(177/2500)-(37/50)^2=117/12500>0.
Dropping only the positive final term in the expansion gives

    |Z|^2>K+333/250+37/50
          =407461/90000
          =1105/256+303751/1440000.                 (11)

This contradicts containment of the actual corner Z. It proves the
whole signed-support barrier, including epsilon=0, h=epsilon, all
actual B frames, both V horizontal endpoints and V_y=g.

## 5. Exact source boundary

| Source | SHA256 | Literal use |
| --- | --- | --- |
| HIGH_VERTICAL_STRIP_AND_NEAR_EAST_UNIT_CENTER_EXCLUSION.md | 75def83e3a67168eb28014641ddfa3d53372028514facaab09529903ba6090f8 | Entire Section 1 physical high-strip center bound; no Section 2 neighbor exclusion or force premise |
| HIGH_SQUARE_CORNER_AND_LOW_LEFT_PORT_CIRCLE_BARRIER.md | f69af5d923356a063c25b108586b9a1905acfa924d244cd25622bcc0273d4176 | Predecessor only; its separator, corner and endpoint proof is rederived above with the signed-support constants |

Every argument treats actual complete units. No sampled pose, mesh,
normal reselection, chosen mean, force deletion, false smaller-degree
equation, Lean compilation, CI, metadata edit, commit or publication
is used. A graph caller must still supply the original actual P,V.
