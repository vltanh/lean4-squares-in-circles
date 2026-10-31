# High top returns beside a common right support are impossible

Date: October 27, 2026.  
Author: topology_final.

**Status: complete analytic local theorem, frozen for a separate full
independent review.** One center-distance bound covers both physical
circle masks of the returning square, every physical HC/CK type and
every actual force mean. The theorem permits arbitrary degrees and
circle masks at K, uses no K2 equation, and selects no K circle corner.
It retains the aligned endpoints, including `d=G=1` and `h=0`.

## 1. Exact local domain and statement

Let H,K,C be contained, pairwise interior-disjoint unit squares in the
origin-centered disk of radius R, where

\[
 \frac{17}{4}\le R^2\le\frac{1105}{256},\qquad
 d=\sqrt{R^2-\frac14}-1,\qquad \delta=d-1.
 \tag{1}
\]

Thus

\[
 1\le d<\frac{61}{60},\qquad
 0\le\delta<\frac1{60},\qquad R<\frac{25}{12},\qquad d+1<R.
 \tag{2}
\]

Suppose the actual H square and the actual K supports satisfy

\[
 H=[h-1,h]\times[G-1,G],\qquad
 |h|\le\delta,\qquad \frac{89}{120}<G\le1,
 \tag{3}
\]

\[
                    \min_K y=G,\qquad \max_K x=h.
 \tag{4}
\]

K physically touches the containing circle. It may have any degree,
either physical circle mask and arbitrary additional forces.

C has positive total circle load and exactly two positive pair forces,
on HC and CK, with their actual force and moment equations. The actual
normal directed H to C is `E2`. Its actual application T lies in the
physical intersection of H and C. In particular

\[
       \min_C y=G,\qquad T=(t,G),\quad h-1\le t\le h.
 \tag{5}
\]

Both physical C masks are initially allowed. A second physical circle
corner remains part of its mask even if its individual weight is zero.
Every actual HC and CK point or shared-segment mean is retained. H may
have any further incident forces and any degree. No assumption about
the normal, owner or force application of an HK edge is needed here.

**Theorem 1.1.** This entire local configuration is impossible.

The only force consequence used is the following: if C has a unique
physical circle corner Z_C, then its original two-force system gives

\[
 Q_C=rZ_C=T+\ell E_2\in C,\qquad
                   0<r\le1,\quad\ell\ge0.
 \tag{6}
\]

Thus the theorem also holds under the weaker explicit local premise
(6) in the unique-circle branch, with no force premise at all in the
physical two-circle branch. Under the stated true-C2 hypotheses, (6)
follows from the complete boundary-neighbor concurrence lemma because
K physically touches the circle. Its application is justified in
Section 3 below. No property of a new or auxiliary force mean is used.

The proof gives the common quantitative contradiction

\[
             |c_C-c_K|^2<\frac{4097}{7200}<1,
 \tag{7}
\]

where `c_C,c_K` are the two actual square centers. This conflicts with
their interior disjointness.

## 2. Two elementary physical facts and the exact K center

Every unit square contains its open radius-one-half disk about its
center. Therefore interior-disjoint unit squares have center distance
at least one. Also, for any unit square with minimum height G, its
vertical width is

\[
             w=|u_y|+|v_y|\in[1,\sqrt2]
 \tag{8}
\]

for its orthonormal side axes u,v. Its center height is consequently

\[
                  G+\frac12\le c_y\le G+\frac{\sqrt2}{2}.
 \tag{9}
\]

This statement is independent of every physical circle mask, frame
angle or force equation. Both K and C satisfy it by (4)--(5). Hence

\[
             |(c_C)_y-(c_K)_y|
                 \le\frac{\sqrt2-1}{2}<\frac5{24},
 \tag{10}
\]

using `sqrt(2)<17/12`. Cert_final_review suggested using this common
height interval for both masks; that proof-economy contribution is
explicitly credited. The independent reviewer of the whole new theorem
is requested to have made no contribution to its derivation.

The two physical supports in (4) give the complete K parameterization

\[
 \begin{aligned}
 &c,s\ge0,\quad c^2+s^2=1,\qquad W=(h-s,G),\\
 &u=(-c,s),\quad v=(s,c),\qquad
 K=W+[0,1]u+[0,1]v.
 \end{aligned}
 \tag{11}
\]

When c,s are positive, W is the actual lowest vertex and W+v the
actual rightmost vertex. When c=0 or s=0, (11) is the same aligned
square `[h-1,h] x [G,G+1]`; the minimum and maximum supports are full
sides. Both endpoints are included, without selecting a K corner or
a point of its actual shared force mean.

Its actual center is

\[
        c_K=\left(h-\frac{c+s}{2},\ G+\frac{c+s}{2}\right).
 \tag{12}
\]

Since `1<=c+s<=sqrt(2)<17/12` and `|h|<=delta<1/60`,

\[
                  -\frac{29}{40}<(c_K)_x<-\frac{29}{60}.
 \tag{13}
\]

The rest of the proof establishes the single uniform C bound

\[
                       -\frac{23}{30}<(c_C)_x\le0.
 \tag{14}
\]

No K circle position, K force equation or CK owner enters (11)--(14).

## 3. Exhaustive physical circle masks and the true proper ray

At a physical circle corner of a contained unit square, choose its
orthogonal frame so the square is `[a-1,a] x [b-1,b]`, with that
corner `(a,b)` and `a,b>=1/2`. The bounds follow by comparing its two
adjacent corners with the containing radius. Another corner has the
same norm exactly when one of a,b equals one half. Both cannot equal
one half in (1). Thus there are precisely two physical possibilities:

* A unique physical circle corner.
* Two adjacent physical circle corners, in which case the square has
  the exact radial form `[d,d+1]e+[-1/2,1/2]f` for orthonormal e,f.

This is the physical classification in `C7_FORCE_POLYGON.md`, Section
3. It does not classify by positive individual circle coefficients.
In addition, a containing-circle point cannot belong to two contained
interior-disjoint squares: the inward radial direction lies strictly
inside each square's inward quadrant at that circle corner. This is
proved in the same source's Section 1.

For unique physical C, the complete Lemma 2.1 of
`TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md` applies to its two original
positive pair forces because at least one neighbor, K, physically
touches the circle. The two actual force lines are nonparallel and
meet at a positive radial multiple of the original circle resultant.
For the unique physical corner that resultant is a positive multiple
of Z_C. The lemma's unique-circle proof puts the concurrence in C
and retains the nonnegative proper offset at each actual application.
At HC the outward normal of C is `-E2`, giving exactly (6).

The bound r<=1 follows also directly from `Q_C in C subset D_R`
and `|Z_C|=R`. Coincident actual applications, zero proper offsets
and shared-segment mean endpoints are allowed by the original lemma.
No later argument requires `ell>0`. No general claim that the
two-circle concurrence lies in C is made or used here.

## 4. The physical two-circle branch, including its vertical endpoint

Write the actual radial C square as

\[
                C=[d,d+1]e+[-1/2,1/2]f.
 \tag{15}
\]

Since every point of C has height at least G>0, its center has
positive height and therefore `e_y>0`. If `e_x>0`, write
`e=(q,p)`, `f=(-p,q)` with p,q>0 and p^2+q^2=1. Its actual
minimum-height vertex has x coordinate

\[
                      dq+\frac p2>\frac12>h.
 \tag{16}
\]

Here d>=1 and p+q>1 justify the strict first inequality. That vertex
cannot touch H's top side, contrary to the actual application (5).

If `e_x=0`, then e=E2 and `min_C y=d`. Equations (2)--(5) give
`d=G=1`, `h=0`. This is retained, not discarded: its actual center
has x coordinate zero, which satisfies (14). All possible actual
shared HC means and both individual circle weights remain allowed.

Otherwise the only physical orientation is

\[
 e=(-q,p),\quad f=(p,q),\quad p,q>0,\quad p^2+q^2=1,
 \tag{17}
\]

with actual minimum-height vertex and height

\[
       T=d e-\frac12f,qquad G=dp-\frac q2.
 \tag{18}
\]

The entire angle interval is small. If `q>=2/5`, then
`p<=sqrt(21)/5<11/12`, so

\[
       G<\frac{61}{60}\frac{11}{12}-\frac15
          =\frac{527}{720}<\frac{89}{120}.
 \tag{19}
\]

The exact squared radical and height reserves are respectively
`1/3600` and `7/720`. Thus `q<2/5` and `p>9/10`.
The actual C center is `(d+1/2)e`, so

\[
        -\frac{91}{150}<-(d+\tfrac12)q=(c_C)_x<0.
 \tag{20}
\]

Since `91/150<23/30`, (14) holds. The vertical endpoint already
treated has `(c_C)_x=0`. No C force, circle-weight ratio, CK contact
normal, selected side owner or K circle choice has entered this
entire physical two-circle argument.

## 5. Unique C with an aligned minimum-height side

Suppose now C has a unique physical circle corner and its minimum
height is attained on a side. It is exactly

\[
                 C=[l,l+1]\times[G,G+1].
 \tag{21}
\]

This covers the whole actual shared HC type and also any admitted
point endpoint of the same physical support geometry. Its unchanged
application is `T=(t,G)` with `h-1<=t<=h`; no value of t is chosen.

Since G>0, a bottom corner cannot be on the containing circle: its
vertically adjacent top corner has larger squared norm. The unique
top circle corner has horizontal magnitude strictly greater than one
half. Indeed the two top horizontal endpoints differ by one, and the
larger of their absolute values is at least one half, with equality
only when both top corners have equal norm.

The actual proper ray (6) gives

\[
       r(Z_C)_x=t,\qquad r(G+1)=G+\ell\ge G,
       \qquad r\ge\frac{G}{G+1}>\frac13.
 \tag{22}
\]

If t=0, its first equation would make the unique circle coordinate
zero, impossible. If t>0, that coordinate exceeds one half, so
`t>1/6`, contradicting `t<=h<=delta<1/60`. Thus t<0 and the
actual circle corner is `(l,G+1)`, with `l<-1/2`.

Its actual radius gives

\[
 \begin{aligned}
 l^2&=R^2-(G+1)^2\\
    &<\left(\frac{25}{12}\right)^2
       -\left(\frac{209}{120}\right)^2
      =\frac{18819}{14400}<\frac{25}{16}.
 \end{aligned}
 \tag{23}
\]

The final exact reserve is `409/1600`. Since l<0, this gives
`-5/4<l<-1/2` and consequently

\[
                -\frac34<(c_C)_x=l+\frac12<0.
 \tag{24}
\]

This is stronger than (14). It includes G=1 and every actual
shared mean endpoint without requiring any circle equation at K.

## 6. Unique tilted C: every possible circle corner and both point signs

The remaining physical case has one strict minimum-height C vertex.
Use its actual point T from (5), without initially assigning its
horizontal sign, and write the full physical square as

\[
 C=T+[0,1]e+[0,1]f,\qquad
 e=(-q,p),\quad f=(p,q),\quad p,q>0,\quad p^2+q^2=1.
 \tag{25}
\]

The actual t interval is the whole closed interval `[h-1,h]`.
The proof does not need a strict relative-interior contact at H.

The point T is shared with H, so it cannot be a circle corner. If
the opposite corner were `Z_C=T+e+f`, put `Y=(Z_C)_y>G`.
From (6),

\[
       r(Z_C)_x=t,\qquad \frac GY\le r\le1.
 \tag{26}
\]

Using its unchanged vertical difference `Y-G`, this gives

\[
 \begin{aligned}
 2=|Z_C-T|^2
 &\le\left(1-\frac GY\right)^2R^2\\
 &\le(R-G)^2
  <\left(\frac{161}{120}\right)^2<2.
 \end{aligned}
 \tag{27}
\]

All factors squared are nonnegative. The middle comparison uses
`G<Y<=R`; the final radius reserve is `2879/14400`. In particular
the opposite corner is excluded before either sign of t is used.

If t>=0, then `0<=t<=h<=delta` and `G<=1`, so

\[
                    |T|^2\le\delta^2+1\le d^2.
 \tag{28}
\]

Both adjacent C corners then have norm at most `d+1<R`. Together
with the preceding exclusions there would be no physical C circle
corner. Hence t<0. This argument retains the possible equality
`|T|=d` when `d=G=1`; strictness comes from `d+1<R`.

Put `t=-z`. The actual support interval now gives

\[
                       z>0,\qquad z\le1-h<\frac{61}{60}.
 \tag{29}
\]

The right adjacent vertex `T+f` has e-coordinate
`T.e=zq+Gp>0`. Its adjacent vertex `T+f+e` is strictly farther
from the origin, so `T+f` cannot be a circle corner. The original
unique physical corner is therefore necessarily

\[
                           Z_C=T+e=(-z-q,G+p).
 \tag{30}
\]

Every physical C corner and both initial point signs have now been
handled. No actual CK support or normal has been used.

## 7. One whole angle bound gives the unique tilted center interval

Define the actual own-frame quantities

\[
                       A=Gp+zq>0,\qquad B=zp-Gq.
 \tag{31}
\]

At the corner (30), the e-coordinate is A+1 and the f-coordinate is
`-B`. Containment of the adjacent `Z_C+f` gives `B>=1/2`;
physical uniqueness makes it strict. The exact radius and inverse
coordinate relations are therefore

\[
 R^2=(A+1)^2+B^2,\qquad B>\frac12,\qquad
 A<d,\qquad G=Ap-Bq<dp-\frac q2.
 \tag{32}
\]

The inequality A<d follows from
`(A+1)^2<R^2-1/4=(d+1)^2` and A+1>0. Applying precisely the
whole angle comparison (19) to (32) gives

\[
                 q<\frac25,\qquad p>\frac9{10},\qquad
                 p-q>\frac12.
 \tag{33}
\]

Also `zp=B+Gq>1/2`, so z>1/2. The actual center of (25) is

\[
                  c_C=\left(-z+\frac{p-q}{2},
                                      G+\frac{p+q}{2}\right).
 \tag{34}
\]

Equations (29) and (33) give its lower horizontal bound, while
z>1/2 and p-q<1 give its upper bound:

\[
 -\frac{61}{60}+\frac14
       =-\frac{23}{30}<(c_C)_x<0.
 \tag{35}
\]

This proves (14) for every unique tilted C. It includes all actual
HC point endpoints and uses only the original proper ray, without
any fixed-singleton owner selection, CK owner classification, smaller
degree at K or special circle-weight hypothesis.

## 8. The same center contradiction closes both physical masks

The complete radial and unique cases prove (14). Together with (13),
they imply

\[
 \begin{aligned}
 (c_C)_x-(c_K)_x&<\frac{29}{40},\\
 (c_K)_x-(c_C)_x&<\frac{23}{30}-\frac{29}{60}
                  =\frac{17}{60}<\frac{29}{40}.
 \end{aligned}
 \tag{36}
\]

Thus the absolute horizontal center difference is strictly below
29/40. The common minimum-height fact (10) applies to both masks
and to every aligned endpoint. Therefore

\[
 \begin{aligned}
 |c_C-c_K|^2
 &<\left(\frac{29}{40}\right)^2+\left(\frac5{24}\right)^2\\
 &=\frac{4097}{7200}
   =1-\frac{3103}{7200}<1.
 \end{aligned}
 \tag{37}
\]

Their two open inscribed radius-one-half disks would overlap. This
contradicts physical interior disjointness, proving Theorem 1.1.

The contradiction is at the actual centers. No physical square, force
mean or circle point has been moved to obtain it. All angle intervals
were treated continuously by one fixed comparison, and no numerical
subdivision or computational exclusion certificate occurs.

## 9. Exact scope and original-caller obligations

The theorem has deliberately local premises. A caller must establish
the actual high top G, the same right support h, K's whole minimum
height and maximum-x relations, and C's actual H-to-C normal E2.
It must retain the true C2 system with boundary neighbor K, or supply
the exact proper line (6) explicitly in the unique-circle branch.

The theorem does not derive an original root chart or an exhaustive
HC direction cover. It does not assume such a cover from a remembered
missing proof. In the intended shared-root/parallel-tip application,
the separate original chart has K's actual lowest vertex on H's top
and the same right support h, so (4) is the natural physical input.
That full original transfer and the complementary far direction
require their own complete sources and independent reviews.

The local statement is stronger than a chosen-circle or owner-specific
exit: it uses no K circle location, no HK force, no H or K degree law,
no CK owner, no variable-mean normal selection and no C force at all
in the radial physical branch. The entire closed endpoint G=1 is
included. In the original nine-unit problem, all true H4/K3/B3/C2
equations and all nine physical units remain; the local contradiction
simply does not need the extra equations or bodies.

No whole original gate, ledger closure or unrestricted packing theorem
is claimed by this helper alone.

## 10. Present inputs, exact checks and review boundary

The only mathematical source inputs are the following complete present
original files under `current_pr11/research/nine`.

| Full input | Exact SHA256 | Scope used |
| --- | --- | --- |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Actual support normals, physical intersections and unchanged shared means. |
| C7_FORCE_POLYGON.md | d50d8ca48ea19156175e651bfa74be30ef3e58065ec14d8d1834670a41559089 | Exhaustive physical circle masks, exact radial square and unshareable circle points. Its all-boundary cycle theorem is not invoked. |
| TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md | 29e38d3f641fe16c6db587e51245f92ad4c447f9536db7d14c221f56b5357e82 | Complete general Lemma 2.1 and its unique-circle interior/proper conclusion, with only one boundary neighbor required. Its pendant-chain theorem is not invoked. |

The author exact record accompanies this file as

    check_common_right_support_top_centers.py
    common_right_support_top_centers_exact.json.

It expands the displayed complete frame, center, circle and radius
identities and checks the fixed rational reserves. It is a transparent
identity check, not a sampled packing search, finite pose cover or
exclusion packet. The entire physical mask/support cover and proper-ray
transfer are proved in the text and require a separate full review.

No source bytes, original ledger, remote branch, Lean file or CI state
are modified by this theorem.
