# A boundary shelf cannot return above the neighboring square

Date: October 27, 2026.  
Author: cert_final_review.

**Status: complete new physical theorem, frozen for full independent
review.** The proof covers every orientation of the returning square,
every actual contact point and both physical contact types. It requires
no force equation, circle mask, degree, selected normal, numerical
certificate or radius window. The closed height endpoint G=1 is included.

## 1. Full physical statement

Let

```
0<A<G<=1, -G/2<=h<=0,
H=[h-1,h] x [G-1,G],
K=[h,h+1] x [A,A+1].                         (1)
```

Suppose H and K are contained in a closed disk of radius R about the
origin, and K has a physical point on that circle. Let C be any closed
unit square contained in the same disk, with interior disjoint from
H and K. Assume C physically touches both H and K and has minimum
height G.

**Theorem 1.1.** These conditions are inconsistent.

Neither physical boundary contact of C nor any force law on C is
assumed. H and K can have arbitrary degrees and circle masks. If a
caller retains an actual HC or CK force and mean, it is not changed
by this geometric theorem. The physical shared segment H intersection K
is the whole vertical interval {h} x [A,G].

The strip in (1) is substantially broader than a small neighborhood
of the origin. Its only horizontal condition is G+2h>=0. In particular
the theorem includes h=0, h=-G/2 and G=1. The strict A>0 and A<G are
explicit; they give G<A+1 throughout the stated domain.

## 2. The actual boundary corner and a common norm comparison

Since G<=1 and h>=-G/2, one has -1/2<=h<=0. Therefore

```
|h+1|>=|h|,  A+1>|A|.
```

The largest norm among K's four actual vertices is attained at
(h+1,A+1), with a possible horizontal tie at h=-1/2. A convex square
has no point with norm larger than its largest vertex norm. Its
physical circle contact and containment consequently give the exact
identity

```
R^2=(h+1)^2+(A+1)^2.                         (2)
```

The proof does not select one of K's actual circle weights. The same
identity holds if both top vertices have the maximum norm.

Set the scalar comparison

```
L=(h-1)^2+(G+1)^2.
```

Then

```
L-R^2=-4h+(G-A)(G+A+2)>0.                    (3)
```

Strictness follows from G>A, while h<=0 makes the other term
nonnegative. It will suffice in one whole contact family to exhibit
an actual C vertex with squared norm greater than L.

## 3. The entire aligned C case

If C has the coordinate side frame, its minimum-height condition gives

```
C=[t,t+1] x [G,G+1].
```

The open height intervals of C and K overlap, since A<G<A+1.
Interior disjointness therefore makes their open horizontal intervals
disjoint. The alternative t>=h+1 cannot touch H, whose maximum first
coordinate is h. Hence t+1<=h. Physical contact with K now requires
t+1=h, so

```
C=[h-1,h] x [G,G+1].
```

Its actual vertex (h-1,G+1) has squared norm L>R^2 by (3), a
contradiction. This argument keeps every possible original aligned
side application or shared mean; it does not choose an application
to obtain the placement.

## 4. Complete physical routing for a tilted C

Otherwise C has a unique minimum-height vertex T. Because C touches
H and every C point has height at least G, while every H point has
height at most G, that actual vertex is

```
T=(t,G), h-1<=t<=h.
```

Name its actual inward unit axes

```
u=(-c,s), v=(s,c), c,s>0, c^2+s^2=1,
C=T+[0,1]u+[0,1]v.                          (4)
```

Thus V=T+v is the unique rightmost vertex of C. Its bottom-to-right
edge is the actual segment T+[0,1]v. Both c and s are strictly
positive; the axis endpoints were already handled in Section 3.

First t<h. If t=h, the actual height G lies strictly inside K's
height interval. A small vector with positive first coordinate from
T into the open C cone also lies inside K, contradicting disjoint
interiors. Next V_x>=h is necessary for physical CK contact, since
K has minimum first coordinate h.

If V_x=h, then V is the only possible common point and its height
must satisfy V_y<=A+1. This is the first entire contact family.

Suppose V_x>h. Then the actual lower-right edge crosses the line x=h
at a strict relative-interior point, with height

```
y_*=G+(c/s)(h-t).                            (5)
```

For any actual point Z=T+lambda*u+mu*v of C, eliminating mu gives
the exact identity

```
Z_y=G+(c/s)(Z_x-t)+lambda/s,
0<=lambda<=1.                               (6)
```

If y_*>A+1, every C point with Z_x>=h has height greater than A+1
by (6), so it cannot touch K. If y_*<A+1, the crossing is inside
K's height interval because y_*>G>A. Small points of the open C
interior just to the right of the crossing remain below A+1 and
lie in the open K square, a contradiction. Thus actual physical
contact forces

```
y_*=A+1.                                    (7)
```

This is the second entire contact family: the actual lower-right
C edge passes through the upper-left K corner (h,A+1). No other
CK contact type remains. The proof of this cover used all points
of C, not a chosen CK force line; free contacts and shared contacts
were included from the outset.

## 5. Rightmost-vertex contact: the whole smaller-c interval

In the first family V_x=h, so T=(h-s,G). Consider the two actual
C vertices

```
Z_1=T+u=(h-s-c,G+s),
Z_2=T+u+v=(h-c,G+c+s).                        (8)
```

If 0<c<=1/2, then s>=sqrt(3)/2>4/5. Using
1-s=c^2/(1+s), the entire squared difference is

```
|Z_1|^2-L
 =c[2s-c-2G*c/(1+s)]-2h(c+s-1).              (9)
```

Since G<=1, c<=1/2 and 1+s>9/5, the bracket is strictly greater
than

```
8/5-1/2-5/9=49/90>0.
```

The last term in (9) is nonnegative because h<=0 and c+s>1.
Consequently |Z_1|^2>L>R^2. This contradicts containment over
the entire interval 0<c<=1/2, including G=1 and either h endpoint.

## 6. Rightmost-vertex contact: the whole larger-c interval

If 1/2<=c<1, the other actual vertex in (8) has the exact difference

```
|Z_2|^2-L
 =s(2c-s)+2G(c+s-1)+2h(1-c).                 (10)
```

Here 2c>=1>s, so its first term is strictly positive. Also

```
c+s-1=(1-c)[(1+c)/s-1]>(1-c)/2,              (11)
```

because 1+c>=3/2 and s<1. The last two terms in (10) are therefore
strictly greater than

```
(G+2h)(1-c)>=0.
```

Thus |Z_2|^2>L>R^2 on the entire interval. The endpoints c=1/2
are covered by both comparisons; no small angle or actual side
position has been subdivided into a computational certificate.

## 7. Upper-left-corner contact: one complete actual norm identity

In the second family put

```
g=A+1-G>0.
```

The crossing is in the strict interior of the actual segment T-V.
Equation (7) gives

```
0<g<c, t=h-(s/c)g,
r=c-g in (0,c).
```

The actual opposite C vertex is therefore

```
Z_2=T+u+v=(h-c+(s/c)r, A+1+r+s).              (12)
```

All denominators are positive. With the unchanged K radius (2),
the exact difference is

```
|Z_2|^2-R^2
 =-2h[1+c-(s/c)r]+2(A+1)(r+s)+r^2/c^2.       (13)
```

Because r<c, the coefficient in square brackets exceeds
1+c-s>0. Its contribution is nonnegative for h<=0. The middle
term is strictly positive, and the final term is nonnegative.
Hence this actual C vertex lies outside the disk throughout the
entire second contact family as well.

Sections 3--7 cover every C orientation and every possible actual
CK incidence. They prove Theorem 1.1.

## 8. Scope, endpoint preservation and physical foundation

This is a physical theorem about the displayed actual squares.
Its proof never requires C to touch the containing circle and
never assigns a circle corner to C. Instead it finds an actual
C vertex outside the circle. It covers any force degree or mask,
and every original mean is retained until its physical incidence
is contradicted.

The complete contact definitions are those of the present original
`PHYSICAL_CONTACT_STRESS.md`, SHA256

```
d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5.
```

All additional geometry, norm comparisons and the complete tilted
contact cover are reproduced here. No original graph reduction,
global physical-mask theorem, force selector, C2 lemma, or missing
recovery artifact is a logical input. A caller must supply the actual
shelf placement (1), K's physical boundary contact, and C's actual
minimum height before applying this theorem.

The endpoint G=1 is part of the proof. There is no need to eliminate
that endpoint by an extra force or moment argument. The strict A>0
ensures G<A+1 there and is used in the full physical routing.

The separate accompanying exact calculation checks the full identities
(3), (6), (9)--(13) and their fixed rational reserves with exact
Fraction polynomials. It is algebra validation, not a computational
exclusion certificate. A complete independent reader must still
check every physical case, actual contact interval and hypothesis
transfer before original adoption. No ledger, remote branch, Lean
file or CI workflow is changed by this new source.
