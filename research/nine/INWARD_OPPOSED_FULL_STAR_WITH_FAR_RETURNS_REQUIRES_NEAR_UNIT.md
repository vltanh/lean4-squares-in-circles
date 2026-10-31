# An inward opposed full star with far return neighbors requires an actual near unit

Date: October 28, 2026 UTC. Author: shared_s continuation.
Read base: `c31ecd109097dde3c8faa1db11a84655575e87ab`.

**Status: complete proposed uniform hand theorem and literal three-family
necessary reduction, submitted for full root and separate independent
review. No original fine or coarse checkbox is changed.**

The new theorem retains an arbitrary full degree at least three. It
requires no physical contact between the nonexceptional neighbors. In
particular it applies to the true degree-four fan hub. Both the original
force equation and its original torque equation are essential.

## 1. Whole original physical statement

Retain all actual interior-disjoint closed unit squares in the unchanged
circle, with

    79/40 <= R <= sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1 < 61/60,
    epsilon=max(d-1,0) < 1/60.

Let U be unloaded and have one actual positive pair neighbor X, with
unchanged outward normal n, application p and magnitude lambda>0. Let
its other actual positive pair neighbors be V_j, with original outward
normals g_j, applications q_j and positive magnitudes mu_j. The V_j
are distinct physical neighbors and there are at least two of them.
These are U's entire original pair forces. Assume

    lambda*n + sum_j mu_j*g_j = 0,
    lambda*det(p,n) + sum_j mu_j*det(q_j,g_j) = 0,

    h_U(n)=p.n < 0,
    det(p,n)>0,
    det(q_j,g_j)<0 for every j,                         (1)

and assume that every V_j avoids the closed disk

    D_(sqrt(2)*epsilon).                               (2)

There is no corresponding avoidance, load, degree or force premise on
X. The nonexceptional neighbors need not touch one another. Each side
mean in (1) is its actual aggregate mean; no new mean is chosen.

**Theorem.** In a positively oriented own frame, U must have the form

    U=[a,a+1] x [b,c],
    0<a<=epsilon, b<=0<=c, c=b+1.                      (3)

Consequently U meets closed D_epsilon, epsilon>0, and U is physically
circle-clear. Reflection gives the same conclusion when all determinant
signs in (1) are reversed.

The degree lower bound is literal: a two-force transmitter is not
covered. The conclusion is an actual geometric position statement,
stronger than a small separating support. It is not a contradiction of
the remaining strip (3).

## 2. Physical center bounds and two elementary caps

For every contained unit with center C, its actual farthest corner gives

    |C|^2+|C|+1/2 <= R^2,
    |C| <= d+1/2 < M=91/60.

Since a unit has half-width at least 1/2 in every direction, a contained
unit beyond an actual support f.z>=h, |f|=1, requires

    C.f>=h+1/2, h<=d.                                 (4)

Every actual point Q in that neighbor also satisfies |Q-C|<=1/sqrt(2).

### 2.1. No support above one carries a point of squared norm at least two

Suppose h=Q.f>1 and |Q|^2>=2. Then h<61/60 and C.f>3/2, so

    |Q.Jf|>sqrt(3479)/60,
    |C.Jf|<sqrt(181)/60,
    |Q-C|>(sqrt(3479)-sqrt(181))/60
           >(58-14)/60=11/15>1/sqrt(2).

This contradicts Q belonging to that actual neighbor. The inequality
is uniform over its orientation, every contact feature and every mean.

### 2.2. At most one distinct neighbor lies beyond a fixed support above one

Two contained units both lying in x>=h>1 would have centers with
x>3/2 and norm<M. The open containing rectangle for these centers
has squared diameter

    (1/60)^2 + 4*(M^2-9/4) = 29/144 < 1.

Their open radius-1/2 incircles could not be disjoint. Thus at most
one actual neighbor may lie there. This uses actual occupied centers,
not a force count or a bound on positive atoms.

## 3. The full two-missing-interval case is impossible

The strict negative support in (1) puts O outside closed U. First
suppose both own intervals miss zero. A proper quarter-turn of its
own frame puts them in the first quadrant:

    U=[a,a+1] x [b,c], a,b>0, c=b+1>1.

No ordering between a and b is assumed. At the Northeast corner
(a+1,c), every outward unit normal has support greater than one,
and that point has squared norm greater than two. Section 2.1 excludes
every actual contact there, including its axis-normal endpoints.

The negative exceptional support and positive exceptional determinant
leave exactly West, strict Southwest at (a,b), or strict Northwest
at p=(a,c). The North and East supports are positive, the South and
Southeast determinants are negative, and the Northeast support is
positive. Every actual feature and axis endpoint is included.

### 3.1. Southwest and West exceptional directions

For strict Southwest n, all possible negative-determinant return
normals have nonpositive y-component: top and Northwest features
have positive determinant, West has positive determinant, and the
Northeast corner is excluded above. The full vertical force sum is
strictly negative, impossible.

For West n, the full vertical equation makes all return normals
horizontal. Their negative determinants require East, since every
West mean has positive height. All at least two distinct return
neighbors would therefore lie beyond x=a+1>1. This contradicts
Section 2.2. This is exactly where the true degree-at-least-three
condition is required.

### 3.2. Northwest exceptional direction and the aggregate equations

Write

    n=(-u,v), u,v>0,
    -a*u+c*v<0,
    kappa=v/u<a/c.                                    (5)

All negative-determinant return features are now East, South, strict
Southwest and strict Southeast. No return is silently removed.

Use the following sums over the entire actual return star:

* E is the sum of East magnitudes. If E>0, write its actual weighted
  height as y and delta=c-y in [0,1]. Section 2.2 ensures that all
  these East atoms belong to one physical neighbor, so their mean
  remains an actual point of that square. In the usual pair-aggregate
  certificate this is already one original force.
* F and T are respectively the sums of the positive x-components
  and the negative y-components of all strict Southeast forces.
* S and W are respectively the sums of the negative x-components
  and negative y-components of all strict Southwest forces.
* N is the sum of all South magnitudes, and N_x is the same sum
  weighted by each original South mean's x-a in [0,1]. Thus
  0<=N_x<=N.

The full force equations and full torque equation about p=(a,c) give

    lambda*u = E+F-S,
    lambda*v = T+W+N,
    E*delta + F-T-S-N_x = 0.                          (6)

When E=0, the term E*delta is simply zero; no fictitious mean is
introduced. The torque terms follow from the actual vertex offsets
(1,-1) for Southeast and (0,-1) for Southwest, and the unchanged
whole South mean interval.

If E=0, equations (6) give

    lambda*u=F-S=T+N_x<=T+N<=lambda*v.

Hence v>=u, and (5) gives a>c>1. But the actual U corner (a+1,c)
then has squared norm greater than five, contrary to
R^2<=1105/256<5. Thus E>0.

The East support is a+1, so (4) now implies

    0<a<=epsilon<1/60, 0<kappa<a/c<1.                 (7)

If a strict Southwest return occurs, its actual application is
(a,b). Condition (2) implies a^2+b^2>2*epsilon^2. Since a<=epsilon,
we must have b>a: the opposite inequality would give
a^2+b^2<=2*a^2<=2*epsilon^2. Its negative original determinant
for normal (-s,-w) is

    -a*w+b*s<0,

so w>(b/a)*s>s. Summing yields W>S whenever a Southwest force is
present, and W=S=0 otherwise. In every case W>=S.

Subtract kappa times the first equation of (6) from the second,
and combine with the third. The exact identity is

    E*(delta-kappa)
      =(1-kappa)*S-W-(1-kappa)*F+N_x-N <= 0.          (8)

All signs are justified by (7), W>=S, F>=0 and N_x<=N.
Thus delta<=kappa<a/c, and

    y=c-delta>c-a/c>1-a>0.                           (9)

For the middle strict comparison, c=b+1>1 and
c-a/c-(1-a)=b+a*(1-1/c)>0.

The actual East neighbor therefore contains the unchanged aggregate
application Q=(a+1,y), with

    |Q|^2>(a+1)^2+(1-a)^2>=2,
    h_U(East)=a+1>1.

Section 2.1 excludes that actual contact. The whole two-missing-interval
case is impossible, for arbitrary return count and without any return
neighbor contact assumption.

## 4. The whole one-missing-interval domain beyond epsilon is impossible

The sole remaining kind of chart has

    U=[a,a+1] x [b,c], a>0, b<=0<=c, c=b+1.

Suppose for contradiction that a>epsilon. The East support a+1>d
excludes every East-normal neighbor by (4). A negative exceptional
support must have negative x-component: all normals with nonnegative
x-component have nonnegative support in this chart. A strict Southwest
normal has determinant -a*v+b*u<0. Thus the exceptional direction is
West at a positive-height mean or strict Northwest at (a,c).

There is no negative-moment return in the Northeast cone. Its strict
case (f,t), f,t>0, would require

    (a+1)*t<c*f,
    h_U(f,t)=(a+1)*f+c*t>(a+1)/f>=a+1>d.

The East axis endpoint is already excluded; the North endpoint has
positive moment. This is the entire cone, not an angle sample.

For West exceptional n, all return normals therefore have nonpositive
y-component. Full vertical balance makes all horizontal. East is
unavailable; all remaining terms point West. Full force balance fails.

For Northwest exceptional n=(-u,v), u,v>0, the return features are
West, South, strict Southwest and strict Southeast. Take the full
torque equation about the actual lower-right corner Q=(a+1,b).
Its exceptional contribution is lambda*(u-v). Every other contribution
is nonnegative:

* West at original height y contributes mu*(y-b)>=0;
* South at original coordinate x contributes mu*(a+1-x)>=0;
* Southwest (-s,-w) at (a,b) contributes mu*w>=0;
* Southeast at Q contributes zero.

Consequently v>=u. Negative exceptional support -a*u+c*v<0 gives
a>c, since c>=0.

Now take the full torque equation about the actual upper-left corner
P=(a,c). Every non-Southeast return contribution is nonpositive:
West contributes mu*(y-c), South contributes -mu*(x-a), and
Southwest contributes -mu*s. Every strict Southeast return (f,-t)
at Q contributes mu*(f-t). At least one Southeast force exists,
because it is the only possible positive-x return and the exceptional
force has strictly negative x-component. The total of its f-t terms
must be nonnegative. At least one actual Southeast return therefore has

    f>=t>0.

Write f=cos(theta), t=sin(theta), 0<theta<=pi/4. Its actual support is

    h_U(f,-t)=(a+1)*cos(theta)+(1-c)*sin(theta).

Here 0<=c<=1. This nonnegative function is concave on [0,pi/4]; its
minimum is at an endpoint. Both endpoint values exceed d:

    a+1>d,
    (a+2-c)/sqrt(2)>sqrt(2)>d.

This contradicts (4) at that actual return neighbor. Every original
side mean, equal-slope endpoint and all other positive forces were
retained. No triangle premise or selected two-force substar was used.

## 5. Conclusion, clearance and exact degree boundary

The strict negative support excludes O in closed U. Section 3 excludes
two missing intervals. Section 4 excludes a>epsilon for the one-missing
case. This proves exactly the residual chart (3), including b=0,
c=0 and a=epsilon.

The point (a,0) belongs to U and D_epsilon. If U also touched the
radius-R circle, these two actual points would be separated by at least

    R-epsilon > 79/40-1/60=47/24>sqrt(2),

contradicting the unit's diameter. Thus U is physically clear. Since
a>0, epsilon>0 as claimed.

The true degree lower bound must not be dropped. An unloaded two-force
East/West channel in a small first-quadrant square can retain the two
opposed moments. The proof excludes the West exceptional case by the
presence of two distinct return neighbors and the actual occupied cap;
it does not exclude a transmitter by treating two atoms at one physical
neighbor as distinct bodies.

The only far-neighbor use was at a genuine Southwest return point in
Section 3.2. Thus (2) can equivalently be weakened to the requirement
that every nonexceptional application satisfies |q_j|>sqrt(2)*epsilon.
Physical circle-touching neighbors automatically satisfy the stronger
literal (2): all their points have norm at least R-sqrt(2)>11/20,
whereas sqrt(2)*epsilon<1/40.

## 6. Common geometric strengthening for three original S-leaf families

Use the exact full graph hypotheses of Sections 1--4 of
`S_LEAF_ONE_UNLOADED_HUB_MOMENT_REDUCTION.md`. In particular the genuine
root X has exactly the positive neighbors L,A,H; A is physical boundary;
H is unloaded; deleting X,L leaves connected G; every other vertex of
G is boundary or a true unloaded degree-two transmitter between two
boundary units; and H has no transmitter neighbor. Assume additionally
that H has true degree at least three and O belongs to int(X).

**Uniform strengthened conclusion:** the actual H meets closed D_epsilon
and is physically circle-clear.

Suppose instead H avoids that closed disk. Every other nontransmitter
vertex of G also avoids it, because it is physically boundary. The
complete arguments of Sections 2--3 of the pinned S reduction apply
under exactly this premise: edges between disk-avoiding units cannot
be radial; every actual transmitter chord is nonradial, retaining both
means and width; and every positive-moment directed private cycle has
strict positive winding. The root's compact segment O--c_X lies inside
int(X), and the original boundary-leaf edge X--L would then be trapped
by that cycle. Thus the private orientation is acyclic.

Its only possible source and sink are A,H, in opposite roles. This
uses every original vertex torque, including zero-moment actual circle
atoms. At H all actual private moments have one same strict sign,
and the actual HX moment is strict with the other sign. Every H
private neighbor is boundary, hence satisfies (2). The exceptional
H-to-X support is strictly negative, because O is in int(X) and the
unchanged X/H separating line strictly separates O from H. After one
whole reflection, H's full true star therefore satisfies (1)--(2).
The theorem forces H to meet D_epsilon, contradicting the supposition.
This proves the strengthened conclusion without asserting that small
support alone makes a body near.

The exact original callers are unchanged:

| Original fine family | X | A | H | True H degree | Return neighbors at H |
| --- | --- | --- | --- | --- | --- |
| M6.B5L.HOUSE.ROOF.LAC.S | T | A | D | 3 | A,C, both boundary |
| M6.B5L.HOUSE.ROOF.LABC.S | T | A | D | 3 | A,C, both boundary |
| M6.B5L.FAN.ENDPOINT.L234.S | 1 | 2 | J | 4 | 2,3,4, all boundary |

The first row retains the actual unloaded B2 between boundary A,C;
the second row retains loaded B; the fan keeps all four original J
forces. The actual direct A--H edge is present in all three rows but
the full-star theorem does not require any contact among H's return
neighbors. The root's own force and every circle mask, zero weight,
positive magnitude, original normal and side mean remain unchanged.

At d<=1, an open-origin root in these three families is impossible:
epsilon=0 would put O in closed H, overlapping int(X). For high tilted
S roots with U<1 the real root is open at O, so their actual return
hub is now forced near and clear. This gives the literal near-neighbor
premise required by the existing S-root triangle owner-selection
theorem, rather than merely a small scalar support. No post-extraction
normal selection is performed here.

The aligned d>=1 roots and origin-free tilted roots are outside the
open-origin hypothesis of this join. The remaining near-strip geometry
and those domains still require a proof. No complete original family
or new fine identifier is claimed from this necessary reduction alone.

## 7. Exact operative source pins and proof boundary

Sections 1--5 are self-contained physical and full-star algebra.
Section 6 uses only the stated earlier complete graph arguments:

| Source | SHA256 | Exact operative scope |
| --- | --- | --- |
| S_LEAF_ONE_UNLOADED_HUB_MOMENT_REDUCTION.md | 94e3a3cec875be191355b1f9baff4ffa597edcae9854d2d557dcb13d631cc157 | Sections 2--4 nonradial private edges, full transmitter chords, winding and acyclic source/sink proof, now with actual H avoidance as the contradiction premise |
| RADIAL_BRIDGE_AND_LEAF_REDUCTION.md | faf453b3c519b10590cf9d6f6dbf9282233bd2ff04c90aa0cd8cd89e060bc676 | Genuine leaf geometry and the retained original radial leaf force |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe | One compatible physical embedding and protected leaf access, including weak-junction routing |
| FIVE_BODY_BLOCK_LEAF_GRAPH_LOAD_COVER.md | e5c84071363e8dc43b09f9033c7cb3a7684f1de19bcd169d53c9eab55d51963b | Literal original graph, degrees, load masks and same-nine completion contract in all three rows |

The existing true-degree-three inward triangle-star theorem permits
arbitrary other-neighbor positions but assumes their actual mutual
contact. The present theorem permits arbitrary true degree at least
three and unrelated returns but requires their actual far applications.
Neither scope is silently substituted for the other. All nine original
units, including arbitrary completion squares, remain. No computational
certificate, numerical pose, coefficient table, Lean execution, CI,
workflow, original ledger mutation or remote operation is used.
