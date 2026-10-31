# Complete independent review of whole-unit projection bridges and singleton return intervals

Date: October 29, 2026 UTC. Reviewer: capacity continuation.

**Verdict: ACCEPT at the exact frozen source below.** I read the complete
new manuscript and reconstructed the whole-unit support projection lemma,
the actual one-unit bridge obstruction, every original force and moment
identity used, both continuous small-y intervals, the complete high-b
upper-return argument including equality, and the literal original D02
transfers. No defect was found.

This is a full noncontributor review of the new projection theorem.
The earlier center-based bridge theorem is not a premise of this proof.
Its separate review does not replace the whole-unit argument checked here.

## 1. Frozen source and exact original inputs

Reviewed manuscript:

    ACTUAL_UNIT_PROJECTION_BRIDGE_AND_PERPENDICULAR_SINGLETON_RETURN_INTERVALS_2026_10_29.md

Frozen SHA256:

    97815bf7d2558343a76316a8095096bb780a8e4fe1664274c1863bcbbb8d6132

The complete original chart and upper-return source is

    PHYSICAL_TWO_WEST_STRICT_PERPENDICULAR_SINGLETON_ADJACENT_RETURN_EXCLUSION_AND_COMPLETE_RESIDUAL_2026_10_29.md

at SHA256

    f3718c86a99ef196eba1ee875b66375582a0fc588f10275ec171c442e46780dd.

I read that entire source again for this review, including the complete
continuous expansions in Sections 4--5. I independently checked the
extension to its formerly absent equality a=b=1/sqrt(2).

The original physical and graph inputs, previously read completely for
the chart review and retained here, are:

| Complete original input | SHA256 |
| --- | --- |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 |

For provenance only, the earlier center-based bridge source has SHA256

    8b73232e774201fedb5eec884672bdb431de09b7452c4636f19d7e232c06faf9.

The new projection theorem is proved independently of that source.

The reviewed source and its antecedent retain the original conditional
common-selection domain. They introduce no new selector and do not
establish the outstanding global extraction compatibility.

## 2. The exact whole-unit support projection lemma

Let

    f=(-h+r e)/sqrt(1+r^2), r>0,

in an orthonormal frame h,e. Let K be the original minimum-f support
point or mean of the actual unit B.

If K is a vertex, write B=K+[0,1]i+[0,1]j using the two actual inward
orthonormal edges. The support assumption gives f.i,f.j>=0.
Since

    f=(f.i)i+(f.j)j,

the two inward edges cannot both have strictly negative e component:
their nonnegative combination f would then have negative e component,
contrary to f.e>0. Zero inward coefficients are included.

For any inward edge with e.i=-v<0, its nonnegative f component gives

    -h.i-r v>=0.

Thus h.i<0 and sqrt(1-v^2)>=r v, so

    v<=1/sqrt(1+r^2).

The exact minimum e coordinate over the unit is the original e.K plus
the sum of the negative e components of its inward edges. At most one
such component is negative. The entire unit therefore satisfies

    min_B(e.X)>=e.K-1/sqrt(1+r^2).

If the minimum-support face is a side, f is the actual inward unit
normal of B. The unit side tangent has absolute e component
1/sqrt(1+r^2). The original support mean has distance at most one to
either endpoint of that same closed side. Moving inward along f
increases e. The same inequality therefore holds for every actual
side mean and both closed endpoints.

This argument neither assigns a new owner nor moves K to an endpoint.
At a side endpoint both the vertex and side descriptions give the same
valid bound.

Reflecting the e direction gives, for

    g=(-h-k e)/sqrt(1+k^2), k>0,

and the actual minimum-g support point or mean L of C,

    max_C(e.X)<=e.L+1/sqrt(1+k^2).

These inequalities are about the entire actual units, not just the
translated support points K+f and L+g.

## 3. The one-unit physical bridge

Choose actual intersection points

    X in B intersection N, Y in C intersection N,

where the actual unit N physically touches both B and C. The e width of
N is at most sqrt(2), because its two orthonormal own edges satisfy

    |e.i|+|e.j|<=sqrt(2).

Hence e.(X-Y)<=sqrt(2). The whole-unit bounds just proved give

    e.(K-L)-1/sqrt(1+r^2)-1/sqrt(1+k^2)
      <=e.(X-Y)<=sqrt(2).

This is exactly the new necessary bridge inequality. It is force-free,
radius-free and independent of every degree, load, corner mask or
additional contact of B,C,N. The actual contacts with N may be vertices,
owned sides or genuinely shared sides with their unchanged means.

The proof needs the physical existence of the two contacts only. It
does not contract N, treat a loaded N as a transmitter, or replace N
with a segment or disk.

## 4. Complete original equations and full original side mean

The inherited physical-two chart retains all nine actual units and

    A:{V,D,B}, D:{V,A,C}, V:{A,D},

with A,D unloaded true3 and V loaded true2 with two PHYSICAL circle
corners. It keeps

    79/40<=R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1, 9/10<d<61/60,
    P=(d,1/2), Q=(d,-t), 0<t<=1/2,
    H=t+1/2, h=(c,-s), e=(s,c),
    c,s>0, c^2+s^2=1.

AD is the actual A-only perpendicular singleton, with original A-to-D
normal -e and magnitude gamma. All original strict contact parameters
remain:

    A=P+[-1,0]h+[-l,1-l]e,
    W=P-xh-le, 0<l,x<1,
    v=W-Q=-a h+b e=(-u,y),
    a=H s+x>0, b=H c-l>0,
    a^2+b^2=u^2+y^2=1,
    u=a c-b s>0, y=a s+b c>0,
    w=-b h-a e=(-y,-u).

The complete A3 force is F_B=-mu h+gamma e. Its strict components
make the actual application K=P-h+(1-l)e. Expanding the entire
A torque about P gives

    gamma*x-gamma+mu*(1-l)=0,

so the unchanged positive ratio is

    r=gamma/mu=(1-l)/(1-x)
      =(1-H c+b)/(1-a+H s).

Its denominator is positive because the original x<1. K is the
minimum-f support point of the actual B for the exact f used above.

D's full unloaded force is

    F_C=-nu East-gamma e
       =-nu c h-(nu s+gamma)e.

The actual components on (v,w) are

    F_C.v=nu u-gamma b,
    F_C.w=nu y+gamma a>0.

Consequently its actual exterior application or original mean has the
complete form

    L=Q+w+zv, 0<=z<=1.

It is z=0 for the adjacent strict vertex, z=1 for the opposite strict
vertex, and the full original z when the v component is zero. Every
owner and both side endpoints are retained before torque is used.

Expanding D's entire torque about Q gives

    -gamma a-(nu u-gamma b)+z*(nu y+gamma a)=0.

With q=gamma/nu this is exactly

    q*[b-(1-z)a]=u-z y.

For the opposite vertex it gives q=(u-y)/b>0. For the side, the
original force equation first gives q=u/b; the same original torque
then fixes

    z=q a/(y+q a)=u a/c.

The second equality uses b y+a u=c, verified by expanding the original
frame coordinates. Positivity in the first expression gives 0<z<1.
No side mean was chosen anew.

The actual direction into C is the g in Section 2 with

    k=(s+q)/c>q.

For the D-owned side its exact value simplifies further to k=a/b.
It follows that the general bridge condition is

    1+a+(1-z)b
      <=sqrt(2)+1/sqrt(1+r^2)+1/sqrt(1+k^2),

because direct subtraction of the two original applications gives

    (K-L).e=1+a+(1-z)b.

In the side row, 1/sqrt(1+k^2)=b, so its exact sharper form is

    1+a-zb-1/sqrt(1+r^2)<=sqrt(2).

Both formulas preserve the original full mean z.

The original V2 origin-moment equation remains

    nu*t=mu*(d*s+c/2).

Since t<=1/2 and d>1/2, it gives

    nu/mu>=2d s+c>c+s>1,
    r=(nu/mu)q>q.

The two other original V2 force equations and both physical corner
coefficients remain. This strict ratio does not require each
individual circle coefficient to be positive.

## 5. Complete interval y<=11/50, every exterior return

Write u=cos(theta), y=sin(theta) with 0<theta<pi/2, and
c=cos(phi), s=sin(phi). The original positive b=c y-s u gives
0<phi<theta. Thus

    a=cos(theta-phi)>u,
    0<b=sin(theta-phi)<y.

These facts can also be obtained directly from the unit identities
and b>0; they hold on the entire original chart.

For y<=11/50,

    u^2>=2379/2500>1521/1600,
    u>39/40.

The right side u-z y of the complete D3 identity is then positive
for every original z in [0,1]. The positive q forces
0<b-(1-z)a<=b, and hence

    q>=(u-y)/b>(u-y)/y=u/y-1>151/44.

Both r and k are strictly greater than this bound. Therefore

    1/sqrt(1+r^2)+1/sqrt(1+k^2)
      <88/sqrt(24737)<14/25.

The actual whole-square gap between B and C in direction e is thus
strictly greater than

    1+39/40-14/25=283/200>sqrt(2).

The actual N cannot touch both. The proof includes y=11/50, every
original side mean and both original mean endpoints. Where an
endpoint is inconsistent with the full D3 equation, that is a
deduction from the equation rather than a prior deletion.

The squared reserves are respectively 39/40000,
8452/15460625 and 89/40000, as independently recomputed below.

## 6. Complete D-owned-side interval y<=3/11

For the entire original side row, q=u/b>u/y. Since r>q and k>q,
the exact unit identity gives

    1/sqrt(1+r^2)+1/sqrt(1+k^2)
      <2/sqrt(1+(u/y)^2)=2y.

For y<=3/11 one has

    u^2>=112/121>576/625, u>24/25.

The actual whole-square projection gap is consequently strictly
greater than

    1+a+(1-z)b-2y
      >1+24/25-6/11
      =389/275>sqrt(2).

This excludes the entire side interval, including y=3/11 and all
original positive ratios and side means. The exact positive reserves
are 304/75625 and 71/75625.

The proof uses the actual physical bridge in both D02 callers. It
does not use the unloaded-N condition of only one caller.

## 7. Full high-b upper-return proof, including equality

The extension b>=1/sqrt(2) is valid independently of the D return
row. The original geometry gives b<c and s<a, hence

    0<s<a<=1/sqrt(2)<=b<c<1.

The function r(H) is strictly decreasing, with derivative numerator

    -c*(1-a)-s*(1+b)<0.

At H=1 its numerator exceeds its denominator because

    c-b=(a-s)*(a+s)/(c+b)<a-s.

This stays strict at a=b: the strict s<c gives a+s<b+c. Thus r>1.

The original l>0 gives H>b/c, so

    r<1/(1-a+b*s/c)<=c/s.

For the last comparison,

    (s/c)*(1-b)<(a/b)*(1-b)<=1-a.

Only the second inequality becomes equality when a=b; the first
remains strict. There is no loss of the desired r bound.

For f=(-h+r e)/sqrt(1+r^2), its world y component
(s+rc)/sqrt(1+r^2) increases while r<=c/s. Thus

    f_x<=0, f_y>=(s+c)/sqrt(2),

and, with

    D0=1-a+s, N0=1-c+b,
    X=-c D0+s N0, Y=s D0+c N0,

one has X<=0, Y>0 and f_y>=Y/sqrt(X^2+Y^2).

I checked the complete three continuous intervals directly against
the original expansion.

For b>=9/10, f_y>=1/sqrt(2) is immediate.

For 4/5<=b<=9/10, the exact expansion of Y+(4/3)X has coefficients

    -1/3+(4/3)a+b>=1,
    7/3-a+(4/3)b>=14/5.

Indeed 2/5<a<=3/5 and 4/5<=b<=9/10. Hence

    Y+(4/3)X
      >=c(1-c)+s^2+s(14/5-(8/3)c)>0.

With X<=0 this implies f_y>4/5. This entire interval is separated
from a=b, so its existing endpoints are unchanged.

For 1/sqrt(2)<=b<=4/5, one has 3/5<=a<=1/sqrt(2).
If s>=5/16, the increasing function s+sqrt(1-s^2) gives

    f_y>=(5+sqrt(231))/(16sqrt(2))
        >63/(50sqrt(2))>8/9.

If s<=5/16, hold s,c fixed and vary a from 3/5 to the actual a,
putting b=sqrt(1-a^2). The exact derivative is

    d(Y+2X)/da=(2c-s)-(a/b)(c+2s)
      >=c-3s
      >=(sqrt(231)-15)/16>0.

The inequality a/b<=1 includes its endpoint equality. At a=3/5,
b=4/5 the exact value is

    c(1-c)+4s(1-c)+s^2>0.

Thus f_y>2/sqrt(5)>8/9 throughout this whole interval, including
a=b=1/sqrt(2).

Finally the original actual corner obeys

    K_y>1/2+b,

because the difference after replacing H by its upper bound one is
s+(1-c)(c-b)>0. The actual translated point K+f belongs to the
physical B for any B owner or mask: a unit normal added to an actual
minimum-support point stays inside its unit square, with all side
means and endpoints included.

The three intervals consequently give

    (K+f)_y>209/100>R.

All joining endpoints are included. In the last interval the least
comparison is

    1/2+1/sqrt(2)+8/9>209/100,

with the stated square reserve 6839/810000. This proves the full
high-b exclusion, including equality, without any supplementary
D torque hypothesis or equation at B.

## 8. Literal original transfers and precise surviving domain

The original labels are A=0,V=1,D=2,C=3,N=4,B=5, with rim

    A--V--D--C--N--B--A

and chord AD. A,D retain unloaded true3, and V,B,C retain loaded
true2. N remains unloaded true2 in D02.L135 and loaded true2 in
D02.L1345. Both original BN and CN edges remain positive, hence
supply the physical bridge in both rows.

The new proofs preserve every original force, normal, mean and
circle coefficient. They make no reduced force assumption at N.
The three additional actual units remain unrestricted in the packing
and are unnecessary for the local bridge contradiction.

Combining the newly proved intervals with the earlier complete
adjacent-return and c<=3/4 exclusions gives precisely the stated
necessary residual:

| Original return | Additional necessary surviving conditions |
| --- | --- |
| Opposite D vertex | c>3/4, 11/50<y<1/sqrt(2), z=1, q=(u-y)/b>0 |
| D-owned exterior side | c>3/4, y>3/11, 0<b<1/sqrt(2), q=u/b, z=u a/c in (0,1) |

For the opposite row u>y implies y<1/sqrt(2); b<y already implies
the new high-b restriction there. The side row records the high-b
restriction explicitly. Every original equation and physical
constraint is still required, including the general projection
inequality and its sharper exact side form.

These rows are necessary remainders, not assertions that packings
realizing them exist. Whole-data reflection preserves their exact
scope. No other AD owner, unique-corner feature or physical-two chart
is introduced by changing labels within a fixed configuration.

This does not close either whole D02 load family or any coarse
inventory cell.

## 9. Independently recomputed exact reserves

The following values were recomputed using exact integer fractions.

| Check | Exact positive reserve |
| --- | --- |
| 2379/2500-1521/1600 | 39/40000 |
| (14/25)^2-88^2/24737 | 8452/15460625 |
| (283/200)^2-2 | 89/40000 |
| 112/121-576/625 | 304/75625 |
| (389/275)^2-2 | 71/75625 |
| (209/100)^2-1105/256 | 8271/160000 |
| 1/2-(631/900)^2 | 6839/810000 |
| 1/2-(69/100)^2 | 239/10000 |
| 231-(379/25)^2 | 734/625 |
| 14/5-8/3 | 2/15 |
| 3969/5000-64/81 | 1489/405000 |
| 4/5-64/81 | 4/405 |
| 231-225 | 6 |
| (167/80)^2-1105/256 | 33/800 |

Every radical comparison is between positive quantities before
squaring. These are finite corroborating checks of complete continuous
arguments, not an angle or pose mesh.

## 10. Final adoption verdict

I accept the entire frozen source at
97815bf7d2558343a76316a8095096bb780a8e4fe1664274c1863bcbbb8d6132:
the generic whole-unit projection bound, the actual one-unit bridge
obstruction, all-return interval y<=11/50, full side interval
y<=3/11, high-b exclusion including b=1/sqrt(2), literal original
D02 transfers, and exact retained remainder.

The physical-two individual-zero circle coefficients and all original
shared-mean endpoints remain included. No input manuscript was edited,
no original flag or denominator was changed, and no pose search, angle
mesh, new packing certificate, Lean/Lake build, CI, remote mutation
or merge was performed.
