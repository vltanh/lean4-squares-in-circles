# An upper-return compensation inequality excludes the whole large b domain

Date: October 29, 2026 UTC. Author: roofs continuation.

**Status: complete proposed hand theorem, submitted for full independent
review.** The actual upper-return height admits one uniform lower bound
throughout the entire roof-angle and original mean domain. It excludes
every perpendicular-singleton return with b>=16/25, at arbitrary exterior
degrees and loads. The proof does not use a D return row, a B--N--C
bridge, an additional positive edge or an equation at an exterior unit.

The previous whole b>=1/sqrt(2) exit is thereby strengthened. Both original
D02 rows remain open outside the exact features stated below.

## 1. Complete actual chart and force premise

Keep the same nine actual contained squares, original physical circle
origin and physical-two West/strict roof of

    PHYSICAL_TWO_WEST_STRICT_PERPENDICULAR_SINGLETON_ADJACENT_RETURN_EXCLUSION_AND_COMPLETE_RESIDUAL_2026_10_29.md
    SHA256 f3718c86a99ef196eba1ee875b66375582a0fc588f10275ec171c442e46780dd.

The unchanged original data include

    79/40<=R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1,
    V=[d,d+1] x [-1/2,1/2],
    P=(d,1/2), Q=(d,-t), 0<t<=1/2,
    H=t+1/2, 1/2<H<=1,
    h=(c,-s), e=(s,c),
    c,s>0, c^2+s^2=1.

A,D are the two unloaded true3 hubs, V the loaded true2 unit with
two PHYSICAL circle corners. The entire positive stars remain

    A:{V,D,B}, D:{V,A,C}, V:{A,D}.

The original A-to-V normal h is A-owned and strict at V. The physical
singleton AD is owned by A alone with perpendicular normal -e from A.
The complete geometric entry supplies

    A=P+[-1,0]h+[-l,1-l]e,
    W=P-xh-le,
    0<l<1, 0<x<1,

    v=W-Q=-a h+b e=(-u,y),
    a=H s+x>0, b=H c-l>0,
    a^2+b^2=1,
    0<b<c, 0<s<a.

The symbols a,b are the actual D-side components in the A frame, not
the coordinates of a circle corner. They are not independently varied
physical squares during the argument.

The full unloaded A3 force and torque, at the original P,W and exterior
application, give

    F_B=-mu h+gamma e, mu,gamma>0,
    K=P-h+(1-l)e,

    r=gamma/mu=(1-l)/(1-x)
       =(1-H c+b)/(1-a+H s)>0.                     (1)

K is the actual strict A support vertex, and belongs to the actual B
minimum-support face in direction

    f=F_B/|F_B|=(-h+r e)/sqrt(1+r^2).               (2)

The actual D3/V2/B/C/N and completion equations remain unchanged.
Only the complete A3 equation (1) is needed after the physical chart.

**Uniform height theorem.** If b>=1/2 and c>s, then the actual B
contains a point whose world vertical coordinate is strictly greater than

    1/2+b+sqrt((1+a)/2).                            (3)

In particular, if b>=16/25 and c>s, B contains a point higher than
52/25. The containing-radius bound excludes that whole domain.

## 2. The actual point retained in B

The chosen point will be the actual K+f, which belongs to B.
Here is the complete elementary support fact, including means.

Write the actual B own frame as orthonormal i,j, with each own-coordinate
interval of length one. Since K minimizes f on B, whenever f.i>0
its i coordinate is the lower endpoint, and whenever f.i<0 it is the
upper endpoint. The coordinate increment f.i has absolute value at
most one and points inward, so adding it remains in the same interval.
If f.i=0, that coordinate of the original K or mean is unchanged.
The identical argument applies to j. Thus K+f is in the actual
closed B for every support owner, side point and endpoint.

The vertical coordinates from (1)--(2) are

    K_y=1/2+s+c*(1-H c+b),
    f_y=(s+r c)/sqrt(1+r^2).                       (4)

No exterior square has been replaced by this point. Its actual
containment is a necessary consequence of containment of the full B.

## 3. A uniform bound on the return-angle change

Assume b>=1/2 and c>s. Put

    c=cos(phi), s=sin(phi), 0<phi<pi/4,
    D0=1-a>0, N0=1-H+b>=b>0,
    r0=N0/D0, psi0=atan(r0).

The number r0 is an auxiliary scalar comparison for the *same* a,b,H.
It is not obtained by rotating or reconstructing any actual square.
Since a,b>0 and a^2+b^2=1, one has a+b>1 and hence

    r0>=b/(1-a)>1,
    pi/4<psi0<pi/2.                                (5)

Rewrite the actual ratio (1) as

    r=[N0+H*(1-c)]/[D0+H*s].

Because r0>1>tan(phi/2)=(1-c)/s, this actual r is strictly
smaller than r0. Define

    delta=atan(r0)-atan(r), 0<delta<pi/2.

The exact tangent difference is

    tan(delta)
      =H*[N0*s-D0*(1-c)]
         /[D0^2+N0^2+H*D0*s+H*N0*(1-c)].

Every denominator and every displayed additional denominator term is
nonnegative, with D0,N0 positive. Therefore

    tan(delta)
       < H*N0*s/(D0^2+N0^2)
       <= (H/N0)*s
       <= s/b
       <= 2s.                                    (6)

Meanwhile 0<2phi<pi/2 and

    tan(2phi)=2s*c/(c^2-s^2)>=2s.

For the last inequality, c>=c^2-s^2=2c^2-1 follows from
(2c+1)(c-1)<=0. The relevant tangent branch is increasing, so
(6) proves

    0<delta<2phi.                                 (7)

Thus the actual angle

    psi=phi+atan(r)=psi0+phi-delta

lies strictly between psi0-phi and psi0+phi. By (5), this entire
comparison interval is in (0,pi). Sine is concave there, so its
minimum over that interval is at an endpoint. Since psi0<pi/2,
the smaller endpoint sine is sin(psi0-phi). Consequently

    f_y=sin(psi)
        >=sin(psi0-phi)
        =c*sin(psi0)-s*cos(psi0).                  (8)

All comparisons include H=1 and b=1/2. The actual physical strict
tilt s>0 remains; no side-angle endpoint was removed from its caller.

## 4. Exact compensation by the unchanged corner height

The lower bound (8) can lose at most s from the zero-tilt scalar
comparison. Indeed

    c*sin(psi0)-s*cos(psi0)-[sin(psi0)-s]
      =s*(1-cos(psi0))-(1-c)*sin(psi0)
      =s*sin(psi0)*
          [tan(psi0/2)-tan(phi/2)]
      >0,                                        (9)

because psi0>pi/4>phi. The half-angle denominators are positive
on these exact intervals. Therefore

    f_y>sin(psi0)-s.                              (10)

The actual K height in (4) has precisely the compensating positive
term. Since H<=1,

    K_y>=1/2+s+c*(1-c+b)
         =1/2+b+s+(1-c)*(c-b)
         >1/2+b+s.                               (11)

Here c<1 and c>b are the original strict geometric inequalities.
Neither the application nor either original mean has been altered.

Combining (10)--(11),

    (K+f)_y>1/2+b+sin(psi0).

Finally r0>=b/(1-a)=(1+a)/b, so monotonicity of sine after arctangent
on the positive interval gives

    sin(psi0)
       >= (1+a)/sqrt((1+a)^2+b^2)
        =sqrt((1+a)/2).                           (12)

Equations (10)--(12) prove the complete uniform height theorem (3).

The compensation is a scalar comparison of original quantities.
It does not assume that changing phi at fixed a,b,H preserves a
packing, a contact, a circle corner or a force certificate.

## 5. One concavity argument treats the entire b>=16/25 interval

For 0<b<1 define

    a(b)=sqrt(1-b^2),
    J(b)=sqrt((1+a(b))/2),
    G(b)=1/2+b+J(b).

Its continuous extension to b=1 has J(1)=1/sqrt(2).
Direct differentiation on 0<b<1 gives

    J'(b)=-b/(4*a*J),

    J''(b)= -1/(4*a*J)
            -b^2/(4*a^3*J)
            -b^2/(16*a^2*J^3)<0.

Hence G is concave, and its minimum over the closed comparison
interval [16/25,1] is at one of its endpoints. At b=16/25,

    a^2=369/625>(959/1250)^2,
    369/625-(959/1250)^2=2819/1562500>0.

Both sides being positive, this implies a>959/1250. Since

    (1+959/1250)/2=(47/50)^2,

one has J(16/25)>47/50. Consequently

    G(16/25)>1/2+16/25+47/50=52/25.

At b=1,

    G(1)=3/2+1/sqrt(2)>3/2+3/5=21/10,

using 1/2-(3/5)^2=7/50>0. Also 21/10>52/25.
Concavity therefore proves

    G(b)>52/25 throughout 16/25<=b<=1.              (13)

The physical domain has b<1; the endpoint b=1 is only an exact
continuous comparison endpoint. No hypothetical degenerate square
is used as a physical input.

By (3),(13) the actual point K+f has height greater than 52/25.
But throughout the original closed radius interval,

    (52/25)^2-R^2
       >=(52/25)^2-1105/256
        =1599/160000>0.                            (14)

This is impossible for any point of the actual contained B.

## 6. All original roof-angle alternatives and literal D02 transfer

The new height argument assumes c>s. The entire complementary
angle domain c<=s satisfies c<=1/sqrt(2)<3/4. It was already
excluded for *every* D return and original mean by Theorem B of the
frozen perpendicular-singleton source. Thus those two complete
alternatives join to give:

**Entire large-b conclusion.** Every original perpendicular-singleton
configuration with b>=16/25 is impossible, regardless of the D exterior
support row, every original C-side mean and endpoint, or any degree
or physical circle mask at B,C,N.

No second branch is lost at c=s; that equality is contained in the
previous closed c<=3/4 theorem. The new b=16/25 endpoint belongs to
the concavity proof (13).

For D02.L135 and D02.L1345 retain exactly

    A=0, V=1, D=2, C=3, N=4, B=5,

the original rim A--V--D--C--N--B--A and chord AD. A,D stay unloaded
true3; V,B,C stay loaded true2; N stays unloaded true2 in L135 and
loaded true2 in L1345. Every positive force and full mean at B,C,N
remains. The three actual completing squares remain arbitrary and
present. The proof requires no equation at any of them.

Together with the previous complete adjacent-return and c<=3/4
exclusions, a survivor of this exact physical feature must therefore
have c>3/4 and 0<b<16/25. The separate actual-unit projection theorem

    ACTUAL_UNIT_PROJECTION_BRIDGE_AND_PERPENDICULAR_SINGLETON_RETURN_INTERVALS_2026_10_29.md
    SHA256 97815bf7d2558343a76316a8095096bb780a8e4fe1664274c1863bcbbb8d6132

also retains its exact two necessary rows:

| Original exterior support at D | Remaining conditions after the complete joins |
| --- | --- |
| Opposite vertex | c>3/4, 0<b<16/25, 11/50<y<1/sqrt(2), original z=1 and q=(u-y)/b>0 |
| D-owned exterior side | c>3/4, 0<b<16/25, y>3/11, original q=u/b and z=u*a/c in (0,1) |

Every original force equation, support inequality, physical containment
condition and the full necessary projection inequality in that source
remain in both rows. These are necessary residuals, not constructions.

Whole-data reflection transports the entire physical chart, labels,
normals, coefficients and original means. Other AD owners, other
physical-two charts and all unique-physical-circle types remain at
their own exact scopes. Neither entire D02 load row, a coarse parent,
the global selection audit, equality classification nor Lean is closed
by the present theorem.

## 7. Inputs, full-source boundary and verification

The frozen perpendicular-singleton source supplies only the original
actual chart, its whole A3 equations, and the earlier complete
c<=3/4 exit. The new continuous ratio comparison, angle compensation,
concavity and height contradiction are fully printed above. They
do not assume or use the adjacent D torque inequality a<b.

PHYSICAL_CONTACT_STRESS.md at SHA256

    d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5

retains the original force, moment and actual-mean convention.
SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md at SHA256

    cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1

retains the exact original graph/load substitutions. No additional
normal selection is made; the earlier conditional common-selection
domain remains unchanged.

The comparison uses one entire interval in phi and one concavity
argument over the complete b interval. The three printed rational
reserves were recomputed exactly. They corroborate the continuous
proof and are not a pose sample, angle mesh or packing certificate.
Complete separate independent review is required before adoption.

No source, original flag, original identifier, ledger or metadata was
edited. No physical square, force, normal, mean, circle coefficient
or true degree was changed. No Lean/Lake build, CI/workflow, remote
mutation or merge was used.

