# Full review of the tilted long-endpoint return profile

Date: October 30, 2026 UTC.

Reviewer: annular_capacity. Source author: axial_chain.

**Verdict: PASS for the complete final frozen source, including the
geometric side-wrapper theorem, full physical vertex/side cover, original
two-circle force caller, and coupled actual support-height budget.**

The reviewed file is

`TILTED_LONG_ENDPOINT_RETURN_WRAPPERS_OBEY_THE_SHARP_SECTION_PROFILE_2026_10_30.md`

with 19,575 bytes and SHA256
`c7553b418c64c12bda69bcccb565e6f5d7cdd1613dbb8eecfe282ce6126a26c3`.

The initial 18,920-byte version had SHA256
`1f093924ca84803969f9fc4c2e7bfbf2cf0e299e27287c57b08db22f0cff1e12`.
During this review the author added the short explicit proof that the
full degree-two long endpoints are positively circle-loaded before the
physical-boundary endpoint theorem is invoked. The final version above,
including that addition, is the version approved here. No further repair
is requested.

The reviewer had contributed the earlier aligned-wrapper squared identity
and the vertical positive-combination observation in discussion. Those
contributions are disclosed; the full tilted parameter range, chord
comparison, original-force quotient and every caller join were separately
reconstructed from the displayed equations. The reviewer is not the author
of the source being approved.

## 1. Full geometric domain and existence of the actual section

The geometric theorem explicitly keeps

    Q=1105/256, z=5/4, g(Y)=sqrt(Q-Y^2),
    17/4<=q<=Q,
    a^2+b^2=1, a>399/400, 0<b<7/100,
    |s|<1/60, -9/16<=t<-1/2,
    (2+|s|)^2+t^2<=q.

The actual vertex is p=(x,f)=(s+1+b,t+a). The resulting strict
parameter bounds are correct:

    87/200<f<1/2, 59/60<x<163/150,
    3/4<k=5/4-f<163/200<7/8,
    7/16<d=g(f+1)-1<51/100.

In particular the lower floor is the exact difference
399/400-9/16=87/200. The upper bound on d follows from the positive
squared reserve 3667/160000 printed in the source. All square-root
arguments used later are positive and below Q.

For the entire original support chart

    C=p+[0,1]n+[r-1,r]u,
    n=(-alpha,beta), u=(beta,alpha),
    alpha,beta>0, alpha^2+beta^2=1, 0<=r<=1,

the top height is f+beta+r*alpha, the minimum x coordinate is
x-alpha-(1-r)beta, and the maximum x coordinate is x+r*beta.
These formulas include both closed side-mean endpoints.

If the top were at most z, then beta+r*alpha<=k<7/8. Thus
alpha>sqrt(15)/8>7/16 and

    r*beta <= beta*(k-beta)/alpha
           <= k^2/(4alpha) < 7/16.

Consequently the whole actual square lies in

    -1/2<X<25/16, -5/8<Y<=5/4.

The minimum x estimate uses alpha+beta<=sqrt(2)<17/12, giving
X>59/60-17/12=-13/30. The maximum x comparison has the exact
positive margin 23/600. The minimum y estimate follows from
f-alpha>87/200-1>-5/8. Hence every actual point has squared norm
strictly below 1025/256, whereas q>=17/4 exceeds this by 63/256.
This contradicts the asserted physical boundary contact of C.

The lower support is below z because the actual point p belongs to C
and f<z. The upper support is strictly above z by the preceding
argument. The resulting actual horizontal section is nondegenerate,
and the relative open interval is in the original open square interior.
No section of an extended side line is confused with an actual section.

## 2. Both actual section-edge candidates

Solving the original two support strips on y=z gives exactly

    ell=max(ell_1,ell_2),
    ell_1=x+(r-1-alpha*k)/beta,
    ell_2=x+(beta*k-1)/alpha.

The first candidate comes from the lower u-coordinate bound, and the
second from the upper n-coordinate bound. The established nonemptiness
makes their maximum an actual section endpoint.

### 2.1 Original upper-corner control of ell_1

For the actual upper corner P=p+n+r*u,

    E=n.P=1-alpha*x+beta*f,
    beta*ell_1=u.P-1-alpha*z.

Containment gives u.P<=sqrt(Q-E^2), independently of the sign of
u.P. Put T=1+alpha*z+beta*d>0. Direct expansion using
(d+1)^2+(f+1)^2=Q and 1-beta=alpha^2/(1+beta) gives

    (T^2+E^2-Q)/alpha
      =2(z-x)+2(zd-xf)beta
       +alpha*(z^2+x^2-d^2-f^2-2(d+f)/(1+beta)).

The exact global bounds are

    2(z-x)>49/150,
    zd-xf>17/4800,
    z^2+x^2-d^2-f^2-2(d+f)/(1+beta)>-59/90000.

The last bound follows by using the smallest allowed x, the largest
allowed d,f and 1+beta>=1. If that bracket is negative, multiplication
by 0<alpha<=1 can only improve its stated lower bound; if it is
nonnegative the same conclusion is automatic. Thus the complete
expression is greater than 29341/90000. Since T is positive,
sqrt(Q-E^2)<T, and therefore ell_1<d. The argument is uniform in
the entire normal quadrant and the entire closed slider interval.

### 2.2 The occupied force-line chord controls ell_2

For D=x-d>0, the original chord inequality gives

    x+1=2+s+b<=b+g(-t)=b+g(a-f).

It is essential that a-f=-t is the actual force-line height, and the
proof preserves it. With A=399/400 and a>A, strict decrease of g gives

    D<7/100+g(A-f)-g(1+f).

The function S(f)=g(A-f)+g(1+f) decreases on the whole closed
interval [87/200,1/2], because Y/g(Y) strictly increases and
A-f<1+f. At its upper endpoint,

    S(1/2)>g(1/2)+23/16>161/80+23/16=69/20.

The radical comparison uses the exact positive reserve 13/800.
Rationalizing gives

    g(A-f)-g(1+f)
      =(1+A)(1-A+2f)/S(f)
      <1/690+(80/69)f.

Thus 0<D<L(f)=493/6900+(80/69)f. I independently recomputed the
two endpoint values of L(f)^2+(5/4-f)^2:

| f | Value | Reserve below one |
| --- | --- | --- |
| 87/200 | 7585357/7617600 | 32243/7617600 |
| 1/2 | 23483837/23805000 | 321163/23805000 |

The expression is a convex quadratic on the entire closed interval,
so these two positive exact reserves establish D^2+k^2<1 everywhere.
Then alpha*D+beta*k<1 by Cauchy--Schwarz, proving ell_2<d. This is
a whole-interval proof, not an inference from sampled endpoint poses.

Together the two edge arguments prove the complete geometric side
profile, with strict inequality throughout its declared domain.

## 3. Complete physical vertex/side contact cover

The source reproduces the inward-owned-face obstruction in full.
For a physical boundary square

    [kappa-1,kappa] x [lambda-1,lambda],
    kappa-lambda>1, lambda>=1/2, kappa^2+lambda^2=q,

a neighbor wholly on the inward side and touching that side has an
actual vertex P=(kappa-1,y), |y|<=lambda, in the common face.
If the contact face of the neighbor is a side, its length-one interval
and the original length-one interval have an overlap containing one
of the neighbor's endpoints. Thus the vertex assertion includes
shared sides and contacts at their endpoints.

The two unit edge directions from P have nonpositive first components.
Each adjacent vertex has squared norm at most
q-2kappa+2lambda+2<q. Their sum has first component at most -1 and
absolute second component at most one. The opposite vertex therefore
has squared norm at most q-4kappa+2lambda+5<q; the last strictness
uses kappa>lambda+1 and lambda>=1/2. P itself is strictly inside.
This proves that the neighbor cannot physically touch the same circle.

For the actual tilted B, its own center coordinates satisfy

    P_B>35541/24000,
    |a*t+1/2|<=1/16,
    |T_B|<401/3000,
    P_B-|T_B|>32333/24000>1.

These constants were checked independently. In particular
a*t+1/2 lies between -1/16 and 1/800. Reflecting the second own
axis if necessary gives the exact face-obstruction parameters
kappa=P_B+1/2 and lambda=|T_B|+1/2. Consequently the direction
-u_B cannot separate B from a physical boundary neighbor at that face.

At a neighbor vertex p, the two actual contact-normal cones are
closed angular intervals of length pi/2. Their intersection contains
the unchanged original normal n. At least one endpoint of B's cone
belongs to the neighbor's cone: otherwise the latter interval would
be strictly contained in the former despite having equal length.
The forbidden endpoint -u_B is excluded by the preceding face proof.
Thus v_B is also a geometric minimizing normal on C at p.

Because n=(-alpha,beta), alpha,beta>0, and v_B=(b,a) with b>0,

    alpha*v_B+b*n=(0,alpha*a+b*beta)

is a positive multiple of e_y. Both original support inequalities
minimize at the same actual p, so their positive combination proves
the genuine whole-square floor C subset {y>=f}. No auxiliary direction
is substituted into any force equation. The complete unequal-floor
theorem applies to this branch, including normal-cone endpoints.

If p is instead in a neighbor side interior, its unchanged original
normal is the unique inward own normal of that side and gives exactly
the chart already covered above, with 0<r<1. The geometric theorem
also included r=0,1, so no endpoint mean is omitted. This exhausts
the actual side and vertex alternatives and proves the complete
physical return profile with the stated strictness.

## 4. Full original-force caller and both circle weights

The final source explicitly supplies physical boundary status for its
true-degree-two endpoints. If B were zero-loaded, full translational
balance would propagate the long normal through U,V,B. The actual
three internal projection widths are each at least one; telescoping
therefore forces center projection at least four between A and the
next return body. This contradicts 2M=91/30. The same argument
applies at A. This is the complete entry clarification added during
review; it uses the original stars and does not identify zero load
with physical circle clearance.

The above-axis neighbor condition in this caller is the actual
wholly-y>0 condition of the pinned contact-locus input in the centered
long-normal frame. It is not the weaker condition y>t relative to an
offset force line. With that literal input, the unchanged endpoint
theorem gives the negative tilt sign, actual upper-inner return mean,
t<-1/2, the chord bound, and positive original return-normal y component.
The support gap independently gives q>=17/4 through a center of norm
at least 3/2. No lower-radius window is an additional premise.

Let m be the full nonnegative circle-weighted corner sum. The possible
physical corners are z_-=(X+a,t-b) and z_+=(X+a+b,t-b+a), with
X=s+1. Their x coordinates are positive. The full endpoint y equation
gives m_y<0; it is not asserted that every individual circle atom has
negative y. If T_B=0, both original circle weights are retained.

The original force and origin-moment equations give, for the intercept
of the original return-normal line with y=t,

    x_0=t*m_x/m_y.

I checked the elimination directly: substitute
mu=2m_x+nu*n_x and nu*n_y=-2m_y into the angular equation,
using p cross n=n_y*x_0-t*n_x. The pair-force terms cancel to
2m_x*t-2m_y*x_0=0.

The ratio m_y/m_x is the convex combination of the actual corner
slopes with weights equal to each original circle weight times that
corner's positive x coordinate. It is at least (t-b)/(X+a).
Both ratios are negative, and t<0, so the direction of the resulting
inequality is

    x_0>=t*(X+a)/(t-b).

Writing tau=-t, this yields the displayed lower bound

    -n_x/n_y >= [tau*(a-b)-b*(X+b)]/[a*(tau+b)].

The numerator is positive in the stated domain. Replacing a by one
in the denominator lowers the quotient. The remaining quotient
increases with tau, with derivative proportional to b(a+X)>0.
The exact substitutions a-b>37/40, b<17/240, X<61/60 and tau>1/2
therefore give

    -n_x/n_y>7401/10960>2/3,

with final reserve 283/32880. The a-b comparison has squared reserve
19/2880. Thus the original return normal is strict northwest. No
set distance between the two return squares enters this local proof.

The source correctly separates other callers: an endpoint whose next
neighbor is an unloaded transmitter cannot be assigned that neighbor's
physical boundary status. Such a caller must supply its own actual
upper-inner point and strict original normal, as the adjacent-cycle
input does.

## 5. Actual coupled heights, imports, and final scope

For actual horizontal widths w_i, let
E=(w_A+w_B-2)/2, 0<=E<1/30. The pinned coupled endpoint estimate gives

    |y_A|+|y_B|<=1/8-E+(320/39)E^2.

The highest horizontal support of a unit square is
f_i=y_i+w_i/2, since its horizontal and vertical widths agree.
For nonpositive endpoint center heights, summing gives exactly

    f_A+f_B>=7/8+2E-(320/39)E^2.

The excess is positive for E>0: its linear factor is greater than
2-32/117=202/117. For the tilted chart f_B=t+a is exactly this
actual highest support, and for an aligned endpoint it is y_B+1/2.
No tilted support is replaced by a fictitious horizontal side.

The three explicitly imported frozen source hashes were checked:

| Input | SHA256 |
| --- | --- |
| Complete long-endpoint contact locus and vertex reduction | `cf942c1069e451ad043c80c8075fd67c85d2b71faa05c29b9baa3dae32f66fe3` |
| Two-endpoint expanded-square cover and coupled height estimate | `78dfc5ed83b1538b2484007fc6d60d047c078b7f124944c0aef4dce6593558f6` |
| Complete unequal-floor section profile | `abfb4887037851d2715c8ff746ff11dc238109692b2cc0fbc42598bb4dae9d94` |

All uses respect their full geometric or original-force hypotheses.
The theorem does not itself order several section intervals, infer a
whole-set distance from a slice gap, or close a cycle without its
remaining geometric premises. Those are explicit obligations of later
assemblies. Within its stated scope the proof is complete over every
allowed orientation, side parameter, circle-weight combination and
closed geometric endpoint.

This review used source reconstruction and exact rational/algebraic
checks only. It used no numerical pose search, force reselection,
removed physical square, original ledger mutation, Lean compilation,
CI execution or publication.
