# Independent full review: boundary terminal with a low physical port

Date: October 28, 2026 UTC. Reviewer: sole-UT continuation.

**Disposition: PASS at the exact source hash below.** I read the entire
source and checked the geometric lift, the complete continuous distance
argument, its scalar identity, all sign conditions before squaring, and
every stated endpoint.

Reviewed source:

    BOUNDARY_TERMINAL_CENTER_LOW_PORT_ARC_ANGLE_BOUND.md
    SHA256 d94502aed4091098a1fa23801284a734f9f42989f130a5f0d9b0f464bb7497e6

Independence disclosure: before reading the source, I received the
intended theorem statement and intended reuse from the author and root.
I made no contribution to its discovery, constants, scalar inequality
or proof. I did not use root's reported PASS as a substitute for this
independent check. My own earlier sole-UT chart is not an input to the
reviewed lemma.

## 1. Actual physical premises and the center lift

The actual boundary unit E has a physical circle corner at distance
1/sqrt(2) from its center C. Therefore |C|>=R-1/sqrt(2)>129/100 on the
stated R>2 range. Every actual point P of E has |C-P|<=1/sqrt(2).
These statements do not require P to be a vertex, circle contact or
force application.

If C_x>=0, moving the comparison point P=(-A,-h) horizontally to
(0,-h) decreases its distance to C. The reverse triangle inequality
then makes that distance greater than 129/100-27/100=102/100,
contradicting the circumradius bound. Thus C_x<0, proving the unique
claimed lift theta in (pi/2,3pi/2). This proof includes A=1 and both
closed h endpoints. No lower positive bound on A is silently added.

For C_y>=0, theta<=pi and the theorem follows directly. For C_y<0,
the actual c,s are strictly positive, satisfy c^2+s^2=1, and the
physical point-distance gives r*s<=h+sigma<98/100. This is valid even
when h is negative. The stated s<4/5 and c>3/5 therefore follow.
The case phi<=beta is explicitly discharged before the stronger
lower bound s>1/4 is used.

## 2. Correct angular equivalence

Since 0<A<=1<rho=5/4,

    theta_A=pi/2+arcsin(A/rho).

With theta=pi+phi, the desired inequality is exactly

    phi-beta<arcsin(A/rho).

On the retained phi>beta branch, both sides lie in the increasing
sine domain. Thus proving A>rho*sin(phi-beta) is sufficient and has
the stated strict direction. No major/minor-angle ambiguity remains.

## 3. Whole-domain distance contradiction

Under the alleged reverse inequality, angle subtraction with the exact
beta values gives

    r*c-A >= (r+rho*sin(beta))*c-rho*cos(beta)*s.

The rational bounds in the source make this strictly larger than
(83/50)c-(6/5)s, which is positive by c>3/5 and s<4/5. Independently
r*s-h>(129/100)s-27/100>0 on s>1/4. Both coordinate lower bounds are
therefore legitimately squared. This sign check matters because the
contradiction uses their sum of squares rather than an unsigned norm
bound.

I independently expanded that sum after subtracting 1/2. Modulo
c^2+s^2=1 it is precisely

    4657/2000+(697/2000)s^2
      -(498/125)c*s-(3483/5000)s.

The estimate c*s<=1/2 yields the printed quadratic f(s). Its derivative
is negative on the whole closed interval [0,4/5], so its minimum there
is the displayed positive f(4/5). This is a continuous global scalar
bound; it is not a verification at finitely many square poses.

Thus the actual squared distance would exceed 1/2, contradicting the
unit circumradius. The upper A endpoint, both h endpoints, the possible
zero center height and phi=beta have all been retained or separately
discharged with strict final inequalities.

## 4. Exact scalar checks

| Comparison | Exact difference |
| --- | --- |
| (71/100)^2-1/2 | 41/10000 |
| 4/5-98/129 | 26/645 |
| 25/281-1/16 | 119/4496 |
| 625/16-281*(37/100)^2 | 371/625 |
| 36/25-400/281 | 116/7025 |
| (83/50)*(3/5)-(6/5)*(4/5) | 9/250 |
| (129/100)*(1/4)-27/100 | 21/400 |
| (697/1000)*(4/5)-3483/5000 | -695/5000 |
| f(4/5) | 113/50000 |

Exact rational arithmetic checked these printed constants and the
expansion. The geometric and continuous inequalities above provide
the mathematical proof.

## 5. Accepted scope and caller boundary

The complete force-free center-angle statement passes. It allows any
true degree, physical circle mask, individual zero coefficient and
actual point type because none is narrowed by its proof.

The source correctly separates its metric conclusion from actual
occupied-crosscut routing. Its final two-extra consequence requires an
independent proof that every complete extra arc lies in the stated
angular interval, plus the actual arc-length and interior-disjointness
facts. This review does not certify an unseen pocket proof or assign
the lemma to a caller without those premises.

No original gate, force, application, mean, normal, circle corner or
packing unit is changed. No Lean compilation, CI, workflow, pose mesh,
numerical exclusion certificate, shared-ledger edit or remote write
was performed in this review.
