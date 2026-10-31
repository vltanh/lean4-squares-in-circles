# Full independent review: lower-house TAC.S with the aligned upper C

Date: October 28, 2026. Reviewer: hexagon.

**Decision: ACCEPTED, unchanged, for the complete original aligned
strict-low C-upper/A-lower placement.** I read the entire physical
manuscript and exact checker, read the operative portions of every
direct input and their actual degree restrictions, independently
derived the whole geometric argument, reproduced the author's complete
certificate, and separately reconstructed every terminal box with a
new exact rational implementation. No correction is requested.

This is a full physical, scalar-domain and code review of a
root-authored source. It does not count root's own calculation or
rooted_blocks' contribution to the lower-root sign observation as
independent verification. In particular I derive that sign below
using a separate rational positive-definite identity. The earlier
accepted local geometric inputs remain literal prerequisites, with
their degree restrictions checked explicitly.

| Reviewed artifact | SHA-256 |
| --- | --- |
| HOUSE_LOWER_TAC_S_ALIGNED_UPPER_C_EXCLUSION.md | b773da381ac721c0f3c06083c9da6258ea1142353fd4a6e000edaff1d8398125 |
| certificates/aligned_low_s_upper_c_visibility_separation.py | d57e7506d4f6e1dd92c991c8579fcfcd03377703863b0d42d50f417267fe2c4c |

## 1. Exact original graph, radius and inherited chart

The original edges are AT, DT, AD, AB, BC, CD and BL. Their full
degrees are A3, D3, B3, T2, C2 and L1. The positive block loads
are T,A,C, with the genuine S leaf L also positively loaded. D
is unloaded but is not assumed physically clear. B is physically
clear by the genuine-leaf reduction. All three remaining physical
units are retained. Neither AD nor either force at T is deleted.

This is precisely the lower-root TAC row of the original rooted
five-body load cover. The proof uses the existing same-nine R>2
theorem, whose current provenance is the accepted five-charge proof.
It then treats exactly 2<R<sqrt(17)/2. The elementary implication
d=sqrt(R^2-1/4)-1>14/15 has squared reserve 11/900. No low-radius
configuration is discarded by a statement about only the six core
units, and the high/critical and complementary placements remain
separate whole-family inputs.

I read all of S_LEAF_C5_ALIGNED_LOW_RADIUS_EXCLUSION.md. Its
Sections 1--6 are explicitly local at the actual genuine degree-three
root and allow arbitrary degrees and other forces at its two
physical boundary neighbors. Only Section 7 needs the additional
three-edge all-boundary path, and that section is not used here.
Thus the substitution of the original B for the local root is
legitimate even though A has degree three and D need not be boundary.

In the stated placement the unchanged actual chart is

    B=[-a,d] x [-g,h], L=[d,d+1] x [-1/2,1/2],
    a=1-d, g=1-h, 29/50<h<2/3,
    P_C=(-a,h), n=(-c,s), j=(-s,-c),
    P_A=(x,-g), 3/10<x<=d,
    c/s=(x+a)/h, c,s>0, c^2+s^2=1.

I checked the full root force and torque cover that supplies these
relations. In particular the lower normal is exactly South, and the
two actual applications are distinct. The lower A is physically
tilted before the singleton selection is used. At a hypothetical
free BC normal, the fixed physical applications give the nonzero
selection vector (-(x+a),h). The old finite avoidance is therefore
made at the physical pose before extraction; no actual multiplier,
mean or subsequently chosen normal enters it. It forces C to own
the strict Northwest root normal. The original uncrossing and
thinning rules preserve this consequence. No A2 premise is present.

The lower actual frame is

    A=P_A+[0,1](b,-t)+[0,1](-t,-b),
    b,t>0, b^2+t^2=1.

I read the complete lower-boundary unique-corner theorem and checked
its whole-q physical screen. Its Sections 1--3 prove that the only
physical circle corner of this A is

    Z_A=(X,-Y), X=x+b-t, Y=g+b+t,
    X^2+Y^2=R^2.

Those sections use no force or degree at A. Its later degree-two
concurrence and b>=t conclusions are not imported. Both b<t and
b>=t remain throughout the current source and certificate.

## 2. Independent derivation of the lower A sign and screen

If X<=0, then |X|=t-b-x<t-b, because x>0. Hence

    R^2<(t-b)^2+(g+b+t)^2
       =2+2g(b+t)+g^2
       <2+297/250+441/2500=4-1589/2500.

Here g<21/50 and b+t<=sqrt(2)<99/70. This contradicts R>2,
so X>0 in the original physical chart.

If x<=t, then 0<X<=b. The needed quadratic bound can be checked
without an eigenvalue approximation:

    (21/8)(b^2+t^2)-[b^2+(b+t)^2]
       =(5/8)(b-(8/5)t)^2+t^2/40>0.

Thus

    R^2<=b^2+(g+b+t)^2
       <21/8+297/250+441/2500=4-53/5000.

This independently proves x>t with no A2 properness, no ordering
of b,t and no use of either actual return mean. Every point of A
therefore has horizontal coordinate at least x-t>0 and vertical
coordinate at most -g. The source's two printed reserves agree
exactly with rational arithmetic.

Since b+t>1 and x>t, the real edge from P_A in direction (b,-t)
crosses x=d before its other endpoint: x+b>1>d. Nonoverlap with
the unchanged real leaf gives

                    (d-x)t >= (h-1/2)b.

The weak leaf-corner crossing is retained. Because b>0 and h>1/2,
this also makes x<d. For t>2/25, the complete split in the source
is valid: if b<7/10 then t>sqrt(51)/10>7/10; otherwise use
b>=7/10, d-x<7/10 and h-1/2>2/25 in the actual screen.
This covers both entire lower tilt directions, including b=t.

## 3. Full upper C2, unique physical mask and every return mean

The original incoming mean is retained by

    C=P_C+[0,1]n+[-rho,1-rho]j, 0<=rho<=1,
    N=ac+hs>0, K=hc-as=xs>0,
    W=K+rho, delta=1-rho.

The physical chart excludes every corner on the inner n face by
comparison with its outer counterpart. The outer corner having
j coordinate 1-W has squared norm below 389/100<4. Thus C has
one physical circle corner, exactly (N+1,-W), and
R^2=(N+1)^2+W^2. No second physical corner is erased by setting
its weight to zero; its physical existence has been excluded.

The full C2 equation has incoming B force along -n and a positive
circle resultant with strictly negative j coordinate. Hence its
actual return normal has strictly positive j component. This proves
nonparallelity directly, without a boundary status assumption at D.
I read the nonparallel proper-concurrence lemma in the five-cycle
domain and checked its unique-corner calculation against C7 Section 4
and the explicit rectangle argument in the triangle-chain Lemma 2.1.
The boundary-neighbor hypothesis in the older full lemma was used
to establish nonparallelity. It is not needed for the already
nonparallel unique-corner calculation used here.

Consequently the actual concurrence lies in C and on the incoming
normal line. Its coordinates give exactly

    q=(N+lambda,-K),
    lambda=(K-N*rho)/(K+rho)>=0.

This retains lambda=0 and coincident force-line applications. The
negative circle coordinate also ensures the return's j component
cannot vanish. The complete support cover is the near corner, the
owned +j side, or the far corner. For the owned side, its unchanged
force line fixes the actual n-coordinate to N+lambda, including
zero return distance and both side endpoints. There is no free
choice of a new side mean.

I read the entire upper-boundary return source. Only its physical
chart, full C2 feature cover and contained-neighbor far-return exit
are imported. The latter uses N>1/4, K<5/9, rho>7/8 and
lambda<2/5 to show the actual far support is greater than
27/25>1>d. A contained unit cannot lie beyond it. Its subsequent
boundary-neighbor and S124 conclusions are not needed for D.

For completeness, rho>7/8 follows from N^2+K^2=a^2+h^2<101/225
and the triangle inequality: rho<=7/8 would give
R<sqrt(101)/15+sqrt(113)/8<2. I checked the exact squared reserve
3666721. The only actual return applications remaining are therefore

    Q=P_C+u*n+delta*j,
    u=0 or u=lambda.

The source's stronger mean bound is valid uniformly. Because
K=xs<h<=2/3 and N>=hs=(h/x)K>=(29/50)K,

    lambda <= (197/400) K/(K+7/8)
           <= 197/925 < 1/4.

Both rational constants are exact. This inequality enlarges the
range of the actual mean; it does not alter that mean. In particular
rho=1, delta=0 and lambda=0 remain in the scalar enlargement.

## 4. Complete segment obstruction at the actual B square

Write

    A0=a+x-t>0,
    L=u*c+delta*s>=0,
    H=1+u*s-delta*c>7/8.

The actual CD point is Q=(-a-L,H-g). The unchanged actual AD
point P belongs to the lower A, so P_x>=x-t>0 and P_y<=-g.
Both Q and P belong to the same actual unit D. Its convexity and
diameter give [Q,P] subset D and |P-Q|<=sqrt(2), independently
of D's frame, mean endpoints, circle mask or force equation.

The segment cannot enter int(B). This statement is valid also
when the segment runs along D's boundary: any point of a
full-dimensional closed square inside an open set has interior
points of that square arbitrarily near it. Such an entry would
therefore violate disjoint open interiors of D and B.

If L=0, positivity of c,s and nonnegativity of u,delta give
u=delta=0. Then Q=(-a,h), and the segment toward P immediately
enters int(B); this actual zero-distance case is explicitly closed.

For L>0, the segment crosses x=-a at an interior parameter. Its
height must be at most -g. Here is the complete top-edge check.
If Q_y<=h, its crossing height is strictly below h. Any crossing
above -g would then enter int(B). If Q_y>h and P_x>=d, the
horizontal distance is at least 1+L and the vertical distance is
greater than 1, contradicting |P-Q|<=sqrt(2). Thus P_x<d in
this case. A crossing on or above the top edge would subsequently
enter below that edge at an x strictly between -a and d. Equality
at the top-left vertex also enters immediately. Therefore the only
possible crossing is on or below the lower-left corner in every
case. The lower-corner equality is retained.

The crossing-height formula gives exactly

    (P_x+a+L) H <= L(Q_y-P_y) <= sqrt(2)*L,
    (A0+L) H <= sqrt(2)*L.

The second inequality uses P_x+a>=A0, and the first uses the
actual positive vertical displacement and diameter. No hidden
one-unit vertical reach bound is assumed for a tilted D. This is
the necessary condition contradicted by the scalar proof.

## 5. Entire coupled scalar domain and all outward operations

The initial closed box is

    14/15<=d<=1, 29/50<=h<=2/3, 2/25<=t<=1.

All dependent quantities in source (19) retain their actual
definitions. In particular both circles use the same
R^2=(d+1)^2+1/4; X and W are the nonnegative radicals from
those circle identities; x=X-b+t; rho=W-xs; and lambda is its
original proper-concurrence quotient. The retained constraints are
R^2>4, X>0, 3/10<=x<=d, x>=t, the weak leaf screen,
7/8<=rho<=1, and 0<=lambda<=197/925. There is no b>=t
premise and no degree-two formula at the lower A.

I checked each exact author interval operation. Addition, negation,
all four multiplication products and squaring enclose every possible
sign pattern. Division requires a strictly positive denominator
interval. The radical floor is the exact 48-bit dyadic floor,
with the upper endpoint increased by one step unless the value is
an exact square. A formal negative lower radicand is only clamped
to zero, while an impossible upper radicand is separately rejected.

Every rejection is a necessary-domain contradiction. The radius
guard uses an upper bound at most four, matching the strict R^2>4
premise. The X guard likewise respects X>0. Both x intersections
retain the displayed weak endpoints, even though the diagnostic
reason strings use some strict notation. The X contraction uses
the exact unchanged identity X=x+b-t. The screen is rejected only
when its upper bound is strictly negative. The W radical is
rejected only when its upper bound is negative. The rho and lambda
intersections retain both endpoints. A still unresolved denominator
causes subdivision rather than unsafe division or exclusion.

The normal formulas c=1/sqrt(1+(h/w)^2),
s=1/sqrt(1+(w/h)^2), w=x+a>0, are exactly equivalent to the
actual normalization. Enclosing their repeated uses independently
loses correlation only by enlarging the range. No independently
chosen direction or mean is inserted.

## 6. The quadratic bound proves both original return targets

For r=99/70 define

    G(u)=(A0+u*c+delta*s)(1+u*s-delta*c)
                                      -r(u*c+delta*s).

I independently expanded all coefficients and verified

    G(u)=G(0)+B0*u+c*s*u^2,
    B0=s*A0+(1-r)c+delta(s^2-c^2).

I also checked the alternative factored evaluation
G=A0*H+L(H-r) and the original concurrence numerator identity.
These are identities in the full symbolic variables; no numerical
pose or circle approximation is substituted into them.

Taking the greater of two outward lower endpoints for G(0) remains
a valid lower bound. If g0,b0,q0 are the lower bounds for
G(0),B0,c*s, then q0>0 and the actual lambda is nonnegative.
Therefore G(lambda)>=g0+b0*lambda+q0*lambda^2. The minimum of
this rational quadratic on the entire retained lambda interval is
at its clipped vertex. This checks a whole interval, including both
mean endpoints, rather than evaluating a candidate configuration.

The final G(lambda) lower bound is the greater of the two direct
bounds and this quadratic bound. The lesser of that bound and the
G(0) bound certifies both actual applications. The author initially
marks a target box only when this lesser bound is positive, then
checks that the minimum over all final boxes exceeds 1/1000000.
The latter exact uniform-floor assertion is present and passes.

## 7. Independent reproduction and complete 112-bit reconstruction

Running the entire frozen author checker reproduces exactly

| Terminal reason | Count |
| --- | ---: |
| Strict two-target certificate | 17,438 |
| Radius exclusion | 234 |
| Proper-concurrence exclusion | 226 |
| Actual leaf-screen exclusion | 1,024 |
| Actual x-interval exclusion | 359 |
| Upper physical-mean exclusion | 70 |
| Total terminal boxes | 19,351 |

There are 38,701 visited nodes, maximum depth 18 and no unresolved
terminal. The full canonical leaf payload has exactly the printed
SHA-256 c8abdb83f97e69fd9445b3733df9fd2fcd77eaf357a69eea23fe63d3800397ad.
I checked the complete smallest author margin by exact Fraction
comparison, not by a decimal approximation.

My separate implementation imports no author code or interval helper.
It uses a new immutable Fraction interval type and 112-bit radical
endpoints. For a rational n/d its floor is computed by the different
integer formula floor(sqrt(n*d*S^2)/d), S=2^112. At each call it
checks both defining squared floor inequalities before forming its
outward bounds. The author paths, reasons and margins are treated
as untrusted certificate data, not as successful test results.

I construct a new binary trie and reject every duplicate path,
prefix-leaf conflict, leaf with descendants or missing sibling.
Each box is reconstructed from the original rectangle using the
largest normalized width, first-coordinate tie rule and exact
rational midpoint. Both closed children are checked to cover their
parent, including the splitting plane. This independently recovers
all 38,701 nodes and all 19,351 leaves, at depth at most 18.

Every leaf is then evaluated anew with the separate intervals and
all original guards. The complete reason counts agree. All 17,438
target leaves give both lower bounds strictly above 1/1000000;
each new bound is at least its corresponding author bound. Every
remaining leaf is excluded by its actual printed necessary-domain
condition. No admissible continuous parameter point can be missing
from this closed-box cover.

The independent code also checks twelve positive exact rational
reserves, three coefficientwise polynomial identities and both
lambda rational equalities. In particular it rechecks the 1589/2500
and 53/5000 physical reserves, the 11/100 upper-corner reserve,
the 137/3700 gap below lambda=1/4, and sqrt(2)<99/70 with squared
reserve 1/4900.

| Independent artifact | SHA-256 |
| --- | --- |
| certificates/review_aligned_low_s_upper_c_visibility_hexagon.py | dd657ff02b1061590ff19533babe0e56c68d68d68452c00aef2b1c2ece7ae588 |
| checkpoints/hexagon_aligned_low_s_upper_c_visibility_independent_checks_2026_10_28.json | b5f4dd16e204785379fadc7f15ec9ff8d5ea6ef44427e10b06939d2bea920178 |

The reproduced complete author-output JSON has SHA-256
a960dd73c0ed3084e4dfe4cf34a3f749e2a2ca2fef962e247c46cc3ffc405691.
Both complete leaf records are retained in the recovery checkpoint.

## 8. Final physical contradiction and exact acceptance scope

For either original return point the exact certificate gives

    (A0+L)H>(99/70)L>=sqrt(2)*L,

because L>=0 and sqrt(2)<99/70. This contradicts the necessary
segment inequality in Section 4. The L=0 case was already closed
geometrically and is also compatible with the strict scalar target.

Thus no actual contained D can meet both the original upper C and
the original lower A in this entire placement. Both return owners,
all side means, zero proper-distance endpoints, both lower tilts,
all possible D frames and all physical masks are retained. C's and
A's unique masks are proved physically before being used. A remains
loaded degree three, D remains unloaded degree three, and their
extra original forces are never suppressed.

This accepts the entire stated aligned strict-low C-upper/A-lower
LTAC.S placement. It does not itself claim the complementary
placement, the tilted/high-aligned root cases, or a whole graph
parent. Those are separate reviewed inputs for the eventual family
join. No metadata, frozen source, remote state, Lean/CI or original
packing was changed by this review.

## 9. Exact direct prerequisite pins and scope readback

All nine printed source-table pins match the current exact bytes.
The following are the operative mathematical scopes checked in this
review; broader unused conclusions are not transferred.

| Input | SHA-256 | Scope checked |
| --- | --- | --- |
| FIVE_BODY_BLOCK_LEAF_GRAPH_LOAD_COVER.md | 7ba98ef149c1faff4ef4baeaf0b0305a38cf1153f883a3fe4bfa92087d33622d | Sections 1 and 4.3: original lower-house TAC graph and full degrees |
| RADIAL_BRIDGE_AND_LEAF_REDUCTION.md | 6154eee2ab1114d063b0dbd1a2800c3522cbb1b46ec44a258c1c89d8ffb9e975 | Actual S leaf, radial bridge, physical root clearance and shared means |
| NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md | 6e2279b627754fe6ba3c7d9a9779308ee8133223b09f5374803797cb41f3d96c | Complete same-nine R>2 theorem, with accepted current five-charge provenance |
| S_LEAF_C5_ALIGNED_LOW_RADIUS_EXCLUSION.md | 02fd37d94d14f8342365160064cff63d91b572e9e162944e9551590fc8f535a1 | Whole local Sections 1--6 and explicit arbitrary-neighbor-degree export; no all-boundary path imported |
| ALIGNED_LOW_S_ROOT_LOWER_BOUNDARY_UNIQUE_CORNER_AND_CENTER.md | c32b99ad24da76907f2e3eaa4d4e7c88b9b2d2599a0eefe50234fae493441c48 | Complete force-free Sections 1--3, with both b/t orders; later A2 assertions unused |
| ALIGNED_LOW_S_ROOT_UPPER_BOUNDARY_RETURN_EXCLUSION.md | 843e9afce21baa487804740b3aa7505cac254ef2904e525819960302505dace2 | Actual unique frame, full C2 return cover and far-support exit for every contained D |
| FIVE_CYCLE_FORCE_POLYGON_DOMAIN.md | 7d0c4092ba133a832cf963f329b1c3a6442a3260576f16319293835b39e6d282 | Lemma 1.1 at the already nonparallel actual unique C2, with no boundary-neighbor premise |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | eb26f19b27dc7327f80a64ccfd1febb542c5915aadcf95227e35765b20d3509a | Original physical singleton convention and compatible initial selection, no late normal replacement |
| certificates/aligned_low_s_upper_c_visibility_separation.py | d57e7506d4f6e1dd92c991c8579fcfcd03377703863b0d42d50f417267fe2c4c | Entire exact continuous two-target proof, all guard/mean endpoints and complete cover |

The properness scope was additionally checked directly in
C7_FORCE_POLYGON.md Section 4, pin
d50d8ca48ea19156175e651bfa74be30ef3e58065ec14d8d1834670a41559089,
and TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md Lemma 2.1, pin
0d61292a0aa57084b88b4a72754fc78e123e8b684dac09be966fb074ab58e877.
The contained-unit minimum-support cap follows from the complete
rigid-cap calculation in FOUR_CYCLE_ALIGNED_S_ARTICULATION_EXCLUSION.md
Section 1, pin f538032c069d34ef4e26e4ad03f85fd7f30f98b341e08b89a2579cdc7d9e9e56.
These local arguments do not impose their parent graphs on the
present original house.
