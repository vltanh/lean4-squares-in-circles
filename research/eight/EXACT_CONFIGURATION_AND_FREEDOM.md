# Exact candidate coordinates, angles, and a three-parameter family

This is an exact construction theorem at the isolated candidate radius R*. It is NOT an unrestricted optimality theorem. The missing global lower bound is not supplied by knowing these coordinates.

Baseline for the earlier isolation and five-corner work: da725913eb121855d00271f40425a81634cc063e.

## 1. A polynomial specification with small integer coefficients

Use seven real variables q,y,z,r,u,v,w, with r,u,v,w positive. Put D=1+z^2 and

    H1=(1-z^2)(r-1)+2zy-2D,
    H2=(1-z^2)(v-2)+2z(w-1)-D.

Require the four circle equations

    r^2+y^2=q,
    u^2+(y+2)^2=q,
    (u-3)^2+v^2=q,
    w^2+(v-2)^2=q,

and the following three polynomial equations:

    H1^2+H2^2-qD^2=0,

    H1(2zr-(1-z^2)y)uvw
      +H2 r(u-3)(y+2)((1-z^2)w-2z(v-2))=0,

    H1(-2z(r-1)+(1-z^2)y)
      +H2((1-z^2)(w-1)-2z(v-2))=0.

The unique solution is selected by the existing rational isolating box for (q,y,z): centers

    3.91553413751747532652,
   -0.92065667800760613175,
    0.06189741100766035970,

with radius 10^(-16) in each coordinate. Positivity selects the other four roots uniquely. The previous contraction proof establishes existence and uniqueness in this box; this is not an assertion based only on rounded decimals.

To check equivalence with the previous specification, write F=H1^2/D^2+H2^2/D^2-q. If the last two polynomial left sides are denoted Y and T, differentiation along the four positive circle roots gives

    F_y=2Y/(D^2 ruvw),       F_z=4T/D^3.

All cleared denominators are positive. Thus these are exactly F=F_y=F_z=0, not extra conjectured contact equations. Both differential identities were checked symbolically. This system specifies algebraic coordinates without displaying a potentially huge eliminated minimal polynomial.

## 2. Exact coordinates and orientations

Let

    c=(1-z^2)/D,   s=2z/D,
    e=(c,s),      f=(-s,c),
    P5=(H1/D)e+(H2/D)f,
    H=P5+(e+f)/2.

A representative packing, in the order A,B,C,T,D_left,E_left,G,H, is:

| Square | Center | Edge angle |
| --- | --- | --- |
| A | (r-1/2,y+1/2) | 0 |
| B | (u-1/2,y+3/2) | 0 |
| C | (u-3/2,h_C) | 0 |
| T | (u-3/2,h_T) | 0 |
| D_left | (u-5/2,v-1/2) | 0 |
| E_left | (1/2-w,v-3/2) | 0 |
| G | H+e+eta f | 2 arctan(z) |
| H | P5+(e+f)/2 | 2 arctan(z) |

The scalar D=1+z^2 is not the square D_left. Centers and the cosine/sine of every edge angle are algebraic. The angle itself is specified exactly as 2 arctan(z); no claim that the angle is an algebraic real number is needed.

For h_C=7/20, h_T=27/20, eta=0, approximate centers are:

    A = ( 1.2515494337178937784, -0.4206566780076061317)
    B = ( 1.1584788605188487290,  0.5793433219923938683)
    C = ( 0.1584788605188487290,  0.3500000000000000000)
    T = ( 0.1584788605188487290,  1.3500000000000000000)
    D = (-0.8415211394811512710,  0.9545979409591740527)
    E = (-1.4021226909722471249, -0.0454020590408259473)
    G = ( 0.2459535366908851004, -0.9065755718052959758)
    H = (-0.7464131298405002117, -1.0298979102415513222).

The common tilted angle is approximately

    0.123637086521587971034510545084 radians
    =7.08388324898078641639357315549 degrees.

The radius is sqrt(q), approximately 1.97877086533976321492995738414223876309. Only the polynomial system and isolating box, not this table of decimals, define the exact construction.

## 3. Three independent sliding parameters: a complete box of packings

Every choice in the product box

    1/3 <= h_C <= 7/20,
    27/20 <= h_T <= 34/25,
    -1/10 <= eta <= 1/10

is a packing at the SAME exact radius R*. In particular h_T-h_C>=1. This establishes a three-dimensional set of representatives, not merely a suggestion based on visible gaps.

The five circle-contact vertices are unchanged. Nine separating identities remain exact: A/B, B/C, B/T, C/D, T/D, D/E, E/H, H/G, and G/A. For H/G and G/A the transverse displacement eta*f disappears on taking the e projection. The tenth listed pair C/T has vertical separating margin h_T-h_C-1>=0.

The remaining 27 vertices and 18 unordered pairs are checked simultaneously on the entire three-parameter box and entire stationary root enclosure by verify_candidate_family.py. Its interval operations use integer-directed rounding, not floating-point acceptance. The executed verification proves every other squared containment margin exceeds 1/1000 and every other pair has a separating projection margin exceeding 1/100.

Both local coordinates of C have magnitude below 5/12 uniformly, so the closed disk of radius 1/12 remains inside its open square. Thus this is also a family compatible with the central-core theorem.

Convexity reduces each square's containment to its four vertices. Each separating projection puts the two open squares in disjoint open half-planes (touching boundary is allowed). The symbolic contacts and verified strict inequalities cover all 32 vertices and all 28 unordered pairs.

## 4. What this does and does not settle about freedom

There are at least three independent sliders in the candidate family: the central height, the upper height, and the inner tilted square's transverse position. Therefore a claimed isolated eight-square equality configuration would be false if R* is globally optimal.

This product box is only a convenient verified subset of the allowed parameter region. It is not a maximal classification. The fixed angles in the displayed family do not prove that all candidate-radius packings have those angles, nor that a rotated slack square is impossible. Rotation freedom and global classification require separate arguments.

No Lean formalization is being attempted.
