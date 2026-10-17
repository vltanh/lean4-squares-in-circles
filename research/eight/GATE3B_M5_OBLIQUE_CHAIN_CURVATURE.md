# Gate 3B.2 / M5: a seven-square oblique-chain curvature obstruction

2026-10-13. This is a whole-continuum geometric exclusion, not a sampled
minimum or an isolated fixed-angle dual certificate. It discharges a
specified separator subfamily of M5-I and applies whenever that subfamily
occurs in any eight-square packing. It does NOT exclude all M5-I or M5-II.

## 1. The reference seven-square family

Put s=1/sqrt(2), u=(s,s), v=(-s,s), and w=(1+sqrt(2))/2.
Consider seven unit squares A,B,H,L,D,R,E in a disk centered at zero.
A and B have the standard frame; H,L,D,R,E have the frame (u,v).
No symmetry of centers, exact contacts, or prescribed circle contacts is
assumed. Let p_X=(x_X,y_X) denote their actual centers.

Assume these seven DIRECTED WHOLE-SQUARE separator inequalities:

| Pair, directed from first to second | Normal | Required center projection |
|---|---|---:|
| A -> B | (1,0) | >=1 |
| H -> A | u | >=w |
| E -> B | v | >=w |
| H -> L | -v | >=1 |
| L -> D | -v | >=1 |
| E -> R | -u | >=1 |
| R -> D | -u | >=1 |

Thus two two-edge oblique paths run from H and E to D; H and E are also
separated from the horizontally ordered pair A,B. Other square pairs may
have any valid separators. Only the seven displayed inequalities enter
the proof.

### Theorem 1 — reference curvature obstruction

Every such configuration has

    R^2 > 99/25 = 3.96.                                  (1)

The proof uses five actual outward vertices, the two top-square vertices,
and the path projection sums. In particular it keeps circle curvature
that the four-strip relaxation discards.

## 2. A center-independent scalar inequality, without a symmetry assumption

Write q=R^2. It suffices to consider q<=99/25. Define

    ybar=(y_A+y_B)/2,
    a_L=-x_H-y_H,       b_L=-x_H+y_H,
    a_R= x_E-y_E,       b_R= x_E+y_E,
    abar=(a_L+a_R)/2,   bbar=(b_L+b_R)/2.

The actual vertices

    (x_A-1/2,y_A+1/2),   (x_B+1/2,y_B+1/2)

are in the disk. Their x-coordinate difference is at least two because
x_B-x_A>=1. Averaging their squared norms and discarding nonnegative terms
gives

    q >= 1+(ybar+1/2)^2,
    ybar <= sqrt(q-1)-1/2.                              (2)

This also proves q>=1, so the radical is defined. No assumption that
x_A=-1/2, x_B=1/2, or y_A=y_B was made.

The H->A and E->B inequalities, divided by s, give

    a_L >= 1+s-x_A-y_A,
    a_R >= 1+s+x_B-y_B.

Combining with x_B-x_A>=1 and (2),

    abar+s >= 2+sqrt(2)-sqrt(q-1).                       (3)

Adding the two edges on each oblique path gives

    b_L >= 2sqrt(2)-x_D+y_D,
    b_R >= 2sqrt(2)+x_D+y_D.

The true bottom vertex of D is (x_D,y_D-s), so y_D>=s-R. Therefore

    bbar+s >= 3sqrt(2)-sqrt(q).                          (4)

The actual leftmost vertex of H and rightmost vertex of E have squared
norms respectively

    ((a_L+s)^2+(b_L+s)^2)/2,
    ((a_R+s)^2+(b_R+s)^2)/2.

Average their disk inequalities and apply the elementary inequality
(X^2+Y^2)/2>=((X+Y)/2)^2 separately to the a and b terms. This yields

    q >= ((abar+s)^2+(bbar+s)^2)/2.

Both lower bounds in (3)--(4) are positive for q<=99/25. Hence

    2q >= (2+sqrt(2)-sqrt(q-1))^2
           +(3sqrt(2)-sqrt(q))^2.                       (5)

This necessary inequality holds for ALL centers of the stated family.
It is not an evaluation at the numerically observed symmetric packing.

## 3. Short exact rational contradiction

For q<=99/25,

    sqrt(q)<199/100,
    sqrt(q-1)<1721/1000,
    sqrt(2)>1414/1000.

These follow by squaring the positive rational endpoints. Thus (5) gives

    q > ((1693/1000)^2+(2252/1000)^2)/2
      = 7937753/2000000
      = 99/25 + 17753/2000000,

contradicting q<=99/25. This proves Theorem 1. The scalar inequality could
be sharpened, but that is unnecessary for the current research ceiling.

## 4. Independent frame rotations: a full positive-width theorem

Set

    epsilon=1/200,
    a=(1-epsilon-epsilon^2/2)(1-2epsilon^2)
      =1591900401/1600000000.                           (6)

Now allow ALL SEVEN true square frames to rotate independently. After
one common rotation, require only that A,B be within epsilon radians of
the standard frame modulo quarter-turns, and H,L,D,R,E be within epsilon
of the 45-degree reference frame modulo quarter-turns.

For each pair in the table require that it admit a CANONICAL true signed
SAT normal within epsilon of the displayed directed reference normal.
Canonical means that it maximizes n dot (p_second-p_first) among the
pair's eight actual signed side normals. All maximizing ties are allowed.
This is a condition on an actual owner branch, not an assertion that the
branch is forced in every M5 packing.

### Theorem 2 — independently rotated chain exclusion

Every actual seven-square packing satisfying these frame and owner
conditions has

    R^2 > (99/25)a^2
        =250880541783692119299/64000000000000000000
        >9789/2500.                                    (7)

In particular NO eight-square packing under the research ceiling can
contain this seven-square separator subfamily. The eighth square is
unrestricted and need not be central.

### Proof: inscribe reference squares and use canonical projections

For a canonical normal n, put d=p_second-p_first,
A=n dot d and B=(Jn) dot d. The perpendicular signed axes are also true
owners, so maximality gives |B|<=A. Nonoverlap gives A>=w_actual>0.
For the reference normal n0 at angular distance at most epsilon,

    n0 dot d >= (cos(epsilon)-sin(epsilon)) A.           (8)

The reference support sum is either one or w. For a same-reference-frame
pair, w_actual>=1. For a mixed pair its relative angle is within 2epsilon
of pi/4, so

    w_actual >= (1+sqrt(2)cos(2epsilon))/2
              >= cos(2epsilon) w.

In BOTH cases w_actual>=cos(2epsilon)w_reference. By (8), the true center
projection in n0 is at least

    rho w_reference,
    rho=(cos(epsilon)-sin(epsilon))cos(2epsilon) >= a.   (9)

The last inequality uses sin(t)<=t and cos(t)>=1-t^2/2, with positive
factors throughout the stated range.

At each actual center place a reference-oriented square of side length a.
It is contained in the corresponding true unit square. Indeed its largest
coordinate half-width in the true frame is at most

    a(cos(epsilon)+sin(epsilon))/2 <= 1/2,

because a<=rho and

    rho(cos(epsilon)+sin(epsilon))=cos(2epsilon)^2<=1.

Thus all these smaller reference squares remain in the ORIGINAL disk,
and (9) supplies all seven reference separator inequalities at side a.
Scale the entire configuration by 1/a. Theorem 1 applies to the resulting
reference unit squares in radius R/a, proving R^2>(99/25)a^2.

The exact margin over the research ceiling is

    (99/25)a^2-9789/2500
       =282141783692119299/64000000000000000000 >0.

No bound on the centers' displacement from a reference pose is required.
No exact contact, symmetry, or parallelism is required in Theorem 2. QED.

## 5. How this closes a real M5 subfamily

The exact M5-I examples in `GATE3B_M5_FOUR_STRIP_NO_GO.md` both satisfy
Theorem 2's seven frame/owner conditions, with zero-based labels

    A=1, B=7, H=4, L=2, D=5, R=3, E=6.

Their canonical normals and angle bounds are checked by exact dot/cross
inequalities in `verify_m5_four_strip_counterexample.py`; no floating
angle test is used. One example passes even the full-square four-strip
constraints at radius 191/100, far below the candidate, but Theorem 2
rejects its ENTIRE specified center/owner family for the actual disk
ceiling. It is not merely a test of that one coordinate witness.

This illustrates the necessary distinction: the simultaneous projection
orders remain valid necessary constraints, but circle-curvature arguments
can exclude families that every consequence of those four strips admits.

## Gate status

Proved: a full continuous separator subfamily is impossible in the n=8
radius window, including independent frame variations up to 1/200.

OPEN: prove that every M5-I or M5-II packing either has this subfamily or
belongs to explicitly listed other children; then discharge those other
children. The two folded orientation types do NOT force this chain, its
near-reference angles, or its canonical owner choices.

Therefore Gate 3B.2 / M5 remains active. M6, M7, M8 and the unrestricted
sharp lower bound have not been closed or bypassed.
