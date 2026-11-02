# Weak middle edge: an upper central unit above P has whole floor above one tenth

## Status and physical statement

This manuscript gives the complete geometric reduction and an independently
replayed exact finite table. It proves the stated whole-floor consequence;
it does not by itself change any mask count. Floating discovery first found
a negative necessary-system optimum near `-0.005305947`; that observation
is not a premise of the proof.

Retain the original nine physical unit squares in the closed disk with
squared radius `Q=1105/256`, with independent frames and disjoint open
interiors. Their marked comparisons are those of `010/01`: the outer main
links `A--B`, `C--D`, and the selected link `L--P` are actual horizontal
projection separations; the other marked links are their original weak
horizontal-cone comparisons. Use the upward routing from
`WEAK_MIDDLE_ROUTING_AND_HIGH_FLOOR.md`.

Assume `y_P-h_P<=1/10`. The claim of this reduction is:

> Every original additional unit U with `|x_U|<=29/60` and `y_U>=y_P`
> has `y_U-h_U>1/10`.

The separate complete central-order table shows that any original central
extra above both inner mains is above P. The present reduction does not
assume U is part of a new cone chain or that any particular owner separates
P and U. The two original physical frames and all their owner possibilities
are retained.

## 1. Facts from the original caller

Write `h_S` for coordinate halfwidth and `g_S=1/(4h_S)` for the halfwidth
of the aligned inset inside physical unit S. Set

    rho=91/60,   p=h_P, u=h_U, x=x_P, v=x_U, C0=451/810.

The outer-link and uniform-routing theorems, together with the original
endpoint/shoulder caps, give

    -23/405<=x<=23/60,            -29/60<=v<=29/60,
    1/2<=h_B,h_C<=13/20,         V=eta_B+eta_C<=1/30,
    eta_M=h_M+1/(4h_M)-1<=V,
    x-p+C0-(92/27)*eta_M>=0,
    y_P>max(y_B,y_C),
    -13/12<=x_L<=-23/30,         y_L>=25/32.

The displayed inequality for x follows from the original actual `L--P`
link and the two endpoint/shoulder caps, retaining the common endpoint span
at least `2+V`. It is valid for either choice M in `{B,C}`. See Section 1 of
`WEAK_MIDDLE_LOW_FLOOR_MAINHEIGHT_THREE_TENTHS.md` for its algebra. The
main-height conclusion of that manuscript is not needed here.

Choose the original M on P's own horizontal half-plane: M=C for x>=0 and
M=B for x<=0. At zero either choice works. Write

    h=h_M, g=1/(4h), eta=h+g-1, kM=sqrt(1/2-h^2).

The reflected inner center interval is

    g-1/60 <= |x_M| <= 61/60-h.

Thus the true horizontal M/P gap is at most

    d=max(|x|-g+1/60, 61/60-h-|x|) <=31/60.        (1)

At physical points d is nonnegative; the original center interval is
nonempty. Its inset margin is also bounded below:

    g-d >=-1/60.                                  (2)

For the first alternative in (1), use `g>=5/13` and `|x|<=23/60`;
for the second, use `g+h>=1`. These facts cover both signs of x.

The outer cone comparison and the original endpoint reserve imply

    y_M>m(h):=g-199/120+(32/9)*eta.                (3)

Indeed the matched endpoint has `y_E>=-1/8+(32/9)*eta`, its absolute
horizontal center is at most rho, and the main's absolute center is at
least `g-1/60`. The original cone gives (3), including after horizontal
reflection. In particular no new coordinate separator is imposed on M/P.

## 2. Physical support and vertical clearance

For an arbitrary original unit use its folded orientation t in [0,1]:

    a=1/sqrt(1+t^2), b=t*a, h=(a+b)/2, k=(a-b)/2.

The signs of its frame remain free. For two original units i,j the smaller
side-axis support over their independent chiralities equals

    s(i,j)=1/2+max(k_i*a_j+h_i*b_j,
                  h_i*a_j-k_i*b_j).

Equivalently it is
`(1+a_i*a_j+b_i*b_j+|a_i*b_j-b_i*a_j|)/2`.
The opposite-sign relative angle has at least this support: for folded
angles alpha>=beta the difference in `cos+sin` is
`2*sin(beta)*(cos(alpha)-sin(alpha))>=0`. The supplementary support bound

    s(i,j)>=1+|h_i-h_j|

follows because the halfwidth increment over a fixed angular difference
is largest when the smaller angle is zero. The exact evaluators use the
maximum of these valid lower bounds.

Put s=s(M,P). P is above M. All four genuine owner axes and the true
center distance therefore yield a vertical clearance at least

    C_axis=min((s-aM*d)/bM, (s-bM*d)/aM,
               (s-aP*d)/bP, (s-bP*d)/aP),
    C_disk=sqrt(s^2-d^2).                          (4)

Terms with zero denominator are omitted. A nonpositive vertical component
cannot separate these originals because its projection is at most
`d<1<=s`. Each numerator in (4) is at least `29/60>0`, so this omission
also handles every aligned boundary.

The physical P must additionally avoid M's aligned inset. Its coordinate
or P-owned side separator gives

    C_inset=g+min(p,(1/2+(g-d)*bP)/aP,
                   (1/2+(g-d)*aP)/bP).            (5)

The last term is omitted at bP=0. The horizontal axis and nonpositive
vertical directions are impossible by (2). Every numerator is at least
`29/60`, so the full sign and zero-component cases are covered. The
upward vertical axis supplies p; the two P-owned axes supply the other
two terms.

Consequently the original P height satisfies

    y_P>=Ymin:=m(h)+max(C_axis,C_disk,C_inset).      (6)

The exact scalar lower bound on m is particularly simple:

    m(h)=(32/9)*h+41/(36*h)-32/9-199/120.

It decreases up to `h^2=41/128` and increases afterward. On an interval
containing that critical point its minimum is
`4*sqrt(82)/9-32/9-199/120`. Otherwise the proper interval endpoint is
the minimum. This is an analytic convex minimum, not a numerical estimate.

## 3. A corner-free height bound for a leftward U

Suppose contrary to the claim that `y_U-h_U<=1/10`. Always

    y_U<=u+1/10.                                  (7)

If `v<=-1/10`, the original L gives a useful second cap. Write
`A=-x_L`. Since `L--P` is actual,

    A0:=max(23/30,p+1/2-x) <= A <= A1:=13/12.      (8)

U must be below L. Otherwise their vertical gap is at most

    17/24+1/10-25/32=13/480,

where `u<=1/sqrt(2)<17/24`, while their horizontal gap is at most
`13/12-1/10=59/60`. Their squared center distance would then be less
than one, with exact reserve

    1-(59/60)^2-(13/480)^2=7447/230400>0.

This contradicts their disjoint open radius-one-half center disks.
Thus their genuine vertical gap is at least
`sqrt(1-(A+v)^2)`. The original center norm bound gives

    y_U<=F_v(A):=sqrt(rho^2-A^2)-sqrt(1-(A+v)^2).   (9)

On the full rectangle in question,
`17/60<=A+v<=59/60`, so all roots are real with positive denominators.
Moreover F_v increases with v. Its derivative with respect to A has the
sign of `rho*(A+v)-A`, hence has only one possible zero, a minimum.
Therefore

    y_U<=max(F_v(A0),F_v(A1))                     (10)

whenever (8) is possible. No frame or contact assumption on L or U was
used to obtain this bound.

For interval evaluation, use the lower endpoint of an interval for A0
and the upper endpoint for v in (10). The allowed A interval only
increases and both endpoint evaluations remain rigorous. If A0>A1,
the necessary condition (8) itself is false.

Define C as the minimum of (7) and (10) when v<=-1/10, and as (7)
otherwise. On an interval straddling v=-1/10, using (7) alone remains a
valid upper bound throughout; this boundary loses no physical points.

## 4. Seven necessary expressions on one complete root

Use the five original scalar variables

    tP,tU in [0,1],
    x in [-23/405,23/60], v in [-29/60,29/60],
    h in [1/2,13/20].                             (11)

Put `D=|x-v|`, `Z=max(0,C-Ymin)`, and `sPU=s(P,U)`. Since the assumed
ordering is `y_U>=y_P`, any physical counterexample must satisfy every
row below. The last row explicitly covers all four owner axes; taking
absolute components increases each actual directed projection.

| Code | Necessary expression, required to be nonnegative |
|---:|---|
| 0 | `x-p+C0-(92/27)*eta` |
| 1 | `1/30-eta` |
| 2 | `A1-A0` |
| 3 | `p+1/10-Ymin` |
| 4 | `C-Ymin` |
| 5 | `D^2+Z^2-sPU^2` |
| 6 | `max(aP*D+bP*Z,bP*D+aP*Z,aU*D+bU*Z,bU*D+aU*Z)-sPU` |

Rows 3--4 retain the two whole-floor assumptions and their order. The
harmless maximum with zero in Z enlarges the bound outside the already
necessary region in row 4. The independent originals M,P,U and their
retained endpoint information therefore give a point of (11) obeying
all seven rows if a counterexample exists.

## 5. Exact finite coverage and independent replay

`certify_upper_central_floor.py` chooses exact midpoint splits and a
violated row on each eventual leaf, using a directed dyadic evaluator.
The output is `upper_central_floor_candidate.json`. A split tag 0--4
bisects the corresponding coordinate of (11); a leaf tag 5--11 selects
the row with code equal to the tag minus five. Preorder traversal always
places the lower half before the upper half. A finite complete prefix
tree thus specifies every rational box without storing approximate
coordinates or trusting producer-computed margins.

`verify_upper_central_floor.py` independently reconstructs the fixed
root, every split, all physical expressions, and every strict leaf
reserve. It imports no producer or optimizer. It uses Fraction arithmetic
and independently enclosed 90-bit radicals. It also evaluates the direct
relative-frame expression in addition to the collected support formula.
An accepted replay requires no pending branch, no trailing node, exactly
`2*leaves-1` nodes, and a strictly positive exact reserve at every leaf.

The complete independent Fraction replay passed all 142,251 nodes and
71,126 strict leaves, maximum depth 38. The exact least positive reserve,
stored without rounding in `upper_central_floor_candidate_exact_replay.json`,
is greater than `1/10000000`. The leaf counts are:

| Necessary row | Strict leaves |
|---:|---:|
| 0 | 5,841 |
| 5 | 34,742 |
| 6 | 30,543 |
| **Total** | **71,126** |

The certificate SHA-256 is

    942bb4be822f244eb2e7a1df96865997ac32eb1bcbddcde8c369f464fea4d619

The independent checker SHA-256 is

    de816128ad06d5edaccc56d33cdea684ff786a0683a45997b80be91616433d4a

`check_upper_central_floor_controls.py` also verifies that the checker
rejects missing subtrees, an invalid node tag, a false whole-root leaf,
and a noninteger tag. All four controls passed; the record is
`upper_central_floor_negative_controls.json`.

An independent agent reviewed the full physical reduction and the separate
Fraction checker. In particular that review checked both same-half choices
of M, the convex main-height minimum, all four owner axes and independent
chiralities, the left-shoulder order reserve, both monotonicity statements
for F_v, the enlargement of the allowed A interval, and the boundary
v=-1/10. No gap was found. This is agent review and independent exact
arithmetic, not human or proof-kernel verification.

Every hypothetical original U with the contrary whole-floor condition
would satisfy all seven necessary expressions at a point of the complete
root. The strict leaf cover excludes every such point. Therefore
`y_U-h_U>1/10`, as claimed. No Lean, Lake, or CI was run.
