# A.2: a sharp arbitrary-tilt neighborhood terminal

**Status.** The theorem below is proved by a finite hand argument with a
seven-row rational sign table. The accompanying separate arithmetic checker
verifies two exact polynomial identities and all fourteen signed table entries.
It is a conditional local theorem, NOT a global extraction theorem or closure
of A.2. No fixed Q-minus-epsilon radius, pose mesh, or optimizer is a premise.

Put Q=1105/256, e=h=1/8 and b=1/64. These are positional and tilt tolerances;
they do not weaken the target radius.

## 1. The physical neighborhood and conclusion

Consider seven independently oriented, pairwise interior-disjoint unit squares
M0,M1,M2,M3,B0,B1,B2 in a disk centered at zero with squared radius q. After one
common rotation and a relabeling suppose their centers are

    M_i=(-3/2+i+dx_i, 1/16+z_i),           i=0,1,2,3,
    B_j=(-1+j+dx_(4+j), -15/16+z_(4+j)),   j=0,1,2,

where |dx_i|<=1/8 and |z_i|<=1/8 for every i. Represent the square frames as
u_i=(a_i,t_i), v_i=(-t_i,a_i), with a_i>=0, a_i^2+t_i^2=1 and |t_i|<=1/64.
Choose the common rotation so that (a0,t0)=(1,0). No other square is assumed
parallel. A quarter-turn of a frame is only a change of representation of
the same physical square; all actual movements here are common rotations.

Define

    V_M=|t1-t0|+|t2-t1|+|t3-t2|,
    V_B=|t5-t4|+|t6-t5|,
    V_C=|t0-t4|+|t3-t6|,     V=V_M+V_B+V_C.

For the four anchors A={0,3,4,6}, put d_i=(dx_i,z_i), w0=w3=23/64 and
w4=w6=9/64. The conclusion is the exact quantitative inequality

    q-Q >= (1/256)V + (1/2) sum_(i in A) w_i |d_i|^2.       (T)

Thus q>=Q, uniformly arbitrarily close to equality. Two additional physical
squares may have arbitrary poses; the proof neither changes nor uses them.
In particular this is not the old certificate assuming two parallel rows:
all seven orientations and all seven heights may initially vary independently.

The required global caller is explicit: a search leaf may use (T) only after
establishing EVERY bound in this section in ONE common frame. A root containing
an attaining pose is not thereby a certified sharp neighborhood.

## 2. Relative-frame support and the complete local axis cover

For two allowed unit frames let d=|t_i-t_j|. Since b<=1/4,

    a_i>=1-b,
    |a_i-a_j|=|t_i+t_j|d/(a_i+a_j)<=2bd.

Consequently

    |a_i t_j-t_i a_j| >= (1-b-2b^2)d >= (1-2b)d,
    a_i a_j+t_i t_j
      =1-((a_i-a_j)^2+(t_i-t_j)^2)/2
      >=1-b(1+4b^2)d >=1-2bd.

The second calculation uses d<=2b. The dot product is positive. The exact
two-square support halfwidth on an axis owned by either square is therefore

    (1+dot+|det|)/2 >= 1+c d,    c=(1-4b)/2=15/32.           (1)

For consecutive horizontal-chain squares, dx is in [1-2e,1+2e] and |dy|<=2h.
The magnitude of projection on a v-axis is at most

    b(1+2e)+2h=69/256<1,

so such an axis cannot separate them. Projection on a u-axis is positive,
with lower bound (1-b)(1-2e)-2bh=47/64. The separating-axis theorem, including
weak touching, consequently yields an owner o equal to either endpoint and

    dx >= 1+c|t_j-t_i|-t_o dy.                              (2)

Indeed a_o dx+t_o dy is at least the right side of (1), and a_o dx<=dx.

For B0--M0 and B2--M3, directed from B to M, |dx|<=1/2+2e and dy is in
[1-2h,1+2h]. A u-axis projection has magnitude at most 197/256<1. The v-axis
projection is positive with lower bound 93/128. Hence for either actual owner,

    dy >= 1+c|t_M-t_B|+t_o dx.                              (3)

These inequalities cover every owner and sign possibility. They concern the
actual pairs, whether touching or separated. No stress or contact graph is
assumed. Only these seven pair predicates are needed for (T).

## 3. Telescoping the two chains and both vertical owner choices

Set W_M=23/16, W_B=27/64 and W_C=207/512. If i owns a horizontal edge i--j,

    t_i(z_j-z_i)=t_j z_j-t_i z_i-z_j(t_j-t_i).

If j owns it, the last z_j is replaced by z_i. Summing (2), with |z_i|<=h,
gives the exact endpoint-product bounds

    W_M(x3-x0-3) >= W_M(c-h)V_M+W_M(t0 z0-t3 z3),
    W_B(x6-x4-2) >= W_B(c-h)V_B+W_B(t4 z4-t6 z6).           (4)

The endpoint products are retained, not estimated by a tiny anchor error.
Internal heights need not agree.

Let l be the tilt of the left vertical owner, either t0 or t4; let r be the
right owner tilt, either t3 or t6. Their directed x-displacements are
-1/2+dx0-dx4 and +1/2+dx3-dx6. Summing (3) gives

    (y0-y4-1)+(y3-y6-1)
       >= c V_C-l/2+r/2+l(dx0-dx4)+r(dx3-dx6).

Use l<=max(t0,t4) and r>=min(t3,t6) in the constant terms only. Expanding max
and min yields the lower bound

    (c-1/4)V_C-(t0+t4)/4+(t3+t6)/4
             +l(dx0-dx4)+r(dx3-dx6).                       (5)

The same actual l,r remain in their displacement terms. Thus all four owner
choices are retained consistently.

## 4. A weighted identity using four actual corners

Choose these frame signs and weights:

| Anchor | u sign s | v sign v | Weight | Base center |
|---|---:|---:|---:|---|
| M0 | -1 | +1 | 23/64 | (-3/2,1/16) |
| M3 | +1 | +1 | 23/64 | (3/2,1/16) |
| B0 | -1 | -1 | 9/64 | (-1,-15/16) |
| B2 | +1 | -1 | 9/64 | (1,-15/16) |

Put L_i=s_i x_i+v_i y_i and J_i=-v_i x_i+s_i y_i. The selected actual corner
has squared norm |c_i|^2+1/2+a_i L_i+t_i J_i. All four corners are contained,
and the weights sum to one. Expanding about the listed base centers gives

    q-Q >= W_M(x3-x0-3)+W_B(x6-x4-2)
          +W_C[(y0-y4-1)+(y3-y6-1)]
          +sum_A w_i |d_i|^2
          +sum_A w_i[(a_i-1)L_i+t_i J_i].                   (6)

This is an exact polynomial identity followed by the four containment bounds.
The base weighted coefficients of t0,t3,t4,t6 are respectively
529/1024,-529/1024,-9/1024,9/1024. The base L values are 25/16 for M and 31/16
for B. The checker expands the physical corners independently and retains
explicit unit-frame remainders (a_i^2+t_i^2-1)/2; its residual is zero.

## 5. Absorb the displacement products by positive squares

Write w=23/64, v=9/64 and k=207/512. Combining (4)--(6), using a0=1,t0=0,
groups the linear anchor-displacement terms into L'_i.d_i with

| Anchor | x coefficient of L'_i | y coefficient |
|---|---|---|
| M0 | k l | 0 |
| M3 | w(a3-1-t3)+k r | w(a3-1-3t3) |
| B0 | v(1-a4+t4)-k l | v(1-a4+2t4) |
| B2 | v(a6-1+t6)-k r | v(1-a6-2t6) |

This grouping is a second exact polynomial identity, separately expanded by
the checker. Since 1-a_i=t_i^2/(1+a_i)<=b|t_i|, put P=w(1+b)+k and H=v(1+b)+k.
Using |l|<=|t4|, |r|<=|t3|+|t6| and (A+B)^2<=2A^2+2B^2 gives

    |L'_0|^2 <= k^2 t4^2,
    |L'_3|^2 <= [2P^2+w^2(3+b)^2]t3^2+2k^2 t6^2,
    |L'_4|^2 <= [H^2+v^2(2+b)^2]t4^2,
    |L'_6|^2 <= [2H^2+v^2(2+b)^2]t6^2+2k^2 t3^2.

For each positive weight,

    w_i |d_i|^2+L'_i.d_i
      >= (w_i/2)|d_i|^2-|L'_i|^2/(2w_i),                   (7)

by completing a square. Also (a_i-1)L_i(base)>=-L_i(base)t_i^2. All the
negative terms are thus bounded by C3 t3^2+C4 t4^2+C6 t6^2, with

| Coefficient | Formula | Exact value |
|---|---|---:|
| C3 | [2P^2+w^2(3+b)^2]/(2w)+k^2/v+25w/16 | 2623909/524288 |
| C4 | k^2/(2w)+[H^2+v^2(2+b)^2]/(2v)+31v/16 | 484929/262144 |
| C6 | k^2/w+[2H^2+v^2(2+b)^2]/(2v)+31v/16 | 1647099/524288 |

The anchor-0 tilt terms vanish identically. This estimate preserves half of
every anchor displacement square in (7).

## 6. Fourteen signed layers, displayed in seven rows

The base tilt terms combined with (5) are

    -A t3+B(t6-t4),   A=851/2048, B=225/2048.

Set lambda=1/256. Subtract lambda V from the lower bound obtained above.
Because W_M(c-h)>lambda and W_B(c-h)>lambda, we may minimize the two chain
variations by V_M>=|t3| and V_B>=|t6-t4|. Use t_i^2<=b|t_i| on the remaining
quadratic costs. Writing X=t3,Y=t4,Z=t6 reduces the desired inequality to
F(X,Y,Z)>=0 for

    F=(W_M(c-h)-lambda)|X|-A X
       +(W_B(c-h)-lambda)|Z-Y|+B(Z-Y)
       +(W_C(c-1/4)-lambda)(|Y|+|X-Z|)
       -b(C3|X|+C4|Y|+C6|Z|).                              (8)

This is a homogeneous piecewise-linear expression. It is enough to check
F(1_S)>=0 and F(-1_S)>=0 for the seven nonempty subsets S of {X,Y,Z}.
Here is a complete elementary justification, so the table is not a sample:
write each positive coordinate as the sum of lengths of its positive level
layers, and each negative coordinate as minus the lengths of its negative
layers. For two coordinates x,y, |x-y| is exactly the sum of the lengths of
layers on which their indicators differ. This remains true when x and y have
opposite signs. The same decomposition applies to |x| and every linear term.
Consequently F is a nonnegative linear combination of those fourteen layer
values. Zero coordinates and repeated levels cause zero-length layers, not
missing cases. The layer vectors are algebraic test directions; they are not
claimed to be physical tilts of magnitude one.

Every entry below is **2^25 times F** at the indicated layer. They are all
strictly positive integers.

| Nonzero coordinates S | F(1_S) times 2^25 | F(-1_S) times 2^25 |
|---|---:|---:|
| X | 2,719,323 | 30,604,891 |
| Y | 2,915,198 | 10,287,998 |
| X,Y | 5,634,521 | 40,892,889 |
| Z | 9,610,757 | 2,237,957 |
| X,Z | 6,657,120 | 27,169,888 |
| Y,Z | 3,056,003 | 3,056,003 |
| X,Y,Z | 102,366 | 27,987,934 |

The smallest layer reserve is 51183/16777216>0. Formula (8) is therefore
nonnegative for every real triple. Retaining the anchor squares from (7)
proves (T). This argument is uniform in q, including its sharp boundary.

## 7. Exact equality within this neighborhood

At q=Q, (T) gives V=0 and d_i=0 for all four anchors. The variation graph is
connected and t0=0, so all t_i=0 and all a_i=1. The horizontal gaps are at least
one, while their outer spans are exactly three and two. Hence all gaps are
one and every x-coordinate equals its listed base value.

Write the internal M heights as 1/16+s1,1/16+s2 and the internal B height as
-15/16+t. Full nonoverlap is equivalent, within the neighborhood, to

    0<=s1<=1/8,   0<=s2<=1/8,   -1/8<=t<=min(s1,s2).        (9)

Each internal M square overlaps an outer B square horizontally and therefore
must be at least height 1/16. The middle B square overlaps both internal M
squares and must satisfy the upper bound on t. Opposite vertical orderings
are impossible in these height bands. Every other pair is horizontally
separated or is one of the already fixed vertical anchor pairs.

Conversely (9) gives a physical seven-square packing. Its selected anchor
corners attain Q; the three internal squares have maximum corner squared
norms at most 377/256 and 689/256, both below Q. Thus this is a full necessary-
and-sufficient equality description for the seven squares in this chart.
The eighth and ninth squares, when present, must satisfy their original
containment and nonoverlap constraints. No global equality classification
is inferred from this local result.

## 8. Verification and the remaining global caller

Run `python make_sharp_neighborhood_certificate.py` and
`python verify_sharp_neighborhood_certificate.py --negative-controls`.
The second program imports no generator. It reconstructs both physical
polynomial identities, all fourteen rational layer values and the elementary
axis bounds. It also checks exact equality and genuinely tilted physical
examples and rejects deliberately corrupted constants/table coverage.
The finite controls are regression tests; Sections 1--7 are the hand proof.
No separate human reviewer, Lean, Lake or CI verification is claimed.

This provides a sharp terminal that can retain equality while excluding all
q<Q assignments in its neighborhood. The missing step for A.2 is still a
complete caller: every remaining domain must be excluded or proved to enter
such a terminal. No original case count is reduced solely because this theorem
has been written, and no new roadmap gate is introduced.
