# Uniform capacity closure of both strict side-source rows in LSLSLD

**Subsequent whole-case completion:** [the radial-D three-body capacity theorem](RADIAL_DIAGONAL_THREE_BODY_CAPACITY.md) now completes the remaining radial-D class. The entire LSLSLD signature is closed; the branch-specific statements below record their original scope.

**Status:** complete necessary-parameter classification and completion bound
for E_A and E_B with both D endpoints uniquely circle-loaded. The finite
rational tables below were checked by two arithmetic implementations in
this single-agent session. There has been no independent agent review or
Lean verification. This is a branch closure, not a closure of LSLSLD.

## 1. Statement and dependencies

Use the coordinates and five source circle-feature rows of
[the strict source reduction](STRICT_SIDE_SOURCE_RATIONAL_REDUCTION.md),
after [the vertical-endpoint exclusion](RADIAL_VERTICAL_SOURCE_EXCLUSION.md).
Assume an E_A source, or its E_B reflection, and keep the full intervals
of both S-transmitter slides.

**Theorem.** Such a component in a disk with squared radius at most 9/2
has total packing capacity at most nine. Thus it cannot occur in the
hypothetical strictly subcritical ten-square packing.

Only the four centers A,B,C,D are used for the completion bound. In
particular neither transmitter slide is normalized or removed.

The remaining source-feature table in the both-unique-D-endpoint branch is:

| Source feature | Status after this argument |
| --- | --- |
| E_A, unique upper-left circle vertex | Excluded uniformly |
| E_B, unique upper-right circle vertex | Excluded by reflection |
| V_V, unique upper-left circle vertex | Open |
| V_V, unique upper-right circle vertex | Open; reflection of preceding row |
| V_V, both upper circle vertices | Open; retain every load split |

The separate radial-D-endpoint branch is also open. The fixed master
ledger remains **276/336 hand closed; 60 open**.

## 2. All admissible E_A parameters lie in one small rectangle

Put b=sqrt(2)-1 and retain x=p/(1+q), y=r/(1+s). Actual strict
directions satisfy 0<x,y<b. Define E,G and the four centers by the
formulas of the source reduction. Also retain the actual common-edge
length condition

```text
0 < ell=(sqrt(2)-p-r)/q <= 1.
```

All required divisions have the signs proved in that reduction. The
containing rational square [0,27/64]^2 includes the closed parameter
square [0,b]^2.

Let S=2^44=17592186044416. Define the closed rectangle T exactly by

```text
x in [4639059459912/S, 4642577897122/S],
y in [4244994492517/S, 4250272148331/S].
```

These are outward dyadic brackets of the familiar decimal bounds;
the dyadic endpoints above, rather than a decimal approximation, are used.

The complete table in
[strict_side_source_closure_certificate.json](strict_side_source_closure_certificate.json)
partitions [0,27/64]^2 by longest-side binary bisection (x first on ties).
Each leaf path records its half choices, including the common boundary.
The 1,133 paths are prefix-free and have Kraft sum one, or equivalently
form the leaves of a full binary tree. They therefore cover the entire
closed initial square. There are no unprocessed or depth-cutoff leaves.

| Leaf rejection or retained region | Number |
| --- | ---: |
| Impossible ell interval | 10 |
| G has strict nonzero sign | 81 |
| E has strict nonzero sign | 6 |
| Interval Newton necessary enclosure misses the cell | 1,010 |
| Outside x,y<b | 23 |
| Inside T | 1 |
| Inside boundary box B_1 | 1 |
| Inside boundary box B_2 | 1 |
| **Total** | **1,133** |

Maximum binary depth is 25. For an outside leaf its lower x or y
endpoint is at least the upper bracket for b, so it contains no actual
strict point.

For completeness, the Newton test is an elementary mean-value identity.
For a cell X, midpoint m, F=(E,G), any rational matrix C, and an interval
matrix J containing every derivative DF on X, every zero z in X satisfies

```text
z in m - C*F(m) + (I-C*J)*(X-m).
```

Each Newton row supplies the four integer numerators of C, denominator
1024. If either resulting coordinate interval misses X, there is no
zero in X. This inference needs neither existence of a zero nor
invertibility of C. The derivative bounds use exact forward
differentiation of the displayed rational formulas. All intermediate
denominators avoid zero on a leaf where they are used.

Every interval operation rounds outward to an integer multiple of 2^-44.
The only irrational constant is bracketed by

```text
24879108095803/S < sqrt(2) < 24879108095804/S.
```

The bracket follows by squaring integers; it is a premise only through
those two strict integer comparisons. No numerical optimizer, floating
endpoint or assumed root count enters the table.

## 3. Both boundary boxes contain only a known invalid limit

The two retained boundary boxes are

```text
B_1 = [53/128,425/1024] x [53/128,425/1024],
B_2 = [53/128,425/1024] x [0,1/1024].
```

For B_1 take C_1=[[-92,-228],[-1598,-378]]/1000.
For B_2 take C_2=[[-26,188],[411,107]]/1000.

On each entire box the interval derivatives give the following upper
bounds on the two absolute row sums of I-C_i*DF:

| Box | First row bound | Second row bound |
| --- | --- | --- |
| B_1 | 3991344362772/S | 15930549892700/S |
| B_2 | 3566751017924/S | 6277960150387/S |

All four numerators are strictly less than S. Hence F is injective on
each box: if F(z)=F(w), integrate DF along the segment and rearrange
z-w=(I-C_i*integral(DF))*(z-w); the strict row-sum norm bound forces z=w.

Exact arithmetic in Q(sqrt(2)) verifies

```text
F(b,b)=(0,0),       F(b,0)=(0,0).
```

These identities are also verified directly by the committed checker,
using rational triples (a+c*sqrt(2))/d with exact integer cancellation.
At (b,b), d=0 and T=Y-K^2/(4Y), Y=1+3/sqrt(2).
At (b,0), d=-1 and T=K*(K-1)/(K+1), K=2+sqrt(2).
Both have squared radius (219+130*sqrt(2))/98.

The known point lies in its respective box. Both have x=b, so neither
belongs to the actual strict domain x<b. Injectivity therefore excludes
all actual configurations in both boxes. It would be invalid merely
to discard a neighborhood because the limiting point is invalid;
the derivative argument is what excludes that whole neighborhood.

Consequently every actual E_A configuration has (x,y) in T.

## 4. A uniform four-center cover bounds total capacity by nine

Interval evaluation over the entire T gives

```text
R^2 <= 4.137398891389410 < 17/4.
```

Here the terminating decimal is an outward presentation only; the
checker compares the exact scaled-integer upper endpoint with 17/4.
The four compact center boxes K_A,K_B,K_D,K_C in the certificate are
also the exact outward interval evaluations on T. Their order is
A,B,D,C. Rough decimal presentations for orientation are

| Center | x interval | y interval |
| --- | --- | --- |
| A | [-1.298065,-1.297169] | [-0.450981,-0.446128] |
| B | [1.116149,1.117045] | [-0.734414,-0.729561] |
| D | [-0.090958,-0.090062] | [-0.626719,-0.618423] |
| C | [-0.028917,-0.027088] | [1.336706,1.342121] |

Use the JSON integer endpoints, divided by S, for exact comparisons.

Every unit-square center c in a disk satisfies

```text
R^2 >= |c|^2 + |c| + 1/2.
```

Indeed the farthest vertex has squared norm
|c|^2+1/2+|c dot e|+|c dot f| >= |c|^2+1/2+|c|.
Since R^2<17/4, every center has |c|<3/2.

Now cover [-3/2,3/2]^2 by the second full binary tree in the certificate.
Its 161 leaves have maximum depth 15. A leaf is assigned as follows:

* Outside: every point has squared norm strictly greater than 9/4.
* Core i: every point of the cell is within distance strictly less than
  one of every point of K_i.
* Slot j: the entire cell is inside the disk of radius 9/20 at the
  specified slot center.

The five slot centers, all divided by 1000, are

```text
(-1130,779), (1223,404), (544,340), (997,825), (-605,425).
```

All checks reduce to corners of axis-aligned rectangles. For a core
assignment, maximize squared distance independently in each coordinate
over cell and core endpoints. For a slot assignment, perform the same
check against its rational singleton center, with bound 81/400.
For an outside assignment, minimize coordinate squares, including zero
when the coordinate interval straddles zero.

| Leaf assignment | Count |
| --- | ---: |
| Outside center disk | 24 |
| Core A | 12 |
| Core B | 13 |
| Core D | 49 |
| Core C | 22 |
| Slot 1 | 10 |
| Slot 2 | 6 |
| Slot 3 | 12 |
| Slot 4 | 5 |
| Slot 5 | 8 |
| **Total** | **161** |

Two distinct packed unit squares have center distance at least one,
since their open inscribed disks of radius 1/2 are disjoint. Thus no
additional center is in a core-assigned leaf. No actual center is in an
outside leaf. Every additional center is consequently in one of five
slot disks. Each disk has diameter 9/10<1 and contains at most one
additional center. Total capacity is at most 4+5=9.

This is the [finite center-cover criterion](FINITE_CENTER_COVER_CAPACITY.md)
with the sharper center-radius bound and disk slots. The two S
transmitters count among the additional centers, over their full slide
intervals. Reflection gives the identical conclusion for E_B.

## 5. Reproduction and scope

```text
node research/ten/check_strict_side_source_closure.mjs
node research/ten/check_strict_side_source_closure_60bit.mjs
```

The 44-bit arithmetic uses direct integer quotient bounds and quotient
differentiation. The 60-bit backend was written separately, uses
integer-square-root brackets, reciprocal interval arithmetic and Jet
differentiation, and checks the radius and force height through
algebraically different expressions. It verifies the same 1,133+161
leaves. Coverage is checked by Kraft/prefix tests in one implementation
and by recursive full binary tries in the other. The logical Newton and
capacity predicates are shared; this is not independent mathematical
review. Exact Q(sqrt(2)) evaluation checks both boundary identities.

Both arithmetic/checking bodies were executed successfully in the
session's V8 JavaScript runtime. The execution workspace was unavailable,
so the Node command-line entry points were not run there. The full data,
checker bodies and this proof are committed; there is no claimed
n=10 Lean theorem, Lean build or kernel verification.

No whole master-family status changes: the V_V source rows and radial D
endpoints must still be closed before this argument can exclude LSLSLD.
