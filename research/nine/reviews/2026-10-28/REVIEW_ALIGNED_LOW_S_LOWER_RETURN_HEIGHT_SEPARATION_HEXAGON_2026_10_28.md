# Full independent review: aligned-low lower-return height separation

Date: October 28, 2026. Reviewer: hexagon.

**Decision: ACCEPTED, unchanged, for the entire stated enlarged scalar
domain and its complete exact certificate.** I read the full theorem
and the entire author implementation, checked every mathematical
guard and interval operation, reproduced the exact author certificate,
and separately replayed every terminal box using an independently
written rational interval implementation and a finer radical lattice.
No correction is requested.

The exact reviewed artifacts are

| Artifact | SHA-256 |
| --- | --- |
| ALIGNED_LOW_S_LOWER_RETURN_HEIGHT_SEPARATION.md | 93bb8e2d6dc3f2965c1a1868ba4a7552f63c5326cbe05cab5381950f4db765be |
| certificates/aligned_low_s_lower_return_height_separation.py | bd92d1895f240805a78ea5160b0b7ed56f6948a4ec6ce88ff870bb55a6472f15 |

Root contributed the initial continuous scalar argument. This is a
separate full peer review of the frozen theorem, domain and complete
code; it does not count that contribution or the author's arithmetic
as an independent acceptance. The actual geometric LTAC caller and its
remaining contact placement are outside this scalar-only review.

## 1. Complete scalar domain, including all weak endpoints

I retained the whole printed parameter box

    14/15<=d<=1, 29/50<=h<=2/3, 2/25<=t<=5/7.

The definitions are a=1-d, g=1-h, b=sqrt(1-t^2), with the
additional actual inequality b>=t. The lower circle equation is

    R^2=(d+1)^2+1/4, Y=g+b+t,
    X=sqrt(R^2-Y^2)>0, x=X-b+t.

The entire required physical-mean/screen enlargement is

    3/10<=x<=d, x>=t,
    (d-x)t >= (h-1/2)b.

The upper quantities retain their original coupled definitions

    w=x+a, ell=sqrt(w^2+h^2), c=w/ell, s=h/ell,
    N=ac+hs, K=xs,
    W=sqrt(R^2-(N+1)^2), rho=W-K,
    7/8<=rho<=1, delta=1-rho,
    tau=b(xY/X-g), 0<=tau<=1.

Both circle equations use the same actual d and radius expression.
No independent maximal-radius bound replaces one of them. The upper
mean rho and the lower mean tau remain constrained by their actual
formulas, and are not selected inside their allowed intervals.

Every actual denominator is positive: h>=29/50, w>=3/10,
ell>0, and X>0 is an explicit hypothesis. Also K>0 and
rho>=7/8 imply W>0. The parameter box and mean inequalities have
their printed weak endpoints; the explicitly required X>0 is not
weakened into a zero-denominator evaluation. In particular d=1,
h=2/3, b=t, x=d, x=t, rho=7/8 or 1, and tau=0 or 1 are
not discarded merely because the physical caller has stricter bounds.

The accepted conclusion is precisely

                    tau*b-delta*c > 1/25000.

It is not asserted from the lower-circle equation alone, outside
the printed t range, or without the actual leaf screen and upper
mean constraints.

## 2. Every author interval operation is an outward enclosure

The author code uses only integers, Fraction and integer square root
for mathematical decisions. There are no floating-point constants,
approximate optimizer calls or sampled poses. Its immutable rational
endpoint pairs have the standard exact addition/negation rules.
Multiplication takes all four endpoint products, so it is valid for
every sign pattern. The square operation uses zero as the lower
bound exactly for an interval containing zero and otherwise the
lesser endpoint square. Division is performed only after the full
denominator interval has a strictly positive lower endpoint.

For a nonnegative rational z and S=2^64, the lower radical endpoint
is floor(S*sqrt(z))/S. Computing integer square root after taking
the exact integer quotient z*S^2 gives exactly that floor. The
upper endpoint is the same point at an exact square, and otherwise
one lattice unit larger. The code explicitly checks the squared
lower/upper inequalities. A formal negative lower radicand bound is
clamped only to zero, while a negative upper bound is rejected at
the preceding real-radicand guard. This retains every real actual
radical and every exact radical endpoint.

Interval intersections are only with necessary inequalities or
another enclosure of the same actual quantity. They never identify
two independent variables or replace a shared mean. Treating repeated
uses of a variable independently can only enlarge the range. There
is therefore no hidden correlation assumption in the enclosure
arithmetic.

## 3. Complete audit of the rejection and contraction guards

I checked every possible code return, including guards that do not
occur as a final reason in this particular terminating tree.

1. Intersecting b with [t_lower,1] is necessary for b>=t.
   It does not replace b>=t by a false pointwise equality. An empty
   interval proves that the entire box has no admissible point.

2. X^2 has its lower-circle enclosure R^2-Y^2. An upper bound
   at most zero is incompatible with the explicit X>0 premise.
   Otherwise the outward square root retains every possible actual
   X, including when the formal lower radicand is negative.

3. Intersecting x with [max(3/10,t_lower),d_upper] retains
   every actual x>=3/10, x>=t, x<=d. The subsequent X
   intersection with x+b-t is justified by the exact original
   identity. Neither intersection removes an admissible parameter
   point or fixes its x value.

4. The screen expression is the left side minus the right side of
   (d-x)t>=(h-1/2)b. Only a strictly negative interval upper
   endpoint causes rejection. A possible screen equality is retained.

5. The actual ell, c,s,N,K and W radicand use their complete
   definitions. A negative upper W-radicand bound excludes reality.
   Intersecting rho=W-K with [7/8,1] retains both mean endpoints.
   A denominator interval containing zero causes subdivision, not
   division or rejection of an otherwise admissible point.

6. Tau uses its original quotient b(xY/X-g), then is intersected
   with [0,1]. This retains tau=0 and tau=1. The final target
   enclosure is tau*b-(1-rho)c. Its lower endpoint is therefore
   a valid lower bound for every admissible point in that box.

The author's first terminal success test is a strictly positive
target bound. The complete run then verifies that every such bound
is greater than 1/25000. This final exact comparison is essential
and is present. An early positive bound below the claimed uniform
floor would make the checker fail, rather than prove a weaker result
silently. No such terminal occurs in the actual certificate.

## 4. Whole initial box coverage

Unresolved boxes split at the rational midpoint of the coordinate
having largest width divided by its original width. Ties choose the
first coordinate. Both closed children are retained, so their union
is the exact closed parent and includes its splitting plane. The
stack operation processes both children; a terminal box is never
also subdivided. Hence the generated paths are a finite prefix-free
partition, with no duplicate or omitted child.

I reproduced the author run with its exact frozen code. Its complete
result is

| Quantity | Reproduced exact value |
| --- | ---: |
| Visited nodes | 3,135 |
| Terminal boxes | 1,568 |
| Leaf-screen exclusions | 374 |
| Strict target certificates | 1,194 |
| Maximum depth | 15 |
| Unresolved terminal boxes | 0 |

The node count is 2*1568-1. The author's sibling-collapse check
returns the single empty root path. The canonical terminal payload
matches exactly the printed digest

    3e16224eccf7d9f4b93cd98f0b49901d15ac6ff1aa0decfff4620c6e282f9662.

I also checked the entire printed large minimum fraction against
the reproduced minimum over all positive leaves. It is equal, and
its comparison with 1/25000 is strictly positive. There is no
rounded decimal minimum in the proof.

## 5. Separate 96-bit reconstruction of every terminal box

My independent implementation imports no author code or interval
helper. It uses a separate immutable Interval class, exact Fraction
arithmetic and S=2^96. For z=n/d its radical floor is computed by
the different exact formula

    floor(sqrt(n*d*S^2)/d).

This equals floor(S*sqrt(n/d)). At every evaluation the independent
code checks both defining floor inequalities before producing the
outward radical bounds. Its lattice is finer than the author's,
but all comparisons remain exact rational operations.

The only author data consumed are the terminal binary paths, reasons
and claimed margins as a certificate to check. I build a new binary
trie, rejecting duplicate paths, a leaf with descendants, a leaf
under a previous prefix leaf, and every missing sibling. Each box
is reconstructed from the initial rectangle by independently
recomputing the largest normalized width and rational midpoint at
each internal node. The two closed child endpoints are checked
against their parent. Thus coverage is not inferred from the author's
node counts or claimed sibling-collapse output.

At every reconstructed leaf I re-evaluate the full scalar formulas
and every guard using the independent intervals. All 374 screen
leaves again have a strictly negative screen upper endpoint. All
1,194 positive leaves again have a target lower endpoint strictly
above 1/25000. Every independently obtained positive bound is at
least the corresponding author bound. All original terminal reasons
agree, all 3,135 tree nodes are reconstructed, and the maximum
depth is independently 15.

This proves the full continuous statement: every admissible actual
point of the initial rectangle lies in some closed terminal box.
It cannot lie in any screen-excluded box. Every remaining terminal
gives a strictly valid lower bound above 1/25000 for that point.
Boundary points shared by children cause no gap, and all endpoint
inequalities of Section 1 remain exactly as stated.

The complete independent records are

| Artifact | SHA-256 |
| --- | --- |
| certificates/review_aligned_low_s_lower_return_height_separation_hexagon.py | c8ced658818cb45978c14964337e2fdbcb43c9ab3aad623667bf77d9029e25b0 |
| checkpoints/hexagon_aligned_low_s_lower_return_height_independent_checks_2026_10_28.json | 2c81e956ec55ca2c6abdd648a92c45ba74efdf64718bc622d2b149df269589f1 |

The reproduced author-output JSON has SHA-256
ce034bcdca30eb79e8ea0e1647885f71614af2da138ebf58d5856978e41d9470.
Both complete terminal records are retained in the recovery archive.

## 6. Exact physical interpretation and remaining caller obligations

The algebraic height conversion in the source is correct. Since
g=1-h, the difference between the upper height h-delta*c and
one unit above the lower return height -g-tau*b is exactly
tau*b-delta*c. Thus the accepted strict scalar bound gives

    1-g-tau*b < h-delta*c-1/25000.

This conversion does not assert that an arbitrary tilted connecting
unit rises at most one above a contact. The physical caller must
establish the actual contact feature, all scalar premises and that
literal height reach separately. I have not imported a two-force
equation at either degree-three physical body or certified the whole
LTAC.S family by this scalar-only record. Triangle's complete physical
caller audit remains separate.

The full stated scalar theorem and its complete exact code are
independently accepted at the frozen pins above, including all
weak mean, angle and parameter endpoints. No original force,
physical unit or contact mean is changed by this review. No numerical
sample, approximation premise, Lean/CI, shared metadata or remote
operation was used.
