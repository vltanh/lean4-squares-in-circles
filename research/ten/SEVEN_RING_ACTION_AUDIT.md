# Independent audit of the exact seven-ring action verifier

Auditor: four_core_geometry, 2026-10-29.

Scope: `research/ten/check_seven_ring_action.cpp`, conditional on the exact
one-chirality equations and internal-concurrence inequality from the existing
reviewed manuscripts. This is a computer-assisted verification, not a Lean
proof or a new unrestricted n=10 proof.

## Correction found during audit

The first scratch verifier assigned the floating midpoint directly into a
Q36 endpoint field. An odd sum of endpoint grid indices gives a Q37 midpoint;
`grid()` would then truncate rather than enclose it. That initial run cannot
support the theorem. The corrected source splits at the integer grid midpoint
and gives both children that same endpoint. The current repository source
contains this fix, exact rational initial enclosures, rejection of reversed
intervals, and failure exit on incomplete coverage.

## Arithmetic audit

With the corrected split, every stored endpoint is an integer multiple of
2^-36 with absolute grid index <2^52. Binary64 stores these values and the
integer-to-double conversions exactly. All endpoint sums have integer indices
of absolute value <2^53 and are computed in 64-bit integers. Products have
absolute value <2^104 in signed 128-bit integers; division numerators have
absolute value <2^88. Floor and ceiling division correctly handle negatives.
No floating product or quotient decides an interval bound.

For square roots, the integer radicand is below 2^88. The floating square-root
guess is corrected by exact unsigned-128 comparisons until it is the exact
floor, followed by a ceiling increment when needed. The repaired square-root
index is below 2^44. A negative lower radicand is clipped only to retain the
nonnegative physical subdomain; a negative upper radicand rejects the cell.

The final source rejects reversed intervals conservatively (subdivision).
The initial parameter box contains the displayed rational domain. The split
uses an integer shared endpoint, so its two children cover the parent exactly.
The choice of longest side can use ordinary floating comparisons without
affecting coverage or any mathematical acceptance decision.

## Map and differential audit

For x=sin(a), y=sin(b), let c=sqrt(1-y^2), D2=R^2+1-2Rc, H=Rx-1,
k=sqrt(D2-H^2). The implemented sine/cosine of delta follow from the positive
root branch of the implicit angle equation. The cosine C of beta=delta-b is
(k(R-c)+Hy)/D2, and satisfies k=RC-cos(delta). Criticality gives next k=k*c/C,
then the displayed cosine of the next angle and its positive sine. Thus the
implemented f_R is the required physical recurrence, with no inverse-trig
branch left unresolved.

All three derivatives in basic() check by direct differentiation. In particular
C_y=-sin(beta)*cos(delta)/(k*c), which gives the less immediate y derivative.
For the x derivative, (k*c/C)_x=-R*y*c/(k*C^2), giving exactly the code's formula.
The R derivative is ordinary differentiation of D2,H,k,C, the next k, and
the next-angle cosine. The positivity checks used by tight() guarantee that
the expression is C1 on the whole interval box; its mean-value enclosure is
therefore valid. The rounded midpoint boxes still contain the exact midpoint
and remain inside the original boxes.

The centered product, quotient, square, and square-root identities used in
slope() are exact divided-difference identities. Replacing the base output
by s is justified by f_R(s,s)=s when R=sqrt(1-s^2)+1/(2s). Coefficients computed
before that replacement enclose the same exact coefficients. Repeating the
construction therefore gives valid one- and two-step centered matrices even
arbitrarily near the fixed point.

## Physical rejection audit

Every status-2 test is necessary for the specified physical orbit: positive
sine/cosine of alpha and of the acute delta; positive cosine(beta); strict
farthest-corner coordinate bounds R*sin(alpha)>1/2 and R*cos(alpha)>1/2;
internal concurrence cos(delta)*sin(alpha)<=cos(beta); and the stipulated
radius window. A failing interval computation is otherwise status 0 and is
subdivided, not silently discarded. Two propagated steps need not explicitly
return to the initial point: rejection of a necessary condition anywhere along
those steps already excludes a physical period-seven orbit from the box.

## Cone and winding audit

The one-step quadratic Y^2-XZ is positive by A>0 and 4A-B^2>0. The matrices
Q and K in the source have the correct signs for D=X dot T^2X and clockwise
cross product Kcw=Y Z-X W: Q=-sym(J), Kmat=sym(rot J). Positive definiteness of
Q, Kmat+(9/20)Q, and Q-Kmat gives

D<0, (9/20)D<Kcw<-D.

The dot and cross products are the ordinary Euclidean ones. Each one-step clockwise angle
has lift in (0,pi), and each sum of two consecutive lifts lies in
(3pi/4, pi+atan(9/20)). The latter upper endpoint is below 8pi/7: tan(3/7)>
3/7+(3/7)^3/3=156/343>9/20, while pi>3. Summing seven two-step lifts produces
4pi times an integer, strictly between 21pi/4 and 8pi. There is no such multiple
of 4pi. A period-seven orbit passing through (s,s) is the constant orbit;
otherwise all centered states are nonzero and the argument applies.

## Final result: PASS

The repository source was independently compiled with `-O1 -g -std=c++17
-fsanitize=undefined -fno-sanitize-recover=all` and replayed completely:

```
RESULT nodes 1631795 pass 618545 elim 197353 todo 0 deep 0 maxdepth 29
```

Exit status was zero and there were no sanitizer errors. The audited source
SHA-256 is `420d2dc56932b9f5b61d3c0b4d6d1ac5f6121178461fd000845e7c7c8eacf5f1`.

The accompanying SEVEN_RING_GLOBAL_ACTION.md was independently reviewed in
full. The only manuscript correction requested was to state the radius window
explicitly among the permitted rejection conditions; this has been made.
The exact rational endpoint calculations and elementary angle comparison
were separately checked using Python Fraction arithmetic.

The final version uses the identity metric in both cone checks and tests two
forward steps. Its full replay was independently repeated after reviewing
that simplification. All interval arithmetic, centered-coefficient, and
coverage checks above apply to this final source.

This passes the mathematical and implementation audit for the stated
computer-assisted one-chirality theorem. It does not constitute a hand-only
proof, formal verification, or classification of other contact ownerships.
