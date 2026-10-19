# Gate 3B.2 / M5: disk-preserving surplus split

Recovered and reviewed from the preceding uncommitted handoff. Depends on
GATE3B_M5_GLOBAL_SUPPORT_SURPLUS.md. Full M5 and unrestricted optimality
remain OPEN. This note does not assume that competitive packings have LOW
surplus or that the oblique chain is forced.

## 1. Exhaustive threshold split

Let Q=9789/2500, W0=(41+15sqrt(2))/2, and E=W-W0. Every actual M5 packing
under q<=Q belongs to exactly one of

    HIGH: E>3/1000,
    LOW: 0<=E<=3/1000.

The equality threshold is in LOW. Both folded types, all centers, actual
SAT choices, and angle or tangency ties remain covered. The harmonic
support theorem is a lower bound on W, not a disk-dependent upper bound.

## 2. Inscription removes all frame variables in LOW

The proved stability theorem supplies three frames within epsilon=1/200
of one reference frame, and five within epsilon of the reference frame
at 45 degrees, modulo quarter-turns. After a common rotation, take the
three-label reference frame to be standard.

Set b=200/201. At every actual center place a square of side b in the
assigned exact reference orientation. It is contained in its host unit
square, since its half-width in either host axis is at most

    b(|cos delta|+|sin delta|)/2 <= b(1+epsilon)/2 = 1/2.

The interiors of these full-dimensional subsets lie in the interiors of
their host squares; boundary coincidences do not invalidate nonoverlap.
Thus all eight smaller squares remain in the SAME disk and all 28 pair
nonoverlap conditions survive, without choosing or preserving SAT owners.

Scale the entire configuration by 1/b. Every LOW packing therefore gives
an ACTUAL packing of three standard unit squares and five 45-degree unit
squares with

    q_ref=q/b^2 <= Q*(201/200)^2
        =395485389/100000000 =3.95485389 <99/25.         (R)

This implication is one-way. A reference packing need not lift back to
an original LOW M5 packing. No original center, frame, or owner is assumed
to be near a candidate pose, beyond the proved frame stability.

## 3. Exact reference problem

For a standard square centered at p_i=(x_i,y_i), true disk containment is

    x_i^2+y_i^2+|x_i|+|y_i|+1/2 <= q_ref.             (D0)

For a 45-degree square it is

    x_i^2+y_i^2+sqrt(2) max(|x_i|,|y_i|)+1/2 <= q_ref. (D45)

These expressions are maxima of the actual four vertex squared norms.
For center difference d=(dx,dy), exact nonoverlap is:

    standard/standard: max(|dx|,|dy|)>=1;
    diagonal/diagonal: |dx|+|dy|>=sqrt(2);
    mixed: max(|dx|,|dy|,(|dx|+|dy|)/sqrt(2)) >= (1+sqrt(2))/2.

All equalities are allowed. Impose all three standard pairs, all ten
diagonal pairs, and all fifteen mixed pairs, as well as (R), (D0), (D45).
There are 16 continuous center coordinates and no frame variables.
The problem is still disjunctive; the reduction is not an exclusion.

## 4. The previously proved reference-chain child is excluded

Choose two standard squares A,B and label the five diagonal squares
H,L,D,R,E. Put e=(1,0), f=(0,1), u=(e+f)/sqrt(2), v=(-e+f)/sqrt(2),
w=(1+sqrt(2))/2. The reference-chain child is defined by

    e dot(p_B-p_A)>=1,
    u dot(p_A-p_H)>=w,
    v dot(p_B-p_E)>=w,
   -v dot(p_L-p_H)>=1,
   -v dot(p_D-p_L)>=1,
   -u dot(p_R-p_E)>=1,
   -u dot(p_D-p_R)>=1.

Allow any labeling and any common rotation/reflection preserving the
reference frame classes. The remaining standard square is unrestricted.
These projections need only be valid separators; they need not be
canonical choices or contacts.

GATE3B_M5_OBLIQUE_CHAIN_CURVATURE.md proves that this family has
q_ref>99/25 for all centers. In its contrary radius range, actual vertex
averaging and path sums give

    2q_ref >= (2+sqrt(2)-sqrt(q_ref-1))^2
                 +(3sqrt(2)-sqrt(q_ref))^2.

The top-pair bound ensures q_ref>=1. The rational estimates
sqrt(2)>1414/1000, sqrt(q_ref)<199/100, sqrt(q_ref-1)<1721/1000
make the right half exceed

    7937753/2000000 =99/25+17753/2000000,

a contradiction to q_ref<=99/25. This contradicts (R). In original units
such a LOW-CHAIN packing would require q>17600/4489>Q, whose margin is
57179/11222500. The useful improvement is the owner-independent inclusion
argument, not tuning that constant.

## 5. Exact remaining obligations

Every hypothetical M5 packing under Q lies in:

* HIGH: E>3/1000, with the full original geometry (OPEN).
* LOW-CHAIN: E<=3/1000 and a derived reference packing has the chain
  (EXCLUDED by Section 4).
* LOW-REST: E<=3/1000 and the derived exact 3+5 reference packing satisfies
  all the equations in Section 3 but has no such chain (OPEN in this note).

This is a complete parent-to-children implication: threshold split,
stability, subset inscription, then existence/nonexistence of the finite
chain choices. It is not a final classification of internal arrangements.
Any feasible original packing must have every derived reference packing
chain-free, by the proved contradiction.

Continue by proving an actual exclusion or usable geometric decomposition
of LOW-REST, retaining all disk curvature and all pair conditions. HIGH
still needs a separate disk-dependent obstruction. Neither failed local
optimization nor four tangent strips can discharge these obligations.
Do not advance to M6 or make a global optimality/equality claim.

## Audit and provenance

The preceding handoff's Fraction-only verifier was rerun successfully in
this continuation, including host/reference inclusions, true vertex and
pair checks, and the exact rational radius margins. The continuous
reduction and reference-chain implication are the hand arguments above.
No Lean compilation or CI was invoked.
