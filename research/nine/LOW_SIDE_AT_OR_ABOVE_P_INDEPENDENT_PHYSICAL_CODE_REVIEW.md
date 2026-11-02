# Independent review of the low side at-or-above-P exclusion

November 2, 2026. Independent review by the weak-outer work agent of
`LOW_OPPOSITE_SIDE_AT_OR_ABOVE_P_WITH_LOWER_CENTRAL_HAND_TABLE.md`,
the complete restored `verify_low_side_upper_order_exact.cpp`, and
`run_low_side_upper_order_exact_replay.py`.

**Verdict: PASS.** The physical reduction and all thirteen implemented
necessary scalars are sound for the stated original-square caller. The
eight closed roots are complete. The delivered full saved C++ source is
the source actually compiled for the accepted canonical replay. The
canonical replay accepts all 143,088 strict leaves, with least reserve
136564324/2^48. No Lean, Lake, CI, human review or proof-kernel claim is
made. This review did not repeat that full arithmetic replay.

## 1. Retained original caller and the actual assigned main

The caller keeps the original low-P-floor 010/11 configuration, the
selected actual P above both inner mains, xP>=0, a lower central original
V, and an original left-side S above B with yS<=3/5. The contrary order
is yS>=yP. S can be the original selected L or an unselected extra.
There is no new S/P cone and no replacement frame.

The actual lower central V and the accepted quarter-main-height theorem
give hB,hC<57/100 and yB,yC>-61/60 through the separate original-pair
lemma. That lemma compares the genuine B/C owned projections with the
width-increment support 1+|hB-hC|; it does not infer a narrow second
main solely from a narrow first main.

Choose M on V's own horizontal half: M=B for xV<=0 and M=C for
xV>=0. The actual V/M clearance exceeds 909/1000, so

    yM>yV+909/1000>-91/60+909/1000=-1823/3000.

This is a bound on that same original M. The code keeps its side in
`main_side` and uses only that main's actual folded frame and coordinate
band. It does not apply this stronger height to both mains. At xV=0
either permitted main suffices and both charts are present.

The selected cone and original center disks give xP<1129/3000 and
xR>707/1000; the root weakens the latter to 7/10. Original side
clearance, endpoint localization and yS<=3/5 give

    29/60<=-xS<=121/200,       |yS|<=3/5.

These deductions hold whether S=L or an extra. The original selected
L need not receive another variable when S=L: no later scalar requires
an independently parameterized copy of L.

## 2. Complete unsigned support and physical vertical clearance

For a folded frame let a>=b>=0, a^2+b^2=1,
h=(a+b)/2 and k=(a-b)/2. For a second frame write A,B,H,K.
The code's two expressions

    (1+aA+bB+|aB-bA|)/2,
    1/2+max(kA+hB,hA-kB)

are pointwise identical: the two entries of the maximum are
`(aA+bB +/- (aB-bA))/2`. Intersecting their independently computed
interval enclosures is therefore sound. It is not an intersection of
two different lower bounds.

This common expression is the physical owned-axis support at the
folded-angle difference. If the two actual chiralities instead produce
the folded-angle sum, that sum lies between d and pi/2-d, where d is
their folded-angle difference in absolute value. The function cos+sin
has its minimum at the equal-valued endpoints of this interval. Thus
the difference expression is a lower bound for either actual relative
chirality. The separately proved 1+|h-H| bound is also necessary, so
the maximum of it and the difference expression is a valid lower
support `sigma` for every genuine pair owner.

For an ordered physical pair with horizontal gap at most d<1, every
owned normal gives a vertical lower bound among

    (sigma-a*d)/b, (sigma-b*d)/a,
    (sigma-A*d)/B, (sigma-B*d)/A.

Taking their minimum includes all owners and signs, because replacing
the signed horizontal projection by its absolute upper bound weakens
the separator inequality. Each numerator is positive: sigma>=1>d.
Increasing either small denominator to 1/40 can only weaken its lower
bound. A zero vertical component cannot separate at this horizontal
gap, and adding its finite clipped expression can only lower the
minimum. The center-distance radical is another independent necessary
clearance for the same actual pair. The maximum of it and the facet
minimum is therefore sound.

All these lower bounds are nonincreasing in nonnegative d. Consequently
the larger horizontal bounds used for the original S/P and M/P pairs
retain every physical possibility. The relevant roots have d<1;
the S/P maximum is 368/375 and the farther left-main/P bound is below
9/10. Both folded S and P parameters are retained throughout.

## 3. The same original S meets its original endpoint rectangle

The lower adjusted endpoint coordinates AL,AR follow from the original
endpoint/R pair toll and Vmain>=etaM. This remains true when M=C:
AL is still a lower bound for the actual left endpoint because only
the valid nonnegative total budget has been weakened. No side of S is
changed when choosing the assigned-main chart.

On the necessary domain AL,AR<=61/60, the height functions cL,cR
describe rectangles inside those same original endpoints. Clipping an
endpoint contribution at 61/60 merely defines the scalar beyond points
already rejected by the separate endpoint rows. Every radical remains
defined on the full closed root.

Reflect the left endpoint horizontally. Its fixed horizontal center and
halfwidth are 3/2 and 217/480, so its inward edge is 503/480. The same
actual S has reflected coordinate z=-xS and |yS|<=3/5. Put
q=503/480-z and e=3/5-cL. The rectangle's vertical owner is impossible
because 3/5<cL+hS. Its horizontal owner needs q>=hS. The two physical
S-owned axes, bounding both signs and both chiralities, need respectively

    aS*q>=1/2-bS*e,
    bS*q>=1/2-aS*e.

These are exactly the code's three alternatives for qmin. Both
numerators are positive. A denominator floor weakens the alternative;
the aligned vertical owner is impossible, so its finite replacement is
also conservative. Thus z<=zmax is necessary, and row 2 retains the
separate condition zmax>=29/60.

The actual S slope `box[2]` is used in this endpoint comparison and
again in `vertical_clearance(p,s,dPS)`. Its frame is never independently
chosen in the two inequalities. Forgetting its chirality is justified
by the preceding pointwise bounds, without omitting a sign root.

On a physical point x+zmax is nonnegative. Replacing it by its positive
part in nonphysical scalar extensions does not alter the physical use.
The contrary order yS>=yP then gives exactly the code's bound

    yP<=3/5-K(P,S,x+zmax).

## 4. The same original M and P supply the lower height

For M=B, its negative coordinate band yields
dMP=xP+1+delta-h. For M=C, taking the maximum of the two absolute
endpoint gaps to [g-delta,1+delta-h] gives the code's other formula.
Both bound the actual original M/P horizontal gap without choosing
a new position of M.

The physical lower-support clearance above and the original main's
aligned inset are independent lower bounds for that same pair. The
inset formula includes its vertical coordinate owner and both upward
P-owned axes. Since dMP-g<1/2, a horizontal or downward separating
owner is impossible. All numerator signs are positive, so the same
denominator-floor convention is valid. Adding the actual main-height
bound -1823/3000 gives the code's `Pminus`.

The P frame is the same frame in the S/P support, M/P support, inset
facets, bad whole floor, circle corners and original P/R pair. No
clearance is assigned to a different version of P. The original R
parameters likewise remain in its shoulder toll, corner bounds,
endpoint clearance and physical P/R support.

## 5. All thirteen scalar rows and sign charts

The code reconstructs the four actual signed P and R corners. Its
positive-chirality offsets are `(k,h),(h,-k),(-k,-h),(-h,k)`;
the negative ones are `(h,k),(k,-h),(-h,-k),(-k,h)`. Each circle
inequality gives a necessary upper height even when a center is below
zero. The initial cap 3 exceeds the universal center radius.

The R rectangle loss has the correct global R chirality. The aligned
negative-chirality complement is covered by k(1/4)>503/480-7/10;
its positive-part loss is zero below that slope. Thus the denominator
floor at 1/4 does not omit a possible axis.

The four finite cone contractions preserve the same actual P,R heights.
Intersecting their difference with [-D,D] retains both possible
vertical orders. The exact signed support

    (1+|aP*aR+sP*sR*bP*bR|
        +|sR*aP*bR-sP*bP*aR|)/2

is used in both final P/R physical rows. Every one of the four original
owner axes appears with both directions through the absolute projection;
maximizing at both height-interval endpoints is a conservative bound.
The original weak-gap and inset-gap inequalities are separate rows.
All thirteen returned entries match the manuscript's numbered table.

The C++ roots are exactly

    [0,1]^3 x [0,1129/3000] x [7/10,13/12] x [1/2,57/100].

The stored integer triples `(0,1129,3000)`, `(42,23,60)` and
`(50,7,100)` have precisely these last three intervals. Charts 0--3
use the left assigned main and 4--7 the right; the remaining bits give
all four independent P/R sign combinations in lexicographic order.
The actual S and M chiralities were removed only by pointwise bounds.
Thus the eight roots include every original choice, all zero slopes,
the diagonal slopes, xP=0 and every root boundary.

## 6. Directed arithmetic and complete forest reconstruction

The arithmetic engine uses signed integer endpoints over 2^48.
Multiplication and division enumerate all endpoint products or quotients
with outward floor/ceiling; division requires a strictly positive
denominator. Square treats an interval containing zero separately.
Absolute value, minima and maxima preserve their full ranges. Every
square-root endpoint comes from an integer square root, with both
squared enclosure inequalities checked.

Signed 64-bit results are range-checked; their products fit the signed
128-bit intermediate range. The rational-coordinate constructor checks
its scaled numerator range before multiplication. The integer radical
workspace remains below the 128-bit limit. The actual forest depth is
41, well within the explicit limits. The monotone frame endpoint bounds
are valid: a,k decrease and b,h increase with folded slope; main a,g,k
decrease and main b,eta increase with h>=1/2. The toll curve has one
maximum at t=4/9, explicitly checked when the interval crosses it.

Root coordinates are reconstructed as exact rational dyadic subdivisions,
not rounded midpoint data. Each split has both closed children. The
engine demands exactly eight complete roots, node/leaf identity, legal
split and scalar tags, no missing or trailing byte, an empty final
stack, and a strictly negative upper enclosure at every leaf. A zero
upper enclosure is rejected.

The JSON wrapper rejects duplicate keys, noninteger and boolean events,
illegal tags, nonempty frontier, incorrect counts and incomplete graph
coverage. In the compact schema the root constants and chart order
are fixed by the standalone engine. Only integer split/leaf tags enter
the arithmetic replay; discovery upper bounds do not enter it.

## 7. Complete delivered-source binding and accepted evidence

The restored source is 13,969 bytes and includes the complete evaluator,
all thirteen scalar rows and the full replay loop. Its SHA-256 is

    d4fab70e53914877a54bbaadfb37e1a413172a5078f33ac31216334c773db453.

The wrapper now reads those exact saved source bytes, writes an immutable
temporary snapshot, compiles that snapshot, hashes the resulting
executable and executes that executable. An old binary is never used.
The earlier truncated-source problem therefore cannot be hidden by a
stale executable in this accepted replay. The wrapper SHA-256 is

    30b36db32e34a4aeb6e98a548f583c75ce10208c0d7ac2cc42992c57490f2293.

The accepted executable SHA-256 is

    98c2a33710887b7ecf1e0ef875d3038b7d1730cff64d874b7617ffdb664cf889.

The certificate SHA-256 is

    53769f5264a76d8991a72f22eaebf882337f1a9fb5f7857c71ffa3652132446b.

The canonical report in `computer_assisted` records a fresh complete
source-snapshot replay with these same hashes. I independently checked
that the reviewed agent files and canonical source, wrapper and
certificate are byte-identical, and reconstructed the event payload hash

    3575dd3f257d106b3f4cd31207c64450faaa06873d011dc225a06e94c40efa61.

The full accepted forest has eight roots, 286,168 nodes, 143,088 strict
leaves, maximum depth 41 and no frontier. The per-root leaf counts are

    946, 45571, 946, 95545, 20, 20, 20, 20.

Its least positive reserve is 136564324/2^48. All thirteen recorded
rejection controls are bound to the same complete source and executable;
they include a false full-root proof, truncated/trailing binary streams,
illegal binary tags, malformed metadata and boolean events. The records
were inspected; this review does not claim to have rerun those controls.

The original counterexample would supply a point of one of these complete
roots with all thirteen scalars nonnegative. The accepted strict leaf
containing it gives a contradiction. Together with the accepted below-P
component, this proves the complete low-side/lower-central exclusion,
including yS=yP and yS=3/5. Whole-mask closure remains the responsibility
of the separate original-nine assembly.
