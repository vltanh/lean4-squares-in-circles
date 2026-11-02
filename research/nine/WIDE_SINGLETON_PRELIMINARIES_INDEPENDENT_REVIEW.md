# Independent review of the wide-main singleton preliminaries

November 2, 2026. Independent agent mathematical and code review by
`whole_mask`. No Lean or CI. This is not a human or kernel verification
claim and is not a whole-mask closure.

## 1. Reviewed sources and result

The following root-owned sources were read in full:

- `root_wide_pair/WEAK_MIDDLE_LOW_FLOOR_OPPOSITE_HEIGHT_HAND_PROOF.md`,
  SHA-256 `e8c6912f4ccb5d42633ba1e7d52f34b60e1a7517c83ddd88f2640f77bf5b8e40`;
- `root_wide_pair/verify_wide_lower_height.py`, SHA-256
  `d8dac63b533d6df30c0ea34af28fa2308084659ff5df6c3d25b00196d5f101ba`;
- `root_wide_pair/WEAK_MIDDLE_SINGLETON_NARROW_INSET_EXTENSION.md`,
  SHA-256 `2a11bac8a0105821838bacd3e2f74755348dd924e82220124639642ae7427b1b`.

The imported exact original-pair clearance implementation was already
reviewed separately in `WIDE_MIDDLE_PAIR_RELAXATION_INDEPENDENT_REVIEW.md`.
The complete original singleton manuscript and its accepted 4,512-leaf
interface were reread to check the proposed scope extension.

**Result: PASS for both preliminary height theorems and for the narrow
inset singleton extension.** No omitted frame, height order, endpoint,
original pair owner, or use of actual middle separation was found.

## 2. The two six-original height theorems

The precise hypotheses retain an original cone chain A,B,C,D with actual
outer links, an original central F above both inner mains, and a distinct
original central G below both. F has whole floor at most 1/10. The middle
main link may be actual or weak. The conclusions are strictly
\(y_G<-3/5\), and, on the same closed horizontal half-plane,
\(y_G+h_G<-9/20\).

The universal farthest-corner bound gives
\(|c|\le\sqrt{Q-1/4}-1/2\). The exact rational comparison with
\(r_*=3/2+331/20000\) is valid and has positive reserve
\(27061/400000000\). Repeating the already accepted outer-actual
position argument with this stricter radius gives the displayed main
bands. The largest central/main endpoint gap is
\(1-7/60000\), strictly below one. This explicit reserve is needed:
it rules out a zero-vertical-component owner at the artificial band
endpoint even for aligned original squares.

For fixed original frames and a nonzero vertical owner component,
\((\sigma-p|x-z|)/q\) is concave in the original main coordinate z.
The strict gap reserve and \(\sigma\ge1\) keep its numerator positive
throughout the root. The minimum over the finite original-owner family
is still concave: its hypograph is the intersection of the convex
hypographs. Consequently each sum of the F/main and G/main clearances
is concave, and its minimum on the full main interval occurs at an
endpoint. This verifies precisely the correlated sums \(T_B,T_C\).
Each sum uses the same original main endpoint for both terms.

The middle-pair path is also complete. If C is higher than B, the path
F,C,B,G gives \(C_F+M+B_G\). If B is higher, the path F,B,C,G gives
\(B_F+M+C_G\). Taking the smaller of these two values includes either
height order and equality. The quantities \(B_S,C_S\) and M use valid
upper bounds on their horizontal center gaps; monotonicity of the
physical clearance therefore gives lower vertical bounds. The middle
horizontal gap itself need not be below one because no endpoint
concavity claim is made for that gap.

Thus the displayed maximum T is a lower bound for the original height
difference \(y_F-y_G\). Since \(y_F\le h_F+1/10\), the implication
\(-y_G\ge T-h_F-1/10\) has the correct direction. The two strict table
targets then give exactly the two claimed conclusions.

Horizontal reflection to \(x_F\ge0\) preserves all hypotheses. In the
general theorem xG ranges over the full closed central strip; in the
same-half theorem it ranges over the corresponding closed half. The
folded support lower bound already includes both original chirality
relations, so no physical frame is identified with another.

## 3. Exact evaluator and complete cover interface

Every formula in `verify_wide_lower_height.py` matches the displayed
bands and the three paths. The interval expression for each correlated
sum separately evaluates both shared main endpoints before taking the
minimum. Distances and halfwidth subtractions use upper endpoints;
positive resources use lower endpoints. The maximum of the three lower
path bounds remains a lower bound. Subtracting the upper endpoint of hF
and, in the own-half target, hG is conservative.

The imported shape bounds use monotone exact endpoint functions, and
the imported clearance retains all four original owners, including its
explicit zero-component handling. It imports no numerical producer.

The checker reconstructs the exact six-dimensional root for each mode,
checks both printed rational reserves, and validates the entire binary
tree before arithmetic replay. Only tags 0 through 5 split; -1 and -2
are the budget and height leaves. Every leaf is recomputed with a
strict positive reserve. The final empty stack, exact node and leaf
counts, binary-tree identity, and computed maximum depth are checked.
The producer's numerical estimates are never acceptance premises.

The root author's separate complete exact replays establish:

| Root | Leaves | Nodes | Depth | Least exact reserve |
|---|---:|---:|---:|---|
| General lower height | 4,029 | 8,057 | 62 | `848421225106421/23058430092136939520` |
| Same-half lower whole ceiling | 8,278 | 16,555 | 19 | `5997044552684051/92233720368547758080` |

Their certificate hashes are respectively
`fb7c85683cd187d62a11ba3595f7bd4c908d3b484737b9f6a89082244daf5f22`
and
`1315576b59f780891595d9c3c672fd596a97579f895e2881f47f026d339f3588`.
The two exact reports and eight rejected damaged controls were inspected.
This review does not claim an additional full arithmetic replay by the
reviewer.

The routing consequence for two lower originals is sound: reflected
heights exceed 3/5, upper-column separation puts them on opposite strict
horizontal sides, the same-half one has reflected whole floor above
9/20, and the accepted ordered central-strip theorem fixes it as the
higher one. Applying that ordered theorem once more shows the other
whole floor is below 9/20. This is routing only; the wider-frame
singleton remainder is correctly left separate.

## 4. The narrow inset extension of the accepted singleton theorem

Assume now \(h_B,h_C\le31/60\), so both aligned inset halfwidths are
at least \(g_0=15/31\). The sharpened outer-actual main bands imply

\[
 x_B+g_B>-\delta,\quad x_B-g_B<\delta-2g_0,
 \qquad
 x_C-g_C<\delta,\quad x_C+g_C>2g_0-\delta.
\]

For every \(|x|\le l\), split according to whether x lies to the left
or right of the chosen main center. In the usual order, the first edge
bound gives the claimed adjusted distance immediately. In the alternate
order, \(g_0-l=1/1860>0\) gives the missing strict bound. Hence

\[
 |x-x_B|-g_B<x+\delta,
 \qquad |x-x_C|-g_C<-x+\delta.
\]

These remain valid even when a main center itself lies inside the
central strip. The upper endpoint of either loss argument is
\(l+\delta=1/2-7/60000\), so the original singleton proof's full
inset-clearance derivation, common-projection order, and aligned-angle
boundary are unchanged.

The remainder of that original proof uses only the two lower bounds on
the inset widths, these two loss bounds, the stated upper/lower orders
of F,G,H, and original square containment and nonoverlap. In particular,
the own-half loss bound, lower-center routing, opposite-side labels,
ordered strip cap, coupled elimination of the original F, small-slope
hand complement, and four-variable terminal formulas use no actual
middle projection link. All original physical square frames remain
independent.

Allowing \(g=g_0\) introduces no equality gap. The strict horizontal
distance below 1/2 gives the needed strict disk/inset clearance, and the
subsequent comparisons have their original positive rational reserves.
The accepted certificate
`9dd295e9755acfa9087736752fd8d33d4b1c52604fcfd41a43952bb56a0639f9`
and both of its accepted exact replay implementations therefore apply
without changed table bytes. The conclusion is the original high-floor
singleton theorem throughout this narrow-inset range, with either an
actual or a weak middle link.
