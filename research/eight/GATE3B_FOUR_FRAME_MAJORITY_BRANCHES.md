# Gate 3B.1: four exhaustive frame-majority branches

2026-10-13. Continuation after Gate 3A, not a new parallel work queue.
This supplies an explicit first parent-to-children coverage theorem for
Gate 3B. The internal joint order/owner classifications remain OPEN.

## 1. At least five frames fit in a closed 45-degree window

A unit square's frame is a point on the orientation circle of circumference
pi/2, because a quarter-turn preserves the same square. For each square i,
let M_i count square frames in the clockwise CLOSED arc of length pi/4
beginning at its frame; count i itself and retain all multiplicities.

### Theorem 1 — majority-anchor lemma

For eight square frames, some M_i is at least five. One may choose i
maximizing M_i, rotate its frame to zero, and sort the other relative
frames in [0,pi/2). Exactly m of them then lie in [0,pi/4], for some

    m in {5,6,7,8}.

### Proof

Each label counts itself once. For each unordered pair of distinct labels,
at least one of their two clockwise directed differences on the orientation
circle is at most pi/4. Thus that pair contributes at least one to the
sum of all M_i. Coincident or antipodal frame points may contribute twice;
this only strengthens the estimate. Consequently

    sum_i M_i >= 8 + binomial(8,2) = 36.

If all eight counts were at most four their sum would be at most 32.
Therefore max_i M_i>=5. Rotating a maximizing frame to zero and sorting
is precisely the legitimate normalization already proved in Gate 1.
No centers, contacts, or disk constraints are altered. QED.

The same argument for N frames gives a closed-half-circle window containing
at least ceil((N+1)/2) labels. The n=8 conclusion is a direct counting
lemma, not a numerical clustering assumption.

## 2. Four covering branches in the exact rational chart

Use the majority anchor in the Gate 1 chart. Let L be labels 1,...,m,
whose relative angles lie in [0,pi/4], and H the remaining 8-m labels,
whose angles lie in (pi/4,pi/2). Denote these branches by M5, M6, M7, M8.

The cutoff needs no approximate angle or transcendental constant. For
z=tan(theta/2), the condition theta<=pi/4 is exactly

    g(z):=1-2z-z^2 >= 0.

It follows from cos(theta)-sin(theta)=g(z)/(1+z^2).

Every packing has a normalized representative in at least one of the
four branches. For closed polynomial covering regions, permit

    g(z_i)>=0 on L,      g(z_i)<=0 on H.

These closed regions overlap at theta=pi/4. Such overlap is intentional;
it avoids losing boundary configurations. When an argument needs the
chosen anchor to have MAXIMUM window count, retain that additional
condition explicitly. The weak polynomial chamber inequalities alone
do not imply maximality or an exclusive exact count.

This distinction prevents a later classifier from silently treating a
closed relaxation as a disjoint partition.

## 3. Canonical owner orders can be chosen coherently within each group

Use the four projection vectors from Gate 3A:

    u_0=(12,5), u_1=(5,12), u_2=(-5,12), u_3=(-12,5).

The pairs (u_0,u_2) and (u_1,u_3) are orthogonal; every vector has norm 13.
For a canonical owner, octant-boundary membership was allowed to choose
either adjacent octant. Make that choice consistently with its OWNER
square's frame group as follows:

| Owner frame group | Positive e-axis octant | Positive f-axis octant |
|---|---:|---:|
| L: 0<=theta<=pi/4 | 0 | 2 |
| H: pi/4<=theta<=pi/2 | 1 | 3 |

Negative axes use the corresponding opposite octant and reverse the
edge arrow. These memberships hold on the closed intervals as written,
including theta=0, pi/4, pi/2. They do not change the canonical normal or
its true separator inequality; only an allowed octant label is selected.

### Theorem 2 — full pair-family ownership restriction

Every packing in branch Mm admits canonical owners whose four projected
order graphs satisfy:

* An L-L pair is assigned to order 0 or 2.
* An H-H pair is assigned to order 1 or 3.
* An L-H pair may be assigned to any of the four orders.

Every selected edge still has projection gap at least 7w_ij>=7.
All four graphs are jointly realized by the same centers, are acyclic,
and have no six-edge path in the research radius window.

### Proof

A true SAT owner is an axis of one of its two incident squares. If both
squares are in L, either possible owner's e/f axes have precisely the
allowed L octants in the table; hence the pair uses only orders 0 or 2.
The H-H argument is identical. Mixed pairs may use either endpoint's
owner, so all four orders remain possible. At an angular or octant tie,
the coherent table chooses one of the memberships already covered by
Gate 3A's non-strict theorem. No maximizer tie is discarded. QED.

## 4. The actual branch ledger now available

| Branch | L labels | H labels | Pairs restricted to orders 0/2 | Pairs restricted to orders 1/3 | Mixed pairs |
|---|---:|---:|---:|---:|---:|
| M5 | 5 | 3 | 10 | 3 | 15 |
| M6 | 6 | 2 | 15 | 1 | 12 |
| M7 | 7 | 1 | 21 | 0 | 7 |
| M8 | 8 | 0 | 28 | 0 | 0 |

Each row accounts for all 28 true square pairs. The table is exhaustive
at the **macrobranch** level, but the projected orders, actual owners,
centers, and seven relative angles still vary within each row.
Four rows do not mean four already-solved or small finite cases.

In particular M8 reduces all 28 pair classes to two orthogonal projected
orders; it is not an axis-parallel-square assumption. The individual
square angles may range independently across the entire 45-degree window.

The known sharp construction has its frames in one such window, so it
is admitted by M8. The universal coverage proof, rather than a numerical
picture, protects it. No M5--M8 branch is excluded by this note.

## 5. Precise next gate and execution order

**Gate 3B.1 passes:** the initial global domain has an explicit four-child
cover, with polynomial angular conditions and attached canonical-owner
class restrictions.

**Gate 3B.2 is ACTIVE:** begin with M5. Classify its JOINT two-order L
subsystem, two-order H subsystem, and 15 mixed pairs using the actual
canonical/SAT constraints and the radius ceiling. A valid outcome is a
proved structural exclusion or an explicit further survivor decomposition,
with a parent-to-children coverage proof. Then proceed to M6, M7, and M8.

Do not drop the shared two-dimensional realization of all projections.
Do not infer actual square feasibility from the projection relaxation.
Do not import strict Slater for homogeneous canonical comparisons without
handling their affine hull. Do not assume maximal-window conditions from
the closed chamber inequalities alone.

The final usable owner-family list, Gate 3C exhaustiveness audit, Gate 4
sharp inequalities, unrestricted optimality, and equality remain open.

## 6. Exact arithmetic regression

`verify_frame_majority_cover.py` was run locally on 503 exact eight-frame
inputs, including coincident frames and exact 45-degree direction ties.
It checks sum_i M_i>=36 and max_i M_i>=5. All four maxima 5,6,7,8 occur in
the regression inputs. Both the existing rational n=8 packing and its
strictly separated eight-distinct-frame perturbation have maximum eight
and remain admitted. These finite tests audit angular conventions; the
complete majority theorem is the pair-counting proof above.
