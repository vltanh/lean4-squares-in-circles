# A central right cone endpoint is high when its middle square has the coupled floor

November 2, 2026. Complete physical theorem and exact finite table.
All 7,035 direct interval leaves passed independent exact Fraction replay;
an independent agent reviewed the physical reduction and evaluator.
Numerical discovery is not a proof premise. No Lean or CI is used.

Put `Q=1105/256`, `l=29/60`, `rho=91/60`, `A=503/480`,
`B=937/480`, and `c=221/600`.

## 1. Original-square statement

Retain an actual horizontal four-chain whose consecutive center
comparisons are also horizontal cone comparisons, together with an
original outsider cone three-chain `L <c P <c R`. Every square has its
own original frame, all original pairs have disjoint open interiors,
and all original corners lie in the closed centered Q-disk. Suppose R
is central and

`yP-hP >= 1/10+13/4960 = 509/4960`.

Then `yR>3/5`.

The statement uses no actual projection edge of the selected triple and
no assumption about the two remaining outsiders. Its horizontally
reflected counterpart treats a central left endpoint.

The horizontal part of the accepted common cone-three routing makes P
central. Its stated floor makes its center higher than `3/5`. If it were
below both inner mains, its own-half-plane physical clearance would put
that inner main above `3/5+59/60=19/12>139/120`, contradicting the main
height bound. Thus P is already the upper routed member in the stated
coordinate frame. The accepted common cone-three routing gives

`-13/12 < xL < -11/12`, `-23/60 < xP < 0`,
`19/60 < xR <= l`, and `yL>27/40`.

R is above its corresponding right inner main. The accepted central
physical clearance and the actual-cone-four main lower bound imply
`yR>-139/120+59/60=-7/40`. These statements concern original squares,
not asserted projection separators. In proving the theorem, assume
`yR<=3/5`; all the resulting closed bounds will be included in the table.

## 2. A lower height for the left endpoint of the selected triple

Reflect horizontally to write the original L center as `(Z,Y)` with
`11/12<=Z<=13/12`. The original outer endpoint contains the fixed
rectangle `[A,B] x [-c,c]`. Write L's folded original side components as
`a>=b>=0`, `a^2+b^2=1`, `h=(a+b)/2`, and `t=b/a`.

Coordinate horizontal separation is impossible: `Z+h>A` and `Z-h<B`.
Also `Y>=27/40>c`, so downward vertical separation is impossible.
For an original L-owned normal, a nonpositive vertical component cannot
separate: its horizontal advantage over the nearest rectangle boundary
is at most `A-Z<=21/160<1/2`, while its downward vertical contribution
is nonpositive. The original square's support on its own axis is one
half.

For a normal with positive vertical component, either horizontal sign
gives a necessary clearance no stronger than the one using the rectangle
corner `(A,c)`: `Z<13/12<(A+B)/2` makes the opposite boundary farther
away. Thus all possible separators imply one of

`Y >= c+h`,
`Y >= c+1/(2a)+t(Z-A)`,
`Y >= c+1/(2b)+(Z-A)/t` (when `b>0`).

The last quotient is no smaller than the second. Their difference has
the sign of

`(a-b) {1/2+(Z-A)(a+b)}`,

and the expression in braces is at least
`1/2-(21/160)(17/12)=201/640>0`.
The aligned case is included by the coordinate alternative. Consequently
the complete original-pair lower bound is

`Y >= ell(t,Z) := max(27/40, c+min(h,1/(2a)+t(Z-A)))`.

This argument uses the contained endpoint rectangle only as a necessary
physical nonoverlap constraint; it never treats a chosen rectangle
separator as an actual edge of L.

## 3. Three original frames and all their corner caps

For each j in `{L,P,R}`, use a folded slope `tj in [0,1]` and a
chirality `sj in {-1,1}`. Put

`dj=sqrt(1+tj^2)`, `aj=1/dj`, `bj=tj/dj`,
`hj=(aj+bj)/2`, `kj=(aj-bj)/2`.

The original side directions are `(aj,sj*bj)` and `(-sj*bj,aj)`.
The four corner offsets are

`(hj,-sj*kj)`, `(sj*kj,hj)`, `(-hj,sj*kj)`, `(-sj*kj,-hj)`.

For a center with horizontal coordinate v, define its necessary upper
height cap by the minimum of `rho` and, for all four listed offsets
`(dx,dy)`, the four values

`sqrt(Q-(v+dx)^2)-dy`.

Call this function `Uj(v,sj)`. All radicals have positive arguments
over the complete root box below. In particular, the global folded
bounds `1/2<=hj<=17/24` and `0<=kj<=1/2` imply
`|v+dx|<=13/12+17/24<sqrt(Q)`.

The original left center has coordinate `-Z`. Horizontal reflection
therefore gives its upper bound as `UL(Z,-sL)`, preserving its actual
frame. Write the six height bounds as

`Llo=ell(tL,Z)`, `Lhi=UL(Z,-sL)`,
`Plo=hP+509/4960`, `Phi=UP(xP,sP)`,
`Rlo=-7/40`, `Rhi=min(3/5,UR(xR,sR))`.

The same `sP,tP` occur in both original short-chain pair constraints.

## 4. Complete physical pair inequalities under a cone comparison

For a selected pair i before j, let `D=xj-xi>0` and `V=yj-yi`.
Its cone comparison says `|V|<=D`. The common support sum on any
side normal owned by either original unit is

`sigma(i,j) = [1 + |ai*aj+si*sj*bi*bj| + |si*bi*aj-sj*ai*bj|]/2`.

Every genuine separating normal may be replaced, if necessary, by one
of the following four positive-horizontal normals with at least as
large a projection onto `(D,V)`:

`(ai,si*bi)`, `(bi,-si*ai)`, `(aj,sj*bj)`, `(bj,-sj*aj)`.

For completeness, the negative of a near-horizontal normal has projection
at most `(-a+b)D<=0`. If the negative of the other normal has positive
projection, it equals `-bD+s*aV` with `sV>=0`; the near-horizontal
positive normal has larger projection because their difference is
`(a+b)D-(a-b)sV>=2bD>=0`. This also includes `b=0` and `a=b`.
The support sum is unchanged under this choice of owner axis.

The cone comparison and the original contained aligned insets also give

`D>=gi+gj`, where `gj=1/(4hj)`.

No original-square projection edge or separator owner is prescribed.

## 5. Elimination of the three vertical center variables

Let `DL=xP+Z` and `DR=xR-xP`. For the left pair define

`eLlo=max(-DL,Plo-Lhi)`, `eLhi=min(DL,Phi-Llo)`.

For the right pair define

`eRlo=max(-DR,Rlo-Phi)`, `eRhi=min(DR,Rhi-Plo)`.

The actual signed vertical gap belongs to its corresponding interval.
Thus each interval must be nonempty. For any normal `(nx,ny)` in
Section 4, its projection over the whole interval is at most

`nx*D + ny*(ehi if ny>=0, elo otherwise)`.

Define `pair(i,j)` as the minimum of `ehi-elo` and the maximum of
these four projection upper bounds minus the common support sum.
For the left and right physical pairs, respectively, set

`Left = min(Lhi-Llo, DL+Phi-Llo, DL+Lhi-Plo, pair(L,P))`,
`Right = min(Rhi-Rlo, DR+Phi-Rlo, DR+Rhi-Plo, pair(P,R))`.

All four arguments are nonnegative in a physical configuration. Allow
the two possible original L chiralities in `Left`, and the two possible
original R chiralities in `Right`, by taking their maxima. For a fixed
original P chirality set

`C(sP)=min(Phi-Plo, max_sL Left, max_sR Right)`.

Finally define the necessary scalar function

`F=min(DL-gL-gP, DR-gP-gR, max_{sP=-1,1} C(sP))`.

Every original counterexample to Section 1 satisfies `F>=0`. This
allows more choices of vertical centers than an original configuration,
so it is a necessary relaxation. The shared original P frame is retained
throughout; there is no independent left-pair/right-pair chirality choice
for P.

## 6. Complete independently replayed table

The exact closed root box, in the order `(tL,tP,tR,Z,xP,xR)`, is

`[0,1]^3 x [11/12,13/12] x [-23/60,0] x [19/60,29/60]`.

`230_middle_low_right_complete_cover.json.gz` is a complete midpoint
binary cover of this box, with 14,069 nodes and 7,035 strict direct
interval leaves, maximum depth 25. Every leaf has a strictly negative
direct rational interval upper bound for F. Every internal node contains
both children, including their common midpoint face. There are no pending
boxes or omitted frames, chiralities, coordinate endpoints, or contacts.

The independently written `verify_230_middle_low_right.py` reconstructs
the entire tree from the root and uses exact Fraction arithmetic with
outward 80-bit square-root bounds. It computes the relative-frame support
both from the unnormalized dot product and determinant and from the
equivalent normalized component formula. Taking the larger of these two
interval lower bounds and the universal bound one remains a valid support
lower bound. On `[0,1]`, `a,k` decrease and `b,h` increase, so their exact
endpoint radical bounds enclose each complete frame interval. The verifier
imports no producer, producer evaluator, derivative code, or dyadic
interval kernel, and accepts direct interval leaves only.

The final tree was discovered by an untrusted floating interval producer.
Every leaf was then recomputed by the separate exact verifier. The saved
report `230_middle_low_right_fraction_replay.json` records PASS and the
strictly negative largest interval upper bound

`-2990601586744534481772519411449998663815163525673147172773661666853661`
`/39224967236998201060627914125212551607494070578726971109877473141924104400`.

The certificate SHA-256 is
`2a170b17eea5b2325941f293ad4f4e3b71b50645728d6a2e7b1350a23ed56320`.
Four damaged controls were rejected: a changed root boundary, a missing
child, an unknown rule, and a false whole-root exclusion. The independent
physical review is `CENTRAL_RIGHT_CONE_ENDPOINT_PHYSICAL_REDUCTION_AUDIT.md`.
The complete table contradicts the necessary inequality `F>=0` and
therefore proves the theorem in Section 1.

## 7. Complete remaining middle-main occupancy caller

In the remaining `(L,C,R)=(2,3,0)` middle-main alternative, the selected
right endpoint is central and the left main is at its middle marker.
The coupled cone inset-loss theorem gives P the precise floor required
in Section 1. This theorem therefore makes the selected R a high
right shoulder. The common routing already makes selected L a high left
shoulder. Together with original P and the two original outer endpoints,
the accepted widened five-square cap then gives `D<=2`, contradicting
the normalized strict-counterexample span `D>2`.

When the full-side main is bottom, a low selected central R already
contradicts a lower central outsider by the two-low-mains theorem:
`|xR-x2|<1/5<g2` gives `yR-y2>=g2+1/2>61/62`, hence
`y2<3/5-61/62=-119/310`. This uses the original half-unit disk of R
and does not require R to occupy a side column.
