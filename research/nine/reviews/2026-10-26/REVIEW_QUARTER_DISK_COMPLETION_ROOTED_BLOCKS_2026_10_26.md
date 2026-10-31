# Full independent review: weak quarter-distance arcs and nine-unit obstruction

Date: October 26, 2026.

Reviewer: rooted-blocks agent, independently of the author and root review.

**Verdict: ACCEPT the complete weak-distance arc-measure theorem and the
complete nine-square quarter-disk obstruction. No correction is required.**

Source: `CHORDED_HEXAGON_QUARTER_DISK_COMPLETION_OBSTRUCTION.md`.
SHA-256 of the complete source read:

    1cbdbfea6a19153074850222d7beb8ae48f9b35fbd215dae9998d9542ad25d59

The source does not prove the missing five-boundary-neighbor margin and
does not claim to exclude the entire exterior fan. This review preserves
that exact limitation.

## 1. Full-source and prerequisite audit

I read the entire new source and the full accepted
`GENERAL_SIDE_CHANNEL_CAP_INNER_ARC.md`. For the stated fan consequence
I also read the complete
`CHORDED_HEXAGON_CENTRAL_CAPACITY_ONE.md`,
`SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md`,
`SIMPLE_CYCLE_CHANNEL_POCKET_CAPS.md`, and
`CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md`.

The geometric arc argument only needs containment in D_(sqrt(Q)) and
the stated distance from O. Although its accepted predecessor was
phrased with a separating half-plane at height greater than 1/4, its
own-axis proof uses precisely the nearest-point distance. The weak
version in the new source therefore has the declared force-free scope.
No stress, load, degree or common-frame premise is imported.

## 2. All arc-measure cases, including equality

Use the actual square's own axes, with center coordinates ordered and
signed so that

    E=[A,a] x [B,b], a=A+1, b=B+1,
    a>=b>=1/2, a^2+b^2<=Q.

These conventions include every physical orientation and are not a
rotation of an individual unit inside the packing.

If a>5/4, then A>1/4 already. The accepted inner-face proof applies
unchanged. Its two possible angular endpoint differences have strict
reserves depending on Q and the own-axis inequalities, independently
of whether dist(O,E)=1/4 or is larger. In fact equality in the latter
distance is impossible in this particular branch, but no extra use
of strict distance is needed.

If a<=5/4 and B>0, then 0<B<=A<=1/4 and k^2=A^2+B^2>=1/16.
The four-candidate interval proof remains valid. I independently
checked the derivative sign used for the only delicate outer-outer
candidate. For fixed k and B=sqrt(k^2-A^2), its two positive
derivative terms can be squared without changing their comparison.
The resulting numerator is

    (A-B)[2k^2+2AB+(A+B)(k^2-9/16)]
      =(A-B)[(A+B-1/4)^2+(k^2-1/16)(A+B+1)].

It is nonnegative also at k=1/4. Continuity includes an endpoint
where A or B is 1/4 and an individual derivative is infinite. The
equal-coordinate lower bound is monotone in k, so its weak comparison
at k=1/4 is valid. The final comparison remains strict, with squared
reserve (16-9sqrt(2))/100>0; its positivity follows from 256>162.
The other candidates keep their strict strip or inner-face bounds.

The remaining branch B<=0 is the genuine new equality case. The
nearest distance is max(A,0), and a<=5/4 forces exactly

    A=1/4, a=5/4, -1/2<=B<=0, 1/2<=b<=1.

All circle points in E have positive x, and the two transverse
inequalities give the single angular interval

    asin(B/(5/4)) < theta < asin(b/(5/4)).

Throughout its closure x>=sqrt(25/16-1)=3/4>1/4. The only additional
restriction for the open square is x<5/4. It removes theta=0 if that
point is in the interval, and removes no interval of positive measure.
At B=0 it is already an endpoint. Thus the total angular measure is
exactly the source's difference of arcsines, even when the open
intersection has two components.

On b in [1/2,1], that difference is nondecreasing because
b>=|b-1| and the derivative of asin increases with the magnitude of
its argument. Its minimum is 2asin(2/5)>pi/4. The strict elementary
comparison is equivalent to sqrt(2)>34/25, whose squared reserve is
94/625>0. Consequently every equality alternative still contributes
strictly more than pi/4 of total open-interior angular measure.

The source correctly does not claim connectedness or membership of
the radial center point in this weak case. Neither is needed in the
later summation.

## 3. All eight physical completion units are counted

If H contains the closed D_(1/4), the open disk is an open subset of
H and therefore lies in int H. Every other physical square E must
avoid that open disk even on its own boundary. Otherwise any small
neighborhood of a boundary point of E in int H would meet int E,
contradicting the original disjoint open interiors.

Hence all eight other squares satisfy dist(O,E)>=1/4. Their
open-interior intersections with the same radius-5/4 circle are
pairwise disjoint measurable open subsets of that circle. The new
lemma assigns each total angular measure greater than pi/4, so their
sum exceeds 2pi. This is impossible regardless of whether an
individual intersection is one arc or two and regardless of whether
the eight units have positive stress or touch the containing circle.

The own-frame reformulation is exact. For a unit centered at (x,y),
all four side inequalities contain D_(1/4) precisely when
|x|<=1/4 and |y|<=1/4. Therefore every actual unit in any such
nine-square packing has max(|x|,|y|)>1/4 in its actual own frame.
The weak endpoint is essential to the strict final conclusion, and
is supplied by Section 1 rather than assumed.

## 4. Fan application and the retained open premise

The full exterior-fan graph has the true degree-five clear hub and
the unique load set 12345, as proved in the complete graph/load
cover. All its four bounded faces are triangles; the accepted
central-capacity theorem gives zero capacity for their entire free
union, including weak junctions and all additional zero-weight
contacts. The degree-free exterior touching-boundary-pair theorem
empties each of the direct path-pair pockets. Thus the three
physical completion units, if present, are exterior in the remaining
hub pocket, with every chord and hub force retained.

The new quarter-disk obstruction is an independent necessary
condition for that full fan. A proof that its actual hub satisfies
the two quarter-margin inequalities would contradict it. The source
explicitly leaves this five-neighbor geometric/force premise open;
neither the pocket assignment nor the arc lemma supplies that
premise. No sampled star or relaxed center arrangement is used to
assert it. No whole fan graph/load orbit or coarse label is closed
by this source alone.

## 5. Verification boundary

All physical squares and weak contact endpoints are retained. The
proof does not require an orientation shared by different bodies,
replace original application means, delete chord forces, call a
higher-degree hub a transmitter, or perform a stress selection.
This review involved full mathematical reads and exact comparisons;
no Lean compilation, CI, remote action, or shared-ledger change was
performed.
