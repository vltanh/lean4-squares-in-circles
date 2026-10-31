# The whole aligned-tip obstacle excludes every additional boundary root neighbor, and every parallel intact petal

Date: October 31, 2026.

**Status: complete proposed hand theorem, frozen for a full independent
noncontributor review.** The force-free kernel below is self-contained.
Its original parallel-petal classification input has received a complete
clean independent gate, unchanged. This new theorem is not adopted until
its separate full review passes.

The new whole-obstacle construction is by physical_two_continue. Root
independently reconstructed the hand argument as a collaborator and
supplied no mathematical repair. The preceding large-support and complete
parallel-tip classification has its explicitly credited root/physical
construction; it is a separate fully gated operative input.
A new full noncontributor review of this entire source is required.

## 1. Standalone force-free theorem

Put Q=1105/256. Suppose four distinct actual closed unit squares H,B,C,E,
with independently oriented frames and pairwise disjoint open interiors,
are contained in the same disk centered at O of radius

    41/20 < R <= sqrt(Q).

Set u=sqrt(R^2-1), s=u-1. Assume only the following literal shapes of the
three original obstacle units, in one orthonormal frame about O:

    H=[-s,1-s] x [-b,a],       a+b=1, 0<a,b<=1/u,
    B=[-u,-s] x [0,1],
    C=[-u,-s] x [-1,0].                                (1)

No force, load, positive graph, vertex degree, original mean, or normal
selection is a hypothesis of this kernel. The arbitrary fourth unit E
may have any actual orientation and any closed support feature. Physical
circle contact, with or without positive stress, is the relevant property.

**Whole-obstacle theorem.** If E physically touches the containing circle,
then E does not physically touch H. Equivalently, among all additional
actual units in this disk, every physical neighbor of H is physically
circle-clear. The specified B,C are the only possible physical boundary
neighbors of H. The conclusion covers contact at every side interior,
every root corner, all shared contact intervals, and the B-C-H junction.

The theorem is conditional on the exact actual shapes (1); it does not
assert a general count for an arbitrary root or for a prescribed drawing.
It is not a statement that H has no physically clear neighbor.

## 2. Exact whole-window bounds

From the lower radius and u^2=R^2-1,

    u^2>1281/400>(16/9)^2,

where the last difference is 1361/32400. From the upper radius,

    u^2<=849/256<(73/40)^2,

where the last difference is 91/6400. Hence

    16/9<u<73/40<2,
    s<33/40,
    0<1-s=2-u<1/4,
    7/16<a,b<9/16<4/7.                                (2)

For the lower bounds on a,b, use a+b=1 and the two upper bounds
a,b<=1/u<9/16. In particular both obstacle tips extend strictly
beyond H's top and bottom ordinates, since a,b<1.

Let r=R-sqrt(2). The fixed radical estimates sqrt(2)<17/12 and
1/sqrt(2)<71/100 give

    r>19/30,
    R-1/sqrt(2)>67/50.                                 (3)

Every point p of a physical boundary unit satisfies |p|>=r, by its
actual diameter sqrt(2) and an actual radius-R corner. Every physical
boundary unit center c_E satisfies

    |c_E|>=R-1/sqrt(2)>67/50.                            (4)

These two statements hold for every physical circle corner, including
zero-coefficient corners; they require no circle-force equation.

## 3. The complete opposite side is too close to O

Every point p on the opposite closed H side x=1-s has

    |p_x|<1/4,       |p_y|<=max(a,b)<4/7,

so

    |p|^2<1/16+16/49=305/784<361/900<r^2.               (5)

The middle positive gap is 2131/176400. A physical boundary E cannot
contain any such p. Thus the entire opposite side, with both corners
and all possible contact means, is excluded before any orientation
classification of E.

## 4. Every remaining contact is an actual upper or lower support

Suppose E touches H, and choose any actual point p in their closed
intersection. By Section 3 it is not on the opposite side.

At a relative-interior point of H's west side with p_y>0, actual H
occupies the nearby right half-neighborhood and actual B occupies the
nearby left half-neighborhood. For p_y<0 use C instead. At p_y=0,
B and C together occupy the nearby left half-neighborhood, while H
occupies the right one. A distinct full unit E cannot have an interior
point in this neighborhood without overlapping one of those interiors.

This local observation is valid even when p is an E vertex. If z is
an interior point of E, then (1-t)p+t z is in int E for every 0<t<1.
An open interior point can be chosen off the finitely many obstacle
boundary lines. For small t it would lie in one of the occupied open
half-neighborhoods. Thus there is no additional unit at any west-side
relative-interior point, including the exact triple junction p_y=0.

At the northwest root corner p=(-s,a), actual B occupies all nearby
points to the west, on both sides of height a, because 0<a<1. Actual
H occupies the southeast quadrant. Therefore the only locally available
sector is the closed northeast quadrant. The same segment-to-interior
argument proves that the entire convex E is in

    x>=-s,                 y>=a.                         (6)

In particular it has a genuine geometric minimum-y support at p.
This is not a newly chosen certificate normal. The southwest corner
has the reflected conclusion y<=-b using actual C.

At a relative-interior point of the top H side, H occupies the local
lower half-neighborhood. Convexity and the same argument force E wholly
into y>=a. The bottom side similarly forces E into y<=-b.

The entire contact cover is consequently: E is above H with an actual
minimum-y point p=(x,a), or it is below H with the reflected support.
The northeast and southeast corners were already excluded by (5).
No side endpoint, coincident corner, or weak contact junction is lost.

It remains to exclude the entire upper alternative; the lower one is
its reflection interchanging a,b and B,C.

## 5. Every physical upper contact lies strictly left of -1/4

Let E be a physical boundary unit wholly in y>=a, with its actual
minimum-y point p=(x,a) on the top H segment. Since

    -s<=x<=1-s<1/4,

the possibility x>=-1/4 would imply

    |p|^2<1/16+16/49=305/784<r^2,

using a<4/7. This contradicts p belonging to that physical boundary
unit. Therefore

    x<-1/4.                                             (7)

This comparison applies to every chosen point of a shared top contact,
including its endpoints. It is only a necessary physical condition; no
port is moved to the displayed strict boundary.

## 6. Entire aligned E, with every actual contact mean

If E's minimum-y support is a side, the actual unit is aligned and has
the form

    E=[ell,ell+1] x [a,a+1],             ell<=x<=ell+1.

The vertical interiors of E and B overlap on the nonempty interval
(a,1). Hence their horizontal open intervals must be disjoint:

    ell>=-s,                  or ell+1<=-u.

The latter is impossible, since the actual contact x>=-s>-u belongs
to [ell,ell+1]. Thus ell>=-s. Its center obeys

    (c_E)_x=ell+1/2>=-s+1/2>-13/40>-49/120,
    (c_E)_x<=x+1/2<1/4,
    0<(c_E)_y=a+1/2<9/16+71/100=509/400.                (8)

The original point x remains arbitrary in its whole closed side.
In particular neither a midpoint nor a mean endpoint has been imposed.

## 7. Entire strict minimum-y vertex E and the actual occupied tip

Otherwise p is E's unique minimum-y vertex. Its complete actual shape
has the form

    E=p+[0,1](c,d)+[0,1](-d,c),
    c,d>0,                  c^2+d^2=1.                  (9)

There is no ordering assumed between c and d. These are the entire
two strict orientation signs relative to the horizontal axis. The
aligned endpoints are already included by Section 6.

Consider the actual left-going edge p+t(-d,c). Whenever

    0<t<min(1,b/c),

its ordinate lies strictly between a and 1. Its abscissa is strictly
above -u, since x>=-s and t d<1. If this abscissa were below -s,
that actual point of E would lie in int B. Approximating the point
from int E would give open overlap, a contradiction. Thus

    x+s>=t d

for the whole displayed interval. Taking its endpoint limit gives the
closed necessary barrier

    x+s>=d min(1,b/c).                                  (10)

The equality c=b, a contact at B's upper-right corner, and an edge
endpoint at x=-s all remain. No displacement of E or B was made.
Only a necessary consequence of their actual nonoverlap is used.

The actual center is

    (c_E)_x=x+(c-d)/2,
    (c_E)_y=a+(c+d)/2.

Equation (10) yields

    (c_E)_x>=-s+F,
    F=d min(1,b/c)+(c-d)/2.                             (11)

We next bound this expression over its entire orientation domain.

## 8. One whole orientation inequality for the occupied-tip barrier

For every c,d>0 with c^2+d^2=1 and every b>7/16,

    F=d min(1,b/c)+(c-d)/2>5/12.                         (12)

If c<=b, then F=(c+d)/2>1/2. This includes c=b.
Otherwise c>b. Put t=d/c>0, so c=1/sqrt(1+t^2), and write

    F=bt+(1-t)/(2sqrt(1+t^2)).                          (13)

If t>=1, rearrange without changing a sign:

    F=b+(t-1)(b-c/2).

Here c<=1/sqrt(2), so b-c/2>7/16-1/(2sqrt(2))>0.
Consequently F>=b>7/16>5/12, with t=1 included.

For the whole remaining interval 0<=t<=1, the elementary inequality

    1/sqrt(1+t^2)>=1-t^2/2

has nonnegative sides. On squaring it follows from

    (1-t^2/2)^2(1+t^2)=1-t^4(3-t^2)/4<=1.

As 1-t>=0, (13) and b>7/16 give

    F>=1/2-t/16-t^2/4+t^3/4.

Subtracting 5/12 and multiplying by 48 gives the single cubic

    p(t)=4-3t-12t^2+12t^3.                              (14)

Its derivative is 36t^2-24t-3. The negative critical point lies
outside [0,1], and its unique positive critical point

    tau=(2+sqrt(7))/6

lies inside that interval and is its minimum. At that point direct
substitution, or the derivative equation, gives

    p(tau)=(19-7sqrt(7))/9>0,

because 19^2>49*7. Hence (14) is strictly positive on the whole closed
interval, including both endpoints. This proves (12) without any
sampled orientation, subdivision, approximate minimizer, or imposed
ordering of the original frame.

## 9. The whole center box contradicts every physical circle mask

For strict E, (2),(11),(12) give

    (c_E)_x>-33/40+5/12=-49/120.

Also (7) and c-d<=1 give

    (c_E)_x<=x+1/2<1/4.

Finally c+d<=sqrt(2) and a<9/16 give

    0<(c_E)_y<9/16+71/100=509/400.

Thus both the entire strict case and the entire aligned case (8)
obey exactly the same strict box:

    -49/120<(c_E)_x<1/4,
    0<(c_E)_y<509/400.                                 (15)

Since 49/120>1/4, this implies

    |c_E|^2<(49/120)^2+(509/400)^2
            <(67/50)^2.                               (16)

The exact positive reserve in the second comparison is

    (67/50)^2-(49/120)^2-(509/400)^2=2767/288000.

This contradicts the physical boundary-center lower bound (4).
Every actual upper boundary neighbor is impossible. Reflection gives
the complete lower alternative, with a,b interchanged and unchanged
radius and obstacle units. Sections 3--4 already covered the other
two sides and all four corners. The force-free whole-obstacle theorem
is proved for every original orientation and contact feature of E.

## 10. Literal entire parallel intact-petal caller

Keep the same original nine units and selected certificate as in the
parallel-petal input 3a778, at R^2<=Q. Its whole support/frame/mean
theorem proves for every actual parallel intact petal, without a bound
on the true root degree:

    R>41/20,   u=sqrt(R^2-1),   s=u-1,
    B=[-u,-s] x [0,1], C=[-u,-s] x [-1,0],
    H=[-s,1-s] x [-b,a],
    a+b=1, 0<a,b<=1/u.

These are precisely the unchanged actual shapes (1). The force-free
kernel therefore says that every other physical H-neighbor is
physically circle-clear. This conclusion includes an extra neighbor
whose circle contact has total coefficient zero. No graph assumption
was used in deriving it.

Now use the complete accepted 103a original-component normal form. An
intact root has exactly one additional cyclic block K. Its private
vertices keep all of their original positive pair forces and every
circle atom; all other physical units remain present. The original
private moment DAG and full source/sink equations supply two distinct
positively circle-loaded actual K-neighbors of H. Their true degrees
are arbitrary. They are different from the two intact tips.

Each of these actual neighbors physically touches H and the circle,
contradicting the force-free kernel. Consequently **the entire original
parallel intact-petal family is excluded**, at every root degree and
for every additional private graph, private load mask and permitted
genuine leaf. No outerplanarity, simplicity of the private block,
unloaded true2 equation at a higher-degree body, new normal selection,
or claim that a distant load touches H is used. The actual source/sink
neighbors are the ones supplied by the full 103a theorem.

This is a whole interface family, not a closure of the nonparallel
intact-root remainder or the global packing theorem. It changes no
original fine/coarse count. The standalone force-free obstacle result
can be used elsewhere only after its exact shapes and radius premises
have been established for the same actual units.

## 11. Complete operative boundary and review status

The complete frozen input manifest is
entire_parallel_petal_aligned_obstacle_input_manifest_2026_10_31.json.
It supplies the following five ENTIRE operative bodies, unchanged full
copies, byte/LF counts, exact current pins, and actual read records.

| Complete operative source or gate | Current SHA256 | Exact use |
| --- | --- | --- |
| WHOLE_INTACT_PETAL_SUPPORT_BOUND_AND_ENTIRE_PARALLEL_ROOT_CLEAR_NEIGHBOR_BY_COMPLETE_TIP_FRAME_AND_MEAN_COVER_2026_10_31.md | 3a778d5196fa0eb8faa939440472f052485e694fdbe4000396b9ac1f49c2dc88 | Entire actual parallel-petal frame, full original mean and whole radius cover, at arbitrary root degree |
| REVIEW_WHOLE_INTACT_PETAL_SUPPORT_AND_ENTIRE_PARALLEL_ROOT_CLEAR_NEIGHBOR_COMPLETE_NONCONTRIBUTOR_2026_10_31.md | 7bc9189fe1b5147885ffbd2a935e8a0156f469079b0221f44be5a627edbc78a4 | Complete independent hand gate of the preceding unchanged693-LF source, including all physical masks and original star/mean scope |
| GLOBAL_NEXT_INTACT_ROOT_UNLOADED_MOMENT_AND_BLOCK_REDUCTION.md | 103a0f4ceccba044c132a45c632bd64df57540feb70fd69d6159c52759e449c6 | Full original-component normal form and two distinct actual positively loaded root neighbors at arbitrary degrees |
| REVIEW_INTACT_ROOT_UNLOADED_MOMENT_AND_COMPONENT_ROOT_2026_10_27.md | 27b8e71cd4aebd35e0bfc6dfa6c17438bbd5fc758a00d9afd14e1ccf49245e79 | Complete root gate of103a, with full actual private stars and inherited common-selection prerequisites |
| REVIEW_INTACT_ROOT_UNLOADED_MOMENT_BLOCK_REDUCTION_C6_NEXT_2026_10_27.md | 4bde800a7d74b1af0f82bdf48b673abfcc672ba2968a0e530fc0b9ff0a3426f1 | Complete independent gate of103a and the literal all-nine scope |

All five complete bodies have been read in the continuing construction,
not only their cited formulas. The final432-LF 7bc gate and its entire
226-LF flat manifest were read after its full hand reconstruction. Its
one prefreeze reviewer-prose plus-sign correction is separately preserved
in that gate's packet; the source and its mathematics never changed.

No excerpt replaces a complete input. The eleven complete accepted
inputs of 3a778 remain preserved and pinned in that source's own base;
they are not newly re-audited recursively here. The same-nine analytic
lower-window replacement and the common physical-certificate scope are
exactly those reconciled in the entire 3a778/7bc pair. The proof does not
reactivate the older five-charge alternative in103a or claim any new
global selection theorem.

The new geometric kernel in Sections 1--9 imports no outside geometric
lemma: its support, local convexity, whole-edge barrier, polynomial
minimum and physical-circle comparisons are all reprinted. Section 10
alone imports the full accepted original chart and original-component
normal form. All original means and masks stay unchanged. The previous
classification's shared mean k in [0,1] remains in that complete input;
only its proved a,b<=1/u consequence is consumed here.

All new reasoning is by hand. Only metadata pin/copy/byte/LF checks are
permitted. No mathematical script, pose evaluation, parameter mesh,
optimizer, Lean/Lake/build, CI, normal reselection, force deletion,
GitHub write, Library mutation, or original ledger edit is part of this
construction. This entire source and all copied operative bytes remain
immutable after the communicated freeze. A new full clean noncontributor
gate is required before adopting the new obstacle theorem or its entire
original parallel-petal conclusion.
