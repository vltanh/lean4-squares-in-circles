# Two outer centers in every three-square cap of offset at least 7/50

**Theorem (arbitrary frames, contact-free).**
Let three unit squares with pairwise disjoint open interiors
lie wholly in the same cap

    D_R intersect {x>=h},     R<=99/50, h>=7/50.

Then **at least two distinct square centers have Euclidean
norm strictly greater than one**. The two squares may be
selected as the highest and lowest actual vertical-slice
chords at the exact midpoint of the containing horizontal
strip [h,R]. The conclusion is independent of every
square frame and requires neither touching pairs
nor equality of any disk-contact constraint.

This improves the **one-outer-center** result of
HUMAN_SINGLE_SIDE_OUTER_K_PRUNING.md, section 1,
throughout the substantial positive-offset range
h>=7/50. It does not assert either extreme square
is wholly in a positive/negative origin quadrant:
that stronger assertion was proved in
HUMAN_TRIPLE_CAP_ORTHOGONAL_WITNESSES.md only
at h>=13/60.

## 1. One common slice, and the geometry of each chord

Let

    X=(R+h)/2,     m=(R-h)/2,     B=sqrt(R^2-X^2).

At the specified ceiling and minimum offset,

    m <= (99/50-7/50)/2=23/25,                     (1)

and

    B<42/25.                                        (2)

For (2), the expression
B^2=[3R^2-2Rh-h^2]/4 increases with R and
decreases with h for 0<=h<R. At R=99/50,
h=7/50 it equals

    (99/50)^2-(53/50)^2
       =6992/2500 <7056/2500=(42/25)^2.

For one of the three unit squares choose its
unsigned side-frame angle theta in [0,pi/4].
Put c=cos(theta),s=sin(theta),L=c+s,D=c-s.
Its horizontal full width is L in [1,sqrt(2)],
and c*s=(L^2-1)/2.

The square's horizontal projection is an interval
of length L contained in [h,R]. Consequently the
midpoint X lies at least L-m from either end of
that projection. This quantity is positive,
because L>=1>23/25. The vertical line x=X
therefore crosses the **open square interior**.

Let ell denote its actual vertical chord length
inside this square. Direct intersection with
the four edges gives the exact formulas

    ell=1/c,                          if |delta|<=D/2,
    ell=(L/2-|delta|)/(c*s),         otherwise,    (3)

where delta is the difference between X and the
square-center x coordinate. The second formula
holds for s>0; the axis-aligned case has ell=1.
The horizontal-projection estimate gives, in
the sloping chord case,

    ell>=(L-m)/(c*s).                               (4)

## 2. The hand-proved uniform chord reserve ell>987/1000

For an axis-parallel square ell=1>987/1000.
For s>0 and a plateau chord,
ell=1/c>=1>987/1000.
For a sloping chord, it suffices by (1),(4)
to prove

    L-(987/1000)*c*s >23/25
                 for 1<=L<=sqrt(2).              (5)

The expression on the left is the strictly
concave quadratic

    g(L)=L-(987/2000)*(L^2-1).

Its minimum on [1,sqrt(2)] occurs at an
endpoint. At L=1 we have g(1)=1.
At L=sqrt(2),

    g(sqrt(2))=sqrt(2)-987/2000
      >707/500-987/2000
      =1841/2000>1840/2000=23/25.                (6)

The rational comparison sqrt(2)>707/500 follows
by squaring: 2*500^2=500000>707^2=499849.
This proves (5), hence

    **ell>987/1000**                               (7)

for each of the three squares, over every
continuous orientation and position in the cap.

## 3. The highest and lowest square centers lie outside the unit circle

The three open vertical chord intervals at X are
pairwise disjoint, since their squares' open
interiors are disjoint. Order them bottom-to-top.
Let S_top be the square of the topmost chord and
L_top its horizontal/vertical projection width.

Its chord begins at ordinate y0 satisfying

    y0>=-B+ell_bottom+ell_middle.                 (8)

A square's entire vertical projection has
length L_top and contains its chord of length
ell_top. Consequently its true minimum
ordinate is at least y0-(L_top-ell_top).
Its center therefore satisfies

    p_top.y >=y0+ell_top-L_top/2
       >-42/25+3*(987/1000)-L_top/2
       =1281/1000-L_top/2.                          (9)

Cap containment also gives

    p_top.x>=h+L_top/2
           >=7/50+L_top/2.                          (10)

Both right sides are positive, because
L_top<=sqrt(2)<3/2 and
1281/1000-3/4>0.

Adding (9)--(10) cancels the unknown frame width:

    p_top.x+p_top.y>7/50+1281/1000
                   =1421/1000 >sqrt(2),          (11)

the last inequality being the integer comparison

    1421^2=2019241>2000000.

By Cauchy--Schwarz,

    |p_top|^2 >=(p_top.x+p_top.y)^2/2>1.           (12)

For the bottommost chord, the reflected
argument gives

    p_bottom.x-p_bottom.y>1421/1000,

and hence |p_bottom|^2>1. These are two
**different square labels** because their
chords occupy different intervals. This
proves the theorem. QED.

## 4. New eliminations of outer-center macro-cases

Write k for the number of packed square centers
whose norm is at least one. Every cap population
triple has **at least one** outer center for any
nonnegative offset by
HUMAN_SINGLE_SIDE_OUTER_K_PRUNING.md, section 1.
The new theorem upgrades that to **two** whenever
the triple offset reaches 7/50. Crucially,
in the *all-single-side* branches the different
signed cap populations comprise **different**
square labels, so their outer-center counts add.

**S1: (3+0,3+1).** There are two distinct
perpendicular triple caps and one far-side
singleton on the 3+1 axis, which is outer
because its offset is >17/24>1/2.
If *both* triple offsets are at least 7/50,
then the two triples give 2+2 outer centers
and the singleton adds one:

    S1, both triple offsets >=7/50 => k>=5.      (13)

Thus S1/k=3 or 4 requires at least one of the
two triple offsets to be <7/50. This is a
larger exclusion region than simply proving
the existence of a shared double status above
the 13/60 threshold.

**S2: (3+0,2+2).** The farther cap of the
2+2 axis has offset >=1/2, hence contributes
two outer centers. If the triple offset
is >=7/50, it contributes another two:

    S2, triple offset >=7/50 => k>=4.            (14)

If also the signed central-center coordinate
t on the 2+2 axis satisfies |t|<=1/10,
then its nearer cap has offset
1/2-|t|>=2/5. The cap-inner-pair lemma
guarantees a third outer center on that
axis, and therefore

    S2, triple offset >=7/50, |t|<=1/10
       =>k>=5.                                    (15)

Even without the extra triple-offset hypothesis,
any S2 configuration with |t|<=1/10 has
k>=4: three outer centers on its 2+2 axis
and at least one from the triple. This
strictly strengthens the old |t|<=1/14
band for excluding S2/k=3.

**S3: (3+1,2+1).** The singleton opposite the
triple is outer, its signed cap offset being
>17/24. For the separate 2+1 axis, at
least one member is outer: if its two-square
side offset is >=1/2, both its members are
outer; otherwise its opposite singleton
has offset >1/2 and is outer. Hence if the
triple offset is >=7/50, the three
disjoint status groups supply 2+1+1
distinct outer centers:

    S3, triple offset >=7/50 => k>=4.            (16)

If, additionally, the two-square side of
the 2+1 axis has offset >=2/5, the
existing two-case cap argument gives two
outer centers on that axis, yielding k>=5.
Thus S3/k=3 requires **both**
triple offset <7/50 and two-square
side offset <2/5.

**S4** has no triple population and is
not constrained by this theorem. It contains
the exact sharp five-corner candidate.

**Saturated Type A: (3+1,3+1).**
Its two perpendicular triple populations
share exactly one RU double-status member;
its opposite L,D singletons are outer
and distinct from the triple-side members.
If both triple offsets are >=7/50,
the four extremal outer-center witnesses
from the two triples can overlap only
in their unique shared RU label.
Thus at least three distinct outer
centers come from the triples and two
more from the opposite singletons:

    Type A, both triple offsets >=7/50
       => k>=5.                                   (17)

Therefore Type A/k=3,4 forces at least
one of its two triple offsets below 7/50.

These conclusions eliminate actual
**continuous position regions** in the
stated k/status branches. They do
not exclude complete S1,S2,S3 or Type A
regardless of k, and do not classify
other double-side/corner-only exceptions.

## 5. An additional far-singleton lane in a small-offset triple

Suppose one central side serves three whole
squares at offset h<7/50, and its opposite
side also serves a whole square T. The
opposite offset is 1-h>43/50>2/5.
The sharp one-square arbitrary-orientation
cap envelope in HUMAN_ONE_SQUARE_CAP_ENVELOPE.md
gives, with z the center coordinate of T
transverse to the shared side normal,

    R^2 >= (2-h)^2+(|z|+1/2)^2.

Since 2-h>93/50 and R^2<=9789/2500,
we have

    (|z|+1/2)^2
       < 9789/2500-(93/50)^2
       =1140/2500=57/125.                          (18)

But (17/25)^2=289/625>57/125=285/625.
Therefore

    **|z|<17/25-1/2=9/50.**                        (19)

Thus in the surviving 3+1 branch with an
exceptionally small triple offset <7/50,
its opposite singleton's center lies within
9/50 of the diameter along the cap normal.
This is an exact narrow-lane restriction on
an actual remaining case, independent of
all unit-square frame angles.

## Limitations

The proof proves no new all-pattern lower
bound on R. At offsets below 7/50, three
whole squares need not have two outer
centers, and no such assertion is made.
The k=7 full exterior contact cycle with
its central square, including exact candidate
equality, remains a legitimate branch.

The unrestricted optimality implication
R8>=Rhat is still OPEN.
