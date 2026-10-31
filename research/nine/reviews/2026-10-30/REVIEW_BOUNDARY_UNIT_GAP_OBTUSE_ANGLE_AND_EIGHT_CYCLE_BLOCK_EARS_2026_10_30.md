# Independent review of the obtuse boundary-gap theorem and full four-mark C8 exclusion

Date: October 30, 2026 UTC.

**Verdict: PASS for the complete frozen source. No repair requested.**

## 1. Literal source and review scope

Read the complete current file

`BOUNDARY_UNIT_GAP_FORCES_OBTUSE_CENTER_ANGLE_AND_FOUR_LOAD_EIGHT_CYCLE_EXCLUSION_2026_10_30.md`

- Size: 11,921 bytes.
- SHA256: `fa63e0ef4a0d94d47ff05e848b46792ac2861d0504b8369bc109beb3fd7d5e5a`.
- Git blob: `60f27e3eb723dbb6782fd07f6357ee59bb230d9d`.

The reviewer independently reconstructed the self-contained fixed-point
geometry, both whole-interval cubic estimates, the strict right-angle
argument, and every cycle caller. The reviewer authored the imported
base marked-cycle theorem; this note does not describe that source as
independently authored. Its full root and axial reviews are separate.

The sole cycle input is the base source frozen at SHA256
`b5d9f55141ca2ab2c4f4195de68a714340fa2de607b8b9e81bb484578e4b16be`.
The new two-square geometric theorem uses none of its cycle assumptions.

## 2. Center frame, inward displacement, and the dominant coordinate

For a physical boundary unit, the source correctly keeps

    5/4<r<M=91/60,
    r<133/64-(s+c)/2,
    c>=s>=0, c^2+s^2=1.

The affine radius bound follows by completing the actual farthest-
corner equality; no equality radius or endpoint orientation is fixed.

With K=1/sqrt(2), B=13/32 and A=K+B, the proposed points have relative
radial/transverse coordinates (-(r-A),+-B). The displacement r-A is
positive. The exact bound K>70/99 gives

    K+13/16>M,
    70/99+13/16-M=23/7920>0.

Thus F1-F2=(c-s)*(A+B-r)>=0 for the two coordinate deviation bounds.
It is sufficient to control F1. The substitution

    F1<=G=(6113/6336)*s+(13/32)*c-(s^2+s*c)/2

is valid for the whole interval, including s=0. All coordinate
reflections and exchanges are descriptive changes to the calculation,
not changes to the original square.

## 3. Both continuous cubic intervals

The upper bound c<=1-s^2/2 is valid throughout. For a lower bound
c>=1-k*s^2, squaring nonnegative sides gives exactly the threshold
s^2<=(2*k-1)/k^2. It yields the stated k=5/9 bound for s<=3/5 and
the k=3/5 bound on the entire interval s<=1/sqrt(2).

On the first interval, these bounds give

    1-2G>=P(s)=3/16-(2945/3168)*s+(45/32)*s^2-(5/9)*s^3.

At z=s-9/20 the exact expansion is

    P=467/140800-(47/31680)*z+(21/32-(5/9)*z)*z^2.

For -9/20<=z<=3/20, the quadratic coefficient is at least 55/96.
Dropping its nonnegative term and using |z|<=9/20 gives the uniform
strict lower bound 373/140800. This covers both closed endpoints.

On the second interval, the cubic H differs only by its -3*s^3/5
term. Its second derivative is strictly above 9/80 because s<3/4.
The exact initial values

    H'(3/5)=43517/396000>0,
    H(3/5)=2107/330000>0

therefore make H positive throughout. There is no missing neighborhood
at the split point. Both coordinates of both proposed fixed points
are strictly inside the original square's own coordinate intervals.
Lemma 1 is proved on the entire boundary orientation and radius domain.

## 4. Strict set-distance conclusion at and below ninety degrees

After symmetric placement of the center directions at +-theta/2,
the selected interior points facing each other have equal horizontal
coordinates and distance

    2*|A*sin(theta/2)-B*cos(theta/2)|.

The expression inside the absolute value increases from -13/32 to
1/2 on 0<=theta/2<=pi/4, since its derivative is positive. The point
distance is therefore at most one, including theta=pi/2.

Strictness in the set distance is justified by actual interior
membership. If the two points differ, move the point in the first
square a sufficiently small amount toward the other while staying in
its open interior. The point distance decreases strictly. If they
coincide, the set distance is already zero. Consequently any two
physical boundary squares with a nonobtuse center angle have set
distance strictly less than one.

The proof uses arbitrary independent frames. It does not choose
contact applications or replace support faces by midpoint assumptions.
The two-square theorem is force-free and includes zero-weight physical
circle corners and marks.

## 5. Actual run clearance and full cycle scope

For a common-normal supported run, the exact endpoint support identity
implies n.(y-x)>=sum internal widths for every x in the first endpoint
square and y in the second. Taking the minimum over the two actual
closed squares gives set distance at least the internal count.

Every nonempty run between physical boundary marks therefore has
endpoint minor angle greater than ninety degrees. The imported
compatible annular-order theorem supplies one full turn of consecutive
marked-center angular gaps; each gap is at least its minor angle.
Four nonempty runs would consequently consume more than a full turn.
The at-most-three conclusion is uniform over all other runs and all
marked degrees.

For an eight-body marked cycle, the base integer bound m+ell<=8
first excludes two-internal runs. Four marks and four unmarked bodies
then force the alternating pattern (1,1,1,1). Its four nonempty runs
contradict the new angle theorem. Thus the whole eight-body four-mark
family is excluded, not only its all-side, all-diagonal or fixed-mean
subfamilies.

With at most three marks and no two-internal runs, an eight-body cycle
would have at most six bodies. Combined with the four-mark exclusion,
every surviving compatible eight-body marked cycle requires at least
five marks, as stated.

## 6. Force caller and retained frontier

In the physical stress application, every unmarked body retains its
zero total circle weight and true positive degree two in the whole
same graph. Full translational balance supplies the common normal;
no torque equation or side/diagonal classification is used. All extra
marked endpoint forces, contacts and means remain in place.

For an entire simple component, marking its four positive-circle-load
bodies satisfies those premises. The base theorem excludes nine or
more bodies, and the new theorem excludes eight, so its body count is
at most seven. The seven-body record pattern (2,0,1,0) has only two
nonempty runs and is preserved.

The source accurately leaves eight-body cycles with five or more
marks, arbitrary additional forces at circle-clear cycle vertices,
and the sharp seven-body side-short terminal beyond its conclusion.
It claims no automatic original coarse-row closure. No Lean
compilation, CI, numerical pose search, finite certificate, original
ledger mutation or remote write was used in this review.
