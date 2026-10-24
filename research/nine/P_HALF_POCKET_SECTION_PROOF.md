# Exact section lemma for the entire E/W upper half-pocket

Complete all-orientation local section theorem and capacity-three bound.
It is one input to the full P.ALL theorem in P_ALL_COMPLETION.md. It does
not assert the stronger standalone rigidity of every upper triple.

Let D be the disk x²+y²≤17/4, E=[1,2]×[-1/2,1/2], W=-E. Let T be an arbitrary
unit square in D∩{y≥0}, physically interior-disjoint from E and W. Write N for
[-1/2,1/2]×[1,2].

**Section lemma.** Either T=N, or T is aligned with center (z,1/2), |z|≤1/2,
or the open interior section I of T at y=1 satisfies

    length(I)>1/2,  inf I<1/2,  sup I>−1/2.                 (1)

In particular each nonexceptional square contains at least one of
(-1/2,1),(0,1),(1/2,1) in its open interior.

## 1. Section existence and length

The exact corner bound gives center radius at most 3/2. Write the center
height as y and the vertical halfwidth as h≥1/2. Whole upper-half containment
gives y≥h. The line y=1 meets the interior unless y+h=1 or y−h=1. The first
equality forces y=h=1/2, hence alignment; avoiding E/W then forces
|z|≤1/2. The second forces y=3/2,h=1/2 and center x=0, hence N.

By reflection and frame equivalence write A≥B≥0, A²+B²=1, h=(A+B)/2,
k=(A−B)/2. For B=0 every nonexceptional section has length one. For B>0,
the chord at displacement δ from the center has length

    min{1/A, (h−|δ|)/(AB)}.

If y≤1, then |δ|=1−y≤1−h, and the second expression is at least

    (A+B−1)/(AB)=2/(A+B+1)>1/2.

If y≥1, the all-angle argument of TWO_COLUMN_SIX_BODY_CAPACITY.md,
§2.2, applies verbatim: it uses only y>0 and corner containment, and proves
1+h−y>AB/2. Thus (1)'s length statement holds without a floor at 1/2.

## 2. The right endpoint

Suppose the right endpoint p=(x0,1) has x0≤−1/2. It lies on an outward side
with normal n=(u,v), u>0, u²+v²=1. Put t=(-v,u). For λ∈[0,1] the vertices are

    P0=p−λt, P1=p+(1−λ)t, Q0=P0−n, Q1=P1−n.             (2)

The outer-face screen gives -2<x<2 at every point of T. Consequently any
point of T with -2<x<-1 and 0≤y<1/2 lies in the open interior of W, which is
impossible. An edge entering that open rectangle is impossible as well.

### 2.1 v≥0

The edge Q0Q1 has its lower endpoint at the lowest point of T. If its lower
height is at least 1/2, the cap endpoint lemma S.1, §2.3 applies and gives a
contradiction. Suppose instead that its lower height is below 1/2.

If Q0Q1 reaches y=1/2, its x-coordinate there is

    x0−(1−v/2)/u < −1,

because u+v<2. Points of that edge just below height 1/2 lie in the interior
of W, a contradiction.

Otherwise the whole edge Q0Q1 lies below y=1/2. The floor at zero gives
λu+v≤1. Thus its upper endpoint Q1 has

    X=x0−u−(1−λ)v
      ≤−1/2−[v+(1−v)/u]≤−3/2.

Its height lies in [0,1/2), so Q1 is inside W, again impossible. The same
edge argument handles equality at the upper height 1/2. Thus v≥0 always
reduces to the already-proved cap case.

### 2.2 v=−w<0 and w≥u

Here the lowest vertex is P0=(x0−λw,1−λu). If it is below height 1/2, then
λu>1/2 and

    (P0)x≤−1/2−λw<−1/2−w/(2u)≤−1.

It lies inside W. Otherwise T is wholly above 1/2, and the cap endpoint
lemma applies. This case is impossible.

### 2.3 v=−w<0 and 0<w≤u

We first prove λ≤(u+w)/2. If P0 has height at least 1/2, then

    λ≤1/(2u)≤(u+w)/2,

where the last inequality is equivalent to w≤u. If P0 lies below 1/2,
avoidance of W forces its x-coordinate to be strictly greater than −1:
equality would make the edge P0Q0 enter W immediately. But

    (Q0)x=x0−λw−u≤−1/2−u<−1,

since u≥1/√2. At its crossing of x=−1, the edge P0Q0 has height

    Y=1+(w/u)(x0+1)−λ/u.

Avoidance of W forces Y≥1/2, so again

    λ≤u/2+w(x0+1)≤(u+w)/2.                              (3)

Put r=1−λ≥1−(u+w)/2. The upper opposite vertex Q1 has coordinates

    (x0−u+rw, 1+w+ru).

Its first coordinate is negative, because w≤u and r≤1. Its squared norm
cannot decrease when x0 is decreased below −1/2. At x0=−1/2 that norm is

    9/4+r²+u+2w+r(2u−w).

This is increasing in r≥0. Substituting the lower bound in (3), and using
u²+w²=1, gives

    |Q1|²≥4+2u−(3/2)u²≥9/2,

because 1/√2≤u≤1 and 4+2u−(3/2)u² is decreasing on that interval. This
contradicts |Q1|²≤17/4.

All normal directions are covered. Therefore sup I>−1/2. Reflection proves
inf I<1/2 and completes the section lemma.

## 3. Exact capacity consequence and the nonexceptional triple case

For any interval satisfying (1), either it contains zero, or its length
and central crossing force it to contain −1/2 or 1/2. Thus the three stated
points pierce every nonexceptional square strictly.

If N is present, Corollary 3 of HALF_DISK_CLOSE_CENTER_RIGIDITY.md shows that
any two other upper squares force exactly the canonical triple

    [-1,0]×[0,1], [0,1]×[0,1], N.                       (4)

If an aligned bottom exception centered at (z,1/2) is present, its top edge
at y=1 is [z−1/2,z+1/2]. Any other nonexceptional section must avoid that
closed interval. If z≥0, (1) rules out a section to its right, while every
section to its left contains −1/2 strictly. Thus at most one nonexceptional
square exists; reflection handles z≤0. Two distinct bottom exceptions can
only have centers ±1/2 and then force any third square to be N. Therefore
every triple with any exception is (4).

If no exception is present, the three-point transversal gives capacity at
most three. For a triple, order its three open sections from left to right.
They contain −1/2,0,1/2 respectively, and the middle section lies wholly in
(-1/2,1/2) with length greater than 1/2. The left section has its right
endpoint below zero and the right section has its left endpoint above zero.

This section theorem alone does not exclude the last triple of
nonexceptional sections or prove standalone HALF.3. The stronger
classification is proved separately in HALF_POCKET_TRIPLE_RIGIDITY.md. P_ALL_COMPLETION.md
handles every such triple by forcing both path-slider heights down and
proving capacity at most one in the opposite half-pocket. That separate
coupled argument closes P.ALL without assuming standalone HALF.3.
