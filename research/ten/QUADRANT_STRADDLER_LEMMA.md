# At most one unit square can straddle an empty quadrant

**Status:** complete hand proof, checked in this session. No independent
agent review or Lean verification is claimed. This is a geometric lemma;
it uses no stress or circle hypothesis.

Let O be the open northeast quadrant `{x>0,y>0}`. Call a closed unit
square S a straddler if its interior avoids O and

```text
max_S x>0,       max_S y>0.
```

**Theorem.** Any two such straddlers overlap in their interiors. Moreover,
every straddler overlaps the interior of the anchored square `[-1,0]^2`.
The conclusions are invariant under translations, reflections and rotations
of the whole configuration.

## 1. A straddler has a strictly positive square-side normal

For each sufficiently large integer M, S and the square `[0,M]^2` have
disjoint interiors. The separating-axis theorem for rectangles supplies
one of the coordinate axes or one of S's two side-normal axes separating
them. Choose its sign so that

```text
max_{p in S} n dot p <= min_{q in [0,M]^2} n dot q.
```

There are finitely many candidate signed unit normals, independent of M.
One occurs for arbitrarily large M. Its right side is
`M*(min(n_x,0)+min(n_y,0))`. A negative component would make this tend to
minus infinity, which is impossible for the fixed left side. Hence both
components are nonnegative and the right side is zero. A coordinate-axis
normal is impossible because S has strictly positive maxima in both
coordinates. Thus n is a side normal of S and

```text
n=(c,s),       c,s>0,       c^2+s^2=1,
max_S n dot p=-d<=0.
```

This proves the separator coverage; it is not an assumption on S's frame.
Put `v=(-s,c)`. Since both directional widths of a unit square in its own
side frame are one, write exactly

```text
S={-u*n+z*v : d<=u<=d+1, t<=z<=t+1}.
```

The two positive coordinate maxima say

```text
-d*c-t*s>0,       -d*s+(t+1)*c>0.
```

Consequently

```text
-1<t<0,
-1+d*s/c < t < -d*c/s,
0<=d<c*s<=1/2.                                      (1)
```

The strict upper bound for d follows by subtracting the two bounds for t
and using `c/s+s/c=1/(c*s)`.

## 2. Every separating axis of two straddlers fails

Give the two squares subscripts 1 and 2. On the mixed-sign axis
`v_1=(-s_1,c_1)`, each square has both a strictly negative and a strictly
positive projection. Indeed a point with positive x must have nonpositive
y, giving negative projection, while a point with positive y similarly
gives positive projection. A boundary point in O is impossible as well:
O is open and a square is the closure of its interior. Thus both
projection interiors contain zero.

On the other axis n_1, S_1 has projection interval `[-d_1-1,-d_1]`.
Set `A=n_1 dot n_2`. Then `0<A<=1`, and

```text
A=c_1*c_2+s_1*s_2
 >=min(c_1,s_1)*(c_2+s_2)
 >min(c_1,s_1)>=c_1*s_1>d_1.                         (2)
```

By (1), zero belongs to the interior of S_2's z interval. Its projection
on n_1 therefore contains the values `-(d_2+1)*A` and `-d_2*A`. Hence

```text
min_{S_2} n_1 dot p <= -(d_2+1)*A <= -A < -d_1,
max_{S_2} n_1 dot p >= -d_2*A > -1/2 > -d_1-1.
```

The projection interiors overlap on n_1 too. Exchanging the two squares
checks both axes of S_2. All four rectangle separating axes fail with
strict overlap. The rectangle separating-axis theorem proves that the
square interiors overlap.

## 3. An anchored southwest square also excludes a straddler

Let Z=`[-1,0]^2` and use the straddler's n,v,d,t from Section 1. The
projection intervals of Z are

```text
n dot Z=[-c-s,0],       v dot Z=[-c,s].
```

Its v interval and the straddler's `[t,t+1]` both contain zero strictly.
The n intervals overlap strictly because `d<c*s<c+s` and `-d-1<0`.
The straddler's coordinate projections also contain zero strictly: its
maxima are positive, while

```text
min_S x=-(d+1)*c-(t+1)*s<0,
min_S y=-(d+1)*s+t*c<0.
```

They consequently overlap the interiors of Z's coordinate projection
intervals `[-1,0]`. These are all four separating axes of S and Z, proving
the second assertion.

