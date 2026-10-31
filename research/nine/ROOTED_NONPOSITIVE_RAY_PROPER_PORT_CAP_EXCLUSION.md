# Two proper terminal ports cannot avoid their nonpositive resultant ray

Date: October 26, 2026.

**Status: accepted complete uniform geometric implication after full root and independent reviews in `REVIEW_NONPOSITIVE_RAY_PROPER_PORT_CAP_ROOT_2026_10_26.md` and `REVIEW_NONPOSITIVE_RAY_PROPER_PORT_CAP_GLOBAL_2026_10_26.md`.** Both reviews pin the unchanged mathematical source before this acceptance-only status edit. No original gate or shared ledger is changed.

Keep all original interior-disjoint unit squares contained in the circle with center O and

    79/40<=R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1<61/60.

Every contained unit center has norm at most d+1/2<91/60. Every actual contained neighbor beyond a unit support of height h requires h<=d. These are the sharp center/halfwidth bounds in `END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md`, Section 1.

## 1. Full actual local hypothesis

Let K have two distinct actual neighbors T_1,T_2, with positive force magnitudes mu_1,mu_2, actual unit outward normals n_1,n_2, and unchanged applications P_1,P_2. All three actual squares and every other physical square stay in place. Put

    M=mu_1 n_1+mu_2 n_2.

Assume n_1,n_2 are nonparallel, their actual force lines concur at

    q=-t M,                         t>0,

and their actual ports are proper at K:

    P_i=q+a_i n_i,                  a_i>=0.                (1)

Assume also the whole closed K avoids the nonpositive resultant ray:

    K intersect {-s M:s>=0} is empty.                      (2)

**Theorem.** These hypotheses are impossible.

No force equation involving any other neighbor of K is imposed. The vector M is precisely the displayed pair sum, not a replacement leaf. The conclusion uses no load or degree premise at T_i. In particular it is available when M is the full resultant of a genuine terminal block, once the negative concurrence, properness and forbidden ray have all separately been proved.

## 2. A positive resultant-ray point belongs to K

Since q lies on the forbidden ray, (2) gives q not in K. Therefore a_1,a_2 are strictly positive in (1). Put

    W=mu_1/a_1+mu_2/a_2>0.

The positive convex combination of the two actual ports with weights (mu_i/a_i)/W is

    P_bar=q+M/W=(1/W-t)M in K.                            (3)

Condition (2) makes its coefficient strictly positive. Thus

    P_bar=r M in K,                 r>0.                 (4)

The vector M is nonzero because two nonparallel positive vectors cannot sum to zero.

## 3. Both ports occupy one far side at coordinate A>1

The origin itself is excluded by (2). Choose an own side coordinate of K whose closed interval misses zero, and reflect that coordinate if necessary. Write K in its own orthonormal axes about the unchanged origin as

    K=[a,a+1] times [b,b+1],          a>0.

Equation (4) gives M_x>0. Consequently q_x=-t M_x<0. Every actual port has x>=a>0, so (1) gives (n_i)_x>0. Each P_i is therefore on the far side x=A, where

    A=a+1>1.                                               (5)

If (n_i)_y>0 the actual port is the upper-right vertex; if it is negative the port is the lower-right vertex; if zero the port is its original far-side mean.

Both vertical normal components cannot be strictly positive or both strictly negative. In either case both ports would equal the same vertex. The two nonparallel actual force lines would then concur there, contrary to q not in K. They are not both zero because the normals are nonparallel.

If the two vertical components have opposite signs, properness places q_y between the lower and upper endpoint heights. If one component vanishes, q_y equals the height of that side mean. Thus in all cases

    q_y in [b,b+1].

The point P_bar in (4) also has height in this interval, and its height r M_y has the opposite weak sign from q_y=-t M_y. It follows that

    b<=0<=b+1.                                             (6)

In particular every nonzero vertical normal component has the same sign as its actual port height.

## 4. The exact moment identity bounds every normal angle

Because q=-tM and the actual lines pass through q, their total origin moment is zero. Writing P_i=(A,y_i) gives

    A M_y=sum_i mu_i y_i (n_i)_x,
    M_x=sum_i mu_i (n_i)_x>0.

Hence, with k=M_y/M_x,

    k is a positive weighted mean of y_1/A and y_2/A.       (7)

For a positive vertical normal component, its port is the upper-right vertex, so y_i is the largest available port height and k<=y_i/A. For a negative component, its port is the lower-right vertex and k>=y_i/A. From (1), the actual normal slope is

    (n_i)_y/(n_i)_x
       =(y_i+tM_y)/(A+tM_x)
       =(A/(A+tM_x))(y_i/A)
          +(tM_x/(A+tM_x))k.                              (8)

Thus in the positive case the slope is at most y_i/A; in the negative case it is at least y_i/A. In both cases multiplication by the correctly signed vertical component gives

    y_i (n_i)_y >= A (n_i)_y^2/(n_i)_x.

The same inequality holds when that component is zero. Therefore the actual support height satisfies

    h_i=P_i.n_i
       =A(n_i)_x+y_i(n_i)_y
       >=A/(n_i)_x.                                      (9)

Every original neighbor is contained, so h_i<=d. Equations (5),(9) imply

    (n_i)_x>=A/d>60/61,
    |(n_i)_y|<11/61,
    h_i>1.                                                (10)

These estimates are consequences of the actual moment equation and the entire proper-port geometry; they do not assume the normals are side axes or reset either mean.

## 5. The two actual neighbor centers cannot be a unit apart

Put M_*=91/60 and let c_i be the actual center of T_i. Its inward separating support has halfwidth at least 1/2, so

    c_i.n_i>=h_i+1/2>3/2,
    |c_i|<M_*.

Its transverse component relative to n_i therefore has magnitude less than

    sqrt(M_*^2-9/4)=sqrt(181)/60<27/120.

Using (10), the horizontal coordinate has the strict lower bound

    (c_i)_x
      > (3/2)(60/61)-(11/61)(27/120)
      =3501/2440=:L.                                    (11)

Both centers consequently lie in the same open rectangle

    L<x<M_*,
    |y|<sqrt(M_*^2-L^2).

Its squared diameter is

    (M_*-L)^2+4(M_*^2-L^2)
      =52124381/53582400
      =1-1458019/53582400 <1.                            (12)

Thus |c_1-c_2|<1. But distinct actual interior-disjoint unit squares have disjoint open incircles of radius 1/2, and their centers are at least one apart. This is a contradiction, proving the theorem.

## 6. Use and limitations

In a middle triangle with an origin-interior neighbor, `ROOTED_ORIGIN_TRIANGLE_EXTERNAL_RAY_RESTRICTION.md` supplies (2) for the actual full external resultant. To apply the present theorem to another two-port block at that root, one must still prove its concurrence is a strictly negative multiple of that same resultant and both of its actual root ports are proper. Those are genuine hypotheses. A root with one improper port is not removed by this source.

The result is uniform in all root degrees, neighbor loads, side owners, actual mean endpoints and original completion squares. It is a physical two-neighbor center contradiction, not a sampled pose or a numerical stress test. No Lean compilation, CI, remote action, or shared-ledger edit is used.
