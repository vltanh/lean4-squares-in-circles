# Cyclic side ownership excludes the entire distinct unloaded triangle by one incenter support inequality

November 1, 2026. PR #11 continuation. **Evidence at construction: H; independent full review requested.**

## 1. Complete original domain

Retain the same nine actual unit squares in one disk with center O and radius R and one unchanged original physical contact-force-and-torque certificate. Three actual squares S_0,S_1,S_2 are entirely selected-circle-unloaded, have positive original triangle edges and exactly one other original positive outside edge each. All outside terminals, other squares, contacts, degrees, loads, zero coefficients and original means are retained. Outside terminals may repeat.

Assume the following precise physical feature:

- The three core frames are pairwise nonparallel modulo quarter turns.
- The three actual pair intersections are singletons, with no point common to all three core squares.
- Every internal selected normal is side-owned, with ownership cyclic: the original S_i-to-S_(i+1) unit normal n_i is an own side axis of S_i, and its original application p_i is in the relative interior of that S_i side and a strictly exposed vertex of S_(i+1). Indices are modulo three.

No new normal is selected and no generic-selection property beyond these literal original hypotheses is used in the proof.

**Theorem.** Every such complete original feature forces

    R > 3/sqrt(2),     R^2 > 9/2 > 1105/256.

This is a uniform exclusion of every cyclic side-owner triangle, with all original positive magnitude ratios and continuous physical side-contact parameters.

## 2. The original contact triangle and its complete moment identity

Let a_i>0 be the unchanged magnitude on S_i-to-S_(i+1). At S_i the two internal outgoing normals are n_i and -n_(i-1).

The reviewed geometric theorem [UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md](UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md) applies because n_i is an own axis and both neighboring actual squares touch. It gives

    n_i dot (-n_(i-1)) >= 0.

Equality would make the own axes of S_i and S_(i-1) perpendicular, contrary to their pairwise nonparallel frames. Parallel or antiparallel axes are excluded by the same frame premise. Therefore their angle alpha_i satisfies

    0<alpha_i<pi/2.

The original incoming application p_(i-1) is a strict vertex of S_i. The positive n_i component of its outgoing normal -n_(i-1) puts this vertex on the **same** n_i support side as the original owned application p_i. The latter is side-interior. The points are distinct because a coincidence would put that point in all three actual squares.

Let t_i be the unit tangent along this actual side from p_(i-1) toward p_i, and write

    p_i=p_(i-1)+ell_i t_i,     0<ell_i<1.

Put N_i=-n_i, the direction from the contact side into S_i. The actual core is

    S_i=p_(i-1)+[0,1]t_i+[0,1]N_i.                (1)

The three p_i form a nondegenerate contact triangle T. To see the strict side incidence, S_(i+1) lies in the n_i outward halfplane of S_i and its minimum-n_i support is the unique vertex p_i. The distinct third contact p_(i+1), which belongs to S_(i+1), consequently lies strictly in that halfplane. Thus the interior of T is on the n_i side of each actual contact segment, and every core lies outward from T.

The interior angle of T at p_(i-1) is exactly alpha_i: its two side normals are n_(i-1),n_i and their external turn is pi-alpha_i. In particular

    alpha_0+alpha_1+alpha_2=pi.

In the own frame (t_i,n_i), the unchanged internal force toward S_(i-1) is

    a_(i-1) [cos(alpha_i)n_i-sin(alpha_i)t_i].

The complete unloaded translation forces the original outside vector to be

    E_i=U_i N_i+V_i t_i,
    U_i=a_i+a_(i-1)cos(alpha_i)>0,
    V_i=a_(i-1)sin(alpha_i)>0.                     (2)

Both own components are positive, so its unchanged original support application on S_i is forced to the actual opposite corner

    q_i=p_(i-1)+t_i+N_i.                           (3)

Now retain the complete original torque about p_(i-1). The incoming internal application contributes zero. The owned application is ell_i t_i. Dividing only by the sign det(t_i,n_i), which is plus or minus one, gives

    a_i ell_i+V_i-U_i=0,
    a_i(1-ell_i)=a_(i-1)[sin(alpha_i)-cos(alpha_i)]. (4)

Because a_i>0 and 0<ell_i<1, this proves

    pi/4<alpha_i<pi/2.                             (5)

It also gives V_i=U_i-a_i ell_i<U_i. Thus the original outside unit normal e_i makes an angle delta_i from N_i toward t_i with

    0<delta_i<pi/4.                                (6)

Every original magnitude, application and full moment has been kept in these identities.

## 3. One existing full-moment inequality bounds the actual inradius

Write g_i=1-ell_i, so 0<g_i<1. Multiplying the three **original** equations (4), and cancelling only the common positive product a_0 a_1 a_2, gives

    product_i g_i = product_i [sin(alpha_i)-cos(alpha_i)]. (7)

Let rho be the circumradius of the actual contact triangle T and set lambda=2rho. By the sine rule its three side lengths ell_i are the three numbers lambda sin(alpha_j), in the corresponding opposite-angle order. Hence (7) is exactly

    product_j [1-lambda sin(alpha_j)]
      = product_j [sin(alpha_j)-cos(alpha_j)],

with all factors positive and all angles in (pi/4,pi/2) summing to pi. The generic theorem in [THREE_ANGLE_CONTACT_TRIANGLE_FULL_MOMENT_UNIFORM_GAP_BOUND_HAND_LEMMA_2026_10_31.md](THREE_ANGLE_CONTACT_TRIANGLE_FULL_MOMENT_UNIFORM_GAP_BOUND_HAND_LEMMA_2026_10_31.md), Sections 1--2, therefore applies literally and gives

    lambda>=sqrt(3)-1,
    rho>=(sqrt(3)-1)/2.                            (8)

Only that generic angle/product theorem is imported; none of its separate loaded-endpoint or A-only caller hypotheses is used here.

Let H and r>0 be the incenter and inradius of this same actual T. The elementary triangle identity is

    r/rho = cos(alpha_0)+cos(alpha_1)+cos(alpha_2)-1.

For example it follows by combining r=4rho product sin(alpha_i/2) with the angle-sum identity cos(alpha_0)+cos(alpha_1)+cos(alpha_2)=1+4 product sin(alpha_i/2).

Concavity of cosine on [pi/4,pi/2] puts its graph above the chord between its two endpoints:

    cos(x) >= sqrt(2)-(2sqrt(2)/pi)x.

Sum at the three angles, using their sum pi. It follows that the sum of their cosines is at least sqrt(2). Therefore (8) gives the exact uniform lower bound

    r >= (sqrt(3)-1)(sqrt(2)-1)/2 > 7/50 > 1/8.   (9)

For the rational strict comparison, sqrt(3)>17/10 and sqrt(2)>7/5, as follows by squaring positive numbers. Their product after subtracting one and dividing by two is 7/50.

## 4. All actual exit corners have one strong support bound about H

Let d_i be the distance from the initial contact vertex p_(i-1) to the foot of H on the corresponding side. Standard right-triangle geometry at the angle bisector gives

    d_i=r cot(alpha_i/2),
    H=p_(i-1)+d_i t_i+r n_i.                      (10)

In particular 0<d_i<ell_i<1. The other endpoint foot-distance on the same side is likewise r cot(alpha_j/2) for its angle alpha_j.

Since every angle lies strictly between pi/4 and pi/2,

    d_i-r < sqrt(2) r.

The other endpoint foot-distance is strictly larger than r. Their sum is ell_i<1, so also

    d_i-r < 1-2r.

For every r>0,

    min(sqrt(2)r,1-2r) <= sqrt(2)-1.

Indeed the two affine bounds intersect at r=1/(2+sqrt(2)); use the first below that value and the second above it. Consequently

    d_i-r < sqrt(2)-1.                            (11)

Combining (3) and (10) gives

    q_i-H=(1-d_i)t_i+(1+r)N_i.

For any delta in [0,pi/4], the function

    f_i(delta)=(1+r)cos(delta)+(1-d_i)sin(delta)

is strictly positive and has second derivative -f_i(delta)<0. Its minimum on the closed interval is therefore at an endpoint. Both endpoints exceed 3/sqrt(2)-1:

    f_i(0)=1+r>9/8>3/sqrt(2)-1,

where 17/8>3/sqrt(2) follows by squaring, since 289/64>288/64; and, by (11),

    f_i(pi/4)=(2+r-d_i)/sqrt(2)
               >(3-sqrt(2))/sqrt(2)
                =3/sqrt(2)-1.

Thus, at the unchanged original outside normal e_i from (6),

    e_i dot (q_i-H) > 3/sqrt(2)-1.                 (12)

## 5. Actual outside squares and original force averaging

The original q_i minimizes the unit normal e_i on its unchanged actual outside neighbor. Therefore that same neighbor contains the actual point

    w_i=q_i+e_i.

The unit-step fact holds in every square frame and for every support mean: each nonzero component of e_i moves inward from its minimizing endpoint by at most one, and a zero component leaves the original coordinate unchanged.

Equation (12) now gives, for all three actual points,

    e_i dot (w_i-H) > 3/sqrt(2).                   (13)

Let z_i=|E_i|>0 be the unchanged original outside magnitudes. Summing the three complete unloaded translations cancels every internal original force, so

    sum_i z_i e_i=0.

Because every actual w_i lies in the same disk,

    R sum_i z_i
      >= sum_i z_i e_i dot (w_i-O)
       = sum_i z_i e_i dot (w_i-H)
       > (3/sqrt(2)) sum_i z_i.

Divide by the positive sum to obtain R>3/sqrt(2), hence R^2>9/2. This excludes the entire cyclic-owner domain at R^2<=1105/256.

## 6. Scope and original compatibility

This argument covers all strictly positive original magnitudes, every original side-interior parameter ell_i in (0,1), all pairwise nonparallel orientations and all actual outside-terminal identities in the stated cyclic-owner family. No external star is shortened, no loading is moved and no mean is replaced. The endpoint support estimates deliberately use closed angle intervals only to weaken the actual strict hypotheses.

The three actual owned contact gaps, their full moment product and the original force sum are essential. A radius-free angle identity without the original moment equations would not justify the inradius estimate.

The theorem does not cover the transitive side-owner tournament or a free internal normal. Those are separate physical/selected features. It does not by itself close an original coarse parent; the complete direct-triangle union and original callers still require an explicit join and independent review.
