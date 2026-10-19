# Every seven-square annular neighbor cycle has a radial-boundary representative

This is a hand-proved global geometric reduction. Together with the completed [four-type pair certificate](FOUR_TYPE_BOUNDARY_PAIR_CERTIFICATE.md), it gives the [global exterior-frame theorem](GLOBAL_EXTERIOR_FRAME_WINDOW.md), excluding M5 and M6. The reduction itself does not assert a sharp radius lower bound.

Set

\[
Q=9789/2500,\qquad \rho=1/12.
\]

A unit square is **admissible** if it lies in the closed disk of squared radius Q and its distance from the origin is at least rho. We retain only the seven cyclic neighbor nonoverlap conditions; nonneighbor squares may overlap in this relaxation.

## Theorem

Let seven admissible unit squares have distinct center rays in cyclic order, and suppose each consecutive pair, including the last and first, has disjoint open interiors. There is another such seven-square neighbor-cycle configuration in which:

1. every square's true frame is unchanged;
2. the cyclic order of the seven center rays is unchanged;
3. every square touches either the outer containing circle or the boundary of the forbidden radius-rho disk;
4. every one of the seven pair support widths is unchanged.

The deformation is not asserted to retain nonneighbor nonoverlap or avoidance of an entire central unit square. Those conditions have already been relaxed to the central disk and cyclic neighbor conditions. That relaxation is sound for proving an impossibility theorem.

Consequently, if an actual eight-square packing supplies a central radius-rho disk and seven exterior squares, any width-budget inequality depending only on the exterior frames survives this reduction. A universal obstruction for the two radial boundary types therefore excludes the original packing.

## 1. Uniform radial and angular separation

Write an admissible square's center as p, with r=|p|. Its inscribed open radius-1/2 disk cannot intersect the open radius-rho disk, so

\[
r\ge 1/2+\rho=7/12.
\]

In the square's own frame let the center coordinates be x,y. The largest squared vertex norm is

\[
r^2+|x|+|y|+1/2\ge r^2+r+1/2.
\]

Thus r^2+r+1/2<=Q, and in particular

\[
r<71/50,
\]

since (71/50)^2+71/50+1/2-Q=13/625>0.

Two disjoint unit-square interiors have center distance at least one, by their open inscribed disks. If their center radii are r,s and their smaller angular separation is gamma, then

\[
\cos\gamma\le F(r,s):=\frac{r^2+s^2-1}{2rs}.
\]

On the square [7/12,71/50]^2, F attains its maximum at a corner. Indeed, for fixed s,

\[
\partial_r F=\frac{r^2-s^2+1}{2r^2s};
\]

this is positive throughout if s<=1, and otherwise has at most one zero, which is a minimum. Hence the maximum in r is at an endpoint; apply the same argument in s. The three distinct corner values are

\[
-23/49,\qquad 17443/21300,\qquad 3791/5041.
\]

Their maximum is 17443/21300. Since

\[
17443/21300<41/50\le\cos(3/5),
\]

we obtain the strict universal bound

\[
\boxed{\gamma>3/5.}
\]

Let delta_0,...,delta_6 be the cyclic directed center gaps. Every gap exceeds 3/5. None can be at least pi: otherwise the other six sum to more than 18/5>pi, contradicting the total 2pi. Therefore

\[
\boxed{3/5<\delta_i<\pi\quad\text{for all seven neighbors}.}
\]

This deduction uses only adjacent-pair nonoverlap, the disk, and the central core. It does not use all 21 exterior pair conditions or assume an angular-marker order.

## 2. Translate one unanchored square

Fix all true frames and all centers except p_i. Select one genuine signed SAT axis witnessing nonoverlap on each of its two neighboring pairs. Both selected axes remain fixed because every frame is fixed.

As constraints on p_i, the two chosen SAT inequalities have the form

\[
a_1\cdot p_i\ge b_1,\qquad a_2\cdot p_i\ge b_2,
\]

with unit vectors a_1,a_2. Their intersection P has a nonzero recession direction. If a_1+a_2!=0, choose d=a_1+a_2; then a_j dot d=1+a_1 dot a_2>=0. If a_2=-a_1, choose d perpendicular to a_1. In either case p_i+t d remains in P for all t>=0.

Let K_i be the center body for outer-disk containment of this fixed square frame. It is the intersection of the four closed radius-sqrt(Q) disks obtained from the vertex inequalities, hence compact and convex. Its boundary means that at least one actual square vertex lies on the containing circle.

Let B_i be the forbidden center body for meeting the open radius-rho disk. Its closure is the Minkowski sum of the reflected centered unit square and the closed radius-rho disk. It is compact and convex, and its boundary means dist(0,S_i)=rho.

If the current square touches either boundary, leave it fixed. Otherwise, move its center along p_i+t d until it first meets the boundary of K_i or B_i. Such a first time exists and is finite: the starting point has strict clearance from both boundaries, whereas the ray eventually leaves compact K_i. At the first time, the square still lies in K_i and has not entered the interior of B_i. Its two selected SAT inequalities still hold. Thus it is admissible and retains both neighboring nonoverlap conditions.

Throughout this motion, the center radius stays bounded away from zero, so center arguments have continuous lifts. The cyclic order cannot change: the first change would make two neighboring rays coincide, contrary to their separation bound. A directed gap cannot reach pi either, by the seven-gap argument in section 1. Hence the same seven cyclic neighbor labels remain valid throughout the deformation.

## 3. Anchor all seven labels

Perform the preceding operation successively for the seven squares. Moving a later square does not alter any earlier square's center or frame; therefore the earlier square remains on its outer or core boundary. The true frames of all squares stay fixed, so every genuine pair width

\[
w_{ij}=\frac{1+|\cos(\theta_j-\theta_i)|+|\sin(\theta_j-\theta_i)|}{2}
\]

is unchanged. After at most seven such translations, every label touches one of the two boundaries. This proves the theorem.

## 4. The resulting exact state domain

For a center of radius r, select a quarter-turn-equivalent frame with relative angle alpha in [-pi/4,pi/4]. Put

\[
c=\cos\alpha,\quad s=|\sin\alpha|,\quad L=c+s.
\]

The outer boundary has

\[
r=r_+(\alpha)
=\frac{-L+\sqrt{L^2+4(Q-1/2)}}2.
\]

The core boundary is the unique radial solution of

\[
(rc-1/2)^2+\max(rs-1/2,0)^2=\rho^2.
\]

Explicitly, let r_side=(1/2+rho)/c. Then

\[
r_-(\alpha)=
\begin{cases}
r_{\rm side},&r_{\rm side}s\le1/2,\\
\dfrac{L+\sqrt{L^2-2+4\rho^2}}2,&r_{\rm side}s\ge1/2.
\end{cases}
\]

The formulas agree at the branch boundary. Thus the complete reduced state space is the union of **two one-dimensional curves**. A seven-cycle has 2^7 radial type words and seven continuous alpha parameters. Relabeling by cyclic rotation reduces the binary type words to 20 necklaces; also quotienting by reflection gives 18 bracelets. A proof need not use those quotients: retaining all 128 words is already finite and complete.

Every actual original packing under the ceiling maps into this domain with all seven widths unchanged. The completed four-type certificate supplies a universal cost inequality on all continuous angles; the unrestricted sharp radius inequality remains a separate proof obligation.

## 5. Optional extension to abstract cycles with fixed rotational holonomy

The same argument applies to the cyclic local-state relaxation used by min-plus discovery, whose directed gaps need not sum to 2pi, provided its low-cost level prevents gap endpoints. Write Phi=sum delta_i and realize the chain with endpoint p_7=Rot(Phi)p_0 and endpoint frame theta_7=theta_0+Phi. Hold Phi and the absolute lifted true frames fixed. For label 0, the incoming neighbor is the rotated copy Rot(-Phi)p_6. Each label again has just two fixed SAT halfplanes.

Uniformly for 0<=beta<=1/3, c0=(sqrt(2)-1)/2, and

\[
G=\sum_i\delta_i-\beta\sum_i(w_i-1)+2\beta c_0,
\]

translations at fixed frames and Phi preserve G exactly. A gap delta_i=0 is impossible by radial span<1 and center distance>=1. If delta_i=pi and all other gaps lie in [0,pi], section 1 gives

\[
G>\pi+18/5-5\beta c_0>63/10,
\]

Indeed c0<1/4 and pi>157/50 give

\[
\pi+18/5-5\beta c_0
>157/50+18/5-5/12
=1897/300>63/10.
\]

Hence within G<=63/10 no gap can reach pi during the motion. This yields the same boundary-only representative for every abstract low-cost cycle for the entire coefficient interval 0<=beta<=1/3. The preceding ordinary plane theorem suffices for the completed global M5/M6 obstruction, so this stronger holonomy formulation is optional.

No numerical optimizer, finite sampling, or missing full-domain inequality is used in the boundary reduction itself.
