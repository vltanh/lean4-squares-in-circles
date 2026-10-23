# A G-zero endpoint opposite a negative outer error has the same small angular domain

## 1. Exact mixed-endpoint hypotheses

Put
\[
 Q=\frac{9789}{2500},\qquad q_L=\frac{19577}{5000},\qquad
 K=\frac{13}{12},\qquad C_0=\sqrt{Q/2}-\frac12,
 \qquad W(z)=\frac{1+\cos z+\sin z}{2}.
\]
Let H, A, B and D be nonnegative sorted anchors with containing
circle ceiling `q_L<=q<=Q`. Assume A is on its actual q-circle,
\[
 \frac{67}{200}\le b_A<\frac12,
 \qquad b_A+b_B\ge1,
\tag{1}
\]
and let
\[
 t,u,e,h\ge0,\qquad \alpha=t+u+e\le\frac7{10},
 \qquad z=t+h<\frac25.
\tag{2}
\]
The positive-side G-zero endpoint supplies
\[
 (a_A-\tfrac12)\cos z-(b_A+\tfrac12)\sin z=\frac12,
\tag{3}
\]
\[
 b_H\ge\frac12+\frac12\cos h
              -(\sqrt{q-1/4}-1)\sin h.
\tag{4}
\]
On the opposite negative side retain the exact core composite
\[
 (\sec e)b_D+a_B\cos u-b_B\sin u
 \ge W(u)+\frac12+\frac12\sec e+K\tan e.
\tag{5}
\]
No E sign or E inequality is needed for the conclusion below.

**Domain theorem.** These hypotheses imply
\[
 \boxed{\quad h>\frac{107}{1000},\qquad
             \alpha+h<\frac{311}{1000},\qquad
             \alpha<\frac{51}{250},\qquad
             u+e<\frac3{25}.\quad}
\tag{6}
\]
Thus allowing the opposite negative outer error does not enlarge
the angular domain used in
`HAND_G5_G_ZERO_TWO_AFFINE_STRESS_SCALARS.md`. Its contribution
to the stress still has to be retained; (6) alone is not an
endpoint exclusion.

## 2. The unchanged positive side and a short negative span

The proofs in Sections 2--3 of
`HAND_G5_G_ZERO_ENDPOINT_EXCLUSION.md` use only (1), (3), (4)
and the H/A circles. They therefore give, unchanged,
\[
                         h>.107,\qquad z>.19.
\tag{7}
\]
For clarity, the first comparison uses `C_0<.89923` and the
HG endpoint lower bound at `h=.107`. The second uses the active
A circle and
`L_{q_L,1/2}(.19)>1`, whereas `b_A+1/2<1`.

Equation (1) gives `b_B>1/2`; consequently
\[
                     a_B\le\sqrt{Q-1}-\frac12<1.20752.
\tag{8}
\]
The unsigned shared-chain estimate in Section 5 of
`HAND_G4_NEGATIVE_NONCANCELING_ZERO_CORE_TRANSPORT.md` applies
directly to (5). Before its weaker uniform coefficient is used,
it gives
\[
 b_D+a_B\ge2+(b_B+\tfrac12)\sin u+\frac9{10}\sin e
           \ge2+\frac9{10}\sin(u+e).
\tag{9}
\]
The cosine term dropped there is nonnegative; feasibility of
(5) gives its required `V(u)>3/5` and `a_B>1/2`. Also
`0<=u+e<=alpha<=.7`, so sine is increasing on the relevant
interval. Since `b_D<.9`, (8)--(9) imply `u+e<.12`: otherwise
\[
 \frac9{10}\sin(.12)
 \ge\frac9{10}\left(.12-\frac{.12^3}{6}\right)
 =.1077408>.10752.
\tag{10}
\]
The final exact reserve is `69/312500`.

## 3. Retain a continuous cap for the negative side

Write
\[
 L(z,D)=\cos z\sqrt{Q-(D+\cos z)^2}
                       -\sin z(D+\cos z)
\tag{11}
\]
and put
\[
 D(e)=1+(\tfrac12-C_0)\sec e+K\tan e.
\tag{12}
\]
Using `b_D<=C_0` in (5), its corner cap is at most
`L(u,D(e))`. Together with A's active circle and AB, this yields
\[
                       2\le L(z,1/2)+L(u,D(e)).
\tag{13}
\]

The same exact derivative identity as in the all-outer AB note
gives
\[
 D'(e)-1\ge
 \frac{(\sin e-1/5)^2+13/300}{\cos^2e}>0.
\tag{14}
\]
In particular `D(e)>.6+e`. Feasibility and `b_B>1/2` give
\[
 D(e)\le(a_B-\tfrac12)\cos u-(b_B+\tfrac12)\sin u
           \le a_B-\tfrac12<.70752,
\tag{15}
\]
and
\[
                       Q\ge(D(e)+1)^2+1.
\tag{16}
\]
All cap radicands below are therefore positive. At fixed e,
`L(z,1/2)` is strictly convex on `[.19,.311]`, as proved in
Section 4 of the G-zero endpoint note. The other cap
`L(u,D(e))` is strictly convex on its full interval by
`HAND_G5_HARD_SPLIT_CONVEXITY_FULL_FEASIBLE_CAP_RANGE.md`,
using `D(e)>.6` and (16).

Suppose contrary to (6) that `z+u+e>=.311`. Since `e<.12`,
decrease z and u, keeping e fixed, until
\[
                        z+u+e=.311,
 \qquad .19\le z\le.311-e.
\tag{17}
\]
This is possible without increasing either angle or making z
less than .19. Both caps decrease with their first argument,
so (13) still holds at the decreased pair. At fixed e their
sum in (17) is convex in z. It suffices to exclude its two
endpoints `z=.19` and `u=0`.

## 4. The z=.19 endpoint

Here `u+e=.121`. If the B cap is below `1/2`, the cap sum is
less than `1.01+.5<2`, by the existing bound
`L(.19,1/2)<1.01`. Otherwise take the B corner on its cap,
\[
 Y=L(u,D(e)),\quad X=\sqrt{Q-Y^2},\quad
 (a,b)=(X-\tfrac12,Y-\tfrac12).
\]
This is sorted: its cap identity gives `X>=1+D(e)>1.6`.
Realize the negative pair with the diagonal outer anchor
`a_D=b_D=C_0` and the core intermediate
\[
                   a_T=7/12,\qquad b_T=D(e)-1/2.
\]
Equations (12), (15) make its negative zero contact an equality,
and the B cap makes its hard-quarter contact an equality. This
core intermediate is sorted and has circle below q_L, by the
same calculation as (15) of the all-outer AB note.

If `b>=1/2`, the proof of (8)--(10) applies to this necessary
pair and contradicts `u+e=.121>.12`. If `0<=b<=1/2`, the
small-transverse negative transport gives the aligned composite
at angle `.121`, keeping this same B coordinate. Its cap then
satisfies
\[
 Y\le L(.121,3/2-C_0)<L(.121,.6)<.98.
\tag{18}
\]
For e zero the same assertion is the original aligned cap;
no strict transport is required. The last numerical bound is
the exact rational comparison in Section 4 of the G-zero
endpoint note. Thus the sum in (13) is less than
`1.01+.98<2` in all cases. This excludes the first endpoint.

## 5. The u=0 endpoint decreases strictly with e

The second endpoint sum is
\[
 S(e)=L(.311-e,1/2)+\sqrt{Q-(D(e)+1)^2}.
\tag{19}
\]
It is defined on the whole interval from zero to the original
e: (16) holds there because D increases. On that interval
`0<=e<.12` and `.19<.311-e<=.311`.

The first cap is convex on this interval, and
\[
                       -L_z(.19,1/2)<\frac{73}{50}.
\tag{20}
\]
Here is an explicit rational verification of (20). At z=.19,
alternating Taylor bounds give
\[
 .982004<\cos z<.982005,\qquad
 .188858<\sin z<.188859.
\]
With `C=.5+cos z`, `w=sqrt(Q-C^2)` and
`X=C cos z+w sin z`, positive squaring gives `w<1.311208`,
and substitution gives `X<1.70297`. Their exact positive
reserves are respectively
\[
 \frac{28441}{12500000000},\qquad
 \frac{248303}{1000000000000}.
\]
The derivative formula `-L_z=X(1-sin z/w)` therefore gives
\[
 \frac{73}{50}-1.70297
                \left(1-\frac{.188858}{1.311208}\right)
 =\frac{6070601}{2622416000}>0,
\]
which proves (20).

For the other term write
\[
 J(D)=\frac{D+1}{\sqrt{Q-(D+1)^2}}.
\]
On its real domain with `D>=.6`,
\[
 J(.6)>1.37,
 \qquad J'(D)=\frac{Q}{[Q-(D+1)^2]^{3/2}}>2.
\tag{21}
\]
The two positive-squaring reserves at D=.6 are
`391859/25000000` and `5241643189/976562500`; the derivative
increases thereafter. Equations (14), (21) give
`J(D(e))>1.37+2e`. Directly from (12), using `sin e<=e`,
`C_0<.9` and the positive numerator, also
\[
                         D'(e)\ge K-.4e.
\]
Consequently, for `0<=e<=.121`,
\[
 J(D(e))D'(e)>(1.37+2e)(K-.4e)
                      \ge\frac{1781}{1200}>1.48.
\tag{22}
\]
The linear coefficient after subtracting `1.37K` stays
positive: `2K-.548-.8(.121)=5707/3750>0`.

Convexity and (20)--(22) show that `S'(e)<1.46-1.48<0`.
But the already proved cap comparisons give
\[
 S(0)<L(.311,1/2)+L(0,.6)
                      <.8356+1.1644=2.
\tag{23}
\]
Thus (13) also fails at this second endpoint. This contradicts
(17), and proves `z+u+e=alpha+h<.311`. Together with (7)
and (10), it proves all of (6).

The proof keeps the negative error in its same-center cap and
uses two intrinsic convexity endpoints. It assumes no angular
mesh, sampled minimum, or omitted preservation of the original
G-to-D frame span. Reflection is permitted, since no E sign
entered any step.
