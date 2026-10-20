# A positive noncanceling zero owner reduces to alignment or a zero transverse endpoint

## 1. Scope and the two useful conclusions

Put

\[
 q_L=\frac{19577}{5000},\qquad Q=\frac{9789}{2500},
 \qquad q_L\le q\le Q.
\tag{1}
\]

Consider original signs H positive, G negative, A positive, with
nonnegative magnitudes and sorted own-frame coordinates. Each corner
satisfies

\[
 (a_i+\tfrac12)^2+(b_i+\tfrac12)^2\le q.
\tag{2}
\]

Normalize A's frame to zero and write

\[
 \theta_H=\Theta\ge0,\qquad
 \theta_G=\Theta+h,\qquad h\ge0,
 \qquad \Theta+h\le7/10.
\tag{3}
\]

Retain original HG axis 0 and GA axis 0. With
`W(z)=(1+cos z+sin z)/2`, their exact inequalities are

\[
 b_H+a_G\sin h+b_G\cos h\ge W(h),
\]
\[
 a_A\cos(\Theta+h)-b_A\sin(\Theta+h)-b_G
                                      \ge W(\Theta+h).
\tag{4}
\]

The positive HG axis 2 transport in
`HAND_G4_SIGNED_THREE_ZERO_REDUCTION_FOR_CANCELING_OUTER_OWNERS.md`
does not apply to (4). Here the same original G circle gives the
replacement.

**Constant-cap conclusion.** For every feasible positive h in (3),
the two inequalities in (4) give one hard-quarter cap with a constant
parameter `D in [1/2,.915)`. This parameter has exactly the form needed
by that note's AB alignment argument.

**Boundary conclusion.** Suppose also `b_A>=67/200=.335`. One may
raise A's primary to its containing q-circle, keeping its transverse
coordinate and frame fixed. The resulting necessary H--G--A system
has a descendant at one of the following two endpoints:

1. HG is aligned and
   `b_H+a_A cos Theta-b_A sin Theta>=1+W(Theta)`;
2. G has zero transverse coordinate, lies on its q-circle, and the
   original GA0 inequality is an equality.

H and A's frame and A's transverse coordinate stay fixed. The
statement concerns the necessary adjacent-edge system. It does not
assert that additional nonneighbor constraints or an original mismatch
restriction survive.

When `b_A>=1/2`, the first alternative always suffices and has strict
pair slack greater than `h/25` for `h>0`. When `b_A>=.335` and
`0<h<=1/10`, it has strict pair slack greater than `h/150`.

The reflected statements apply to original BT2/TD2, with B as the
middle point and D as the fixed outer point. They have the same
positive-error convention as the TD transport in the cited note.

## 2. Exact elimination of the same G circle gives a constant cap

Write `c=cos h`, `s=sin h`, and put

\[
 Z_G=b_G+\tfrac12,\qquad
 M=\tfrac12+c+s-b_H,
\]
\[
 D=\max\left\{\tfrac12,
                Mc-s\sqrt{q-M^2}\right\}.
\tag{5}
\]

The radicand is positive for an actual feasible pair. Indeed, HG0
and the G circle give

\[
             cZ_G+s\sqrt{q-Z_G^2}\ge M.
\tag{6}
\]

Sorting gives `Z_G<=sqrt(q/2)`. On `[1/2,sqrt(q/2)]` the left
side of (6), as a function of Z, has strictly positive derivative

\[
              c-\frac{sZ}{\sqrt{q-Z^2}}\ge c-s>0.
\]

Consequently `M<=sqrt(q/2)(c+s)<sqrt q`. Also `M>0`, because
`b_H<.9` and `c+s>=1`. Rotation of the circle shows that its
unclipped inverse is `Mc-s sqrt(q-M^2)`. Hence (6) is equivalent,
on the nonnegative sorted G domain, to `Z_G>=D`.

Introduce A's corner coordinates

\[
 X_A=a_A+\tfrac12,\qquad Y_A=b_A+\tfrac12.
\]

The GA0 inequality in (4) says

\[
 (X_A-1)\cos(\Theta+h)-Y_A\sin(\Theta+h)\ge Z_G\ge D.
\tag{7}
\]

The primary circle bound `a_A<283/200` gives

\[
                     \frac12\le D<\frac{183}{200}=.915.
\tag{8}
\]

Thus (7) is exactly the hard cap used in Sections 4--5 of the cited
three-zero note, with `D>.434` and the actual q in its radicand.
Its AB comparison depends only on this cap, not on the canceled
form of the original outer pair. In particular its two AB owner
cases and both signs remain valid for (7).

Conversely, if a new A satisfies (7), choose

\[
 b_G'=D-\tfrac12,\qquad
 a_G'=\sqrt{q-D^2}-\tfrac12.
\tag{9}
\]

Equations (5)--(8) show that this is a nonnegative, strictly sorted
G on its q-circle and that both inequalities (4) hold. Thus this
constant cap retains the exact G circle relaxation. No independent
upper estimate for `a_G` has replaced that circle.

## 3. The exact positive-error scalar after lifting A to its circle

Fix `b=b_A`, and set

\[
 Y=b+\tfrac12,\qquad R=\sqrt{q-Y^2},\qquad
 a_A'=R-\tfrac12,\qquad P=R-1.
\tag{10}
\]

Increasing A's primary to `a_A'` preserves (4). The cap feasibility
in (7) implies `a_A'>=1`, so this lifted point is strictly sorted.
In the rest of the proof A denotes this lifted point. Define, for
the angles in question,

\[
 V(z)=P\cos z-Y\sin z,\qquad
 U(z)=P\sin z+Y\cos z,
\]
\[
 w(z)=\sqrt{q-V(z)^2},\qquad T(z)=w(z)-U(z).
\tag{11}
\]

The exact same-circle identity is

\[
        w^2-U^2=q-(P^2+Y^2)=2R-1=2a_A'>0.
\tag{12}
\]

In particular `T>0`. GA0 requires `V(Theta+h)>=1/2`. On the
interval where `V>=1/2`, maximizing the left side of HG0 over the
permitted G transverse coordinate sets `Z_G=V(Theta+h)`, by the
monotonicity in Section 2. Thus the necessary pair inequality is

\[
 b_H+\cos h\,V(\Theta+h)+\sin h\,w(\Theta+h)
                        \ge\tfrac12+\cos h+\sin h.
\tag{13}
\]

Angle addition gives the exact cancellation

\[
 V(\Theta)=\cos h\,V(\Theta+h)+\sin h\,U(\Theta+h).
\]

Consequently (13) is precisely

\[
 J+F(h)\ge1,
\qquad J=b_H-\tfrac12+V(\Theta),
\]
\[
 F(h)=\sin h\{T(\Theta+h)-1\}+1-\cos h.
\tag{14}
\]

The aligned composite is `J>=1`. Retaining `F(h)` exactly is the
reason a local positive-error benefit is not discarded.

## 4. Strict convexity on the entire feasible positive-error interval

Assume `b>=67/200`. Positive squaring gives

\[
 Y\ge\frac{167}{200},\qquad
 P<\frac{397}{500}=.794,
\]
\[
 (897/500)^2+(167/200)^2-Q=\frac{61}{1000000}>0.
\tag{15}
\]

In particular `Y>P`. The function V is strictly decreasing as long
as `V>=1/2`, since `V'=-U<0`. There is a unique end angle
`z_max` satisfying `V(z_max)=1/2`. It is less than `2/5`: indeed
`sin(2/5)>19/50`, so

\[
 V(2/5)<\frac{397}{500}
             -\frac{167}{200}\frac{19}{50}
          =\frac{4767}{10000}<\frac12.
\tag{16}
\]

The complete feasible positive-error interval at fixed Theta is
`0<=h<=h_max:=z_max-Theta`. It contains the original h and all
angles in it are less than `2/5`.

Direct differentiation in z gives

\[
 T'=-\frac{VT}{w}<0,
\qquad
 T''=\frac{T(qU+V^2w)}{w^3}>0.
\tag{17}
\]

At zero, `T(0)<1` is equivalent by positive squaring to `Y>P`.
Thus `0<T<1` throughout this interval. Also `U>=Y` because
`U'=V>0`, and

\[
 w\le\sqrt{q-1/4}<\frac{383}{200},\qquad
 \frac{T}{w}=1-\frac Uw<1-\frac{167}{383}
                           =\frac{216}{383}.
\tag{18}
\]

Equations (15),(18) give the uniform rational reserve

\[
 1-\frac{2VT}{w}
 >1-2\frac{397}{500}\frac{216}{383}
 =\frac{4999}{47875}>0.
\tag{19}
\]

Differentiating (14), with (17), now proves

\[
 F''(h)=\cos h\left(1-\frac{2VT}{w}\right)
       +\sin h\{1-T+T''\}>0,
\tag{20}
\]

where the functions on the right are evaluated at `Theta+h`.
This is one continuous strict-convexity proof on the entire feasible
interval, with no angular subdivision.

Since `F(0)=0`, convexity gives

\[
 F(h)\le\max\{0,F(h_{\max})\}.
\tag{21}
\]

Together with (14), it proves the two endpoint alternatives in
Section 1. At the second endpoint `V(Theta+h_max)=1/2`, so (9)
becomes exactly

\[
 b_G'=0,\qquad a_G'=\sqrt{q-1/4}-\tfrac12.
\tag{22}
\]

If `0<h<h_max`, inequality (21) is strict. The chosen endpoint
therefore has strict pair slack. At the aligned endpoint, lower
A's primary slightly while keeping its tangent and frame fixed.
At the zero-G endpoint, lower it slightly and adjust `h_max`
continuously to retain `V(Theta+h_max)=1/2`; `V'=-U<0` makes
this possible. The strict HG0 slack persists. In either case A's
corner value can be made strictly less than q. Any circle loss at
the other middle point is unchanged.

If the original lifted point is already at `h=h_max`, it is already
the zero-G endpoint. No strictness is asserted merely from relabeling
that boundary. This endpoint must be handled by its retained shared
cycle constraints.

An earlier strict A-corner loss is not erased by the temporary lift.
If A originally has corner value below q and `h>0`, lifting its
primary strictly increases `V(Theta+h)`, because
`cos(Theta+h)>0`. Original feasibility gave `V>=1/2`, so after
the lift `V>1/2` and `0<h<h_max`. The strict endpoint comparison
just proved therefore recreates a corner value strictly below q for
A. If `h=0`, skip the lift and retain A's original aligned
inequality and corner. A strict loss on the other middle point is
unchanged in either case. This includes a loss supplied by the
preceding AB comparison.

## 5. A tangent of at least 1/2 forces direct alignment globally

For `b>=1/2`, (15) strengthens to `Y>=1` and `P<177/250=.708`.
Feasibility `V(z)>=1/2` implies `sin z<.208`. Since

\[
 \sin(21/100)\ge\frac{21}{100}
                 -\frac{(21/100)^3}{6}
               >\frac{26}{125}=.208,
\]

the whole feasible interval has `z<21/100`. We also have

\[
                              T(z)<849/1000.
\tag{23}
\]

Here is a monotonicity justification retaining the radius dependence.
In the sorted frontier range, increasing b decreases R and increases
`U(z)`, since `dU/db=cos z-(Y/R)sin z>0`. Formula (12) shows
that T decreases. It also decreases with z by (17). At fixed b,z,

\[
                 \frac{\partial T}{\partial q}
                  =\frac{1-T\sin z}{2Rw}>0,
\tag{24}
\]

using `T<1`. Thus the maximum in (23) occurs at `q=Q,b=1/2,z=0`.
At that point `P>.707`, because `1.707^2+1<Q`, and

\[
 Q-(707/1000)^2<(1849/1000)^2.
\]

This proves (23) by positive squaring.

For `0<h<.21`, `sin h>.99h` and `1-cos h<=h^2/2`. Thus

\[
 -F(h)>(151/1000)\sin h-(1-\cos h)
         >\left(\frac{14949}{100000}-\frac{21}{200}\right)h
         =\frac{4449}{100000}h>\frac h{25}.
\tag{25}
\]

Equation (14) gives the claimed strict aligned composite.

## 6. The smaller tangent threshold also aligns in the one-tenth band

For `b>=67/200`, the same monotonicities give

\[
             T(\Theta+h)\le T_{Q,67/200}(h).
\]

Write `P_0=sqrt(Q-(167/200)^2)-1`. Exact positive squaring gives

\[
 .793<P_0<.794,
\]
\[
 Q-(167/200)^2-(1793/1000)^2=\frac{1763}{500000},
\]
\[
 (1794/1000)^2+(167/200)^2-Q=\frac{61}{1000000}.
\tag{26}
\]

On `0<=h<=1/10`, the worst-case scalar satisfies

\[
 V\ge\frac{793}{1000}\frac{199}{200}
                  -\frac{167}{200}\frac1{10}
       =\frac{141107}{200000},
\]
\[
 U\le\frac{397}{5000}+\frac{167}{200},\qquad
 w<\frac{37}{20},\qquad T>\frac{187}{200}.
\tag{27}
\]

The squared reserve for the bound on w is
`187185449/40000000000`. The T bound follows from
`T=(2P_0+1)/(w+U)`; its cleared reserve using (27) is
`643/500000`. Consequently

\[
 -T'=\frac{VT}{w}>\frac7{20},
\qquad
 \frac{141107}{200000}\frac{187}{200}\frac{20}{37}
                 -\frac7{20}=\frac{487009}{74000000}>0.
\tag{28}
\]

At zero `T(0)<489/500=.978`; the positive-square reserve using
`P_0>.793` is `109/500000`. Integration therefore gives
`T(h)<.978-.35h`. Substitution in (14) yields

\[
 -F(h)>\sin h\left(\frac{11}{500}+\frac7{20}h\right)
                          -(1-\cos h)
          \ge\frac{1381}{200000}h>\frac h{150}.
\tag{29}
\]

The middle inequality follows directly from
`sin h>=h-h^3/6`, `1-cos h<=h^2/2`, and `h<=1/10`.
Thus the small-band result is a corollary of the same exact scalar,
not a substitute for the full-range boundary reduction.

## 7. Joining the AB comparison and recording the remaining endpoint

Suppose both remaining outer zero differences are nonnegative,
the original quarter owners are GA0 and BT2, either transverse AB
owner is retained, and the H/D ordering is that in the cited
three-zero note. On a canceling outer side use its effective cap
from that note. On a noncanceling HG0 or TD2 side use (5).
Every resulting parameter belongs to `(.434,.915)`, so the same
AB comparison gives a common A/B frame and `b_A+b_B>=1`.

At least one of these middle tangents is at least `1/2`. A
canceling side then aligns by the cited positive transport, and a
noncanceling side aligns by Section 5. The aligned inequality forces
its primary above `1.1` and its tangent below `.665`, exactly as in
Section 7 of that note. The other tangent is consequently above
`.335`. Its canceling owner aligns as before; its noncanceling owner
reduces by Section 4 to alignment or to one zero-transverse outer
endpoint. Thus at most one such endpoint remains, and the opposite
side is already aligned.

For the G endpoint, the exact retained five-center and G conditions
are as follows. Keep A/B's common frame zero, H's frame Theta,
D's frame `-u`, and E between H and D, with

\[
 \alpha=\Theta+u=\delta+\epsilon\le7/10,
 \qquad \Theta,u,\delta,\epsilon\ge0.
\tag{30}
\]

Put `R_0=sqrt(q-1/4)`. Besides all retained circle and sign
conditions, the endpoint satisfies

\[
\begin{split}
 &(a_A-\tfrac12)\cos(\Theta+h)
             -(b_A+\tfrac12)\sin(\Theta+h)=\tfrac12,\\
 &b_H\ge\tfrac12+\tfrac12\cos h-(R_0-1)\sin h,\\
 &a_B\cos u-b_B\sin u+b_D\ge1+W(u),\\
 &b_A+b_B\ge1,\qquad b_B<.665,\quad b_A>.335,\\
 &a_D+a_E\sin\delta+b_E\cos\delta\ge W(\delta),\\
 &a_H+a_E\sin\epsilon-b_E\cos\epsilon\ge W(\epsilon),\\
 &0\le\Theta+h<2/5.
\end{split}
\tag{31}
\]

There are two useful further restrictions when this endpoint is
chosen only after applying every available direct alignment. Its
middle tangent may be assumed below `1/2`, since Section 5 otherwise
aligns it as well. Thus `.335<b_A<.5`. If the AB sum is larger than
one, decrease B's tangent to `b_B'=1-b_A`. This preserves the aligned
B--D hard inequality because `u>=0`, improves B's circle, and leaves
all H/D/E data fixed. Accordingly the remaining endpoint may assume

\[
 b_A+b_B=1,\qquad .335<b_A<.5<b_B<.665.
\tag{32}
\]

It also has `h>1/10`. For `0<=h<=1/10`, `R_0-1<.915` and the
second line of (31) would give

\[
 b_H\ge\tfrac12+\tfrac12(1-h^2/2)-.915h
       \ge\tfrac12+\frac{199}{400}-\frac{183}{2000}
       =\frac{453}{500}=.906,
\]

contradicting the sorted H circle bound `b_H<.9`. Thus the unresolved
endpoint is a concrete continuous branch with
`1/10<h<=Theta+h<2/5` and (30)--(32).

The last two mixed projections are the unchanged original DE3 and
EH1 when those hard-owner hypotheses are imposed. The reflected
endpoint has T transverse zero. A subsequent exclusion must retain
this shared A/B/D/E system; the H--G--A pair alone is not excluded
by this note.

The original total G-to-D frame spread need not be preserved when
h is increased to its endpoint. The construction keeps alpha at
most `.7` and `Theta+h<.4`, but it may give `h+alpha>.7`.
A downstream theorem that requires `h+alpha<=.7` must therefore
retain the additional boundary `h=.7-alpha` instead of silently
discarding it. The radius lower-bound route may use the larger
necessary endpoint domain (30)--(31) if its endpoint theorem proves
that entire domain impossible.

Negative noncanceling outer errors, other quarter or mixed owners,
and other frame/sign orders are not supplied as hypotheses here.
This note does not assert a global mismatch contraction.
