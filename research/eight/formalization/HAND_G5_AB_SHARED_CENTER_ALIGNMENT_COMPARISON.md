# A shared-center alignment comparison for both original AB witnesses

## 1. Exact branch and conclusion

Let `0<q<=Q=9789/2500`. Retain the original strict-sign roles

\[
 (y_H,y_G,y_A,y_B,y_T,y_D)
 =(b_H,-b_G,b_A,-b_B,b_T,-b_D),\qquad b_i\ge0,
\]

their own-frame primary inequalities `a_i>=b_i`, and their original
corner bounds

\[
 (a_i+1/2)^2+(b_i+1/2)^2\le q.
\tag{1}
\]

Assume that HG and TD are aligned and retain either original
transverse witness on each. Retain original GA axis 0, original BT
axis 2, and either original AB transverse axis 0 or 2. The real frames
are

\[
 \theta_H=\theta_G=t,\quad \theta_A=0,\quad \theta_B=d,
 \quad\theta_T=\theta_D=d-u=t-\alpha,
\]
\[
 0\le t,u\le\alpha\le7/10,\qquad d=t+u-\alpha.
\tag{2}
\]

Thus both A and B frames lie between the fixed G and T frames.
The original E state and its two neighboring constraints may be
retained unchanged. No claim that every candidate has the ordering,
owners, or two zero alignments in (2) is made.

This note gives a continuous comparison, for both signs of d and both
original AB witnesses, to an aligned AB path with the same G and T
centers and frames. The new nonnegative quarter tilts `t',u'` satisfy
`t'+u'=alpha`. When `d!=0`, the aligned path has strict AB slack. For
`d>0` its transverse slack is greater than `9d/200`.

The comparison also constructs A and B satisfying the stated corner,
sorting, sign, frame and original neighboring-SAT constraints. All
other centers remain fixed. It is a statement about this necessary
edge system. Additional global packing conditions, if required by a
later theorem, must be checked separately. In particular, it is not a
claim that a bad-mismatch domain is preserved.

All decimals below are exact rational numbers.

## 2. Cap parameters use the unchanged G and T centers

Write

\[
 W(z)=\frac{1+\cos z+\sin z}{2}\qquad(0\le z\le7/10).
\]

The two fixed zero edges give

\[
 b_H+b_G\ge1,\qquad b_T+b_D\ge1.
\]

The corner and sorting bounds imply `b_i<.9` and
`|(a_i,b_i)|<U=283/200`. Hence `b_G,b_T>.1`. The two actual
hard-quarter witnesses are

\[
 a_A\cos t-b_A\sin t\ge W(t)+b_G,
 \qquad
 a_B\cos u-b_B\sin u\ge W(u)+b_T.
\tag{3}
\]

They also give `b_G,b_T<U-1=.415`. Set

\[
 D_A=b_G+\frac12,\qquad D_B=b_T+\frac12;
 \qquad .6<D_A,D_B<.915.
\tag{4}
\]

These parameters retain the actual middle centers. Replacing them by
`1.5-b_H` and `1.5-b_D` would be a further necessary relaxation,
but is unnecessary here.

For either fixed D in (4), define

\[
 C(\theta)=D+\cos\theta,\quad
 w(\theta)=\sqrt{q-C(\theta)^2},
\]
\[
 X(\theta)=C(\theta)\cos\theta+w(\theta)\sin\theta,
 \qquad
 L(\theta)=w(\theta)\cos\theta-C(\theta)\sin\theta.
\tag{5}
\]

Use subscripts A and B for the two fixed parameters. The actual
quarter witnesses imply `a_A>=1+b_G` and `a_B>=1+b_T`, so

\[
 q\ge(D_A+1)^2+\frac14,
 \qquad q\ge(D_B+1)^2+\frac14.
\tag{6}
\]

Thus every radicand in (5) is positive throughout `[0,.7]`.
Also `w^2-sin^2(theta)>=q-(D+1)^2>=1/4`. The identities

\[
 X^2+L^2=q,\qquad
 (X-1)\cos\theta-L\sin\theta=D,
\]
\[
 L'=-X\frac{w-\sin\theta}{w}<0
\tag{7}
\]

hold on this full interval. In particular each cap decreases.

If `Z_A=b_A+1/2` and `Z_B=b_B+1/2`, (3) gives

\[
 Z_A\le L_A(t),\qquad Z_B\le L_B(u).
\tag{8}
\]

For example, rotate the A corner vector by t. Its first coordinate
is at least `D_A+cos t`; the original circle bounds its second
coordinate by the corresponding square root. Rotating back gives
(8). Consequently both original caps in (8) are at least `1/2`.
Every cap, feasible or otherwise, satisfies

\[
 L(\theta)\le L(0)=\sqrt{q-(D+1)^2}
 <\sqrt{Q-(8/5)^2}<233/200=1.165.
\tag{9}
\]

## 3. A uniform derivative bound at every feasible cap

Whenever `L(theta)>=1/2`,

\[
                         -L'(\theta)>6/5.
\tag{10}
\]

This assertion is uniform in the actual q and D. Put `Z=L(theta)`
and `X=X(theta)`. Equation (7) and `D>=3/5` imply

\[
 X\ge8/5,\qquad
 \tan\theta\le\frac{X-8/5}{Z}.
\]

Also

\[
 -L'=X\frac{Z+(X-1)\tan\theta}{Z+X\tan\theta}.
\]

The last expression decreases with `tan theta`. Substituting its
upper bound, and then using `Z^2>=1/4`, gives

\[
 -L'\ge
 X\frac{Z^2+(X-1)(X-8/5)}{Z^2+X(X-8/5)}
 \ge
 X\frac{1/4+(X-1)(X-8/5)}{1/4+X(X-8/5)}.
\tag{11}
\]

The second substitution is valid because the rational expression
increases with `Z^2`. After multiplication by the positive
denominator, the difference of the last fraction from `6/5` is
the polynomial

\[
 p(X)=X^3-\frac{19}{5}X^2+\frac{377}{100}X-\frac3{10}.
\]

Let `y=X-37/20>=-1/4`. Direct expansion gives

\[
 p(X)=\frac9{8000}-\frac9{400}y+\frac74y^2+y^3
 \ge\frac9{8000}-\frac9{400}y+\frac32y^2
 \ge\frac{333}{320000}>0.
\]

This proves (10) without an angle subdivision or a state table.

## 4. Exact AB cap bounds retain the original witness

The two original AB inequalities in corner coordinates are

\[
\begin{array}{ll}
 0:&Z_A+X_B\sin d+Z_B\cos d
       \ge1+\cos d+(\sin d)_+,\\
 2:&X_A\sin d+Z_A\cos d+Z_B
       \ge1+\cos d+(\sin d)_+.
\end{array}
\tag{12}
\]

These identities include the support-width cusp exactly. Since
`d<=t,u`, the same circle calculation used in (8) bounds the
rotated term in the first line by

\[
 X_B(u)\sin d+L_B(u)\cos d.
\]

Indeed, in B's cap coordinates the coefficient pair is
`(-sin(u-d),cos(u-d))`; its first entry is nonpositive and its
second positive. The upper circle support therefore occurs at
the retained boundary `C_B(u)`, not at an unrelated corner.
The second original witness has the reflected statement.

Consequently, an original axis 0 witness implies

\[
 F_0:=L_A(t)+X_B(u)\sin d+L_B(u)\cos d
             -1-\cos d-(\sin d)_+\ge0.
\tag{13}
\]

Axis 2 implies the same inequality with A,t and B,u interchanged.
It therefore suffices to prove both signs for (13).

## 5. Negative AB error: compare to the A-frame alignment

Suppose `d<0` and put `v=u-d=alpha-t`. Then `0<=u<v<=.7`.
Define, for the unchanged B parameter,

\[
 g_v(C)=\cos v\sqrt{q-C^2}-\sin v\,C.
\]

For `C>=D_B+cos v`,

\[
                              g_v'(C)<-1.
\tag{14}
\]

Here is a uniform algebraic check. Put `c=cos v,s=sin v`.
The desired inequality is
`cC>(1-s)sqrt(q-C^2)`. Both sides are nonnegative. Since
`C>=3/5+c`, `q<=Q`, and `c+s>=1`,

\[
\begin{split}
 2C^2-q(1-s)
 &\ge 2(3/5+c)^2-Q(1-s)\\
 &\ge2c^2-\frac{3789}{2500}c+\frac{18}{25}>\frac25>0.
\end{split}
\]

The final quadratic comparison is its completed-square bound.
Multiplication by `1-s>0` proves the squared form of (14).

The rotated B cap in (13) is exactly `g_v(C_B(u))`, while
`g_v(C_B(v))=L_B(v)`. Integrating (14) gives

\[
 g_v(C_B(u))-L_B(v)<-(\cos u-\cos v).
\]

The identity

\[
 \cos u-\cos v
 =2\sin((u+v)/2)\sin((v-u)/2)
 \ge1-\cos(v-u)
\]

therefore proves

\[
 0\le F_0<L_A(t)+L_B(v)-2.
\tag{15}
\]

Thus the aligned choice is `(t',u')=(t,u-d)`. Its AB
transverse slack is strictly positive. Reflection gives
`(t',u')=(t-d,u)` for an original axis 2 witness.

## 6. Positive AB error: compare to the B-frame alignment

Suppose `d>0` and put `v=t-d=alpha-u`. Since L decreases and
the original A cap is feasible, `L_A(theta)>=1/2` throughout
`v<=theta<=t`. Equation (10) gives

\[
 L_A(t)-L_A(v)<-\frac65d.
\]

The actual B cap satisfies `L_B(u)>=1/2` and
`X_B(u)<=sqrt q<99/50`. Thus

\[
\begin{split}
 F_0-&\{L_A(v)+L_B(u)-2\}\\
 &=L_A(t)-L_A(v)+(X_B(u)-1)\sin d
                  +(L_B(u)-1)(\cos d-1)\\
 &<-\frac65d+\frac{49}{50}d+\frac14d^2
 \le-\frac9{200}d.
\end{split}
\tag{16}
\]

Only `sin d<=d`, `1-cos d<=d^2/2`, and `d<=7/10` were
used in the final step. Consequently

\[
 L_A(v)+L_B(u)-2>\frac9{200}d>0.
\tag{17}
\]

Here `(t',u')=(t-d,u)`. Reflection gives
`(t',u')=(t,u-d)` for original axis 2, with the same strict
reserve.

## 7. What the aligned comparison constructs

For the selected `t',u'`, put the new A and B frames at their
common aligned value and use the corner vectors

\[
 (X_A(t'),L_A(t')),\qquad (X_B(u'),L_B(u')).
\tag{18}
\]

Their squared norms are q. The two caps sum to more than two if
`d!=0`, and each is less than `1.165` by (9). Hence each exceeds
`.835`, so both new transverse coordinates are positive. The
new hard-quarter contacts are exact, with the same original
`b_G,b_T`, and their primaries exceed `1.1`. Sorting follows
also from `X>=1.6>L`. Both original aligned AB witnesses hold.
HG, TD, DE and EH are unchanged. Every condition explicitly
listed in Section 1 is therefore preserved in this edge system.

For `d!=0`, continuity permits replacing q by some strictly
smaller common value in the two cap constructions (18), while
keeping the same other centers, tilts and hard-quarter contacts.
The strict AB sum, strict sorting, and positive transverse
coordinates persist for a sufficiently small reduction. Thus
both A and B corner values can be made strictly less than the
original q. This strict loss can be useful in a later equality
argument whose hypotheses apply to the constructed edge system.

The original E center and the total H-to-D frame span are unchanged.
No assertion about additional nonneighbor packing conditions is
hidden in this construction.

## 8. Mismatch bookkeeping and remaining domain conditions

If the remaining hard signs are `delta,epsilon>=0` with
`delta+epsilon=alpha`, the forward mismatch in this branch is

\[
 S=|d|+u+\delta,
 \qquad S_{\rm aligned}=u'+\delta.
\]

The exact changes are:

| Original AB axis | Sign of d | `t'` | `u'` | `S_aligned` |
| --- | --- | --- | --- | --- |
| 0 | negative | `t` | `u-d` | `S` |
| 2 | negative | `t-d` | `u` | `S-|d|` |
| 0 | positive | `t-d` | `u` | `S-d` |
| 2 | positive | `t` | `u-d` | `S-2d` |

Thus no forward mismatch increases. If a minimization is required
to remain in `S>=s_0`, an alignment with a decreased S cannot
simply discard the boundary `S=s_0`. The same issue applies to
an imposed reflected mismatch condition. For the explicit
reflected quantity `|d|+t+epsilon`, the respective decreases in
the four rows are `|d|,0,2d,d`.

For a radius lower bound, a legitimate reduction may instead use
the constructed descendant without imposing the old bad-S
condition. Such an application must verify its downstream
hypotheses. This note leaves other GA/BT owners, other frame
orders, nonzero HG/TD errors and any additional global packing
conditions as separate obligations. It does not assert the
global G4/G5 contraction.
