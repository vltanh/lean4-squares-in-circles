# A negative BT1 error disappears from a dual bound when its exact prefix gives a high T primary

## 1. Conditional prefix and conclusion

Put
\[
 Q=9789/2500,\quad R=\sqrt Q,\quad
 c_0=\sqrt{Q/2}-1/2,\quad a_0=\sqrt{Q-1/4}-1/2,
 \quad \kappa=49/50,\quad K=13/12.
\tag{1}
\]
Suppose an exact reduced AB--BT1 prefix supplies
\[
 b_A+\sec z\,a_T\ge R_1(z),\qquad
 R_1(z)=\frac32+\frac12\sec z+K\tan z,
 \quad 0\le b_A\le c_0,
 \quad 0\le z\le7/10.
\tag{2}
\]
Retain T's sorted corner disk at Q. It follows directly that
\[
 a_T\ge A(z):=\frac12+L\cos z+K\sin z,
 \qquad L:=\frac32-c_0.
\tag{3}
\]
The condition (2) is part of the theorem. A charge comparison
for some other original prefix does not by itself establish
(2) or the primary restriction (3).

Let c be any fixed TD multiplier with
\[
                              3/5\le c\le\kappa.
\tag{4}
\]
For negative TD error -u, `0<=u<=7/10`, the T force is
\[
 (\kappa\sec z,c)\quad\text{for TD0},\qquad
 (\kappa\sec z-c\sin u,c\cos u)\quad\text{for TD2}.
\tag{5}
\]
Set eta=0 for TD0 and eta=u for TD2, and write
\[
 f(z)=\kappa\sec z-c\sin\eta,
 \qquad B=c\cos\eta.
\]
Define the exact restricted T support
\[
 S(z)=\max\{f(z)a+Bb:
       a\ge A(z),\ a\ge b\ge0,
       (a+1/2)^2+(b+1/2)^2\le Q\}.
\tag{6}
\]
Its domain is the interval where A(z)<=a_0.

**High-primary dual transport.** On that whole interval,
\[
                       J(z):=-z+\kappa R_1(z)-S(z)
\tag{7}
\]
is strictly increasing. In particular
\[
 J(z)\ge2\kappa-
       \left[R\sqrt{(\kappa-c\sin\eta)^2+c^2\cos^2\eta}
                  -\frac{\kappa-c\sin\eta+c\cos\eta}{2}\right].
\tag{8}
\]
The right side simply forgets the primary restriction at z=0
and uses the full shifted-circle support.

Thus an exact prefix satisfying (2) permits its negative BT1
error to be set to zero in the resulting dual lower bound,
for either TD owner. All D and E terms, their errors, their
actual radial kinds and their chosen DE multiplier stay
unchanged. The TD and DE weights may depend on the unchanged
tail parameters; they must be fixed during this z comparison.
The lemma supplies no separate lower bound for that remaining
TD--DE tail.

## 2. The feasible prefix interval and its cap

Positive squaring gives
\[
 .899<c_0<.8993,\qquad .6007<L<.601.
\tag{9}
\]
The two reserves for the c_0 comparisons are respectively
`599/1000000` and `24049/100000000`.
On `[0,.7]`,
\[
 A'(z)=K\cos z-L\sin z
 >K\frac34-.601\frac{13}{20}
 =\frac{8437}{20000}>0.
\tag{10}
\]
At z=13/40, the quadratic cosine and cubic sine lower
polynomials give
\[
 A(13/40)>\frac{814959781}{576000000}.
\]
The corner square of this last number with transverse zero
exceeds Q by
\[
 \left(\frac{814959781}{576000000}+\frac12\right)^2
                 +\frac14-Q
 =\frac{362172903567961}{331776000000000000}>0.
\tag{11}
\]
Consequently the feasible domain in (6) is `[0,z_max]` with
\[
                       0<z_{\max}<13/40.
\tag{12}
\]
It contains 1/10, since A(1/10)<1.21<a_0.

Put
\[
 X(z)=A(z)+\frac12=1+L\cos z+K\sin z,
 \qquad Z(z)=\sqrt{Q-X(z)^2}.
\tag{13}
\]
Throughout (12),
\[
 \frac85<X<\frac{383}{200},\qquad
 \frac12\le Z<\frac{233}{200},\qquad X'>\frac{83}{100}.
\tag{14}
\]
The final comparison follows from
\[
 K\frac{3031}{3200}-.601\frac{13}{40}-\frac{83}{100}
                       =\frac{763}{960000}>0,
\tag{15}
\]
using `cos z>=3031/3200`, `sin z<=13/40` on (12).
The other bounds follow from X(0)>8/5, the defining
transverse lower bound Z>=1/2, and positive squaring.
In particular every point allowed by (6) is strictly sorted.

## 3. The support reaches its primary boundary before one tenth

For the forces in (5),
\[
 f\ge\frac{343}{1000}>0,\quad
 B\ge\frac9{20},\quad f<\frac{21}{20},\quad
 0\le f'=\kappa\sec z\tan z<\frac9{25}.
\tag{16}
\]
The derivative comparison has exact reserve
\[
 \frac9{25}-\kappa\frac{13/40}{(3031/3200)^2}
                         =\frac{23401}{4687225}>0.
\]
The free circle support has primary corner
\[
                    X_f(z)=R\frac{f(z)}{\sqrt{f(z)^2+B^2}}.
\tag{17}
\]
Its transverse corner exceeds 1/2: indeed
`B/f>3/7>5/19> (1/2)/sqrt(Q-1/4)`.
Thus the lower transverse endpoint cannot be the maximizer
except when the feasible cap itself ends at Z=1/2.

The support (6) is therefore the free circle support when
X_f>=X, and the point `(a,b)=(X-1/2,Z-1/2)` otherwise.
There is at most one transition between these cases.
To see this, differentiate (17) and use
\[
 \frac{2R}{3\sqrt3}<\frac{763}{1000},\qquad
 \left(\frac{763}{1000}\right)^2-\frac{4Q}{27}
                   =\frac{18721}{9000000}>0.
\]
The elementary maximum of `t^2/(1+t^2)^(3/2)` gives
\[
 0\le X_f'\le\frac{2R}{3\sqrt3}\frac{f'}f
 <\frac{763}{1000}\frac{9/25}{343/1000}
 =\frac{981}{1225}<\frac{83}{100}<X'.
\tag{18}
\]
The difference X-X_f is strictly increasing.

Moreover X_f<17/10 for z<=1/10. First note
\[
 \frac{\kappa\sec z}{c}<\frac74,\qquad
 \tan(\eta/2)<\frac25.
\]
Their product is less than one. Therefore
\[
 \frac{f}{B}
 =\frac{\kappa\sec z/c-\sin\eta}{\cos\eta}
 \le\frac{\kappa\sec z}{c}
 \le\frac{\kappa\sec z}{3/5}.
\tag{19}
\]
Using `cos z>=199/200` up to one tenth, the claimed
bound follows from the positive-square reserve
\[
 \left(\frac{17}{10}\right)^2
       \left\{\kappa^2+\frac9{25}(199/200)^2\right\}
          -Q\kappa^2=\frac{4503577}{100000000}>0.
\tag{20}
\]
But
\[
 X(1/10)-\frac{17}{10}
 >1+\frac35\frac{199}{200}
       +K\left(\frac1{10}-\frac1{6000}\right)-\frac{17}{10}
 =\frac{371}{72000}>0.
\tag{21}
\]
By (18), the support is on the primary boundary for all
z>=1/10, and any transition occurs strictly before it.

## 4. The free-support branch has positive derivative

On this branch,
\[
 S=R\sqrt{f^2+B^2}-\frac{f+B}{2}.
\]
Differentiating (7), with P_f=X_f-1, gives exactly
\[
 J'(z)=\frac{\kappa K-1-\kappa P_f\sin z+\sin^2z}
                      {\cos^2z}.
\tag{22}
\]
The preceding section places this branch below 1/10 and
gives P_f<7/10 there. The quadratic
`kappa K-1-(7/10)kappa s+s^2` decreases for `0<=s<=1/10`.
Its value at 1/10 is
\[
                  \kappa(K-7/100)-99/100=23/7500>0.
\tag{23}
\]
Hence J'>0 on the entire free-support branch.

## 5. The primary-boundary branch has increasing positive derivative

On this branch the prefix cancellation in (2)--(3) gives
\[
 J(z)=\kappa c_0-z
        +c\sin\eta\,(X-1/2)-c\cos\eta\,(Z-1/2).
\tag{24}
\]
We first prove a uniform curvature bound for Z. Since
`X''=1-X`, differentiation of (13) gives
\[
 -Z''=\frac{Q(X')^2-X(X-1)(Q-X^2)}{Z^3}.
\tag{25}
\]
The polynomial `F(X)=X(X-1)(Q-X^2)` decreases for X>=8/5
in (14). Indeed
\[
 F'(8/5)=-1121/12500<0,\qquad
 F''(8/5)=-16611/1250<0,
\]
and `F'''(X)=6-24X<0`. Thus
`F(X)<=F(8/5)=(24/25)(Q-64/25)`.
Equations (14),(25), and the exact reserve
\[
 Q(83/100)^2-\frac{24}{25}(Q-64/25)
                   -\frac45(233/200)^3
                     =\frac{6557357}{50000000}>0
\tag{26}
\]
give `-Z''>4/5` throughout the cap. Consequently
\[
\begin{aligned}
 J''&=-c(X-1)\sin\eta-cZ''\cos\eta\\
 &>c\cos\eta\left\{\frac45-
                       \frac{183}{200}\frac{13}{15}\right\}
 =\frac7{1000}c\cos\eta>0.
\end{aligned}
\tag{27}
\]

If this branch begins at z=0, its support condition implies
\[
 c\left(\sin\eta+\frac{X(0)}{Z(0)}\cos\eta\right)\ge\kappa.
\]
Since X'(0)=K, (24) gives
`J'(0)>=kappa K-1=37/600>0`.

If the branch begins at a transition z=s>0, then s<1/10
and the support condition is an equality. Therefore
\[
 J'(s)=\kappa K-1-\kappa L\tan s
 >\kappa K-1-\kappa(.601)\frac{1/10}{199/200}
 =\frac{7381}{2985000}>0.
\tag{28}
\]
By (27), the derivative remains positive to the end of
the feasible cap. Equations (22)--(28) prove that J is
strictly increasing, including its continuous transition.
This establishes (7)--(8).

The proof retains the exact same T circle and the exact
primary restriction from (2). Its only case distinction is
whether the circle support point lies inside that cap or
on its boundary. All bounds hold on whole intervals and
follow from the displayed derivatives and rational square
comparisons. No angle mesh, numerical minimum, or external
acceptance result is a premise.
