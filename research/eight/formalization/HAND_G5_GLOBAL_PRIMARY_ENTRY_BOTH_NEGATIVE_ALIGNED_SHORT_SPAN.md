# The two aligned negative primary endpoints have span below .21

## 1. Original states and actual owners

Use the hypotheses of
[the two-negative aligned span theorem](HAND_G5_GLOBAL_PRIMARY_ENTRY_BOTH_NEGATIVE_ALIGNED_SPAN.md),
and retain its notation
\[
 Q=9789/2500,\quad K=13/12,\quad
 m=2-\sqrt{Q/2},\quad 0<t,u<9/100.
\tag{1}
\]
Thus HG and TD are aligned, GA1 and BT3 are actual negative
primaries whose alternatives GA0 and BT2 are unavailable,
and either AB0 or AB2 is an actual witness. The signed
states of H,A and B,D have their normal signs. G and T
need no additional sign input: their aligned transverse
witnesses force the signs used in the cited theorem.
All states are sorted, avoid the true core, and are
contained at one actual ceiling q<=Q. Their real frames
lie in an interval of length at most 7/10.

**Stronger span theorem.** On these original states,
\[
                        \theta_H-\theta_D<21/100.
\tag{2}
\]
There is no E state or E witness in this assertion. No state,
frame, circle, or weak contact is changed. This strengthens
the cited .22 conclusion by one whole-rectangle estimate;
it introduces no angular subdivision or list of sampled cases.

## 2. The same actual circle caps

The two actual negative-primary inequalities and their
unavailable alternatives give the primary corner lower bounds
\[
 X_A\ge X(t),\qquad X_B\ge X(u),\qquad
 X(z)=1+m\cos z+K\sin z.
\tag{3}
\]
Consequently their actual tangent corners are at most
\[
                 Y(z)=\sqrt{Q-X(z)^2}.
\tag{4}
\]
The cited proof supplies, on the whole interval [0,.09],
\[
 .6007859<m<.600786,
 \qquad 1.6007859<X(z)<1.697,
 \qquad 1.018<Y(z)<1.163222.
\tag{5}
\]

Suppose instead that alpha=theta_H-theta_D>=.21. Then
\[
              v=\theta_A-\theta_B=\alpha-t-u>.03.
\]
The exact AB0 inequality, with its negative error -v,
implies
\[
             Y(t)+\{Y(u)-1\}\cos v-X(u)\sin v-1\ge0.
\tag{6}
\]
Both sine and cosine have their usual positive signs on
the actual interval. Since Y(u)>1, the left side decreases
strictly with v. It suffices to contradict (6) at
\[
                         v=.21-t-u\in[.03,.21].
\tag{7}
\]
For actual AB2 the same necessary expression has t and u
interchanged. Thus one estimate on the entire square
[0,.09]^2 proves the result for either actual owner.

## 3. A simple polynomial tangent cap

Let C_j and S_j denote the alternating Taylor polynomials
of cosine and sine through degree j. Define
\[
 \begin{split}
 X_L(z)&=1+.6007859C_6(z)+KS_7(z),\\
 Y_U(z)&=1.163222-1.4908z-z^2.
 \end{split}
\tag{8}
\]
On [0,.09], X_L<=X and Y_U>1. The following single
polynomial proves that Y<=Y_U throughout that interval:
\[
                  P(z)=Y_U(z)^2+X_L(z)^2-Q.
\tag{9}
\]
Write P(z)=sum p_i z^i. Its first two coefficients are
\[
             p_0=.00000091892281,
             \qquad p_1=.0001067348.
\tag{10}
\]
Direct rational multiplication of (8) gives the compact
coefficient bound
\[
 p_2+\sum_{\substack{i\ge3\\p_i<0}}
                       p_i(.09)^{i-2}>.1079.
\tag{11}
\]
All positive higher coefficients may be discarded in a
lower bound. Hence P(z)>=p_0+p_1z+.1079z^2>0 on the
entire interval. Since X_L<=X and Y_U>0,
\[
                Y(z)^2=Q-X(z)^2
                    \le Q-X_L(z)^2<Y_U(z)^2.
\tag{12}
\]
Every inequality in (10)--(12) is strict even at z=0.

## 4. One whole-square polynomial certificate

Put
\[
 t=\frac9{200}(1+x),\qquad
 u=\frac9{200}(1+y),\qquad v=\frac{21}{100}-t-u,
                 \qquad -1\le x,y\le1.
\tag{13}
\]
Consider the explicit rational polynomial
\[
 \mathcal P(x,y)=1-Y_U(t)
     -\{Y_U(u)-1\}C_4(v)+X_L(u)S_7(v).
\tag{14}
\]
Its total degree is at most 14. Equations (5),(7),(8),(12)
and the alternating Taylor inequalities give
\[
 Y(t)+\{Y(u)-1\}\cos v-X(u)\sin v-1
                           \le-\mathcal P(x,y).
\tag{15}
\]
In particular the cosine coefficient is positive, and both
factors in the negative sine term have positive lower bounds;
no inequality has been multiplied by an unknown sign.

Here is a complete coefficient specification and a compact
norm certificate for (14). Write
\[
       \mathcal P(x,y)=\sum_{a,b}p_{ab}x^ay^b
                    =\sum_{i,j}c_{ij}T_i(x)T_j(y),
\tag{16}
\]
where T_i are the ordinary Chebyshev polynomials. For
nonnegative a,i define
\[
 d_{a i}=
 \begin{cases}
 2^{-a}\binom{a}{a/2},&i=0,\ a\text{ even},\\
 2^{1-a}\binom{a}{(a-i)/2},&i>0,\ i\le a,\ a-i\text{ even},\\
 0,&\text{otherwise}.
 \end{cases}
 \qquad c_{ij}=\sum_{a,b}p_{ab}d_{a i}d_{b j}.
\tag{17}
\]
Thus every coefficient is specified by the single factored
polynomial (14) and the elementary identity (17), without
any stored coefficient rows. Exact rational arithmetic gives
\[
        c_{00}>.01085336,
       \qquad \sum_{(i,j)\ne(0,0)}|c_{ij}|<.00814616.
\tag{18}
\]
The two bounds in (18) have respective positive reserves
greater than 2.49 times 10^-9 and 3.19 times 10^-9.
They follow by expanding only (8),(13),(14) and using (17).
Together with |T_i(x)|<=1 on [-1,1], they prove on the
entire closed square
\[
            \mathcal P(x,y)>.01085336-.00814616
                              =.0027072>.0027.
\tag{19}
\]
This is one polynomial identity and one coefficient norm on
one whole rectangle. There is no grid, subdivision, angle
sample, interval ownership table, or omitted boundary face.

Equations (15),(19) contradict the actual AB0 requirement
(6). Interchanging t and u gives the identical contradiction
for actual AB2. This proves (2), including every original
weak witness tie. All lower-degree and norm comparisons
in this proof are rational comparisons, with the explicit
definitions (8)--(11),(13)--(18) sufficient to reproduce
them independently.

## 5. Same-radius use before the second primary conversion

Restore a nonpositive E on its true-core boundary or its
actual outer q-circle, with q_L=19577/5000<=q<=Q and
the usual actual DE/EH owner sets. The first-side assembly
in Section 5 of the cited .22 span theorem remains valid,
and reaches actual GA0 while retaining negative BT3 and
aligned TD. That assembly decreases H's frame and keeps
D's frame fixed, so the stronger conclusion (2) persists
at its output. It also leaves actual EH0, or actual positive
EH1 of error at most .22. The genuine local contact bounds
at that output retain b_H>.844 and a_H<1.

Those are actual same-radius inputs for an opposite-side
D/T/E construction. This note supplies just the strict
short-span input to that construction. It does not invoke
reflection of the E sign or identify any transported state
with its original ancestor.
