# A negative DE2 error also permits the long-EH1 outside transport

## 1. Same-radius theorem with explicit anchor hypotheses

Let
\[
 q_L=19577/5000,\quad q_L\le q\le Q=9789/2500,
 \quad h=7/10,\quad c_q=\sqrt{q/2}-1/2.
\tag{1}
\]
Retain sorted D,E,H with signs negative, nonpositive, positive,
respectively. D is on the outer q-circle. H is on that circle
and satisfies
\[
                       b_H>.844,\qquad a_H<1.
\tag{2}
\]
E is on its actual true-core boundary or outer q-circle. The
two actual witnesses are DE2 and EH1, with errors
\[
                 -n=\theta_E-\theta_D<0,
                 \qquad p=\theta_H-\theta_E>.22,
                 \qquad n,p\le h.
\tag{3}
\]
An anchor may first be raised to its q-circle at fixed tangent
if every other retained witness is unchanged or improved by
that primary lift. This condition is explicit: it holds for H
with aligned HG, and for D with TD2 or aligned TD. Original
outer boundary anchors need no such lift.

**Transport theorem.** Changing only E, moving its frame toward
H, reaches an actual EH0 witness, an EH1 error at most .22,
or DE alignment with remaining EH error \(p-n>.22\).
The E circle does not increase, E keeps its radial alternative,
and both signed variations decrease by the frame movement.
Every other state and witness is unchanged after any permitted
initial lift. In particular, if
\[
                          \theta_H-\theta_D<.22,
\tag{4}
\]
the aligned-DE alternative cannot occur before the short-EH stop.
The conclusion then joins the
[EH0 or short-EH1 negative-GA transport](HAND_G5_GLOBAL_PRIMARY_ENTRY_ALIGNED_HG_NEGATIVE_GA_EH0.md).

The outer-D hypothesis is used at a possible simultaneous
contact in Section 2. It is not inferred from mere containment.
This note preserves the original DE2 witness; it does not
reselect DE3 or assume that a different mixed-owner theorem
already applies. All decimals below are exact rationals.

## 2. The contact derivative and the sorted D bound

Write E as \((a,b)\) in unsigned own-frame coordinates and
put \(v=-da/db\). On the true-core and sorted outer arcs,
\(0\le v\le1\). Initially keep b fixed while moving E's frame
toward H by \(\tau\), so \(n,p\) both decrease at unit speed.
The EH1 slack decreases, and the DE2 slack increases. At the
first EH1 contact follow that contact on the same radial arc.
Exactly as in the
[DE3 outside transport](HAND_G5_GLOBAL_PRIMARY_ENTRY_LONG_EH_OUTSIDE_TRANSPORT.md),
the contact equation gives
\[
 \frac{db}{dp}=\beta
   :=\frac{(a-1/2)\cos p+(b+1/2)\sin p}
                 {\cos p+v\sin p}>0.
\tag{5}
\]
Thus b decreases as E moves toward H. Sorting improves, and
E stays on its same true-core or outer arc with nonincreasing
circle value. The core circle derivative is \(2(1-v)\ge0\).

The actual DE2 slack is
\[
             M=a_D\cos n-b_D\sin n+b-W(n),
 \qquad W(n)=(1+\cos n+\sin n)/2.
\tag{6}
\]
Along the EH contact its derivative is
\[
        \frac{dM}{d\tau}
          =(a_D-1/2)\sin n+(b_D+1/2)\cos n-\beta.
\tag{7}
\]
It suffices to prove this is positive at any possible first
boundary \(M=0\). At such a boundary put
\[
 Y=b+1/2,\quad L_n=1+\cos n-Y,
 \quad Z_n=\sqrt{q-L_n^2}.
\tag{8}
\]
The shifted D corner, rotated by n, has first component
\(L_n\) by (6) and positive second component \(Z_n\),
because D is on its q-circle. Consequently its term in (7) is
\[
                           Z_n-\sin n.
\tag{9}
\]
For \(Y\ge1/2\), this expression decreases with n throughout
the interval relevant here, including its algebraic extension
to h. Indeed its derivative is
\[
              -\{Z_n\cos n-L_n\sin n\}/Z_n<0.
\tag{10}
\]
One has \(L_n\le3/2\), \(Z_n>1.29\), and hence the numerator
is greater than
\[
                  1.29 C_6(h)-1.5S_5(h)
                           =487049093/24000000000>0.
\tag{11}
\]
The square reserve for \(Z_n>1.29\) is
\(q_L-(3/2)^2-1.29^2=13/10000\).
In particular, define
\[
                   C_q(Y)=\sqrt{q-(1+\cos h-Y)^2}-\sin h.
\tag{12}
\]
Then the D term in (7) is at least \(C_q(Y)\). This function
increases with Y on all states used below, since
\(1+\cos h-Y>0\).

## 3. The true-core E case

Every true-core E has \(a\le7/12\). Feasible EH1 with
\(a_H<1\) gives
\[
 Y\le(a_H-1/2)\sec p+(a-1/2)\tan p
       <\tfrac12(1.308)+\tfrac1{12}(.843)<.725.
\tag{13}
\]
Here \(\sec h<1.308\), \(\tan h<.843\) follow by the
alternating Taylor bounds. Thus \(b<.225<1/2\): E is on
the flat core, \(a=7/12\), and v=0. Formula (5) yields
\[
                  \beta=1/12+Y\tan p<.695.
\tag{14}
\]
On the other hand, (12) gives \(C_q(Y)\ge C_{q_L}(1/2)>.87\).
The latter positive-square comparison has the reserve
\[
 q_L-\{C_4(h)+1/2\}^2-\{S_5(h)+.87\}^2
                     =3205454966251/144000000000000>0.
\tag{15}
\]
The reserve in (14) is
\(.695-1/12-(.725)(.843)=59/120000\).
Thus (7) is strictly positive at a possible core-E boundary.

## 4. Outer E: the least H primary is the worst contact

Now E is outer. Put
\[
 X=a+1/2,\quad Y=b+1/2,\quad P=a_H-1/2,
 \quad P_0=\sqrt{q/2}-1,
\tag{16}
\]
so \(P_0\le P<1/2\). EH1 contact says
\[
        Y\cos p-(X-1)\sin p=P,\qquad X^2+Y^2=q.
\tag{17}
\]
With \(U=P-\sin p\), \(Z=\sqrt{q-U^2}\), the positive
solution is
\[
        X=Z\cos p-U\sin p,\qquad
        Y=Z\sin p+U\cos p.
\tag{18}
\]
Because \(v=Y/X\), (5) becomes
\[
                      \beta=X(1-\cos p/Z).
\tag{19}
\]
At fixed p, Y increases with P and beta decreases with P.
The first assertion follows from \(Y_P=X/Z>0\). For the
second, exact differentiation gives
\[
 Z^3\beta_P=-YZ(Z-\cos p)-XU\cos p<0.
\tag{20}
\]
If U is nonnegative this is immediate. Otherwise use
\(Y\ge1/2\), \(X<1.915\), \(-U<.246\), and \(Z>1.958\).
The negative term dominates with reserve
\[
       \tfrac12(1.958)(.958)-(1.915)(.246)
                              =58349/125000>0.
\tag{21}
\]
For these bounds, \(.3991<P_0<.3993\), and
\(-.246<U<.282\) on \(.22\le p\le h\); also
\(q_L-.282^2-1.958^2=33/15625>0\).
Decreasing P toward \(P_0\) decreases Y and increases X,
so sorting is preserved. Section 5 supplies \(Y>.6064\)
at that endpoint, ensuring the positive tangent floor as well.

As \(C_q(Y)\) increases with Y, it is enough to prove
\[
                    C_q(Y(p))>\beta(p)
\tag{22}
\]
for the reference solution (18) with \(P=P_0\), uniformly
over the entire interval \(.22\le p\le h\). No original
anchor is moved to that reference solution; this is a scalar
comparison of contact derivatives.

## 5. One whole-interval polynomial proves the outer derivative gap

In this section use (18) at \(P=P_0\), and write \(R_q=\sqrt q\).
Define the convenient upper bound
\[
 B(p)=X(p)(1-\cos p/R_q)\ge\beta(p),
 \qquad F(p)=C_q(Y(p))-B(p).
\tag{23}
\]
Along this reference contact \(Y'=\beta\) and
\(X'=-Y\beta/X\). Consequently
\[
 F'=\beta\left\{
 \frac{1+\cos h-Y}{\sqrt{q-(1+\cos h-Y)^2}}
           +\frac YX(1-\cos p/R_q)\right\}
                         -\frac{X\sin p}{R_q}.
\tag{24}
\]

Here is a compact exact polynomial certificate for \(F'>0\).
Let all Taylor polynomials below have argument p, and put
\[
 \begin{gathered}
 R_l=1.9787,\quad R_u=1.9788,\quad Z_l=1.962,
 \quad P_l=.3991,\quad P_u=.3993,\\
 Y_l=(Z_l-C_4)S_3+P_lC_2,\qquad
 Y_u=(R_u-C_2)S_5+P_uC_4,\\
 X_l=Z_lC_2-P_uS_5+S_3^2,\qquad
 X_u=R_uC_4-P_lS_3+S_5^2,\\
 A=1-C_4/Z_l,\qquad L=1.7648-Y_u.
 \end{gathered}
\tag{25}
\]
All six polynomials are positive on \([.22,.7]\).
For example \(C_2\ge.755\), \(S_5<.645\), \(C_4\le1\)
make this immediate directly in (25). The endpoint square
bounds give
\[
 R_l<R_q<R_u,\quad P_l<P_0<P_u,\quad Z>Z_l,
\]
the last with reserve \(q_L-.246^2-Z_l^2=17/3125\).
Taylor bounds in (18)--(19) therefore give
\[
       Y_l\le Y\le Y_u,\quad X_l\le X\le X_u,
       \quad \beta\ge X_lA,\quad 1-\cos p/R_q\ge A.
\tag{26}
\]
Substituting these positive bounds in (24) and clearing
the positive denominator \(R_lR_uX_u\) leaves the degree-27
polynomial
\[
 \mathcal P(p)
       =R_lX_lA\{LX_u+R_uY_lA\}-R_uX_u^2S_5.
\tag{27}
\]
Its positivity on one whole interval is certified as follows.
Expand \(\mathcal P(23/50+(6/25)x)=\sum_{j=0}^{27}a_jx^j\),
and define its Chebyshev coefficients by
\[
 \begin{split}
 c_0&=\sum_{n\ {\mathrm{even}}}a_n2^{-n}\binom n{n/2},\\
 c_j&=\sum_{\substack{n\ge j\\n-j\ {\mathrm{even}}}}
       a_n2^{1-n}\binom n{(n-j)/2}\qquad(j>0).
 \end{split}
\tag{28}
\]
Direct rational expansion of the factored polynomial (27) gives
\[
                  c_0>2.2362,\qquad
                  \sum_{j=1}^{27}|c_j|<1.4183.
\tag{29}
\]
Hence \(\mathcal P>.8179>.81\) because \(|T_j(x)|\le1\)
on \([-1,1]\). Equations (25)--(29) specify the entire
certificate and its exact rational conversion; there is no
angle subdivision or list of sampled values. They prove
\(F'>0\) throughout \([.22,.7]\).

It remains to check F at .22. At that point \(Y>.6064\):
otherwise \(X>1.8834\), and (17) would give
\[
 P_0\le .6064C_4(.22)-.8834S_7(.22)<.3991,
\]
contrary to (25). The square and last-comparison reserves are
\[
 q_L-.6064^2-1.8834^2=12087/25000000,
\]
\[
 .3991-.6064C_4(.22)+.8834S_7(.22)
                  =280519717600099/2812500000000000000>0.
\tag{30}
\]
Since \(Y'=\beta>0\), this tangent floor holds on the whole
reference interval. Moreover \(X<1.8837\) at .22, since
\(1.8837^2-(Q-.6064^2)=8933/20000000>0\).
The remaining base comparisons are
\[
                 C_q(Y)>.9598,\qquad B(.22)<.955.
\tag{31}
\]
For the first use
\[
 q_L-\{1+C_4(h)-.6064\}^2-\{S_5(h)+.9598\}^2
                  =16067399851/144000000000000>0.
\]
For the second use
\[
 .955-1.8837\{1-C_6(.22)/R_u\}
                    =7330813097827/24735000000000000>0.
\tag{32}
\]
Thus \(F(.22)>.0048\). With \(F'>0\), this proves (22)
and the strict positivity of (7) at every outer-E contact.

## 6. Completion of the actual transport

Before EH1 contact, DE2 improves at fixed b. During contact,
Sections 3--5 show that a positive DE2 margin cannot first
cross zero: its derivative at such a boundary is strictly
positive. Thus both actual witnesses persist while E moves.

The radial-arc denominator in (5) stays positive. The only
remaining radial endpoint is b=0. The zero-tangent arguments
in Section 5 of the DE3 outside-transport note apply without
using DE3: a core zero-tangent EH1 contact gives actual EH0,
whereas an outer zero-tangent contact at \(p\ge.22\) would
force \(a_H<.844<b_H\), contrary to sorting. Thus the path
reaches EH0, short positive EH1, or DE alignment. At DE
alignment the remaining EH error is exactly the original
\(p-n=\theta_H-\theta_D\), proving the stated alternatives
and the join under (4).

The E frame stays in its original interval and both signed
variations decrease by its movement. Core E retains
\(a_E\le7/12\); outer E retains
\(a_E\ge c_q\ge\max\{b_H,b_D\}\). These are precisely the
hard-class radial alternatives. At an original boundary input,
continuity of the actual neighboring separations preserves
the neighbor order and winding as in the boundary-domain
bridge. No assertion about unretained nonneighbor separators
is needed for the subsequent necessary-system theorem.

The following H/G transport records its own strict H-circle
loss if GA0 was unavailable. A possible loss at E is not
used in its place. The argument therefore retains the
original-radius and anchor-loss obligations for equality.
