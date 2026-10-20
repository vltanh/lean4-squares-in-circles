# A high GA target has signed tangent below one half

## 1. The original path and the assertion

Work on the fixed-witness G0--G2 boundary cycle at

\[
 Q=\frac{9789}{2500},\qquad y_E\le0.
\tag{1}
\]

Retain an original high GA witness, of index 2 or 3. The global
EH theorem gives H positive and outer; the high-GA source theorem
gives G negative and outer; and global BT rigidity gives B negative
and outer. The claim is

\[
                         \boxed{y_A<\frac12.}
\tag{2}
\]

This is a restriction on the retained boundary representative.
There is no frame-order hypothesis, no prior sign assumption on A
or T, and no replacement of any original witness. Both original
zero owners and every chart-junction marker choice are included.

Suppose instead that \(y_A=b_A\ge1/2\). Write the signed
tangents along H,G,A,B as

\[
                  b_H,-b_G,b_A,-b_B,
\]

and their three real errors as

\[
 v=\theta_G-\theta_H,\qquad u=\theta_A-\theta_G,\qquad
 w=\theta_B-\theta_A,\qquad \delta=v+u+w.
\tag{3}
\]

All four frames lie in the original common interval of length
less than \(h=7/10\), so every individual error and \(\delta\)
has absolute value below h. Use the unchanged original unsigned
markers F, with one choice at each junction. The old charged path is

\[
                  C_3=\frac\pi2+\delta+F_H+F_B.
\tag{4}
\]

We prove

\[
 C_3+\frac9{50}h_0(|\delta|)>\frac{11}{4},
 \qquad h_0(t)=\frac{\sin t+\cos t-1}{2}.
\tag{5}
\]

The four unchanged return edges then contradict the global G1
sum. The needed quarter signs, outer anchors, and global EH
rigidity are in
[the outer-anchor theorem](HAND_G3_EVERY_QUARTER_HAS_AN_OUTER_ANCHOR.md),
[global BT rigidity](HAND_G3_GLOBAL_BT_OWNER_RIGIDITY.md), and
[global EH rigidity](HAND_G3_GLOBAL_EH_OWNER_RIGIDITY.md).

## 2. A slightly stronger whole-outer marker floor

Put

\[
 R=\sqrt Q,\quad a_0=\sqrt{Q-1/4}-1/2,\quad
 c_0=\sqrt{Q/2}-1/2,\quad m=\frac{8669}{10000}.
\tag{6}
\]

Every original outer chart satisfies

\[
                              F\ge m b.
\tag{7}
\]

Here is a whole-chart verification, including both markers at a
junction. All displayed decimals are exact rationals. On L,
\(a>1.298\), \(b<.325\), and

\[
 -a'(b)=\frac{b+1/2}{a+1/2}<\frac{.825}{1.798}<.46.
\]

The two coordinate bounds follow by substituting \(b=a/4\)
into the increasing shifted-circle equation. Hence

\[
 F_L=.403875(a-a_0)+1.089065b
 \ge(1.089065-.46\cdot.403875)b>m b
 \qquad(b>0).
\tag{8}
\]

At b=0 the non-strict form in (7) includes equality.
On M, \(F_M-mb\) is concave in b. Its endpoints have
\((b/a)=1/4\) and \(3/7\), respectively. Their primaries
exceed 1.298 and 1.199, and the endpoint lower bounds are

\[
\begin{split}
 -2.143075+\{1.489593+(1.580219-m)/4\}(1.298)&>0,\\
 -2.143075+\{1.489593+3(1.580219-m)/7\}(1.199)&>0.
\end{split}
\tag{9}
\]

For H, write

\[
 p=.569472,\quad q=m-.390886=.476014,\quad
 C_H=\pi/4+.178586c_0.
\]

Then \(F_H-mb=C_H-pa-qb\). The full shifted-circle support
gives

\[
 pa+qb\le R\sqrt{p^2+q^2}-\frac{p+q}{2}<C_H.
\tag{10}
\]

The last strict comparison follows from \(\pi>3.14159\),
\(c_0>.8992140\), and the exact positive square reserve

\[
 \left(\frac{3.14159}{4}+.178586(.8992140)
                   +\frac{p+q}{2}\right)^2-Q(p^2+q^2)
 =\frac{6545897824987888201}{62500000000000000000000}>0.
\tag{11}
\]

The elementary lower bound for pi can be obtained from the
four-term lower Machin estimate recorded in
[the marker helper](HAND_G3_BT_PATH_MARKER_AND_NEGATIVE_AB_COMPARISON.md).
This proves (7).

## 3. Every outer zero error pays its return-charge variation

For a normal zero projection, the endpoint whose coordinates
rotate has unsigned coordinates \((a,b)\). Thus

\[
                 P(d)-P(0)=a\sin d+b(\cos d-1).
\]

This covers either HG owner, and either AB owner when A is
outer. Define its exact error contribution at weight m by

\[
 I(d)=d+m\{W(d)-1-[P(d)-P(0)]\},
 \qquad W(d)=\frac{1+\cos d+|\sin d|}{2}.
\tag{12}
\]

For an outer rotating endpoint,

\[
                         I(d)\ge\frac9{100}|d|.
\tag{13}
\]

For d>=0, the actual boundary bounds \(a<1.415\), \(b\ge0\)
give

\[
 I'(d)=1+m\{(b-1/2)\sin d+(1/2-a)\cos d\}
       >1-1.043m>\frac9{100}.
\tag{14}
\]

Indeed \(1.043^2>.5^2+.915^2\). This positive-error
estimate also holds for a core rotating endpoint.

For \(d=-z\le0\),

\[
 I(-z)=-z+m\{(a+1/2)\sin z+(b-1/2)(1-\cos z)\}.
\tag{15}
\]

At fixed z this is concave along the whole outer arc, so its
minimum occurs at \((a,b)=(a_0,0)\) or \((c_0,c_0)\).
On \([0,h]\), \(\sin z\ge.92z\) and
\(1-\cos z\le z^2/2\le.35z\). Also
\(a_0+1/2>1.9\) and \(c_0+1/2>1.399\). The two endpoint
coefficients in (15) are consequently greater than

\[
 -1+m(1.9\cdot.92-.175)>.09,\qquad
 -1+m(1.399)(.92)>.09.
\tag{16}
\]

This proves (13) on one whole interval.

Only one possible exception will be needed: if A is core and
AB2 has negative error \(-z\), then \(b_A\ge1/2\) and the
true-core bound \(a_A>447/800\) give instead

\[
 I_{AB}(-z)
 \ge-z+m\frac{847}{800}\sin z>-.16z.
\tag{17}
\]

Since \(|h_0'(t)|\le1/2\) on \([0,h]\),

\[
 \frac9{50}h_0(|\delta|)
 \ge\frac9{50}h_0(u)-\frac9{100}(|v|+|w|)
\tag{18}
\]

whenever \(0\le u\le h\). Thus (13) pays exactly for
discarding the two zero errors from this augmented charge.

## 4. The retained GA owner is 3 with positive error

On the outer arc, concavity gives \(a_G+b_G\ge a_0\),
and therefore \(a_G^2+b_G^2\le a_0^2<1.415^2\).
An owner-2 projection would satisfy

\[
 a_G\cos u+b_G\sin u-b_A
 \le\sqrt{a_G^2+b_G^2}-\frac12<1\le W(u),
\]

which is impossible. If owner 3 had \(u=-z\le0\), its
projection minus its width would be

\[
 a_G-\frac12-(b_A+\frac12)\cos z
                         -(a_A+\frac12)\sin z
 <a_0-\frac12-(\cos z+\sin z)<0.
\tag{19}
\]

Here \(b_A\ge1/2\), \(a_A>447/800>1/2\), and
\(\cos z+\sin z\ge1\). Hence the only remaining original
case is

\[
                 GA3,\qquad 0<u<h,\qquad
                 a_G+a_A\sin u-b_A\cos u\ge W(u).
\tag{20}
\]

## 5. Outer A: one scalar and one convexity certificate

Set

\[
 S=\sqrt{Q-1},\qquad P=S-1,\qquad
 K(u)=1+\cos u-P\sin u,\qquad
 Y(u)=\sqrt{Q-K(u)^2}.
\tag{21}
\]

Since A is outer and \(b_A\ge1/2\), its primary is at
most \(a_*=S-1/2\). Equation (20) implies

\[
                   a_G+1/2\ge K(u),\qquad
                   K(u)^2\le Q-1/4.
\tag{22}
\]

Thus the root in (21) is positive on the full feasible interval.
Use weight m on each zero inequality and

\[
                         \lambda(u)=\frac{mK(u)}{Y(u)}>0
\tag{23}
\]

on the actual GA3 inequality. The exact force collection, using
(7) and (12), is

\[
\begin{split}
 C_3-\frac\pi2\ge{}&u+2m+\lambda W(u)
      -(\lambda a_G+mb_G)\\
 &-\{\lambda a_A\sin u+(m-\lambda\cos u)b_A\}
       +I_{HG}(v)+I_{AB}(w).
\end{split}
\tag{24}
\]

The G support is at most
\(R\sqrt{\lambda^2+m^2}-(\lambda+m)/2\). The A support in
braces is maximized, on its entire allowed arc, at \(b_A=1/2\).
To check this endpoint assertion define

\[
 C(u)=\cos u+\frac{\sin u}{S},\qquad
 B(u)=K(u)^2\{1+C(u)^2\}-Q.
\tag{25}
\]

The support derivative at \(b=1/2\) is \(m-\lambda C(u)\).
It is negative exactly when \(K(u)C(u)>Y(u)\), which follows
from \(B(u)>0\). Here is a whole-interval proof. On
\([0,h]\),

\[
 K>1.3,\quad K\le2,\quad 1\le C<7/6,\quad
 U:=-K'=\sin u+P\cos u>P>.7.
\tag{26}
\]

The bound C>=1 follows by concavity and its two endpoint
values; U increases because \(\cos u-P\sin u>0\).
When C'>=0, use \(C'<1/S<10/17\) to obtain

\[
 U(1+C^2)-KCC'>\frac75-\frac{70}{51}
                         =\frac7{255}>0.
\tag{27}
\]

When C'<0 the same expression is plainly positive. Therefore
B decreases on the whole interval. Its endpoint is positive:
the rational root enclosure

\[
                 1.7075128<S<1.7075129
\tag{28}
\]

and alternating Taylor bounds at h give

\[
 \begin{gathered}
 K(h)>1+C_6(h)-.7075129S_9(h)=:K_-,\\
 C(h)>C_6(h)+S_7(h)/1.7075129=:C_-,\\
 K_-^2(1+C_-^2)-Q>\frac3{100}>0.
 \end{gathered}
\tag{29}
\]

Here \(S_j,C_j\) denote the ordinary alternating sine and
cosine polynomials ending at degree j. The force objective in
A is concave in b because its primary coefficient is positive.
Its negative derivative at the left endpoint proves the asserted
support maximum on the complete arc.

Substitution into (24), followed by (13) and (18), now gives

\[
 C_3+\frac9{50}h_0(|\delta|)
 \ge\frac\pi2+J(u),\qquad
 J(u)=u+m\{2-Y(u)\}
                 +\frac9{100}(\sin u+\cos u-1).
\tag{30}
\]

The optimizing identity used here is
\(\lambda K-R\sqrt{\lambda^2+m^2}=-mY\).

We certify, on the entire feasible interval (22),

\[
                              J(u)>1.17938.
\tag{31}
\]

For a short convexity proof, let \(D=K-1\). Differentiating
(21) gives

\[
 J''=m\frac{N(D)}{Y^3}-.09(\sin u+\cos u),\qquad
 N(D)=Q(1+P^2)-Q(2D^2+D)+D(D+1)^3.
\tag{32}
\]

Here \(.3<D<.915\), \(Y<1.5\), and
\(N'(D)=-(4D+1)\{Q-(D+1)^2\}<0\). Consequently

\[
 N(D)>Q(1.49)-Q\{2(.915)^2+.915\}
                            +.915(1.915)^3>2.
\]

Also \(\sin u+\cos u<1.42\). Thus

\[
 J''>m\frac{2}{1.5^3}-.09(1.42)
       =\frac13+\frac{7099}{135000}>\frac13.
\tag{33}
\]

One rational point completes the certificate. At \(u_0=61/100\),
use \(S_{11}\le\sin u_0\le S_9\),
\(C_{10}\le\cos u_0\le C_{12}\), and (28). Positive
squaring gives

\[
 1.3839258<Y(u_0)<1.3839261,\qquad
 J(u_0)>1.17939,\qquad |J'(u_0)|<.001.
\tag{34}
\]

For example the direct rational lower value in (34) is

\[
 u_0+m(2-1.3839261)+.09\{S_{11}(u_0)+C_{10}(u_0)-1\}
 =\frac{5230878680632054221953138400239}
        {4435200000000000000000000000000}>1.17939.
\]

The derivative bounds follow from
\(J'=1-mKU/Y+.09(\cos u-\sin u)\) using the same root
and Taylor bounds. Completing the square in (33) yields

\[
 J(u)>1.17939-\frac32(.001)^2>1.17938.
\tag{35}
\]

Finally \(\pi/2>1.570795\), so (30) is strictly greater
than \(2.750175>11/4\). This proves (5) for every outer A.

## 6. Core A: the same path has a larger reserve

Now A is core, so \(a_A\le7/12\), \(1/2\le b_A<.56\).
Equation (20) forces \(u>3/10\). Indeed it implies

\[
 a_G\ge\frac12+\cos u-\frac1{12}\sin u,
\]

whereas the right side at \(u=3/10\) already exceeds 1.415
and decreases on \([0,h]\).

Use fixed weight \(\lambda=7/5\) on GA and m on the zeros.
At zero errors the force sum, before the three error terms, gives

\[
 C_3-\frac\pi2
 \ge 2m+2\lambda-R\sqrt{\lambda^2+m^2}
                  +I_{HG}(v)+I_{GA}(u)+I_{AB}(w).
\tag{36}
\]

This uses \(b_A\ge1/2\), since \(\lambda>m\).
Positive squaring gives the fixed base in (36) greater than 1.27.
For the actual core GA3 error,

\[
 I_{GA}(u)
 =u-\lambda\{(b_A+1/2)(1-\cos u)+(a_A-1/2)\sin u\}
 \ge f(u),
\]

\[
 f(u)=u-\frac75\left\{1.06(1-\cos u)+\frac1{12}\sin u\right\}.
\tag{37}
\]

The function f is concave on the whole interval \([.3,.7]\).
Both endpoint values exceed .19, as follows directly from
\(C_6\) and \(S_5\). Therefore \(I_{GA}>.19\).
Equations (13), (17), and (18) lose at most
\((.16+.09)h=.175\) at the only possible core AB2 exception.
The augmented path consequently satisfies

\[
 C_3+\frac9{50}h_0(|\delta|)
 >\frac\pi2+1.27+.19-.175
 >\frac\pi2+1.28>\frac{11}{4}.
\tag{38}
\]

This proves (5) for the remaining radial kind.

## 7. The unchanged four-edge return

The four original return edges BT,TD,DE,EH have G1 charges
at least \(.8833+.18h_0(|d|)\) each. The established
whole-interval compression inequality gives

\[
 C_{\rm return}\ge4(.8833)+.18h_0(|\delta|).
\tag{39}
\]

This is exactly the return use in Section 10 of
[the conditional EH exclusion](HAND_G3_HIGH_EH_EXCLUSION_UNDER_LOW_GA.md);
the return owner and radial choices remain arbitrary here.
Together with (5), telescoping the unchanged original markers
would give

\[
 2\pi=C_3+C_{\rm return}
 >\frac{11}{4}+4(.8833)>\frac{710}{113}>2\pi,
\tag{40}
\]

a contradiction. Thus (2) holds.

The new restriction is the signed target cut (2); this note
does not assert complete high-GA exclusion or a frame transport.
Every scalar comparison is on a whole interval or an intrinsic
chart endpoint, with exact rational Taylor and square reserves.
No angular mesh, numerical optimizer, generated case inventory,
Lean build, or CI run is a premise.
