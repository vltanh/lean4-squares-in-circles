# Wrong word 0011011, edge 3: negative core to positive outer

## Theorem and scope

Let a negative core-boundary state precede a positive outer-boundary state.
At \(Q=9789/2500\), on the entire interval
\[
 p-.7\le\phi\le p+.7,\qquad p=\pi/2,
\]
every true separating axis implies
\[
 C=\phi-H(a,b)-J(B)>\gamma,\qquad \gamma=.89765,
\tag{1}
\]
where the two exact role labels are
\[
 \begin{aligned}
 H(a,b)&=.22042-.34492a+.98439b-.05334b^2,\\
 J(B)&=.03965+3.85510B-1.49748B^2-1.89442A(B)B,\\
 A(B)&=\sqrt{Q-(B+.5)^2}-.5.
 \end{aligned}
\tag{2}
\]
Every decimal in this note denotes an exact rational.

The proof covers both core pieces, all four retained signed axes,
the whole angle interval, and all closed endpoints. There are 118 fixed
rational comparisons, including 32 coefficients of four fixed
polynomials. Two explicitly identified endpoint results from already
proved mixed-pair lemmas are reused. No sampled minimum or adaptive
state subdivision is a premise.

Write
\[
 a_c=7/12,\quad d_c=.5+\sqrt2/24,\quad
 d=\sqrt{Q/2}-.5,\quad a_0=\sqrt{Q-.25}-.5,\quad
 g=.98439,\quad v=.05334,\quad
 e=.22042-.34492a_c.
\tag{3}
\]
On the source side, \(a=a_c,\ 0\le b\le .5\). On its corner,
\[
 .5\le b\le d_c,\qquad
 a=.5+\sqrt{1/144-(b-.5)^2}.
\tag{4}
\]
The target satisfies \(0\le B\le d\). Own-frame centers are
\((a,b)\) and \((A,-B)\).

## 1. Common bounds and absent axes

Set
\[
 U=A+.5,\quad V=B+.5,\quad r=V/U.
\]
Then
\[
 U^2+V^2=Q,\quad A'=-r,\quad
 r'=Q/U^3,\quad r''=3QV/U^5.
\tag{5}
\]
With \(k=1.89442\),
\[
 \begin{aligned}
 J'&=3.85510-2.99496B-k(A-Br),\\
 J''&=-2.99496+k(2r+Br'),\\
 J'''&=k(3r'+Br'')>0.
 \end{aligned}
\tag{6}
\]
Thus \(J''\) increases and \(J'\) is convex. The fixed bounds
\[
 J'(.5)>.624,\quad -.032<J''(.5)<0,\quad J''(.55)>0
\]
prove \(J'>0\) throughout: through .5 the derivative decreases, between
.5 and .55 its possible decrease is less than \(.032(.05)\), and
thereafter it increases. Endpoint bounds on the convex derivative give
\[
 0<J'<1.176,\qquad J(d)<.763568,\qquad
 J'''>3k(.557)>1.
\tag{7}
\]

The core label \(H\) increases along the whole core. On the corner,
if \(t=-a'\in[0,1]\), its derivative is \(.34492t+g-2vb>0\).
There is also the useful global affine bound
\[
 H(a,b)\le e+gb<.570.
\tag{8}
\]
It is immediate on the side. On the corner its required correction is
\[
 .34492(a_c-a)-vb^2
 \le .34492(a_c-d_c)-v/4<0.
\]

A second global bound is
\[
 J(B)<.108+.73B.
\tag{9}
\]
On \([0,.5]\), \(J''\le J''(.5)<-.03\). At \(B=.3\), the
strong-concavity upper bound
\[
 [J(.3)-.73(.3)]+\frac{[J'(.3)-.73]^2}{.06}<.108
\]
proves (9). On \([.5,d]\), the derivative of \(J-.73B\) is convex
and negative at .5. It can first be negative and then positive,
without creating an interior maximum. Its two endpoint values are
below .108.

Let \(s=\sin\phi,c=\cos\phi\) and \(W=(1+s+|c|)/2\).
The four possible separating inequalities are
\[
\begin{array}{c|l}
1&-b+As-Bc\ge W,\\
2&-ac-bs+A\ge W,\\
3&as-bc-B\ge W,\\
4&a-Ac-Bs\ge W.
\end{array}
\tag{10}
\]
In row 2, \(a\) is the variable source coordinate; \(ac\) means
\(a\cos\phi\), not \(a_c\).

The core norm is less than .8 and \(W\ge1\), so row 3 is impossible
on the whole interval. Every outer center has norm at most \(a_0<1.415\).
For completeness, \(A+B\) is concave in \(B\), so its minimum is
\(a_0\) at the axial endpoint, since \(2d>a_0\). The circle equation
then gives \(A^2+B^2\le a_0^2\).
Consequently row 1 cannot use a core corner: its left side is at most
\(-.5+a_0<1\).

Below the quarter turn, row 4 is impossible because its left side
is at most \(a_c<1\). Row 2 cannot use a corner there either:
\(a,b\ge .5\) would imply
\[
 A\ge W+.5(c+s)=.5+c+s\ge1.5>a_0.
\]
Only source-side contacts in rows 1 and 2 remain below \(p\).

We use twice the whole aligned-pair theorem in
**WRONG_0011011_ALIGNED_MIXED_QUARTER_HAND_PROOF.md**.
It covers both coincident separators at \(\phi=p\), with these exact
labels, and supplies a strict bound above (1).

## 2. Row 1 below the quarter turn

At a fixed target and angle, \(H\) increases with the source coordinate.
Thus it suffices to increase \(b\) until contact:
\[
 b=(A-.5)\sin\phi-(B+.5)\cos\phi-.5
   =P\sin\phi-V\cos\phi-.5,\qquad P=U-1.
\tag{11}
\]
A feasible target has \(A\ge1\), hence
\[
 0\le B\le B_1:=\sqrt{Q-2.25}-.5,\qquad
 0\le b\le A-1<a_0-1<.415.
\tag{12}
\]
Contact therefore stays strictly on the source side.

### 2.1. Targets \(B\ge .54\): deformation to alignment

For fixed \(B\),
\[
 b_\phi=P\cos\phi+V\sin\phi>0,\qquad
 b_{\phi\phi}=-(b+.5).
\]
The contact cost satisfies
\[
 C_{\phi\phi}=2v b_\phi^2+(g-2vb)(b+.5)>0.
\tag{13}
\]
At \(\phi=p\),
\[
 C_\phi(p)=1-[g-2v(A-1)](B+.5)<0.
\tag{14}
\]
The bracketed product increases with \(B\); its value at .54 already
makes (14) strict. Since \(C_\phi\) increases with \(\phi\), it is
negative throughout the lower interval. Increasing \(\phi\) to \(p\)
decreases the cost. The contact coordinate increases but remains below
.415, so no boundary interrupts this deformation. The aligned theorem
finishes this case.

### 2.2. Targets \(B\le .54\): exact minimization in the angle

For any positive rational \(h\),
\[
 -gb+vb^2\ge-hb-\epsilon_h,\qquad
 \epsilon_h=\frac{(g-h)^2}{4v}.
\tag{15}
\]
Put
\[
 T=P^2+V^2=Q+1-2U,\quad
 S=\sqrt{h^2T-1},\quad
 \beta=\arctan(V/P).
\]
The roots are positive on the intervals used below. Since a feasible
contact has \(P\sin\phi-V\cos\phi=b+.5>0\), the angle
\(\theta=\phi-\beta\) lies in \((0,\pi)\).
The function \(\theta-h\sqrt T\sin\theta\) is convex there and has
minimum \(\arctan S-S\). Combining this exact minimum with (11) and (15),
\[
 C\ge E_h(B):=
 \beta+\arctan S-S-e-\epsilon_h+h/2-J(B).
\tag{16}
\]
Use \(h=g\) on \([0,.45]\) and \(h=.975\) on \([.45,.54]\).

Here is a continuous derivative proof of the scalar lower bounds.
For \(N=Q-U-VS,\ D=UT\),
\[
 \begin{aligned}
 E_h'&=N/D-J',\\
 N'&=r-S-h^2Vr/S,\qquad D'=r(2U-T),\\
 E_h''&=(N'D-ND')/D^2-J''.
 \end{aligned}
\tag{17}
\]
The following fixed polynomial identity proves
\[
 E_h'''<0
\tag{18}
\]
on both intervals. In the polynomial variable \(u=U\), set
\[
 \begin{aligned}
 T&=Q+1-2u,&W_0&=Q-u^2,&Z&=h^2T-1,\\
 E_0&=2u^2-4Qu+Q(Q+1),&
 E_0'&=4u-4Q,\\
 A_0&=E_0u^2T-W_0\{E_0'uT-E_0(3T-4u)\},\\
 D_0&=u^5T^3-A_0,\\
 C_h&=3h^2QuT^2Z-h^4W_0u^2T^2-4h^2W_0u^2TZ\\
    &\qquad+3QT^2Z^2-6QuTZ^2+8W_0u^2Z^2.
 \end{aligned}
\tag{19}
\]
For \(G_h=\beta+\arctan S-S\), direct differentiation gives
\[
 G_h'''=\frac{A_0S^3-VC_h}{u^5T^3S^3}.
\tag{20}
\]
This identity can be checked without expanding radicals. First,
\(\beta'=(Q-u)/(uT)\); differentiating twice gives
\(\beta'''=A_0/(u^5T^3)\).
Next \((\arctan S-S)'=-rS/T\), where
\[
 T'=2r,\quad T''=2r',\quad
 S'=h^2r/S,\quad S''=h^2r'/S-h^4r^2/S^3.
\]
The product rule gives
\[
 (rS/T)''
 =r''S/T+3h^2rr'/(ST)-h^4r^3/(S^3T)
  -6rr'S/T^2-4h^2r^3/(ST^2)+8r^3S/T^3,
\]
which is precisely \(VC_h/(u^5T^3S^3)\).

The degree-8 polynomial \(D_0\) is positive on \([1.68,1.915]\).
The degree-6 \(C_g\) is positive on the same interval, and
\(C_{.975}\) is positive on \([1.68,1.74]\).
These intervals contain all relevant \(U\)'s:
\(U(.54)>1.68,\ U(0)<1.915,\ U(.45)<1.74\).
The fixed coefficient rows in Section 7 prove these assertions.
All denominators in (20) are positive; hence \(G_h'''<1\).
Equation (7) now yields (18).

For \(h=g\), the fixed values are
\[
\begin{array}{c|l}
 B&\text{bounds}\\ \hline
 .3035&E_g>.89776733,\quad |E_g'|<.000006,\\
 .32&E_g>.8978,\quad E_g'>0,\quad E_g''>.22,\\
 .4&E_g>.8985,\quad E_g'>0,\quad E_g''<0,\\
 .45&E_g>.8985.
\end{array}
\tag{21}
\]
On \([0,.32]\), (18) implies \(E_g''>.22\). Completing the quadratic
at .3035 gives
\[
 E_g\ge .89776733-\frac{(.000006)^2}{.44}>\gamma.
\tag{22}
\]
On \([.32,.4]\), \(E_g'\) is concave and positive at both endpoints,
so \(E_g\) increases. On \([.4,.45]\), its second derivative is
negative and decreasing, so the two endpoint values bound the minimum.
Finally \(E_{.975}''(.45)<0\), and (18) makes this second derivative
negative throughout \([.45,.54]\). Both endpoint values exceed .89807.
This finishes every lower row-1 contact.

## 3. Row 2 below the quarter turn

Here again the source lies on its side. Increasing \(b\) to contact
reduces the cost. The contact equation is
\[
 b=(A-.5)\csc\phi-.5-\frac{13}{12}\cot\phi.
\tag{23}
\]
Feasibility forces \(\phi>1.12\): at 1.12 the required target with
\(b=0\) has \(A>a_0\), and the requirement decreases thereafter.
As before, \(A\ge1,\ B\le B_1,\ 0\le b<.415\).

Put \(L=b+.5\) and \(t=\cot\phi<.485\). Then
\[
 b_\phi=13/12-Lt,\qquad
 b_{\phi\phi}=L(1+2t^2)-(13/12)t.
\tag{24}
\]
In particular,
\[
 0<b_\phi\le13/12,\qquad
 b_{\phi\phi}\ge .5+.485^2-(13/12)(.485)>.2.
\]
The quadratic on the right decreases for \(0\le t\le .485\).
Thus the fixed inequality
\[
 2v(13/12)^2-[g-2v(.415)]
       \{.5+.485^2-(13/12)(.485)\}<0
\tag{25}
\]
proves \(C_{\phi\phi}<0\).
At fixed \(B\), the feasible contact interval starts at \(b=0\) and
ends at \(p\); (24) proves this continuation. Its minimum is therefore
at one of those two endpoints. Alignment is already proved.

At the zero endpoint,
\[
 \begin{aligned}
 m&=.5\sin\phi+(13/12)\cos\phi,&
 U&=1+m,\\
 V&=\sqrt{Q-U^2},&
 B_z&=V-.5,\\
 K(\phi)&=\phi-e-J(B_z).
 \end{aligned}
\tag{26}
\]
The function \(B_z\) increases over the relevant angle interval.

### 3.1. Zero endpoints with \(B_z\le .43\)

These endpoints already satisfy row 1. Its margin factors as
\[
 \cos\phi\{(13/12)\sin\phi-.5\cos\phi-V\}.
\]
The expression before \(V\) is positive, and
\[
 \{(13/12)\sin\phi-.5\cos\phi\}^2-V^2
   =349/144-Q+2m>0.
\tag{27}
\]
Indeed \(B_z\le .43\) gives
\(m\ge\sqrt{Q-.93^2}-1\), and substitution in (27) is strictly positive.
Section 2 applies directly.

### 3.2. Zero endpoints with \(.43\le B_z\le .65\)

This part of the zero curve is contained in \([1.32,1.48]\).
Throughout that enlarged interval \(.4<B_z<.7\). If
\(w=(13/12)\sin\phi-.5\cos\phi\), then
\[
 B_z'=w/r,\qquad
 B_z''=Um/V-Qw^2/V^3.
\]
Use
\[
 w^2\le205/144,\quad r>.51,\quad B_z'<2.35,\quad
 J''>-.52,\quad J'<.74.
\]
The derivative bound follows from convexity of \(J'\) and its endpoints
at .4 and .7. These inequalities give
\[
 K''=-J''(B_z')^2-J'B_z''
 <.52(2.35)^2+.74Q(205/144)/(.9^3)<9.
\tag{28}
\]
Five fixed comparisons show
\[
 K(1.32),K(1.36),K(1.40),K(1.44),K(1.48)>.9000.
\]
For a twice differentiable function with \(K''\le9\), its value on
an interval of length .04 is at least the smaller endpoint value
minus \(9(.04)^2/8\). This follows by subtracting \(9\phi^2/2\) and
using concavity. Therefore \(K>.8982>\gamma\) on all four intervals.

### 3.3. Zero endpoints with \(.65\le B_z\le B_1\)

Section 5.2 of
**WRONG_0011011_EDGE3_POSITIVE_CORE_TO_POSITIVE_OUTER_HAND_PROOF.md**
proves the zero-curve inequality
\[
 \phi-.01449-J(B_z)>.9025
\tag{29}
\]
on exactly this part of (26). Its proof uses strict concavity of the
zero-curve cost, the monotone ratio \(J''/J'\), and its two endpoints;
it does not assume the present negative-core theorem.
Since
\[
 e-.01449=709/150000,
\]
(29) gives
\[
 K>.9025-709/150000=.897773333\ldots>\gamma.
\tag{30}
\]
Every lower row-2 endpoint is now covered.

## 4. Row 1 above the quarter turn

Put \(x=\phi-p\in[0,.7]\). The contact coordinate is
\[
 b=P\cos x+(B-.5)\sin x-.5.
\tag{31}
\]
Its derivative satisfies
\(b_x\le\max(B-.5,0)<.4\).
Since \(0<g-2vb\le g\), the contact cost has
\[
 C_x=1-(g-2vb)b_x>1-.4g>0.
\tag{32}
\]
Thus reducing \(x\) lowers the cost.

If \(B\le B_1\), the endpoint at zero has \(b=A-1\ge0\) and
the deformation reaches alignment.
Here is the needed domain continuation. The function \(b+.5\) is
positive on the whole strip: it is concave in \(B\), and its two
outer endpoint lower bounds are
\[
 (a_0-.5)\cos(.7)-.5\sin(.7)>0,\qquad d-.5>0.
\]
Consequently \(b_{xx}=-(b+.5)<0\), and nonnegative contact coordinates
form an interval in \(x\). If the starting point and the aligned
endpoint are feasible, the whole path is feasible. Also every such
contact has \(b\le a_0-1<.415\), by the norm bound in Section 1.

If \(B>B_1\), decreasing \(x\) reaches the first zero coordinate.
Every such first zero occurs before .31:
\[
 b(d,.31)>0,\quad
 b_B=-r\cos x+\sin x<0,\quad
 b_x=(B-.5)\cos x-P\sin x>0
\]
on \(B_1\le B\le d,\ 0\le x\le .31\).
For the last inequality, use
\(B-.5\ge B_1-.5\), \(P\le .5\), and its positive bound at .31.
The zero curve therefore runs monotonically from \((0,B_1)\) to
its diagonal endpoint and satisfies
\[
 B_z'=
 \frac{(B-.5)\cos x-P\sin x}{r\cos x-\sin x}
 \le\frac{.4}{r(B_1)\cos(.31)-\sin(.31)}<.79.
\tag{33}
\]
Its zero-source cost increases, since
\(1-J'B_z'>1-1.176(.79)>0\).
Its minimum is
\[
 p-e-J(B_1)>.89780>\gamma.
\tag{34}
\]
Equations (32)–(34) cover every possible upper row-1 exit.

## 5. Row 2 above the quarter turn

### 5.1. The strip \(0\le x\le .3\)

No source corner is feasible here. On the corner the projection
\(a\sin x-b\cos x\) decreases with \(b\), and its maximum at \(b=.5\)
has SAT margin at most
\[
 a_0-.5+(a_c-.5)\sin x-\cos x<0.
\tag{35}
\]
This expression increases in \(x\) and is still negative at .3.

The side contact is
\[
 b=P\sec x-.5+\frac{\tan x}{12}.
\]
Its derivative obeys
\[
 0<b_x=P\sec x\tan x+\frac{\sec^2x}{12}
 \le\frac{(a_0-.5)\sin(.3)+1/12}{\cos^2(.3)}<.4.
\tag{36}
\]
As in (32), reducing \(x\) decreases the cost, and the contact coordinate
also decreases. The path reaches alignment or \(b=0\).
At the zero endpoint,
\[
 A_{\rm req}=.5+.5\cos x-\sin x/12,\qquad
 B_z'=\frac{.5\sin x+\cos x/12}{r}<.27.
\tag{37}
\]
This zero curve stays in the outer arc:
\(A_{\rm req}(.3)>d\), and it starts at \(B_1\).
Its cost derivative is greater than \(1-1.176(.27)>0\), so (34)
again supplies its minimum.

### 5.2. The remaining interval \(.3\le x\le .7\)

Here the global bounds (8)–(9) suffice, including on the source corner.
Subtract \(g/\cos x\) times the row-2 SAT margin from
\(\phi-e-gb-.108-.73B\). The \(b\) coefficient cancels.
Use \(a\le a_c\), then minimize the remaining linear functional
in \((A+.5,B+.5)\) on the full circle of radius \(R=\sqrt Q\).
The result is
\[
 F(x)=p+x-e-.108+\frac{g+.73}{2}
   +\frac{g(1-\sin x/12)
       -R\sqrt{g^2+.73^2\cos^2x}}{\cos x}.
\tag{38}
\]
Minimizing over the full circle enlarges the target domain, so this
is a valid lower bound.

The fourth polynomial row in Section 7 proves \(F>\gamma\)
on the entire interval. Explicitly, let \(C_j,S_j\) be the Taylor
polynomials for cosine and sine of the indicated degrees, and set
\[
 \begin{aligned}
 K&=\pi_{\rm low}/2-e-.108+(g+.73)/2-\gamma,\\
 \mathcal A(x)&=C_{10}(x)(K+x)+g-(g/12)S_9(x),\\
 P_{\rm full}(x)&=\mathcal A(x)^2
          -Q\{g^2+.73^2 C_8(x)^2\}.
 \end{aligned}
\tag{39}
\]
On \([.3,.7]\), \(C_{10}\le\cos x\le C_8\) and
\(\sin x\le S_9\). The lower polynomial \(\mathcal A\) is positive:
\(C_{10}\ge1-x^2/2\) and \(S_9\le x\) give a strictly positive
rational lower bound.
The degree-8 truncation of \(P_{\rm full}\), reduced by the sum
of the absolute negative omitted coefficients times the corresponding
powers of .7, is positive by the printed Bernstein row.
It is a lower bound for \(P_{\rm full}\), so squaring proves (38).

## 6. Row 4 above the quarter turn

Row 3 was already excluded. Row 4 implies
\[
 B\le\frac{a_c+a_0\sin x-W}{\cos x}.
\]
If this upper bound is negative, the row is infeasible.
Otherwise apply (8) and (9):
\[
 C\ge p+x-.570-.108+\frac{.73}{2}
    -\frac{.73}{12}\sec x-.73(a_0-.5)\tan x.
\tag{40}
\]
This function is concave on \([0,.7]\), because secant and tangent
are convex there. Both endpoints exceed 1.19. This completes the
last signed axis.

## 7. Fixed rational arithmetic

For a degree-\(n\) polynomial \(P\) on \([L,H]\), the Bernstein
coefficients are the unique \(b_j\) in
\[
 P(L+(H-L)t)=\sum_{j=0}^n b_j\binom njt^j(1-t)^{n-j}.
\]
The following integers, divided by \(10^8\), are strict lower bounds
for the coefficients, in order. Every listed integer is positive.

| Polynomial | Interval | Degree | Lower numerators |
|---|---|---:|---|
| \(D_0\) | \([1.68,1.915]\) | 8 | 2787804586, 3011298926, 3194343971, 3343335303, 3465605636, 3569452117, 3664113405, 3759672496, 3866853865 |
| \(C_g\) | \([1.68,1.915]\) | 6 | 489607785, 323313124, 225100758, 168621192, 129208651, 82908158, 5312839 |
| \(C_{.975}\) | \([1.68,1.74]\) | 6 | 435018120, 395594851, 360296092, 328700368, 300392840, 274964286, 252010027 |
| Reduced \(P_{\rm full}\) | \([.3,.7]\) | 8 | 99491629, 115049933, 128428668, 139219167, 147047210, 151595871, 152627541, 150000491, 143672521 |

The companion checker uses exact integer fractions, fixed Taylor sums,
and integer-squared radical brackets. At the finitely many points in
(21), it evaluates
\[
 \beta=\pi/4+\arctan\frac{V-P}{V+P}.
\]
All inverse-tangent arguments, including \(S\), have absolute value
below .75. Alternating sums through indices 39 and 40 give certified
lower and upper bounds; negative arguments use oddness. A fixed
Machin enclosure supplies \(\pi\). These operations verify the
118 displayed or supporting comparisons and the four complete
polynomial rows. They are finite arithmetic verifications of the
continuous arguments above.

