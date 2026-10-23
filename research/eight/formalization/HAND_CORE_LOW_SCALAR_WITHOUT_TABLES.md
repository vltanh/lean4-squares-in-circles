# The complete C/L scalar argument without coefficient tables

**Status.** This note replaces all five Bernstein rows in
`../CORE_LOW_WHOLE_PAIR_HAND_PROOF.md`, as well as the three coarse
endpoint tables in its Sections 3.2, 5.1, and 5.3. The arguments are
inequalities on the entire stated angle intervals. Their premises are
circle support, differentiation, a completed square, and explicit
rational Taylor bounds. No coefficient list, angle mesh, sampled
curvature bound, or computed certificate status is used.

Together with the geometric reductions in Sections 1--5 of that
manuscript, this proves the **complete C/L entry, with cost strictly
greater than \(91/100\)**: all sixteen ordered source-axis branches,
and the retained target axes by reflected reversal. The scope remains
the boundary ring after the independent core, cap, common-point, and
retained-axis reductions; frame concentration is not a hypothesis.

All terminating decimals in this note are exact rationals.

## 1. Constants and elementary calculus

Use the notation of the original C/L argument:

\[
 Q=9789/2500,\quad R=\sqrt Q<1.979,\quad
 \beta=.18,\quad g=1.077372,\quad
 \mu=.403875,\quad q=1.089065,
\]
\[
 A_*=(g+\beta)/2=.628686,\qquad
 C_*=(g-\beta)/2=.448686.
\]

Here \(q\) is the coefficient in the low-state label, not a radius.
The low-circle endpoints and endpoint label satisfy the elementary
squared bounds

\[
 1.4145<a_0<1.415,\qquad
 1.2987<a_1<1.2988,\qquad b_1=a_1/4,\qquad
 .306<E<.307.                                           \tag{1}
\]

We repeatedly use the following consequence of Taylor's theorem:

\[
 f''\ge m>0
 \quad\Longrightarrow\quad
 f(x)\ge f(z)+f'(z)(x-z)+\frac m2(x-z)^2
       \ge f(z)-\frac{f'(z)^2}{2m}.                    \tag{2}
\]

We also use two elementary consequences of concavity. A concave
function that is positive at the left endpoint can change sign at
most once, from positive to negative. This follows because its
nonnegative superlevel set is an interval. Consequently:

* if \(f'\) is concave and \(f'(a)>0\), then \(f\) has its minimum
  on \([a,b]\) at an endpoint;
* if \(f''\) is concave, \(f''(a)>0\), and \(f'(a)>0\), the same
  conclusion holds. In this case \(f'\) first increases and then
  decreases, so it too can change sign only from positive to negative.

In these statements a missing sign change simply gives monotonicity.

Write (S_j,C_j) for the sine and cosine Taylor polynomials through
degree \(j\). Alternating remainders give, on the intervals used below,

\[
 S_{11}<\sin x<S_9,\qquad C_{10}<\cos x<C_8,
 \qquad S_7\le\sin x\le S_5,\qquad C_6\le\cos x.      \tag{3}
\]

The strict versions are used only at positive angles. Every fixed
trigonometric comparison below follows by substitution in \(3\).

## 2. The negative-target axial scalar

The scalar in the original Section 4.1 is

\[
 F_a(x)=x+A_*+C_*\cos x-(ga_0-C_*)\sin x,
 \qquad 0\le x\le\pi/2.                              \tag{4}
\]

For completeness, consider any

\[
 f(x)=C+x+A\cos x-B\sin x,\qquad A,B\ge0,
 \quad r=\sqrt{A^2+B^2}.
\]

If \(r\le1\), then \(f'\ge0\). Otherwise put

\[
 y=\sqrt{r^2-1},\quad
 \eta=\arccos(1/r)=\arctan y,
 \quad B=r\cos\delta,\quad A=r\sin\delta.
\]

The negative part of \(f'=1-r\cos(x-\delta)\) on

\([0,\pi/2]\) is contained in \(|x-\delta|<\eta\). Its
total integral is at most

\[
 \int_{-\eta}^{\eta}(r\cos t-1)\,dt
 =2(y-\arctan y)
 \le\frac{2y^3}{3}.                                   \tag{5}
\]

Thus \(f(x)\ge f(0)-2y^3/3\) on the whole interval. For \(4\),

\[
 C_*^2+(g(1.415)-C_*)^2
 =1.3586548262253444<\frac{34}{25}.
\]

Therefore \(y<3/5\), and

\[
 F_a(x)>g-\frac{18}{125}=.933372>.91.                  \tag{6}
\]

This replaces the entire (P_-) row. The other low endpoint in the
same branch is already strictly increasing by

\(D^2+B_*^2<.1^2+.952^2<1\), as in the original argument.
Both endpoint estimates continue into the second quadrant by their
positive derivatives there.

## 3. The full-circle scalar and its cubic norm bound

For the positive target in the original Section 4.2, let

\[
 \begin{split}
 F(x)&=x+C_0+(g-.09)\sin x-.09\cos x-RN(x),\\
 C_0&=(g+\beta+\mu+q)/2+\mu a_0,\\
 N(x)^2&=\mu^2+q^2+g^2+2g(\mu\sin x-q\cos x),\\
 U(x)&=.405+1.086x-.037x^2-.048x^3.
 \end{split}                                          \tag{7}
\]

We prove both \(U>N\) and \(F>.91\) throughout

\([0,6/5]\), without either historical Bernstein row.

### 3.1 One derivative-shape argument proves \(U>N\)

Define the explicit polynomial

\[
 P=U^2-[\mu^2+q^2+g^2+2g(\mu S_9-qC_6)].             \tag{8}
\]

By \(3\), \(U^2-N^2\ge P\). Four differentiations of \(8\) give
the exact identity

\[
 \begin{split}
 P''''(x)={}&-.12263172564-.444007233x\\
 &+x^2(-.34388813718+.1450412055x)
   -.007252060275x^5.
 \end{split}                                          \tag{9}
\]

Because \(0\le x\le6/5\), the coefficient in parentheses is
negative. Thus \(P''''<0\) on this whole interval: \(P'''\)
decreases and \(P''\) is strictly concave.

Direct rational substitutions in \(8\) give

\[
 \begin{gathered}
 P'''(1/2)=\frac{662660529531}{25600000000000}>\frac1{40},\\
 P'(2/5)=\frac{11460897566081}{13671875000000000}>.0008,
 \qquad
 |P''(2/5)|=\frac{3000282554571}{2734375000000000}<.0011,\\
 P''(1/2)=\frac{1233763189563}{358400000000000}>0.
 \end{gathered}                                        \tag{10}
\]

On \([0,1/2]\), \(9\)--\(10\) imply \(P'''>1/40\).
Apply \(2\) to \(f=P'\), with \(z=2/5\). It gives

\[
 P'(x)>.0008-20(.0011)^2=.0007758>0.                   \tag{11}
\]

Hence \(P\) increases up to \(1/2\). On \([1/2,6/5]\),
the concavity of \(P''\), together with \(P''(1/2)>0\) and

\(P'(1/2)>0\), applies the second derivative-shape observation
in Section 1: \(P\) has no interior minimum. Its two relevant
endpoint bounds are

\[
 P(0)=\frac{386629063}{500000000000}>\frac1{6000},
 \qquad
 P(6/5)=\frac{6981963028883}{39062500000000000}
       >\frac1{6000}.                                 \tag{12}
\]

Equations \(11\)--\(12\) therefore show \(P>1/6000\) over the
entire original interval. Finally,

\[
 U'=1.086-.074x-.144x^2
 \ge1.086-.074(1.2)-.144(1.2)^2=.78984>0.
\]

Thus \(U\ge.405>0\), and \(U^2>N^2\) implies \(U>N\).

### 3.2 The cost polynomial decreases on the whole interval

After substituting \(a_0>1.4145\), \(R<1.979\), and \(N<U\)
in \(7\), the Taylor bounds give \(F-.91>P_F\), where

\[
 \begin{split}
 P_F={}&.1449421875-.161822x+.118223x^2-.06957x^3
 -.00375x^4\\
 &+.0082281x^5+.000125x^6
 -\frac{27427}{140000000}x^7-\frac{x^8}{448000}.
 \end{split}                                          \tag{13}
\]

This is precisely the polynomial obtained from

\[
 x+(g+\beta+\mu+q)/2+\mu(1.4145)-.91
 +(g-.09)S_7-.09C_8-1.979U.
\]

For \(0\le x\le1.2\), dropping negative terms in its derivative
and using \(x^4\le1.2^2x^2\), \(x^5\le1.2^3x^2\) gives

\[
 \begin{split}
 P_F'&\le-.161822+.236446x
    +[-.20871+.0411405(1.2)^2+.00075(1.2)^3]x^2\\
 &<-.16+.237x-.14x^2<-.05.
 \end{split}                                          \tag{14}
\]

The last step is the completed square, since

\(.237)^2/(4(.14))<.11\). Consequently

\[
 P_F(x)\ge P_F(6/5)
 =\frac{574865058837}{43750000000000}>.013>0.            \tag{15}
\]

This completes both full-circle scalar obligations.

## 4. The positive-target cut endpoint

For \(6/5\le x\le\pi/2\), the remaining target functional
decreases along the whole low arc, as proved directly in the original
Section 4.3. The cut endpoint gives

\[
 F_c=x+A_*-E+(C_*+gb_1)\cos x-(ga_1-C_*)\sin x.
\]

Using \(1\), define the strict lower bound

\[
 \begin{split}
 f(x)&=x+.628686-.307+D\cos x-B\sin x,\\
 D&=.448686+1.077372(1.2987)/4=.7984817541,\\
 B&=1.077372(1.2988)-.448686=.9506047536.
 \end{split}                                          \tag{16}
\]

On this interval, \(\sin x>.932\), \(0\le\cos x<.363\),
so

\[
 f''=-D\cos x+B\sin x
 >-.8(.363)+.95(.932)=.595>\frac12.                   \tag{17}
\]

At the single comparison point \(z=4/3\), \(3\) gives

\[
 .97193<\sin z<.97195,\qquad
 .23523<\cos z<.23525.
\]

Substitution in \(16\) and \(f'=1-D\sin x-B\cos x\) yields

\[
 f(z)>.918,\qquad |f'(z)|<.001.
\]

For example the exact lower substitution for (f(z)) is

\[
 \frac{2756717718266269}{3000000000000000}>.918;
\]

the same sine and cosine bounds put \(f'(z)\) between

\(.000285\) and \(.000321\\). Equations \(2\) and \(17\) prove

\[
 F_c(x)>f(x)>.918-(.001)^2=.917999>.91                 \tag{18}
\]

on the entire interval. This replaces the \(P_c\) row. Beyond

\(\pi/2\), the actual cosine coefficient changes to

\(-C_*+gb_1<0\); its derivative is greater than one, so the
same bound continues to \(2.05\).

## 5. The mixed multiplier on its whole first-quadrant interval

For the low source, the multiplier \(g/\sin x\) reduces the
negative core target, and the positive core target on its straight
side, to the same scalar

\[
 G=x-.09(\sin x+\cos x-1)-E+g/2
   +g\frac{(13/12)\cos x-(a_1-1/2)}{\sin x},
 \qquad .6\le x\le\pi/2.                            \tag{19}
\]

Set

\[
 A=13/12,\quad B=.7988,\quad k=-.588314
       =.09-.307+g/2-.91
\]

and consider the actual trigonometric function

\[
 T(x)=(x+k)\sin x-.09\sin^2x-.09\sin x\cos x
          +gA\cos x-gB.                               \tag{20}
\]

Since \(E<.307\), \(a_1-1/2<.7988\), and \(\sin x>0\),

\[
 (G-.91)\sin x>T(x).                                  \tag{21}
\]

Here no polynomial approximation on an angle interval is needed.
Direct differentiation gives

\[
 \begin{split}
 T'&=(1-gA)\sin x+(x+k)\cos x
            -.18\sin x\cos x-.09\cos2x,\\
 T''&=(2-gA)\cos x-(x+k)\sin x
            -.18\cos2x+.18\sin2x,\\
 T'''&=-(3-gA)\sin x-(x+k)\cos x
            +.36(\sin2x+\cos2x).
 \end{split}                                          \tag{22}
\]

Throughout the domain, \(x+k\ge.011686>0\),

\(\sin x>.564\), and \(\sin2x+\cos2x\le\sqrt2<17/12\\).
Therefore the single uniform bound

\[
 T'''<-(1.832847)(.564)+.36(17/12)
       =-.523725708<-\frac12                           \tag{23}
\]

holds. In particular, \(T''\) decreases and \(T'\) is concave.

At \(z=.9\), the rational Taylor bounds

\[
 .783326<\sin z<.783328,\qquad
 .621609<\cos z<.621611
\]

give directly from \(20\)--\(22\)

\[
 T(.9)>.0099,\qquad |T'(.9)|<.005.                    \tag{24}
\]

For explicit arithmetic, the lower substitution in \(20\) is

\(250306952093/25000000000000>.0099\); the derivative lies
between (-.004388) and (-.004385).

At the comparison point \(a=1.1\), use

\[
 .89120<\sin a<.89122,\qquad
 .45359<\cos a<.45361.
\]

The identities \(\cos2a=\cos^2a-\sin^2a\) and

\(\sin2a=2\sin a\cos a\) then give

\[
 T''(1.1)\ge\frac{2706219283}{15625000000}>\frac16,
 \qquad T'(1.1)>.06,
 \qquad T(1.1)>.016.                                  \tag{25}
\]

Because \(T''\) decreases, it exceeds \(1/6\) throughout

\([.6,1.1]\). Applying \(2\) with \(z=.9\) and \(24\) proves

\[
 T(x)>.0099-3(.005)^2=.009825>0
       \qquad (.6\le x\le1.1).                       \tag{26}
\]

For \(1.1\le x\le\pi/2\), \(23\) makes \(T'\) concave, and

\(T'(1.1)>0\). Thus the first derivative-shape observation in
Section 1 puts the minimum of \(T\) at an endpoint. The left value
is positive by \(25\), and the right value is explicit:

\[
 T(\pi/2)=\pi/2+k-.09-gB
 >1.57+k-.09-gB
 =\frac{19425779}{625000000}>.03.                      \tag{27}
\]

Equations \(21\), \(26\), and \(27\) prove \(G>.91\) over the whole
first-quadrant domain. This replaces the degree-thirteen \(P_m\)
row. Its second-quadrant continuation has the positive derivative
already proved algebraically in the original Section 5.2.

## 6. Removing the remaining coarse endpoint tables

The original proof also displayed short endpoint tables for three
other branches. The following whole-function arguments make those
tables unnecessary.

### 6.1 Core source, primary axis, positive low target

The original support reduction on \(1.9\le x\le2.05\) is

\[
 \mathcal C>x-\cos x+.43213375-RN_0(x),
 \quad
 N_0(x)=\| (\mu,q)-(\cos x,\sin x)\|.                \tag{28}
\]

The map \(x\mapsto(\cos x,\sin x)\) has speed one, so the
triangle inequality gives

\[
 N_0(x)\le N_0(1.9)+(x-1.9).
\]

At the single left endpoint, Taylor's inequalities give

\[
 \begin{split}
 N_0(1.9)^2
 &\le\mu^2+q^2+1-2[\mu C_6(1.9)+qS_7(1.9)]\\
 &=\frac{2793644154379657}{5040000000000000}
   <\frac9{16}.
 \end{split}                                          \tag{29}
\]

Also \(-\cos x>.32\). Write \(t=x-1.9\in[0,.15]\).
Equations \(28\)--\(29\) imply on this entire interval

\[
 \begin{split}
 \mathcal C
 &>1.9+t+.32+.43213375-1.979(.75+t)\\
 &\ge1.9+.32+.43213375-1.979(.75)-.979(.15)\\
 &=\frac{816827}{800000}>1.02>.91.
 \end{split}                                          \tag{30}
\]

This replaces the two-interval table in the original Section 3.2.

### 6.2 Low source on the primary axis, \(.3\le x\le.6\)

Keep the original full-circle support constant

\[
 S_0=\mu(1.4145)+(\mu+3+q)/2-1.979(3.574),
 \qquad C=(3+\beta)/2+S_0-.005.
\]

The two reduced functions are

\[
 H_-=x+C+g/2+3.16\cos x-.09\sin x,
 \qquad
 H_+=x+C-g/2+3.16\cos x+2.91\sin x.                  \tag{31}
\]

On their whole interval, \(\sin x>.295\),

\(\cos x>.82\), and \(\sin x<.6\\). Hence

\[
 H_-'<1-3.16(.295)-.09(.82)<0,
 \qquad
 H_+'>1-3.16(.6)+2.91(.82)>0.                         \tag{32}
\]

Only the respective monotone endpoints remain. The simple bounds

\(\cos .6>.82\), \(\sin .6<.6\\),

\(\cos .3>.955\), and \(\sin .3>.2955\\) give

\[
 H_-(.6)>.6+C+g/2+3.16(.82)-.09(.6)
       =\frac{16091059}{16000000}>1,
\]
\[
 H_+(.3)>.3+C-g/2+3.16(.955)+2.91(.2955)
       =\frac{15501187}{16000000}>.968>.91.             \tag{33}
\]

Thus the four-entry table in the original Section 5.1 is unnecessary.

### 6.3 Positive core target on its corner

The original geometric argument excludes \(x\le1.9\). For the
whole remaining interval \(1.9\le x\le2.05\), put

\[
 d=-\cos x,\quad s=\sin x,\quad
 k(x)=1+s-d/12,
 \quad B(x)=\sqrt{Q-k(x)^2}-\frac12.
\]

The necessary primary separation is

\(a\ge\tfrac12+s-d/12=k-\tfrac12\). By the low-circle
equation this implies \(b\le B(x)\).

Throughout the interval, fixed endpoint Taylor bounds and monotonicity
of sine and cosine give

\[
 .887<s<.947,\qquad .32<d<.462,
 \qquad 1.8485<k<1.921.
\]

Since \(1.921^2<Q<1.8485^2+.73^2\), the square root defining

\(B\) is positive and less than \(.73\). Differentiating the
actual radical gives a uniform lower bound

\[
 B'(x)=\frac{k(d+s/12)}{\sqrt{Q-k^2}}
 >\frac{1.8485(.32+.887/12)}{.73}
 =\frac{17475719}{17520000}.
\]

Multiplication by \(q=1.089065\) gives

\[
 qB'>\frac{3806438782547}{3504000000000}>1.              \tag{34}
\]

Using \(\ell_L\le qb\), \(\ell_C<.786\), and

\(\beta h<.0378\), the whole branch satisfies

\[
 \mathcal C>x-.8238-qB(x)=:J(x).
\]

Equation \(34\) says \(J'<0\). Therefore its minimum is at the
single right endpoint, where \(B<.23\), and

\[
 \mathcal C>J(2.05)>2.05-.8238-.23q
 =\frac{19514301}{20000000}>.975>.91.                  \tag{35}
\]

This replaces the original Section 5.3's two-interval table.

## 7. Coverage

The original C/L reductions exclude all low-to-core secondary axes,
the nonpositive core-to-low secondary angles, and the relevant small
primary angles by direct projection inequalities. Angles at least

\(2.05\) are covered by the uniform label bound. These steps require
no scalar table.

For the remaining cases, Section 2 above covers the negative-target
axial scalar; Section 3 covers the positive-target full-circle scalar
and its norm majorant; Section 4 covers the cut endpoint; and Section 5
covers the variable multiplier. These are all five former polynomial
obligations. Section 6 covers every coarse endpoint table left in the
original source-axis proof. The other endpoint and continuation
arguments in that proof use explicit derivative or projection signs.

Thus every ordered C/L source-axis branch has cost strictly greater
than \(.91\). Reflected reversal, which preserves the cost and center
gap, covers every retained target axis as well. No further C/L scalar
certificate remains to be supplied.
