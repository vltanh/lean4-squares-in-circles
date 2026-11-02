# Signed weak-outer transfer through transverse gap 5/8

November 2, 2026. Computer exploration of the signed support deficit led
to the following complete hand proof. No numerical optimization result is
a premise. No Lean, Lake, or CI is used.

This manuscript proves a physical two-square transfer and an unconditional
horizontal localization of the original right endpoint pair. Its final
fixed-mask caller explicitly retains the vertical-order premise until
that premise is supplied by a complete separate proof.

## 1. Notation and the signed transfer theorem

Put

\[
 a=46,\qquad b=27/2,\qquad k_*=207/16,\qquad T=211/4,
 \qquad V=5/8.
\]

For an original physical unit square S, let h_S(n) be its centered
support in direction n, and write h_S=h_S((1,0)). Suppose two original
unit squares C,D have disjoint open interiors, with center difference

\[
 c_D-c_C=(d,v),\qquad 0<d<\sqrt2,\qquad 0\le v\le V.
\tag{1}
\]

Assume that D has the original frame

\[
 u_D=(\alpha,\beta),\quad w_D=(-\beta,\alpha),\qquad
 \alpha\ge\beta\ge0,\quad\alpha^2+\beta^2=1.
\tag{2}
\]

The sign in (2) is a hypothesis; it is not obtained by reflecting D
individually. Put

\[
 h=(\alpha+\beta)/2,\quad j=(\alpha-\beta)/2,\qquad
 \sigma=(a-k_*)\beta-a(1-\alpha).
\tag{3}
\]

**Transfer theorem.** Under (1)--(2),

\[
             d+h_C-h_D+\sigma/a\ge1.
\tag{4}
\]

The inequality is strict if beta>0, or if the horizontal comparison is
weak, d<h_C+h_D. In particular it is strict on the fixed weak-link
domain, including its aligned-D face.

## 2. All owned physical separators are retained

The separating-axis theorem supplies an axis n of one of the two original
squares, signed so that

\[
              n\cdot(c_D-c_C)\ge h_C(n)+h_D(n)\ge1.
\tag{5}
\]

Its horizontal component c is positive: otherwise its left side is at
most v<=5/8. Write s=|n_y| and t=s/c. If n_y<0 and s>=c, its left side
is at most cd<=d/sqrt(2)<1, also impossible. Thus a downward separator
has t<1. An upward separator may have any finite t>=0.

For either sign of n_y and every unchanged C-frame,

\[
 h_C(n)+c h_C\ge(1+c^2+cs)/2.
\tag{6}
\]

To prove (6), reflect the coordinates for this scalar calculation if
needed. On each projection-sign interval the left side is a positive
linear combination of sine and cosine, hence has its minimum at an
endpoint of that interval. The endpoint frames are parallel to e or n.
Their values are c+s/2 and (1+c^2+cs)/2. The latter is no larger because
their difference is (1-c)(1-c-s)/2<=0. This minimizes a support
expression; it does not replace a physical square.

For an upward normal, the actual D-frame (2) gives

\[
 h_D(n)=
 \begin{cases}
 ch-sj,&0\le t\le t_D:=\beta/\alpha,\\
 cj+sh,&t\ge t_D.
 \end{cases}
\tag{7}
\]

For a downward normal, reflect its vertical component just for evaluating
supports. D then has negative chirality. On the already proved range
0<=t<1 its support is no smaller than the right side of (7): the other
chirality has support ch+sj; comparison with the two branches in (7)
gives respectively 2sj>=0 and beta(c-s)>=0.

In (5), the vertical contribution is at most sV, for either sign.
Combining (5)--(7), setting r(t)=sqrt(1+t^2), and subtracting h_D gives

\[
 d+h_C-h_D\ge
 \begin{cases}
 F_-(t)=r/2+(1+t)/(2r)-t(j+V),&0\le t\le t_D,\\
 F_+(t)=r/2+(1+t)/(2r)-\beta+t(h-V),&t\ge t_D.
 \end{cases}
\tag{8}
\]

For a downward normal the second branch is used only up to t=1. For an
upward normal it is valid for the entire remaining half-line. Thus no
physical owner, sign, or steep normal has been discarded.

## 3. Three endpoint values suffice

The common nonlinear term A(t)=r/2+(1+t)/(2r) satisfies

\[
 A''(t)=\frac{3t(t-1)}{2(1+t^2)^{5/2}}.
\tag{9}
\]

Both branches in (8) are concave on their subintervals of [0,1]. On
t>=1, A' is increasing and A'(1)=1/(2sqrt(2)); hence

\[
 F_+'(t)\ge1/(2\sqrt2)+h-5/8>0.
\]

Consequently the complete minimum is bounded by the three endpoint
values

\[
 F_-(0)=1,\qquad
 F_-(t_D)=F_+(t_D)=(1-V\beta)/\alpha,\qquad
 F_+(1)=\sqrt2+j-V.
\tag{10}
\]

We prove that adding sigma/a makes each value at least one, strictly
except for the first value when beta=0.

First, sigma/a=beta(23/32-z), where

\[
 z=\frac{1-\alpha}{\beta}=\frac{\beta}{1+\alpha}
       \in(0,\sqrt2-1]
\]

when beta>0. Therefore sigma>0, since sqrt(2)-1<23/32.

For the middle value, the required positive numerator, divided by beta,
is

\[
 \frac{\alpha\sigma/a+(1-\alpha)-V\beta}{\beta}
 =\frac{64z^3-43z^2+3}{32(1+z^2)}.
\tag{11}
\]

The numerator decreases on [0,sqrt(2)-1], because its derivative is
2z(96z-43)<=0 there. For example sqrt(2)-1<5/12<43/96 proves the
sign directly. Its minimum is

\[
 406\sqrt2-574=2(203\sqrt2-287)>0,
 \qquad 2\cdot203^2-287^2=49.
\tag{12}
\]

For the last value in (10),

\[
 \sqrt2+j-V+\sigma/a-1
 =\sqrt2-2-V+\tfrac32\alpha+\tfrac7{32}\beta.
\tag{13}
\]

The last two terms form a positive sine/cosine expression, concave on
the folded-angle interval [0,pi/4]. Its minimum is at an endpoint and
equals 55/(32sqrt(2)). Thus (13) is bounded below by

\[
 \frac{119}{32\sqrt2}-\frac{21}{8}>0,
 \qquad 119^2-2\cdot84^2=49.
\tag{14}
\]

This proves strict (4) when beta>0. If beta=0, sigma=0 and t_D=0.
Weakness d<h_C+1/2 rules out a horizontal physical separator. The
remaining branch has t>0, F_+(0)=1 and F_+(1)>1. Concavity makes its
chord strictly greater than one for 0<t<=1, and it is increasing for
t>=1. This proves the strict weak-link assertion also on beta=0.

## 4. An unconditional horizontal localization in 001/00

Now retain the entire original-nine fixed predicate 001/00 at
Q=1105/256, with main chain A,B,C,D and actual short chain E,F,G. Set
r=sqrt(Q). Write g_S=1/(4h_S). The inherited bounds are

\[
 |c_S|<91/60,\quad r<133/64,\quad
 h_S\ge1/2,\quad h_S+g_S\ge1,\quad g_S\ge1/(2\sqrt2).
\tag{15}
\]

The actual first two main links give

\[
 x_C>h_C-1/60,
 \qquad d=x_D-x_C<31/30<\sqrt2.
\tag{16}
\]

The cone link C,D gives d>=g_C+g_D, hence

\[
 x_D>59/60+1/(2\sqrt2)>4/3.
\tag{17}
\]

In particular x_G-x_D<91/60-4/3=11/60<1.

For the other direction, apply the accepted physical cap to (A,E) in
direction e=(1,0). Sum the two actual main links and the two actual
short links into that cap. It implies

\[
 a(x_C-h_C)+b(x_G-h_G)\ge a+b-T=b/2.
\tag{18}
\]

Put Delta=x_D-x_G. Because h_C+g_C>=1 and h_G>=1/2,

\[
 x_C-h_C\le x_D-1-g_D,\qquad
 x_G-h_G\le x_D-\Delta-1/2.
\]

Substitution in (18) yields

\[
 b\Delta\le(a+b)(x_D-1)-a g_D.
\tag{19}
\]

Containment gives x_D+h_D<=r. Also, for h>=1/2,

\[
 (a+b)h+\frac{a}{4h}-T
 =(h-1/2)\left(\frac{119}{2}-\frac{23}{h}\right)\ge0.
\tag{20}
\]

Therefore

\[
 b\Delta\le(a+b)r-T-(a+b)<1459/128,
 \quad\text{so}\quad
                 x_D-x_G<1459/1728<1.
\tag{21}
\]

Together with (17), this proves |x_D-x_G|<1 without any assumption on
their vertical order or either extra square.

If y_G>y_D, every usable signed physical separator from D to G has
positive vertical component: otherwise its value on c_G-c_D is at
most |x_G-x_D|<1, whereas its support sum is at least one. Thus the
vertical-order premise has a precise physical consequence, not merely
a choice of a favorable separator.

## 5. Conditional fixed-mask caller with the signed cap

Assume y_D-y_C lies in [0,5/8], D has the positive chirality (2), and
y_G>y_D. Reflect the horizontal coordinate for the right cap. D then
has the negative chirality in
`SIGNED_NEGATIVE_MAIN_UPWARD_SEPARATOR_CAP_INDEPENDENT_PROOF.md`, while
the physical separator to G has positive vertical component by Section 4.
That cap gives

\[
 a(x_D-h_D)+b(x_G-h_G)+\sigma\le T.
\]

The ordinary left cap, applied to A,E, gives

\[
 a(-x_A-h_A)+b(-x_E-h_E)\le T.
\]

The transfer theorem and the actual first two main links imply

\[
 x_D-x_A-h_A-h_D+\sigma/a
 \ge 2h_B+d+h_C-h_D+\sigma/a>2.
\]

The actual short links give x_G-x_E-h_E-h_G>=2h_F>=1. Adding the
two cap inequalities contradicts 2a+b=2T. This excludes this complete
conditional subdomain even at closed Q. Every selected unit is an
unchanged original, and all nine units remain present.

The reflection y->-y covers the corresponding reversed transverse sign
and chirality simultaneously. It does not reflect a single original.
The y_G>y_D premise must be established, or its complement excluded,
before this caller can be credited with any larger domain. This source
alone does not close 001/00, 100/00, A.2, or any other fixed mask.
