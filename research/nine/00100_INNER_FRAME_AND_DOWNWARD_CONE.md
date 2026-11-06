# A narrow inner frame and a stronger downward-cone obstruction

This chapter proves two hand implications for the original `001/00`
domain. The first uses only the four originals A,B,C,D. The second uses
their constraints and the original B/H nonoverlap. Its final application
uses the complete nonpositive-D C-slant hand/table proof. All squares retain their
own frames; physical boundary contacts are allowed throughout.

These implications do **not** exclude the entire Cb882 or Cd402 original,
the full mask, or the unrestricted nine-square domain. In particular,
the complementary Cb882 domain identified at the end remains open.

Put

\[
 Q=\frac{1105}{256},\qquad r=\sqrt Q<\frac{133}{64},
 \qquad \rho=\frac{91}{60}.
\]

For a physical original S let h_S be its coordinate projection
halfwidth and g_S=1/(4h_S) its concentric aligned-inset halfwidth.
We use the [foundation](FOUNDATION.md), Part A, and the unary inset
bound in [the extraction chapter](EXTRACTION.md), Lemma 2.1:

\[
 \frac12\le h_S\le\frac1{\sqrt2},\quad
 g_S\ge\frac1{2\sqrt2},\quad h_S+g_S\ge1,
 \quad |c_S|<\rho,
 \quad |x_S|-g_S<\frac{17}{16}.                 \tag{1}
\]

The inequality h+g>=1 is the identity
h+1/(4h)-1=(2h-1)^2/(4h). The inset is an actual subset of the
same original, and its open interior is contained in the original's
open interior. Every original also contains its open radius-one-half
incircle. These facts justify all distances below.

## 1. The inner original B has a narrow frame

Assume AB and BC are actual positive horizontal projection links,
and CD is a positive horizontal center-cone link. Thus

\[
\begin{aligned}
 x_B-x_A&\ge h_A+h_B,\\
 x_C-x_B&\ge h_B+h_C,\\
 x_D-x_C&\ge g_C+g_D.
\end{aligned}                                                   \tag{2}
\]

The last inequality follows from the contained insets and the cone
comparison. Strict weakness of CD is not needed in this lemma.
Adding gives

\[
 (x_D-g_D)-(x_A+h_A)
 \ge 2h_B+h_C+g_C\ge2h_B+1.                    \tag{3}
\]

On the other hand, (1) and h_A>=1/2 give

\[
 x_D-g_D<\frac{17}{16},\qquad
 -x_A-h_A\le |c_A|-h_A<\frac{61}{60}.
\]

Consequently

\[
 \boxed{\quad h_B<\frac{259}{480},\qquad
                  g_B>\frac{120}{259}>\frac{37}{80}.\quad}       \tag{4}
\]

Indeed 17/16+61/60=499/240, and 9600>9583 verifies the
last comparison. Every inequality used here holds even in the closed
Q-disk. There is no endpoint-orientation or extra-square assumption.

One can state the frame consequence without radicals. Write a canonical
side of B as (a,b), with a>0, |b|<=a, and put t=b/a. Then

\[
 h_B=\frac{1+|t|}{2\sqrt{1+t^2}},\qquad
                         \boxed{|t|<1/12.}                      \tag{5}
\]

The displayed function increases for 0<=|t|<=1. At |t|=1/12 its
value is 13/(2 sqrt(145)), which exceeds 259/480 because

\[
 13^2\,480^2-(2\cdot259)^2\,145=30620>0.
\]

This proves (5) on the whole angle interval, including t=0 and both
orientation signs.

Neither short-chain link was used. Thus (4)--(5) apply to every
`001/de` witness, for all four choices of de. Reversing both coordinate
axes and both chains gives h_C<259/480 and |t_C|<1/12 for every
`100/de` witness. This is a frame bound, not a full-mask exclusion.

## 2. Coordinate bounds needed in the downward cone

The same hypotheses imply

\[
                  -31/60<x_B<-27/64.                            \tag{6}
\]

For the lower bound use x_A>-rho and h_A+h_B>=1.
For the upper bound, the right projection of D is at most r. Using
(2) and h_D+g_D>=1 gives x_C+g_C<=r-1. Subtract
h_C+g_C>=1 and then apply BC to get

\[
 x_B+h_B\le x_C-h_C\le r-2.
\]

Thus x_B<=r-5/2<-27/64. These arguments also supply

\[
                  29/60<x_C<3/4<4/5.                            \tag{7}
\]

The lower bound follows from BC and (6). For the upper bound use
x_C+g_C<=r-1, r<25/12 and g_C>1/3.

## 3. A complete exclusion on the nonpositive horizontal half-plane

**Lemma.** Under (1)--(2), no additional original H can satisfy all
three inequalities

\[
 y_B\le-\frac{67}{120},\qquad
 y_H-y_B\le-|x_H-x_B|,\qquad x_H\le0.            \tag{8}
\]

*Proof.* Put k=y_B-y_H and z=|x_H-x_B|. The cone says k>=z;
the original incircles say k^2+z^2>=1. Therefore

\[
 k\ge1/\sqrt2>7/10,\qquad
 y_H<-67/120-7/10=-151/120<-5/4.                \tag{9}
\]

The center bound and the exact comparison

\[
 (7/8)^2+(5/4)^2-\rho^2=\frac{401}{14400}>0
\]

imply |x_H|<7/8. Together with x_H<=0 and (6), this gives

\[
 z<\max\{31/60,\ 7/8-27/64\}=31/60,            \tag{10}
\]

since 7/8-27/64=29/64<31/60.

Let R_B be B's *actual contained aligned inset*. Its distance from
c_H is at least 1/2. Otherwise the open incircle of H meets the
closed inset; an arbitrarily small move into the inset interior gives
an interior intersection of the two original squares.
The distance formula for a closed rectangle is

\[
 \operatorname{dist}(c_H,R_B)^2
 =\max\{z-g_B,0\}^2+\max\{k-g_B,0\}^2.          \tag{11}
\]

Here k>7/10 and g_B<=1/2, so the second maximum is k-g_B.
Equations (4) and (10) give

\[
 \max\{z-g_B,0\}<\frac{31}{60}-\frac{37}{80}
                         =\frac{13}{240}.
\]

It follows from (11) that

\[
 (k-g_B)^2>
 \frac14-\left(\frac{13}{240}\right)^2
 >\left(\frac{119}{240}\right)^2.
\]

The last strict inequality is exactly
14400-13^2-119^2=70>0. Taking positive square roots and using
(4) now gives

\[
 k>\frac{37}{80}+\frac{119}{240}=\frac{23}{24}.
\]

Therefore y_H=y_B-k<-67/120-23/24=-91/60=-rho,
contrary to (1). This proves the lemma. \(\square\)

The proof uses the incircle of H against the inset of B, rather than
only the distance between their centers. All inequalities are necessary
conditions for the original squares; no new packing is substituted.

## 4. The whole low-B downward cone for nonpositive D

For the normalized `001/00` original-nine domain with nonpositive
canonical D tilt and y_D-y_C>2/3, the
[complete C-slant assembly](00100_C_SLANT_LOWER_COMPLEMENT.md)
proves y_C+(7/8)x_C<-7/32 using only the physical foundation and
the printed rational tables. It implies the following geometric fact:

> No additional original X satisfies x_X>=0 and y_X<=y_C.

Here is the full implication. Put p=x_C and q=-y_C. By (7) and
C-slant, 29/60<p<4/5 and q>77/120>5/8. Moreover

\[
 0<\rho+y_C<623/480-(7/8)p.
\]

The latter affine expression is positive throughout [29/60,4/5].
The convex quadratic p^2+(623/480-(7/8)p)^2 has maximum at an
endpoint; its two reserves below one are respectively 11/14400
and 23/9216. Therefore p^2+(rho-q)^2<1.

Suppose an additional center is (u,-w), u>=0 and w>=q. If u<=p,
its squared distance from C is at most p^2+(rho-q)^2<1,
contradicting the two original incircles. If u>=p, put
z=u-p>=0 and t=w-q>=0. Incircle separation gives
z^2+t^2>=1 and z+t>=1. Hence its squared center norm is at least

\[
 p^2+q^2+1+2pz+2qt
 \ge(89/60)^2+(5/8)^2=\rho^2+93/320>\rho^2,
\]

again impossible. This proves the displayed geometric fact without
an archived C-slant or G-order input.

**Proposition.** In that unchanged nonpositive-D domain
no additional original H can
satisfy

\[
 y_B\le-67/120,\qquad y_H-y_B\le-|x_H-x_B|.       \tag{12}
\]

*Proof.* Section 3 excludes x_H<=0. In the other case (9) and the
center bound still give 0<x_H<7/8 and y_H<-5/4. The C-slant
input forces y_H>y_C. Equations (1) and (7) give

\[
 0<y_H-y_C<\rho-5/4=4/15,\qquad
 |x_H-x_C|<4/5.
\]

For the second bound, both x_H and x_C are positive, x_C<4/5,
and x_H-x_C<7/8-29/60=47/120<4/5. Hence

\[
 |c_H-c_C|^2<(4/5)^2+(4/15)^2=32/45<1,
\]

contrary to the original C/H incircles. These two horizontal cases
cover every H, including x_H=0. \(\square\)

## 5. Exact application and remaining predicate

The literal Cb882 escape conditions give
y_H-y_B<=-|x_H-x_B|, as decoded in the earlier chapter. Therefore
every strict-radius witness in the *same complete Cb882 original*
necessarily satisfies

\[
                         \boxed{y_B>-67/120.}                   \tag{13}
\]

This improves the previously proved bound y_B>-2/3. The complete
partition of the low-B domain in (12) is the two-row hand table:

| Additional original H | Original physical information used | Contradiction |
|---|---|---|
| x_H<=0 | Original B inset and H incircle; (4), (6), (9)--(11) | y_H<-rho |
| x_H>0 | Complete hand/table C-slant proof and original C/H incircles; (7), (9) | Squared center distance <32/45<1 |

No original ancestry, mask bit, frame sign, extra order or physical pair
is removed from the calling theorem. The **entire complementary domain**
y_B>-67/120, together with every original Cb882 constraint, remains open.
No whole-original or full-mask closure is credited.

All arithmetic needed for the new lemmas is printed above. Local
computations suggested this direction and checked the rational identities;
no optimization result or unsuccessful numerical search is a proof input.
The new arguments have been author-checked. No independent review, Lean,
Lake, CI or kernel verification is claimed.
