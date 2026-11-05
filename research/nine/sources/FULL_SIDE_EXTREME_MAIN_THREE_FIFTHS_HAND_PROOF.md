# A full side's extreme main has center height beyond three fifths

November 2, 2026. Hand proof; no Lean, CI, or computational certificate.
Candidate scalar direction checks suggested the test vectors; the proof
below gives the full signed-normal and orientation argument.

Put Q=1105/256 and r=sqrt(Q). The elementary bound r<25/12 will
suffice for the new positive-normal terminal.

## 1. Statement

Suppose physical unit squares with disjoint open interiors in the closed
Q-disk contain an actual horizontal four-chain
\[
                         M_0<_xM_1<_xM_2<_xM_3.
\]
If two outsiders with centers x>=29/60 both have center heights below
y_M2, then
\[
                             \boxed{y_{M_2}>3/5.}          \tag{1}
\]
If both are above M2, then y_M2<-3/5. Horizontal reflection gives
the corresponding two statements on the left side.

The theorem is unconditional on outsider orientations and physical
separating-axis owners. It does not replace center order by actual
vertical projection separation.

## 2. A near-main clearance that retains the outsider's halfwidth

Let a physical unit F be interior-disjoint from an aligned square of
halfwidth g. Suppose their horizontal center gap is D and
\[
                         g-D>3/8.
\]
If h is F's coordinate projection halfwidth, then their vertical center
gap V satisfies
\[
                         V\ge g+h-1/128.                 \tag{2}
\]

Horizontal separation is impossible because D<g. The separating-axis
theorem supplies either the vertical axis, giving V>=g+h, or a side
normal of F. Write the absolute side components of F as c>=s>=0,
c^2+s^2=1, and put epsilon=g-D>3/8. The side-normal alternatives
give
\[
 V\ge g+\frac{1/2+\epsilon s}{c}.
\]
The alternative component ratio is larger: after multiplying by the
positive product cs, the difference has numerator
(c-s)[1/2+epsilon(c+s)]>=0. A vanishing component is handled directly
by the vertical axis.

Put t=s/c and k=(c-s)/2. Since h=(c+s)/2,
\[
 \frac{1/2+\epsilon s}{c}-h=t(\epsilon-k).
\]
Also k=(1-t)/(2sqrt(1+t^2))<=(1-t)/2. Thus
\[
 t(k-\epsilon)\le t(1/8-t/2)\le1/128.
\]
This proves (2), including the coordinate-aligned case.

## 3. A positive-normal two-square cap with a whole-square floor

There cannot be two physical units U,V in the closed Q-disk with
disjoint open interiors, such that
\[
 l:=29/60\le x_U,x_V\le u:=13/12,\qquad y_U\le y_V,
 \qquad y_U-h_U\ge-1/8,                                  \tag{3}
\]
and which admit a separating unit normal directed from U to V of the
form n=(a,b), a>=0, b>0, a^2+b^2=1.

Write H_S(w) for support halfwidth. The exact two-vector minimum is
\[
 H_S(w)+H_S(z)\ge\frac12\left(L+
          \frac{|w\cdot z|+|\det(w,z)|}{L}\right),
 \qquad L=\max(|w|,|z|),                                 \tag{4}
\]
as proved in [TWO_SQUARE_CENTRAL_STRIP_CAP_HAND_PROOF.md](TWO_SQUARE_CENTRAL_STRIP_CAP_HAND_PROOF.md).
In particular,
\[
                    H_U(n)+b h_U\ge1/2+b(a+b)/2.          \tag{5}
\]
Take t=1/2 and m=(t,b). Put L=|m|=sqrt(5/4-a^2).

### 3.1. The normal range 0<=a<=1/2

Here t-a>=0, so the separator and (3) imply
\[
 m\cdot c_V\ge tl-b/8+b h_U+H_U(n)+H_V(n).
\]
Both horizontal endpoints in this bound are the lower endpoint l;
the coefficient t-a is positive. Also L>=1 and
\[
 |n\cdot m|+|\det(n,m)|=t(a+b)+b^2-ab.
\]
Containment, (4), and (5) give
\[
 r\ge F(a):=\frac12+\frac A L
       +\frac{t(a+b)+b^2-ab}{2L^2},
 \quad A=\frac{89}{120}-\frac b8+\frac12ab+\frac12b^2.    \tag{6}
\]
We show F increases on [0,1/2].

First, differentiation and collection of terms give
\[
 (A/L)'=\frac{N_1}{L^3},
\quad
 N_1=\frac{b^3}{2}+\frac{b^2-a^2}{8b}
                  +\frac{a}{32b}-\frac a{120}+\frac{a^3}{2}.
\]
Here b>6/7, b^2-a^2>=1/2, b<=1, and a<=1/2. Hence
\[
 N_1>\frac{108}{343}+\frac1{16}-\frac1{240}
       =\frac{108}{343}+\frac7{120}>\frac{37}{100}.
\]
Also L^3<=5sqrt(5)/8<3/2, so
\[
                               (A/L)'>37/150.             \tag{7}
\]

The last numerator in (6) equals
L^2+(b-t)(t-a). Consequently
\[
 F=1+A/L+G,
 \quad G=\tfrac12(t-a)f(b),\quad
 f(b)=\frac{b-t}{b^2+t^2}.
\]
For sqrt(3)/2<=b<=1, one has 0<f<=2/5 and
0<f'<3/8. To check the latter, its numerator is
-b^2+b+1/4; it decreases on this interval, and its largest value
sqrt(3)/2-1/2 is less than 3/8. Its denominator L^4 is at least one.
Since a(t-a)<=1/16 and b>6/7,
\[
 G'=-\tfrac12f+\tfrac12(t-a)f'b'
      >-1/5-7/512.                                      \tag{8}
\]
Equations (7)--(8) give F'>0.

At a=0,
\[
 F(0)=\frac{11}{10}+\frac{67}{30\sqrt5}
       >\frac{11}{10}+\frac{134}{135}
       =\frac{113}{54}>\frac{25}{12}>r,                  \tag{9}
\]
where sqrt(5)<9/4 was used. Thus the whole first normal range is
impossible.

### 3.2. The normal range 1/2<=a<1

Now t-a<=0. The separator uses x_U>=l and x_V<=u, so
\[
 m\cdot c_V\ge-\frac35a+tu-b/8+b h_U+H_U(n)+H_V(n).
\]
Here L<=1 and
\[
 |n\cdot m|+|\det(n,m)|=b(a+b)+(a-b)t.
\]
Equations (4)--(5) therefore give
\[
 rL\ge N:=\frac{37}{24}-\frac7{20}a-\frac38b+ab+b^2.
                                                                    \tag{10}
\]
We prove N>(25/12)L on 0<=b<=sqrt(3)/2.

For 0<=b<=7/20, the coefficient b-7/20 of a in (10) is
nonpositive. Use a<=1-b^2/2 and L<=1/2+b^2. Then
\[
 N-\frac{25}{12}L
 \ge\frac3{20}+\frac58b-\frac{109}{120}b^2-\frac12b^3
 \ge\frac3{20}+\frac{59}{240}b>0.                        \tag{11}
\]
The last inequality uses b<=7/20.

For 7/20<=b<=sqrt(3)/2, that coefficient is nonnegative.
Concavity gives a>=1-(2/3)b^2, and a tangent bound gives
L<=5/8+b^2/2. Hence
\[
 N-\frac{25}{12}L\ge
 P(b):=-\frac{53}{480}+\frac58b+\frac{23}{120}b^2-\frac23b^3.
                                                                    \tag{12}
\]
The polynomial P is concave on [7/20,7/8], since
P''=23/60-4b<0. This interval contains the present one. Its
endpoint values are
\[
 P(7/20)=\frac{991}{9600}>0,
 \qquad P(7/8)=\frac{1049}{7680}>0.
\]
Thus P>0 throughout. This contradicts (10), completes the second
normal range, and proves the positive-normal cap.

## 4. Join the two signed caps to prove the extreme-main theorem

Suppose contrary to (1) that y_M2<=3/5 and both right-side outsiders
are below M2. The unrestricted inner-clearance theorem gives each
outsider y<3/5-97/100=-37/100. Reflect y and label them U,V with
\[
                            37/100<y_U\le y_V.
\]
The side-strip center cap proves y_U<9/16. Therefore the new low-center
bound in [ORIENTED_SIDE_PAIR_CAP_AND_LOW_OUTSIDER_BAND_HAND_PROOF.md](ORIENTED_SIDE_PAIR_CAP_AND_LOW_OUTSIDER_BAND_HAND_PROOF.md)
gives
\[
                         l\le x_U<47/80.
\]
The main center belongs to (29/60,31/60). Hence the horizontal center
gap between U and M2 is less than 5/48. The main's contained aligned
square has halfwidth g>15/31, so
\[
 g-D>15/31-5/48>3/8,
\]
with exact reserve 7/1488 in the last comparison. Applying (2) gives,
in the reflected coordinate,
\[
 y_U-h_U>15/31-1/128-y_{M_2}
            \ge15/31-1/128-3/5>-1/8.                    \tag{13}
\]
The final rational reserve is 21/19840.

Any separating unit normal from U to V has positive vertical component:
their horizontal center gap is below 3/5, whereas the sum of physical
supports is at least one. If its horizontal component is nonpositive,
the oriented asymmetric cap from
[ORIENTED_SIDE_PAIR_CAP_AND_LOW_OUTSIDER_BAND_HAND_PROOF.md](ORIENTED_SIDE_PAIR_CAP_AND_LOW_OUTSIDER_BAND_HAND_PROOF.md) applies,
using x_U<47/80<4/5 and y_U>37/100. If its horizontal component is
positive, (13) supplies the whole-square floor required in Section 3.
Both alternatives are impossible. This proves y_M2>3/5.

The coordinate reflections prove the other three versions of (1).
All signed normals and all physical orientation choices have been retained.

## 5. Consequences for full-side marker patterns

After the standard strict-counterexample center expansion to closed-disjoint
units at Q, the side-marker order theorem identifies the actual center
order of the three members of each full side. We have now proved
\[
 \text{main at bottom marker}\Longrightarrow y_M<-3/5,
\quad
 \text{main at top marker}\Longrightarrow y_M>3/5.         \tag{14}
\]
Together with the reconstructed middle-main theorem, the three ranges are
\[
 (-\infty,-3/5),\qquad (-7/20,7/20),\qquad (3/5,\infty).
\]

If both full-side mains occupy their top markers, every outsider center
lies below both mains. Indeed an outsider in either half-plane cannot
be above its corresponding main, because that would force
y>3/5+97/100=157/100>91/60. It is therefore below that main by more
than 97/100, and hence
\[
                  y_F<91/60-97/100=41/75<3/5.
\]
The reflected conclusion holds if both mains occupy bottom markers.

These are new necessary restrictions on the genuine nine-body geometry.
They do not declare the entire full-side pattern impossible, do not
replace center bounds by whole-square cap bounds, and do not by themselves
close unrestricted A.2 or nine-square equality.
