# The exceptional five-square tree core has total capacity nine

**Status:** hand proof with two independent mathematical audits. This theorem covers all
transverse parameters of the five-body family and arbitrary orientations of
every additional square. No numerical search or sampled grid is a premise.

Use the exact family from
[EXPANDED_TREE_INVENTORY.md](EXPANDED_TREE_INVENTORY.md). Its constants are

\[
 d^4+32(1+\sqrt2)d+20-32\sqrt2=0,\quad 8/25<d<1/3,
 \quad a=d^2/4,\quad A=1+a,\quad B=1-d,
\]

\[
 k=1/\sqrt2,\quad h=A+1/2,\quad
 C=(1-a)/A,\quad S=d/A,\quad n=(-C,S),\quad m=(S,C).
\]

Here n,m are orthonormal. The disk radius satisfies

\[
 R_\kappa=1+\sqrt2-d,\qquad q_\kappa=R_\kappa^2=(A+1)^2+1/4.
\]

The five fixed squares are

\[
\begin{array}{ll}
 H=[a-1,a]\times[-B,d],
 &U=[a,A]\times[b-1/2,b+1/2],\\
 E=[A,A+1]\times[-1/2,1/2],
 &L=\{r n+t m:A\le r\le A+1,\ |t|\le1/2\},\\
 D=\{(x,y):|x|+|y+B+k|\le k\},
 &d-1/2-a\le b\le1/2.
\end{array}                                                    \tag{1}
\]

**Theorem.** Every packing in D_(q_kappa) containing (1) has at most nine
squares. Equivalently, at most four additional unit squares fit.

The proof confines every additional center to one of two small rectangles.
One rectangle accommodates at most three centers at mutual distance one;
the other accommodates at most one.

## 1. Center constraints and exact constants

Let p=(x,y) be the center of an additional square. Its maximum squared vertex
norm is at least ||p||^2+||p||+1/2. Since

\[
                       h^2+h+1/2=q_\kappa,
\]

we have ||p||<=h. Its open inscribed disk of radius 1/2 is disjoint from each
core square interior. Thus its distance from each closed core square is at
least 1/2. Its distance from every core center, and from every other additional
center, is at least one.

The following bounds follow directly from 8/25<d<1/3 and elementary squares:

\[
\begin{gathered}
 16/625<a<1/36,\quad 1<A<37/36,\quad
 2/3<B<17/25,\quad 3/2<h<55/36<153/100,\\
 35/37<C<20/21,\qquad 31/100<S<1/3,\qquad
 7/10<k<71/100,\\
 \sqrt{h^2-1}<29/25,\qquad
 \sqrt{6a}<5/12,\qquad
 \sqrt{h^2-(1-a)^2}<6/5.                                  \tag{2}
\end{gathered}
\]

We also use

\[
 d-a>184/625,
 \qquad a+B<441/625<12/17<k.                               \tag{3}
\]

The first inequality holds because d-d^2/4 increases on this interval, and
its value at 8/25 is 184/625. The second follows from a+B=1-(d-a).

### 1.1 No additional center is too far below the hub

We claim

\[
                              y>-B-1/2.                   \tag{4}
\]

The slight strictness needed here follows from exact rational estimates.
The defining polynomial is negative at d_0=163/500, because sqrt(2)>24/17
and

\[
 d_0^4+32d_0+20+32(24/17)(d_0-1)
       =-5999500063/1062500000000<0.
\]

Hence d>d_0. Also k<99/140, by squaring. The defining polynomial, after
substitution a=d^2/4 and sqrt(2)=2k, gives the identity

\[
 h^2-B^2-B-k-1/2=(3-4d)k-3/2+d-a.
\]

The right side increases with k and decreases with d in the present range.
Consequently

\[
 h^2-B^2-B-k-1/2
 <(3-4d_0)(99/140)-3/2+d_0-d_0^2/4
 =-8783/7000000<0.                                        \tag{5}
\]

If y<=-B-1/2, the squared distance from p to D's center (0,-B-k) would be

\[
\begin{split}
 x^2+(y+B+k)^2
 &\le h^2-2(B+k)(B+1/2)+(B+k)^2\\
 &=h^2-B^2-B+1/2-k<1,
\end{split}
\]

contradicting center separation. This proves (4).

## 2. No additional center lies to the left of H

Write ell=1-a. We prove

\[
                               x\ge-\ell=a-1.             \tag{6}
\]

Suppose x<-ell, and split by height.

**Above H, y>d.** In L's frame put r=p dot n and t=p dot m. Then

\[
 r>C\ell+Sd=(\ell^2+d^2)/A=A.
\]

Since ||p||<=h<A+1, its radial coordinate lies within L's radial interval.
Distance at least 1/2 from L therefore requires |t|>=1. But
t=Sx+Cy>-Sh>-1, so t>=1. It follows that r<=sqrt(h^2-1) and

\[
 x=-Cr+St\ge-C\sqrt{h^2-1}+S
 >-(20/21)(29/25)+31/100=-1669/2100>-4/5.
\]

This contradicts x<-ell<-35/36.

**Along H's vertical interval, -B<=y<=d.** Distance from H forces
x<=a-3/2. The norm bound then gives |y|<=sqrt(6a)<5/12. Hence

\[
 p\mathbin{\cdot}n\ge C(3/2-a)-S\sqrt{6a}
 >(35/37)(53/36)-(1/3)(5/12)=835/666>5/4.
\]

L's center is h n. Thus

\[
 \|p-hn\|^2\le2h^2-2h(5/4)<275/324<1,
\]

again contradicting center separation.

**Below H, y<-B.** Put X=-x>ell and Y=-y>B. If Y<=11/10, the squared
distance to H's lower-left corner is

\[
                             (X-\ell)^2+(Y-B)^2.
\]

For fixed Y it increases with X. On the bounding arc X=sqrt(h^2-Y^2), it
is a constant minus twice the concave function
ell sqrt(h^2-Y^2)+BY. Its maximum over B<=Y<=11/10 is therefore at an
endpoint. At Y=B its square root is less than

\[
                   (\sqrt{2449}-35)/36<1/2.
\]

At Y=11/10, we have X<107/100, X-ell<1/10 and Y-B<13/30, so the squared
distance is less than 1/100+(13/30)^2=89/450<1/4. Both endpoints contradict
the required distance from H. Consequently Y>11/10.

Now X<107/100 and Y<6/5 by (2). D's left vertex is (-k,-B-k), and

\[
 0<X-k<37/100,\qquad 0<B+k-Y<29/100.
\]

The squared distance to that vertex is less than
(37/100)^2+(29/100)^2=221/1000<1/4, also impossible. These three cases
prove (6).

## 3. The core contains a thin horizontal rectangle

For every allowed b, H, U and E together contain

\[
                       [a-1,A+1]\times[0,d-a].             \tag{7}
\]

Indeed their horizontal intervals tile [a-1,A+1], each lower edge is at or
below zero, and each upper edge is at least d-a. The lower endpoint of the
b interval in (1) is exactly what is needed for U's upper edge.

By (6) and ||p||<=h<A+1, the horizontal coordinate of p lies within (7).
Distance at least 1/2 from that rectangle forces

\[
                 y\ge d-a+1/2\quad\hbox{or}\quad y\le-1/2. \tag{8}
\]

We bound these upper and lower center regions separately.

## 4. The upper region has capacity three

An upper center has y>=d-a+1/2>79/100. It also satisfies

\[
                      -4/5<x<6/5,\qquad y<153/100.        \tag{9}
\]

The upper y bound follows from h. For the right x bound, x<A gives it
immediately. If x>=A, then x<A+1, and distance from E requires y>=1.
Thus x<=sqrt(h^2-1)<29/25<6/5.

For the left bound, use r=p dot n and t=p dot m. Here t>0, because
x>=a-1>-1, y>79/100, C>35/37 and S<1/3. Distance from L gives the following
three lower bounds on x=-Cr+St:

- If r<=A-1/2, then x>=-C(A-1/2).
- If A-1/2<=r<=A, then
  x>=min{-C(A-1/2),-CA+S}. To see this in the only nontrivial range
  1/2<=t<=1, put z=A-r. Clearance from L gives
  t>=1/2+sqrt(1/4-z^2), with 0<=z<=1/2. The resulting expression
  -CA+Cz+S/2+S sqrt(1/4-z^2) is concave in z, so its minimum is at an
  endpoint. The ranges t<=1/2 and t>=1 give the same bounds directly.
- If r>=A, then r<=h<A+1, so t>=1 and
  x>=-C sqrt(h^2-1)+S.

The first two quantities exceed -19/36 and -69/100, respectively. The
third exceeds -1669/2100, as in Section 2. Each is greater than -4/5,
proving (9).

Four upper centers, ordered by their horizontal coordinates, would have
vertical differences strictly below 74/100=37/50. Since every pair has
distance at least one, each consecutive horizontal gap would exceed
sqrt(1131)/50. Their total horizontal span would therefore exceed

\[
                         3\sqrt{1131}/50>2,
\]

where the strict inequality follows from 9*1131=10179>10000. This contradicts
the width two in (9). Thus there are at most three upper centers.

## 5. The lower region has capacity one

By (4) and (8), a lower center has

\[
                         -B-1/2<y\le-1/2.
\]

It must have x>a. Otherwise (6) places x in H's horizontal interval, where
the displayed vertical range makes its distance from H less than 1/2.
We claim in fact x>A.

Suppose a<x<=A. Put q=y+B, g=x+q and w=x-q. We have
-1/2<q<=B-1/2<9/50. The rotated-coordinate description of the diamond D
is -2k<=g<=0 and 0<=w<=2k.

- If w<0, then 0<x<q<9/50. The center is at squared distance less than
  2(9/50)^2<1/4 from D's top vertex (0,-B), impossible.
- If 0<=w<=2k, then g>-1/2>-2k. A point with g<=0 would be in D; hence
  clearance requires g>0 and g/sqrt(2)>=1/2, or g>=k.
  Write z=-y-1/2>=0 and j=1/2+k-B. This gives x>=j+z. Because x<=A,
  we have 0<=z<=A-j, and (3) gives
  A-j=1/2+a+B-k<1/2. The squared distance to E's lower-left corner is

  \[
  (A-x)^2+z^2\le(A-j-z)^2+z^2\le(A-j)^2<1/4,
  \]

  again impossible.
- If w>2k, then x>2k-1/2>k. At D's right vertex (k,-B-k), the coordinate
  differences satisfy
  0<q+k<x-k<=A-k<1/3. The squared distance is less than 2/9<1/4.

These cases exclude x<=A. Now x>A and x<=h<A+1 put the center over E's
horizontal interval, so its negative height must satisfy y<=-1. Therefore

\[
                         1<x<6/5,\qquad -6/5<y\le-1.     \tag{10}
\]

Here x<=sqrt(h^2-1)<29/25, and the lower y bound follows from
y>-B-1/2>-59/50. The rectangle (10) has diameter sqrt(2)/5<1, so it contains
at most one additional center.

## 6. Complete the capacity count

Every additional square has its center in the upper or lower region by (8).
Sections 4 and 5 give capacities three and one. Thus at most four squares
can be added to the five-body core, for a total of at most nine.

This excludes the entire exceptional q_kappa family from any ten-square
packing, not only one parameter value or one stress realization. Combined
with the expanded tree inventory, the remaining positive-tree completion
problem in its stated radius window is the staggered four-square S-S chain.
The positive-graph cyclic branch is unaffected by this argument.
