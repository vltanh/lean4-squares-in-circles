# Eight squares at the exact least five-corner radius

## Theorem

Let $\widehat q=\widehat R^2$ be the least squared radius of the projected
five-corner family, equivalently the least admissible root of the polynomial
stationary system in [HUMAN_FIVE_CORNER.md](HUMAN_FIVE_CORNER.md), Lemma 8.
Then eight unit squares with disjoint open interiors fit in the disk of
radius $\widehat R$. The construction has three independently variable
positions. Consequently

$$
\boxed{R_8\le\widehat R.}                                  \tag{1}
$$

This closes the construction at the globally selected exact family radius.
Every assertion below follows from the defining equations and proved
analytic bounds. No numerical approximation to the root, root-isolation
program, or interval check of additional square pairs is used.

The opposite unrestricted inequality $R_8\ge\widehat R$ is a separate
structural problem. Also, identifying this least admissible root with the
previously isolated candidate $q_*$ is not assumed in the theorem.

## 1. Bounds supplied by the stationary equations

Choose a minimizing family configuration, whose existence and interior
stationarity were proved in HUMAN_FIVE_CORNER.md. Put $q=\widehat q$ and
use its notation

$$
\begin{aligned}
r&=\sqrt{q-u^2},&w&=\sqrt{q-v^2},\\
U&=\sqrt{q-(2-u)^2},&V&=\sqrt{q-(2-v)^2},&U+V&=3,\\
c&=\cos t,&s&=\sin t,&e&=(c,s),&f&=(-s,c),\\
k_1&=2-c(r-1)+su,&k_2&=1+cv-s(w-1),&k_1^2+k_2^2&=q.
\end{aligned}                                               \tag{2}
$$

The new order theorem in
[HUMAN_FAMILY_CLOSURE.md](HUMAN_FAMILY_CLOSURE.md), Proposition 1, and
the enclosure in [HUMAN_FAMILY_ENCLOSURE.md](HUMAN_FAMILY_ENCLOSURE.md)
give

$$
\frac{79}{40}<R<\frac{\sqrt{9789}}{50}<1.9788<2,
\qquad 0<t<\arctan\frac15,
\qquad \frac12<v<u<1.                                      \tag{3}
$$

Also $k_1>1$ and $k_2>1/2$ by the uniform bounds in
HUMAN_FIVE_CORNER.md. The following convenient rational consequences will
suffice:

$$
\begin{gathered}
\frac7{10}<u<1,\qquad
\frac{17}{10}<r<\frac{93}{50},\qquad
\frac{17}{10}<w<\frac{48}{25},\\
\frac32<U<\frac{41}{24},\qquad
r>U,\qquad w>V,\\
c>\frac{49}{50},\qquad s<\frac15,\qquad
cs<\frac5{26},\qquad k_1>\frac{51}{50}.                    \tag{4}
\end{gathered}
$$

Here are the derivations. The function
$x\mapsto\sqrt{q-(2-x)^2}$ increases, so $u>v$ gives $U>V$, hence
$U>3/2$. At the symmetric position
$m=2-\sqrt{q-9/4}$ one has $U=V=3/2$, so $u>m>7/10$;
the last inequality follows from $q<9789/2500<9/4+169/100$.
Now

$$
r^2<\frac{9789}{2500}-\frac{49}{100}<\left(\frac{93}{50}\right)^2,
\qquad
w^2<\frac{9789}{2500}-\frac14<\left(\frac{48}{25}\right)^2.
$$

Since $u,v<1$, both $r^2,w^2$ exceed
$(79/40)^2-1>(17/10)^2$. Also $U^2<q-1<2257/576-1=(41/24)^2$.
The differences $r^2-U^2=4(1-u)$ and $w^2-V^2=4(1-v)$ give
$r>U$ and $w>V$.

For $h=\tan t<1/5$, use $c=1/\sqrt{1+h^2}$,
$s=h/\sqrt{1+h^2}$ and $cs=h/(1+h^2)$. The last function increases
for $0\le h\le1$ and takes the value $5/26$ at $h=1/5$.
Finally $k_1\ge3-R>51/50$, since $R<99/50$.

## 2. The eight square centers

Define the five points

$$
P_1=(r,-u),\quad P_2=(U,2-u),\quad
P_3=(-V,2-v),\quad P_4=(-w,-v),\quad
P_5=-k_1e-k_2f.                                             \tag{5}
$$

Every one has squared norm $q$. Six squares have the standard horizontal
and vertical frame and the following centers:

| Square | Center |
| --- | --- |
| $A$ | $(r-1/2,1/2-u)$ |
| $B$ | $(U-1/2,3/2-u)$ |
| $C$ | $(U-3/2,z_C)$ |
| $D$ | $(U-5/2,3/2-v)$ |
| $E$ | $(1/2-w,1/2-v)$ |
| $T$ | $(U-3/2,z_T)$ |

The other two squares have frame $(e,f)$ and centers

$$
H=P_5+\frac{e+f}{2},\qquad
G=H+e+\eta f.                                               \tag{6}
$$

Let $\epsilon=1/100000$. The three parameters may be chosen
**independently** in the closed intervals

$$
\begin{aligned}
\frac{343}{1000}-\epsilon
&\le z_C\le\frac{343}{1000}+\epsilon,\\
\frac{13431}{10000}-\epsilon
&\le z_T\le\frac{13431}{10000}+\epsilon,\\
-\epsilon&\le\eta\le\epsilon.
\end{aligned}                                               \tag{7}
$$

A square with center $p$ and frame $(a,b)$ means
$p+[-1/2,1/2]a+[-1/2,1/2]b$. Thus (5)--(7) specify full unit squares.

## 3. Every square is contained in the disk

For a standard square centered at $(x,y)$, the largest squared vertex
norm is $(|x|+1/2)^2+(|y|+1/2)^2$. The signs in (3)--(4) show that
$P_1,P_2,P_3,P_4$ are farthest vertices of $A,B,D,E$, respectively.
Their norms are exactly $R$ by (2).

The middle squares have positive center coordinates, and

$$
U-1<\frac{17}{24},\qquad
z_C+\frac12<z_T+\frac12\le\frac{184311}{100000}.
$$

Both are strictly contained, because

$$
\left(\frac{79}{40}\right)^2
-\left(\frac{17}{24}\right)^2
-\left(\frac{184311}{100000}\right)^2
=\frac{165097511}{90000000000}>0.                           \tag{8}
$$

For $H$, the two local vertex-coordinate intervals are
$[-k_1,1-k_1]$ and $[-k_2,1-k_2]$. Since $k_1>1$ and $k_2>1/2$,
their greatest absolute values are $k_1$ and $k_2$. Hence $P_5$ is a
farthest vertex and $H$ is contained.

For $G$, the intervals are $[1-k_1,2-k_1]$ and
$[\eta-k_2,\eta+1-k_2]$. Both choices of the first coordinate have
squared magnitude at most $k_1^2-\delta$, where

$$
\delta=\min(2k_1-1,4(k_1-1))>\frac2{25}.
$$

Every second coordinate has magnitude at most $k_2+\epsilon$. Since
$k_2<\sqrt q<2$,

$$
|\text{any vertex of }G|^2
\le q-\delta+2k_2\epsilon+\epsilon^2
<q-\frac2{25}+4\epsilon+\epsilon^2<q.                        \tag{9}
$$

Every whole square is contained because it is the convex hull of its
vertices and the disk is convex.

## 4. The fifteen pairs among the standard squares

They form three horizontally separated columns:

| Column | Squares | Horizontal intervals or bounds |
| --- | --- | --- |
| Left | $D,E$ | $D$ has right edge $U-2$; $E$ has right edge $1-w<U-2$ |
| Middle | $C,T$ | Both occupy $[U-2,U-1]$ |
| Right | $A,B$ | $B$ has left edge $U-1$; $A$ has left edge $r-1>U-1$ |

The strict inequalities follow from $w>V=3-U$ and $r>U$.
Within the left column, $E$'s top and $D$'s bottom are both $1-v$.
Within the right column, $A$'s top and $B$'s bottom are both $1-u$.
The two middle heights satisfy

$$
z_T-z_C\ge1+\frac{1}{10000}-2\epsilon>1.
$$

Thus every pair in different columns is separated horizontally, and every
pair in a common column is separated vertically. This covers all fifteen
pairs among $A,B,C,D,E,T$.

## 5. The tilted pair and the four pairs with A and E

The two tilted squares are separated along $e$, since
$e\cdot(G-H)=1$ for every allowed $\eta$.
The sum of a standard square's and a tilted square's half-widths along
either $e$ or $f$ is

$$
W=\frac{1+c+s}{2}.
$$

Equations (2), (5), and (6) give the exact center identities

$$
e\cdot(A-G)=W,\qquad e\cdot(A-H)=W+1,\qquad
f\cdot(E-H)=W.                                              \tag{10}
$$

The first identity is independent of $\eta$ because $e\cdot f=0$.
These are separating-line checks for three of the four pairs.

For the remaining pair $E,G$, first take $\eta=0$. The difference
between $G$'s leftmost $x$ coordinate and $E$'s rightmost $x$ coordinate
is

$$
\Delta_x=c\bigl(c(r+w-2)-1-s(u-v)\bigr).
$$

The bounds in (3)--(4) give

$$
\Delta_x>
\frac{49}{50}\left(\frac{49}{50}\frac75-1-\frac1{10}\right)
=\frac{833}{3125}>\frac14.                                 \tag{11}
$$

Changing $\eta$ by at most $\epsilon$ changes a vertex's $x$ coordinate
by at most $s\epsilon<\epsilon$. The gap stays positive, so $E,G$
remain separated horizontally throughout (7).

## 6. The remaining eight pairs

At $\eta=0$, the top of $G$ has the exact height

$$
Y_G=cs(r+w-2)-s^2u-c^2v
   =-v+s^2(v-u)+cs(r+w-2).
$$

Using $u>v>1/2$, $r+w-2<89/50$ and $cs<5/26$ gives

$$
Y_G< -\frac12+\frac5{26}\frac{89}{50}
=-\frac{41}{260}.                                         \tag{12}
$$

The top of $H$ is $Y_G-s<Y_G$. Allowing (7), both tilted tops are
strictly below $-41/260+\epsilon$.
The lowest possible bottom among $B,C,D,T$ is the bottom of $C$:

$$
z_C-\frac12\ge-\frac{157}{1000}-\epsilon.
$$

Indeed $B,D$ have positive bottom heights $1-u,1-v$, while $T$ is above
$C$. The gap between this lower bound and the bound on either tilted top
is positive, since

$$
\frac{41}{260}-\frac{157}{1000}-2\epsilon
=\frac9{13000}-\frac2{100000}>0.                            \tag{13}
$$

Thus a horizontal line separates each of $G,H$ from each of $B,C,D,T$.
These are the final eight pairs.

The fifteen column pairs, the tilted pair, the four pairs checked in
(10)--(11), and these eight pairs total $15+1+4+8=28$, all pairs of eight
squares. Together with containment, this proves the theorem and the three
independent slider intervals (7).

## 7. What this settles

The least-root definition now comes with an exact eight-square
realization proved by ordinary inequalities. No extra assumption about
the tiny previously isolated root is needed to obtain (1).

Consequently a proof that every eight-square packing below
$\widehat R$ yields the five-corner obstruction would immediately give
$R_8=\widehat R$. Identifying $\widehat R$ with a particular numerical
root specification and deriving the obstruction globally remain separate
claims; neither is inferred from this construction.
