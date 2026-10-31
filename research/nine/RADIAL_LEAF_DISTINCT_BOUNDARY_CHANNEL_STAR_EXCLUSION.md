# A radial-leaf root cannot feed distinct boundary endpoints through normal channels

Date: October 26, 2026.

**Status: complete Sections 1--7 accepted after independent full-source
and physical-scope review, including the repeated-endpoint extension.**
See REVIEW_RADIAL_LEAF_CHANNEL_STAR_ROOT_2026_10_26.md.
This extends the accepted two-channel fork theorem to arbitrary root
degree under an explicit endpoint hypothesis. Every nonleaf positive
force at the root must be an actual unloaded normal-channel force,
and all of the far endpoints must physically touch the circle. The
first proof treats pairwise distinct endpoints; Section 7 retains
repeated endpoints by exact algebraic grouping and requires only
that at least two endpoint bodies are distinct. No positive force
is removed to arrange these conditions.

The D and tilted-S root forms follow from the arbitrary-degree
arguments already recorded in
RADIAL_LEAF_TWO_BOUNDARY_CHANNEL_FORK_EXCLUSION.md, Section 3.1.
The new ingredient here is an aggregate force-and-torque argument for
the full aligned-S family. It keeps every side-axis mean, including
all endpoints, and requires no root-degree bound or computational
certificate.

## 1. Original premises and common support bound

Work with the original physical packing and selected certificate in

\[
 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},\qquad
 d=\sqrt{R^2-\frac14}-1,\qquad \delta=d-1<\frac1{60}.
\tag{1}
\]

Let A have one genuine positive degree-one neighbor L. Its remaining
positive edges are indexed by 1<=i<=m, where m>=2. Each starts an
actual normal channel from A to Q_i, with at least one true unloaded
degree-two internal transmitter. The physical units Q_i are pairwise
distinct and each physically touches the containing circle. Their
positive degrees and their other forces are unrestricted; they may
have zero total circle load. All original physical units remain.

Write e for the radial outward leaf direction, lambda>0 for its
actual pair-force magnitude, and mu_i>0,n_i,p_i for each unchanged
root-channel magnitude, outward unit direction and application. The
genuine leaf makes A physically circle-clear. Thus its complete
equations are

\[
             \lambda e+\sum_i\mu_i n_i=0,
                  \qquad\sum_i\mu_i\det(p_i,n_i)=0.
\tag{2}
\]

The leaf's actual origin moment is zero. Each channel has its actual
reserve w_i>=1 and support h_i=h_A(n_i), with

\[
 A\subseteq\{x:n_i\cdot x\le h_i\},\qquad
 Q_i\subseteq\{x:n_i\cdot x\ge h_i+w_i\}.
\tag{3}
\]

The sharp contained-unit center bound gives

\[
 |c_{Q_i}|\le d+\frac12,
 \qquad h_i+w_i+\frac12\le n_i\cdot c_{Q_i},
                         \qquad h_i\le\delta.
\tag{4}
\]

The genuine leaf-root central-disk theorem gives
dist(0,A)<=max(delta,0). If delta<0, it makes h_i>=0, contradicting
(4). Hence every putative configuration has

\[
                          0\le\delta<\frac1{60}.
\tag{5}
\]

These deductions require no equation at a far endpoint. They apply
to every original mean and every permissible transmitter width.

## 2. The D and tilted-S forms are already excluded at this degree

For D, the full root is
[rho-1,rho] times [-b,a], with rho=R-sqrt(2), a,b>0,
a+b=1 and 1/2<rho<3/4. Every channel support in (4) therefore
forces |(n_i)_x|<1/15 and |(n_i)_y|>14/15. The complete vertical
equation in (2) supplies at least one upward and one downward
channel. Their support sum exceeds 14(a+b)/15=14/15 and is at
most 2delta<1/30, a contradiction. The other forces remain in the
equation establishing the opposite-sign pair.

For tilted S, use the entire own-frame support table of Section 3
of the accepted fork source. Every feasible channel moment about
the actual leaf vertex is nonpositive, including all side-axis
means. The full second-component balance is
sum mu_i y_i=lambda b>0 in those inward axes, so at least one
channel has a strictly negative moment. Their complete sum cannot
vanish. This argument already permits every finite m and uses no
far-endpoint circle premise.

Thus only the aligned S root remains to be considered.

## 3. Every upward channel at an aligned root is nearly westward

Rotate e east, and reflect across the horizontal axis if needed, so
the full aligned root domain is

\[
 A=[\delta,d]\times[-b,a],\qquad
 a,b\ge0,\quad a+b=1,\quad a\ge\frac12\ge b.
\tag{6}
\]

The actual leaf application is (d,0). Both endpoint root sliders
remain, including b=0. Define the westward cone

\[
             \mathcal W=\{n:n_x<0,\ |n_y|<-n_x/14\}.
\tag{7}
\]

If n is an actual upward channel normal, n_y>0. It cannot have
n_x>=0, because then

\[
 h_A(n)=d n_x+a n_y
      \ge a(n_x+n_y)\ge a\ge\frac12>\delta.
\tag{8}
\]

Thus write n=(-c,s), c,s>0, c^2+s^2=1. Its actual application
is the upper-left root vertex, and (4) gives

\[
       -\delta c+as\le\delta,
             \qquad s\le4\delta<\frac1{15},
             \qquad c>\frac{14}{15}.
\tag{9}
\]

Consequently s/c<1/14, so every upward channel belongs to W.
Every horizontal channel also belongs to W: the rightward unit
normal has support d>delta and is impossible, leaving only west.
Its original application remains any actual mean on the entire
left root side.

## 4. The full root equations force two channels in the westward cone

If all channels are horizontal, m>=2 supplies two channels in W.
Otherwise the complete vertical force equation supplies both upward
and downward channels. If at least two are upward, Section 3 already
supplies the desired pair. If there is exactly one upward channel
and at least one horizontal channel, those two again belong to W.

The only case left is exactly one upward channel and no horizontal
channels. Write its actual weighted vector as

\[
                         \mu n=(-P,V),\qquad
                         P,V>0,\quad V<P/14.
\tag{10}
\]

Every other channel is downward. Divide these actual forces according
to their horizontal signs:

\[
 \begin{array}{ll}
 \text{left downward:}&(-Q_j,-W_j),\quad Q_j,W_j>0,\\
 \text{nonleft downward:}&(X_k,-W_k),\quad X_k\ge0,\ W_k>0.
 \end{array}
\tag{11}
\]

Let Q=sum_j Q_j, W_L=sum_j W_j, W_R=sum_k W_k. Empty sums are
allowed. Vertical balance retains all forces and reads

\[
                               V=W_L+W_R.
\tag{12}
\]

Take full root torque about the fixed point o=(delta,0), which
belongs to the actual root. The genuine leaf still has zero moment
about o because its force and application are horizontal. The upward
application is (delta,a), so its torque contribution is aP.
Each left-downward application is the actual lower-left vertex
(delta,-b), contributing -bQ_j.

For a nonleft-downward channel, its application is (xi_k,-b), with
delta<=xi_k<=d. If X_k>0 it is the lower-right vertex xi_k=d;
if X_k=0 it may be any actual bottom-side mean. Set
t_k=xi_k-delta in [0,1]. Its exact torque is

\[
                         -t_k W_k+bX_k.
\tag{13}
\]

Thus the full torque equation gives

\[
           aP=bQ+\sum_k(t_kW_k-bX_k)\le bQ+W_R.
\tag{14}
\]

No nonleft force or mean was discarded from the equality; the final
inequality simply uses their actual t_k<=1 and bX_k>=0.

Suppose none of the downward channels belongs to W. For every
left-downward channel this means W_j>=Q_j/14, hence Q<=14W_L.
Using (10),(12),(14),

\[
 \begin{split}
 aP&\le14bW_L+W_R\\
   &\le\max(14b,1)(W_L+W_R)\\
   &=\max(14b,1)V\\
   &<\max(b,1/14)P\le aP.
 \end{split}
\tag{15}
\]

The last comparison uses a>=1/2 and a>=b. This contradiction
includes b=0, all empty-subsum cases, and every bottom-side mean
endpoint. A downward channel in W must therefore exist, providing
a second channel there in addition to the original upward one.

We have proved a degree-free statement about the actual root forces:

**Westward-pair lemma.** Under (2)--(6), with at least two actual
channels, at least two distinct root edges have normals in W.

## 5. Distinct physical boundary endpoints contradict angular separation

For every channel at the aligned root, the actual root point
o=(delta,0) gives h_i>=delta(n_i)_x>=-delta. Equations (3)--(5)
therefore imply

\[
 n_i\cdot c_{Q_i}>\frac{89}{60},\qquad
                         |c_{Q_i}|<\frac{91}{60}.
\tag{16}
\]

Its endpoint center direction is consequently at angular distance
less than pi/12 from n_i, because

\[
              \frac{89}{91}>\cos\frac\pi{12}.
\tag{17}
\]

The fixed exact check is the one in the accepted fork source:
cos^2(pi/12)=(2+sqrt(3))/4<15/16 and
16 times 89^2>15 times 91^2.

Each normal in W is at angle less than pi/36 from west. Indeed
tan(pi/36)>sin(pi/36)>1/12>1/14; the middle inequality follows
from the exact triple-angle comparison
sin(pi/12)>1/4. Thus the two endpoint centers supplied by Section 4
are each within

\[
                         \frac\pi{36}+\frac\pi{12}=\frac\pi9
\tag{18}
\]

of west, and their mutual minor separation is less than 2pi/9.

The far endpoints are distinct physical circle-touching unit squares
by the original hypotheses. CENTERED_INNER_ARC.md gives their strict
minor center separation greater than 2pi/9. This contradiction closes
the aligned S case, and hence every genuine leaf/root form.

## 6. The whole theorem and its exact limitations

**Distinct-boundary-channel star theorem.** In (1), no physical
selected certificate has a genuine leaf root whose other positive
forces are at least two actual unloaded normal channels to pairwise
distinct physical circle-touching far endpoints.

The proof retains arbitrary actual root degree, every positive
magnitude, all actual support means and their endpoints, both genuine
leaf forms, every far-endpoint physical circle mask and all additional
physical squares. The far endpoints may have additional forces or zero
total circle weight. All internal channel bodies retain their true
unloaded degree-two equations. No higher-degree body is turned into a
transmitter.

For a degree-three root this includes the accepted two-boundary-channel
fork and its complete C5 load23 S/D application. The present theorem
also covers higher-degree channel stars wherever the stated actual
premises hold. It does not add or retick that original C5 consequence.

Pairwise distinctness is an explicit hypothesis of the theorem as
proved so far. Section 7 explains exactly how endpoint repetitions
can be retained by grouping equal channel normals, without discarding
forces. Merely having two boundary endpoints somewhere in a collection
with other clear endpoints still does not ensure that the selected
westward channels end at boundary bodies; that weaker hypothesis is
not substituted here.

The theorem supplies no whole larger coarse-cell closure without a
separate exact graph/load join. It leaves the one-channel-plus-direct-
boundary-neighbor C5 load13 case outside its premises. No new roadmap
label, finite sign packet, numerical pose assertion, Lean compilation
or CI is used.

## 7. Repeated endpoints can be retained by exact force grouping

There is a stronger whole theorem with the same proof. Require that
every nonleaf positive root edge starts an actual unloaded normal
channel of reserve at least one to a physical circle-touching body,
and that the collection of far endpoints contains at least two
distinct physical bodies. Endpoint repetitions are now allowed.

First consider two actual channels from the unchanged root A to the
same physical endpoint Q. For each channel, its genuine root and far
applications p_i,q_i satisfy

    q_i-p_i=w_i n_i,
    n_i.x<=n_i.p_i for x in A,
    n_i.y>=n_i.q_i for y in Q.

Thus every displacement y-x in the convex difference Q-A has norm
at least w_i, and the actual displacement q_i-p_i has norm w_i.
Each channel vector is a shortest vector of Q-A. The shortest vector
of a convex set is unique: if two distinct vectors had the same
minimal norm, their midpoint would have strictly smaller squared
norm by the parallelogram identity. Consequently all channels with
this same endpoint have exactly the same reserve and direction,

    w_i=w_Q>=1, n_i=n_Q.

This is also the direct content of the accepted parallel-transmission
Lemma N.2. No further contact, load or degree premise at Q is used.

For the whole group I_Q of original channels ending at Q, put

    M_Q=sum_(i in I_Q) mu_i>0,
    pbar_Q=(sum_(i in I_Q) mu_i p_i)/M_Q.

The point pbar_Q belongs to A's actual support face in direction n_Q,
by convexity. The corresponding weighted mean of the far applications
is pbar_Q+w_Q n_Q and belongs to Q. More significantly, the complete
root force and moment sums are exactly unchanged:

    sum_(i in I_Q) mu_i n_i = M_Q n_Q,
    sum_(i in I_Q) mu_i det(p_i,n_i)
                         = M_Q det(pbar_Q,n_Q).

These identities are only algebraic groupings of the original terms.
The point pbar_Q is not asserted to be a new physical pair application
or a permitted replacement of any individual mean. Every individual
root contact, internal transmitter, original force and actual mean
remains in the physical packing and in the underlying equations.

The D and tilted-S moment arguments of Section 2 apply verbatim to
these grouped terms. For aligned S, Sections 3--4 use only positive
magnitudes, support-face membership and the full force and moment
sums. Every unique-vertex application remains that vertex under a
weighted mean; a side-axis group mean remains in its complete side
interval, including both endpoints. All of their hypotheses therefore
hold with the grouped quantities M_Q,n_Q,pbar_Q. There are at least
two groups by the new endpoint premise.

The westward-pair lemma now supplies two distinct endpoint groups.
Their actual far centers are distinct physical boundary centers,
and each still satisfies Section 5's unmodified support and center
bounds. The same strict angular contradiction follows.

**Boundary-channel star theorem with repetitions.** A genuine leaf
root cannot have all of its remaining positive forces supplied by
actual unloaded normal channels of reserve at least one to physical
circle-touching endpoints, when at least two of those endpoint bodies
are distinct. This holds for arbitrary actual root degree and every
original physical leaf form, force magnitude and mean.

The root's actual nonleaf edges need not have different far endpoints.
The theorem still requires every such edge to belong to a stated real
normal channel and every far endpoint to be physically boundary. It
does not handle an omitted root force, a higher-degree internal body,
a clear far endpoint, or a collection with just one distinct endpoint.
No new original gate is counted by this extension alone.
