# An exact one-radial alternating C6 core: positive stress and no seventh square

**Status: exact constructive control and hand saturation proof for one specified physical core. This does not close the whole one-radial family. Root and separate independent full saved-source and direct-prerequisite audits passed.**

The zero-diagonal alternating C6 with exactly one physical radial load cannot be excluded by a universal contradiction involving its six bodies alone. The following exact core exists in the declared radius window, satisfies every true force and torque equation with positive pair magnitudes, and has the required physical masks. For the specified transmitter positions it is saturated: even a seventh independently oriented unit square cannot be added.

The saturation argument is specific to these positions. It must not be applied to other transmitter sliders or used to tick the unrestricted one-radial completion gate.

## 1. Six actual unit squares in the radius window

Put

\[
r=\sqrt2,\quad s=1/\sqrt2,\quad d=r-1/2,\quad K=r+1/2,
\qquad R_0^2=K^2+1/4=5/2+\sqrt2.
\]

The radius belongs to the original interval:

\[
(79/40)^2<R_0^2<1105/256.
\]

For the first strict comparison, \(r>2241/1600\) follows by squaring, with reserve \(97919/2560000>0\). For the second, \(465/256>3/2>r\).

Let

\[
P=(d,1/2),\quad Q=(s-1/2,s+1/2),\quad T=(-1/2,1/2),
\qquad g=(-s,s),\quad u=(-s,-s).
\]

Define the radial square and the upper boundary square by

\[
S=[d,d+1]\times[-1/2,1/2],\qquad
B=Q+[0,1]g+[0,1]u.
\]

The lower boundary square \(C\) is the reflection of \(B\) across the horizontal axis. The three actual side-normal transmitters are

\[
U_+=P+[0,1]g+[-1/2,1/2]u,\qquad
U_- = \text{the horizontal reflection of }U_+,\qquad
W=[-1,0]\times[-1/2,1/2].
\]

These are six genuine unit squares. Their actual contact cycle is

\[
S-U_+-B-W-C-U_--S.
\]

At \(S-U_+\) the singleton is \(P\), a strict side-interior point of \(U_+\). At \(U_+-B\), the shared side is exactly \(Q+[0,1/2]u\). Its unchanged stress application below is the endpoint \(Q\). At \(B-W\), the singleton is \(T\), a strict side-interior point of \(W\). Reflect these assertions for the lower half.

For completeness, all other physical pairs are separated as follows. The largest x-coordinate of \(B,C\) is \(s-1/2<d\), and the largest x-coordinate of \(W\) is zero, so all three avoid \(S\). The squares \(B,C\) lie respectively in \(y\ge1/2\), \(y\le-1/2\). The whole \(U_+\) has \(y\ge(1-s)/2>0\), so it avoids both \(C\) and \(U_-\); the reflected assertion handles \(U_-\) and \(B\). Finally \(U_+\) has \(x+y\ge s>1/2\), while \(W\) has \(x+y\le1/2\); use \(x-y\) for \(U_-\). The adjacent supporting half-planes in the displayed contact descriptions prove their nonoverlap. Thus all fifteen pairs have disjoint open interiors.

The physical circle corners of \(S\) are \(z_S^\pm=(K,\pm1/2)\). The unique circle corner of \(B\) is \(z_B=(-1/2,K)\), and \(z_C=(-1/2,-K)\). The other three squared corner norms of \(B\) are \(1/2,3/2,3/2+r\), all strictly below \(R_0^2\); reflection handles \(C\). The maximum squared corner norm of either \(U_\pm\) is \(11/4\), and that of \(W\) is \(5/4\). Every square is therefore contained in the disk, and exactly \(S,B,C\) are physically circle-touching.

## 2. Original positive forces and torque, with the endpoint mean retained

Put pair magnitude one on each edge of the two channels \(S-U_+-B\), \(S-U_--C\). Put pair magnitude two on each edge of \(B-W-C\). Each transmitter carries its own side-axis normal, so all three reserves are exactly one.

The original circle-force coefficient at each of \(z_S^+,z_S^-\) is

\[
\gamma_S=r/(2K)>0.
\]

The circle-force coefficients at \(z_B,z_C\) are both \(r>0\). Here a circle force is written as its nonnegative coefficient times the actual corner position; this only absorbs the conventional common factor two.

At \(S\), the two outward pair normals are \(g=(-s,s)\) and its horizontal reflection. Their sum is \((-r,0)\), cancelled by

\[
\gamma_S(z_S^++z_S^-)=(r,0).
\]

At \(B\), the outward pair forces are \((s,-s)\) at \(Q\), and \((0,-2)\) at \(T\). Their sum is cancelled by

\[
r z_B=(-s,2+s).
\]

Reflect for \(C\). Opposite forces on each transmitter are equal, aligned with the original channel, and cancel.

Every circle force has zero torque about the origin. The two pair torques at \(S\) are \(+1,-1\). At \(B\), they are

\[
\det(Q,(s,-s))=-1,\qquad \det(T,(0,-2))=1.
\]

Again reflect for \(C\); each transmitter's pair of collinear opposite forces has zero total torque. Thus every actual body's exact force and torque equations hold. There is one positive six-cycle, exactly three loaded bodies with physical masks S,U,U, and no discarded force or changed mean.

The shared-side application \(Q\) is a legitimate endpoint of the actual positive-length intersection. It is not a point-only vertex/vertex contact. All singleton normals are strict in the loaded vertex cone and act in the corresponding transmitter's strict side interior. This preserves the existing strict singleton convention.

In particular, a theorem claiming that every such one-radial core is impossible would be false. Its complete packing obstruction must involve the additional physical squares.

## 3. Universal center conditions for a possible seventh square

For any contained unit square of center \(c\), its farthest corner satisfies

\[
R_0^2\ge |c|^2+|c|+1/2.
\]

The right side is increasing for \(|c|\ge0\) and takes the value \(R_0^2\) at \(|c|=r\). Therefore every possible additional center has \(|c|\le r\). Two interior-disjoint unit squares have center distance at least one, because their open inscribed radius-1/2 disks are disjoint.

The six original centers are

\[
c_S=(r,0),\quad c_W=(-1/2,0),\quad
c_B=(-1/2,b),\quad c_C=(-1/2,-b),\quad
c_{U_\pm}=(a,\pm h),
\]

where

\[
b=1/2+s,\qquad a=3s/2-1/2,\qquad h=1/2+s/2.
\]

We prove that their open radius-one disks cover the entire closed center disk \(|c|\le r\). The following exact elementary bounds will be used:

\[
b^2=3/4+s<7/4,\quad 1/2<a<3/5,\quad
3/4<h<7/8,\quad r-h=a,\quad r<3/2.
\]

## 4. The entire left half of the center disk is covered

Write \(c=(x,y)\), with \(x\le0\); reflect to assume \(y\ge0\).

If \(0\le y\le b/2\), use \(c_W\). For fixed \(y\), its squared distance is convex as a function of \(x\) on \([-\sqrt{2-y^2},0]\). At \(x=0\) it is at most \(1/4+b^2/4<1\). At the other endpoint it is

\[
9/4-\sqrt{2-y^2}\le9/4-\sqrt{2-b^2/4}<1,
\]

because \(b^2<7/4\) gives \(\sqrt{2-b^2/4}>5/4\). Thus the whole interval has distance less than one from \(c_W\).

If \(b/2\le y\le r\), use \(c_B\). At \(x=0\), the squared distance \(1/4+(y-b)^2\) is maximized at an endpoint of the y interval. Its two endpoint values are \(1/4+b^2/4<1\) and \(1/4+(r-b)^2<1\).

At the left circle endpoint, the squared distance is

\[
F(y)=9/4+b^2-\sqrt{2-y^2}-2by.
\]

This is convex on \([b/2,r]\), by continuity at \(r\) and convexity of the negative square root on the interval's interior. At \(b/2\) its value is \(9/4-\sqrt{2-b^2/4}<1\); at \(r\) it is \(1/4+(r-b)^2<1\). Hence it is less than one throughout. Convexity in \(x\) now covers every intervening point. Reflection uses \(c_C\) below the axis.

## 5. The entire right half is covered

First suppose \(x\ge0\), \(|y|\le1/4\). The horizontal distances to \(c_W,c_S\) have minimum at most \((r+1/2)/2\) for every \(0\le x\le r\). Therefore one of these two centers has squared distance at most

\[
\frac{(r+1/2)^2}{4}+\frac1{16}=\frac58+\frac r4<1.
\]

For the remaining upper half, assume \(y\ge1/4\).

If \(0\le x\le1\), use \(c_{U_+}\). The entire rectangle \([0,1]\times[1/4,r]\) satisfies

\[
|x-a|<3/5,\qquad |y-h|<5/8.
\]

Its squared distance is consequently less than \(9/25+25/64=1201/1600<1\).

If \(x\ge1\) and \(y\le1/2\), use \(c_S\): its squared distance is at most \((r-1)^2+1/4<1/2<1\).

Finally suppose \(x\ge1,y\ge1/2\). Circle containment gives \(y\le1\) and \(x\le\sqrt7/2<4/3\). Thus

\[
|x-a|<5/6,\qquad |y-h|<3/8,
\]

so its squared distance from \(c_{U_+}\) is less than \(25/36+9/64=481/576<1\). Reflecting covers the lower half by \(c_{U_-}\).

The open-disk cover is complete, including every dividing line and the circle boundary. A seventh square's center would have distance less than one from an original center, contradicting the necessary center separation. No seventh square fits.

## 6. Exact scope of this control

This is a positive six-body core in the complete target radius window, with all three loaded physical masks, all positive original force magnitudes, the two original radial corner weights, and the actual endpoint means verified exactly. It is a useful counterexample to universal core exclusion and an exact saturation control for a proposed completion method.

The center cover uses the specified positions of \(U_+,U_-,W\). Other physical transverse positions of these transmitters can open real completion space. No assertion here identifies every one-radial core with this one, bounds every arbitrary completion of all such cores, or classifies an original nine-square equality packing. In particular the existing one-radial alternating-C6 roadmap gate remains OPEN.

No numerical search, angle mesh, polynomial certificate, Lean compilation or CI is a premise of the construction or the saturation proof.
