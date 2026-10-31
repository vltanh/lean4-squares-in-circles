# A zero-diagonal alternating six-cycle with at least two radial loads is impossible

**Status: complete continuous-domain hand core exclusion; root and separate independent full exact-source, prerequisite, all-mean geometry and scope audits passed.**

Work in 79/40≤R≤√1105/16. The entire positive component is an alternating six-cycle with three loaded bodies and three unloaded degree-two side-normal transmitters, one between each pair of consecutive loads. Assume at least two loaded bodies have physical two-circle-corner masks. The third loaded body's physical mask is arbitrary.

**Theorem.** This entire family is impossible.

Every original force, physical circle contact, original side mean and all three additional physical squares are retained. The third loaded body is not restricted to singleton contacts, owned axes, adjacent or opposite vertices, or a particular concurrence position. The proof uses its two unchanged applications as arbitrary points of its actual unit square. No unloaded transmitter is assumed physically circle-clear.

## 1. Exact original radial support and distinct ports

Put K=√(R²−1/4), d=K−1, D=4d²+1. The window gives

91/100<d<61/60. (1)

For the lower bound,

(79/40)²−1/4−(191/100)²=101/40000>0.

For the upper,

(121/60)²−1041/256=31/57600>0.

Thus both inequalities in (1) are strict even at the original radius endpoints.

Use the complete radial support cover in RADIAL_LOAD_SIDE_CHANNEL_POCKET_CAPACITY.md, Section 1. In a radial body's actual frame (e,f=Je), every original width-one channel to another loaded body uses a strict inner vertex and a strict normal

p=de+εf/2,
g=−u e+εv f,
ε∈{−1,1}, u,v>0, u²+v²=1. (2)

The exact next-loaded application is p+g. The original transmitter side mean has not changed. The cited support cover excludes the inner radial axis by the boundary-unit distance floor, the tangential axis by far support 5/2>R, and every outer support by circle unshareability or width. It uses no equality of the individual circle weights.

The two actual ports at a radial loaded body must be its different inner vertices. Indeed

det(p,g)=ε(dv+u/2).

Both actual pair magnitudes are positive. Every original circle force has zero torque about the origin, individually, including zero-weight endpoints. If both pair ports had the same ε, the two pair torques would have the same strict sign, contradicting true torque balance. This proves distinctness without placing a radial concurrence inside its square.


## 2. The whole radial/radial channel fixes the two other ports

Choose two radial loads and label them S_+,S_−. In the alternating C6 they are connected by one actual side-normal transmitter. Their two applications have the same norm √(d²+1/4) and distance one. The actual positive outward-height convention therefore normalizes them to

(d,1/2), (d,−1/2). (3)

This is the radial/radial channel geometry of the cited source, Sections 7–8, rotated so the outward direction is +x.

Let φ=arctan(1/(2d)). The two possible radial-axis directions compatible with the upper inner vertex in (3) are 0 and 2φ. Direction 0 would make the actual channel normal a forbidden radial tangential axis. Thus the upper body's radial axis is 2φ. The lower body's is −2φ, by the same exact two-embedding check. Write

e_±=(cos2φ,±sin2φ), f_±=J e_±.

Its other port must be the opposite inner vertex by Section 1. Consequently the two unchanged ports toward the third loaded body C are exactly

Q_+=d e_++f_+/2=(A,B),
Q_−=d e_−−f_−/2=(A,−B),
A=d(4d²−3)/D,
B=(12d²−1)/(2D)=3/2−2/D. (4)

These are actual positions of the original radial units and actual contacts, not a symmetrization of C or any transmitter.

We need only

A>0, 207/200<B<9/8. (5)

The first follows from d>91/100>√3/2. Since B′(d)=16d/D²>0,

B(91/100)−207/200=2633/2156200>0.

For the upper bound, (61/60)²<13/12, with difference 179/3600. Thus D<16/3, giving B<9/8.

The original normals from these ports toward C have strictly negative horizontal components. From (2) they are

g_+=−u_+ e_++v_+ f_+,
g_−=−u_− e_−−v_− f_−,

with all u_±,v_±>0. Because 0<2φ<π/2,

(g_±)_x=−u_± cos2φ−v_± sin2φ<0. (6)

Their corresponding actual C applications are

P_±=Q_±+g_±. (7)

## 3. One original positive-weight C circle corner lies strictly to the left

C has true positive degree two in the full selected component. Let its actual pair magnitudes be m_±>0, and write its original circle resultant as Σ_z γ_z z, with γ_z≥0 and positive total. Absorb the harmless common normalization of circle multipliers into γ. The original force balance gives

Σ_z γ_z z=m_+ g_++m_− g_−. (8)

By (6), the right side has strictly negative horizontal component. Thus at least one original physical circle corner z with positive weight satisfies

z_x<0, |z|=R. (9)

If C is unique this is its unique corner. If it is radial, (8) selects an existing positive-weight corner; the other original weight remains arbitrary and may vanish. No corner, weight or force is replaced.

Since A>0, (9) implies

|z|<|z−(A,0)|. (10)


## 4. A complete corner-to-midpoint bound for arbitrary points of a unit square

Let P,Q be any two points of any closed unit square, let z be any one of its corners, and put

M=(P+Q)/2, ell=|P−Q|∈[0,√2].

Choose own coordinates with z at the origin and the square equal to [0,1]². Write the absolute coordinate differences of P,Q as p,q∈[0,1], so p²+q²=ell². Their midpoint coordinates are bounded above by 1−p/2,1−q/2, and are nonnegative. Hence

|z−M|²≤2−(p+q)+ell²/4. (11)

For 0≤ell≤1, p+q≥ell. For 1≤ell≤√2, p+q≥1, and

(p+q−1)²−(ell²−1)=2(1−p)(1−q)≥0.

Therefore p+q≥1+√(ell²−1). Equation (11) proves the full bound

|z−M|≤C(ell), where

C(ell)=√(2−ell+ell²/4) for 0≤ell≤1,
C(ell)=√(1+ell²/4−√(ell²−1)) for 1≤ell≤√2. (12)

This covers all face-interior points, corner points, owner combinations, shared means and endpoints at once. It does not presume that P,Q are vertices, are on one side, or are the applications of distinct features.

## 5. The channel midpoint and its whole one-variable maximum

Apply Section 4 to the actual P_+,P_−∈C. Let M=(P_++P_−)/2, t=P_+−P_−, ell=|t|. Set O_A=(A,0) and w=t/2−B e_y. By (7),

g_+=M−O_A+w, g_−=M−O_A−w.

Their original unit lengths give the exact identity

|M−O_A|²+|w|²=1.

Since B>1>ell/2, the reverse triangle inequality yields

|M−O_A|²≤1−(B−ell/2)². (13)

Its radicand must be nonnegative; thus every feasible original chord has

2(B−1)≤ell≤√2. (14)

In particular coincident applications are already impossible.

Combine (10), (12), (13) and the triangle inequality:

R=|z|<√(1−(B−ell/2)²)+C(ell)=:Psi_B(ell). (15)

We prove its maximum over the entire feasible interval (14) occurs at ell=1.

For 2(B−1)<ell≤1, put x=1−ell/2, y=B−ell/2. Then y>x>0, and the derivative of the right side of (15) is

(1/2)[y/√(1−y²)−x/√(1+x²)]>0.

For instance the first term is at least y, the second at most x, and y>x. The feasible radicand-zero endpoint follows by continuity.

For 1<ell≤√2, (5) gives

0<B−ell/2<B−1/2<5/8<1/√2.

The derivative of the first square root in (15) is therefore strictly less than 1/2. Write zeta=√(ell²−1)∈(0,1]. The second root equals

C(ell)=(1/2)√((2−zeta)²+1).

Its derivative is at most −1/2: after squaring positive quantities the claim is exactly

(1+zeta²)(2−zeta)²≥zeta²((2−zeta)²+1),

which reduces to (2−zeta)²≥zeta², valid for 0<zeta≤1. Thus Psi_B strictly decreases on this whole interval. Continuity at ell=1 completes the maximum proof, with no missing pole or subinterval:

Psi_B(ell)≤Psi_B(1)=√(3/4−B²+B)+√5/2. (16)


## 6. Exact radius contradiction and whole scope

The quadratic 3/4−B²+B decreases for B>1/2. From (5),

3/4−B²+B<3/4−(207/200)²+207/200=28551/40000<(169/200)².

The final squared reserve is 1/4000. Also √5/2<9/8 has squared reserve 1/64. Equations (15)–(16) therefore imply

R<169/200+9/8=197/100<79/40≤R.

The last strict rational margin is 1/200. This is a contradiction.

All constants and comparisons above are exact; the eight elementary rational reserves were independently recomputed with BigInt arithmetic. No polynomial certificate, sampled-angle box, interval subdivision, Lean or CI is used.

The proof excluded the actual core before making any completion allocation. It covers exactly two radial loads with arbitrary unique C owners and means, and also three radial loads with every original individual weight endpoint. All three extra physical units remain in the original packing. The exact positive degree of C and the exact one-transmitter width-one channels are essential: no higher-degree body or longer channel is silently substituted.

This closes the entire zero-diagonal, at-least-two-physical-radial alternating C6 family. The sole-radial and all-unique/shared zero-diagonal families remain separate.
