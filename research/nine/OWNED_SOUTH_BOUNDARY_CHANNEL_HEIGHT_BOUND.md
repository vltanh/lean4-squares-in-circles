# The original side return of a lower boundary unit has a low unit-channel endpoint

Date: October 27, 2026.

**Status: complete analytic scalar theorem with two explicit exact
univariate polynomial certificates, submitted for full review.** The
certificate has 30 coefficients on one closed interval. It is not an
angle mesh or a sampled pose argument.

## 1. Exact scalar statement and actual interpretation

Let

    1/3<=g<=21/50, b>=t>=0, b²+t²=1, R>2,
    Y=g+b+t, X=sqrt(R²−Y²)>0, x=X−b+t,
    tau=b(xY/X−g).

Define the actual unit-channel endpoint height

    q_y=−g+t−b*tau.                                   (1)

**Theorem.** q_y<=−1/3. The inequality is strict if g>1/3 or b>t.
In particular it is strict in the original low aligned S-root domain.

The intended caller keeps a real unit

    B=(x,−g)+[0,1](b,−t)+[0,1](−t,−b)

with unique physical circle corner (X,−Y). Its incoming root force
has outward normal North, and its original return is the owned
normal (−b,t) at the actual mean
(x,−g)+tau(−t,−b). The full B2 equations give the displayed tau;
the actual side-normal transmitter has unit width, so its far
original endpoint has height (1). No mean is chosen by this theorem.

## 2. Monotone radius and convex depth reduction

Put k=b−t>=0 and S=b+t. Since x=X−k, direct expansion gives

    q_y=−g−k(1+bt)+b² k Y/X.                          (2)

Throughout the stated domain, Y<=21/50+sqrt(2)<37/20<2.
Replacing R by 2 decreases X and therefore weakly increases (2).
For fixed b,t define its resulting upper bound

    F(g)=−g−k(1+bt)+b² k (g+S)/sqrt(4−(g+S)²).        (3)

The last term is convex in g. In fact the second derivative of
u/sqrt(4−u²) is 12u/(4−u²)^(5/2)>0. Hence F is convex on
[1/3,21/50], including the affine k=0 case. It suffices to prove

    F(1/3)<=−1/3, F(21/50)<−1/3.                     (4)

For k=0 the first is equality and the second is immediate. Assume
k>0 for the first endpoint. At g=1/3 it is equivalent to

    b²Y/sqrt(4−Y²)<1+bt.

Both sides are positive. At g=21/50 put delta=13/150; the needed
strict inequality is

    b² k Y/sqrt(4−Y²)<k(1+bt)+delta,

whose right side is again positive. These are legitimate positive
squaring steps, with no zero denominator or sign case omitted.

## 3. Two exact polynomial identities

Use the exact half-angle parameter z=t/(1+b). Because b>=t>=0,

    0<=z<=sqrt(2)−1<5/12,
    A=1+z², B=1−z², T=2z,
    b=B/A, t=T/A,
    K=B−T, L=A²+BT, Y_i=g_i A+B+T,
    g_0=1/3, g_1=21/50.

All A factors are positive. At the first endpoint the positive
squared comparison in Section 2 is exactly P_0(z)>0, where

    P_0=4L²A²−Y_0²(L²+B⁴).

At the second endpoint put D_1=KL+(13/150)A³. The exact comparison
is P_1(z)>0, where

    P_1=D_1²(4A²−Y_1²)−B⁴K²Y_1².

Their full coefficient lists, in increasing powers of z, are

    9 P_0:
    4, −16, 64, 144, 292, 160, 560, −256,
    508, −336, 208, −80, 28;

    56250000 P_1:
    18333171, −243089800, 1083164568, −852829400,
    −1017825612, −4046689800, 7165087176, −8708591000,
    22765217970, −6563911000, 13817385576, −219529800,
    −387768012, 1236410600, −534697032, 163670200,
    152982771.

These identities retain the full radical inequalities from Section 2;
no physical parameter is replaced by a numerical solution.

## 4. Complete rational positivity on the whole interval

If P(z)=sum_(i=0)^N p_i z^i, its Bernstein coefficients after
z=(5/12)u, 0<=u<=1, are exactly

    beta_j=sum_(i=0)^j p_i (5/12)^i binom(j,i)/binom(N,i).

Thus

    P((5/12)u)=sum_(j=0)^N beta_j binom(N,j) u^j(1−u)^(N−j).

The following complete integer lower lists give **10000 beta_j**
strictly greater than the corresponding positive entry, in order:

    N=12, P_0:
    4443, 3826, 3395, 3205, 3326, 3855, 4914,
    6666, 9323, 13161, 18547, 25954, 36006;

    N=16, P_1:
    3258, 2132, 1285, 698, 346, 204, 236, 402,
    654, 937, 1191, 1357, 1381, 1227, 900, 472, 136.

Every coefficient is strictly positive, so both polynomials are
strictly positive on the whole closed interval, including both
endpoints. The exact arithmetic is reproduced in
`certificates/house_tdb_owned_south_channel_height_check.py` using
only integer arithmetic and rational fractions. It independently
expands the defining expressions, checks both entire coefficient
lists, and verifies all 30 displayed lower bounds.

Equations (4) follow. Convexity proves F(g)<=−1/3, strictly in the
interior depth range. If g=1/3 and k>0 its endpoint comparison is
already strict. Equation (2) and R>2 complete the theorem.

The scalar proof does not shorten a physical star, introduce a
concurrence or set any side mean. Its literal B2 caller must establish
the full force/moment formula and the condition b>=t beforehand.
