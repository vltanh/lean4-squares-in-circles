# A uniform coupled-return inequality at a near-origin third support

Date: October 28, 2026 UTC. Author: root continuation.

**Status: complete proposed scalar theorem and conditional physical
corollary, submitted for independent full review.** All inequalities
below hold over the entire displayed continuous domain. The theorem
does not assert that an arbitrary original contact family has that
domain. Its lower-house caller needs a separate complete physical join,
including the branch t>a. No original checkbox is changed here.

## 1. Exact closed-domain theorem

Put

    A=59/60, Y=31/120, T=61/60, k=4/15,
    Q=1105/256.

Let real parameters satisfy

    A<=a<=T, 0<=y<=Y, 0<=q<=k, 0<t<=a.

Define

    s=1-t*q, l=sqrt(t^2+s^2), u=t/l, v=s/l.

Assume the following necessary transverse reach inequality:

    u + 1/(2*sqrt(1+q^2))
        + (y-(a-t)*q)/(1+q^2) >= 1.                (R)

Then

    (a+u)^2+(s-y+v)^2 > Q.                         (1)

The domain includes every displayed interval endpoint, including q=0,
y=0 and t=a. No sign assumption on y-(a-t)q is needed for this scalar
statement. The conclusion is strict throughout the whole domain.

## 2. A monotone two-variable lower bound

For 0<=t<=T and S<=s<=1, where

    S=1-k*T=164/225,

write

    F(t,s)=(A+t/sqrt(t^2+s^2))^2
             +(s-Y+s/sqrt(t^2+s^2))^2.

Both s-Y and the full second parenthesis are positive. Since a>=A
and y<=Y, the left side of (1) is at least F(t,1-t*q). We now prove
that F is strictly increasing in its second argument over this whole
rectangle.

With l=sqrt(t^2+s^2), u=t/l and v=s/l, differentiation gives

    (1/2)*dF/ds
      =s-Y+v + [t^2*(s-Y)-A*t*s]/l^3.

Here v>1/2, because

    3*S^2-T^2=151261/270000>0.

Also t*s/l^3<=1/(2s), by 2ts<=l^2 and l>=s. Consequently

    (1/2)*dF/ds
      >s-Y+1/2-A/(2s)
      >=S-Y+1/2-A/(2S)
      =87383/295200>0.                              (2)

This proves the needed monotonicity with a strict uniform reserve.
It does not assume that the larger relaxed domain is physically
realizable.

## 3. The entire interval 3/8<=t<=T

Since q<=k, s>=1-kt. By (2) it suffices to bound

    G(t)=F(t,1-kt), 3/8<=t<=T.

For this section put s=1-kt, l=sqrt(t^2+s^2),

    N=A*s-t*(s-Y), B=t-k*s.

The exact derivatives are

    G'(t)/2=N/l^3-k*(s-Y+s/l),
    G''(t)/2=k^2+[-(A*k+1-Y)+3kt]/l^3
                         -3*N*B/l^5.               (3)

Throughout the entire interval, B>=27/200>0. Also

    N=s*(A-t)+t*Y>=-1/30+(3/8)*Y=61/960>0.

The squared length l^2 is increasing there and its endpoint value
is T^2+S^2. The following exact bounds hold:

    (13/10)^2-(T^2+S^2)=101339/810000>0,
    A*k+1-Y-3kT=343/1800.

Dropping the negative last term in (3), and keeping all denominator
signs, therefore gives

    G''(t)/2
      < k^2-(343/1800)/(13/10)^3
      =-7723/494325<0.                              (4)

Thus G is strictly concave. Its minimum on this closed interval is
at an endpoint, so it is enough to check the two exact endpoints.

At t=3/8, s=9/10 and l=39/40, hence u=5/13,v=12/13. Directly,

    G(3/8)=808649/187200,
    G(3/8)-Q=2471/748800>0.                         (5)

At t=T, use L=251/200. The exact reserve

    L^2-(T^2+S^2)=32837/3240000>0

gives u>T/L=610/753 and v>S/L=1312/2259. Both squared
quantities are positive, so

    G(T) > (A+610/753)^2+(S-Y+1312/2259)^2,
    [(A+610/753)^2+(S-Y+1312/2259)^2]-Q
         =4323176011/816492960000>0.                (6)

Equations (4)--(6) prove (1) on all 3/8<=t<=T, even without using
the reach assumption (R).

## 4. Reach controls the whole remaining small-t domain

Now suppose 0<t<=3/8. First,

    l^2=(1+q^2)*(t-q/(1+q^2))^2+1/(1+q^2)
          >=225/241.

Therefore u<=sqrt(241/225)*t<(25/24)*t; the final squared reserve
is 67/4800>0. On the other hand (R), y<=Y, t<A and q<=k give

    u>=1-1/(2sqrt(1+q^2))
             -(y-(a-t)q)/(1+q^2)
      >=29/120+(225/241)*(A-t)*q.                  (7)

Every term in this bound has the displayed sign: y>=0, A-t>0 and
q>=0. In particular t>t0:=29/125. Combining (7) with the strict
upper bound for u yields

    tq <= [t/(A-t)]*(241/225)*[(25/24)t-29/120]
        <= (241/365)*[(25/24)t-29/120]
        =K*(t-t0),                                 (8)

where

    K=1205/1752, C=1+K*t0=50789/43800.

The second inequality uses the increasing ratio t/(A-t) and its
endpoint value (3/8)/(A-3/8)=45/73. Its other factor is positive
because t>t0. Thus s>=C-Kt. By (2), it remains to bound

    H(t)=F(t,C-Kt), t0<=t<=3/8.                    (9)

For completeness we prove H strictly decreasing on this entire
interval, rather than infer that from its endpoint values.

Put s=C-Kt, l=sqrt(t^2+s^2),

    N=A*s-t*(s-Y).

The exact derivative is

    H'(t)/2=C*N/l^3-K*(s-Y+s/l).                   (10)

Here N>0, and N is strictly decreasing: its negative derivative
has the uniform lower bound

    A*K+C-Y-2K*(3/8)=279019/262800>0.

To make (10) negative, it suffices to show

    K*(s-Y)*l^3+K*s*l^2-C*N>0.

Since l>=s and s-Y>0, its left side is at least

    K*[(s-Y)*s^3+s*t^2+s^3]-C*N.                  (11)

The following simple rational bounds hold on the two entire listed
intervals. The N bounds use its proved monotonicity.

| Interval for t | Lower bound for s | Lower bound for t | Upper bound for N |
| --- | --- | --- | --- |
| [29/125,3/10] | 19/20 | 23/100 | 13/16 |
| [3/10,3/8] | 9/10 | 3/10 | 73/100 |

For both intervals K>11/16 and C<29/25. Substitution of the first
row into (11) gives the exact lower bound

    (11/16)*[(19/20-Y)*(19/20)^3
               +(19/20)*(23/100)^2+(19/20)^3]
       -(29/25)*(13/16)
          =6850199/76800000>0.

The second row similarly gives

    (11/16)*[(9/10-Y)*(9/10)^3
               +(9/10)*(3/10)^2+(9/10)^3]
       -(29/25)*(73/100)
          =20269/640000>0.

Every substitution is in a nonnegative factor or the explicitly
negative product -C*N. For direct endpoint verification,

    K-11/16=1/3504,
    29/25-C=19/43800,
    s(3/10)-19/20=283/87600,
    13/16-N(t0)=37/30000,
    73/100-N(3/10)=5917/5256000.

Also

    s(3/8)=315937/350400
       =9/10+577/350400>9/10.

Thus (10) is strictly negative on the whole interval in (9).
Using the already proved strict s-monotonicity and (5),

    H(t)>=H(3/8)>F(3/8,9/10)>Q.

Together with Section 3 this proves (1) over the complete original
closed parameter domain, including t=a and every permitted endpoint.

## 5. Conditional physical use and exact boundary of this result

The inequality can be applied whenever an original physical argument
supplies the following actual data, without moving the circle origin:

* A unit has its two real return points at (-a,y+h) and
  P_D=(-a,y+h-1), with h=tq and the parameters of Section 1.
* The external D has inward minimum-support normal n_D=(-u,-v)
  at P_D. For any actual unit at a minimum support, P_D+n_D belongs
  to that unit: at a vertex the normal's two inward orthonormal
  coefficients lie in [0,1], and at a side the unchanged mean plus
  the inward unit axis is on the opposite side. This includes
  original side endpoints and free vertex normals.
* The upper return T has actual inward normal
  m=(-1,q)/sqrt(1+q^2), actual side tangent
  j=(-q,-1)/sqrt(1+q^2), and its unchanged contact on the unit side.
  Write T=P_T+[0,1]m+[-tau,1-tau]j. Suppose the actual physical
  side/circle geometry has proved
  tau>=1/2-(y-(a-t)q)/sqrt(1+q^2).
* The real TD contact gives u+(1-tau)/sqrt(1+q^2)>=1.

The last two facts imply (R). The actual contained point P_D+n_D
has squared norm exactly the left side of (1), so D cannot lie in
any disk with R^2<=Q. This is a whole-support contradiction, using
no equilibrium at D, no assumed D ownership and no fixed TD mean.

The geometric upper-side premise, parameter bounds and t<=a must
all be proved in each original caller. The lower-house port-order
source and the pending side/radius join are separate obligations;
the scalar proof above does not assume they have already closed.
In particular no t>a domain, B-owned root interface, physical mask
or completion square is discarded by invoking this result.

All printed reserves are exact rational algebra. Their arithmetic
was recomputed to check transcription; the displayed continuous
proof, rather than that execution, supplies the inequality. There
is no numerical pose search, angle mesh, Lean compilation, CI or
computational exclusion certificate, and no original gate credit.
