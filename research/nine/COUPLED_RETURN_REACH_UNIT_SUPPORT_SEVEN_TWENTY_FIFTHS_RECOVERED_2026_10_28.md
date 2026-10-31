# Coupled return reach with unit support and a seven-twenty-fifths port

Date: October 28, 2026 UTC. Author: pentagon continuation.

**Status: complete proposed scalar theorem and conditional physical
corollary, reconstructed as new bytes for fresh independent review.**
This is a mathematical reconstruction of the lost
COUPLED_RETURN_REACH_UNIT_SUPPORT_SEVEN_TWENTY_FIFTHS_EXCLUSION.md
(old SHA-256
8d3617f955218373a05ef6184c862aca4b7f944562d90b127d78c4ee5471a97a).
It is not an exact-byte recovery. No previous review is asserted to
apply to these bytes.

Every estimate below covers its whole displayed continuous domain.
The scalar theorem is self-contained. Its physical corollary is
conditional on actual original geometry supplying all the stated
premises. No original family or checkbox is closed by this source
alone.

## 1. Exact closed-domain statement

Put

    T=61/60, Y=7/25, k=11/60, Q=1105/256.

Suppose real parameters satisfy

    1<=a<=T, 0<=y<=Y, 0<=q<=k, 0<t<=a.

Define

    s=1-t*q, l=sqrt(t^2+s^2), u=t/l, v=s/l.

Assume the necessary transverse reach inequality

    u + 1/(2*sqrt(1+q^2))
      + (y-(a-t)*q)/(1+q^2) >= 1.                  (R)

Then

    (a+u)^2+(s-y+v)^2 > Q.                         (1)

The conclusion is strict even at every permitted interval endpoint,
including a=1, y=0, q=0 and t=a. There is no scalar hypothesis that
y-(a-t)q be positive.

## 2. Monotonicity in the second coordinate

On the whole rectangle

    0<=t<=T, S<=s<=1, S=1-k*T=2929/3600,

write

    F(t,s)=(1+t/sqrt(t^2+s^2))^2
             +(s-Y+s/sqrt(t^2+s^2))^2.

Here s-Y>0. Since a>=1 and y<=Y, both squared quantities being
compared are positive, and the left side of (1) is at least
F(t,1-t*q).

With l=sqrt(t^2+s^2), differentiation gives

    F_s/2=s-Y+s/l + [t^2*(s-Y)-t*s]/l^3.            (2)

The exact inequality

    3*S^2-T^2=4113841/4320000>0

implies s/l>1/2. Also

    t*s/l^3 <= 1/(2s),

because 2ts<=l^2 and l>=s. As s-Y>0, (2) yields

    F_s/2 > s-Y+1/2-1/(2s)
          >= S-Y+1/2-1/(2S)
           =4418809/10544400>0.                    (3)

Thus F is strictly increasing in s throughout the entire rectangle.

## 3. The whole interval 5/16<=t<=T

Set b=5/16. Since q<=k, (3) reduces this interval to

    G(t)=F(t,1-kt), b<=t<=T.

In this section put

    s=1-kt, l=sqrt(t^2+s^2),
    N=s-t*(s-Y), B=t-k*s.

Direct differentiation gives

    G'/2=N/l^3-k*(s-Y+s/l),
    G''/2=k^2-[(k+1-Y)-3kt]/l^3-3*N*B/l^5.         (4)

For example, along this line (t/l)'=s/l^3 and (s/l)'=-t/l^3;
these identities give both formulas without an unstated parameter
dependence.

Over the entire interval,

    B>=B(b)=1609/11520>0.

Also s*(1-t)>=-1/60: for t<=1 this is nonnegative, while for
1<=t<=T it is at least 1-t>=-1/60 because s<=1. Hence

    N=s*(1-t)+t*Y >= -1/60+b*Y=17/240>0.            (5)

The derivative of l^2 is 2B, so l^2 is increasing. Its largest
value is T^2+S^2, and

    (4/3)^2-(T^2+S^2)=1065359/12960000>0.
    k+1-Y-3kT=413/1200.

Dropping the strictly negative last term in (4), with all
denominators positive, gives

    G''/2 < k^2-(413/1200)/(4/3)^3
           =-25709/230400<0.                      (6)

Thus G is strictly concave, and its minimum on this closed interval
is at an endpoint.

At t=b the actual s is s_b=181/192. The upper length L_b=199/200
satisfies

    L_b^2-b^2-s_b^2=84551/23040000>0.

Both terms in F are positive. Consequently

    G(b) > (1+b/L_b)^2+(s_b-Y+s_b/L_b)^2,

and the exact endpoint reserve is

    (1+b/L_b)^2+(s_b-Y+s_b/L_b)^2-Q
       =301114929/101378560000>0.                  (7)

At t=T the length is strictly less than 4/3, as already proved.
Therefore

    G(T) > (1+3T/4)^2+(S-Y+3S/4)^2
          =(141/80)^2+(16471/14400)^2,

with reserve

    (141/80)^2+(16471/14400)^2-Q
        =20388241/207360000>0.                    (8)

Concavity and (7)--(8) prove (1) for every b<=t<=T.
No reach premise was needed on this interval.

## 4. The reach inequality forces a linear bound for small t

Suppose now 0<t<=b. Completing the square gives

    l^2=(1+q^2)*(t-q/(1+q^2))^2+1/(1+q^2)
         >=1/(1+k^2)=3600/3721.

As 3721=61^2, it follows that

    u<=T*t.                                      (9)

On the other hand (R), a>=1, y<=Y and t<1 imply

    u >= 1-1/(2sqrt(1+q^2))
                -y/(1+q^2)+(a-t)q/(1+q^2)
      >= 11/50+(3600/3721)*(1-t)*q.               (10)

Here 1-1/(2sqrt(1+q^2))>=1/2, and the sign
(1-t)q>=0 justifies replacing 1/(1+q^2) by its lower
bound 3600/3721. Also -y/(1+q^2)>=-Y.

Equations (9)--(10) give

    t>=t0:=66/305,   T*t0=11/50.

They further imply

    tq <= [t/(1-t)]*(3721/3600)*T*(t-t0)
        <= K*(t-t0),

where

    K=(5/11)*(3721/3600)*T=226981/475200,
    C=1+K*t0=39721/36000.                          (11)

The second step uses t/(1-t)<=b/(1-b)=5/11 and the
nonnegativity t-t0>=0. Thus

    s=1-tq >= z(t):=C-Kt.

For t0<=t<=b, one has z<=1. Also K<1/2, so

    z>=1-Kb>1-b/2=27/32>S.

It is therefore legitimate to use (3) between z and the original s.
It remains to prove

    H(t):=F(t,z(t))>Q,  t0<=t<=b.                 (12)

## 5. A uniform derivative bound on the whole small interval

For this section use

    z=C-Kt, lambda=sqrt(t^2+z^2), L=41/40.

We first bound lambda over the whole interval. Its square is a convex
quadratic, so its maximum occurs at an endpoint. At t=t0, z=1 and

    L^2-(1+t0^2)=22617/5953600>0.                  (13)

At t=b, the inequalities K>2/5 and t0<1/4 imply

    K*(b-t0)>(2/5)*(1/16)=1/40,

so z(b)<39/40. Therefore

    L^2-lambda(b)^2
      > L^2-b^2-(39/40)^2=3/1280>0.              (14)

Together (13)--(14) prove lambda<L everywhere on the closed interval.

Write

    N=z-t*(z-Y).

Since t<1 and z>Y, this N is positive. Direct differentiation, using
z+Kt=C, gives

    H'/2=C*N/lambda^3-K*(z-Y+z/lambda).            (15)

Multiplying by the positive lambda^3 and using lambda<L yields

    lambda^3*H'/2
      =C*N-K*(z-Y)*lambda^3-K*z*lambda^2
      >C*N-K*[(L+1)z-LY]*lambda^2
       =:P(t).                                   (16)

The strict inequality uses K>0 and z-Y>0. We prove P positive by
simple uniform coefficient bounds, without relying on sampled values
or unproved monotonicity.

For complete reproducibility, put

    D=(L+1)C-LY.

The cubic P=p0+p1*t+p2*t^2+p3*t^3 has exact coefficients

    p0=C^2*(1-KD),
    p1=C*(-C-K+Y)+K^2*(2DC+(L+1)C^2),
    p2=CK-K*(D*(1+K^2)+2*(L+1)C*K^2),
    p3=(L+1)K^2*(1+K^2).

Substituting the fixed rational constants in (11) gives the following
four exact positive reserves:

    p0-17/200
      =452803458218641/8957952000000000000>0,

    p1-1/10
      =872065344354797017/118244966400000000000>0,

    p2+111/100
      =132064132645570898873/17169169121280000000000>0,

    p3-1/2
      =1697700349169775598321/25181448044544000000000>0.

These are rational identities, so each sign is certified directly
by its positive integer numerator and denominator. Since
t>=t0>1/5 and t<=b=5/16, they give on the entire interval

    P(t)
       >17/200+(1/10)t-(111/100)t^2+(1/2)t^3
       >=17/200+1/50-(111/100)*(25/256)+1/250
        =77/128000>0.                             (17)

Thus (16) proves H'>0 throughout the interval.

At t=t0, z=1 and lambda<L, while both squared quantities are
positive. Hence

    H(t0) > (1+t0/L)^2+(1-Y+1/L)^2,

and direct exact arithmetic gives

    (1+t0/L)^2+(1-Y+1/L)^2-Q
       =25507473319/1000800160000>0.               (18)

Since H is increasing, (18) proves (12). Combining Sections 2--5
proves (1) on the entire stated closed parameter domain.

## 6. Conditional physical corollary

Suppose an original physical argument, without translating the circle
origin, supplies the following actual data.

* An actual unit has return points
  P_T=(-a,y+h) and P_D=(-a,y+h-1), with h=tq and all
  parameters satisfying Section 1.
* The external unit D has inward minimum-support normal
  n_D=(-u,-v) at the unchanged actual point P_D.
* The upper unit T has inward normal
  m=(-1,q)/sqrt(1+q^2) and tangent
  j=(-q,-1)/sqrt(1+q^2), with its actual contact on an owned side:
  T=P_T+[0,1]m+[-tau,1-tau]j.
  Its actual physical circle/side geometry has proved
  tau>=1/2-(y-(a-t)q)/sqrt(1+q^2).
* Its real contact with D supplies
  u+(1-tau)/sqrt(1+q^2)>=1.

The last two premises imply (R), with all inequality directions
preserved. Furthermore P_D+n_D is an actual point of D. At an
owned side it is the unchanged mean translated by the unit inward
axis onto the opposite side. At a vertex, the two coefficients of
an inward unit normal in the square's inward orthonormal axes are
nonnegative and at most one. Thus this assertion includes free
vertex normals, side endpoints and every allowed original mean.

The squared norm of this actual D point is

    |P_D+n_D|^2
      =(-a-u)^2+(y+tq-1-v)^2
      =(a+u)^2+(s-y+v)^2>Q.

It cannot belong to a disk with radius squared at most Q. This
conditional contradiction uses no equilibrium equation at D and
does not replace its true degree by two. It imposes no D ownership
or TD application-point choice.

Every premise in this physical corollary must be proved by the
original caller, including a>=1, q<=11/60, the upper-side estimate
and t<=a. The source does not address t>a, nor does it by itself
classify root contacts, physical circle masks, omitted completion
squares or an original graph family.

The proof is continuous exact scalar algebra. Rational arithmetic
was recomputed to check transcription; the written argument supplies
the proof. There was no numerical pose search, angle mesh, Lean
compilation, CI or computational exclusion certificate.

