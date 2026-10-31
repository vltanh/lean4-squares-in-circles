# A closed positive-dot domain has terminal projection strictly above one eighth

Date: October 28, 2026 UTC. Author: house continuation, with the projection strategy and large-b comparison supplied by pentagon and the initial F bound supplied by root. Cycles independently obtained the same retained-z-term reduction. The closed-endpoint statement and small-b increasing-z proof are assembled below.

**Status: complete proposed continuous scalar theorem, submitted for full separate review.** The theorem has no radius, force, degree or physical-mask premise. Its conditional high-Y physical invocation is stated explicitly at the end.

## 1. Entire closed scalar domain

Let

    a,b>=0, a^2+b^2=1,
    z>=1, r>=12/31,
    kappa=a-zb>=2/5,
    tau=(r-1+kappa)/(r+z)>=0.                      (1)

Define

    e=a^3+b-1-z*[b(1+a^2)+tau],
    f=1-a-b^3-z*ab^2.                              (2)

**Theorem.**

    G:=-e+3f>1/8.                                  (3)

The comparison endpoints b=0, z=1, kappa=2/5, tau=0 and r=12/31 are included. No upper bound on r is needed. Every denominator used below is positive.

The original application has strict positive parameters, but the larger closed domain makes all comparison endpoints explicit.

## 2. One exact reduction and the entire b interval

Since z>=1, equation (1) gives

    a-b>=a-zb>=2/5.

Squaring a>=b+2/5 yields

    0<=b<=b_*:=(sqrt(46)-2)/10<12/25<1/2.          (4)

The radical comparison uses (34/5)^2-46=6/25>0. In particular a>0.

Put

    G0=4-a^3-3a-b-3b^3,
    H=1+a^2-3ab=2-b^2-3ab.

Because b<1/2 and a<=1,

    H>2-1/4-3/2=1/4>0.                            (5)

Direct expansion of (2) gives

    G=G0+zbH+z*tau.

Define the complete baseline function

    F(b)=G0+bH
        =4-a(4+2b^2)+b-4b^3,
    a=sqrt(1-b^2).                                (6)

The full closed domain therefore satisfies

    G=F(b)+(z-1)bH+z*tau>=F(b).                   (7)

The elementary square comparison

    a<=1-b^2/2

gives the useful global lower bound

    F(b)>=P(b):=b+b^4-4b^3.                       (8)

Indeed (1-b^2/2)(4+2b^2)=4-b^4. No orientation is selected in this comparison.

The three intervals below cover the entire closed range (4).

## 3. All small b, including b=0: retain the true z*tau term

Assume 0<=b<=1/5, and put

    N=r+a-1.

From tau>=0,

    N>=zb>=b.

Moreover N+br>0. If b>0 this is immediate from N>=zb; if b=0, then a=1 and N=r>0.

For fixed a,b,r, the exact expression for G as a function of z is

    G(z)=G0+ab(a-3b)z
                  +(N+br)z/(r+z).                (9)

This follows by writing

    z*tau=z(N-zb)/(r+z)
          =(N+br)z/(r+z)-bz.

In this whole small-b range, a>3b because a^2=1-b^2>=24/25 while9b^2<=9/25. Therefore

    dG/dz=ab(a-3b)+r(N+br)/(r+z)^2>0.             (10)

This remains strictly positive at b=0. Along the interval from the comparison endpoint z=1 to the actual z, N-zb stays nonnegative, so the entire comparison remains in its stated tau domain. Hence

    G(z)>=G(1)
       =F(b)+(r+a-1-b)/(r+1).                     (11)

For fixed a,b, the quotient in (11) increases in r:

    d/dr [(r+a-1-b)/(r+1)]
          =(2+b-a)/(r+1)^2>0.

Use r>=12/31, a>=1-b^2, and, from (8),

    F(b)>=b-4b^3>=(21/25)b.

These yield the entire quadratic bound

    G>=12/43+(128/1075)b-(31/43)b^2=:Q0(b).        (12)

Q0 is concave. Its two endpoints on [0,1/5] are

    Q0(0)=12/43,
    Q0(1/5)=1473/5375.

Thus throughout this entire interval,

    G>=1473/5375>1/8,

with exact strict reserve6409/43000. The b=0, z=1 and tau=0 comparison conventions create no omitted endpoint.

## 4. The complete middle interval

Assume1/5<=b<=2/5. The polynomial from (8) satisfies

    P''(b)=12b(b-2)<0.

Its minimum on this entire closed interval is therefore at an endpoint. Both endpoint values are exactly

    P(1/5)=P(2/5)=106/625.

By (7)--(8),

    G>=106/625>1/8,

with strict reserve223/5000. This comparison does not need strict z>1 or strict tau>0.

## 5. The complete final interval up to the exact physical bound

Assume2/5<=b<=b_*. Since b_*<12/25,

    a^2=1-b^2>1-(12/25)^2>(7/8)^2,

where the last squared reserve is159/40000. Differentiate (6) with a=sqrt(1-b^2). Exact cancellation gives

    F'(b)=6b^3/a+1-12b^2.

On this entire interval,

    F'(b)
       <6*(12/25)^3/(7/8)+1-12*(2/5)^2
        =-17681/109375<0.                         (13)

Thus F(b)>=F(b_*). At that endpoint,

    b_*=(sqrt(46)-2)/10,
    a_*=(sqrt(46)+2)/10,

and direct exact expansion gives

    F(b_*)=(538-77sqrt(46))/125.                  (14)

It is strictly greater than1/8. Indeed this is equivalent to

    sqrt(46)<4179/616,

whose exact positive squared reserve is

    (4179/616)^2-46=185/7744>0.                    (15)

All compared sides are positive. Combining (7),(13)--(15) proves G>1/8 on the entire last interval, including b=b_*.

Sections3--5 cover every b in(4), so the full closed-domain theorem(3) follows.

## 6. Literal high-Y terminal-port use

Use the unchanged unique-V V-owned positive-dot chart of the complete entry pinned below. In its actual V-top frame,

    V=[-Y,1-Y] x [X-1,X],
    S=(-A,B),
    e=A-Y, f=B-X+2.

The original full U3 and unique-V torque give exactly

    a,b>0, a^2+b^2=1,
    z=L/K>0,
    kappa=a-zb,
    r=Y/X,
    tau=(r-1+kappa)/(r+z)>0,

and the actual e,f formulas (2). No original application is moved.

If a complete separate minus-entry argument supplies

    z>=1, kappa>=2/5, Y>=3/4,

then the radius upper bound and actual circle equation imply

    X^2<=1105/256-9/16=(31/16)^2,
    r=Y/X>=12/31.

Every premise in (1) is therefore literal, and the entire actual terminal projection satisfies

    -e+3f>1/8.

This invocation has no Y<1 condition. It covers the higher-Y portion of the actual unique-minus feature whenever those exact entry bounds have been separately proved. Strict versions of those bounds fit the closed theorem automatically.

The present theorem does not itself prove the original minus mask's z or kappa bounds. It also supplies no actual V open-arc membership, terminal-angle comparison, occupied cap, angular route or completion allocation. Those remain their exact geometric caller obligations.

| Complete physical source | SHA-256 | Exact use |
| --- | --- | --- |
| TERMINAL_HUB_AXIS_TIP_OWNED_POSITIVE_DOT_FULL_MASK_ENTRY.md | 1e9e597ad4b13995909cdac5d204b111d20ef305768fe6d44def11264e4a4c49 | Section6 only: actual unique-V point/side/force identities; the self-contained scalar theorem does not depend on this source |

## 7. Verification and accounting boundary

The exact reduction (9), derivative (13), endpoint radical expression (14), both polynomial endpoint values and all printed rational reserves were independently expanded or recomputed with rational arithmetic. The proof itself is the displayed full-interval monotonicity and concavity argument. No sampled angle, physical pose, numerical minimizer or computational geometric certificate is an input.

The stronger closed scalar statement includes every comparison endpoint and is wider than the current physical caller. All original means, normal choices, positive forces, circle masks, zero individual coefficients, true degrees and physical units remain. No original fine/coarse flag, Lean compilation, CI, workflow, shared ledger or remote state was changed.

