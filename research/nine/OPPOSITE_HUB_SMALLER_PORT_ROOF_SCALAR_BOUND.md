# A uniform scalar bound for the smaller port below an exterior roof

Date: October 28, 2026 UTC. Scalar proof author: root, with the fixed-sum boundary reduction supplied by cycles.

**Status: complete proposed continuous hand inequality, submitted for separate independent review.** This is an algebraic lemma. A physical caller must establish its actual coordinates and perform its own occupied routing. It gives no original graph/load checkbox by itself.

## 1. Entire domain and strict conclusion

Put

    sigma=1/sqrt(2), r=5/4.

Let X,h,phi be real numbers satisfying

    0<=X<=sigma, h>=1/2, 0<=phi<=pi/4.

Define

    S=(X+h)/sqrt(2),
    v=sqrt(r^2-S^2),

and assume the square root is real and

    v>=h.

Write c=cos(phi), s=sin(phi), and assume

    K=v*c-S*s>=0.

Then

    F=(1+X*c+h*s)^2+(v*c-S*s)^2<4.                  (1)

All weak endpoints above are included. No geometric, force, support-owner, radius-window or numerical premise is hidden in this scalar statement.

## 2. A fixed-sum reduction to two full boundary intervals

Fix t=X+h, and therefore fix S,v,K. Increasing X while decreasing h by the same amount preserves v>=h and increases

    N=X*c+h*s

weakly, because c>=s. Also N>=0, so F=(1+N)^2+K^2 increases weakly.

Continue until X=sigma or h=1/2. The entire path remains in the stated domain. Consequently it suffices to prove (1) on the two boundaries

    h=1/2, 0<=X<=sigma;
    X=sigma, 1/2<=h, v>=h, K>=0.                   (2)

There is no selection of a physical square in this reduction; it is a monotonicity statement on the complete scalar domain.

## 3. The boundary h=1/2 increases with X

On this boundary S=sigma*(X+1/2). Differentiating gives

    S_X=sigma, v_X=-sigma*S/v.

Here v>0 because v>=h=1/2. Put

    H=(r^2-2S^2)/v=v-S^2/v<=v.

Direct expansion gives

    F_X/2
      =c+(X/2-1/4)c^2+(1/2-sigma*H)c*s
          +sigma*S*s^2
      >=c*[1+(X/2-1/4)c+(1/2-sigma*v)s].           (3)

Use X>=0, c<=1, s<=sigma<3/4 and v<=r=5/4. The bracket in (3) is at least

    1-1/4-(7/16)*(3/4)=27/64>0.

Thus F increases strictly with X on this whole boundary. It remains to bound the corner X=sigma,h=1/2.

At that corner put S0=(1+sigma)/2 and v0=sqrt(r^2-S0^2). The identities are

    S0^2=3/8+sigma/2,
    v0^2=19/16-sigma/2.

In particular S0>17/20, v0>9/10 and sigma>7/10. Set

    C0=sigma/2-v0*S0<0,
    L=3/2-2*sigma*v0*S0<43/100.

Indeed 2*sigma*v0*S0>1071/1000, so L<429/1000<43/100.

Expand F using c^2=1-s^2. Since c>=sigma and C0<0, replace 2*C0*c*s by the larger 2*C0*sigma*s. Since c<=1-s^2/2, replace 2*sigma*c by the larger 2*sigma-sigma*s^2. The result is

    F<=43/16+(3/2)*sigma+L*s-(17/16)*s^2.

As sigma<17/24, completing the square gives the uniform strict bound

    F<15/4+(4/17)*(43/100)^2
      =40306/10625<4.                              (4)

The last strict reserve is 2194/10625. This proves the whole first boundary in (2), for every allowed phi.

## 4. Complete parameter interval on X=sigma

Now fix X=sigma. Then

    S=1/2+sigma*h, v=sqrt(r^2-S^2).

The condition v>=h is exactly

    1/2<=h<=h_*,

where h_* is the unique positive solution of

    (1/2+sigma*h_*)^2+h_*^2=r^2.

Put S_*=1/2+sigma*h_*. The following strict bounds hold:

    29/40<h_*<3/4,
    81/80<S_*<61/60.                               (5)

For h_*<3/4, at h=3/4 one has S>1 because sigma>2/3, and therefore S^2+h^2>1+9/16=r^2.

For the lower height, sigma<17/24 and exact arithmetic give

    r^2-(1/2+(17/24)*(29/40))^2-(29/40)^2
       =1771/184320>0.

The squared sum increases strictly with h, proving h_*>29/40.

Eliminating h_* gives

    3S_*^2-2S_*-17/16=0.

This polynomial is increasing for S>1/2, and its values at 81/80 and 61/60 are respectively

    -77/6400 and 1/200.

This proves the two support bounds in (5).

Throughout this full interval,

    S>=S0>17/20, 0<v<1, v>=h>=1/2.

The condition K>=0, if it truncates the interval, does so at only its upper end: K decreases strictly with h.

## 5. Two derivative identities that cover every phi

Define

    t=S/v,
    H=(r^2-2S^2)/v,
    N=sigma*c+h*s.

Direct differentiation, with S_h=sigma and v_h=-sigma*S/v, gives

    F_h/2=s*(1+sigma*c+h*s)
             -sigma*[S*cos(2phi)+c*s*H],           (6)

and

    F_hh=4s^2-1+c*s*(3t+t^3).                      (7)

For completeness,

    dH/dS=-S*(3r^2-2S^2)/v^3=-(3t+t^3),

which verifies the second identity.

The ratio t increases strictly with h. Thus for every fixed phi, F_h is convex as a function of h: its second derivative is the derivative of (7), which is nonnegative because c*s>=0 and 3t+t^3 increases. At phi=0 this is a weak convexity assertion and is sufficient.

On 0<=phi<=pi/12, F_h increases strictly with phi. The derivative of its half is

    c+sigma*(1-H)*cos(2phi)+2*(h+2*sigma*S)*c*s>0.   (8)

All factors have the required signs: c>0, cos(2phi)>0 and H<=v<1.

These identities justify a complete split at phi=pi/12, or 15 degrees.

## 6. The entire low-angle range has F decreasing with h

By (8), it is enough to show F_h<0 at phi=pi/12 throughout the full interval [1/2,h_*]. By the convexity of F_h, it is enough to check both endpoints of that interval.

Use the exact 15-degree facts

    c*s=1/4,
    s<13/50,
    s^2<27/400,
    cos(2phi)>173/200>43/50,

together with

    7/10<sigma<17/24,
    sigma>70/99.

For example s^2=(2-sqrt(3))/4 and sqrt(3)>173/100 give the displayed upper bounds. The sigma comparisons follow by squaring positive rational numbers.

At h=1/2, H>0. Indeed S0<7/8 gives S0^2<r^2/2. Discarding the negative last term in (6) and using S0>17/20 gives

    F_h/2
      <13/50+17/96+(1/2)*(27/400)
            -(7/10)*(17/20)*(43/50)
       =-613/15000<0.                              (9)

At h=h_*, one has v=h_*, so H=(h_*^2-S_*^2)/h_*<0. By (5),

    -H<(2*(61/60)^2-25/16)/(29/40).

Substitute this and the same rational comparisons into (6):

    F_h/2
      <13/50+17/96+(3/4)*(27/400)
         +(17/96)*(2*(61/60)^2-25/16)/(29/40)
         -(70/99)*(81/80)*(173/200)
       =-114011/13780800<0.                        (10)

Both endpoint bounds are strict. Convexity of F_h and (8) therefore prove

    F_h<0 throughout 1/2<=h<=h_*,
    for every 0<=phi<=pi/12.

Consequently F is at most its h=1/2 value, already strictly below four by (4). This also covers any shorter interval imposed by K>=0.

## 7. The entire high-angle range has F convex in h

For pi/12<=phi<=pi/4, one has

    s>1/4, c*s>=1/4.

Also t=S/v>17/20, so

    3t+t^3>25313/8000>3.

Equation (7) therefore gives

    F_hh>-3/4+(1/4)*3=0.                            (11)

Thus F is strictly convex in h on the whole interval. On the allowed subinterval K>=0, its maximum is at an endpoint. The lower endpoint h=1/2 is covered by (4). The upper endpoint is either h=h_* or a point at which K=0. We check both, retaining equality K=0.

## 8. Every possible K=0 endpoint has N<1

For X=sigma and K=0, the actual c,s are S/r,v/r. Thus

    N=beta(h):=(sigma*S+h*v)/r.

This beta increases strictly with h on [1/2,h_*]. Its numerator has derivative

    1/2+v-sigma*h*S/v
      >=1/2+v-sigma*S>0,

because v>=h>=1/2, S<61/60 and sigma<3/4 imply the last expression is greater than 19/80.

At h=h_*, v=h_* and

    (3/2)h_*^2+sigma*h_*=21/16.

Consequently

    r*beta(h_*)
      =sigma/2+h_*/2+h_*^2
      =7/8+sigma/2+(1/2-2*sigma/3)*h_*.

The coefficient 1/2-2*sigma/3 is positive. Using h_*<3/4 gives

    r*beta(h_*)<7/8+sigma/2+3/8-sigma/2
                 =5/4=r.

Therefore beta(h)<1 on the entire interval. At every possible K=0 upper endpoint,

    F=(1+N)^2<4.                                   (12)

## 9. The endpoint h=h_* also satisfies the strict bound

At h=h_* keep phi variable with K>=0. Since v=h_*,

    N=sigma*c+h_*s,
    K=h_*c-S_*s.

Their phi derivatives satisfy

    N_phi=h_*c-sigma*s>=K,
    -K_phi=h_*s+S_*c<=sqrt(h_*^2+S_*^2)=r.

Also N+1>=3/2>r, because c>=sigma and sigma^2=1/2. Hence while K>=0,

    F_phi/2=(N+1)N_phi+K*K_phi
              >=K*(N+1-r)>=0.

The admissible phi interval ends at K=0, since h_*<S_* makes arctan(h_*/S_*)<pi/4. Its endpoint value is strictly below four by (12). Monotonicity therefore bounds every earlier phi by that same strict value.

This completes the h=h_* endpoint in Section 7. Together with Sections 6 through 8, it proves the entire second boundary in (2), and the fixed-sum argument proves (1) on the whole original domain.

## 10. Intended physical use and exact limits

For an opposite-hub-vertex boundary-path chart, a caller may have actual ports (-X,h),(Y,h), X+Y=sqrt(2), and may select the smaller positive X<=sigma. If its actual roof geometry supplies h>=1/2, S=(X+h)/sqrt(2), v>=h and K>=0, then (1) bounds the two specified own-coordinate expressions strictly below radius squared four.

This source supplies only the printed scalar implication. The caller must still prove that these quantities describe the relevant actual normal support, that a circle corner must lie beyond the comparison point, and that the full occupied pocket routing retains every extra. Neither an auxiliary point nor this inequality alone supplies a capacity claim.

The proof uses continuous monotonicity, convexity, exact derivatives and rational bounds over the entire stated domain. The displayed fractions check algebraic transcriptions only. No numerical optimization, pose sample, angle mesh, Lean compilation, CI, workflow or ledger change is used.
