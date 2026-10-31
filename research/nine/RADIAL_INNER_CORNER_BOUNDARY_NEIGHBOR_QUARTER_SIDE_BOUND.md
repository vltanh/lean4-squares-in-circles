# A radial inner-corner boundary neighbor has less than a quarter of transverse side displacement

Date: October 28, 2026 UTC. Author: root continuation.

**Status: complete proposed force-free hand theorem, submitted for full independent review.** The statement is uniform in radius and uses no force equation, normal selection, circle coefficient or graph degree. Its three parameter intervals are continuous inequalities, not sampled orientations.

## 1. Complete physical statement

Work about the fixed origin in an orthonormal frame. Let

    d>11/12, R^2=(d+1)^2+1/4, M=(1/2,d),
    f=(gamma,eta), g=(eta,-gamma),
    gamma,eta>=0, gamma^2+eta^2=1.

Suppose an actual contained unit square W physically touches the circle of radius R and has its unchanged shape

    W=M+[-beta,1-beta]f+[0,1]g,
    0<=beta<=1.                                      (1)

Thus M lies on the actual g-minimum side of W; beta is its actual location on that side, including either side endpoint. No stress or positive circle weight at any particular corner is assumed.

**Theorem.** Every such actual W satisfies

    beta*gamma<1/4.                                  (2)

If 0<gamma,eta<1 and beta>0, W has exactly one physical circle corner, namely M+(1-beta)f+g, and its exact circle equation is given in (6) below. The theorem has no upper-radius restriction. Every R>=2 satisfies its d threshold.

The point M is the right inner vertex of a radial S square [−1/2,1/2]x[d,d+1], when such a square is present. That other square and any disjointness relation are unnecessary to the theorem itself.

## 2. All weak frame and side endpoints

If beta=0 or gamma=0, (2) is immediate. These endpoints are retained without claiming a unique physical W corner there.

If eta=0, then gamma=1 and W is the rectangle

    [1/2-beta,3/2-beta] x [d-1,d].

Every point has absolute first coordinate at most 3/2 and absolute second coordinate at most d, because d>1/2. Hence every point has squared norm at most d^2+9/4, strictly below R^2 by reserve 2d-1>0. Such a W cannot be a physical boundary unit.

It remains to take 0<gamma,eta<1 and beta>0. Put tau=1-beta, so 0<=tau<1. The possible endpoint beta=1, or tau=0, remains in this entire argument.

## 3. The complete physical W mask is forced

The own center coordinates of W are

    c_W.f=d*eta-(1-gamma)/2+tau,
    c_W.g=(1+eta)/2-d*gamma.                          (3)

The first is strictly positive: eta>1-gamma on the open quarter circle and d>1/2.

Suppose the second were nonpositive. Since the first is positive, the actual top corner Z_top=M+tau*f would be a physical farthest corner, including the zero second-coordinate tie. Its exact circle deficit is

    R^2-|Z_top|^2
      =2d+1-tau*(gamma+2d*eta)-tau^2
      >2d*(1-eta)-gamma.                             (4)

The strict comparison uses tau<1 and the strict decrease of the displayed expression in tau. The assumed nonpositive second coordinate gives 2d*gamma>=1+eta, so

    2d*(1-eta)>=(1+eta)*(1-eta)/gamma=gamma.

Thus (4) is strictly positive. A physical farthest corner of a contained boundary square must have norm R, a contradiction.

Both own center coordinates are therefore strictly positive. W has exactly one physical circle corner

    Z_W=M+tau*f+g.

Expanding its unchanged circle equation gives

    2d*(1+gamma-tau*eta)=tau^2+tau*gamma+eta,           (5)

or

    d=F(gamma,tau)
      =(tau^2+tau*gamma+eta)/
           [2*(1+gamma-tau*eta)],
    eta=sqrt(1-gamma^2).                             (6)

The denominator is strictly positive on the whole domain. This physical mask was derived before choosing a circle-corner equality. No initial one-corner or positive-weight pattern was imposed.

## 4. Three exact monotonicities

For 0<gamma<1 and 0<=tau<=1, the function F increases strictly with tau. After discarding positive denominator factors, its derivative numerator is

    (2tau+gamma)*(1+gamma-tau*eta)
       +eta*(tau^2+tau*gamma+eta)>0.                  (7)

It decreases strictly with gamma along eta=sqrt(1-gamma^2). Multiplying the corresponding derivative numerator by eta gives exactly

    tau*(1-tau)*eta-(1+tau^2)-(1+tau^3)*gamma<0.      (8)

Indeed the first term is at most 1/4 and the middle subtraction is at least one. The denominator remains positive.

Finally, treating eta as an independent comparison parameter at fixed gamma,tau, F increases with eta wherever its denominator is positive: the derivative numerator is

    1+gamma-tau*eta+tau*(tau^2+tau*gamma+eta)>0.

This last comparison is only an algebraic upper bound. It does not replace an actual W orientation.

## 5. The whole alleged beta*gamma>=1/4 domain

Suppose beta*gamma>=1/4. Then

    gamma>=1/4,
    tau<=1-1/(4gamma),
    tau<=3/4.                                       (9)

The following three closed gamma intervals exhaust (9).

For 1/4<=gamma<=1/2, (9) gives tau<=1/2. By (7),(8), followed by the harmless algebraic increase eta<1,

    d<=F(1/4,1/2)
       <[(1/2)^2+(1/2)(1/4)+1]/
          [2*(1+1/4-1/2)]
        =11/12.                                     (10)

For 1/2<=gamma<=2/3, (9) gives tau<=5/8. At gamma=1/2, eta=sqrt(3)/2<7/8. Hence

    d<=F(1/2,5/8)
       <[(5/8)^2+(5/8)(1/2)+7/8]/
          [2*(1+1/2-(5/8)(7/8))]
        =101/122<11/12.                             (11)

The last rational reserve is 65/732.

For 2/3<=gamma<1, use tau<=3/4 and sqrt(5)/3<3/4 at gamma=2/3. This gives

    d<=F(2/3,3/4)
       <[(3/4)^2+(3/4)(2/3)+3/4]/
          [2*(1+2/3-(3/4)(3/4))]
        =87/106<11/12.                              (12)

The last reserve is 61/636; the squared radical reserve for sqrt(5)/3<3/4 is 1/144.

All three possibilities contradict d>11/12. This proves (2). The beta=1 endpoint is also impossible: (6) at tau=0 would give d=eta/[2(1+gamma)]<1/2.

## 6. Radius and original-data scope

At R>=2 one has d>=sqrt(15)/2-1>11/12; the exact squared comparison is

    15/4-(23/12)^2=11/144>0.

Thus the theorem applies at every radius R>=2 and is not restricted to the nine-square upper window. No individual circle coefficient, force magnitude, neighbor degree, support owner outside (1), or original shared mean was used. The entire closed side-parameter interval and both aligned orientation endpoints have been addressed.

A caller must still derive the actual chart (1), its actual M and the physical boundary status of W. Naming an arbitrary neighbor of a radial square is insufficient. The conclusion is a uniform geometric restriction, not a whole graph/load exclusion.

The proof is self-contained. No sampled pose, optimization, finite angle mesh, new computational exclusion certificate, changed normal or mean, deleted force, Lean compilation, CI, workflow or merge was used.
