# Four-square paired-gap corollary (hand proof)

Let Q=1105/256, r=sqrt(Q), and let h_S(e) denote the support halfwidth of an actual unit square S in direction e. For two actual squares define g_e(X,Y)=e·(c_Y-c_X)-h_X(e)-h_Y(e).

The already proved physical two-square cap theorem, with its radius-dependent argument retained, gives for any disjoint actual pair M,B and unit e, provided R<=r,

46[-e·c_M-h_M(e)]+(27/2)[-e·c_B-h_B(e)] <=211/4-(119/2)(r-R).

Indeed its scalar proof bounds the left side by R(|46e+kn|+|(27/2)e-kn|)-P_M-P_B, with k=207/16 and actual separating normal n; the bound at r is 211/4. The sum of norms is at least 119/2, yielding the stated slack.

Apply this to distinct pairs (M_L,B_L) in direction e and (M_R,B_R) in direction -e. Addition yields the **four-square paired-gap inequality**

46 g_e(M_L,M_R)+(27/2)g_e(B_L,B_R) <= 211/2-119(r-R).

Thus if g_e(M_L,M_R)>=2 and g_e(B_L,B_R)>=1, then R>=r. This is independent of any intervening chain squares and of all other five actual squares.

For an actual four-square projection chain M_1,...,M_4, let d_i>=0 be its successive projection gaps and put G=d_1+d_2+d_3+(2h_{M_2}(e)-1)+(2h_{M_3}(e)-1)>=0. Telescoping gives g_e(M_1,M_4)=2+G. Therefore **every ordered pair** C,D among the five complementary actual squares satisfies

g_e(C,D) <= beta=1-(92/27)G-(238/27)(r-R).

In particular every complementary projection interval meets a common closed interval of length beta. To see this, take L=max left endpoints; every right endpoint is >=L-beta, with the same-square extremum automatic. Also 0<beta: the center norm bound |c|<91/60 implies G<1/30, while a four-chain gives R>=2 and r<25/12, hence beta>41/270.

At R=r and with both gaps attaining 2 and 1, equality in the original cap forces the four endpoint squares to be aligned with e. Up to global rotation their centers are M_L=(-3/2,sigma_L/16), M_R=(3/2,sigma_R/16), B_L=(-1,-15sigma_L/16), B_R=(1,-15sigma_R/16), where each sigma is independently ±1. This is a conditional four-anchor classification, not an unrestricted nine-square classification.

**Status:** complete conditional hand corollary; no original fine/coarse case closes. The missing global step is to extract such paired gaps, or to rule out the complementary T-shaped alternative. No Lean, CI, scripts, or numerical certificate used.