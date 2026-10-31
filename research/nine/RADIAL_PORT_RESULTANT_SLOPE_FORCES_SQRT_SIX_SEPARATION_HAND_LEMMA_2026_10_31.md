# A radial port and an opposite circle resultant have separation greater than sqrt(6)

Date: October 31, 2026 UTC.

**Status: complete hand geometric theorem.** This is independent of the original owner, contact graph, or equations at exterior neighbors. It is intended to be combined with the whole-aperture radial/unique side-channel slope theorem, but its exact hypotheses are stated independently below.

## 1. Geometric statement

Let f,w be orthonormal unit vectors, with either orientation. Suppose

    R>2,
    d=sqrt(R^2-1/4)-1>117/125,
    Q=d*f+chi*w, 0<chi<1/2,
    Z=R*(-z*f+w)/sqrt(1+z^2), z>=21/25.

Then

    |Z-Q|^2>6+29587/20437500>6.                  (1)

Thus |Z-Q|>sqrt(6). Q is allowed to be any unchanged genuine radial side-interior application with the stated positive transverse coordinate. Z is a point on the same containing circle in the direction of the stated opposite resultant. No circle coefficient or force at either point is assumed equal to another.

## 2. Exact continuous comparison

The squared distance is

    |Z-Q|^2=R^2+d^2+chi^2
                 +2*R*(d*z-chi)/sqrt(1+z^2).    (2)

At fixed d,chi, the derivative of (d*z-chi)/sqrt(1+z^2) is

    (d+chi*z)/(1+z^2)^(3/2)>0.

Consequently z>=21/25 gives

    |Z-Q|^2>=R^2+d^2+chi^2
                   +2*R*(21*d-25*chi)/sqrt(1066). (3)

The right side decreases with chi on [0,1/2]: its derivative is 2*chi-50*R/sqrt(1066)<0, since R>2 and sqrt(1066)<33. Using the unchanged chi<1/2 therefore gives the strict comparison

    |Z-Q|^2>R^2+d^2+1/4
                    +2*R*(21*d-25/2)/sqrt(1066). (4)

The coefficient 21*d-25/2 is positive already at d=117/125, where it equals 1789/250. Every term in (4) is therefore increasing in the positive comparison variables R,d. Replace them only in the scalar lower bound by 2 and 117/125. Since sqrt(1066)<327/10, proved by squaring 1066<1069.29,

    |Z-Q|^2
      >4+(117/125)^2+1/4+3578/(125*sqrt(1066))
      >4+13689/15625+1/4+7156/8175
       =6+29587/20437500.                       (5)

For a direct arithmetic check of the last positive reserve,

    6-(4+13689/15625+1/4)=54619/62500,
    7156*62500-54619*8175=739675>0.

This proves (1). All comparisons concern the same actual Q,Z; no physical point, force or circle radius has been moved to a comparison value.

## 3. A complementary unit-diagonal length bound

For any pi/4<a<pi/2 and 0<g<2/5, a vector with orthonormal coordinates

    (1+sin(a)+cos(a), g+cos(a)-sin(a))

has squared length strictly less than 6. Indeed, with s=sin(a), c=cos(a),

    (1+s+c)^2+(g+c-s)^2
       =3+2*(s+c)+g^2-2*g*(s-c)
       <3+2*sqrt(2)+4/25<6.                    (6)

The final comparison uses sqrt(2)<71/50, whose positive squared reserve is 41/2500.

Therefore a physical configuration establishing both this displacement formula and the hypotheses of Section 1 is impossible. This is one whole-domain obstruction, independent of which actual square supplies g or which orientation the orthonormal frame has.

No script-generated inequality, pose sample, numerical certificate, Lean or CI is a proof premise.
