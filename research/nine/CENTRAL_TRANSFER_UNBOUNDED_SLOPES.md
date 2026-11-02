# The central transfer holds for all real slopes

The central theorem of `CENTRAL_LINEAR_TRANSFER_HAND_TABLE.md` extends
from the displayed slope box to every pair of real slopes. No new
finite table is required. This extension removes a slope restriction;
it does not itself close a new mask.

Let L,U,R be the same original physical squares in the centered
Q-disk, Q=1105/256. Suppose U has whole floor at least 1/10 and the
genuine directed central separators are

    m_L=(-1,z_L), m_R=(1,z_R),  z_L,z_R in R.

Set p=(z_L)_++(z_R)_+, n=(-z_L)_++(-z_R)_+, and S=p-n. Then

    H_U(m_L)+H_U(m_R)+S y_U
        >= 1+(29/27)p-(32/27)n.

The inequality is strict whenever (z_L,z_R) is nonzero.

## 1. Regions already proved without a slope bound

The hand arguments for S<=0, for mixed signs, and for |S|<=1 in the
existing theorem use no upper bound on either slope. Their strict
reserves therefore remain valid on their entire unbounded regions.

It remains to consider z_L,z_R>=0. Put S=z_L+z_R. If S<=4, both
slopes belong to [0,4], hence the entire pair lies in the existing
independently verified [0,6]^2 cover. Only S>=4 needs a new argument.

## 2. A uniform triangle bound when S>=2

For the triangle with vertices (0,0),(1,z_R),(0,S), let M denote
the minimum sum of its two orthogonal projection widths. The existing
edge-alignment proof gives the vertical candidate 1+S and, for either
sloping-edge parameter z>=0, the candidate

    L(S,z)=max(d+S/d, S(z+1)/d),  d=sqrt(1+z^2).

To verify this form directly, the corresponding exact candidate is

    [d^2+|zS-d^2|+S(2+z)]/(2d).

Resolving the absolute value gives the displayed maximum.

Fix S>=2 and put

    z_-=(S-sqrt(S^2-4))/2,
    z_+=(S+sqrt(S^2-4))/2.

Both are positive, z_-<=1<=z_+, z_-z_+=1, and
z_-+z_+=S. The first branch d+S/d is active outside
[z_-,z_+], since d^2-Sz=z^2-Sz+1. Its derivative is

    z(d^2-S)/d^3.

On [0,z_-], d^2<=1+z_-^2=S z_-<=S, so that branch
is nonincreasing. On [z_+,infinity), d^2>=S z_+>=S,
so it is nondecreasing.

Inside [z_-,z_+], the active branch is S(z+1)/d. Its
derivative is S(1-z)/d^3. It increases up to z=1 and
decreases thereafter, so its minimum on that interval occurs at
one of its two endpoints.

Consequently the global minimum over z>=0 is attained at a crossing.
There d^2=Sz and z+1/z=S, so

    L(S,z)^2=(d+S/d)^2
             =S(z+1/z)+2S=S^2+2S.

The vertical candidate 1+S is larger because its square exceeds
S^2+2S by one. Therefore

    M>=sqrt(S^2+2S),  S>=2.

This is a hand bound on every actual central orientation. No sampled
triangle shape, candidate frame, or limiting slope is assumed.

## 3. The entire positive tail S>=4

Put c=263/270. For S>=4,

    (S^2+2S)-(1+cS)^2
      =(3731/72900)S^2+(7/135)S-1.

This polynomial is strictly increasing for S>=0, and its value at
four is 479/18225>0. Both sides compared by squaring are positive,
so

    M>1+(263/270)S,  S>=4.

The original whole-floor bound gives

    C=H_U(m_L)+H_U(m_R)+S y_U >= M+S/10.

Since 263/270+1/10=29/27, it follows that

    C>1+(29/27)S.

In the positive quadrant n=0 and p=S, so this is exactly the
required strict central transfer. Together with Section 1 it proves
the unbounded-slope extension.

## 4. The two coefficients must not be identified

The negative coefficient 32/27 cannot simply be replaced by 29/27.
See `SYMMETRIC_CENTRAL_TRANSFER_COUNTEREXAMPLE.md` for an exact
three-square physical counterexample, even with shoulder center
heights at least 3/5. In particular M includes the term |S|h_U:
for S<0, C=M-|S|(h_U+y_U). A bound on y_U alone cannot replace
the bound on the sum h_U+y_U in that identity.
