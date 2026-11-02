# The symmetric 29/27 central transfer is false

This exact control rules out replacing both signed coefficients of
the central transfer by 29/27. It does not contradict the proved
asymmetric theorem, the full 000/01 closure, or the desired n=9 bound.

Put Q=1105/256 and t=1/sqrt(2). Use aligned unit squares

    L=(-1,3/5), R=(1,3/5),

and a unit square U with center (0,4/3) and side axes

    u=(t,t), v=(-t,t).

All three are interior-disjoint and fit in squared radius 17/4<Q.

## Physical checks

For L and R, the farthest squared corner norm is

    (3/2)^2+(11/10)^2=173/50<17/4.

The farthest corner of U is its top corner, of squared norm

    (4/3+t)^2=41/18+(4/3)sqrt(2)<17/4.

The final comparison follows from sqrt(2)<71/48; its squared
positive reserve is 433/2304. The other three U corners are
closer because its center lies on the positive vertical axis.

The pair L,R is horizontally separated, with center gap two.
For the two central pairs choose genuine directed normals

    m_L=(-1,-1), m_R=(1,-1).

Each center projection from U toward its shoulder is 26/15.
The support sum is 1+t, so these normals strictly separate:

    26/15-(1+t)=11/15-t>0,

because (11/15)^2-1/2=17/450>0. Each normal is a side axis
of U. Thus these are valid physical separating normals, not
arbitrary comparison vectors.

Both shoulders have center height 3/5. The central square has
whole floor 4/3-t>1/10.

## Violation

Here z_L=z_R=-1 and S=-2. The original central expression is

    C=H_U(m_L)+H_U(m_R)+S y_U
      =sqrt(2)-8/3.

The proposed symmetric target would be

    1+(29/27)S=-31/27.

Their difference is

    C-[1+(29/27)S]=sqrt(2)-41/27<0,

since (41/27)^2-2=223/729>0. Therefore the symmetric
inequality fails under genuine physical hypotheses.

The existing asymmetric target is 1-64/27=-37/27, which is
smaller and is not contradicted by this configuration.
