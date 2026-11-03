# A folded-angle chord on each original frame interval

This is a complete necessary inequality for the same original physical
frame. It is useful for computer-assisted discovery before selecting a
tilt sign. It does not prove an angle bound or close a mask.

Let alpha=cos(theta)>0 and beta=sin(theta), with |theta|<=pi/4 and
|tan(theta)|<=T. Then

\[
 1-\alpha=\frac{\beta^2}{1+\alpha}
 =|\tan\theta|\frac{\alpha}{1+\alpha}|\beta|
 \le\frac T2|\beta|.
\]

The last inequality uses alpha<=1, hence alpha/(1+alpha)<=1/2. Thus

\[
 \boxed{\alpha+\frac T2|\beta|\ge1.}
\]

The already used global bound alpha+(5/12)|beta|>=1 follows because
tan(|theta|/2)<=sqrt(2)-1<5/12; the exact comparison is
(17/12)^2-2=1/144>0. Both bounds hold for the same original frame, so
their stronger combination is

\[
 \alpha+\min\{5/12,T/2\}|\beta|\ge1.
\]

For a recorded rational interval [l,u] for the original signed tangent,
take T=max(|l|,|u|). The same bound remains valid when the interval
crosses zero. In particular the inherited |tan(theta_A)|,|tan(theta_B)|
<7/40 permits the coefficient 7/80 for A and B, even before choosing
their physical tilt signs.

The private version-9 research producer and exact replayer reconstruct
this rational coefficient from the same effective original interval.
Earlier version-8 leaves keep their unchanged reconstruction. The chord
retains all physical frames and changes only a necessary relaxation.
