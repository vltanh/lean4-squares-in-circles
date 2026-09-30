module
public import SquaresInCircles.Six.Stress.DiagonalFormula
public import SquaresInCircles.Six.Equality.SupportMaximizers

@[expose] public section

/-!
# Equality of the active local supports fixes every exterior center

The supporting disk point is unique. The feasible center is therefore unique
on each active vertex branch, and the axial cap leaves zero transverse slack.
The two signs below cover E/N and W/S without assuming their center coordinates.

Only exact candidate algebra and geometric support theorems are imported here.
The legacy balanced-closure adapter imports this module, not conversely.
-/

noncomputable section
namespace SquaresInCircles.Six.Equality
open Stress Normalization

lemma scalar_vertex_center {R a b x y sx sy l : ℝ} {p : Point}
    (hR : 0≤R) (hg : (x,y)≠(0,0))
    (hbox : (|a|+1/2)^2+(|b|+1/2)^2≤R^2)
    (hsx : |sx|=1) (hsy : |sy|=1) (hx : sx*x=|x|) (hy : sy*y=|y|)
    (hp : normSq p=R^2) (hl : 0≤l) (hgp : (x,y)=scale l p)
    (heq : x*a+y*b=R*Real.sqrt (x^2+y^2)-(|x|+|y|)/2) :
    (a,b)=sub p (sx/2,sy/2) := by
  let S := axisSquare (a,b)
  have hcontain : ∀ q, closedSquare S q → inDisk (0,0) R q := by
    intro q hq
    apply Six.inDisk_of_phi_le (S := S) (o := (0,0)) (R := R) _ hq
    simpa [S,phi,alpha,beta,localX,localY,axisSquare,abs_neg] using hbox
  have he : dot (x,y) S.center=vertexSupport R S (x,y) := by
    simpa [S,dot,vertexSupport,vectorLength,width,frameX,frameY,axisSquare,normSq] using heq
  have hfx : sx*frameX S (x,y)=|frameX S (x,y)| := by simpa [S,frameX,axisSquare] using hx
  have hfy : sy*frameY S (x,y)=|frameY S (x,y)| := by simpa [S,frameY,axisSquare] using hy
  have hc := center_eq_of_vertex_support hR hg hcontain hsx hsy hfx hfy he
  have hdot := radius_length_eq_dot_of_ray hl hR hp hgp
  have hpoint := disk_support_point_unique hR hg hp.le hdot.symm
  rw [← hpoint] at hc
  simpa [S,axisSquare,rotate] using hc

lemma sign_square_abs {sgn : ℝ} (h : sgn=1 ∨ sgn= -1) : sgn^2=1 ∧ |sgn|=1 := by
  rcases h with rfl | rfl <;> norm_num

lemma north_full_support {sgn : ℝ} (hs : sgn=1 ∨ sgn= -1) :
    scalarSupport Six.radius 1 (sgn*rStar)=
      Six.radius*Real.sqrt (1^2+(sgn*rStar)^2)-(|(1:ℝ)|+|sgn*rStar|)/2 := by
  have hsgn := sign_square_abs hs
  have hyabs : |sgn*rStar|=rStar := by rw [abs_mul,hsgn.2,abs_of_pos rStar_pos,one_mul]
  have hysq : (sgn*rStar)^2=rStar^2 := by rw [mul_pow,hsgn.1,one_mul]
  have h : scalarSupport Six.radius 1 (sgn*rStar)=northVertex 1 (-rStar) := by
    rcases hs with rfl | rfl
    · simpa only [one_mul,scalarSupport_neg_second] using candidate_north_exact_support
    · simpa only [neg_one_mul] using candidate_north_exact_support
  rw [h,hyabs,hysq]
  simp [northVertex]

lemma west_full_support {sgn : ℝ} (hs : sgn=1 ∨ sgn= -1) :
    scalarSupport Six.radius (1+rStar) (sgn*mStar)=
      Six.radius*Real.sqrt ((1+rStar)^2+(sgn*mStar)^2)-(|1+rStar|+|sgn*mStar|)/2 := by
  have hsgn := sign_square_abs hs
  have hyabs : |sgn*mStar|=mStar := by rw [abs_mul,hsgn.2,abs_of_pos mStar_pos,one_mul]
  have hysq : (sgn*mStar)^2=mStar^2 := by rw [mul_pow,hsgn.1,one_mul]
  have h : scalarSupport Six.radius (1+rStar) (sgn*mStar)=northVertex (1+rStar) (-mStar) := by
    rcases hs with rfl | rfl
    · simpa only [one_mul,scalarSupport_neg_second] using candidate_west_exact_support
    · simpa only [neg_one_mul] using candidate_west_exact_support
  rw [h,hyabs,hysq,abs_of_pos one_add_rStar_pos]
  simp [northVertex]

/-- E and N have the same radial coordinate and opposite transverse signs. -/
theorem north_center_unique {a b sgn : ℝ} (hs : sgn=1 ∨ sgn= -1)
    (hbox : (|a|+1/2)^2+(|b|+1/2)^2≤Six.radius^2)
    (heq : a+sgn*rStar*b=scalarSupport Six.radius 1 (sgn*rStar)) :
    a=1+Six.sStar ∧ b=sgn*Six.sStar := by
  have hsgn := sign_square_abs hs
  let p : Point := (Six.sStar+3/2,sgn*(Six.sStar+1/2))
  let l : ℝ := 1/(Six.sStar+3/2)
  have hp : normSq p=Six.radius^2 := by
    dsimp [p,normSq]
    rw [mul_pow,hsgn.1,one_mul]
    nlinarith [Six.east_radius_identity,Six.radius_sq]
  have hl : 0≤l := (div_pos (by norm_num) rStar_den_pos).le
  have hgp : ((1:ℝ),sgn*rStar)=scale l p := by
    apply Prod.ext
    · dsimp [scale,l,p]
      field_simp [ne_of_gt rStar_den_pos]
    · dsimp [scale,l,p,rStar]
      field_simp [ne_of_gt rStar_den_pos]
      ring
  have hsign : sgn*(sgn*rStar)=|sgn*rStar| := by
    rw [abs_mul,hsgn.2,abs_of_pos rStar_pos,one_mul]
    calc
      sgn*(sgn*rStar)=sgn^2*rStar := by ring
      _=rStar := by rw [hsgn.1,one_mul]
  have he : 1*a+(sgn*rStar)*b=
      Six.radius*Real.sqrt (1^2+(sgn*rStar)^2)-(|(1:ℝ)|+|sgn*rStar|)/2 := by
    simpa only [one_mul,north_full_support hs] using heq
  have hc := scalar_vertex_center Six.radius_pos.le (by norm_num : ((1:ℝ),sgn*rStar)≠(0,0))
    hbox (show |(1:ℝ)|=1 by norm_num) hsgn.2 (by norm_num : (1:ℝ)*1=|1|)
    hsign hp hl hgp he
  have hx := congrArg Prod.fst hc
  have hy := congrArg Prod.snd hc
  dsimp [p,sub] at hx hy
  exact ⟨by linarith,by nlinarith only [hy]⟩

/-- W and S have the candidate reflected local centers. -/
theorem west_center_unique {a b sgn : ℝ} (hs : sgn=1 ∨ sgn= -1)
    (hbox : (|a|+1/2)^2+(|b|+1/2)^2≤Six.radius^2)
    (heq : (1+rStar)*a+sgn*mStar*b=scalarSupport Six.radius (1+rStar) (sgn*mStar)) :
    a=1-Six.sStar ∧ b=sgn*Six.tStar := by
  have hsgn := sign_square_abs hs
  let p : Point := (3/2-Six.sStar,sgn*(Six.tStar+1/2))
  let l : ℝ := (1+rStar)/(3/2-Six.sStar)
  have hp : normSq p=Six.radius^2 := by
    dsimp [p,normSq]
    rw [mul_pow,hsgn.1,one_mul]
    nlinarith [Six.west_radius_identity,Six.radius_sq]
  have hl : 0≤l := (div_pos one_add_rStar_pos kStar_den_pos).le
  have hgp : (1+rStar,sgn*mStar)=scale l p := by
    apply Prod.ext
    · dsimp [scale,l,p]
      field_simp [ne_of_gt kStar_den_pos]
    · dsimp [scale,l,p,mStar,kStar]
      field_simp [ne_of_gt kStar_den_pos]
      ring
  have hsign : sgn*(sgn*mStar)=|sgn*mStar| := by
    rw [abs_mul,hsgn.2,abs_of_pos mStar_pos,one_mul]
    calc
      sgn*(sgn*mStar)=sgn^2*mStar := by ring
      _=mStar := by rw [hsgn.1,one_mul]
  have hg : (1+rStar,sgn*mStar)≠(0,0) := by
    intro h
    have hx := congrArg Prod.fst h
    dsimp only at hx
    linarith [one_add_rStar_pos]
  have he : (1+rStar)*a+(sgn*mStar)*b=
      Six.radius*Real.sqrt ((1+rStar)^2+(sgn*mStar)^2)-(|1+rStar|+|sgn*mStar|)/2 := by
    rwa [west_full_support hs] at heq
  have hc := scalar_vertex_center Six.radius_pos.le hg hbox
    (show |(1:ℝ)|=1 by norm_num) hsgn.2
    (by simpa using (abs_of_pos one_add_rStar_pos).symm) hsign hp hl hgp he
  have hx := congrArg Prod.fst hc
  have hy := congrArg Prod.snd hc
  dsimp [p,sub] at hx hy
  exact ⟨by linarith,by nlinarith only [hy]⟩

/-- D's positive primary force attains the axial cap only at b=0. -/
theorem diagonal_center_unique {a b : ℝ}
    (hbox : (|a|+1/2)^2+(|b|+1/2)^2≤Six.radius^2)
    (heq : diagonalK*a=scalarSupport Six.radius diagonalK 0) :
    a=rhoStar ∧ b=0 := by
  rw [scalarSupport_positive_axis diagonalK_pos.le] at heq
  have ha : a=rhoStar := by
    change diagonalK*a=rhoStar*diagonalK at heq
    nlinarith [diagonalK_pos]
  rw [ha,abs_of_pos (by linarith [rhoStar_gt_11_10]),Six.radius_sq] at hbox
  have hb : |b|=0 := by
    nlinarith [rhoStar_identity,abs_nonneg b,sq_nonneg |b|]
  exact ⟨ha,abs_eq_zero.mp hb⟩

end SquaresInCircles.Six.Equality
