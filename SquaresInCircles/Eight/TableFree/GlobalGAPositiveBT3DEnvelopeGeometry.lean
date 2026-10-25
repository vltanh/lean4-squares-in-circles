module

public import SquaresInCircles.Eight.TableFree.GlobalGAPositiveBT3DEndpoints
public import SquaresInCircles.Eight.TableFree.ContactArcMinimum

/-!
# Exact support and intrinsic branch endpoints for the BT3 D minorant

Uncompiled transcription of Sections 2--5 of the sorted-D low-angle
companion.  The scalar support is attained on its true sorted arc.
Concavity in the weight follows from that same support point.  The
branch endpoint principle below is a compact-interval formulation of
the hand proof's continuous support transitions, with no angle mesh.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.GlobalGA.PositiveBT3
open Candidate Secondary PositiveAngularEnvelope OrdinaryAngleConcavity
open PairNormCalculus OrdinaryNegativeSlope

theorem sortedSupport_attained {f g : ℝ} (hf : 0<f) (hg : 0<g) :
    ∃a b : ℝ,0<a ∧ 0≤b ∧ b≤a ∧
      (a+1/2)^2+(b+1/2)^2=qCap ∧ sortedSupport f g=f*a+g*b := by
  by_cases hfg : f≤g
  · have hd0 : (0:ℝ)<GlobalGA.Secondary.diagonal :=
      (by norm_num : (0:ℝ)<8992140/10000000).trans diagonal_bounds.1
    refine ⟨GlobalGA.Secondary.diagonal,GlobalGA.Secondary.diagonal,hd0,hd0.le,le_rfl,
      by rw [← diagonal_circle]; ring,?_⟩
    simp [sortedSupport,hfg,diagonalSupport]
    ring
  by_cases haxis : (axial+1/2)*g≤f/2
  · have ha0 : (0:ℝ)<axial := (by norm_num : (0:ℝ)<14145756/10000000).trans axial_bounds.1
    refine ⟨axial,0,ha0,le_rfl,ha0.le,by rw [zero_add]; exact axial_circle,?_⟩
    rw [sortedSupport_axis hg haxis]
    ring
  let N := Real.sqrt (f^2+g^2)
  have hN : 0<N := Real.sqrt_pos.mpr (by positivity)
  have hN2 : N^2=f^2+g^2 := Real.sq_sqrt (by positivity)
  let a := R*f/N-1/2
  let b := R*g/N-1/2
  have hR : 0<R := Real.sqrt_pos.mpr (by norm_num [qCap])
  have hA : 0<axial+1/2 := by linarith [axial_bounds.1]
  have hcross : N/2<R*g := by
    have hstrict : f/2<(axial+1/2)*g := lt_of_not_ge haxis
    have hsquare := pow_lt_pow_left₀ hstrict (by positivity : 0≤f/2) (by norm_num : (2:ℕ)≠0)
    have hmul : ((axial+1/2)^2+(1/2)^2)*g^2=qCap*g^2 := by rw [axial_circle]
    have he : (R*g)^2=qCap*g^2 := by rw [mul_pow,radius_sq]
    have hsq : (N/2)^2<(R*g)^2 := by
      rw [he]
      linarith [hN2,hsquare,hmul]
    exact lt_of_pow_lt_pow_left₀ 2 (mul_pos hR hg).le hsq
  have hb0 : 0≤b := by
    have hh := (lt_div_iff₀ hN).2 (show (1/2)*N<R*g by linarith)
    dsimp [b]
    linarith
  have hsort : b≤a := by
    have hh := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (lt_of_not_ge hfg).le hR.le) hN.le
    dsimp [a,b]
    linarith
  have hc : (a+1/2)^2+(b+1/2)^2=qCap := by
    have ha' : a+1/2=R*f/N := by dsimp [a]; ring
    have hb' : b+1/2=R*g/N := by dsimp [b]; ring
    rw [ha',hb',div_pow,div_pow,← add_div,mul_pow,mul_pow,← mul_add,← hN2,radius_sq,
      mul_div_assoc,div_self (pow_ne_zero 2 hN.ne'),mul_one]
  have ha0 : 0<a := by
    have hh : GlobalGA.Secondary.diagonal≤a := by
      by_contra hlt
      have hlt' : a<GlobalGA.Secondary.diagonal := lt_of_not_ge hlt
      have p1 := mul_pos (sub_pos.mpr hlt')
        (show 0<GlobalGA.Secondary.diagonal+a+1 by linarith [diagonal_bounds.1])
      have p2 := mul_nonneg (sub_nonneg.mpr hsort) (show 0≤a+b+1 by linarith)
      linarith [diagonal_circle]
    linarith [diagonal_bounds.1]
  refine ⟨a,b,ha0,hb0,hsort,hc,?_⟩
  simp only [sortedSupport,hfg,haxis,↓reduceIte]
  change R*N-(f+g)/2=f*a+g*b
  have hfg' : f*a+g*b=R*(f^2+g^2)/N-(f+g)/2 := by dsimp [a,b]; ring
  rw [hfg',← hN2]
  field_simp

/-- The actual sorted support, including its tangent-zero branch, is
convex along the coefficient interpolation used in the hand proof. -/
theorem D_weight_concave {c x y : ℝ} (hc : c∈Icc 1 Cmax)
    (hx : |x|≤frameCap) (hy : |y|≤frameCap) :
    ((Cmax-c)/(Cmax-1))*D 1 x y+((c-1)/(Cmax-1))*D Cmax x y≤D c x y := by
  have hp := force_positive hc hx hy
  obtain ⟨a,b,ha,hb,hs,hcircle,he⟩ := sortedSupport_attained hp.1 hp.2
  have hp1 := force_positive (show (1:ℝ)∈Icc 1 Cmax by norm_num [Cmax]) hx hy
  have hpC := force_positive (show Cmax∈Icc 1 Cmax by norm_num [Cmax]) hx hy
  have h1 := raw_sorted_support ha hb hs hcircle.le hp1.1.le hp1.2.le
  have hC := raw_sorted_support ha hb hs hcircle.le hpC.1.le hpC.2.le
  have hden : 0<Cmax-1 := by norm_num [Cmax]
  obtain ⟨α,hαd⟩ : ∃α:ℝ,α=(Cmax-c)/(Cmax-1) := ⟨_,rfl⟩
  obtain ⟨β,hβd⟩ : ∃β:ℝ,β=(c-1)/(Cmax-1) := ⟨_,rfl⟩
  have hα : 0≤α := by rw [hαd]; exact div_nonneg (sub_nonneg.mpr hc.2) hden.le
  have hβ : 0≤β := by rw [hβd]; exact div_nonneg (sub_nonneg.mpr hc.1) hden.le
  have hbary : α+β=1 := by rw [hαd,hβd]; field_simp [hden.ne']; ring
  have hcoef : α+β*Cmax=c := by rw [hαd,hβd]; field_simp [hden.ne']; ring
  rw [← hαd,← hβd]
  have hA : forceA c x y=α*forceA 1 x y+β*forceA Cmax x y := by
    simp only [forceA]
    linear_combination (-Real.sin x)*hcoef+(-Real.cos y)*hbary
  have hB : forceB c x y=α*forceB 1 x y+β*forceB Cmax x y := by
    simp only [forceB]
    linear_combination (-Real.cos x)*hcoef+(-Real.sin y)*hbary
  have key : D c x y-(α*D 1 x y+β*D Cmax x y)=
      α*(sortedSupport (forceA 1 x y) (forceB 1 x y)-(forceA 1 x y*a+forceB 1 x y*b))+
      β*(sortedSupport (forceA Cmax x y) (forceB Cmax x y)-
        (forceA Cmax x y*a+forceB Cmax x y*b)) := by
    simp only [D]
    rw [he,hA,hB]
    linear_combination (-(edgeWidth x-1)-GlobalGA.Secondary.diagonal)*hcoef+
      (-(edgeWidth y-1)-GlobalGA.Secondary.diagonal)*hbary
  have k1 := mul_nonneg hα (sub_nonneg.mpr h1)
  have k2 := mul_nonneg hβ (sub_nonneg.mpr hC)
  linarith

theorem mixed_far_endpoint {c n : ℝ} (hc : c∈Icc 1 Cmax)
    (hn : n∈Icc 0 frameCap) :
    0<D c frameCap (-n)+slope*frameCap-vstar n := by
  have h1 := DEndpoint.endpoint .one hn
  have hC := DEndpoint.endpoint .upper hn
  have e1 : ((DEndpoint.coefficient .one:ℚ):ℝ)=1 := by norm_num [DEndpoint.coefficient]
  have eC : ((DEndpoint.coefficient .upper:ℚ):ℝ)=Cmax := by
    norm_num [DEndpoint.coefficient,Cmax]
  rw [e1] at h1
  rw [eC] at hC
  have hw := D_weight_concave (x:=frameCap) (y:=-n) hc (by norm_num [frameCap])
    (by rw [abs_neg,abs_of_nonneg hn.1]; exact hn.2)
  have hden : 0<Cmax-1 := by norm_num [Cmax]
  obtain ⟨α,hαd⟩ : ∃α:ℝ,α=(Cmax-c)/(Cmax-1) := ⟨_,rfl⟩
  obtain ⟨β,hβd⟩ : ∃β:ℝ,β=(c-1)/(Cmax-1) := ⟨_,rfl⟩
  have hα : 0≤α := by rw [hαd]; exact div_nonneg (sub_nonneg.mpr hc.2) hden.le
  have hβ : 0≤β := by rw [hβd]; exact div_nonneg (sub_nonneg.mpr hc.1) hden.le
  have hs : α+β=1 := by rw [hαd,hβd]; field_simp [hden.ne']; ring
  rw [← hαd,← hβd] at hw
  generalize D 1 frameCap (-n)=d1 at h1 hw
  generalize D Cmax frameCap (-n)=dC at hC hw
  generalize D c frameCap (-n)=dc at hw ⊢
  generalize slope*frameCap=sf at h1 hC ⊢
  generalize vstar n=v at h1 hC ⊢
  have hsv : α*(sf-v)+β*(sf-v)=sf-v := by rw [← add_mul,hs,one_mul]
  by_cases hα0 : α=0
  · have hβ1 : β=1 := by linarith
    rw [hα0,hβ1] at hw
    linarith
  · have k1 := mul_pos (lt_of_le_of_ne hα (Ne.symm hα0)) h1
    have k2 := mul_nonneg hβ hC.le
    linarith

theorem vstar_slope_zero : Vd R K 1 0<1101/1000 := by
  have hN := pairNorm_pos (p:=K) (q:=1) (t:=0) (by norm_num [K])
    (by norm_num) (by norm_num [frameCap])
  have hN2 := pairNorm_sq (p:=K) (q:=1) (t:=0) (by norm_num [K])
    (by norm_num) (by norm_num [frameCap])
  have hR2 : (R*K)^2=qCap*K^2 := by rw [mul_pow,radius_sq]
  have hs : (R*K)^2<((1101/1000)*pairNorm K 1 0)^2 := by
    norm_num [pairEnergy,pairProduct,K] at hN2
    norm_num [qCap,K] at hR2 ⊢
    nlinarith
  have hc : R*K<(1101/1000)*pairNorm K 1 0 := by
    nlinarith [Real.sqrt_nonneg qCap]
  have he : Vd R K 1 0=R*K/pairNorm K 1 0 := by
    simp [Vd,mixedNDerivative,normD1,pairProduct]
    ring
  rw [he]
  exact (div_lt_iff₀ hN).2 hc

theorem vstar_linear_upper {n : ℝ} (hn : n∈Icc 0 frameCap) :
    vstar n≤(1101/1000)*n := by
  have hh := V_tangent_zero (p:=K) (q:=1) (by norm_num [K])
    (by norm_num [K]) (by norm_num [K]) hn
  have hm := mul_le_mul_of_nonneg_right vstar_slope_zero.le hn.1
  exact hh.trans hm

def diagonalIncrement (w x : ℝ) : ℝ :=
  w*(edgeWidth x-1)-w*GlobalGA.Secondary.diagonal*(Real.sin x+Real.cos x-1)

theorem diagonal_negative_growth {n : ℝ} (hn : n∈Icc 0 frameCap) :
    (1327/1000)*n≤(GlobalGA.Secondary.diagonal+1/2)*Real.sin n+(GlobalGA.Secondary.diagonal-1/2)*(1-Real.cos n) := by
  have hh := derivative_reserve
    (f:=fun t => (GlobalGA.Secondary.diagonal+1/2)*Real.sin t+(GlobalGA.Secondary.diagonal-1/2)*(1-Real.cos t))
    (df:=fun t => (GlobalGA.Secondary.diagonal+1/2)*Real.cos t+(GlobalGA.Secondary.diagonal-1/2)*Real.sin t)
    (k:=1327/1000) (by fun_prop)
    (fun t ht => by
      convert ((Real.hasDerivAt_sin t).const_mul (GlobalGA.Secondary.diagonal+1/2)).add
        (((hasDerivAt_const t (1:ℝ)).sub (Real.hasDerivAt_cos t)).const_mul
          (GlobalGA.Secondary.diagonal-1/2)) using 1 <;> ring)
    (fun t ht => by
      have hh := PositiveTD.diagonal_slope_lower (Ioo_subset_Icc_self ht)
      linarith)
    (show (0:ℝ)∈Icc 0 frameCap by norm_num [frameCap]) hn hn.1
  simpa using hh

theorem diagonal_increment_lower {w x : ℝ} (hw : w∈Icc 1 Cmax)
    (hx : |x|≤frameCap) :
    -slope*positivePart x+(1327/1000)*negativePart x≤diagonalIncrement w x := by
  by_cases hx0 : 0≤x
  · have ht : x∈Icc 0 frameCap := ⟨hx0,by simpa [abs_of_nonneg hx0] using hx⟩
    have hphi : Real.sin x+Real.cos x-1≤x := by
      linarith [Real.sin_le hx0,Real.cos_le_one x]
    have hwd : w*(GlobalGA.Secondary.diagonal-1/2)≤ slope := by
      have hm := mul_le_mul_of_nonneg_right hw.2
        (by linarith [diagonal_bounds.1] : 0≤GlobalGA.Secondary.diagonal-1/2)
      have hd := mul_lt_mul_of_pos_left
        (show GlobalGA.Secondary.diagonal-1/2<(2/5:ℝ) by linarith [diagonal_bounds.2])
        (show 0<Cmax by norm_num [Cmax])
      norm_num [slope,Cmax] at *
      linarith
    have hmul := mul_le_mul_of_nonneg_left hphi
      (show 0≤w*(GlobalGA.Secondary.diagonal-1/2) from
        mul_nonneg (by linarith [hw.1]) (by linarith [diagonal_bounds.1]))
    have hsl := mul_le_mul_of_nonneg_right hwd hx0
    rw [diagonalIncrement,edgeWidth_positive_formula ht]
    simp only [positivePart,negativePart,max_eq_left hx0,
      max_eq_right (neg_nonpos.mpr hx0),mul_zero,add_zero]
    generalize slope=s at hsl ⊢
    linarith
  · have hn : -x∈Icc 0 frameCap := ⟨by linarith,(neg_le_abs x).trans hx⟩
    have hh := diagonal_negative_growth hn
    have hg : 0≤(GlobalGA.Secondary.diagonal+1/2)*Real.sin (-x)+(GlobalGA.Secondary.diagonal-1/2)*(1-Real.cos (-x)) := by
      linarith [hn.1]
    have hm := mul_le_mul_of_nonneg_right hw.1 hg
    have he : diagonalIncrement w x=
        w*((GlobalGA.Secondary.diagonal+1/2)*Real.sin (-x)+(GlobalGA.Secondary.diagonal-1/2)*(1-Real.cos (-x))) := by
      have hwidth := edgeWidth_negative_formula hn
      simp only [neg_neg] at hwidth
      rw [diagonalIncrement,hwidth,Real.sin_neg,Real.cos_neg]
      ring
    rw [he]
    simp only [positivePart,negativePart,max_eq_right (le_of_not_ge hx0),
      max_eq_left (show 0≤ -x by linarith),mul_zero,zero_add]
    linarith

/-- The explicit diagonal expression is safe throughout each orthant,
so integrating it does not assume that a path stays in that branch. -/
theorem diagonal_residual {c x y : ℝ} (hc : c∈Icc 1 Cmax)
    (hxy : SignedDomain x y) :
    0≤c*(edgeWidth x-1)+edgeWidth y-1+(1+c)*GlobalGA.Secondary.diagonal-
      diagonalSupport (forceA c x y) (forceB c x y)+
      slope*positiveTotal x y-vstar (negativeTotal x y) := by
  have hangle := signed_domain_angles hxy
  have hx := diagonal_increment_lower hc hangle.1
  have hy := diagonal_increment_lower
    (show (1:ℝ)∈Icc 1 Cmax by norm_num [Cmax]) hangle.2
  have hN : negativeTotal x y∈Icc 0 frameCap :=
    ⟨add_nonneg (negativePart_nonneg _) (negativePart_nonneg _),hxy.2⟩
  have hv := vstar_linear_upper hN
  have he : c*(edgeWidth x-1)+edgeWidth y-1+(1+c)*GlobalGA.Secondary.diagonal-
      diagonalSupport (forceA c x y) (forceB c x y)=
      diagonalIncrement c x+diagonalIncrement 1 y := by
    dsimp [diagonalSupport,forceA,forceB,diagonalIncrement]
    ring
  rw [he]
  have hh : 0≤diagonalIncrement c x+diagonalIncrement 1 y+
      slope*positiveTotal x y-vstar (negativeTotal x y) := by
    have hnx := negativePart_nonneg x
    have hny := negativePart_nonneg y
    dsimp only [positiveTotal,negativeTotal] at *
    generalize slope=s at hx hy ⊢
    linarith
  exact hh

/-- A continuous full-support branch is bounded by its intrinsic boundary
values.  Strict curvature excludes an interior minimum even if the set
of admissible branch parameters has several components. -/
theorem branch_lower {f df ddf e₁ e₂ : ℝ → ℝ} {l u x κ : ℝ}
    (hf : Continuous f) (he₁ : Continuous e₁) (he₂ : Continuous e₂)
    (hx : x∈Icc l u) (hx₁ : 0≤e₁ x) (hx₂ : 0≤e₂ x) (hκ : 0<κ)
    (hbound : ∀z∈Icc l u,0≤e₁ z → 0≤e₂ z →
      (z=l ∨ z=u ∨ e₁ z=0 ∨ e₂ z=0) → 0≤f z)
    (hd : ∀z∈Ioo l u,0<e₁ z → 0<e₂ z → HasDerivAt f (df z) z)
    (hdd : ∀z∈Ioo l u,0<e₁ z → 0<e₂ z → HasDerivAt df (ddf z) z)
    (hcurv : ∀z∈Ioo l u,0<e₁ z → 0<e₂ z → ddf z≤ -κ) : 0≤f x := by
  let S : Set ℝ := {z | z∈Icc l u ∧ 0≤e₁ z ∧ 0≤e₂ z}
  have hc : IsCompact S := by
    have hS : S=Icc l u∩{z | 0≤e₁ z}∩{z | 0≤e₂ z} := by
      ext z
      simp only [S,Set.mem_ofPred_eq,Set.mem_inter_iff,and_assoc]
    rw [hS]
    exact (isCompact_Icc.inter_right (isClosed_le continuous_const he₁)).inter_right
      (isClosed_le continuous_const he₂)
  have hxS : x∈S := ⟨hx,hx₁,hx₂⟩
  obtain ⟨z,hz,hmin⟩ := hc.exists_isMinOn ⟨x,hxS⟩ hf.continuousOn
  have hz' : z∈Icc l u ∧ 0≤e₁ z ∧ 0≤e₂ z := hz
  by_cases hb : z=l ∨ z=u ∨ e₁ z=0 ∨ e₂ z=0
  · exact (hbound z hz'.1 hz'.2.1 hz'.2.2 hb).trans (hmin hxS)
  have hzi : z∈Ioo l u := by
    simp only [not_or] at hb
    exact ⟨lt_of_le_of_ne hz'.1.1 (Ne.symm hb.1),lt_of_le_of_ne hz'.1.2 hb.2.1⟩
  have hp₁ : 0<e₁ z := by
    have hn : e₁ z≠0 := fun h => hb (Or.inr (Or.inr (Or.inl h)))
    exact lt_of_le_of_ne hz'.2.1 (Ne.symm hn)
  have hp₂ : 0<e₂ z := by
    have hn : e₂ z≠0 := fun h => hb (Or.inr (Or.inr (Or.inr h)))
    exact lt_of_le_of_ne hz'.2.2 (Ne.symm hn)
  let O : Set ℝ := {v | v∈Ioo l u ∧ 0<e₁ v ∧ 0<e₂ v}
  have hO : IsOpen O := by
    have hO' : O=Ioo l u∩{v | 0<e₁ v}∩{v | 0<e₂ v} := by
      ext v
      simp only [O,Set.mem_ofPred_eq,Set.mem_inter_iff,and_assoc]
    rw [hO']
    exact (isOpen_Ioo.inter (isOpen_lt continuous_const he₁)).inter
      (isOpen_lt continuous_const he₂)
  exact False.elim (not_minimum_on_strictly_concave_curve
    (s:=S) (cost:=f) (p:=z) (fun v hv => hmin hv)
    (curve:=id) (value:=f) (dvalue:=df) (ddvalue:=ddf)
    hO (show z∈O from ⟨hzi,hp₁,hp₂⟩) hκ rfl
    (fun v hv => ⟨Ioo_subset_Icc_self hv.1,hv.2.1.le,hv.2.2.le⟩)
    (fun _ _ => rfl)
    (fun v hv => hd v hv.1 hv.2.1 hv.2.2)
    (fun v hv => hdd v hv.1 hv.2.1 hv.2.2)
    (fun v hv => hcurv v hv.1 hv.2.1 hv.2.2))

theorem sortedSupport_full_of_between {f g : ℝ} (hf : 0<f) (hg : 0<g)
    (hfg : g≤f) (haxis : f/2≤(axial+1/2)*g) :
    sortedSupport f g=fullSupport f g := by
  by_cases hd : f≤g
  · have he : f=g := le_antisymm hd hfg
    rw [sortedSupport_diagonal hd]
    exact (full_at_diagonal he (add_nonneg hf.le hg.le)).symm
  by_cases ha : (axial+1/2)*g≤f/2
  · have he : (axial+1/2)*g=f/2 := le_antisymm ha haxis
    rw [sortedSupport_axis hg ha,full_at_axis hf.le hg.le he]
  · simp only [sortedSupport,hd,ha,↓reduceIte]


/-- The three explicit support regions are joined using only their exact
equality values.  The continuous full-circle branch is minimized on its
closed region; the other two regions have their direct hand estimates. -/
theorem support_path_lower {base f g df ddf : ℝ → ℝ} {l u x κ : ℝ}
    (hb : Continuous base) (hf : Continuous f) (hg : Continuous g)
    (hx : x∈Icc l u) (hκ : 0<κ)
    (hpos : ∀z∈Icc l u,0<f z ∧ 0<g z)
    (hdiag : ∀z∈Icc l u,0≤base z-diagonalSupport (f z) (g z))
    (haxis : ∀z∈Icc l u,(axial+1/2)*g z≤f z/2 → 0≤base z-f z*axial)
    (hl : 0≤base l-sortedSupport (f l) (g l))
    (hu : 0≤base u-sortedSupport (f u) (g u))
    (hd : ∀z∈Ioo l u,HasDerivAt (fun v => base v-fullSupport (f v) (g v)) (df z) z)
    (hdd : ∀z∈Ioo l u,HasDerivAt df (ddf z) z)
    (hcurv : ∀z∈Ioo l u,ddf z≤ -κ) :
    0≤base x-sortedSupport (f x) (g x) := by
  by_cases hdiagx : f x≤g x
  · simpa [sortedSupport_diagonal hdiagx] using hdiag x hx
  by_cases haxisx : (axial+1/2)*g x≤f x/2
  · rw [sortedSupport_axis (hpos x hx).2 haxisx]
    exact haxis x hx haxisx
  have hfcont : Continuous (fun v => base v-fullSupport (f v) (g v)) := by
    dsimp [fullSupport]
    fun_prop
  have hh := branch_lower
    (e₁:=fun z => f z-g z) (e₂:=fun z => (axial+1/2)*g z-f z/2)
    (df:=df) (ddf:=ddf) hfcont (by fun_prop) (by fun_prop) hx
    (by linarith [lt_of_not_ge hdiagx]) (by linarith [lt_of_not_ge haxisx]) hκ
    (fun z hz hz₁ hz₂ hedge => by
      have hp := hpos z hz
      rcases hedge with he|he|he|he
      · subst z
        rw [←sortedSupport_full_of_between hp.1 hp.2 (by linarith) (by linarith)]
        exact hl
      · subst z
        rw [←sortedSupport_full_of_between hp.1 hp.2 (by linarith) (by linarith)]
        exact hu
      · rw [full_at_diagonal (by linarith : f z=g z) (add_nonneg hp.1.le hp.2.le)]
        exact hdiag z hz
      · have heq : (axial+1/2)*g z=f z/2 := by linarith
        rw [full_at_axis hp.1.le hp.2.le heq]
        exact haxis z hz heq.le)
    (fun z hz _ _ => hd z hz) (fun z hz _ _ => hdd z hz)
    (fun z hz _ _ => hcurv z hz)
  rw [sortedSupport_full_of_between (hpos x hx).1 (hpos x hx).2
    (le_of_lt (lt_of_not_ge hdiagx)) (le_of_lt (lt_of_not_ge haxisx))]
  exact hh

end SquaresInCircles.Eight.TableFree.GlobalGA.PositiveBT3
