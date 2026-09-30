import SquaresInCircles.Six.Stress.PairCertificateChecks

/-!
# The local pair bound across all three absolute-value walls

The six closed sectors cover the whole small square, including their common
walls and the candidate. On each sector the threshold has an exact smooth
formula. A universally valid smooth upper support is used for the centers.
The derivative certificates prove monotonicity on the ray-coordinate square;
no derivative of a nonsmooth exact support is assumed.
-/

noncomputable section
namespace SquaresInCircles.Six.Stress.PairCertificate
open ProofTools Normalization

def sectorN (k : Fin 6) (x y : ℝ) : ℝ := ((nRay k).1:ℝ)*x+((nRay k).2:ℝ)*y
def sectorW (k : Fin 6) (x y : ℝ) : ℝ := ((wRay k).1:ℝ)*x+((wRay k).2:ℝ)*y

lemma sector_sign_values (k : Fin 6) :
    (nSign k=1 ∨ nSign k= -1) ∧ (wSign k=1 ∨ wSign k= -1) ∧
      (qSign k=1 ∨ qSign k= -1) := by
  fin_cases k <;> norm_num [nSign,wSign,qSign]

lemma sector_bounds (k : Fin 6) {x y : ℝ}
    (hx : 0≤x ∧ x≤1/128) (hy : 0≤y ∧ y≤1/128) :
    0≤(nSign k:ℝ)*sectorN k x y ∧ 0≤(wSign k:ℝ)*sectorW k x y ∧
    0≤(qSign k:ℝ)*(sectorN k x y-sectorW k x y) ∧
    (-1/64≤sectorN k x y ∧ sectorN k x y≤1/64) ∧
    (-1/64≤sectorW k x y ∧ sectorW k x y≤1/64) ∧
    (-1/64≤sectorN k x y-sectorW k x y ∧ sectorN k x y-sectorW k x y≤1/64) := by
  fin_cases k <;> norm_num [sectorN,sectorW,nRay,wRay,nSign,wSign,qSign]
  all_goals repeat' constructor
  all_goals linarith [hx.1,hx.2,hy.1,hy.2]

/-- Exact sector coverage, with nonnegative ray coordinates bounded by 1/128. -/
theorem sector_cover {n w : ℝ} (hn : |n|≤1/128) (hw : |w|≤1/128) :
    ∃ k : Fin 6, ∃ x y : ℝ, (0≤x ∧ x≤1/128) ∧ (0≤y ∧ y≤1/128) ∧
      n=sectorN k x y ∧ w=sectorW k x y := by
  have hn' := abs_le.mp hn
  have hw' := abs_le.mp hw
  by_cases hn0 : n≤0
  · by_cases hw0 : w≤0
    · by_cases hnw : n≤w
      · refine ⟨0,w-n,-w,?_,?_,?_,?_⟩
        all_goals norm_num [sectorN,sectorW,nRay,wRay]
        all_goals first | constructor <;> linarith [hn'.1,hn'.2,hw'.1,hw'.2] | ring
      · refine ⟨1,-n,n-w,?_,?_,?_,?_⟩
        all_goals norm_num [sectorN,sectorW,nRay,wRay]
        all_goals first | constructor <;> linarith [hn'.1,hn'.2,hw'.1,hw'.2] | ring
    · refine ⟨2,-n,w,?_,?_,?_,?_⟩
      all_goals norm_num [sectorN,sectorW,nRay,wRay]
      all_goals first | constructor <;> linarith [hn'.1,hn'.2,hw'.1,hw'.2] | ring
  · by_cases hw0 : w≤0
    · refine ⟨3,n,-w,?_,?_,?_,?_⟩
      all_goals norm_num [sectorN,sectorW,nRay,wRay]
      all_goals first | constructor <;> linarith [hn'.1,hn'.2,hw'.1,hw'.2] | ring
    · by_cases hnw : n≤w
      · refine ⟨4,n,w-n,?_,?_,?_,?_⟩
        all_goals norm_num [sectorN,sectorW,nRay,wRay]
        all_goals first | constructor <;> linarith [hn'.1,hn'.2,hw'.1,hw'.2] | ring
      · refine ⟨5,n-w,w,?_,?_,?_,?_⟩
        all_goals norm_num [sectorN,sectorW,nRay,wRay]
        all_goals first | constructor <;> linarith [hn'.1,hn'.2,hw'.1,hw'.2] | ring

lemma abs_eq_signed {sgn : ℚ} {t : ℝ} (hs : sgn=1 ∨ sgn= -1)
    (ht : 0≤(sgn:ℝ)*t) : |t|=(sgn:ℝ)*t := by
  rcases hs with rfl | rfl
  · norm_num at ht ⊢
    exact abs_of_nonneg ht
  · norm_num at ht ⊢
    exact abs_of_nonpos (by linarith)

lemma half_eq_signed {sgn : ℚ} {t : ℝ} (hs : sgn=1 ∨ sgn= -1)
    (ht : 0≤(sgn:ℝ)*t) (hb : -1/64≤t ∧ t≤1/64) :
    (1+Real.cos t+(sgn:ℝ)*Real.sin t)/2=1/2+angularWidth t := by
  have hc : 0≤Real.cos t := (Real.cos_pos_of_mem_Ioo
    (show t ∈ Set.Ioo (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [hb.1,hb.2,Real.pi_gt_d2])).le
  rcases hs with rfl | rfl
  · have ht0 : 0≤t := by norm_num at ht; exact ht
    have hsin := Real.sin_nonneg_of_nonneg_of_le_pi ht0 (by linarith [hb.2,Real.pi_gt_d2])
    simp only [angularWidth,abs_of_nonneg hc,abs_of_nonneg hsin,Rat.cast_one,one_mul]
    ring
  · have ht0 : t≤0 := by norm_num at ht; linarith
    have hsin : Real.sin t≤0 := by
      have hh := Real.sin_nonneg_of_nonneg_of_le_pi (show 0≤-t by linarith)
        (show -t≤Real.pi by linarith [hb.1,Real.pi_gt_d2])
      rw [Real.sin_neg] at hh
      linarith
    simp only [angularWidth,abs_of_nonneg hc,abs_of_nonpos hsin,Rat.cast_neg,Rat.cast_one,neg_one_mul]
    ring

lemma line_eq_signed {sgn : ℚ} {t : ℝ} (hs : sgn=1 ∨ sgn= -1)
    (ht : 0≤(sgn:ℝ)*t) :
    pairLine t=((if sgn=1 then (-13/50:ℚ) else -73/100):ℝ)*t := by
  rcases hs with rfl | rfl
  · have ht0 : 0≤t := by norm_num at ht; exact ht
    simp [pairLine,max_eq_left ht0,max_eq_right (show -t≤0 by linarith)]
    ring
  · have ht0 : t≤0 := by norm_num at ht; linarith
    simp [pairLine,max_eq_right ht0,max_eq_left (show 0≤-t by linarith)]
    ring

@[simp] lemma value_northForce_first {k : ℕ} (x : Fin k → ℝ) (no wo : Bool) (u : Fin 4) (n w : Smooth k) :
    (northForceE no wo u n w).1.value x=(pairNorthForce no wo u (n.value x) (w.value x)).1 :=
  congrArg Prod.fst (value_northForceE x no wo u n w)

@[simp] lemma value_northForce_second {k : ℕ} (x : Fin k → ℝ) (no wo : Bool) (u : Fin 4) (n w : Smooth k) :
    (northForceE no wo u n w).2.value x=(pairNorthForce no wo u (n.value x) (w.value x)).2 :=
  congrArg Prod.snd (value_northForceE x no wo u n w)

@[simp] lemma value_westForce_first {k : ℕ} (x : Fin k → ℝ) (no wo : Bool) (u : Fin 4) (n w : Smooth k) :
    (westForceE no wo u n w).1.value x=(pairWestForce no wo u (n.value x) (w.value x)).1 :=
  congrArg Prod.fst (value_westForceE x no wo u n w)

@[simp] lemma value_westForce_second {k : ℕ} (x : Fin k → ℝ) (no wo : Bool) (u : Fin 4) (n w : Smooth k) :
    (westForceE no wo u n w).2.value x=(pairWestForce no wo u (n.value x) (w.value x)).2 :=
  congrArg Prod.snd (value_westForceE x no wo u n w)

def smoothPairValue (no wo : Bool) (u : Fin 4) (sgnN sgnW sgnQ : ℚ) (n w : ℝ) : ℝ :=
  pairAlpha no wo n w*((1+Real.cos n+(sgnN:ℝ)*Real.sin n)/2)+
    pairGamma no wo n w*((1+Real.cos w+(sgnW:ℝ)*Real.sin w)/2)+
    rStar*((1+Real.cos (n-w)+(sgnQ:ℝ)*Real.sin (n-w))/2)+mStar/2-
    northVertex (pairNorthForce no wo u n w).1 (pairNorthForce no wo u n w).2-
    northVertex (pairWestForce no wo u n w).1 (pairWestForce no wo u n w).2

lemma localGap_value (no wo : Bool) (u : Fin 4) (k : Fin 6) (x y : ℝ) :
    (localGap no wo u k).value ![x,y]=
      smoothPairValue no wo u (nSign k) (wSign k) (qSign k) (sectorN k x y) (sectorW k x y)-
        pairBase-((if wSign k=1 then (-13/50:ℚ) else -73/100):ℝ)*sectorW k x y-
        (1/1000)*(nSign k:ℝ)*sectorN k x y := by
  simp [localGap,smoothPairValue,sectorN,sectorW]

lemma localGap_zero (no wo : Bool) (u : Fin 2) (k : Fin 6) :
    (localGap no wo (candidateSource u) k).value ![0,0]=0 := by
  have hu : candidateSource u=0 ∨ candidateSource u=3 := by fin_cases u <;> simp [candidateSource]
  have hf := pair_candidate_forces no wo hu
  rw [localGap_value]
  simp only [sectorN,sectorW,mul_zero,add_zero,sub_zero,Real.cos_zero,Real.sin_zero,
    smoothPairValue,pairAlpha_zero,pairGamma_zero,one_mul,zero_mul,add_zero,hf.1,hf.2]
  have hb := pairBase_vertex_identity
  linarith

lemma localGap_le_actual (no wo : Bool) (u : Fin 4) (k : Fin 6) {x y : ℝ}
    (hx : 0≤x ∧ x≤1/128) (hy : 0≤y ∧ y≤1/128) :
    (localGap no wo u k).value ![x,y] ≤
      pairValue no wo u (sectorN k x y) (sectorW k x y)-pairBase-
        pairLine (sectorW k x y)-(1/1000)*|sectorN k x y| := by
  obtain ⟨hn,hw,hq,hnb,hwb,hqb⟩ := sector_bounds k hx hy
  have signs := sector_sign_values k
  have hhn := half_eq_signed signs.1 hn hnb
  have hhw := half_eq_signed signs.2.1 hw hwb
  have hhq := half_eq_signed signs.2.2 hq hqb
  have hline := line_eq_signed signs.2.1 hw
  have habs := abs_eq_signed signs.1 hn
  have hsn := scalarSupport_le_northVertex
    (pairNorthForce no wo u (sectorN k x y) (sectorW k x y)).1
    (pairNorthForce no wo u (sectorN k x y) (sectorW k x y)).2
  have hsw := scalarSupport_le_northVertex
    (pairWestForce no wo u (sectorN k x y) (sectorW k x y)).1
    (pairWestForce no wo u (sectorN k x y) (sectorW k x y)).2
  rw [localGap_value,smoothPairValue,hhn,hhw,hhq,hline,habs]
  dsimp [pairValue,pairThreshold]
  nlinarith only [hsn,hsw]

lemma localGap_nonnegative (no wo : Bool) (u : Fin 2) (sector : Fin 6) {x y : ℝ}
    (hx : 0≤x ∧ x≤1/128) (hy : 0≤y ∧ y≤1/128) :
    0≤(localGap no wo (candidateSource u) sector).value ![x,y] := by
  have hmono := Smooth.origin_le_on_square (localGap no wo (candidateSource u) sector) hx hy
    (fun axis a b ha0 ha1 hb0 hb1 => by
      have hroot : localRoot.Mem ![a,b] := by
        intro i
        fin_cases i
        · exact ⟨ha0,ha1⟩
        · exact ⟨hb0,hb1⟩
      have hh := Smooth.checked_derivative axis (localGap no wo (candidateSource u) sector)
        (1/100) (fun _ => 1) 0 24 localRoot
        (local_derivative_checked no wo u sector axis) hroot
      exact ⟨hh.1,by linarith [hh.2]⟩)
  rwa [localGap_zero] at hmono

/-- The local result includes n=w=0 and every sign/support wall. -/
theorem local_pair_lower (no wo : Bool) (u : Fin 2) {n w : ℝ}
    (hn : |n|≤1/128) (hw : |w|≤1/128) :
    pairBase+pairLine w+(1/1000)*|n|≤pairValue no wo (candidateSource u) n w := by
  obtain ⟨k,x,y,hx,hy,rfl,rfl⟩ := sector_cover hn hw
  have hlocal := localGap_nonnegative no wo u k hx hy
  have hactual := localGap_le_actual no wo (candidateSource u) k hx hy
  linarith

end SquaresInCircles.Six.Stress.PairCertificate
