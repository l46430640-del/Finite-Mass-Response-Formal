import CauchyHorizon.Analysis.TransportEnergy

/-! A variable Young weight gives transport energy bounds uniform in the time endpoint. -/

open Set MeasureTheory

namespace CauchyHorizon

set_option maxHeartbeats 1200000 in
theorem transport_energy_bound {a b T S : ℝ} (hab : a ≤ b) (hTS : T ≤ S)
    {p q c A B d f g cv : ℝ × ℝ → ℝ} {G η : ℝ → ℝ}
    (hp : ContinuousOn p (Icc a b ×ˢ Icc T S))
    (hq : ContinuousOn q (Icc a b ×ˢ Icc T S))
    (hc : ContinuousOn c (Icc a b ×ˢ Icc T S))
    (hA : ContinuousOn A (Icc a b ×ˢ Icc T S))
    (hB : ContinuousOn B (Icc a b ×ˢ Icc T S))
    (hd : ContinuousOn d (Icc a b ×ˢ Icc T S))
    (hf : ContinuousOn f (Icc a b ×ˢ Icc T S))
    (hg : ContinuousOn g (Icc a b ×ˢ Icc T S))
    (hcv : ContinuousOn cv (Icc a b ×ˢ Icc T S))
    (hG : ContinuousOn G (Icc a b)) (hη : ContinuousOn η (Icc a b))
    (hη0 : ∀ x ∈ Icc a b, 0 < η x)
    (hc0 : ∀ z ∈ Icc a b ×ˢ Icc T S, 0 ≤ c z)
    (hcoef : ∀ z ∈ Icc a b ×ˢ Icc T S, |A z + B z| + |2 * d z + cv z| ≤ G z.1)
    (henergy : ∀ x ∈ Ioo a b,
      HasDerivAt (fun y => ∫ t in T..S, p (y, t) ^ 2 + q (y, t) ^ 2)
        ((∫ t in T..S, 2 * (A (x, t) + B (x, t)) * p (x, t) * q (x, t) +
          (2 * d (x, t) + cv (x, t)) * q (x, t) ^ 2 +
          2 * f (x, t) * p (x, t) + 2 * g (x, t) * q (x, t)) +
          c (x, T) * q (x, T) ^ 2 - c (x, S) * q (x, S) ^ 2) x) :
    (∫ t in T..S, p (b, t) ^ 2 + q (b, t) ^ 2) ≤
      ((∫ t in T..S, p (a, t) ^ 2 + q (a, t) ^ 2) +
        ∫ x in a..b, c (x, T) * q (x, T) ^ 2 +
          (∫ t in T..S, f (x, t) ^ 2 + g (x, t) ^ 2) / η x) *
        Real.exp (∫ x in a..b, G x + η x) := by
  let N := fun x => ∫ t in T..S, p (x, t) ^ 2 + q (x, t) ^ 2
  let J := fun z => 2 * (A z + B z) * p z * q z + (2 * d z + cv z) * q z ^ 2 +
    2 * f z * p z + 2 * g z * q z
  let N' := fun x => (∫ t in T..S, J (x, t)) + c (x, T) * q (x, T) ^ 2 - c (x, S) * q (x, S) ^ 2
  let H := fun x => c (x, T) * q (x, T) ^ 2 + (∫ t in T..S, f (x, t) ^ 2 + g (x, t) ^ 2) / η x
  have hNc : ContinuousOn N (Icc a b) := continuousOn_rectangle_integral hab hTS ((hp.pow 2).add (hq.pow 2))
  have hbottom {F : ℝ × ℝ → ℝ} (hF : ContinuousOn F (Icc a b ×ˢ Icc T S)) :
      ContinuousOn (fun x => F (x, T)) (Icc a b) :=
    hF.comp (continuous_id.prodMk continuous_const).continuousOn (fun _ hx => ⟨hx, ⟨le_rfl, hTS⟩⟩)
  have hHc : ContinuousOn H (Icc a b) :=
    ((hbottom hc).mul ((hbottom hq).pow 2)).add
      ((continuousOn_rectangle_integral hab hTS ((hf.pow 2).add (hg.pow 2))).div hη (fun x hx => (hη0 x hx).ne'))
  have hHi : IntervalIntegrable H volume a b := hHc.intervalIntegrable_of_Icc hab
  have hG0 (x : ℝ) (hx : x ∈ Icc a b) : 0 ≤ G x :=
    (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans (hcoef (x, T) ⟨hx, ⟨le_rfl, hTS⟩⟩)
  have hH0 (x : ℝ) (hx : x ∈ Icc a b) : 0 ≤ H x :=
    add_nonneg (mul_nonneg (hc0 (x, T) ⟨hx, ⟨le_rfl, hTS⟩⟩) (sq_nonneg _))
      (div_nonneg (intervalIntegral.integral_nonneg_of_forall hTS (fun t => add_nonneg (sq_nonneg _) (sq_nonneg _))) (hη0 x hx).le)
  have hbound (x : ℝ) (hx : x ∈ Icc a b) : N' x ≤ (G x + η x) * N x + H x := by
    have hslice {F : ℝ × ℝ → ℝ} (hF : ContinuousOn F (Icc a b ×ˢ Icc T S)) :
        ContinuousOn (fun t => F (x, t)) (Icc T S) :=
      hF.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ ht => ⟨hx, ht⟩)
    have hJ : ContinuousOn J (Icc a b ×ˢ Icc T S) := by dsimp only [J]; fun_prop
    have hmajor : ContinuousOn (fun t => (G x + η x) * (p (x, t) ^ 2 + q (x, t) ^ 2) +
        (f (x, t) ^ 2 + g (x, t) ^ 2) / η x) (Icc T S) :=
      (continuousOn_const.mul (((hslice hp).pow 2).add ((hslice hq).pow 2))).add
        ((((hslice hf).pow 2).add ((hslice hg).pow 2)).div_const _)
    have hpoint (t : ℝ) (ht : t ∈ Icc T S) : J (x, t) ≤
        (G x + η x) * (p (x, t) ^ 2 + q (x, t) ^ 2) +
          (f (x, t) ^ 2 + g (x, t) ^ 2) / η x := by
      let z := (x, t)
      have hcs : 2 * |p z| * |q z| ≤ p z ^ 2 + q z ^ 2 := by
        nlinarith only [sq_nonneg (|p z| - |q z|), sq_abs (p z), sq_abs (q z)]
      have hcross : 2 * (A z + B z) * p z * q z ≤ |A z + B z| * (p z ^ 2 + q z ^ 2) := by
        calc
          _ ≤ |2 * (A z + B z) * p z * q z| := le_abs_self _
          _ = |A z + B z| * (2 * |p z| * |q z|) := by rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hcs (abs_nonneg _)
      have hdiag := mul_le_mul_of_nonneg_right (le_abs_self (2 * d z + cv z)) (sq_nonneg (q z))
      have hge := mul_le_mul_of_nonneg_right (hcoef z ⟨hx, ht⟩) (add_nonneg (sq_nonneg (p z)) (sq_nonneg (q z)))
      have hgeom : 2 * (A z + B z) * p z * q z + (2 * d z + cv z) * q z ^ 2 ≤
          G x * (p z ^ 2 + q z ^ 2) := by
        nlinarith only [hcross, hdiag, hge, mul_nonneg (abs_nonneg (2 * d z + cv z)) (sq_nonneg (p z))]
      have hsource : 2 * f z * p z + 2 * g z * q z ≤
          η x * (p z ^ 2 + q z ^ 2) + (f z ^ 2 + g z ^ 2) / η x := by
        apply (mul_le_mul_iff_right₀ (hη0 x hx)).1
        have he := div_mul_cancel₀ (f z ^ 2 + g z ^ 2) (hη0 x hx).ne'
        nlinarith only [sq_nonneg (η x * p z - f z), sq_nonneg (η x * q z - g z), he]
      dsimp only [J]
      nlinarith only [hgeom, hsource]
    have hh := intervalIntegral.integral_mono_on (μ := volume) hTS
      ((hslice hJ).intervalIntegrable_of_Icc hTS) (hmajor.intervalIntegrable_of_Icc hTS) hpoint
    have hNi : IntervalIntegrable (fun t => p (x, t) ^ 2 + q (x, t) ^ 2) volume T S :=
      (((hslice hp).pow 2).add ((hslice hq).pow 2)).intervalIntegrable_of_Icc hTS
    have hSi : IntervalIntegrable (fun t => f (x, t) ^ 2 + g (x, t) ^ 2) volume T S :=
      (((hslice hf).pow 2).add ((hslice hg).pow 2)).intervalIntegrable_of_Icc hTS
    rw [intervalIntegral.integral_add (hNi.const_mul (G x + η x)) (hSi.div_const (η x)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_div] at hh
    have htop := mul_nonneg (hc0 (x, S) ⟨hx, ⟨hTS, le_rfl⟩⟩) (sq_nonneg (q (x, S)))
    dsimp only [N', N, H]
    linarith only [hh, htop]
  let M := fun x => N x + ((∫ y in a..b, H y) - ∫ y in a..x, H y)
  have hprimitive : ContinuousOn (fun x => ∫ y in a..x, H y) (Icc a b) := by
    simpa only [uIcc_of_le hab] using intervalIntegral.continuousOn_primitive_interval' hHi left_mem_uIcc
  have hMc : ContinuousOn M (Icc a b) := hNc.add (continuousOn_const.sub hprimitive)
  have hMd (x : ℝ) (hx : x ∈ Ioo a b) : HasDerivAt M (N' x - H x) x := by
    have hh := (henergy x hx).add ((primitive_hasDerivAt_interior hHi (hHc.mono Ioo_subset_Icc_self) hx).const_sub (∫ y in a..b, H y))
    simpa only [M, N, N', J, zero_sub, sub_eq_add_neg, Pi.add_def, Pi.sub_def] using! hh
  have hNM (x : ℝ) (hx : x ∈ Icc a b) : N x ≤ M x := by
    have hh := intervalIntegral.integral_mono_interval le_rfl hx.1 hx.2
      (show 0 ≤ᵐ[volume.restrict (Ioc a b)] H from by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
        exact hH0 y ⟨hy.1.le, hy.2⟩) hHi
    dsimp only [M]
    linarith only [hh]
  have hh := integrable_coefficient_gronwall hab ((hG.add hη).intervalIntegrable_of_Icc hab)
    ((hG.add hη).mono Ioo_subset_Icc_self) hMc hMd (fun x hx => by
      have hx' : x ∈ Icc a b := ⟨hx.1.le, hx.2.le⟩
      have hgrowth := mul_le_mul_of_nonneg_left (hNM x hx') (add_nonneg (hG0 x hx') (hη0 x hx').le)
      change N' x - H x ≤ (G x + η x) * M x
      linarith only [hbound x hx', hgrowth])
  simpa only [M, N, H, sub_self, add_zero, intervalIntegral.integral_same, sub_zero, Pi.add_apply] using hh

end CauchyHorizon
