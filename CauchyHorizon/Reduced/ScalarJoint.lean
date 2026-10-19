import CauchyHorizon.Reduced.ScalarSecond
import Mathlib.Analysis.Calculus.FDeriv.Partial

/-! Joint interior regularity without differentiating the outgoing scalar data. -/

open Set MeasureTheory Filter
open scoped Topology

namespace CauchyHorizon

set_option maxHeartbeats 1200000 in
theorem IsWaveIntegral.scalar_joint_contDiff
    {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x)
    {c : WaveVector} (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hinu : ∀ᵐ u ∂volume.restrict (Icc 0 U), uIn u 0 = -1)
    {F : ℝ → WaveVector} (hF : ContinuousOn F (Ioi 0))
    (hif : uIn =ᵐ[volume.restrict (Icc 0 U)] F)
    (hfs : ContDiffOn ℝ 1 (fun u => F u 1) (Ioi 0)) :
    let ν := radialNuField hV e Λ zIn x.1 hx.choose
    let C := scalarTransportCorrection hV ν x.2.1
    let ζ := fun p : ℝ × ℝ => zIn (projIcc 0 U hU p.1) 0 * F p.1 1 +
      C (projIcc 0 U hU p.1) (projIcc 0 V hV p.2)
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ =>
      x.1 (projIcc 0 U hU p.1) (projIcc 0 V hV p.2)) (Ioo 0 U ×ˢ Ioo 0 V) ∧
      ContDiffOn ℝ 1 ζ (Ioo 0 U ×ˢ Ioo 0 V) := by
  intro ν C ζ
  let D := Ioo (0 : ℝ) U ×ˢ Ioo (0 : ℝ) V
  have hDo : IsOpen D := isOpen_Ioo.prod isOpen_Ioo
  have hjoint {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      (g : ℝ → C(Icc 0 V, E)) (hg : ContDiffOn ℝ 1 g (Ioo 0 U))
      (G : ℝ × ℝ → E) (hG : ContinuousOn G D)
      (hd : ∀ p ∈ D, HasDerivAt (fun t => g p.1 (projIcc 0 V hV t)) (G p) p.2) :
      ContDiffOn ℝ 1 (fun p : ℝ × ℝ => g p.1 (projIcc 0 V hV p.2)) D := by
    let f := fun u v => g u (projIcc 0 V hV v)
    let A := fun p : ℝ × ℝ => ContinuousLinearMap.toSpanSingleton ℝ
      (deriv g p.1 (projIcc 0 V hV p.2))
    let B := fun p : ℝ × ℝ => ContinuousLinearMap.toSpanSingleton ℝ (G p)
    have hgc : ContinuousOn (fun p : ℝ × ℝ => deriv g p.1) D :=
      (hg.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl).comp
        continuousOn_fst (fun _ hp => hp.1)
    have hAc : ContinuousOn A D := by
      change ContinuousOn (fun p => ContinuousLinearMap.toSpanSingletonLIE ℝ E
        (deriv g p.1 (projIcc 0 V hV p.2))) D
      have he := continuous_eval.comp_continuousOn
        (hgc.prodMk (by fun_prop : ContinuousOn (fun p : ℝ × ℝ => projIcc 0 V hV p.2) D))
      exact (ContinuousLinearMap.toSpanSingletonLIE ℝ E).continuous.comp_continuousOn he
    have hBc : ContinuousOn B D :=
      (ContinuousLinearMap.toSpanSingletonLIE ℝ E).continuous.comp_continuousOn hG
    have hder (p : ℝ × ℝ) (hp : p ∈ D) :
        HasFDerivAt (Function.uncurry f) ((A p).coprod (B p)) p := by
      have hnear : ∀ᶠ q in 𝓝 p, q ∈ D := hDo.mem_nhds hp
      have hu : ∀ᶠ q in 𝓝 p, HasFDerivAt (f · q.2) (A q) q.1 := by
        filter_upwards [hnear] with q hq
        have hdg := ((hg q.1 hq.1).contDiffAt (isOpen_Ioo.mem_nhds hq.1)).differentiableAt (by norm_num)
        exact ((ContinuousMap.evalCLM ℝ (projIcc 0 V hV q.2)).hasFDerivAt.comp_hasDerivAt
          q.1 hdg.hasDerivAt).hasFDerivAt
      have hv : ∀ᶠ q in 𝓝 p, HasFDerivAt (f q.1 ·) (B q) q.2 :=
        hnear.mono (fun q hq => (hd q hq).hasFDerivAt)
      exact (hasStrictFDerivAt_uncurry_coprod (f := f)
        (f₁ := fun u v => A (u, v)) (f₂ := fun u v => B (u, v)) (u := p)
        hu hv (hAc.continuousAt (hDo.mem_nhds hp))
        (hBc.continuousAt (hDo.mem_nhds hp))).hasFDerivAt
    have hdc : ContinuousOn (fun p => (A p).coprod (B p)) D := by fun_prop
    apply (contDiffOn_succ_iff_fderiv_of_isOpen (n := 0) hDo).2
    refine ⟨fun p hp => (hder p hp).differentiableAt.differentiableWithinAt, ?_, ?_⟩
    · norm_num
    · apply contDiffOn_zero.2
      exact hdc.congr (fun p hp => (hder p hp).fderiv)
  have hreg := hx.scalar_transverse_contDiff hzin hinu hF hif hfs
  constructor
  · apply hjoint (intervalExtension hU x.1) hreg.1
      (fun p => x.2.1 (projIcc 0 U hU p.1) (projIcc 0 V hV p.2)) (by fun_prop)
    intro p hp
    have hpv : p.2 ∈ Icc 0 V := ⟨hp.2.1.le, hp.2.2.le⟩
    simpa only [intervalExtension_apply, projIcc_of_mem hV hpv] using!
      (hx.longitudinal_derivative (projIcc 0 U hU p.1) hpv).hasDerivAt
        (Icc_mem_nhds hp.2.1 hp.2.2)
  · let Z := fun u => ContinuousMap.const (Icc 0 V) (zIn (projIcc 0 U hU u) 0 * F u 1) +
      intervalExtension hU C u
    apply hjoint Z hreg.2.2.2
      (fun p => -ν (projIcc 0 U hU p.1) (projIcc 0 V hV p.2) *
        x.2.1 (projIcc 0 U hU p.1) (projIcc 0 V hV p.2) 1) (by fun_prop)
    intro p hp
    have hpv : p.2 ∈ Icc 0 V := ⟨hp.2.1.le, hp.2.2.le⟩
    have hd := (continuousPrimitive_hasDerivWithinAt hV
      (scalarTransportSource ν x.2.1 (projIcc 0 U hU p.1)) hpv).const_add
        (zIn (projIcc 0 U hU p.1) 0 * F p.1 1)
    simpa only [projIcc_of_mem hV hpv] using!
      hd.hasDerivAt (Icc_mem_nhds hp.2.1 hp.2.2)

end CauchyHorizon
