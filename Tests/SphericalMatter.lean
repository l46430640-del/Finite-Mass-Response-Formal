import CauchyHorizon.Reduced.SphericalMatter
import CauchyHorizon.Reduced.RegularCrossing

open CauchyHorizon Set MeasureTheory
open scoped Manifold ContDiff

-- The field has the paper's du wedge dV orientation, with coordinates ordered (V,u).
example (f : ℝ) (p : UnitSphere) :
    sphereElectricForm f p ![((0, 1), 0), ((1, 0), 0)] = f ∧
    sphereElectricForm f p ![((1, 0), 0), ((0, 1), 0)] = -f := by
  simp [sphereElectricForm_apply]

example (f : ℝ) (p : UnitSphere) (a : (ℝ × ℝ) × TangentSpace (𝓡 2) p) :
    sphereElectricForm f p ![a, a] = 0 :=
  (sphereElectricForm f p).map_eq_zero_of_eq _ (i := 0) (j := 1) rfl (by decide)

-- These are pullbacks by the actual inverse-chart derivative, including both translations.
example {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (e : ℝ) (x : WaveState U V)
    (c : OpenPartialHomeomorph UnitSphere (ℝ × ℝ)) (θ φ : ℝ) (w : (ℝ × ℝ) × (ℝ × ℝ)) :
    chartMaxwell hU hV e x c θ φ w = coordinateMaxwell hU hV e x w ∧
    chartScalarGradient hU hV x c θ φ w = coordinateScalarGradient hU hV x w ∧
    chartScalarFlux hU hV x c θ φ w = coordinateScalarFlux hU hV x θ w :=
  ⟨chartMaxwell_eq hU hV e x c θ φ w, chartScalarGradient_eq hU hV x c θ φ w,
    (chartMatterFlux_eq hU hV e x c θ φ w).2⟩

example {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (e : ℝ) (x : WaveState U V)
    (c d : OpenPartialHomeomorph UnitSphere (ℝ × ℝ)) (v y : ℝ × ℝ) (a b : Fin 4 → ℝ) :
    let t := c.symm.trans d
    let T := angularVectorChange (fderiv ℝ t y)
    sphericalMaxwell hU hV e x v (d.symm (t y))
      ![sphericalChartDifferential d (t y) (T a), sphericalChartDifferential d (t y) (T b)] =
      sphericalMaxwell hU hV e x v (c.symm y)
        ![sphericalChartDifferential c y a, sphericalChartDifferential c y b] :=
  (sphericalMatter_transition hU hV e x c d v y a b).2.2

-- All three systems hold on the same actual charts around every sphere point.
example {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V} {x : WaveState U V}
    (hR : HasSphericalRicci hU hV e Λ x) (hE : HasCoordinateEinsteinEquation hU hV e Λ x)
    (hM : HasCoordinateMaxwell hU hV e x) (hS : HasCoordinateScalarEquation hU hV x) :
    HasSphericalFieldEquations hU hV e Λ x := hR.spherical_field_equations hE hM hS

example {U ε e Λ T₀ u₀ : ℝ} (hε : 0 ≤ ε) (hεU : ε ≤ U)
    {X : (S : Ici (0 : ℝ)) → WaveState U S} {χ : ℝ → ℝ}
    {Z : C(Icc ε U, WaveVector)} {O : C(Icc ε U, ℝ)}
    {D : ℝ → C(Icc ε U, WaveVector)} {Dh : C(Icc ε U, WaveVector)}
    (hcross : HasRegularCrossingSolution hε hεU e Λ X χ Z O D Dh T₀ u₀) :
    ∃ L W : ℝ, ∃ hL : 0 ≤ L, ∃ hW : 0 ≤ W, ∃ y : WaveState W L,
      (∀ t s, 0 < y.1 t s 0) ∧ HasSphericalConnectionTransition hW hL y ∧
        HasSphericalFieldEquations hW hL e Λ y := by
  obtain ⟨_ua, L, T, b, _hea, _ham, _hmr, _hrU, _hT₀, _hT, _hn, _hb,
    hL, hW, _zIn, _vOut, _uIn, y, _hy, _hprim, _hpast, _hfuture, _hout, _hxin, _hbottom,
    hr, _hmatch, _hvelocity, _hc, _hi, _hweak, _hdistribution, _hL2, _hmetric, _hcoord, _hconnection,
    _hRicci, _hsource, _hmixed, _hangular, _hoffdiag, _hmaxwell, _heinstein, _hscalar, _hsphere,
    htransition, hfields, _rest⟩ := hcross
  exact ⟨L, _, hL, hW, y, hr, htransition, hfields⟩
