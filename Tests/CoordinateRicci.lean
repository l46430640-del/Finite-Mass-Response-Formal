import CauchyHorizon.Reduced.CoordinateRicci
import CauchyHorizon.Reduced.MixedRicciSources
import CauchyHorizon.Reduced.AngularRicciSources
import CauchyHorizon.Reduced.OffDiagonalRicciSources

open MeasureTheory Set
open scoped Distributions

namespace CauchyHorizon.Tests

-- A zero connection has zero Ricci distribution, including the tested derivative terms.
example (U V A B : ℝ) (i j : Fin 4) :
    ricciDistribution U V A B (fun _ _ _ _ => 0) i j = 0 := by
  have hp : HasRicciPairing U V A B (fun _ _ _ _ => 0) :=
    ricci_distribution_pairing (fun _ _ _ => by simp) (fun _ _ _ _ _ _ => by simp)
  ext ψ
  simpa [ricciTrace, ricciQuadratic] using (hp.2 i j ψ).2.2.2

-- Pure null log-lapse derivatives cancel when both radial derivatives vanish.
example (qell pell : ℝ) (i : Fin 2) :
    ricciQuadratic (nullMetricChristoffel 1 1 1 0 0 0 qell pell) (i.castAdd 2) (i.castAdd 2) = 0 := by
  have hh := (null_connection_contractions (H := 1) (r := 1) (s := 1) (c := 0)
    (qr := 0) (pr := 0) (qell := qell) (pell := pell) (by norm_num) (by norm_num) (by norm_num) i).2.2.1
  fin_cases i <;> simpa using hh

-- The rough direction is the first coordinate and carries the actual q representative.
example {U V e Λ A B θ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) {c : WaveVector}
    (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hθ : 0 < θ) (hθA : θ + A < Real.pi) :
    let r := fun w : (ℝ × ℝ) × (ℝ × ℝ) =>
      x.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2) 0
    let q := fun w : (ℝ × ℝ) × (ℝ × ℝ) => x.2.2 w.1.1 (projIcc 0 V hV w.1.2)
    ricciDistribution U V A B (coordinateChristoffel hU hV x θ) 0 0 =
      (-2 : ℝ) • Distribution.lineDerivCLM (n := ⊤) (k := ⊤) ((1, 0), (0, 0))
        (rectangleProductDistribution U V A B (fun w => q w 0 / r w)) +
      rectangleProductDistribution U V A B
        (fun w => 2 * q w 2 * (q w 0 / r w) - 2 * (q w 0 / r w) ^ 2) := by
  exact ((hx.coordinate_ricci hzin A B θ hA hB hθ hθA).2 0).2.2

-- The second null component uses p and the second coordinate, with the same sign and factor.
example {U V e Λ A B θ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) {c : WaveVector}
    (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hθ : 0 < θ) (hθA : θ + A < Real.pi) :
    let r := fun w : (ℝ × ℝ) × (ℝ × ℝ) =>
      x.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2) 0
    let p := fun w : (ℝ × ℝ) × (ℝ × ℝ) =>
      x.2.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2)
    ricciDistribution U V A B (coordinateChristoffel hU hV x θ) 1 1 =
      (-2 : ℝ) • Distribution.lineDerivCLM (n := ⊤) (k := ⊤) ((0, 1), (0, 0))
        (rectangleProductDistribution U V A B (fun w => p w 0 / r w)) +
      rectangleProductDistribution U V A B
        (fun w => 2 * p w 2 * (p w 0 / r w) - 2 * (p w 0 / r w) ^ 2) := by
  exact ((hx.coordinate_ricci hzin A B θ hA hB hθ hθA).2 1).2.2

-- The mixed contraction keeps its sign and radial factor for both index orders.
example (H c qell pell : ℝ) (i : Fin 2) :
    ricciQuadratic (nullMetricChristoffel H 2 1 c 3 5 qell pell)
      (i.castAdd 2) (i.rev.castAdd 2) = -15 / 2 := by
  have hh := (mixed_connection_contractions (H := H) (r := 2) (s := 1) (c := c)
    (qr := 3) (pr := 5) (qell := qell) (pell := pell) (by norm_num) (by norm_num) i).2
  norm_num at hh ⊢
  exact hh

-- Both actual mixed components have the same integrable source, including charge and Lambda.
example {U V e Λ A B θ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) {c : WaveVector}
    (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hθ : 0 < θ) (hθA : θ + A < Real.pi) :
    let source := fun w : (ℝ × ℝ) × (ℝ × ℝ) =>
      let z := x.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2)
      let p := x.2.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2)
      let q := x.2.2 w.1.1 (projIcc 0 V hV w.1.2)
      2 * q 1 * p 1 + Real.exp (z 2) * (e ^ 2 / (2 * z 0 ^ 4) - Λ / 2)
    Integrable source (rectangleProductMeasure U V A B) ∧
      ricciDistribution U V A B (coordinateChristoffel hU hV x θ) 0 1 =
        rectangleProductDistribution U V A B source ∧
      ricciDistribution U V A B (coordinateChristoffel hU hV x θ) 1 0 =
        rectangleProductDistribution U V A B source := by
  have hh := hx.mixed_ricci_sources hzin A B θ hA hB hθ hθA
  exact ⟨hh.1, hh.2 0, hh.2 1⟩

-- Mixed symmetry is a conclusion at this regularity, with no radial-constraint premise.
example {U V e Λ A B θ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) {c : WaveVector}
    (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hθ : 0 < θ) (hθA : θ + A < Real.pi) :
    ricciDistribution U V A B (coordinateChristoffel hU hV x θ) 0 1 =
      ricciDistribution U V A B (coordinateChristoffel hU hV x θ) 1 0 := by
  have hh := hx.mixed_ricci_sources hzin A B θ hA hB hθ hθA
  exact (hh.2 0).trans (hh.2 1).symm

-- A non-equatorial angular point keeps both intrinsic quadratic terms.
example (qell pell : ℝ) :
    ricciQuadratic (nullMetricChristoffel 1 1 (3 / 5) (4 / 5) 0 0 qell pell) 2 2 = -16 / 9 ∧
      ricciQuadratic (nullMetricChristoffel 1 1 (3 / 5) (4 / 5) 0 0 qell pell) 3 3 = 16 / 25 := by
  have hh := (angular_connection_contractions (H := 1) (r := 1) (s := 3 / 5) (c := 4 / 5)
    (qr := 0) (pr := 0) (qell := qell) (pell := pell) (by norm_num) (by norm_num) (by norm_num)).2.2.2.2
  norm_num at hh ⊢
  exact hh

-- Both diagonal angular sources follow without a radial-constraint or smoothness premise.
example {U V e Λ A B θ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) {c : WaveVector}
    (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hθ : 0 < θ) (hθA : θ + A < Real.pi) :
    let S := fun w : (ℝ × ℝ) × (ℝ × ℝ) =>
      let r := x.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2) 0
      e ^ 2 / r ^ 2 + Λ * r ^ 2
    Integrable S (rectangleProductMeasure U V A B) ∧
      Integrable (fun w => S w * Real.sin (θ + w.2.1) ^ 2) (rectangleProductMeasure U V A B) ∧
      ricciDistribution U V A B (coordinateChristoffel hU hV x θ) 2 2 =
        rectangleProductDistribution U V A B S ∧
      ricciDistribution U V A B (coordinateChristoffel hU hV x θ) 3 3 =
        rectangleProductDistribution U V A B (fun w => S w * Real.sin (θ + w.2.1) ^ 2) := by
  have h₀ := hx.angular_ricci_sources hzin A B θ hA hB hθ hθA 0
  have h₁ := hx.angular_ricci_sources hzin A B θ hA hB hθ hθA 1
  let S := fun w : (ℝ × ℝ) × (ℝ × ℝ) =>
    let r := x.1 (projIcc 0 U hU w.1.1) (projIcc 0 V hV w.1.2) 0
    e ^ 2 / r ^ 2 + Λ * r ^ 2
  have he : angularRicciSource hU hV e Λ x θ 0 = S := by
    funext w
    exact mul_one _
  rw [he] at h₀
  exact ⟨h₀.1, h₁.1, h₀.2, h₁.2⟩

-- No derivative or continuity is assumed in the coordinate on which the density depends.
example {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (f g : ℝ → ℝ)
    (hf : IntegrableOn (fun w : ℝ × ℝ => f w.2) (Icc 0 U ×ˢ Icc 0 V))
    (hg : IntegrableOn (fun w : ℝ × ℝ => g w.1) (Icc 0 U ×ˢ Icc 0 V)) :
    Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (1, 0)
      (rectangleDistribution U V (fun w => f w.2)) = 0 ∧
    Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (0, 1)
      (rectangleDistribution U V (fun w => g w.1)) = 0 :=
  rectangle_independent_derivatives hU hV hf hg

-- The angular off-diagonal connection itself is nonzero away from the equator.
example (H qr pr qell pell : ℝ) :
    nullMetricChristoffel H 2 (3 / 5) (4 / 5) qr pr qell pell 3 2 3 = 4 / 3 ∧
    ricciQuadratic (nullMetricChristoffel H 2 (3 / 5) (4 / 5) qr pr qell pell) 2 3 = 0 ∧
    ricciQuadratic (nullMetricChristoffel H 2 (3 / 5) (4 / 5) qr pr qell pell) 3 2 = 0 := by
  have hh := angular_off_diagonal_contractions (H := H) (r := 2) (s := 3 / 5) (c := 4 / 5)
    (qr := qr) (pr := pr) (qell := qell) (pell := pell) (by norm_num) (by norm_num)
  refine ⟨?_, hh.2.2⟩
  norm_num at hh ⊢
  exact hh.1 3

-- All ten remaining components vanish on the actual low-regularity solution.
example {U V e Λ A B θ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) {c : WaveVector}
    (hzin : zIn = ContinuousMap.const _ c + horizontalPrimitive hU uIn)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hθ : 0 < θ) (hθA : θ + A < Real.pi) :
    let R := ricciDistribution U V A B (coordinateChristoffel hU hV x θ)
    (∀ i j : Fin 2, R (i.castAdd 2) (j.natAdd 2) = 0 ∧ R (j.natAdd 2) (i.castAdd 2) = 0) ∧
      R 2 3 = 0 ∧ R 3 2 = 0 :=
  hx.off_diagonal_ricci_sources hzin A B θ hA hB hθ hθA

end CauchyHorizon.Tests
