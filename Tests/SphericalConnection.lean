import CauchyHorizon.Reduced.SphericalConnection
import CauchyHorizon.Reduced.RegularCrossing

open CauchyHorizon Set MeasureTheory
open scoped Manifold ContDiff Matrix

example : angularJacobian (ContinuousLinearMap.id ℝ (ℝ × ℝ)) = 1 := by
  apply Matrix.ext_iff_mulVec.2
  intro a
  rw [angularJacobian_mulVec, Matrix.one_mulVec]
  ext i
  fin_cases i <;> rfl

-- The coordinate Hessian has no derivative in either unchanged null direction.
example (Q : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) :
    angularJacobianDerivative Q 0 = 0 ∧ angularJacobianDerivative Q 1 = 0 := by
  have h0 : Q (0, 0) = 0 := map_zero Q
  constructor <;> ext k j <;> fin_cases k <;>
    simp [angularJacobianDerivative, angularVectorVariation, Pi.single_apply,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, h0]

example {U V e Λ : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V}
    {zIn : C(Icc 0 U, WaveVector)} {vOut : C(Icc 0 V, WaveVector)}
    {uIn : Lp WaveVector 2 (volume.restrict (Icc 0 U))} {x : WaveState U V}
    (hx : IsWaveIntegral hU hV e Λ zIn vOut uIn x) {z₀ : WaveVector}
    (hzin : zIn = ContinuousMap.const _ z₀ + horizontalPrimitive hU uIn) :
    HasL2CoordinateConnection hU hV x ∧ HasSphericalConnectionTransition hU hV x :=
  ⟨hx.coordinate_connection hzin, hx.spherical_connection_transition⟩

-- Check the old and new coordinate order, inverse Jacobian, and inhomogeneous Hessian term.
example {U V : ℝ} {hU : 0 ≤ U} {hV : 0 ≤ V} {x : WaveState U V}
    (hx : HasSphericalConnectionTransition hU hV x)
    (A B : SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient) (c d : OpenPartialHomeomorph UnitSphere (ℝ × ℝ))
    (hc : EqOn c.symm (rotatedSphericalMap A) c.target)
    (hd : EqOn d.symm (rotatedSphericalMap B) d.target)
    (hcf : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ω c c.source)
    (hci : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ω c.symm c.target)
    (hdf : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ω d d.source)
    (hdi : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ω d.symm d.target)
    (v y α β : ℝ × ℝ) (hy : y ∈ (c.symm.trans d).source)
    (hs : Real.sin y.1 ≠ 0) (ht : Real.sin ((c.symm.trans d) y).1 ≠ 0) (k i j : Fin 4) :
    let t := c.symm.trans d
    let J := angularJacobian (fderiv ℝ t y)
    let K := angularJacobian (fderiv ℝ t.symm (t y))
    let dJ := angularJacobianDerivative (fderiv ℝ (fderiv ℝ t) y)
    coordinateChristoffel hU hV x α.1 (v, y - α) k i j =
      ∑ l, K k l * ((∑ m, (∑ n, J n i * coordinateChristoffel hU hV x β.1 (v, t y - β) l n m) * J m j) +
        dJ i l j) := by
  have h := hx A B c d hc hd hcf hci hdf hdi v y α β hy hs ht
  simpa only [connectionChange, Matrix.mul_apply, Matrix.add_apply, Matrix.sum_apply,
    Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] using congrFun (congrFun (congrFun h k) i) j

-- Retention is on the original crossing state, alongside its local L2 connection.
example {U ε e Λ T₀ u₀ : ℝ} (hε : 0 ≤ ε) (hεU : ε ≤ U)
    {X : (S : Ici (0 : ℝ)) → WaveState U S} {χ : ℝ → ℝ}
    {Z : C(Icc ε U, WaveVector)} {O : C(Icc ε U, ℝ)}
    {D : ℝ → C(Icc ε U, WaveVector)} {Dh : C(Icc ε U, WaveVector)}
    (hcross : HasRegularCrossingSolution hε hεU e Λ X χ Z O D Dh T₀ u₀) :
    ∃ L W : ℝ, ∃ hL : 0 ≤ L, ∃ hW : 0 ≤ W, ∃ y : WaveState W L,
      (∀ t s, 0 < y.1 t s 0) ∧ HasL2CoordinateConnection hW hL y ∧
        HasSphericalConnectionTransition hW hL y := by
  obtain ⟨_ua, L, T, b, _hea, _ham, _hmr, _hrU, _hT₀, _hT, _hn, _hb,
    hL, hW, _zIn, _vOut, _uIn, y, _hy, _hprim, _hpast, _hfuture, _hout, _hxin, _hbottom,
    hr, _hmatch, _hvelocity, _hc, _hi, _hweak, _hdistribution, _hL2, _hmetric, _hcoord, hconnection,
    _hRicci, _hsource, _hmixed, _hangular, _hoffdiag, _hmaxwell, _heinstein, _hscalar, _hsphere,
    htransition, _rest⟩ := hcross
  exact ⟨L, _, hL, hW, y, hr, hconnection, htransition⟩
