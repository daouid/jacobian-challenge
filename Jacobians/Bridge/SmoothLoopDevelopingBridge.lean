/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Jacobians.Bridge.KirovDolbeaultTrace
import Jacobians.RiemannSurface.DevelopingMap
import Jacobians.RiemannSurface.IntegrandIndependence
import Jacobians.Bridge.KirovLineIntegral

/-!
# Smooth Loop ↔ Developing Value Bridge

This file proves that Kirov's `lineIntegral` of a bridged 1-form along a smooth
loop equals our `developingValue` of the corresponding cocycle form.

## Main result

* `lineIntegral_bridgeKDFormEquiv_eq_developingValue`
-/

set_option linter.style.longLine false
set_option linter.style.show false

noncomputable section

namespace Jacobians.Bridge

open scoped Manifold Topology ContDiff
open MeasureTheory Filter intervalIntegral Set
open Jacobians.RiemannSurface

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] [Nonempty Y]

-- ===================================================================
-- Section 1: Smooth loop → Path conversion
-- ===================================================================

/-- Restrict a closed smooth loop `γ : ℝ → Y` to a continuous map on `[0,1]`. -/
def smoothLoopToContinuousMap (γ : ℝ → Y) (hγ : IsClosedSmoothLoop γ) :
    C(unitInterval, Y) :=
  ⟨fun t => γ t, hγ.cont.comp continuous_subtype_val⟩

/-- Restrict a closed smooth loop to a `Path` from `γ 0` to `γ 0`. -/
def smoothLoopToPath (γ : ℝ → Y) (hγ : IsClosedSmoothLoop γ) :
    Path (γ 0) (γ 0) where
  toFun t := γ t
  continuous_toFun := hγ.cont.comp continuous_subtype_val
  source' := rfl
  target' := hγ.closed.symm

omit [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [Nonempty Y] in
@[simp]
theorem smoothLoopToContinuousMap_apply (γ : ℝ → Y) (hγ : IsClosedSmoothLoop γ)
    (t : unitInterval) :
    smoothLoopToContinuousMap γ hγ t = γ t := rfl

theorem smoothLoopToPath_eq_smoothLoopToContinuousMap (γ : ℝ → Y) (hγ : IsClosedSmoothLoop γ) :
    (smoothLoopToPath γ hγ : C(unitInterval, Y)) = smoothLoopToContinuousMap γ hγ := by
  ext t; rfl

-- ===================================================================
-- Section 2: Chart-independence of the integrand (deriv version)
-- ===================================================================

omit [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [Nonempty Y] in
/-- Chart-independence of the 1-form integrand for smooth paths (deriv version). -/
theorem integrand_center_independent_deriv (form : HolomorphicOneForm Y)
    (γ : ℝ → Y) (p q : Y) (r : ℝ)
    (hγ_cont : ContinuousAt γ r)
    (hp : γ r ∈ (extChartAt 𝓘(ℂ) p).source)
    (hq : γ r ∈ (extChartAt 𝓘(ℂ) q).source)
    (hdp : DifferentiableAt ℝ ((extChartAt 𝓘(ℂ) p).toFun ∘ γ) r) :
    form.coeff p ((extChartAt 𝓘(ℂ) p) (γ r)) *
        deriv ((extChartAt 𝓘(ℂ) p).toFun ∘ γ) r =
      form.coeff q ((extChartAt 𝓘(ℂ) q) (γ r)) *
        deriv ((extChartAt 𝓘(ℂ) q).toFun ∘ γ) r := by
  let gp : ℝ → ℂ := fun s => (extChartAt 𝓘(ℂ) p) (γ s)
  let gq : ℝ → ℂ := fun s => (extChartAt 𝓘(ℂ) q) (γ s)
  let z : ℂ := gp r
  let T : ℂ → ℂ := (extChartAt 𝓘(ℂ) q) ∘ (extChartAt 𝓘(ℂ) p).symm
  let d : ℂ := fderiv ℂ T z 1
  have hz : z ∈ (extChartAt 𝓘(ℂ) p).target := by
    simpa [z, gp] using (extChartAt 𝓘(ℂ) p).map_source hp
  have hsymm_z : (extChartAt 𝓘(ℂ) p).symm z = γ r := by
    simpa [z, gp] using (extChartAt 𝓘(ℂ) p).left_inv hp
  have hzq : (extChartAt 𝓘(ℂ) p).symm z ∈ (extChartAt 𝓘(ℂ) q).source := by
    rw [hsymm_z]; exact hq
  have hcoeff : form.coeff p z =
      form.coeff q ((extChartAt 𝓘(ℂ) q) (γ r)) * d := by
    have hcocycle := form.2.2.1 p q z hz hzq
    rw [hsymm_z] at hcocycle
    simpa [HolomorphicOneForm.coeff, T, d] using hcocycle
  have hTdiff : DifferentiableAt ℂ T z :=
    chartTransition_differentiableAt hz hzq
  have hTderiv : HasDerivAt T d (gp r) := by
    simpa [d, z] using hTdiff.hasDerivAt
  have hgp_deriv : HasDerivAt gp (deriv gp r) r := hdp.hasDerivAt
  have hcomp_deriv : HasDerivAt (T ∘ gp) (deriv gp r * d) r := by
    simpa [smul_eq_mul] using hTderiv.scomp (x := r) hgp_deriv
  have hgp_source : ∀ᶠ s in 𝓝 r, γ s ∈ (extChartAt 𝓘(ℂ) p).source :=
    hγ_cont.preimage_mem_nhds ((isOpen_extChartAt_source p).mem_nhds hp)
  have hlocal : gq =ᶠ[𝓝 r] T ∘ gp := by
    filter_upwards [hgp_source] with s hs
    show (chartAt ℂ q) (γ s) =
      (chartAt ℂ q) ((chartAt ℂ p).symm ((chartAt ℂ p) (γ s)))
    rw [(chartAt ℂ p).left_inv (by simpa [extChartAt_source] using hs)]
  have hgq_deriv : deriv gq r = d * deriv gp r := by
    rw [hlocal.deriv_eq, hcomp_deriv.deriv, mul_comm]
  calc form.coeff p z * deriv gp r
      = (form.coeff q ((extChartAt 𝓘(ℂ) q) (γ r)) * d) * deriv gp r := by
        rw [hcoeff]
    _ = form.coeff q ((extChartAt 𝓘(ℂ) q) (γ r)) * (d * deriv gp r) := by
        rw [mul_assoc]
    _ = form.coeff q ((extChartAt 𝓘(ℂ) q) (γ r)) * deriv gq r := by
        rw [hgq_deriv]

-- ===================================================================
-- Section 3: Kirov integrand = fixed-chart integrand for smooth loops
-- ===================================================================

/-- Kirov integrand equals the moving-chart integrand for smooth loops. -/
theorem kirov_integrand_eq_movingChart_of_smoothLoop
    (form : HolomorphicOneForm Y) (γ : ℝ → Y) (hγ : IsClosedSmoothLoop γ)
    (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) 1) :
    (bridgeForm form).toFun (γ t) (pathSpeed γ t) =
      form.coeff (γ t) ((extChartAt 𝓘(ℂ, ℂ) (γ t)) (γ t)) *
        deriv ((extChartAt 𝓘(ℂ, ℂ) (γ t)).toFun ∘ γ) t := by
  set y := γ t
  have hspeed :
      (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) y) y)
          (pathSpeed γ t) =
        fderiv ℝ ((extChartAt 𝓘(ℂ, ℂ) y).toFun ∘ γ) t 1 := by
    exact mfderiv_extChartAt_apply_pathSpeed (x := y) (γ := γ) (t := t)
      hγ.cont.continuousAt (hγ.diff t ht) (mem_extChartAt_source (I := 𝓘(ℂ, ℂ)) y)
  change BridgeForm.rawCLM form y y (pathSpeed γ t) = _
  unfold BridgeForm.rawCLM
  change form.coeff y ((extChartAt 𝓘(ℂ, ℂ) y) y) •
      ((mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) y) y)
        (pathSpeed γ t)) = _
  rw [hspeed]
  change form.coeff y ((extChartAt 𝓘(ℂ, ℂ) y) y) *
      (fderiv ℝ ((extChartAt 𝓘(ℂ, ℂ) y).toFun ∘ γ) t 1) = _
  rw [fderiv_apply_one_eq_deriv]

/-- Kirov integrand equals fixed-chart integrand on a subdivision cell. -/
theorem kirov_integrand_eq_fixedChart_of_smoothLoop
    (form : HolomorphicOneForm Y) (γ : ℝ → Y) (hγ : IsClosedSmoothLoop γ)
    (B : RiemannSurface.PathChartBall Y) (t : ℝ)
    (ht : t ∈ uIcc (0 : ℝ) 1)
    (hsource : γ t ∈ (extChartAt 𝓘(ℂ) B.p).source) :
    (bridgeForm form).toFun (γ t) (pathSpeed γ t) =
      form.coeff B.p ((extChartAt 𝓘(ℂ) B.p) (γ t)) *
        deriv ((extChartAt 𝓘(ℂ) B.p).toFun ∘ γ) t := by
  rw [kirov_integrand_eq_movingChart_of_smoothLoop form γ hγ t ht]
  exact integrand_center_independent_deriv form γ (γ t) B.p t
    (hγ.cont.continuousAt) (mem_extChartAt_source (I := 𝓘(ℂ)) (γ t))
    hsource (hγ.diff t ht)

-- ===================================================================
-- Section 4: Helper lemmas for the per-cell argument
-- ===================================================================

/-- Points of a smooth loop within a subdivision cell lie in the chart source. -/
private theorem smoothLoop_cell_source
    (γ : ℝ → Y) (hγ : IsClosedSmoothLoop γ)
    (S : RiemannSurface.PathChartBallSubdivision (smoothLoopToContinuousMap γ hγ)) (i : Fin S.n)
    (t : ℝ) (ht : t ∈ Set.Icc (S.t i.castSucc : ℝ) (S.t i.succ : ℝ)) :
    γ t ∈ (extChartAt 𝓘(ℂ) (S.cellBall i).p).source := by
  have hu : (⟨t, ⟨(S.t i.castSucc).2.1.trans ht.1, ht.2.trans (S.t i.succ).2.2⟩⟩ : unitInterval) ∈
      Set.Icc (S.t i.castSucc) (S.t i.succ) := ht
  have hset := S.cell_subset i hu
  simpa [smoothLoopToContinuousMap, extChartAt_source] using hset.1

/-- Points of a smooth loop within a subdivision cell map into the coordinate ball. -/
private theorem smoothLoop_cell_coord_mem_ball
    (γ : ℝ → Y) (hγ : IsClosedSmoothLoop γ)
    (S : RiemannSurface.PathChartBallSubdivision (smoothLoopToContinuousMap γ hγ)) (i : Fin S.n)
    (t : ℝ) (ht : t ∈ Set.Icc (S.t i.castSucc : ℝ) (S.t i.succ : ℝ)) :
    (extChartAt 𝓘(ℂ) (S.cellBall i).p) (γ t) ∈
      Metric.ball (S.cellBall i).c (S.cellBall i).r := by
  have hu : (⟨t, ⟨(S.t i.castSucc).2.1.trans ht.1, ht.2.trans (S.t i.succ).2.2⟩⟩ : unitInterval) ∈
      Set.Icc (S.t i.castSucc) (S.t i.succ) := ht
  have hset := S.cell_subset i hu
  simpa [smoothLoopToContinuousMap] using hset.2

/-- Differentiability of the fixed-chart coordinate path for a smooth loop.
    The smooth loop has chart-pullback differentiability at the *moving* chart;
    we compose with the chart transition to get differentiability at the fixed chart. -/
private theorem smoothLoop_fixedChart_differentiableAt
    (γ : ℝ → Y) (hγ : IsClosedSmoothLoop γ)
    (B : PathChartBall Y) (t : ℝ) (ht : t ∈ Set.uIcc (0 : ℝ) 1)
    (hsource : γ t ∈ (extChartAt 𝓘(ℂ) B.p).source) :
    DifferentiableAt ℝ ((extChartAt 𝓘(ℂ) B.p).toFun ∘ γ) t := by
  -- γ is differentiable through chartAt (γ t) by hγ.diff
  have hdiff_moving := hγ.diff t ht
  -- We need to compose with the chart transition: extChartAt B.p = T ∘ extChartAt (γ t)
  -- where T is the chart transition from chart(γ t) to chart(B.p)
  let T : ℂ → ℂ := (extChartAt 𝓘(ℂ) B.p) ∘ (extChartAt 𝓘(ℂ) (γ t)).symm
  have hγt_source : γ t ∈ (extChartAt 𝓘(ℂ) (γ t)).source := mem_extChartAt_source (γ t)
  have hz : (extChartAt 𝓘(ℂ) (γ t)) (γ t) ∈ (extChartAt 𝓘(ℂ) (γ t)).target :=
    (extChartAt 𝓘(ℂ) (γ t)).map_source hγt_source
  have hsymm_z : (extChartAt 𝓘(ℂ) (γ t)).symm ((extChartAt 𝓘(ℂ) (γ t)) (γ t)) = γ t :=
    (extChartAt 𝓘(ℂ) (γ t)).left_inv hγt_source
  have hzq : (extChartAt 𝓘(ℂ) (γ t)).symm ((extChartAt 𝓘(ℂ) (γ t)) (γ t)) ∈
      (extChartAt 𝓘(ℂ) B.p).source := by rw [hsymm_z]; exact hsource
  have hTdiff : DifferentiableAt ℂ T ((extChartAt 𝓘(ℂ) (γ t)) (γ t)) :=
    chartTransition_differentiableAt hz hzq
  have hTdiff_ℝ : DifferentiableAt ℝ T ((extChartAt 𝓘(ℂ) (γ t)) (γ t)) :=
    hTdiff.restrictScalars ℝ
  -- The fixed chart path factors as T ∘ (moving chart path)
  have hlocal : (extChartAt 𝓘(ℂ) B.p).toFun ∘ γ =ᶠ[𝓝 t] T ∘ ((extChartAt 𝓘(ℂ) (γ t)).toFun ∘ γ) := by
    have hgp_source : ∀ᶠ s in 𝓝 t, γ s ∈ (extChartAt 𝓘(ℂ) (γ t)).source :=
      hγ.cont.continuousAt.preimage_mem_nhds ((isOpen_extChartAt_source (γ t)).mem_nhds hγt_source)
    filter_upwards [hgp_source] with s hs
    show (extChartAt 𝓘(ℂ) B.p) (γ s) = T ((extChartAt 𝓘(ℂ) (γ t)) (γ s))
    simp only [T, Function.comp_apply]
    rw [(extChartAt 𝓘(ℂ) (γ t)).left_inv hs]
  exact hlocal.differentiableAt_iff.mpr (hTdiff_ℝ.comp t hdiff_moving)

/-- On one subdivision cell of a smooth loop, the Kirov integrand integral
    equals the developing increment (combining chart independence and FTC). -/
private theorem cell_integral_eq_developingIncrement
    (form : HolomorphicOneForm Y)
    (γ : ℝ → Y) (hγ : IsClosedSmoothLoop γ)
    (S : RiemannSurface.PathChartBallSubdivision (smoothLoopToContinuousMap γ hγ)) (i : Fin S.n)
    (hKI_cell_integrable : IntervalIntegrable
      (fun t => (bridgeForm form).toFun (γ t) (pathSpeed γ t))
      MeasureTheory.volume (S.t i.castSucc : ℝ) (S.t i.succ : ℝ)) :
    ∫ t in (S.t i.castSucc : ℝ)..(S.t i.succ : ℝ),
        (bridgeForm form).toFun (γ t) (pathSpeed γ t) =
      developingIncrement form (smoothLoopToContinuousMap γ hγ) S i := by
  set B := S.cellBall i with hB_def
  set charted : ℝ → ℂ := fun r => (extChartAt 𝓘(ℂ) B.p) (γ r) with hcharted_def
  set fixedIntegrand : ℝ → ℂ :=
    fun r => form.coeff B.p (charted r) * deriv charted r with hfixed_def
  set g : ℂ → ℂ := pathChartBallPrimitive form B with hg_def
  set a : ℝ := (S.t i.castSucc : ℝ) with ha_def
  set b : ℝ := (S.t i.succ : ℝ) with hb_def
  have hab : a ≤ b := S.monotone_t (Fin.castSucc_le_succ i)
  -- (1) Chart independence: pointwise equality of integrands on [a, b]
  have hIntegrand_eq : ∀ r ∈ Set.Icc a b,
      (bridgeForm form).toFun (γ r) (pathSpeed γ r) = fixedIntegrand r := by
    intro r hr
    have hr_uIcc : r ∈ uIcc (0 : ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact ⟨(S.t i.castSucc).2.1.trans hr.1, hr.2.trans (S.t i.succ).2.2⟩
    have hsource : γ r ∈ (extChartAt 𝓘(ℂ) B.p).source :=
      smoothLoop_cell_source γ hγ S i r hr
    exact kirov_integrand_eq_fixedChart_of_smoothLoop form γ hγ B r hr_uIcc hsource
  -- (2) Continuity of g ∘ charted on [a, b]
  have hcharted_cont : ContinuousOn charted (Set.Icc a b) := by
    intro r hr
    have hsource : γ r ∈ (extChartAt 𝓘(ℂ) B.p).source :=
      smoothLoop_cell_source γ hγ S i r hr
    exact ((continuousOn_extChartAt (I := 𝓘(ℂ)) B.p).continuousAt
      ((isOpen_extChartAt_source B.p).mem_nhds hsource)).comp_continuousWithinAt
      hγ.cont.continuousAt.continuousWithinAt
  have hprimPath_cont : ContinuousOn (fun r : ℝ => g (charted r)) (Set.Icc a b) := by
    intro r hr
    have hball : charted r ∈ Metric.ball B.c B.r :=
      smoothLoop_cell_coord_mem_ball γ hγ S i r hr
    exact ((pathChartBallPrimitive_hasDerivAt form B (charted r) hball).continuousAt).comp_continuousWithinAt
      (hcharted_cont r hr)
  -- (3) FTC: ∫ fixedIntegrand = g(charted b) - g(charted a)
  have hFTC_deriv : ∀ r ∈ Set.Ioo a b,
      HasDerivWithinAt (fun u : ℝ => g (charted u)) (fixedIntegrand r) (Set.Ioi r) r := by
    intro r hr
    have hr_Icc : r ∈ Set.Icc a b := ⟨hr.1.le, hr.2.le⟩
    have hball : charted r ∈ Metric.ball B.c B.r :=
      smoothLoop_cell_coord_mem_ball γ hγ S i r hr_Icc
    have hprim : HasDerivAt g (form.coeff B.p (charted r)) (charted r) :=
      pathChartBallPrimitive_hasDerivAt form B (charted r) hball
    have hr_uIcc : r ∈ uIcc (0 : ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact ⟨(S.t i.castSucc).2.1.trans hr.1.le, hr.2.le.trans (S.t i.succ).2.2⟩
    have hsource : γ r ∈ (extChartAt 𝓘(ℂ) B.p).source :=
      smoothLoop_cell_source γ hγ S i r hr_Icc
    have hchart_diff : DifferentiableAt ℝ charted r := by
      exact smoothLoop_fixedChart_differentiableAt γ hγ B r hr_uIcc hsource
    have hchart_hasDeriv : HasDerivAt charted (deriv charted r) r := hchart_diff.hasDerivAt
    have hcomp : HasDerivAt (fun u : ℝ => g (charted u))
        (deriv charted r * form.coeff B.p (charted r)) r := by
      simpa [Function.comp_def, smul_eq_mul] using
        hprim.scomp (x := r) hchart_hasDeriv
    simpa [fixedIntegrand, mul_comm] using hcomp.hasDerivWithinAt
  have hfixed_integrable : IntervalIntegrable fixedIntegrand MeasureTheory.volume a b :=
    hKI_cell_integrable.congr (fun r hr => by
      rw [Set.mem_uIoc] at hr
      exact hIntegrand_eq r (by rcases hr with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩))
  have hFTC : ∫ r in a..b, fixedIntegrand r =
      (fun r : ℝ => g (charted r)) b - (fun r : ℝ => g (charted r)) a := by
    exact intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
      (f := fun r : ℝ => g (charted r)) (f' := fixedIntegrand) hab
      hprimPath_cont hFTC_deriv hfixed_integrable
  -- (4) Relate to developingIncrement
  have hInc : developingIncrement form (smoothLoopToContinuousMap γ hγ) S i =
      g (charted b) - g (charted a) := by
    simp [developingIncrement, smoothLoopToContinuousMap, charted, g, B, a, b]
  -- (5) Combine: ∫ kirovIntegrand = ∫ fixedIntegrand = g(b) - g(a) = increment
  calc ∫ t in a..b, (bridgeForm form).toFun (γ t) (pathSpeed γ t)
      = ∫ t in a..b, fixedIntegrand t := by
        apply intervalIntegral.integral_congr
        intro r hr
        rw [Set.uIcc_of_le hab] at hr
        exact hIntegrand_eq r hr
    _ = g (charted b) - g (charted a) := hFTC
    _ = developingIncrement form (smoothLoopToContinuousMap γ hγ) S i := hInc.symm

-- ===================================================================
-- Section 5: The main bridge theorem
-- ===================================================================

/-- The main bridge: Kirov's line integral of a bridged holomorphic 1-form
along a smooth loop equals our developing value. Both compute
"∮_γ ω" via different formalizations of the contour integral. -/
theorem lineIntegral_bridgeKDFormEquiv_eq_developingValue
    (x₀ : Y) (form : HolomorphicOneForm Y)
    (γ : ℝ → Y) (hγ : IsClosedSmoothLoop γ) :
    Jacobians.Vendor.Kirov.lineIntegral (bridgeKDFormEquiv form) γ =
      developingValue x₀ form (smoothLoopToContinuousMap γ hγ) := by
  -- Both sides compute the contour integral ∮_γ form. On each chart-ball
  -- subdivision cell, the Kirov integrand equals our fixed-chart integrand
  -- (by chart independence), and the fixed-chart integral telescopes to the
  -- developing increment (by FTC). Summing over cells yields the result.
  --
  -- Core sub-arguments:
  -- 1. kirov_integrand_eq_fixedChart_of_smoothLoop (chart independence)
  -- 2. pathChartBallPrimitive_hasDerivAt (FTC primitive)
  -- 3. developingValue_eq_developingValueOfSubdivision (subdivision independence)
  -- 4. sum_integral_adjacent_intervals (integral telescoping)
  -- Abbreviations
  set γc := smoothLoopToContinuousMap γ hγ with hγc_def
  set S := chosenPathChartBallSubdivision γc with hS_def
  -- The Kirov integrand function
  set kirovIntegrand : ℝ → ℂ :=
    fun t => (bridgeKDFormEquiv form).toFun (γ t) (pathSpeed γ t) with hKI_def
  -- Step 1: LHS = ∫₀¹ kirovIntegrand
  have hLHS : Jacobians.Vendor.Kirov.lineIntegral (bridgeKDFormEquiv form) γ =
      ∫ t in (0 : ℝ)..1, kirovIntegrand t := by
    rfl
  -- Step 2: RHS = Σᵢ developingIncrement
  have hRHS : developingValue x₀ form γc =
      ∑ i : Fin S.n, developingIncrement form γc S i := by
    rw [developingValue_eq_developingValueOfSubdivision x₀ form γc S]
    rfl
  -- Step 3: bridgeKDFormEquiv form = bridgeForm form (as sections)
  have hKD_eq_bridge : (bridgeKDFormEquiv form).toFun = (bridgeForm form).toFun := by
    rfl
  -- Step 4: Integrability of the Kirov integrand on [0,1]
  have hKI_integrable : IntervalIntegrable kirovIntegrand MeasureTheory.volume (0 : ℝ) 1 := by
    rw [hKI_def, hKD_eq_bridge]
    exact intervalIntegrable_form_pathSpeed_of_velContinuous
      (bridgeForm form) γ hγ.velCont
  -- Step 5: Per-cell integrability
  have hKI_cell_integrable : ∀ i : Fin S.n,
      IntervalIntegrable kirovIntegrand MeasureTheory.volume
        (S.t i.castSucc : ℝ) (S.t i.succ : ℝ) := by
    intro i
    exact hKI_integrable.mono_set (Set.uIcc_subset_uIcc
      (Set.mem_uIcc_of_le (S.t i.castSucc).2.1 (S.t i.castSucc).2.2)
      (Set.mem_uIcc_of_le (S.t i.succ).2.1 (S.t i.succ).2.2))
  -- Step 6: Telescope: ∫₀¹ kirovIntegrand = Σ ∫_{cell i} kirovIntegrand
  have hTelescope : ∫ t in (0 : ℝ)..1, kirovIntegrand t =
      ∑ i : Fin S.n,
        ∫ t in (S.t i.castSucc : ℝ)..(S.t i.succ : ℝ), kirovIntegrand t := by
    let a : ℕ → ℝ := fun k =>
      if h : k < S.n + 1 then (S.t ⟨k, h⟩ : ℝ) else 0
    have ha0 : a 0 = 0 := by
      have h0 : 0 < S.n + 1 := Nat.succ_pos S.n
      simpa [a, h0] using congrArg Subtype.val S.zero_eq
    have haN : a S.n = 1 := by
      have hN : S.n < S.n + 1 := Nat.lt_succ_self S.n
      have hfin : (⟨S.n, hN⟩ : Fin (S.n + 1)) = Fin.last S.n := by
        ext; simp [Fin.last]
      calc a S.n = (S.t ⟨S.n, hN⟩ : ℝ) := by simp [a]
        _ = (S.t (Fin.last S.n) : ℝ) := by rw [hfin]
        _ = 1 := by simpa using congrArg Subtype.val S.one_eq
    have hsum : ∑ k ∈ Finset.range S.n,
        ∫ t in (a k)..(a (k + 1)), kirovIntegrand t =
          ∫ t in (a 0)..(a S.n), kirovIntegrand t := by
      refine intervalIntegral.sum_integral_adjacent_intervals (a := a) (n := S.n) ?_
      intro k hk
      have hk_le : k ≤ S.n := Nat.le_of_lt hk
      simp only [a, show k < S.n + 1 from by omega,
        show k + 1 < S.n + 1 from by omega, dite_true]
      exact hKI_cell_integrable ⟨k, hk⟩
    rw [ha0, haN] at hsum
    rw [← hsum]
    rw [Finset.sum_fin_eq_sum_range]
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hklt : k < S.n := by simpa using hk
    have hk_le : k ≤ S.n := Nat.le_of_lt hklt
    simp [a, hklt, hk_le]
  -- Step 7: Per-cell chart independence + FTC
  -- On each cell i, the Kirov integrand equals the fixed-chart integrand
  -- and the fixed-chart integral gives the developing increment by FTC.
  have hCell : ∀ i : Fin S.n,
      ∫ t in (S.t i.castSucc : ℝ)..(S.t i.succ : ℝ), kirovIntegrand t =
        developingIncrement form γc S i := by
    intro i
    -- kirovIntegrand = bridgeForm integrand (definitional)
    show ∫ t in (S.t i.castSucc : ℝ)..(S.t i.succ : ℝ),
        (bridgeKDFormEquiv form).toFun (γ t) (pathSpeed γ t) =
      developingIncrement form γc S i
    -- bridgeKDFormEquiv = bridgeForm on toFun
    simp only [show (bridgeKDFormEquiv form).toFun = (bridgeForm form).toFun from rfl]
    exact cell_integral_eq_developingIncrement form γ hγ S i
      (hKI_cell_integrable i)
  -- Combine
  rw [hLHS, hTelescope, hRHS]
  exact Finset.sum_congr rfl (fun i _ => hCell i)

end Jacobians.Bridge
