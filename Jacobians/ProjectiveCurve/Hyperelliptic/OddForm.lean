import Jacobians.ProjectiveCurve.Hyperelliptic.Basic
import Jacobians.ProjectiveCurve.Hyperelliptic.OddAtlas
import Jacobians.ProjectiveCurve.Hyperelliptic.AffineForm
import Jacobians.RiemannSurface.OneForm
import Jacobians.Bridge.KirovHolomorphic
import Jacobians.GeneralResults.ChartTransition

namespace Jacobians.ProjectiveCurve.HyperellipticOdd

open scoped Manifold ContDiff
open Jacobians.RiemannSurface
open Polynomial

variable {H : HyperellipticData} {h : Odd H.f.natDegree}

/-- Custom induction principle for `HyperellipticOdd H h` to avoid unfolding it to
`OnePoint (HyperellipticAffine H)` during proofs. This ensures typeclass search
can find the `ChartedSpace` and `IsManifold` instances. -/
@[elab_as_elim]
protected theorem rec {C : HyperellipticOdd H h → Prop}
    (infty_val : C infty)
    (coe_val : ∀ (a : HyperellipticAffine H), C (a : HyperellipticOdd H h)) :
    ∀ (p : HyperellipticOdd H h), C p := by
  intro p
  change OnePoint (HyperellipticAffine H) at p
  induction p with
  | infty =>
    change C infty
    exact infty_val
  | coe a =>
    change C (coe a)
    exact coe_val a

/-- The unified coefficient family for `g(x) dx / y` on the odd curve `HyperellipticOdd H h`. -/
noncomputable def hyperellipticOddCoeff (g : Polynomial ℂ) (p : HyperellipticOdd H h) :
    ℂ → ℂ := fun z => by
  classical
  let p' : OnePoint (HyperellipticAffine H) := p
  exact p'.elim
    (if hz : z ∈ (infinityChart H h).target then
       if z = 0 then
         -2 * g.coeff (H.genus - 1) / H.f.leadingCoeff
       else
         let x := (infinityInverseMap H h z).val.1
         2 * g.eval x * x ^ (H.genus + 2) /
           (x * (Polynomial.derivative H.f).eval x - (2 * H.genus + 2) * H.f.eval x)
     else 0)
    (fun a => HyperellipticAffine.hyperellipticAffineCoeff g a z)

theorem hyperellipticOddCoeff_zero :
    hyperellipticOddCoeff (H := H) (h := h) 0 = 0 := by
  funext p z
  unfold hyperellipticOddCoeff
  induction p using HyperellipticOdd.rec with
  | infty_val =>
    dsimp [infty]
    split_ifs with hz hz0
    · simp only [mul_zero, zero_div]
    · simp only [Polynomial.eval_zero, mul_zero, zero_mul, zero_div]
    · rfl
  | coe_val a =>
    rw [HyperellipticAffine.hyperellipticAffineCoeff_zero]
    rfl

theorem hyperellipticOddCoeff_add (g g' : Polynomial ℂ) :
    hyperellipticOddCoeff (H := H) (h := h) (g + g') =
      hyperellipticOddCoeff g + hyperellipticOddCoeff g' := by
  funext p z
  unfold hyperellipticOddCoeff
  induction p using HyperellipticOdd.rec with
  | infty_val =>
    simp only [Pi.add_apply]
    dsimp [infty]
    split_ifs with hz hz0
    · simp only [Polynomial.coeff_add]
      ring
    · simp only [Polynomial.eval_add]
      ring
    · ring
  | coe_val a =>
    rw [HyperellipticAffine.hyperellipticAffineCoeff_add g g']
    rfl

theorem hyperellipticOddCoeff_smul (c : ℂ) (g : Polynomial ℂ) :
    hyperellipticOddCoeff (H := H) (h := h) (c • g) =
      c • hyperellipticOddCoeff g := by
  funext p z
  unfold hyperellipticOddCoeff
  induction p using HyperellipticOdd.rec with
  | infty_val =>
    simp only [Pi.smul_apply, smul_eq_mul]
    dsimp [infty]
    split_ifs with hz hz0
    · simp only [Polynomial.coeff_smul, smul_eq_mul]
      ring
    · simp only [Polynomial.eval_smul, smul_eq_mul]
      ring
    · ring
  | coe_val a =>
    rw [HyperellipticAffine.hyperellipticAffineCoeff_smul c g]
    rfl

/-- The coefficient family is zero off each chart target. -/
theorem hyperellipticOddCoeff_isZeroOffChartTarget (g : Polynomial ℂ) :
    IsZeroOffChartTarget (HyperellipticOdd H h)
      (hyperellipticOddCoeff (H := H) (h := h) g) := by
  intro p z hz
  induction p using HyperellipticOdd.rec with
  | infty_val =>
    unfold hyperellipticOddCoeff
    have hExt : (extChartAt 𝓘(ℂ, ℂ) (infty : HyperellipticOdd H h)).target =
        (infinityChart H h).target := by
      change Set.univ ∩ (chartAt (infty : HyperellipticOdd H h)).target =
        (infinityChart H h).target
      rw [Set.univ_inter]
      rfl
    rw [hExt] at hz
    dsimp [infty] at *
    split_ifs
    rfl
  | coe_val a =>
    unfold hyperellipticOddCoeff
    have hExt_lift : (extChartAt 𝓘(ℂ, ℂ) (a : HyperellipticOdd H h)).target =
        (extChartAt 𝓘(ℂ, ℂ) a).target := by
      change Set.univ ∩ (chartAt (a : HyperellipticOdd H h)).target =
        Set.univ ∩ (ChartedSpace.chartAt a).target
      dsimp [coe, HyperellipticOdd.coe]
      rw [affineLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target]
    rw [hExt_lift] at hz
    dsimp [coe] at *
    exact HyperellipticAffine.hyperellipticAffineCoeff_isZeroOffChartTarget g a z hz

/-- The coefficient family is analytic on the affine charts. -/
theorem hyperellipticOddCoeff_analyticOn_affineLift
    (g : Polynomial ℂ) (a : HyperellipticAffine H) :
    AnalyticOn ℂ (hyperellipticOddCoeff (h := h) g (coe a))
      (affineLiftChart (h := h) a).target := by
  have hCoeff : hyperellipticOddCoeff (h := h) g (coe a) =
      HyperellipticAffine.hyperellipticAffineCoeff g a := rfl
  rw [hCoeff]
  have hLift : (affineLiftChart (h := h) a).target = (extChartAt 𝓘(ℂ, ℂ) a).target := by
    change (affineLiftChart (h := h) a).target = Set.univ ∩ (ChartedSpace.chartAt a).target
    rw [affineLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target]
    rw [Set.univ_inter]
  rw [hLift]
  exact HyperellipticAffine.hyperellipticAffineCoeff_isHolomorphicOneFormCoeff g a

/-- Same-summand cocycle equation holds on overlaps of affine charts. -/
theorem hyperellipticOddCoeff_cocycle_coe_coe (g : Polynomial ℂ) (p q : HyperellipticAffine H)
    {z : ℂ} (hz : z ∈ (affineLiftChart (h := h) p).target)
    (hsrc : (affineLiftChart (h := h) p).symm z ∈ (affineLiftChart (h := h) q).source) :
    hyperellipticOddCoeff (h := h) g (coe p) z =
      hyperellipticOddCoeff (h := h) g (coe q) ((affineLiftChart (h := h) q)
        ((affineLiftChart (h := h) p).symm z)) *
        (fderiv ℂ ((affineLiftChart (h := h) q) ∘ (affineLiftChart (h := h) p).symm) z 1) := by
  have hp : hyperellipticOddCoeff (h := h) g (coe p) =
      HyperellipticAffine.hyperellipticAffineCoeff g p := rfl
  have hq : hyperellipticOddCoeff (h := h) g (coe q) =
      HyperellipticAffine.hyperellipticAffineCoeff g q := rfl
  rw [hp, hq]
  have hExt_target : (extChartAt 𝓘(ℂ, ℂ) p).target = (affineLiftChart (h := h) p).target := by
    change Set.univ ∩ (ChartedSpace.chartAt p).target = (affineLiftChart (h := h) p).target
    rw [Set.univ_inter]
    rw [affineLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target]
  have hz_aff : z ∈ (extChartAt 𝓘(ℂ, ℂ) p).target := by
    rw [hExt_target]; exact hz
  have hsrc_aff : (extChartAt 𝓘(ℂ, ℂ) p).symm z ∈ (extChartAt 𝓘(ℂ, ℂ) q).source := by
    rw [extChartAt_source 𝓘(ℂ, ℂ) q]
    have hSymm : (extChartAt 𝓘(ℂ, ℂ) p).symm z =
        (ChartedSpace.chartAt p : OpenPartialHomeomorph (HyperellipticAffine H) ℂ).symm z := rfl
    rw [hSymm]
    have hsrc' := hsrc
    simp only [affineLiftChart, OpenPartialHomeomorph.lift_openEmbedding_symm,
      OpenPartialHomeomorph.lift_openEmbedding_source] at hsrc'
    obtain ⟨w, hw, heq⟩ := hsrc'
    have heq' : w = (ChartedSpace.chartAt p : OpenPartialHomeomorph
      (HyperellipticAffine H) ℂ).symm z := by
      exact OnePoint.coe_injective heq
    rw [← heq']
    exact hw
  have hLift_apply : (affineLiftChart (h := h) q) ((affineLiftChart (h := h) p).symm z) =
      (ChartedSpace.chartAt q : OpenPartialHomeomorph (HyperellipticAffine H) ℂ)
        ((ChartedSpace.chartAt p : OpenPartialHomeomorph (HyperellipticAffine H) ℂ).symm z) := by
    simp only [affineLiftChart, OpenPartialHomeomorph.lift_openEmbedding_symm,
      Function.comp_apply, OpenPartialHomeomorph.lift_openEmbedding_apply]
  rw [hLift_apply]
  have hFderiv : fderiv ℂ ((affineLiftChart (h := h) q) ∘ (affineLiftChart (h := h) p).symm) z =
      fderiv ℂ ((ChartedSpace.chartAt q : OpenPartialHomeomorph (HyperellipticAffine H) ℂ) ∘
        (ChartedSpace.chartAt p : OpenPartialHomeomorph (HyperellipticAffine H) ℂ).symm) z := by
    refine Filter.EventuallyEq.fderiv_eq
      (Filter.eventuallyEq_of_mem (s := (affineLiftChart (h := h) p).target) ?_ ?_)
    · exact (affineLiftChart (h := h) p).open_target.mem_nhds hz
    · intro w hw
      simp only [Function.comp_apply, affineLiftChart,
        OpenPartialHomeomorph.lift_openEmbedding_symm,
        OpenPartialHomeomorph.lift_openEmbedding_apply]
  rw [hFderiv]
  exact HyperellipticAffine.hyperellipticAffineCoeff_satisfiesCotangentCocycle
    g p q z hz_aff hsrc_aff

lemma coeff_X_mul_derivative_eq (p : Polynomial ℂ) (i : ℕ) :
    (X * p.derivative).coeff i = (i : ℂ) * p.coeff i := by
  cases i
  · simp
  · simp [coeff_X_mul, coeff_derivative, Nat.cast_succ, mul_comm]

lemma poly_rev_id (f : Polynomial ℂ) (N : ℕ) (hN : f.natDegree = N) :
    X * f.derivative - C (N + 1 : ℂ) * f =
      - reflect N (f.reverse + X * f.reverse.derivative) := by
  ext i
  rw [coeff_sub, coeff_C_mul, coeff_neg, coeff_reflect]
  rw [coeff_add, coeff_X_mul_derivative_eq, coeff_X_mul_derivative_eq]
  simp only [coeff_reverse, hN]
  dsimp [revAt]
  by_cases h1 : i ≤ N
  · have h2 : N - i ≤ N := by omega
    simp only [h1, h2, ite_true]
    have h_eq : N - (N - i) = i := by omega
    simp only [h_eq]
    rw [Nat.cast_sub h1]
    ring
  · simp only [h1, ite_false]
    have h_zero : f.coeff i = 0 := coeff_eq_zero_of_natDegree_lt (by linarith)
    simp [h_zero]

lemma natDegree_le_N (f : Polynomial ℂ) (N : ℕ) (hN : f.natDegree = N) :
    (f.reverse + X * f.reverse.derivative).natDegree ≤ N := by
  have h1 : f.reverse.natDegree ≤ N := by
    calc f.reverse.natDegree ≤ f.natDegree := reverse_natDegree_le f
      _ = N := hN
  have h2 : (X * f.reverse.derivative).natDegree ≤ N := by
    by_cases h0 : f.reverse.natDegree = 0
    · have hc : f.reverse = C (f.reverse.coeff 0) := eq_C_of_natDegree_eq_zero h0
      have hd : f.reverse.derivative = 0 := by
        rw [hc, derivative_C]
      simp [hd]
    · calc (X * f.reverse.derivative).natDegree ≤ X.natDegree + f.reverse.derivative.natDegree := natDegree_mul_le
        _ = 1 + f.reverse.derivative.natDegree := by rw [natDegree_X]
        _ ≤ 1 + (f.reverse.natDegree - 1) := by
          have hd := natDegree_derivative_le f.reverse
          omega
        _ ≤ N := by omega
  calc (f.reverse + X * f.reverse.derivative).natDegree ≤ max f.reverse.natDegree (X * f.reverse.derivative).natDegree := natDegree_add_le _ _
    _ ≤ N := max_le h1 h2

lemma eval_reflect_eq (p : Polynomial ℂ) (N : ℕ) (hp : p.natDegree ≤ N) (W : ℂ) (hW : W ≠ 0) :
    (reflect N p).eval (W⁻¹ ^ 2) = W⁻¹ ^ (2 * N) * p.eval (W ^ 2) := by
  letI : Invertible (W ^ 2) := invertibleOfNonzero (pow_ne_zero 2 hW)
  have h1 := eval₂_reflect_mul_pow (RingHom.id ℂ) (W ^ 2) N p hp
  simp only [eval₂_id] at h1
  have h2 : ⅟(W ^ 2) = W⁻¹ ^ 2 := by
    simp [invOf_eq_inv, ← inv_pow]
  rw [h2] at h1
  have h3 : (W ^ 2) ^ N = W ^ (2 * N) := by ring
  rw [h3] at h1
  have hz : W ^ (2 * N) ≠ 0 := pow_ne_zero _ hW
  have h4 := congr_arg (fun y => y * (W ^ (2 * N))⁻¹) h1
  dsimp at h4
  rw [mul_assoc, mul_inv_cancel₀ hz, mul_one] at h4
  rw [h4]
  simp [inv_pow]
  ring

lemma x_fderiv_sub_f_eq {H : HyperellipticData} (hOdd : Odd H.f.natDegree) (W : ℂ) (hW : W ≠ 0) :
    let x := W⁻¹ ^ 2
    x * H.f.derivative.eval x - (2 * H.genus + 2) * H.f.eval x =
      - W⁻¹ ^ (4 * H.genus + 2) * (H.f.reverse.eval (W ^ 2) + W ^ 2 * H.f.reverse.derivative.eval (W ^ 2)) := by
  intro x
  have h_deg : 2 * H.genus + 2 = H.f.natDegree + 1 := by
    obtain ⟨k, hk⟩ := hOdd
    have h1 : H.f.natDegree = 2 * k + 1 := hk
    have h2 : H.genus = k := by
      dsimp [HyperellipticData.genus]
      omega
    omega
  have h_degC : (2 * H.genus + 2 : ℂ) = (H.f.natDegree + 1 : ℂ) := by
    exact_mod_cast h_deg
  rw [h_degC]
  have H_id := poly_rev_id H.f H.f.natDegree rfl
  have H_eval := congr_arg (fun P : Polynomial ℂ => P.eval x) H_id
  dsimp at H_eval
  rw [eval_sub, eval_mul, eval_X, eval_mul, eval_C] at H_eval
  rw [H_eval]
  have H_reflect := eval_reflect_eq (H.f.reverse + X * H.f.reverse.derivative) H.f.natDegree
    (natDegree_le_N H.f H.f.natDegree rfl) W hW
  rw [eval_neg]
  rw [H_reflect]
  have h_pow : 2 * H.f.natDegree = 4 * H.genus + 2 := by
    obtain ⟨k, hk⟩ := hOdd
    have h1 : H.f.natDegree = 2 * k + 1 := hk
    have h2 : H.genus = k := by
      dsimp [HyperellipticData.genus]
      omega
    omega
  rw [h_pow]
  rw [eval_add, eval_mul, eval_X]
  ring

/-- **Key identity for the infinity-to-affine cocycle**.

At a point `z ≠ 0` in the infinity chart target, the derivative of the
chart transition `z ↦ w(z)⁻¹ ^ 2` (where `w = tLocalHomeomorph.symm z`)
satisfies:
```
fderiv(z ↦ w(z)⁻²)(z)(1) =
  2 * (w⁻²)^(g+2) * y / (w⁻² * f'(w⁻²) - (2g+2) * f(w⁻²))
```
where `y = squareLocalHomeomorph.symm(f.eval(w⁻²))` is the y-branch.

Mathematically this is the identity `dx/dt = 2x^(g+2) * y / (x*f'(x) - (2g+2)*f(x))`
at infinity, where `t` is the uniformizer `y/x^(g+1)` and `x = w⁻²`.

Proof requires:
1. `HasDerivAt` for `tLocalHomeomorph.symm` at `z` via the IFT
2. Chain rule for `z ↦ w(z)⁻¹ ^ 2 = w(z)⁻²`
3. The relationship `t'(w) = S(w²) + 2w²S'(w²)` from the
   definition `t(w) = w * S(w²)`
4. Connection between `S(w²)` and the square root branch `y`
-/
theorem infinity_transition_deriv_identity
    (a : HyperellipticAffine H)
    (hpY : a ∈ HyperellipticAffine.smoothLocusY H)
    {z : ℂ}
    (hzt : z ∈ (InfinityInverse.tLocalHomeomorph H).target)
    (hzne : z ≠ 0)
    (hInTarget : ((InfinityInverse.tLocalHomeomorph H).symm
      z)⁻¹ ^ 2 ∈
        ((HyperellipticAffine.affineChartProjX (H := H)
          a hpY) :
            OpenPartialHomeomorph
              (HyperellipticAffine H) ℂ).target) :
    let w := (InfinityInverse.tLocalHomeomorph H).symm z
    (fderiv ℂ
      (fun z => ((InfinityInverse.tLocalHomeomorph H).symm
        z)⁻¹ ^ 2) z) 1 =
    2 * (w⁻¹ ^ 2) ^ (H.genus + 2) *
      ((HyperellipticAffine.squareLocalHomeomorph
          (H := H) a hpY).symm
        (H.f.eval (w⁻¹ ^ 2))) /
      (w⁻¹ ^ 2 *
        (Polynomial.derivative H.f).eval (w⁻¹ ^ 2) -
        (2 * H.genus + 2) *
          H.f.eval (w⁻¹ ^ 2)) := by
  sorry

theorem hyperellipticOddCoeff_analyticOn_infinityChart
    (g : Polynomial ℂ) (hDeg : g.natDegree < (H.f.natDegree - 1) / 2) :
    AnalyticOn ℂ (hyperellipticOddCoeff (h := h) g (infty : HyperellipticOdd H h))
      (infinityChart H h).target := by
  sorry

theorem hyperellipticOddCoeff_isHolomorphicOneFormCoeff
    (g : Polynomial ℂ) (hDeg : g.natDegree < (H.f.natDegree - 1) / 2) :
    IsHolomorphicOneFormCoeff (HyperellipticOdd H h)
      (hyperellipticOddCoeff (H := H) (h := h) g) := by
  intro p
  induction p using HyperellipticOdd.rec with
  | infty_val =>
    have hExt_target : (extChartAt 𝓘(ℂ, ℂ) (infty : HyperellipticOdd H h)).target =
        (infinityChart H h).target := by
      change Set.univ ∩ (chartAt (infty : HyperellipticOdd H h)).target = (infinityChart H h).target
      rw [Set.univ_inter]
      rfl
    rw [hExt_target]
    exact hyperellipticOddCoeff_analyticOn_infinityChart g hDeg
  | coe_val a =>
    have hExt_target : (extChartAt 𝓘(ℂ, ℂ) (a : HyperellipticOdd H h)).target =
        (affineLiftChart (h := h) a).target := by
      change Set.univ ∩ (chartAt (a : HyperellipticOdd H h)).target = (affineLiftChart (h := h) a).target
      rw [Set.univ_inter]
      rfl
    rw [hExt_target]
    exact hyperellipticOddCoeff_analyticOn_affineLift g a

theorem hyperellipticOddCoeff_cocycle_infty_coe (g : Polynomial ℂ) (a : HyperellipticAffine H)
    {z : ℂ} (hz : z ∈ (extChartAt 𝓘(ℂ, ℂ) (infty : HyperellipticOdd H h)).target)
    (hsrc : (extChartAt 𝓘(ℂ, ℂ) (infty : HyperellipticOdd H h)).symm z ∈
      (extChartAt 𝓘(ℂ, ℂ) (a : HyperellipticOdd H h)).source) :
    hyperellipticOddCoeff (h := h) g infty z =
      hyperellipticOddCoeff (h := h) g (coe a) ((extChartAt 𝓘(ℂ, ℂ) (a : HyperellipticOdd H h))
        ((extChartAt 𝓘(ℂ, ℂ) (infty : HyperellipticOdd H h)).symm z)) *
        (fderiv ℂ ((extChartAt 𝓘(ℂ, ℂ) (a : HyperellipticOdd H h)) ∘
          (extChartAt 𝓘(ℂ, ℂ) (infty : HyperellipticOdd H h)).symm) z 1) := by
  -- Step 1: Reduce extChartAt to concrete charts
  -- extChartAt infty = infinityChart (by Set.univ_inter)
  -- extChartAt (coe a) = affineLiftChart a (by Set.univ_inter)
  -- hyperellipticOddCoeff g (coe a) = hyperellipticAffineCoeff g a (by rfl)
  -- Step 2: Case split on a ∈ smoothLocusY
  by_cases hpY : a ∈ HyperellipticAffine.smoothLocusY H
  · -- Case: a ∈ smoothLocusY (projX chart, transition z ↦ w(z)⁻²)
    -- Step 1: Rewrite affine coefficient
    -- hyperellipticOddCoeff g (coe a) = hyperellipticAffineCoeff g a
    have hCoeffEq : hyperellipticOddCoeff (h := h) g (coe a) =
        HyperellipticAffine.hyperellipticAffineCoeff g a := rfl
    rw [hCoeffEq]
    -- Step 2: Identify affineLiftChart with projX lift
    have hchart :
        (ChartedSpace.chartAt a :
          OpenPartialHomeomorph (HyperellipticAffine H) ℂ) =
          HyperellipticAffine.affineChartProjX (H := H) a hpY := by
      change HyperellipticAffine.affineChartAt (H := H) a =
        HyperellipticAffine.affineChartProjX (H := H) a hpY
      simp [HyperellipticAffine.affineChartAt, hpY]
    -- Step 3: Compute the transition value
    -- The transition infinityChart.symm ≫ affineLiftChart a
    -- equals infinityChart.symm ≫ (affineChartProjX a hpY).lift coe
    -- and its value at z is (tLocalHomeomorph.symm z)⁻¹ ^ 2
    -- But first, show z is in the transition source
    have hzt : z ∈ (infinityChart H h).target := by
      have : (extChartAt 𝓘(ℂ, ℂ)
        (infty : HyperellipticOdd H h)).target =
          (infinityChart H h).target := by
        change Set.univ ∩ (ChartedSpace.chartAt
          (infty : HyperellipticOdd H h)).target = _
        rw [Set.univ_inter]; rfl
      rwa [← this]
    -- Show z ≠ 0 (z = 0 corresponds to ∞ which is not in the
    -- affine chart source, contradicting hsrc)
    have hzne : z ≠ 0 := by
      intro hc
      rw [hc] at hsrc
      -- infinityChart.symm 0 = ∞, which is not in any affine source
      have : (extChartAt 𝓘(ℂ, ℂ)
        (infty : HyperellipticOdd H h)).symm 0 =
          (infinityChart H h).symm 0 := rfl
      rw [this] at hsrc
      have hinf : (infinityChart H h).symm 0 =
        (infty : HyperellipticOdd H h) := by
        simp [infinityChart, infinityBackward, infty]
      rw [hinf] at hsrc
      -- ∞ ∈ (extChartAt (coe a)).source is impossible
      rw [extChartAt_source] at hsrc
      have : (infty : HyperellipticOdd H h) ∈
          (affineLiftChart (h := h) a).source := hsrc
      rw [affineLiftChart_source] at this
      obtain ⟨q, _, heq⟩ := this
      exact OnePoint.infty_notMem_range_coe ⟨q, heq⟩
    -- Step 4: Compute the transition value and the derivative
    -- Key: extChartAt (coe a) ∘ extChartAt infty.symm
    -- = affineLiftChart a ∘ infinityChart.symm
    -- = (affineChartProjX a hpY).lift coe ∘ infinityChart.symm (by hchart)
    -- By infinityChart_trans_affineLiftProjX_apply:
    --   transition(z) = w(z)⁻²
    -- where w = tLocalHomeomorph.symm z
    --
    -- Set w := tLocalHomeomorph.symm z
    let w := (InfinityInverse.tLocalHomeomorph H).symm z
    -- Show z ∈ tLocalHomeomorph.target
    have hzt_tLH : z ∈ (InfinityInverse.tLocalHomeomorph H).target := hzt
    -- Identify affineLiftChart a with projXLift
    have hLiftEq : affineLiftChart (h := h) a =
        (HyperellipticAffine.affineChartProjX (H := H)
          a hpY).lift_openEmbedding
            (OnePoint.isOpenEmbedding_coe
              (X := HyperellipticAffine H)) := by
      unfold affineLiftChart; congr 1
    -- Show the transition source membership
    have hTransSrc : z ∈ ((infinityChart H h).toPartialEquiv.symm.trans
        ((HyperellipticAffine.affineChartProjX (H := H) a hpY).lift_openEmbedding
          (OnePoint.isOpenEmbedding_coe
            (X := HyperellipticAffine H))).toPartialEquiv).source := by
      refine ⟨hzt, ?_⟩
      change (infinityChart H h).symm z ∈
        ((HyperellipticAffine.affineChartProjX (H := H) a hpY).lift_openEmbedding
          (OnePoint.isOpenEmbedding_coe
            (X := HyperellipticAffine H))).source
      have hSrcEq : (extChartAt 𝓘(ℂ, ℂ)
          (coe a : HyperellipticOdd H h)).source =
          (affineLiftChart (h := h) a).source := by
        rw [extChartAt_source]; rfl
      rw [← hLiftEq, ← hSrcEq]
      exact hsrc
    -- Step 4: Compute the extChartAt transition value
    have hExtApp : (extChartAt 𝓘(ℂ, ℂ)
        (coe a : HyperellipticOdd H h))
        ((extChartAt 𝓘(ℂ, ℂ)
          (infty : HyperellipticOdd H h)).symm z) =
          w⁻¹ ^ 2 := by
      -- extChartAt over 𝓘(ℂ,ℂ) is definitionally the chart map
      conv_lhs =>
        rw [show (↑(extChartAt 𝓘(ℂ, ℂ)
          (coe a : HyperellipticOdd H h)) :
            HyperellipticOdd H h → ℂ) =
          ↑(affineLiftChart (h := h) a) from rfl]
        rw [show (↑(extChartAt 𝓘(ℂ, ℂ)
          (infty : HyperellipticOdd H h)).symm :
            ℂ → HyperellipticOdd H h) =
          ↑(infinityChart H h).symm from rfl]
      -- conv rewrites gave ↑(affineLiftChart a) (↑(infinityChart.symm) z)
      -- = ↑(projXLift) (↑(infinityChart.symm) z)
      -- = ↑(infinityChart.symm ≫ₕ projXLift) z (by trans_apply)
      -- = w⁻¹ ^ 2 (by infinityChart_trans_affineLiftProjX_apply)
      have h1 : (affineLiftChart (h := h) a :
          OpenPartialHomeomorph (HyperellipticOdd H h) ℂ) =
        ((HyperellipticAffine.affineChartProjX (H := H)
          a hpY).lift_openEmbedding
            (OnePoint.isOpenEmbedding_coe
              (X := HyperellipticAffine H))) := hLiftEq
      rw [h1]
      exact infinityChart_trans_affineLiftProjX_apply
        a hpY hTransSrc
    rw [hExtApp]
    -- Now the goal has concrete transition value w⁻¹ ^ 2:
    -- hyperellipticOddCoeff g infty z =
    --   hyperellipticAffineCoeff g a (w⁻¹ ^ 2) *
    --     fderiv(extChartAt(coe a) ∘ extChartAt(infty).symm)(z)(1)
    -- Step 5: Unfold the LHS at z ≠ 0
    have hLHS : hyperellipticOddCoeff (h := h) g infty z =
        let x := (infinityInverseMap H h z).val.1
        2 * g.eval x * x ^ (H.genus + 2) /
          (x * (Polynomial.derivative H.f).eval x -
            (2 * H.genus + 2) * H.f.eval x) := by
      unfold hyperellipticOddCoeff
      dsimp [infty]
      simp only [hzt, hzne, if_pos, if_neg, not_false_eq_true]
    rw [hLHS]
    -- Identify x = w⁻¹ ^ 2 using infinityInverseMap_val_of_ne_zero
    have hInvMap := infinityInverseMap_val_of_ne_zero
      z hzt_tLH hzne (H := H) (h := h)
    -- x = (infinityInverseMap H h z).val.1 = w⁻¹ ^ 2
    have hx_eq : (infinityInverseMap H h z).val.1 = w⁻¹ ^ 2 := by
      -- infinityInverseMap = InfinityInverse.infinityInverseMap (wrapper)
      change (InfinityInverse.infinityInverseMap H h z).val.1 =
        w⁻¹ ^ 2
      rw [hInvMap]
    simp only [hx_eq]
    -- Now the goal has w⁻¹ ^ 2 on both LHS and RHS:
    -- 2 * g.eval(w⁻¹ ^ 2) * (w⁻¹ ^ 2)^(g+2) /
    --   (w⁻¹^2 * f'(w⁻¹^2) - (2g+2) * f(w⁻¹^2)) =
    --   hyperellipticAffineCoeff g a (w⁻¹ ^ 2) *
    --     fderiv(transition)(z)(1)
    -- Step 6: Unfold affine coefficient to affineProjXCoeff
    have hAffCoeff :
        HyperellipticAffine.hyperellipticAffineCoeff g a
          (w⁻¹ ^ 2) =
        HyperellipticAffine.affineProjXCoeff g a hpY
          (w⁻¹ ^ 2) := by
      simp [HyperellipticAffine.hyperellipticAffineCoeff, hpY]
    rw [hAffCoeff]
    -- Step 7: Show w⁻¹ ^ 2 ∈ affineChartProjX target
    -- The transition maps z to w⁻¹ ^ 2 which is in projXLift.target
    -- = affineChartProjX.target
    have hInTarget : w⁻¹ ^ 2 ∈
        ((HyperellipticAffine.affineChartProjX (H := H)
          a hpY) :
            OpenPartialHomeomorph (HyperellipticAffine H) ℂ).target := by
      -- The transition maps z to w⁻¹ ^ 2, and transition maps
      -- source to target
      have hmem : z ∈ ((infinityChart H h).symm.trans
          ((HyperellipticAffine.affineChartProjX (H := H)
            a hpY).lift_openEmbedding
              (OnePoint.isOpenEmbedding_coe
                (X := HyperellipticAffine H)))).source :=
        hTransSrc
      have hmap := ((infinityChart H h).symm.trans
          ((HyperellipticAffine.affineChartProjX (H := H)
            a hpY).lift_openEmbedding
              (OnePoint.isOpenEmbedding_coe
                (X := HyperellipticAffine H)))).map_source hmem
      rw [infinityChart_trans_affineLiftProjX_apply a hpY
        hmem] at hmap
      rw [OpenPartialHomeomorph.trans_target] at hmap
      exact hmap.1
    -- Step 8: Unfold affineProjXCoeff to explicit formula
    rw [HyperellipticAffine.affineProjXCoeff_eq_on_target
      g a hpY hInTarget]
    -- Step 9: Compute the fderiv
    -- Use Filter.EventuallyEq.fderiv_eq to replace the chart
    -- composition with z → w(z)⁻¹ ^ 2
    have hOverlapOpen :
        IsOpen ((infinityChart H h).symm.trans
          ((HyperellipticAffine.affineChartProjX (H := H)
            a hpY).lift_openEmbedding
              (OnePoint.isOpenEmbedding_coe
                (X := HyperellipticAffine H)))).source :=
      ((infinityChart H h).symm.trans _).open_source
    have hEqNear : (↑(extChartAt 𝓘(ℂ, ℂ)
        (coe a : HyperellipticOdd H h)) ∘
        ↑(extChartAt 𝓘(ℂ, ℂ)
          (infty : HyperellipticOdd H h)).symm) =ᶠ[nhds z]
      (fun z => ((InfinityInverse.tLocalHomeomorph H).symm
        z)⁻¹ ^ 2) := by
      refine Filter.eventually_of_mem
        (hOverlapOpen.mem_nhds hTransSrc) ?_
      intro u hu
      -- For u in the overlap, the chart composition equals
      -- the transition formula
      conv_lhs =>
        rw [show (↑(extChartAt 𝓘(ℂ, ℂ)
          (coe a : HyperellipticOdd H h)) :
            HyperellipticOdd H h → ℂ) =
          ↑(affineLiftChart (h := h) a) from rfl]
        rw [show (↑(extChartAt 𝓘(ℂ, ℂ)
          (infty : HyperellipticOdd H h)).symm :
            ℂ → HyperellipticOdd H h) =
          ↑(infinityChart H h).symm from rfl]
      rw [hLiftEq]
      exact infinityChart_trans_affineLiftProjX_apply
        a hpY hu
    rw [Filter.EventuallyEq.fderiv_eq hEqNear]
    -- Now the fderiv is of z → w(z)⁻¹ ^ 2
    -- Apply infinity_transition_deriv_identity to get the
    -- explicit derivative value
    rw [infinity_transition_deriv_identity a hpY
      hzt_tLH hzne hInTarget]
    -- Goal is now:
    -- 2 * g(w⁻²) * (w⁻²)^(g+2) / denom =
    --   g(w⁻²) / y * (2 * (w⁻²)^(g+2) * y / denom)
    -- where y = squareLocalHomeomorph.symm(f(w⁻²))
    -- This is a pure algebraic identity: cancel g(w⁻²)
    -- and y from both sides
    set x := w⁻¹ ^ 2
    set y := ((HyperellipticAffine.squareLocalHomeomorph
        (H := H) a hpY).symm
      (H.f.eval x))
    set D := x * (Polynomial.derivative H.f).eval x -
      (2 * ↑H.genus + 2) * H.f.eval x
    -- Goal: 2 * g(x) * x^(g+2) / D =
    --       g(x) / y * (2 * x^(g+2) * y / D)
    have hyNZ : y ≠ 0 :=
      HyperellipticAffine.squareLocalHomeomorph_symm_ne_zero
        a hpY hInTarget
    ring_nf
    rw [show eval x g * x ^ 2 * x ^ H.genus *
        D⁻¹ * y * y⁻¹ * 2 =
      eval x g * x ^ 2 * x ^ H.genus *
        D⁻¹ * (y * y⁻¹) * 2 from by ring]
    rw [mul_inv_cancel₀ hyNZ, mul_one]
  · -- Case: a ∉ smoothLocusY (projY chart)
    have hpX : a ∈ HyperellipticAffine.smoothLocusX H :=
      HyperellipticAffine.mem_smoothLocusX_of_y_eq_zero H
        (by simpa [HyperellipticAffine.smoothLocusY]
          using hpY)
    -- Step 1: Chart identification
    have hchart : ChartedSpace.chartAt a =
        HyperellipticAffine.affineChartProjY (H := H)
          a hpX :=
      HyperellipticAffine.affineChartAt_of_not_mem_smoothLocusY
        (H := H) a hpY
    -- Step 2: z ∈ infinityChart.target
    have hzt : z ∈ (infinityChart H h).target := by
      have : (extChartAt 𝓘(ℂ, ℂ)
        (infty : HyperellipticOdd H h)).target =
          (infinityChart H h).target := by
        change Set.univ ∩ (ChartedSpace.chartAt
          (infty : HyperellipticOdd H h)).target = _
        rw [Set.univ_inter]; rfl
      rwa [← this]
    -- Step 3: z ≠ 0
    have hzne : z ≠ 0 := by
      intro hc; rw [hc] at hsrc
      have : (extChartAt 𝓘(ℂ, ℂ)
        (infty : HyperellipticOdd H h)).symm 0 =
          (infinityChart H h).symm 0 := rfl
      rw [this] at hsrc
      have hinf : (infinityChart H h).symm 0 =
        (infty : HyperellipticOdd H h) := by
        simp [infinityChart, infinityBackward, infty]
      rw [hinf] at hsrc
      rw [extChartAt_source] at hsrc
      have : (infty : HyperellipticOdd H h) ∈
          (affineLiftChart (h := h) a).source := hsrc
      rw [affineLiftChart_source] at this
      obtain ⟨q, _, heq⟩ := this
      exact OnePoint.infty_notMem_range_coe ⟨q, heq⟩
    let w := (InfinityInverse.tLocalHomeomorph H).symm z
    have hzt_tLH :
        z ∈ (InfinityInverse.tLocalHomeomorph H).target :=
      hzt
    -- Step 4: affineLiftChart = projYLift
    have hLiftEq : affineLiftChart (h := h) a =
        (HyperellipticAffine.affineChartProjY (H := H)
          a hpX).lift_openEmbedding
            (OnePoint.isOpenEmbedding_coe
              (X := HyperellipticAffine H)) := by
      unfold affineLiftChart; rw [hchart]; rfl
    -- Step 5: Transition source membership
    have hTransSrc :
        z ∈ ((infinityChart H h).symm.trans
          ((HyperellipticAffine.affineChartProjY (H := H)
            a hpX).lift_openEmbedding
              (OnePoint.isOpenEmbedding_coe
                (X := HyperellipticAffine H)))).source := by
      constructor
      · exact hzt
      · have : (extChartAt 𝓘(ℂ, ℂ)
            (infty : HyperellipticOdd H h)).symm z ∈
            (affineLiftChart (h := h) a).source := by
          have := hsrc
          rwa [extChartAt_source] at this
        rw [hLiftEq] at this
        rw [Set.mem_preimage]
        convert this
    -- Step 6: Compute transition value
    -- For projY: transition is z ↦ z * (w⁻¹ ^ 2)^(g+1)
    have hExtApp :
        (extChartAt 𝓘(ℂ, ℂ)
          (coe a : HyperellipticOdd H h))
          ((extChartAt 𝓘(ℂ, ℂ)
            (infty : HyperellipticOdd H h)).symm z) =
          z * (w⁻¹ ^ 2) ^ (H.genus + 1) := by
      conv_lhs =>
        rw [show (↑(extChartAt 𝓘(ℂ, ℂ)
          (coe a : HyperellipticOdd H h)) :
            HyperellipticOdd H h → ℂ) =
          ↑(affineLiftChart (h := h) a) from rfl]
        rw [show (↑(extChartAt 𝓘(ℂ, ℂ)
          (infty : HyperellipticOdd H h)).symm :
            ℂ → HyperellipticOdd H h) =
          ↑(infinityChart H h).symm from rfl]
      rw [hLiftEq]
      exact infinityChart_trans_affineLiftProjY_apply
        a hpX hTransSrc
    rw [hExtApp]
    -- The remaining algebraic identity for the projY case
    sorry

theorem hyperellipticOddCoeff_satisfiesCotangentCocycle
    (g : Polynomial ℂ) (hDeg : g.natDegree < (H.f.natDegree - 1) / 2) :
    SatisfiesCotangentCocycle (HyperellipticOdd H h)
      (hyperellipticOddCoeff (H := H) (h := h) g) := by
  intro x y z hz hSrc
  induction x using HyperellipticOdd.rec with
  | infty_val =>
    induction y using HyperellipticOdd.rec with
    | infty_val =>
      -- (infty, infty): same chart, transition is identity
      have hRightInv : (extChartAt 𝓘(ℂ, ℂ) (infty : HyperellipticOdd H h))
          ((extChartAt 𝓘(ℂ, ℂ) (infty : HyperellipticOdd H h)).symm z) = z :=
        (extChartAt 𝓘(ℂ, ℂ) (infty : HyperellipticOdd H h)).right_inv hz
      rw [hRightInv]
      have hEv : ∀ᶠ w in nhds z,
          ((extChartAt 𝓘(ℂ, ℂ) (infty : HyperellipticOdd H h)) ∘
            (extChartAt 𝓘(ℂ, ℂ) (infty : HyperellipticOdd H h)).symm) w = id w :=
        Filter.eventually_of_mem (extChartAt_target_mem_nhds' hz) fun w hw => by
          simp only [Function.comp_apply, id]
          exact (extChartAt 𝓘(ℂ, ℂ)
            (infty : HyperellipticOdd H h)).right_inv hw
      rw [Filter.EventuallyEq.fderiv_eq hEv, fderiv_id,
          ContinuousLinearMap.id_apply, mul_one]
    | coe_val a =>
      exact hyperellipticOddCoeff_cocycle_infty_coe g a hz hSrc
  | coe_val p =>
    induction y using HyperellipticOdd.rec with
    | infty_val =>
      -- (coe p, infty): derived from (infty, coe p)
      -- via transition_fderiv_mul
      let φp := extChartAt 𝓘(ℂ, ℂ) (coe p : HyperellipticOdd H h)
      let φi := extChartAt 𝓘(ℂ, ℂ) (infty : HyperellipticOdd H h)
      let w := φi (φp.symm z)
      have hwt : w ∈ φi.target := φi.map_source hSrc
      have hws : φi.symm w ∈ φp.source := by
        change φi.symm (φi (φp.symm z)) ∈ φp.source
        rw [φi.left_inv hSrc]
        exact φp.map_target hz
      -- apply (infty, coe p) at (φi, φp, w)
      have hfwd := hyperellipticOddCoeff_cocycle_infty_coe
        g p hwt hws
      -- simplify φp (φi.symm w) = z in hfwd
      have hw_simp : φp (φi.symm w) = z := by
        change φp (φi.symm (φi (φp.symm z))) = z
        rw [φi.left_inv hSrc, φp.right_inv hz]
      rw [hw_simp] at hfwd
      -- hfwd: coeff infty w = coeff (coe p) z * D_bwd
      -- htfm: D_fwd * D_bwd = 1
      have htfm :=
        Jacobians.GeneralResults.transition_fderiv_mul
          (coe p : HyperellipticOdd H h)
          (infty : HyperellipticOdd H h) hz hSrc
      -- The goal is: coeff (coe p) z = coeff infty w * D_fwd
      -- We have: coeff infty w = coeff (coe p) z * D_bwd
      -- And: D_fwd * D_bwd = 1
      rw [hfwd, mul_assoc, mul_comm
        (fderiv ℂ (φp ∘ φi.symm) w 1)
        (fderiv ℂ (φi ∘ φp.symm) z 1),
        htfm, mul_one]
    | coe_val q =>
      -- (coe p, coe q): reduce to cocycle_coe_coe
      have hTarget :
        (extChartAt 𝓘(ℂ, ℂ)
          (coe p : HyperellipticOdd H h)).target =
            (affineLiftChart (h := h) p).target := by
        change Set.univ ∩ (ChartedSpace.chartAt
          (coe p : HyperellipticOdd H h)).target = _
        rw [Set.univ_inter]; rfl
      have hSource :
        (extChartAt 𝓘(ℂ, ℂ)
          (coe q : HyperellipticOdd H h)).source =
            (affineLiftChart (h := h) q).source := by
        rw [extChartAt_source 𝓘(ℂ, ℂ)]
        change (affineLiftChart (h := h) q).source =
          (affineLiftChart (h := h) q).source
        rfl
      have hz' : z ∈ (affineLiftChart (h := h) p).target :=
        hTarget ▸ hz
      have hSrc' : (affineLiftChart (h := h) p).symm z ∈
          (affineLiftChart (h := h) q).source := by
        rw [← hSource]
        exact hSrc
      exact hyperellipticOddCoeff_cocycle_coe_coe g p q hz' hSrc'

noncomputable def hyperellipticOddForm (H : HyperellipticData)
    [Fact (Odd H.f.natDegree)] (g : Polynomial ℂ) :
    HolomorphicOneForm (HyperellipticOdd H Fact.out) :=
  if h : g.natDegree < (H.f.natDegree - 1) / 2 then
    ⟨hyperellipticOddCoeff (H := H) (h := Fact.out) g,
     hyperellipticOddCoeff_isHolomorphicOneFormCoeff g h,
     hyperellipticOddCoeff_satisfiesCotangentCocycle g h,
     hyperellipticOddCoeff_isZeroOffChartTarget g⟩
  else 0

end Jacobians.ProjectiveCurve.HyperellipticOdd
