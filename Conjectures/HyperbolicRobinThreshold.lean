import Mathlib

/-!
# A Nonconvex Hyperbolic Obstacle with Positive Exterior Robin Threshold

Lean certification of the computational and geometric content of
`hyperbolic_exterior_robin_threshold.tex`.

The paper constructs, for `0 < r < R` and small `η > 0`, the annular sector
(tex eq. `eq:obstacle`)

  `Ω_η = {(ρ,θ) : r < ρ < R, η < θ < 2π − η} ⊂ ℍ²`

in geodesic polar coordinates `g = dρ² + sinh²ρ dθ²`, `dμ = sinh ρ dρ dθ`
(tex §2), shows it is a bounded, nonconvex, simply connected Lipschitz
obstacle with connected exterior `D_η`, and proves that the trial function
(tex eq. `eq:trial`)

  `u_η = 1` on the inner disk `B_r(o)`, `u_η = χ((ρ−r)/δ)` on the channel
  `{r ≤ ρ < r+δ, |θ| < η}` (`δ = √η`, `χ(t) = (1−t)₊`), `u_η = 0` otherwise,

has Rayleigh quotient below the essential-spectrum threshold `1/4` for the
Robin parameter `α_r = (1/8) tanh(r/2) > 0`.  Hence the critical exterior
Robin threshold `α_*(D_η) = sup{α : λ₁^α(D_η) < 1/4}` is positive
(tex Theorem 1).

## What is fully proved here

* All test-function computations of tex Lemma 2: the energy, boundary-trace,
  and norm integrals of `u_η`, evaluated exactly in the coordinates
  `dμ = sinh ρ dρ dθ` (`energy_eq`, `bdryTrace_eq`, `diskArea_eq`,
  `chi_sq_integral`) and estimated as in tex eqs. `eq:energy`, `eq:trace`,
  `eq:norm` (`energy_le`, `bdryTrace_le`, `normSq_ge`).
* The hyperbolic disk identities of tex §4:
  `P_r/A_r = coth(r/2)` in the form `tanh(r/2)·sinh r = cosh r − 1`
  (`tanh_half_mul_sinh`) and `α_r P_r / A_r = 1/8` (`alphaR_mul_P_div_A`).
* The Rayleigh-quotient estimate `< 1/4` on the paper's explicit
  admissible range of `η` (`rayleigh_quotient_lt_quarter`), together with
  nonemptiness of that range (`etaRange_pos`).
* The geometry of tex §2 at the level Mathlib can express:
  the coordinate obstacle is a nonempty convex rectangle
  (`obstacleCoord_convex`), hence simply connected
  (`obstacleCoord_isSimplyConnected`, and `obstacle_isSimplyConnected` for
  the image under any chart that embeds the slit region);
  the coordinate exterior decomposes as inner disk ∪ wedge ∪ outer region
  and is path-connected (`exteriorCoord_eq_union`,
  `exteriorCoord_isPathConnected`, `exterior_image_isPathConnected`);
  boundedness of the obstacle (`obstacle_isBounded`) and the nonconvexity
  argument (`obstacle_not_metricallyConvex`) from the two metric facts that
  characterise geodesic polar coordinates about `o`; and the concrete
  hyperbolic-plane version of the diameter argument in the upper half-plane
  model, using Mathlib's genuine hyperbolic metric on `UpperHalfPlane`
  (`uhpPt_dist`, `uhp_not_metricallyConvex`).

## What enters as hypotheses (machinery absent from Mathlib)

Mathlib has no Robin Laplacian on exterior domains of the hyperbolic plane,
so the following facts from the paper's source [CKL] are *hypotheses* of the
final theorems, each documented where it is used:

* `hray` — the variational principle tex eq. `eq:rayleigh` evaluated at the
  trial function `u_η` (which lies in `W^{1,2}(D_η)` by the Sobolev gluing of
  tex §3): `λ₁^{α_r}(D_η) ≤ Q_{α_r}[u_η]/‖u_η‖²`, with the three integrals
  expressed by the coordinate formulas `energy`, `bdryTrace`, `normSq`
  proved exact below.
* `hess` — tex eq. `eq:ess` ([CKL, Prop. 3.4]):
  `σ_ess(−Δ_α^{D_η}) = [1/4, ∞)`.
* `hbdd` — the set `{α : λ₁^α(D_η) < 1/4}` is bounded above (needed only so
  that its supremum `α_*` is the honest supremum; the paper takes this for
  granted in writing `α_*(D_η) = sup{…}`).
* `hdist`, `hopp`, `hΦ` — the defining metric/topological properties of
  geodesic polar coordinates about `o ∈ ℍ²` (tex §2): `ρ` is the distance to
  the pole, points whose angles differ by `π` lie on opposite rays of a
  single geodesic through `o`, and the chart embeds the slit region.
  (These are genuine facts about `exp_o` on any Cartan–Hadamard surface;
  the non-vacuity of the two metric hypotheses is certified in the upper
  half-plane model by `uhpPt_dist`.)

The Lipschitz regularity of `∂Ω_η` and the corner-rounding remark
(tex Remark 4) are not expressible with current Mathlib and are not
formalized.
-/

namespace HyperbolicRobinThreshold

open Real Set intervalIntegral

noncomputable section

/-! ## The constants of tex Theorem 1 -/

/-- `A_r = 2π(cosh r − 1)`, the hyperbolic area of the disk `B_r(o)`
(tex Theorem 1). -/
def A (r : ℝ) : ℝ := 2 * π * (cosh r - 1)

/-- `P_r = 2π sinh r`, the hyperbolic perimeter of `B_r(o)` (tex Theorem 1). -/
def P (r : ℝ) : ℝ := 2 * π * sinh r

/-- The Robin parameter `α_r = (1/8) tanh(r/2)` of tex Theorem 1. -/
def alphaR (r : ℝ) : ℝ := tanh (r / 2) / 8

/-- `C_r = sinh(r + 1/4) + α_r` (tex §4, "For an explicit range"). -/
def C (r : ℝ) : ℝ := sinh (r + 1 / 4) + alphaR r

/-- The channel depth `δ = √η` (tex §3). -/
def delta (η : ℝ) : ℝ := Real.sqrt η

theorem delta_nonneg (η : ℝ) : 0 ≤ delta η := Real.sqrt_nonneg η

theorem delta_pos {η : ℝ} (hη : 0 < η) : 0 < delta η := Real.sqrt_pos.mpr hη

theorem A_pos {r : ℝ} (hr : 0 < r) : 0 < A r := by
  have h1 : 1 < cosh r := Real.one_lt_cosh.mpr hr.ne'
  have hπ := Real.pi_pos
  unfold A; nlinarith

/-- `α_r > 0` for `r > 0` (tex Theorem 1: `α_r = (1/8) tanh(r/2) > 0`). -/
theorem alphaR_pos {r : ℝ} (hr : 0 < r) : 0 < alphaR r := by
  have h : 0 < tanh (r / 2) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (by linarith)) (Real.cosh_pos _)
  unfold alphaR; linarith

theorem C_pos {r : ℝ} (hr : 0 < r) : 0 < C r := by
  have h1 : 0 < sinh (r + 1 / 4) := Real.sinh_pos_iff.mpr (by linarith)
  have h2 := alphaR_pos hr
  unfold C; linarith

/-! ## The hyperbolic disk identities (tex §4)

`P_r/A_r = sinh r/(cosh r − 1) = coth(r/2)` and `α_r P_r/A_r = 1/8`. -/

/-- The identity `tanh(r/2) · sinh r = cosh r − 1`, i.e. `P_r/A_r = coth(r/2)`
(tex §4, first display of the proof of Theorem 1). -/
theorem tanh_half_mul_sinh (r : ℝ) : tanh (r / 2) * sinh r = cosh r - 1 := by
  have hc : (0 : ℝ) < cosh (r / 2) := Real.cosh_pos _
  have hs : sinh r = 2 * sinh (r / 2) * cosh (r / 2) := by
    have := Real.sinh_two_mul (r / 2)
    rw [show 2 * (r / 2) = r by ring] at this
    linarith
  have hcc : cosh r = cosh (r / 2) ^ 2 + sinh (r / 2) ^ 2 := by
    have := Real.cosh_two_mul (r / 2)
    rw [show 2 * (r / 2) = r by ring] at this
    linarith
  have hsq : cosh (r / 2) ^ 2 = sinh (r / 2) ^ 2 + 1 := Real.cosh_sq (r / 2)
  rw [Real.tanh_eq_sinh_div_cosh, hs, hcc]
  field_simp
  nlinarith [hsq]

/-- The key identity `α_r · P_r = A_r/8` (tex §4: `α_r P_r / A_r = 1/8`). -/
theorem alphaR_mul_P (r : ℝ) : alphaR r * P r = A r / 8 := by
  unfold alphaR P A
  have h := tanh_half_mul_sinh r
  nlinarith [Real.pi_pos]

/-- Division form of the key identity: `α_r P_r / A_r = 1/8` (tex §4). -/
theorem alphaR_mul_P_div_A {r : ℝ} (hr : 0 < r) : alphaR r * P r / A r = 1 / 8 := by
  rw [alphaR_mul_P]
  field_simp [(A_pos hr).ne']

/-! ## Elementary integrals -/

/-- `∫ₐᵇ sinh = cosh b − cosh a` (used throughout tex Lemma 2; not in Mathlib
as a named lemma, so proved here from the fundamental theorem of calculus). -/
theorem integral_sinh_eq (a b : ℝ) : (∫ ρ in a..b, sinh ρ) = cosh b - cosh a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => Real.hasDerivAt_cosh x)
    (Real.continuous_sinh.intervalIntegrable a b)

/-- Mean-value bound `cosh b − cosh a ≤ (b−a) sinh b` for `a ≤ b`
(tex Lemma 2, proof of eq. `eq:energy`). -/
theorem cosh_sub_cosh_le {a b : ℝ} (hab : a ≤ b) :
    cosh b - cosh a ≤ (b - a) * sinh b := by
  have h1 : (∫ x in a..b, sinh x) ≤ ∫ _ in a..b, sinh b :=
    intervalIntegral.integral_mono_on hab
      (Real.continuous_sinh.intervalIntegrable a b)
      _root_.intervalIntegrable_const
      (fun x hx => Real.sinh_le_sinh.mpr hx.2)
  rw [integral_sinh_eq, intervalIntegral.integral_const, smul_eq_mul] at h1
  linarith

/-- `∫_r^{r+δ} (1 − (ρ−r)/δ)² dρ = δ/3`, the profile integral on the radial
walls of the channel (tex Lemma 2, proof of eq. `eq:trace`). -/
theorem chi_sq_integral {δ : ℝ} (hδ : 0 < δ) (r : ℝ) :
    (∫ ρ in r..(r + δ), (1 - (ρ - r) / δ) ^ 2) = δ / 3 := by
  have hδ' : δ ≠ 0 := hδ.ne'
  have hderiv : ∀ x ∈ uIcc r (r + δ),
      HasDerivAt (fun ρ : ℝ => -(δ / 3) * (1 - (ρ - r) / δ) ^ 3)
        ((1 - (x - r) / δ) ^ 2) x := by
    intro x _
    have h1 : HasDerivAt (fun ρ : ℝ => 1 - (ρ - r) / δ) (-(1 / δ)) x := by
      simpa using (((hasDerivAt_id x).sub_const r).div_const δ).const_sub 1
    have h2 : HasDerivAt (fun ρ : ℝ => (1 - (ρ - r) / δ) ^ 3)
        ((3 : ℕ) * (1 - (x - r) / δ) ^ (3 - 1) * -(1 / δ)) x := h1.pow 3
    have h3 := h2.const_mul (-(δ / 3))
    have heq : -(δ / 3) * (((3 : ℕ) : ℝ) * (1 - (x - r) / δ) ^ (3 - 1) * -(1 / δ))
        = (1 - (x - r) / δ) ^ 2 := by
      push_cast
      norm_num
      field_simp
    rw [heq] at h3
    exact h3
  have hint : IntervalIntegrable (fun x : ℝ => (1 - (x - r) / δ) ^ 2)
      MeasureTheory.volume r (r + δ) := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have e1 : (r + δ - r) / δ = 1 := by
    rw [add_sub_cancel_left]
    exact div_self hδ'
  have e2 : (r - r) / δ = 0 := by simp
  rw [e1, e2]
  ring

/-! ## The trial function integrals (tex §3, Lemma 2)

The trial function `u_η` of tex eq. `eq:trial` is constant equal to `1` on the
inner disk `B_r(o)`, equals `χ((ρ−r)/δ)` on the channel
`{r ≤ ρ < r+δ, θ ∈ W_η}` of angular aperture `2η`, and vanishes elsewhere.
In the coordinates of tex §2 (`dμ = sinh ρ dρ dθ`, arc length `sinh ρ dθ` on
circles, `dρ` on radial rays), its Dirichlet energy, boundary trace, and
squared `L²` norm are the iterated integrals below; these coordinate
expressions are exactly the ones the paper manipulates in Lemma 2. -/

/-- Dirichlet energy `∫_{D_η} |∇u_η|² dμ`: a.e. `|∇u_η|² = (∂_ρ u_η)² = 1/δ²
= 1/η` on the channel and `0` elsewhere (tex Lemma 2, first display). -/
def energy (r η : ℝ) : ℝ :=
  ∫ _ in (-η)..η, ∫ ρ in r..(r + delta η), (1 / η) * sinh ρ

/-- Boundary trace `∫_{∂D_η} |u_η|² dσ`: `u_η = 1` on the inner arc
`{ρ = r, η < θ < 2π−η}`, `u_η = χ((ρ−r)/δ)` on the two radial walls, and
`u_η = 0` on the outer arc `{ρ = R}` (tex Lemma 2, second display). -/
def bdryTrace (r η : ℝ) : ℝ :=
  (∫ _ in η..(2 * π - η), sinh r)
    + 2 * ∫ ρ in r..(r + delta η), (1 - (ρ - r) / delta η) ^ 2

/-- Squared norm `‖u_η‖²_{L²(D_η)}`: the inner-disk contribution (`u_η = 1` on
`B_r(o)`) plus the channel contribution (tex Lemma 2, eq. `eq:norm`). -/
def normSq (r η : ℝ) : ℝ :=
  (∫ _ in (0 : ℝ)..(2 * π), ∫ ρ in (0 : ℝ)..r, sinh ρ)
    + ∫ _ in (-η)..η, ∫ ρ in r..(r + delta η), (1 - (ρ - r) / delta η) ^ 2 * sinh ρ

/-- The inner-disk integral is the hyperbolic area `A_r` (tex §2/Lemma 2:
"the inner disk `B_r(o)`, whose area is `A_r`"). -/
theorem diskArea_eq (r : ℝ) :
    (∫ _ in (0 : ℝ)..(2 * π), ∫ ρ in (0 : ℝ)..r, sinh ρ) = A r := by
  rw [integral_sinh_eq, intervalIntegral.integral_const, smul_eq_mul, Real.cosh_zero]
  unfold A; ring

/-- Exact value of the energy: `2(cosh(r+δ) − cosh r)` (tex Lemma 2 proof,
first computation). -/
theorem energy_eq {r : ℝ} (η : ℝ) (hη : 0 < η) :
    energy r η = 2 * (cosh (r + delta η) - cosh r) := by
  unfold energy
  rw [intervalIntegral.integral_const_mul, integral_sinh_eq,
    intervalIntegral.integral_const, smul_eq_mul]
  field_simp
  ring

/-- tex eq. `eq:energy`: `∫ |∇u_η|² dμ ≤ 2δ sinh(r+δ)`. -/
theorem energy_le {r : ℝ} (η : ℝ) (hη : 0 < η) :
    energy r η ≤ 2 * delta η * sinh (r + delta η) := by
  rw [energy_eq η hη]
  have hδ : 0 ≤ delta η := delta_nonneg η
  have h := cosh_sub_cosh_le (a := r) (b := r + delta η) (by linarith)
  rw [add_sub_cancel_left] at h
  linarith

/-- The energy is nonnegative (`cosh` is increasing on `[0,∞)`). -/
theorem energy_nonneg {r : ℝ} (η : ℝ) (hr : 0 < r) (hη : 0 < η) :
    0 ≤ energy r η := by
  rw [energy_eq η hη]
  have hδ : 0 ≤ delta η := delta_nonneg η
  have h : cosh r ≤ cosh (r + delta η) := by
    rw [Real.cosh_le_cosh, abs_of_pos hr, abs_of_pos (by linarith : (0:ℝ) < r + delta η)]
    linarith
  linarith

/-- Exact value of the boundary trace: `(2π − 2η) sinh r + (2/3)δ`
(tex Lemma 2 proof, second computation). -/
theorem bdryTrace_eq {r : ℝ} (η : ℝ) (hη : 0 < η) :
    bdryTrace r η = (2 * π - 2 * η) * sinh r + 2 * delta η / 3 := by
  unfold bdryTrace
  rw [chi_sq_integral (delta_pos hη) r,
    intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- tex eq. `eq:trace`: `∫_{∂D_η} |u_η|² dσ ≤ P_r + 2δ`. -/
theorem bdryTrace_le {r : ℝ} (η : ℝ) (hr : 0 < r) (hη : 0 < η) :
    bdryTrace r η ≤ P r + 2 * delta η := by
  rw [bdryTrace_eq η hη]
  unfold P
  have h1 : 0 < sinh r := Real.sinh_pos_iff.mpr hr
  have h2 : 0 ≤ delta η := Real.sqrt_nonneg η
  nlinarith

/-- The boundary trace is nonnegative for `η < π/2`. -/
theorem bdryTrace_nonneg {r : ℝ} (η : ℝ) (hr : 0 < r) (hη : 0 < η)
    (hη' : η < π / 2) : 0 ≤ bdryTrace r η := by
  rw [bdryTrace_eq η hη]
  have h1 : 0 < sinh r := Real.sinh_pos_iff.mpr hr
  have h2 : 0 ≤ delta η := Real.sqrt_nonneg η
  have hπ := Real.pi_gt_three
  nlinarith

/-- tex eq. `eq:norm`: `‖u_η‖² ≥ A_r`. -/
theorem normSq_ge {r : ℝ} (η : ℝ) (hr : 0 < r) (hη : 0 < η) :
    A r ≤ normSq r η := by
  unfold normSq
  rw [diskArea_eq]
  have h2 : 0 ≤ ∫ _ in (-η)..η,
      ∫ ρ in r..(r + delta η), (1 - (ρ - r) / delta η) ^ 2 * sinh ρ := by
    apply intervalIntegral.integral_nonneg (by linarith : -η ≤ η)
    intro θ _
    apply intervalIntegral.integral_nonneg
      (by linarith [delta_nonneg η] : r ≤ r + delta η)
    intro ρ hρ
    exact mul_nonneg (sq_nonneg _)
      (Real.sinh_pos_iff.mpr (lt_of_lt_of_le hr hρ.1)).le
  linarith

/-! ## The Rayleigh-quotient estimate (tex §4) -/

/-- The paper's admissible range of `η` is nonempty: the four bounds in
tex §4 (`η < min{π/2, 1/16, (R−r)², (A_r/(16C_r))²}`) have positive minimum. -/
theorem etaRange_pos {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    0 < min (min (π / 2) (1 / 16))
        (min ((R - r) ^ 2) ((A r / (16 * C r)) ^ 2)) := by
  have hπ := Real.pi_pos
  have hC := C_pos hr
  have hA := A_pos hr
  exact lt_min (lt_min (by linarith) (by norm_num))
    (lt_min (pow_pos (by linarith) 2)
      (pow_pos (div_pos hA (by linarith)) 2))

/-- **The central estimate** (tex eq. `eq:quotient` and the explicit range in
tex §4): for `η` in the paper's admissible range, the Rayleigh quotient of
the trial function `u_η` at the Robin parameter `α_r` is strictly below the
essential-spectrum threshold `1/4`. -/
theorem rayleigh_quotient_lt_quarter {r η : ℝ} (hr : 0 < r)
    (hη0 : 0 < η) (hη1 : η < π / 2) (hη2 : η < 1 / 16)
    (hη4 : η < (A r / (16 * C r)) ^ 2) :
    (energy r η + alphaR r * bdryTrace r η) / normSq r η < 1 / 4 := by
  have hδ0 : 0 < delta η := delta_pos hη0
  have hδnn : 0 ≤ delta η := hδ0.le
  have hC := C_pos hr
  have hA := A_pos hr
  have hα := alphaR_pos hr
  -- δ < 1/4 (from η < 1/16, tex: "Then δ < 1/4")
  have hδ14 : delta η < 1 / 4 := by
    unfold delta
    exact (Real.sqrt_lt' (by norm_num)).mpr
      (by rw [show ((1:ℝ)/4) ^ 2 = 1/16 by norm_num]; exact hη2)
  -- δ < A_r/(16 C_r), hence 2δC_r < A_r/8 (tex: "2δ(sinh(r+δ)+α_r)/A_r ≤ 2δC_r/A_r < 1/8")
  have hδC : delta η < A r / (16 * C r) := by
    unfold delta
    exact (Real.sqrt_lt' (by positivity)).mpr hη4
  have hkey : 2 * delta η * C r < A r / 8 := by
    rw [lt_div_iff₀ (by positivity : (0:ℝ) < 16 * C r)] at hδC
    nlinarith
  -- energy ≤ 2δ sinh(r+1/4) (tex eq:energy and δ < 1/4)
  have hE : energy r η ≤ 2 * delta η * sinh (r + 1 / 4) := by
    have h1 := energy_le (r := r) η hη0
    have h2 : sinh (r + delta η) ≤ sinh (r + 1 / 4) :=
      Real.sinh_le_sinh.mpr (by linarith)
    nlinarith
  have hE0 := energy_nonneg η hr hη0
  -- α_r · trace ≤ A_r/8 + 2δα_r (tex eq:trace and the identity α_r P_r = A_r/8)
  have hT : alphaR r * bdryTrace r η ≤ A r / 8 + 2 * delta η * alphaR r := by
    calc alphaR r * bdryTrace r η
        ≤ alphaR r * (P r + 2 * delta η) :=
          mul_le_mul_of_nonneg_left (bdryTrace_le η hr hη0) hα.le
      _ = A r / 8 + 2 * delta η * alphaR r := by
          rw [mul_add, alphaR_mul_P]; ring
  have hT0 : 0 ≤ alphaR r * bdryTrace r η :=
    mul_nonneg hα.le (bdryTrace_nonneg η hr hη0 hη1)
  -- numerator < A_r/4 (tex eq:quotient: bound = 1/8 + 2δC_r/A_r < 1/4)
  have hnum : energy r η + alphaR r * bdryTrace r η < A r / 4 := by
    have h3 : 2 * delta η * sinh (r + 1 / 4) + 2 * delta η * alphaR r
        = 2 * delta η * C r := by unfold C; ring
    nlinarith
  -- divide by the norm, which dominates A_r > 0 (tex eq:norm)
  have hN : A r ≤ normSq r η := normSq_ge η hr hη0
  have hN0 : 0 < normSq r η := lt_of_lt_of_le hA hN
  rw [div_lt_iff₀ hN0]
  nlinarith

/-! ## Geometry of the obstacle (tex §2) -/

/-- The coordinate obstacle `Ω_η = (r,R) × (η, 2π−η)` in geodesic polar
coordinates (tex eq. `eq:obstacle`). -/
def obstacleCoord (r R η : ℝ) : Set (ℝ × ℝ) :=
  Ioo r R ×ˢ Ioo η (2 * π - η)

theorem obstacleCoord_nonempty {r R η : ℝ} (hrR : r < R) (hη : η < π / 2) :
    (obstacleCoord r R η).Nonempty := by
  have hπ := Real.pi_gt_three
  exact ⟨((r + R) / 2, π), ⟨by constructor <;> linarith, by constructor <;> linarith⟩⟩

/-- The coordinate obstacle is a convex rectangle (tex §2: `Ω_η` is
"diffeomorphic to a rectangle"). -/
theorem obstacleCoord_convex (r R η : ℝ) : Convex ℝ (obstacleCoord r R η) :=
  (convex_Ioo r R).prod (convex_Ioo η (2 * π - η))

/-- tex §2: "`Ω_η` is … diffeomorphic to a rectangle, so it is simply
connected" — the coordinate rectangle is convex, hence contractible, hence
simply connected. -/
theorem obstacleCoord_isSimplyConnected {r R η : ℝ} (hrR : r < R)
    (hη : η < π / 2) : IsSimplyConnected (obstacleCoord r R η) := by
  have h := (obstacleCoord_convex r R η).contractibleSpace
    (obstacleCoord_nonempty hrR hη)
  exact (inferInstance : SimplyConnectedSpace (obstacleCoord r R η))

/-- tex §2, chart version: if the polar chart `Φ` restricted to the slit
region `U = (0,∞) × (0,2π)` (which contains the coordinate rectangle) is a
topological embedding — true for geodesic polar coordinates on `ℍ²` — then
the obstacle `Ω_η = Φ '' obstacleCoord` is a simply connected subset of the
manifold. -/
theorem obstacle_isSimplyConnected {X : Type*} [TopologicalSpace X]
    (Φ : ℝ × ℝ → X)
    (hΦ : Topology.IsEmbedding ((Ioi (0:ℝ) ×ˢ Ioo (0:ℝ) (2 * π)).restrict Φ))
    {r R η : ℝ} (hr : 0 < r) (hrR : r < R) (hη0 : 0 < η) (hη : η < π / 2) :
    IsSimplyConnected (Φ '' obstacleCoord r R η) := by
  set U : Set (ℝ × ℝ) := Ioi (0:ℝ) ×ˢ Ioo (0:ℝ) (2 * π) with hU
  have hπ := Real.pi_gt_three
  have hsub : obstacleCoord r R η ⊆ U := by
    rintro ⟨ρ, θ⟩ ⟨⟨h1, _⟩, h3, h4⟩
    exact ⟨lt_trans hr h1, lt_trans hη0 h3, by linarith⟩
  have himg : Φ '' obstacleCoord r R η
      = (U.restrict Φ) '' (Subtype.val ⁻¹' obstacleCoord r R η) := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p, hsub hp⟩, hp, rfl⟩
    · rintro ⟨⟨p, _⟩, hp, rfl⟩
      exact ⟨p, hp, rfl⟩
  rw [himg, hΦ.isSimplyConnected_image]
  have hval : Subtype.val ''
      (Subtype.val ⁻¹' obstacleCoord r R η : Set U) = obstacleCoord r R η := by
    rw [Subtype.image_preimage_coe]
    exact inter_eq_right.mpr hsub
  rw [← Topology.IsEmbedding.subtypeVal.isSimplyConnected_image
    (s := (Subtype.val ⁻¹' obstacleCoord r R η : Set U)), hval]
  exact obstacleCoord_isSimplyConnected hrR hη

/-- The coordinate exterior: the polar-coordinate strip
`[0,∞) × [0,2π]` minus the closed obstacle (tex §2: the exterior `D_η` is
"the union of the inner disk, the removed radial wedge, and the region
outside the radius-`R` disk"). -/
def exteriorCoord (r R η : ℝ) : Set (ℝ × ℝ) :=
  (Ici 0 ×ˢ Icc 0 (2 * π)) \ (Icc r R ×ˢ Icc η (2 * π - η))

/-- The decomposition of the exterior claimed in tex §2: inner disk ∪ wedge
(split by the coordinate cut `θ ∈ {0, 2π}` into its two halves) ∪ outer
region. -/
theorem exteriorCoord_eq_union {r R η : ℝ} (hr : 0 < r) (hrR : r < R)
    (_hη0 : 0 < η) (hη1 : η < π / 2) :
    exteriorCoord r R η =
      (((Ico 0 r ×ˢ Icc 0 (2 * π)) ∪ (Ici 0 ×ˢ Ico 0 η))
        ∪ (Ioi R ×ˢ Icc 0 (2 * π)))
        ∪ (Ici 0 ×ˢ Ioc (2 * π - η) (2 * π)) := by
  have hπ := Real.pi_gt_three
  ext ⟨ρ, θ⟩
  simp only [exteriorCoord, mem_diff, mem_prod, mem_Ici, mem_Icc, mem_Ico,
    mem_Ioi, mem_Ioc, mem_union]
  constructor
  · rintro ⟨⟨hρ0, hθ0, hθ2π⟩, hnot⟩
    rcases lt_or_ge ρ r with h | h
    · exact Or.inl (Or.inl (Or.inl ⟨⟨hρ0, h⟩, hθ0, hθ2π⟩))
    · rcases lt_or_ge R ρ with h' | h'
      · exact Or.inl (Or.inr ⟨h', hθ0, hθ2π⟩)
      · rcases lt_or_ge θ η with h'' | h''
        · exact Or.inl (Or.inl (Or.inr ⟨hρ0, hθ0, h''⟩))
        · rcases lt_or_ge (2 * π - η) θ with h''' | h'''
          · exact Or.inr ⟨hρ0, h''', hθ2π⟩
          · exact absurd ⟨⟨h, h'⟩, h'', h'''⟩ hnot
  · rintro (((⟨⟨h1, h2⟩, h3, h4⟩ | ⟨h1, h3, h4⟩) | ⟨h1, h3, h4⟩) | ⟨h1, h3, h4⟩)
    · exact ⟨⟨h1, h3, h4⟩, by rintro ⟨⟨ha, _⟩, _⟩; linarith⟩
    · exact ⟨⟨h1, h3, by linarith⟩, by rintro ⟨_, hc, _⟩; linarith⟩
    · exact ⟨⟨by linarith, h3, h4⟩, by rintro ⟨⟨_, hb⟩, _⟩; linarith⟩
    · exact ⟨⟨h1, by linarith, h4⟩, by rintro ⟨_, _, hd⟩; linarith⟩

/-- tex §2: "The wedge joins these pieces, and therefore `D_η` is connected."
The coordinate exterior is path-connected: each of the four pieces is a
nonempty convex product, and the wedge halves meet the inner disk and the
outer region. -/
theorem exteriorCoord_isPathConnected {r R η : ℝ} (hr : 0 < r) (hrR : r < R)
    (hη0 : 0 < η) (hη1 : η < π / 2) :
    IsPathConnected (exteriorCoord r R η) := by
  have hπ := Real.pi_gt_three
  rw [exteriorCoord_eq_union hr hrR hη0 hη1]
  -- membership witnesses
  have mA : ((0:ℝ), (0:ℝ)) ∈ Ico (0:ℝ) r ×ˢ Icc (0:ℝ) (2 * π) :=
    Set.mk_mem_prod (mem_Ico.mpr ⟨le_rfl, hr⟩) (mem_Icc.mpr ⟨le_rfl, by linarith⟩)
  have mW1 : ((0:ℝ), (0:ℝ)) ∈ Ici (0:ℝ) ×ˢ Ico (0:ℝ) η :=
    Set.mk_mem_prod (mem_Ici.mpr le_rfl) (mem_Ico.mpr ⟨le_rfl, hη0⟩)
  have mW1' : ((R + 1 : ℝ), (0:ℝ)) ∈ Ici (0:ℝ) ×ˢ Ico (0:ℝ) η :=
    Set.mk_mem_prod (mem_Ici.mpr (by linarith)) (mem_Ico.mpr ⟨le_rfl, hη0⟩)
  have mB : ((R + 1 : ℝ), (0:ℝ)) ∈ Ioi R ×ˢ Icc (0:ℝ) (2 * π) :=
    Set.mk_mem_prod (mem_Ioi.mpr (by linarith)) (mem_Icc.mpr ⟨le_rfl, by linarith⟩)
  have mA' : ((0:ℝ), 2 * π) ∈ Ico (0:ℝ) r ×ˢ Icc (0:ℝ) (2 * π) :=
    Set.mk_mem_prod (mem_Ico.mpr ⟨le_rfl, hr⟩) (mem_Icc.mpr ⟨by linarith, le_rfl⟩)
  have mW2 : ((0:ℝ), 2 * π) ∈ Ici (0:ℝ) ×ˢ Ioc (2 * π - η) (2 * π) :=
    Set.mk_mem_prod (mem_Ici.mpr le_rfl) (mem_Ioc.mpr ⟨by linarith, le_rfl⟩)
  -- the four convex pieces
  have hA : IsPathConnected (Ico (0:ℝ) r ×ˢ Icc (0:ℝ) (2 * π)) :=
    ((convex_Ico 0 r).prod (convex_Icc 0 (2 * π))).isPathConnected ⟨_, mA⟩
  have hW1 : IsPathConnected (Ici (0:ℝ) ×ˢ Ico (0:ℝ) η) :=
    ((convex_Ici 0).prod (convex_Ico 0 η)).isPathConnected ⟨_, mW1⟩
  have hB : IsPathConnected (Ioi R ×ˢ Icc (0:ℝ) (2 * π)) :=
    ((convex_Ioi R).prod (convex_Icc 0 (2 * π))).isPathConnected ⟨_, mB⟩
  have hW2 : IsPathConnected (Ici (0:ℝ) ×ˢ Ioc (2 * π - η) (2 * π)) :=
    ((convex_Ici 0).prod (convex_Ioc (2 * π - η) (2 * π))).isPathConnected ⟨_, mW2⟩
  -- chain them through nonempty intersections
  have h1 := hA.union hW1 ⟨(0, 0), mA, mW1⟩
  have h2 := h1.union hB ⟨(R + 1, 0), Or.inr mW1', mB⟩
  exact h2.union hW2 ⟨(0, 2 * π), Or.inl (Or.inl mA'), mW2⟩

/-- Chart version of the connectedness of the exterior: the image of the
coordinate exterior under any continuous polar chart `Φ` is path-connected.
(Under the full geodesic polar chart of `ℍ²` this image is exactly
`D̄_η ∪ ∂Ω_η ⊇ D_η` up to the boundary; the paper's `D_η` is its interior.) -/
theorem exterior_image_isPathConnected {X : Type*} [TopologicalSpace X]
    (Φ : ℝ × ℝ → X) (hΦ : Continuous Φ) {r R η : ℝ} (hr : 0 < r)
    (hrR : r < R) (hη0 : 0 < η) (hη1 : η < π / 2) :
    IsPathConnected (Φ '' exteriorCoord r R η) :=
  (exteriorCoord_isPathConnected hr hrR hη0 hη1).image hΦ

/-- tex §2: `Ω_η` is bounded.  `hdist` encodes the defining property of
geodesic polar coordinates that `ρ` is the geodesic distance to the pole `o`
(tex: `g = dρ² + sinh²ρ dθ²`); the obstacle then lies in the closed ball of
radius `R` about `o`. -/
theorem obstacle_isBounded {X : Type*} [PseudoMetricSpace X]
    (Φ : ℝ × ℝ → X) (o : X)
    (hdist : ∀ p : ℝ × ℝ, 0 ≤ p.1 → dist o (Φ p) = p.1)
    {r R η : ℝ} (hr : 0 < r) :
    Bornology.IsBounded (Φ '' obstacleCoord r R η) := by
  have hsub : Φ '' obstacleCoord r R η ⊆ Metric.closedBall o R := by
    rintro x ⟨⟨ρ, θ⟩, ⟨⟨h1, h2⟩, _⟩, rfl⟩
    have h0 : (0:ℝ) ≤ ρ := le_of_lt (lt_trans hr h1)
    rw [Metric.mem_closedBall, dist_comm, hdist (ρ, θ) h0]
    exact h2.le
  exact Metric.isBounded_closedBall.subset hsub

/-! ## Nonconvexity (tex §2)

Mathlib has no notion of geodesic convexity in metric spaces, so we encode
the paper's argument through *metric* convexity: a set `S` is metrically
convex if it contains every point lying metrically between two of its
points.  In a uniquely geodesic space such as `ℍ²`, any `z` with
`dist x z + dist z y = dist x y` lies on the unique minimizing geodesic from
`x` to `y`, so a geodesically convex set is metrically convex; failure of
metric convexity therefore certifies the failure of geodesic convexity
claimed in tex §2. -/

/-- Metric convexity: `S` contains every point metrically between two of its
points. -/
def MetricallyConvex {X : Type*} [PseudoMetricSpace X] (S : Set X) : Prop :=
  ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → ∀ ⦃z⦄, dist x z + dist z y = dist x y → z ∈ S

theorem not_metricallyConvex_of_between {X : Type*} [PseudoMetricSpace X]
    {S : Set X} {x y z : X} (hx : x ∈ S) (hy : y ∈ S)
    (hbtw : dist x z + dist z y = dist x y) (hz : z ∉ S) :
    ¬ MetricallyConvex S :=
  fun h => hz (h hx hy hbtw)

/-- **tex §2, nonconvexity.**  With geodesic polar coordinates `Φ` about `o`
(`hdist`: `ρ` is the distance to the pole; `hopp`: two points whose angles
differ by `π` lie on opposite rays of a single geodesic through `o`, so
their distance is the sum of their radii — the tex "diameter through `o`"),
the obstacle contains the two points of radius `s = (r+R)/2` and angles
`π/2`, `3π/2`, the pole `o` lies metrically between them, and `o ∉ Ω_η`
since every point of `Ω_η` has distance `> r > 0` from `o`.  Hence `Ω_η` is
not metrically convex, a fortiori not geodesically convex. -/
theorem obstacle_not_metricallyConvex {X : Type*} [MetricSpace X]
    (Φ : ℝ × ℝ → X) (o : X)
    (hdist : ∀ p : ℝ × ℝ, 0 ≤ p.1 → dist o (Φ p) = p.1)
    (hopp : ∀ ρ₁ ρ₂ θ : ℝ, 0 ≤ ρ₁ → 0 ≤ ρ₂ →
      dist (Φ (ρ₁, θ)) (Φ (ρ₂, θ + π)) = ρ₁ + ρ₂)
    {r R η : ℝ} (hr : 0 < r) (hrR : r < R) (_hη0 : 0 < η) (hη1 : η < π / 2) :
    ¬ MetricallyConvex (Φ '' obstacleCoord r R η) := by
  have hπ := Real.pi_gt_three
  set s : ℝ := (r + R) / 2 with hs
  have hs1 : r < s := by rw [hs]; linarith
  have hs2 : s < R := by rw [hs]; linarith
  have hsnn : (0:ℝ) ≤ s := by linarith
  apply not_metricallyConvex_of_between
    (x := Φ (s, π / 2)) (y := Φ (s, π / 2 + π)) (z := o)
  · exact ⟨(s, π / 2), ⟨⟨hs1, hs2⟩, hη1, by linarith⟩, rfl⟩
  · exact ⟨(s, π / 2 + π), ⟨⟨hs1, hs2⟩, by linarith, by linarith⟩, rfl⟩
  · rw [dist_comm (Φ (s, π / 2)) o, hdist (s, π / 2) hsnn,
      hdist (s, π / 2 + π) hsnn, hopp s s (π / 2) hsnn hsnn]
  · rintro ⟨⟨ρ, θ⟩, ⟨⟨h1, _⟩, _⟩, heq⟩
    have h := hdist (ρ, θ) (le_of_lt (lt_trans hr h1))
    rw [heq, dist_self] at h
    linarith

/-! ### The diameter argument in the genuine hyperbolic plane

Mathlib's `UpperHalfPlane` carries the hyperbolic metric of `ℍ²`.  The
points `i·e^t` lie on the vertical geodesic through the pole `i`, and
`dist (i e^a) (i e^b) = |a − b|`; in particular the pole is metrically
between `i e^s` and `i e^{-s}`.  This certifies, in a concrete model of
`ℍ²`, both the paper's diameter argument and the non-vacuity of the
hypotheses `hdist`/`hopp` above (for the angles `π/2`, `3π/2` used). -/

/-- The point `i·e^t` of the upper half-plane model of `ℍ²`. -/
def uhpPt (t : ℝ) : UpperHalfPlane :=
  ⟨⟨0, exp t⟩, exp_pos t⟩

theorem uhpPt_re (t : ℝ) : (uhpPt t).re = 0 := rfl

theorem uhpPt_im (t : ℝ) : (uhpPt t).im = exp t := rfl

/-- Hyperbolic distance along the vertical geodesic:
`dist (i e^a) (i e^b) = |a − b|` (tex §2: the diameter through `o` is a
minimizing geodesic, parametrized by arc length). -/
theorem uhpPt_dist (a b : ℝ) : dist (uhpPt a) (uhpPt b) = |a - b| := by
  rw [UpperHalfPlane.dist_of_re_eq (by rw [uhpPt_re, uhpPt_re]),
    uhpPt_im, uhpPt_im, Real.log_exp, Real.log_exp, Real.dist_eq]

/-- tex §2 in the concrete hyperbolic plane: any set containing the two
points `i e^{±s}` (`s > 0`) of the vertical geodesic but not the pole
`i = i e^0` metrically between them fails to be (metrically, a fortiori
geodesically) convex.  Applied to `Ω_η` — which contains two such points of
equal radius on a diameter and misses `B_r(o) ∋ o` — this is the paper's
nonconvexity proof. -/
theorem uhp_not_metricallyConvex {S : Set UpperHalfPlane} {s : ℝ}
    (hs : 0 < s) (h1 : uhpPt s ∈ S) (h2 : uhpPt (-s) ∈ S)
    (h0 : uhpPt 0 ∉ S) : ¬ MetricallyConvex S := by
  apply not_metricallyConvex_of_between h1 h2 _ h0
  rw [uhpPt_dist, uhpPt_dist, uhpPt_dist,
    abs_of_nonneg (by linarith : (0:ℝ) ≤ s - 0),
    abs_of_nonneg (by linarith : (0:ℝ) ≤ 0 - -s),
    abs_of_nonneg (by linarith : (0:ℝ) ≤ s - -s)]
  ring

/-! ## The spectral conclusions (tex Theorem 1) -/

/-- The critical exterior Robin threshold
`α_*(D) = sup{α ∈ ℝ : λ₁^α(D) < 1/4}` (tex Introduction), as a function of
the spectral data `lam : α ↦ λ₁^α(D)`. -/
def alphaStar (lam : ℝ → ℝ) : ℝ := sSup {α : ℝ | lam α < 1 / 4}

/-- tex Theorem 1, spectral inequality: given the variational principle
tex eq. `eq:rayleigh` evaluated at the trial function `u_η` (hypothesis
`hray`; `u_η ∈ W^{1,2}(D_η)` by the Sobolev gluing of tex §3, and its
energy, boundary trace, and squared norm are the coordinate integrals
`energy`, `bdryTrace`, `normSq` computed above), the lowest spectral point
satisfies `λ₁^{α_r}(D_η) < 1/4`. -/
theorem lambda_one_lt_quarter {r η : ℝ} (hr : 0 < r)
    (hη0 : 0 < η) (hη1 : η < π / 2) (hη2 : η < 1 / 16)
    (hη4 : η < (A r / (16 * C r)) ^ 2) {lam₁ : ℝ}
    (hray : lam₁ ≤ (energy r η + alphaR r * bdryTrace r η) / normSq r η) :
    lam₁ < 1 / 4 :=
  lt_of_le_of_lt hray (rayleigh_quotient_lt_quarter hr hη0 hη1 hη2 hη4)

/-- tex Theorem 1 / eq. `eq:ess`: with the essential spectrum
`σ_ess(−Δ_{α_r}^{D_η}) = [1/4, ∞)` of [CKL, Prop. 3.4] as hypothesis
`hess`, the lowest spectral point lies strictly below the essential
spectrum — i.e. it is a *discrete* eigenvalue. -/
theorem lambda_one_notMem_essSpectrum {r η : ℝ} (hr : 0 < r)
    (hη0 : 0 < η) (hη1 : η < π / 2) (hη2 : η < 1 / 16)
    (hη4 : η < (A r / (16 * C r)) ^ 2) {lam₁ : ℝ}
    (hray : lam₁ ≤ (energy r η + alphaR r * bdryTrace r η) / normSq r η)
    {essSpec : Set ℝ} (hess : essSpec = Ici (1 / 4)) :
    lam₁ ∉ essSpec := by
  rw [hess, mem_Ici, not_le]
  exact lambda_one_lt_quarter hr hη0 hη1 hη2 hη4 hray

/-- tex Theorem 1, threshold positivity: `α_r` belongs to the defining set
of `α_*(D_η)`, so (with `hbdd`: that set is bounded above, so that `sSup` is
the honest supremum) `α_*(D_η) ≥ α_r > 0`. -/
theorem alphaStar_pos {r η : ℝ} (hr : 0 < r)
    (hη0 : 0 < η) (hη1 : η < π / 2) (hη2 : η < 1 / 16)
    (hη4 : η < (A r / (16 * C r)) ^ 2) (lam : ℝ → ℝ)
    (hray : lam (alphaR r)
      ≤ (energy r η + alphaR r * bdryTrace r η) / normSq r η)
    (hbdd : BddAbove {α : ℝ | lam α < 1 / 4}) :
    0 < alphaStar lam :=
  lt_of_lt_of_le (alphaR_pos hr)
    (le_csSup hbdd (lambda_one_lt_quarter hr hη0 hη1 hη2 hη4 hray))

/-- **tex Theorem 1** (packaged).  Fix `0 < r < R` and take `η` in the
paper's explicit admissible range
`0 < η < min{π/2, 1/16, (R−r)², (A_r/(16C_r))²}` (nonempty by
`etaRange_pos`).  Let `Φ` be a geodesic polar chart about `o ∈ ℍ²`
(hypotheses `hdist`, `hopp` — its defining metric properties, tex §2) and
let `lam α = λ₁^α(D_η)` be the lowest spectral point of the exterior Robin
Laplacian, subject to the variational principle at the trial function `u_η`
(`hray`, tex eq. `eq:rayleigh` + §3) and with `{α : λ₁^α < 1/4}` bounded
above (`hbdd`).  Then:

1. `Ω_η` is bounded (lies in `B̄_R(o)`);
2. `Ω_η` is *not* convex (metrically, a fortiori geodesically);
3. the (coordinate) exterior is path-connected;
4. the channel fits inside the obstacle: `r + δ < R` (tex `δ < R − r`);
5. `α_r > 0`;
6. `λ₁^{α_r}(D_η) < 1/4` — the strict Rayleigh bound;
7. `λ₁^{α_r}(D_η)` lies outside `σ_ess = [1/4,∞)` — a discrete eigenvalue;
8. `α_*(D_η) > 0` — the positive exterior Robin threshold. -/
theorem main_theorem {r R η : ℝ} (hr : 0 < r) (hrR : r < R) (hη0 : 0 < η)
    (hη : η < min (min (π / 2) (1 / 16))
      (min ((R - r) ^ 2) ((A r / (16 * C r)) ^ 2)))
    {X : Type*} [MetricSpace X] (Φ : ℝ × ℝ → X) (o : X)
    (hdist : ∀ p : ℝ × ℝ, 0 ≤ p.1 → dist o (Φ p) = p.1)
    (hopp : ∀ ρ₁ ρ₂ θ : ℝ, 0 ≤ ρ₁ → 0 ≤ ρ₂ →
      dist (Φ (ρ₁, θ)) (Φ (ρ₂, θ + π)) = ρ₁ + ρ₂)
    (lam : ℝ → ℝ)
    (hray : lam (alphaR r)
      ≤ (energy r η + alphaR r * bdryTrace r η) / normSq r η)
    (hbdd : BddAbove {α : ℝ | lam α < 1 / 4}) :
    Bornology.IsBounded (Φ '' obstacleCoord r R η)
    ∧ ¬ MetricallyConvex (Φ '' obstacleCoord r R η)
    ∧ IsPathConnected (exteriorCoord r R η)
    ∧ r + delta η < R
    ∧ 0 < alphaR r
    ∧ lam (alphaR r) < 1 / 4
    ∧ lam (alphaR r) ∉ Ici (1 / 4 : ℝ)
    ∧ 0 < alphaStar lam := by
  obtain ⟨hη12, hη34⟩ := lt_min_iff.mp hη
  obtain ⟨hη1, hη2⟩ := lt_min_iff.mp hη12
  obtain ⟨hη3, hη4⟩ := lt_min_iff.mp hη34
  have hδR : r + delta η < R := by
    have h : delta η < R - r := by
      unfold delta
      exact (Real.sqrt_lt' (by linarith)).mpr hη3
    linarith
  refine ⟨obstacle_isBounded Φ o hdist hr,
    obstacle_not_metricallyConvex Φ o hdist hopp hr hrR hη0 hη1,
    exteriorCoord_isPathConnected hr hrR hη0 hη1,
    hδR,
    alphaR_pos hr,
    lambda_one_lt_quarter hr hη0 hη1 hη2 hη4 hray,
    ?_,
    alphaStar_pos hr hη0 hη1 hη2 hη4 lam hray hbdd⟩
  exact lambda_one_notMem_essSpectrum hr hη0 hη1 hη2 hη4 hray rfl

end

end HyperbolicRobinThreshold
