import Mathlib

/-!
# A width-plateau counterexample to an index-`p` conjecture for mean-curvature flow

Lean certification of `round_sphere_pwidth_counterexample.tex`.

The paper refutes the positive-Ricci branch of Chen–Gaspar's Conjecture 1:
on the unit round `S³` one has `ω₂ = 4π`, every width realizer is a
multiplicity-one equatorial two-sphere of Morse index `1` (not `2`), and no
nonempty closed minimal surface has area `< 4π`, so the required lower-area
endpoint of the eternal flow does not exist.

What is formalized where:

* `volume_unitBall_dim3`, `equator_area` — the equatorial
  two-sphere really has area `4π` (the surface measure of the unit sphere of
  Euclidean `ℝ³`), certifying "every member is an equatorial two-sphere and
  hence has mass 4π" in the proof of Lemma 2 (`lem:width`).
* `geodesicSphereArea_*` — the geodesic-sphere one-sweepout has largest member
  an equator (mass `4π sin² ρ ≤ 4π`, extremes at the poles are the zero cycle),
  the `ω₁ ≤ 4π` step of Lemma 2.
* `no_mass_concentration` — the `C r² → 0` no-concentration display of Lemma 2.
* `equator_pencil_hits_once` — the degree computation behind
  `Φ*λ̄ = α` (eq. `\eqref{eq:pullback}`): along the half-turn loop of equators,
  a generic point of `S³` lies on exactly one equator (mod 2 count = 1).
* `rigidity_counting` — the complete mass/multiplicity bookkeeping of
  Lemma 3 (`lem:rigidity`): integer multiplicities `≥ 1` and Willmore area
  bound `≥ 4π` on each component, with total mass exactly `4π`, force a single
  component of multiplicity one and area exactly `4π`.
* `jacobiEigenvalue_*`, `equator_morse_index`, `equator_nullity` — the
  spectral count (eq. `\eqref{eq:index}`): the Jacobi operator of the equator
  is `-Δ_{S²} - (|A|² + Ric(ν,ν)) = -Δ_{S²} - 2`, the sphere Laplacian has
  eigenvalues `ℓ(ℓ+1)` with multiplicity `2ℓ+1`, and hence `ind(E) = 1`
  (only `ℓ = 0` is negative) and `nul(E) = 3` (only `ℓ = 1` is null).
* `WidthData`, `RoundSphereSetup` — the Almgren–Pitts / Willmore inputs that
  Mathlib cannot express (min–max existence and regularity, the spherical
  Willmore inequality and its equality case, and the identification of the
  Jacobi spectrum with the second variation) are packaged as explicit
  hypotheses; each field is annotated with the tex statement it encodes.
  `trivialModel` shows the hypothesis package is consistent (not vacuous).
* `width_one_eq`, `width_two_eq` — Lemma 2 (`lem:width`): `ω₁ = ω₂ = 4π`.
* `no_realizer_of_index_two`, `no_lower_area_minimal_surface`,
  `chenGaspar_fails_index`, `chenGaspar_fails_endpoint`,
  `chenGaspar_positiveRicci_false` — Theorem 1 (`thm:main`): both the
  exact-index requirement and the lower-area-endpoint requirement fail at
  `p = 2`, hence the published conjecture's conclusion is false on `S³`.
* `augmented_index_relation` — §5: the repaired relation
  `ind(Σ) ≤ p ≤ ind(Σ) + nul(Σ)` does hold at `p = 2` (`1 ≤ 2 ≤ 4`).
* `fifth_width_jump` — the Remark's plateau structure: `ω₅ = 2π² > 4π = ω₄`,
  i.e. the plateau genuinely ends with a strict jump.

Not formalizable in current Mathlib (kept as hypotheses/comments): flat chains
and the space `𝒵₂(S³; ℤ₂)`, Almgren's isomorphism and `H*(RP²; ℤ₂)`,
Almgren–Pitts min–max existence/regularity, varifolds, the Willmore
inequality, Brakke flow.
-/

open Real Set MeasureTheory
open scoped ENNReal

namespace RoundSpherePWidth

noncomputable section

/-! ## The area of an equatorial two-sphere is `4π`

An equator `E = S³ ∩ v^⊥` is a unit round two-sphere, isometric to the unit
sphere of Euclidean `ℝ³`.  We compute its surface measure (Mathlib's
`Measure.toSphere` of Lebesgue measure) to be exactly `4π`.  This certifies
the sentence "Every member is an equatorial two-sphere and hence has mass
`4π`" in the proof of Lemma 2 of the paper. -/

/-- The unit ball of Euclidean `ℝ³` has volume `4π/3` (via Mathlib's
`EuclideanSpace.volume_ball_fin_three`). -/
theorem volume_unitBall_dim3 :
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1) = ENNReal.ofReal (4 * π / 3) := by
  rw [EuclideanSpace.volume_ball_fin_three, ENNReal.ofReal_one, one_pow, one_mul]
  congr 1
  ring

/-- **The equatorial two-sphere has area `4π`.**  The surface measure of the
unit sphere in Euclidean `ℝ³` — to which any equator `S³ ∩ v^⊥` is isometric —
equals `4π`.  (Proof of Lemma 2, `lem:width`.) -/
theorem equator_area :
    (volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere univ = ENNReal.ofReal (4 * π) := by
  rw [Measure.toSphere_apply_univ, volume_unitBall_dim3, finrank_euclideanSpace]
  simp only [Fintype.card_fin]
  rw [show ((3 : ℕ) : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) by norm_num]
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  ring

/-! ## The geodesic-sphere one-sweepout (Lemma 2, upper bound for `ω₁`)

The geodesic sphere at distance `ρ` from a pole of the unit `S³` has area
`4π sin² ρ`.  The family starts and ends at the zero cycle (`ρ = 0, π`) and its
largest member is the equator (`ρ = π/2`), so the sweepout has maximal mass
`4π`, giving `ω₁(S³) ≤ 4π`. -/

/-- Area of the geodesic sphere at distance `ρ` from a pole in the unit `S³`. -/
def geodesicSphereArea (ρ : ℝ) : ℝ := 4 * π * Real.sin ρ ^ 2

/-- Every member of the geodesic-sphere sweepout has mass at most `4π`. -/
theorem geodesicSphereArea_le (ρ : ℝ) : geodesicSphereArea ρ ≤ 4 * π := by
  unfold geodesicSphereArea
  nlinarith [Real.sin_sq_le_one ρ, Real.pi_pos]

/-- The largest member of the sweepout is the equator, of mass exactly `4π`. -/
theorem geodesicSphereArea_max : geodesicSphereArea (π / 2) = 4 * π := by
  unfold geodesicSphereArea
  rw [Real.sin_pi_div_two]
  ring

/-- The sweepout starts at the zero cycle. -/
theorem geodesicSphereArea_start : geodesicSphereArea 0 = 0 := by
  simp [geodesicSphereArea]

/-- The sweepout ends at the zero cycle. -/
theorem geodesicSphereArea_end : geodesicSphereArea π = 0 := by
  simp [geodesicSphereArea]

/-- The no-concentration-of-mass display in the proof of Lemma 2:
`sup ‖Φ([v])‖(B_r(x)) ≤ C r² → 0` as `r → 0`. -/
theorem no_mass_concentration (C : ℝ) :
    Filter.Tendsto (fun r : ℝ => C * r ^ 2) (nhds 0) (nhds 0) := by
  simpa using (continuous_const.mul (continuous_pow 2)).tendsto (0 : ℝ)

/-! ## The half-turn pencil of equators hits a generic point exactly once

This is the verification of `Φ*λ̄ = α` (eq. `\eqref{eq:pullback}`): restricted
to a projective line, the sweepout `Φ([v]) = S³ ∩ v^⊥` is the loop of equators
`t ↦ S³ ∩ v(t)^⊥`, `v(t) = (cos πt, sin πt, 0, 0)`, `t ∈ [0,1)`.  A point
`x = (x₁, x₂, x₃, x₄) ∈ S³` lies on the equator at time `t` iff
`x₁ cos πt + x₂ sin πt = 0`.  For a generic point (`(x₁, x₂) ≠ (0,0)`) this
happens for **exactly one** `t ∈ [0,1)`; hence the swept chain is the
fundamental class `[S³]` and Almgren's isomorphism evaluates `λ̄` nontrivially
on the loop. -/

/-- A generic point belongs to exactly one equator of the half-turn loop:
for `(a, b) ≠ (0, 0)` there is exactly one `t ∈ [0, 1)` with
`a cos (πt) + b sin (πt) = 0`. -/
theorem equator_pencil_hits_once (a b : ℝ) (hab : ¬(a = 0 ∧ b = 0)) :
    ∃! t : ℝ, t ∈ Ico (0 : ℝ) 1 ∧ a * Real.cos (π * t) + b * Real.sin (π * t) = 0 := by
  -- Uniqueness: two incidence times t₁, t₂ ∈ [0,1) give parallel normal
  -- vectors, so sin (π t₁ - π t₂) = 0 with |π t₁ - π t₂| < π, forcing t₁ = t₂.
  have key : ∀ t₁ ∈ Ico (0 : ℝ) 1, ∀ t₂ ∈ Ico (0 : ℝ) 1,
      a * Real.cos (π * t₁) + b * Real.sin (π * t₁) = 0 →
      a * Real.cos (π * t₂) + b * Real.sin (π * t₂) = 0 → t₁ = t₂ := by
    intro t₁ ht₁ t₂ ht₂ h1 h2
    have hπ := Real.pi_pos
    have hb1 : π * t₁ < π := by nlinarith [ht₁.1, ht₁.2]
    have hb2 : π * t₂ < π := by nlinarith [ht₂.1, ht₂.2]
    have ha1 : 0 ≤ π * t₁ := mul_nonneg hπ.le ht₁.1
    have ha2 : 0 ≤ π * t₂ := mul_nonneg hπ.le ht₂.1
    have hlow : -π < π * t₁ - π * t₂ := by linarith
    have hhigh : π * t₁ - π * t₂ < π := by linarith
    have hsin : Real.sin (π * t₁ - π * t₂) = 0 := by
      rw [Real.sin_sub]
      rcases not_and_or.mp hab with ha | hb
      · have hdet : a * (Real.sin (π * t₁) * Real.cos (π * t₂) -
            Real.cos (π * t₁) * Real.sin (π * t₂)) = 0 := by
          linear_combination Real.sin (π * t₁) * h2 - Real.sin (π * t₂) * h1
        exact (mul_eq_zero.mp hdet).resolve_left ha
      · have hdet : b * (Real.sin (π * t₁) * Real.cos (π * t₂) -
            Real.cos (π * t₁) * Real.sin (π * t₂)) = 0 := by
          linear_combination Real.cos (π * t₂) * h1 - Real.cos (π * t₁) * h2
        exact (mul_eq_zero.mp hdet).resolve_left hb
    have hzero := (Real.sin_eq_zero_iff_of_lt_of_lt hlow hhigh).mp hsin
    have : π * t₁ = π * t₂ := by linarith
    exact mul_left_cancel₀ Real.pi_ne_zero this
  by_cases ha : a = 0
  · -- normal vector in the `b`-direction: the unique incidence time is t = 0
    have h0mem : (0 : ℝ) ∈ Ico (0 : ℝ) 1 := ⟨le_rfl, one_pos⟩
    have h0eq : a * Real.cos (π * 0) + b * Real.sin (π * 0) = 0 := by
      simp [ha]
    exact ⟨0, ⟨h0mem, h0eq⟩, fun y hy => key y hy.1 0 h0mem hy.2 h0eq⟩
  · -- a ≠ 0: the function changes sign between t = 0 and t = 1
    have hg0 : a * Real.cos (π * 0) + b * Real.sin (π * 0) = a := by
      rw [mul_zero, Real.cos_zero, Real.sin_zero]; ring
    have hg1 : a * Real.cos (π * 1) + b * Real.sin (π * 1) = -a := by
      rw [mul_one, Real.cos_pi, Real.sin_pi]; ring
    have hcont : Continuous fun t : ℝ => a * Real.cos (π * t) + b * Real.sin (π * t) := by
      fun_prop
    have hmem : (0 : ℝ) ∈ uIcc (a * Real.cos (π * 0) + b * Real.sin (π * 0))
        (a * Real.cos (π * 1) + b * Real.sin (π * 1)) := by
      rw [hg0, hg1]
      rcases le_or_gt 0 a with h | h
      · exact Set.mem_uIcc.mpr (Or.inr ⟨neg_nonpos.mpr h, h⟩)
      · exact Set.mem_uIcc.mpr (Or.inl ⟨h.le, neg_nonneg.mpr h.le⟩)
    obtain ⟨t₀, ht₀, hft₀⟩ := intermediate_value_uIcc hcont.continuousOn hmem
    rw [Set.uIcc_of_le zero_le_one] at ht₀
    have hft₀' : a * Real.cos (π * t₀) + b * Real.sin (π * t₀) = 0 := hft₀
    have ht1 : t₀ ≠ 1 := by
      intro h
      rw [h, hg1] at hft₀'
      exact ha (neg_eq_zero.mp hft₀')
    have hmem₀ : t₀ ∈ Ico (0 : ℝ) 1 := ⟨ht₀.1, lt_of_le_of_ne ht₀.2 ht1⟩
    exact ⟨t₀, ⟨hmem₀, hft₀'⟩, fun y hy => key y hy.1 t₀ hmem₀ hy.2 hft₀'⟩

/-! ## Rigidity of mass-`4π` varifolds: the counting argument of Lemma 3

Almgren–Pitts regularity writes the min–max varifold as `V = Σⱼ mⱼ|Σⱼ|` with
integer multiplicities `mⱼ ≥ 1` over smooth embedded closed minimal
components; the spherical Willmore inequality (eq. `\eqref{eq:willmore}`, with
`H = 0`) gives `Area(Σⱼ) ≥ 4π`.  The following theorem is the *complete*
remaining content of Lemma 3 (`lem:rigidity`): total mass exactly `4π` forces
one component, multiplicity one, and Willmore equality — which then makes the
component a geodesic (hence, being minimal, equatorial) two-sphere. -/

theorem rigidity_counting {ι : Type*} (s : Finset ι) (hne : s.Nonempty)
    (m : ι → ℕ) (area : ι → ℝ)
    (hm : ∀ j ∈ s, 1 ≤ m j)
    (hwillmore : ∀ j ∈ s, 4 * π ≤ area j)
    (hmass : ∑ j ∈ s, (m j : ℝ) * area j = 4 * π) :
    ∃ j, s = {j} ∧ m j = 1 ∧ area j = 4 * π := by
  have hπ : (0 : ℝ) < 4 * π := by positivity
  have hterm : ∀ j ∈ s, 4 * π ≤ (m j : ℝ) * area j := by
    intro j hj
    have h1 : (1 : ℝ) ≤ (m j : ℝ) := by exact_mod_cast hm j hj
    nlinarith [hwillmore j hj]
  -- there is exactly one component
  have hcard : s.card = 1 := by
    by_contra h
    have h2 : 2 ≤ s.card := by
      have := hne.card_pos
      omega
    have hsum : (s.card : ℝ) * (4 * π) ≤ ∑ j ∈ s, (m j : ℝ) * area j := by
      simpa [nsmul_eq_mul] using
        Finset.card_nsmul_le_sum s (fun j => (m j : ℝ) * area j) (4 * π) hterm
    rw [hmass] at hsum
    have h2' : (2 : ℝ) ≤ (s.card : ℝ) := by exact_mod_cast h2
    nlinarith
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard
  have hjmem : j ∈ s := by rw [hj]; exact Finset.mem_singleton_self j
  have hmassj : (m j : ℝ) * area j = 4 * π := by
    rw [hj, Finset.sum_singleton] at hmass
    exact hmass
  -- its multiplicity is one
  have hm1 : m j = 1 := by
    by_contra hne1
    have h2 : 2 ≤ m j := by
      have := hm j hjmem
      omega
    have h2' : (2 : ℝ) ≤ (m j : ℝ) := by exact_mod_cast h2
    nlinarith [hwillmore j hjmem]
  -- and equality holds in the Willmore inequality
  have harea : area j = 4 * π := by
    rw [hm1] at hmassj
    simpa using hmassj
  exact ⟨j, hj, hm1, harea⟩

/-! ## The Jacobi spectrum of the equator: `ind(E) = 1`, `nul(E) = 3`

The equator is totally geodesic (`|A_E|² = 0`) and `Ric_{S³}(ν, ν) = 2`, so the
second-variation form is `Q_E(f, f) = ∫ (|∇f|² − 2 f²)` and the Jacobi
operator is `-Δ_{S²} − 2`.  The Laplacian of the unit `S²` has eigenvalues
`ℓ(ℓ+1)`, `ℓ = 0, 1, 2, …`, with multiplicity `2ℓ+1` (spherical harmonics);
the identification of this spectrum with the second variation is a hypothesis
of `RoundSphereSetup` below, while the resulting *counting* — eq.
`\eqref{eq:index}` — is fully proved here. -/

/-- The `ℓ`-th eigenvalue of the Jacobi operator `-Δ_{S²} - (|A_E|² + Ric(ν,ν))
= -Δ_{S²} - 2` of the equator: `ℓ(ℓ+1) - 2`. -/
def jacobiEigenvalue (ℓ : ℕ) : ℤ := ℓ * (ℓ + 1) - 2

/-- Multiplicity of the `ℓ`-th spherical-harmonic eigenspace on `S²`. -/
def harmonicMultiplicity (ℓ : ℕ) : ℕ := 2 * ℓ + 1

/-- The only negative Jacobi mode is the constant mode `ℓ = 0`. -/
theorem jacobiEigenvalue_neg_iff (ℓ : ℕ) : jacobiEigenvalue ℓ < 0 ↔ ℓ = 0 := by
  unfold jacobiEigenvalue
  constructor
  · intro h
    by_contra h0
    have h1 : (1 : ℤ) ≤ (ℓ : ℤ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
    nlinarith
  · rintro rfl
    norm_num

/-- The kernel modes are exactly the three first spherical harmonics `ℓ = 1`. -/
theorem jacobiEigenvalue_eq_zero_iff (ℓ : ℕ) : jacobiEigenvalue ℓ = 0 ↔ ℓ = 1 := by
  unfold jacobiEigenvalue
  constructor
  · intro h
    have h2 : ((ℓ : ℤ) - 1) * ((ℓ : ℤ) + 2) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact_mod_cast (by linarith : (ℓ : ℤ) = 1)
    · exfalso
      have : (0 : ℤ) ≤ (ℓ : ℤ) := Int.natCast_nonneg ℓ
      linarith
  · rintro rfl
    norm_num

/-- All modes `ℓ ≥ 2` are strictly stable. -/
theorem jacobiEigenvalue_pos_iff (ℓ : ℕ) : 0 < jacobiEigenvalue ℓ ↔ 2 ≤ ℓ := by
  unfold jacobiEigenvalue
  constructor
  · intro h
    by_contra h0
    have hle : ℓ ≤ 1 := by omega
    interval_cases ℓ <;> norm_num at h
  · intro h2
    have h2' : (2 : ℤ) ≤ (ℓ : ℤ) := by exact_mod_cast h2
    nlinarith

/-- **`ind(E) = 1`** (eq. `\eqref{eq:index}`): the number of negative Jacobi
modes counted with multiplicity is `1`, for any spectral truncation containing
the constant mode. -/
theorem equator_morse_index (n : ℕ) (hn : 1 ≤ n) :
    ∑ ℓ ∈ (Finset.range n).filter (fun ℓ => jacobiEigenvalue ℓ < 0),
      harmonicMultiplicity ℓ = 1 := by
  have h : (Finset.range n).filter (fun ℓ => jacobiEigenvalue ℓ < 0) = {0} := by
    ext ℓ
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton,
      jacobiEigenvalue_neg_iff]
    constructor
    · exact fun h => h.2
    · rintro rfl
      exact ⟨hn, rfl⟩
  rw [h, Finset.sum_singleton]
  rfl

/-- **`nul(E) = 3`** (eq. `\eqref{eq:index}`): the number of Jacobi kernel
modes counted with multiplicity is `3`, for any spectral truncation containing
the `ℓ = 1` modes. -/
theorem equator_nullity (n : ℕ) (hn : 2 ≤ n) :
    ∑ ℓ ∈ (Finset.range n).filter (fun ℓ => jacobiEigenvalue ℓ = 0),
      harmonicMultiplicity ℓ = 3 := by
  have h : (Finset.range n).filter (fun ℓ => jacobiEigenvalue ℓ = 0) = {1} := by
    ext ℓ
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton,
      jacobiEigenvalue_eq_zero_iff]
    constructor
    · exact fun h => h.2
    · rintro rfl
      exact ⟨hn, rfl⟩
  rw [h, Finset.sum_singleton]
  rfl

/-! ## The abstract Almgren–Pitts / Willmore package

Min–max existence and regularity, the spherical Willmore inequality
(eq. `\eqref{eq:willmore}`) with its equality case, and the second-variation
identification are geometric inputs beyond current Mathlib.  Each is recorded
as an explicit hypothesis field, annotated with the tex statement it encodes;
the paper's reasoning *from* these inputs is then formally certified. -/

/-- The width data of Lemma 2 (`lem:width`).  `width p` denotes `ω_p(S³)`. -/
structure WidthData where
  /-- `p ↦ ω_p(S³, g_rd)`, the `p`-width defined via mod-2 cyclic sweepouts. -/
  width : ℕ → ℝ
  /-- Widths are nondecreasing in `p` (standard; used at the end of Lemma 2). -/
  width_mono : Monotone width
  /-- The geodesic-sphere sweepout (certified by `geodesicSphereArea_le` and
  `geodesicSphereArea_max`) gives `ω₁ ≤ 4π`. -/
  width_one_le : width 1 ≤ 4 * π
  /-- The `RP²` family of equators `Φ([v]) = S³ ∩ v^⊥` is an admissible
  two-sweepout of maximal mass `4π` (members certified by `equator_area`, the
  double sweep by `equator_pencil_hits_once`, no concentration by
  `no_mass_concentration`), so `ω₂ ≤ 4π`. -/
  width_two_le : width 2 ≤ 4 * π
  /-- Almgren–Pitts existence/regularity plus the Willmore bound on each
  component (the counting is `rigidity_counting`) give `ω₁ ≥ 4π`. -/
  le_width_one : 4 * π ≤ width 1

/-- Lemma 2, first identity: `ω₁(S³) = 4π`. -/
theorem WidthData.width_one_eq (D : WidthData) : D.width 1 = 4 * π :=
  le_antisymm D.width_one_le D.le_width_one

/-- **Lemma 2 (`lem:width`)**: `ω₂(S³) = 4π`, by the squeeze
`4π = ω₁ ≤ ω₂ ≤ 4π`. -/
theorem WidthData.width_two_eq (D : WidthData) : D.width 2 = 4 * π :=
  le_antisymm D.width_two_le (le_trans D.le_width_one (D.width_mono one_le_two))

/-- The full geometric setting of the paper on the unit round `S³`:
the width data plus the (abstract) nonempty closed minimal surfaces with
their areas, Morse indices, and nullities. -/
structure RoundSphereSetup extends WidthData where
  /-- Nonempty smooth closed embedded minimal surfaces in `(S³, g_rd)`
  (Almgren–Pitts realizers are of this form by regularity in ambient
  dimension three). -/
  MinimalSurface : Type
  /-- Area of a minimal surface. -/
  area : MinimalSurface → ℝ
  /-- Morse index (number of negative second-variation directions). -/
  index : MinimalSurface → ℕ
  /-- Nullity (dimension of the Jacobi kernel). -/
  nullity : MinimalSurface → ℕ
  /-- Being an equatorial two-sphere `S³ ∩ v^⊥`. -/
  IsEquator : MinimalSurface → Prop
  /-- The spherical Willmore inequality (eq. `\eqref{eq:willmore}`)
  specialized to minimal surfaces (`H = 0`): `Area(Σ) ≥ 4π`. -/
  willmore_minimal : ∀ S, 4 * π ≤ area S
  /-- The equality case of the Willmore inequality plus minimality
  (Lemma 3, after `rigidity_counting`): a minimal surface of area exactly
  `4π` is an equator. -/
  willmore_rigidity : ∀ S, area S = 4 * π → IsEquator S
  /-- The equator has Morse index `1` — the spectral computation of
  eq. `\eqref{eq:index}`, whose counting content is certified above by
  `equator_morse_index`. -/
  equator_index_one : ∀ S, IsEquator S → index S = 1
  /-- The equator has nullity `3` — certified above by `equator_nullity`. -/
  equator_nullity_three : ∀ S, IsEquator S → nullity S = 3

/-- The conclusion of Chen–Gaspar's Conjecture 1 at level `p`, *weakened* by
dropping the eternal-mean-curvature-flow connectivity requirement (we keep
only "a realizer `Σ₋` of `ω_p` with `ind(Σ₋) = p`, together with a minimal
surface `Σ₊` of strictly smaller area and strictly smaller index").
Refuting this weaker statement refutes the published conjecture a fortiori. -/
def ChenGasparConclusion (D : RoundSphereSetup) (p : ℕ) : Prop :=
  ∃ Sm, D.area Sm = D.width p ∧ D.index Sm = p ∧
    ∃ Sp, D.area Sp < D.area Sm ∧ D.index Sp < D.index Sm

/-- Lemma 3 (`lem:rigidity`), in the abstract setting: every minimal surface
realizing `ω₂ = 4π` is an equator. -/
theorem realizer_is_equator (D : RoundSphereSetup) (S : D.MinimalSurface)
    (h : D.area S = D.width 2) : D.IsEquator S :=
  D.willmore_rigidity S (by rw [h, D.toWidthData.width_two_eq])

/-- First obstruction of Theorem 1: every realizer of `ω₂` has index `1`. -/
theorem realizer_index_one (D : RoundSphereSetup) (S : D.MinimalSurface)
    (h : D.area S = D.width 2) : D.index S = 1 :=
  D.equator_index_one S (realizer_is_equator D S h)

/-- **Theorem 1, first obstruction**: no realizer of `ω₂(S³)` has the Morse
index `p = 2` demanded by the conjecture. -/
theorem no_realizer_of_index_two (D : RoundSphereSetup) :
    ¬∃ S, D.area S = D.width 2 ∧ D.index S = 2 := by
  rintro ⟨S, hA, hI⟩
  have h1 := realizer_index_one D S hA
  omega

/-- **Theorem 1, second obstruction**: there is no nonempty closed minimal
surface in `S³` of area strictly below `4π`, so the required lower-area
endpoint `Σ₊` does not exist. -/
theorem no_lower_area_minimal_surface (D : RoundSphereSetup) :
    ¬∃ S, D.area S < 4 * π := by
  rintro ⟨S, h⟩
  exact absurd (D.willmore_minimal S) (not_le.mpr h)

/-- The conjectured conclusion fails at `p = 2` via the index obstruction. -/
theorem chenGaspar_fails_index (D : RoundSphereSetup) : ¬ChenGasparConclusion D 2 := by
  rintro ⟨Sm, hA, hI, -⟩
  exact no_realizer_of_index_two D ⟨Sm, hA, hI⟩

/-- The conjectured conclusion fails at `p = 2` — independently — via the
missing lower-area endpoint. -/
theorem chenGaspar_fails_endpoint (D : RoundSphereSetup) : ¬ChenGasparConclusion D 2 := by
  rintro ⟨Sm, hA, -, Sp, hlt, -⟩
  have h1 : D.area Sm = 4 * π := by rw [hA, D.toWidthData.width_two_eq]
  have h2 := D.willmore_minimal Sp
  linarith

/-- **Theorem 1 (`thm:main`)**: the positive-Ricci branch of Chen–Gaspar's
Conjecture 1 is false — its conclusion fails on the unit round `S³` at
`p = 2`, for two independent reasons (`chenGaspar_fails_index` and
`chenGaspar_fails_endpoint`). -/
theorem chenGaspar_positiveRicci_false (D : RoundSphereSetup) :
    ¬ChenGasparConclusion D 2 :=
  chenGaspar_fails_index D

/-- §5 (Scope of the correction): the *augmented* index relation
`ind(Σ) ≤ p ≤ ind(Σ) + nul(Σ)` of Chen–Gaspar's Remark 1 does hold for the
round equator at `p = 2`, since `1 ≤ 2 ≤ 1 + 3`. -/
theorem augmented_index_relation (D : RoundSphereSetup) (S : D.MinimalSurface)
    (h : D.IsEquator S) : D.index S ≤ 2 ∧ 2 ≤ D.index S + D.nullity S := by
  rw [D.equator_index_one S h, D.equator_nullity_three S h]
  norm_num

/-- Consistency of the hypothesis package: `RoundSphereSetup` is inhabited, so
the refutation above is not vacuous. -/
def trivialModel : RoundSphereSetup where
  width := fun _ => 4 * π
  width_mono := monotone_const
  width_one_le := le_rfl
  width_two_le := le_rfl
  le_width_one := le_rfl
  MinimalSurface := PUnit
  area := fun _ => 4 * π
  index := fun _ => 1
  nullity := fun _ => 3
  IsEquator := fun _ => True
  willmore_minimal := fun _ => le_rfl
  willmore_rigidity := fun _ _ => trivial
  equator_index_one := fun _ _ => rfl
  equator_nullity_three := fun _ _ => rfl

/-! ## The plateau ends: `ω₅ = 2π² > 4π` (Remark after Lemma 2) -/

/-- The width plateau `ω₁ = ⋯ = ω₄ = 4π` genuinely ends at `p = 5`:
the known value `ω₅(S³) = 2π²` (area of the Clifford torus) strictly exceeds
`4π`. -/
theorem fifth_width_jump : 4 * π < 2 * π ^ 2 := by
  nlinarith [Real.pi_gt_three, Real.pi_pos]

end

end RoundSpherePWidth
