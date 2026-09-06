import Mathlib

/-!
# Eventual Finiteness of Critical Steklov Lengths on Hypersurfaces of Revolution

Formalization of `eventual_finite_steklov_lengths.tex`.

The paper studies, for hypersurfaces of revolution
`M = [0,L] × 𝕊^{n-1}` with two unit spherical boundary components, the
sharp-bound profile `B_n^k(L)` of Métras–Tschanz and proves
(Theorem `thm:main`): for every `n ≥ 3` all sufficiently high Steklov
indices `k` have *finite critical length*, i.e. `sup_{L>0} B_n^k(L)` is
attained at a finite `L`.

Throughout we write `p = n - 2 ≥ 1` (so `q = n - 1 = p + 1` and
`ν = (p : ℝ)` plays the role of `n - 2` in the eigenvalue formulas).

What is formalized:

* the spherical-harmonic multiplicities `m_j` (eq:multiplicity) and the
  closed form for the cumulative multiplicity `S_J` (eq:S);
* the mixed Steklov–Dirichlet/Neumann branches `D_j(R)`, `N_j(R)` on the
  annulus (eq:D, eq:N), their monotonicity in `R` and in the degree `j`,
  and their limits `→ j + n - 2` as `R → ∞` (Lemma `lem:infinity`);
* the model functions `f_s(x) = x tanh(sx)`, `g_s(x) = x coth(sx)`,
  their strict monotonicity, the coupled branch limits at the scale
  `R_i = e^{s/i}` (Lemma `lem:limits`), the roots `a_s, b_s` (eq:roots)
  and the scalar inequality `a_s^q + b_s^q < 2` (Lemma `lem:scalar`);
* the Métras–Tschanz profile `B_n^k(L)`, *defined concretely* as the k-th
  weighted order statistic of the finite branch multiset (eq:multiset),
  its continuity, the diagnosis-index analysis (Lemma `lem:cutoffs`,
  eq:rank/eq:ranklimits, eq:overshoot) and the attainment of the
  supremum at a finite length (Proposition `prop:diagnosis`);
* the main theorem (`thm:main`) for `n ≥ 3`, with the block-propagation
  lemma of Métras–Tschanz ([MetrasTschanz, Lemma 17], quoted in the
  paper as Lemma `lem:propagation`) supplied as an explicit hypothesis,
  since its proof lives in the cited paper, not in this one.

The identification of the concrete order-statistic profile with the
actual Steklov spectral quantity is the content of the cited
Métras–Tschanz derivation and is not re-proved here; the n = 2 case of
`thm:main` is due to Fan–Tam–Yu and is likewise outside this paper.
-/

namespace SteklovLengths

open Real Filter Topology Finset

/-! ## §2 of the paper: multiplicities and cumulative multiplicities

`mult p j` is the multiplicity `m_j` of the degree-`j` spherical
harmonics on `𝕊^{n-1}` with `p = n - 2` (eq:multiplicity), in the
standard binomial form `m_j = C(j+n-2, n-2) + C(j+n-3, n-2)`. -/

/-- Spherical multiplicity `m_j` (eq:multiplicity), with `p = n - 2`. -/
def mult (p j : ℕ) : ℕ := (j + p).choose p + (j + p - 1).choose p

/-- Cumulative multiplicity `S_J = ∑_{j=0}^J m_j` (eq:S, left side). -/
def cumMult (p J : ℕ) : ℕ := ∑ j ∈ Finset.range (J + 1), mult p j

theorem mult_pos (p j : ℕ) : 0 < mult p j :=
  lt_of_lt_of_le (Nat.choose_pos (Nat.le_add_left p j)) (Nat.le_add_right _ _)

theorem cumMult_succ (p J : ℕ) :
    cumMult p (J + 1) = cumMult p J + mult p (J + 1) := by
  simp [cumMult, Finset.sum_range_succ]

/-- **eq:S**: the closed form
`S_J = C(J+n-1, n-1) + C(J+n-2, n-1)` for the cumulative multiplicity,
with `p = n - 2` (so `n - 1 = p + 1`). -/
theorem cumMult_closed (p : ℕ) (hp : 1 ≤ p) (J : ℕ) :
    cumMult p J = (J + p + 1).choose (p + 1) + (J + p).choose (p + 1) := by
  induction J with
  | zero =>
      have h0 : cumMult p 0 = mult p 0 := by simp [cumMult]
      have h1 : (0 + p - 1).choose p = 0 :=
        Nat.choose_eq_zero_of_lt (by omega)
      have h2 : (0 + p).choose p = 1 := by simp
      have h3 : (0 + p + 1).choose (p + 1) = 1 := by
        rw [show 0 + p + 1 = p + 1 by omega]; exact Nat.choose_self _
      have h4 : (0 + p).choose (p + 1) = 0 :=
        Nat.choose_eq_zero_of_lt (by omega)
      rw [h0, mult, h1, h2, h3, h4]
  | succ J ih =>
      have hm : mult p (J + 1) = (J + p + 1).choose p + (J + p).choose p := by
        rw [mult, show J + 1 + p = J + p + 1 by omega,
          show J + p + 1 - 1 = J + p by omega]
      have p1 : (J + p + 2).choose (p + 1)
          = (J + p + 1).choose p + (J + p + 1).choose (p + 1) := by
        rw [show J + p + 2 = J + p + 1 + 1 by omega]
        exact Nat.choose_succ_succ _ _
      have p2 : (J + p + 1).choose (p + 1)
          = (J + p).choose p + (J + p).choose (p + 1) := by
        rw [show J + p + 1 = J + p + 1 by omega]
        exact Nat.choose_succ_succ _ _
      have hs := cumMult_succ p J
      rw [show J + 1 + p + 1 = J + p + 2 by omega,
        show J + 1 + p = J + p + 1 by omega]
      omega

/-- `S_J ≥ J + 1` (each multiplicity is positive). -/
theorem lt_cumMult (p J : ℕ) : J < cumMult p J := by
  induction J with
  | zero => simpa [cumMult] using mult_pos p 0
  | succ J ih =>
      have := mult_pos p (J + 1)
      have := cumMult_succ p J
      omega

/-- `S` is strictly increasing in `J`. -/
theorem cumMult_strictMono (p : ℕ) : StrictMono (cumMult p) := by
  apply strictMono_nat_of_lt_succ
  intro J
  have := mult_pos p (J + 1)
  have := cumMult_succ p J
  omega

/-- The diagnosis indices `k_i = 2 S_{i-1}` of the paper (§2). -/
def kDiag (p i : ℕ) : ℕ := 2 * cumMult p (i - 1)

/-- The block length identity `k_{i+1} - 1 = k_i + 2 m_i - 1` implicit in
Lemma `lem:propagation`. -/
theorem kDiag_succ (p i : ℕ) (hi : 1 ≤ i) :
    kDiag p (i + 1) = kDiag p i + 2 * mult p i := by
  have h1 : i + 1 - 1 = (i - 1) + 1 := by omega
  rw [kDiag, kDiag, h1, cumMult_succ, show i - 1 + 1 = i by omega]
  ring

theorem kDiag_strictMonoOn (p : ℕ) {i i' : ℕ} (hi : 1 ≤ i) (hii' : i < i') :
    kDiag p i < kDiag p i' := by
  have : cumMult p (i - 1) < cumMult p (i' - 1) :=
    cumMult_strictMono p (by omega)
  simp only [kDiag]; omega

/-- The diagnosis indices tend to infinity. -/
theorem le_kDiag (p i : ℕ) : i ≤ kDiag p i := by
  have := lt_cumMult p (i - 1)
  simp only [kDiag]; omega

/-! ## Hyperbolic helpers and the model functions `f_s`, `g_s` (§3)

Mathlib lacks a few elementary facts about `tanh`/`coth`; we prove them
here.  `phi z = z coth z` is the basic model for the Dirichlet branches. -/

theorem continuous_tanh : Continuous Real.tanh := by
  have : Real.tanh = fun x => Real.sinh x / Real.cosh x := by
    funext x; exact Real.tanh_eq_sinh_div_cosh x
  rw [this]
  exact Real.continuous_sinh.div Real.continuous_cosh
    fun x => (Real.cosh_pos x).ne'

theorem tanh_lt_tanh {x y : ℝ} (h : x < y) : Real.tanh x < Real.tanh y := by
  have hs : Real.sinh (x - y) < 0 := by
    rw [Real.sinh_neg_iff]; linarith
  rw [Real.sinh_sub] at hs
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
    div_lt_div_iff₀ (Real.cosh_pos x) (Real.cosh_pos y)]
  linarith

theorem tanh_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.tanh x := by
  rcases eq_or_lt_of_le hx with h | h
  · simp [← h]
  · have := tanh_lt_tanh h
    rw [Real.tanh_zero] at this
    exact this.le

theorem tanh_pos {x : ℝ} (hx : 0 < x) : 0 < Real.tanh x := by
  have := tanh_lt_tanh hx
  rwa [Real.tanh_zero] at this

/-- `tanh y = (1 - e^{-2y}) / (1 + e^{-2y})`. -/
theorem tanh_eq_exp (y : ℝ) :
    Real.tanh y = (1 - Real.exp (-(2 * y))) / (1 + Real.exp (-(2 * y))) := by
  have h3 : Real.exp y * Real.exp (-(2 * y)) = Real.exp (-y) := by
    rw [← Real.exp_add]; ring_nf
  have hp1 : Real.exp y + Real.exp (-y) ≠ 0 := by positivity
  have hp2 : 1 + Real.exp (-(2 * y)) ≠ 0 := by positivity
  rw [Real.tanh_eq, div_eq_div_iff hp1 hp2]
  linear_combination (2 : ℝ) * h3

/-- `1 - tanh y = 2e^{-2y} / (1 + e^{-2y})`. -/
theorem one_sub_tanh (y : ℝ) :
    1 - Real.tanh y
      = 2 * Real.exp (-(2 * y)) / (1 + Real.exp (-(2 * y))) := by
  have hp2 : 1 + Real.exp (-(2 * y)) ≠ 0 := by positivity
  rw [tanh_eq_exp]
  field_simp
  ring

/-- Elementary upper bound for `1 - tanh` used throughout §4. -/
theorem one_sub_tanh_le (y : ℝ) :
    1 - Real.tanh y ≤ 2 * Real.exp (-(2 * y)) := by
  rw [one_sub_tanh]
  have hE : 0 < Real.exp (-(2 * y)) := Real.exp_pos _
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- Elementary lower bound `e^{-2y} ≤ 1 - tanh y` for `y ≥ 0`. -/
theorem le_one_sub_tanh {y : ℝ} (hy : 0 ≤ y) :
    Real.exp (-(2 * y)) ≤ 1 - Real.tanh y := by
  rw [one_sub_tanh]
  have hE : 0 < Real.exp (-(2 * y)) := Real.exp_pos _
  have hE1 : Real.exp (-(2 * y)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- Second-order lower bound `2e^{-2y} - 2e^{-4y} ≤ 1 - tanh y`. -/
theorem le_one_sub_tanh' (y : ℝ) :
    2 * Real.exp (-(2 * y)) - 2 * Real.exp (-(2 * y)) ^ 2
      ≤ 1 - Real.tanh y := by
  rw [one_sub_tanh]
  have hE : 0 < Real.exp (-(2 * y)) := Real.exp_pos _
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- The model function `z ↦ z coth z`. -/
noncomputable def phi (z : ℝ) : ℝ := z * Real.cosh z / Real.sinh z

theorem phi_hasDerivAt {z : ℝ} (hz : z ≠ 0) :
    HasDerivAt phi
      ((Real.cosh z * Real.sinh z - z) / Real.sinh z ^ 2) z := by
  have h1 : HasDerivAt (fun w : ℝ => w * Real.cosh w)
      (1 * Real.cosh z + z * Real.sinh z) z :=
    (hasDerivAt_id z).mul (Real.hasDerivAt_cosh z)
  have h2 := h1.div (Real.hasDerivAt_sinh z) (Real.sinh_ne_zero.2 hz)
  convert h2 using 1
  have hs := Real.cosh_sq_sub_sinh_sq z
  congr 1
  linear_combination z * hs

theorem phi_deriv_pos {z : ℝ} (hz : 0 < z) :
    0 < (Real.cosh z * Real.sinh z - z) / Real.sinh z ^ 2 := by
  have h1 : 2 * z < Real.sinh (2 * z) := Real.self_lt_sinh_iff.2 (by linarith)
  rw [Real.sinh_two_mul] at h1
  have h2 : 0 < Real.sinh z := Real.sinh_pos_iff.2 hz
  apply div_pos (by nlinarith) (by positivity)

/-- `z coth z` is strictly increasing on `(0, ∞)` (used for `g_s` in
Lemma `lem:limits` and for the monotonicity of the Dirichlet branches in
the spherical degree). -/
theorem phi_strictMonoOn : StrictMonoOn phi (Set.Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro z hz
    exact ((phi_hasDerivAt (ne_of_gt hz)).continuousAt).continuousWithinAt
  · intro z hz
    rw [interior_Ioi] at hz
    rw [(phi_hasDerivAt (ne_of_gt hz)).deriv]
    exact phi_deriv_pos hz

/-- `z coth z → 1` as `z → 0⁺` (used for the `x = 0` Dirichlet limit,
`g_s(0) = 1/s`, in Lemma `lem:limits`). -/
theorem phi_tendsto_one : Tendsto phi (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have h1 : Tendsto (fun z : ℝ => Real.sinh z / z) (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
    have h := (Real.hasDerivAt_sinh 0).tendsto_slope
    rw [Real.cosh_zero] at h
    refine h.congr fun z => ?_
    rw [slope_def_field, Real.sinh_zero, sub_zero, sub_zero]
  have hc : Tendsto Real.cosh (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
    simpa using (Real.continuous_cosh.tendsto 0).mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun z : ℝ => Real.cosh z / (Real.sinh z / z))
      (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
    simpa using hc.div h1 one_ne_zero
  have h3 : Tendsto (fun z : ℝ => Real.cosh z / (Real.sinh z / z))
      (𝓝[>] (0 : ℝ)) (𝓝 1) :=
    h2.mono_left (nhdsWithin_mono _ fun z hz => ne_of_gt hz)
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz' : z ≠ 0 := ne_of_gt hz
  rw [phi, div_div_eq_mul_div, mul_comm]

/-- `f_s(x) = x tanh(sx)` (Lemma `lem:limits`, eq:flimit). -/
noncomputable def fs (s x : ℝ) : ℝ := x * Real.tanh (s * x)

/-- `g_s(x) = x coth(sx)` (Lemma `lem:limits`, eq:glimit). -/
noncomputable def gs (s x : ℝ) : ℝ := x * Real.cosh (s * x) / Real.sinh (s * x)

theorem gs_eq_phi {s : ℝ} (hs : s ≠ 0) (x : ℝ) : gs s x = phi (s * x) / s := by
  rw [gs, phi]
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · field_simp

/-- `f_s` is strictly increasing on `[0, ∞)` (Lemma `lem:limits`). -/
theorem fs_strictMonoOn {s : ℝ} (hs : 0 < s) : StrictMonoOn (fs s) (Set.Ici 0) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ici] at hx hy
  have h1 : Real.tanh (s * x) < Real.tanh (s * y) :=
    tanh_lt_tanh (by nlinarith)
  have h2 : 0 ≤ Real.tanh (s * x) := tanh_nonneg (by positivity)
  have hy' : 0 < y := lt_of_le_of_lt hx hxy
  rw [fs, fs]
  nlinarith

/-- `g_s` is strictly increasing on `(0, ∞)` (Lemma `lem:limits`). -/
theorem gs_strictMonoOn {s : ℝ} (hs : 0 < s) : StrictMonoOn (gs s) (Set.Ioi 0) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ioi] at hx hy
  rw [gs_eq_phi hs.ne', gs_eq_phi hs.ne']
  have h1 : phi (s * x) < phi (s * y) :=
    phi_strictMonoOn (by simp [Set.mem_Ioi]; positivity)
      (by simp [Set.mem_Ioi]; positivity) (by nlinarith)
  exact div_lt_div_of_pos_right h1 hs

theorem fs_lt_self {s x : ℝ} (hx : 0 < x) : fs s x < x := by
  have := Real.tanh_lt_one (s * x)
  rw [fs]
  nlinarith

/-! ## The mixed Steklov branches on the annulus (§2, eq:D and eq:N)

`ν` plays the role of `n - 2` and the spherical degree `j` is allowed to
be real (we only ever use natural values, cast to `ℝ`).  We write
`Dv/Nv` for the branch values as functions of `u = R^{2j+n-2}` and
`Db/Nb` for the branches themselves. -/

/-- Value of the Steklov–Dirichlet branch as a function of `u = R^{2j+ν}`. -/
noncomputable def Dv (ν j u : ℝ) : ℝ := ((j + ν) * u + j) / (u - 1)

/-- Value of the Steklov–Neumann branch as a function of `u = R^{2j+ν}`. -/
noncomputable def Nv (ν j u : ℝ) : ℝ := j * (j + ν) * (u - 1) / (j * u + j + ν)

/-- `u = R^{2j+ν}` (real power). -/
noncomputable def upow (ν j R : ℝ) : ℝ := R ^ (2 * j + ν)

/-- The Steklov–Dirichlet branch `D_j(R)` (eq:D), with `ν = n - 2`. -/
noncomputable def Db (ν j R : ℝ) : ℝ := Dv ν j (upow ν j R)

/-- The Steklov–Neumann branch `N_j(R)` (eq:N), with `ν = n - 2`. -/
noncomputable def Nb (ν j R : ℝ) : ℝ := Nv ν j (upow ν j R)

theorem one_lt_upow {ν j R : ℝ} (hν : 0 < ν) (hj : 0 ≤ j) (hR : 1 < R) :
    1 < upow ν j R :=
  Real.one_lt_rpow_iff_of_pos (by linarith) |>.2 (Or.inl ⟨hR, by linarith⟩)

theorem upow_lt_upow_right {ν j j' R : ℝ} (hR : 1 < R) (h : j < j') :
    upow ν j R < upow ν j' R :=
  Real.rpow_lt_rpow_of_exponent_lt hR (by linarith)

theorem upow_lt_upow_left {ν j R R' : ℝ} (hν : 0 < ν) (hj : 0 ≤ j)
    (hR : 0 ≤ R) (h : R < R') : upow ν j R < upow ν j R' :=
  Real.rpow_lt_rpow hR h (by linarith)

/-- `D_j > j + n - 2`: the Dirichlet branch always exceeds its `R → ∞`
limit (used in Lemma `lem:infinity`). -/
theorem lt_Dv {ν j u : ℝ} (hν : 0 < ν) (hj : 0 ≤ j) (hu : 1 < u) :
    j + ν < Dv ν j u := by
  rw [Dv, lt_div_iff₀ (by linarith)]
  nlinarith

/-- `N_j < j + n - 2`: the Neumann branch always lies below its `R → ∞`
limit (used in Lemma `lem:infinity`). -/
theorem Nv_lt {ν j u : ℝ} (hν : 0 < ν) (hj : 0 ≤ j) (hu : 1 < u) :
    Nv ν j u < j + ν := by
  rw [Nv, div_lt_iff₀ (by nlinarith)]
  nlinarith

theorem Nv_nonneg {ν j u : ℝ} (hν : 0 < ν) (hj : 0 ≤ j) (hu : 1 ≤ u) :
    0 ≤ Nv ν j u := by
  apply div_nonneg
  · exact mul_nonneg (mul_nonneg hj (by linarith)) (by linarith)
  · nlinarith

/-- The paper's claim "`N_j` increases in `R`" (at the level of `u`). -/
theorem Nv_lt_Nv {ν j u u' : ℝ} (hν : 0 < ν) (hj : 0 < j) (hu : 1 ≤ u)
    (huu' : u < u') : Nv ν j u < Nv ν j u' := by
  rw [Nv, Nv, div_lt_div_iff₀ (by nlinarith) (by nlinarith)]
  nlinarith [mul_pos (mul_pos hj (show (0:ℝ) < j + ν by linarith))
    (mul_pos (show (0:ℝ) < 2 * j + ν by linarith) (sub_pos.2 huu'))]

/-- The paper's claim "`D_j` decreases in `R`" (at the level of `u`). -/
theorem Dv_lt_Dv {ν j u u' : ℝ} (hν : 0 < ν) (hj : 0 ≤ j) (hu : 1 < u)
    (huu' : u < u') : Dv ν j u' < Dv ν j u := by
  rw [Dv, Dv, div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- The Neumann value is strictly increasing in the degree at fixed `u`. -/
theorem Nv_lt_Nv_degree {ν j j' u : ℝ} (hν : 0 < ν) (hj : 0 ≤ j)
    (hjj' : j < j') (hu : 1 < u) : Nv ν j u < Nv ν j' u := by
  rw [Nv, Nv, div_lt_div_iff₀ (by nlinarith) (by nlinarith)]
  nlinarith [mul_pos (mul_pos (sub_pos.2 hu) (sub_pos.2 hjj'))
      (mul_pos (show (0:ℝ) < j + ν by linarith)
        (show (0:ℝ) < j' + ν by linarith)),
    mul_nonneg (mul_nonneg (mul_nonneg (sub_pos.2 hu).le (sub_pos.2 hjj').le)
      hj) (mul_nonneg (le_of_lt (lt_of_le_of_lt hj hjj'))
        (by linarith : (0:ℝ) ≤ u))]

/-- "The mixed eigenvalues are strictly increasing in the spherical
degree" (proof of Lemma `lem:cutoffs`), Neumann case. -/
theorem Nb_strictMono_degree {ν j j' R : ℝ} (hν : 0 < ν) (hj : 0 < j)
    (hjj' : j < j') (hR : 1 < R) : Nb ν j R < Nb ν j' R := by
  have h1 : Nv ν j (upow ν j R) < Nv ν j' (upow ν j R) :=
    Nv_lt_Nv_degree hν hj.le hjj' (one_lt_upow hν hj.le hR)
  have h2 : Nv ν j' (upow ν j R) < Nv ν j' (upow ν j' R) :=
    Nv_lt_Nv hν (lt_trans hj hjj') (one_lt_upow hν hj.le hR).le
      (upow_lt_upow_right hR hjj')
  exact lt_trans h1 h2

/-- `N_j(R)` is strictly increasing in `R` (paper §2). -/
theorem Nb_strictMono_R {ν j R R' : ℝ} (hν : 0 < ν) (hj : 0 < j)
    (hR : 1 < R) (hRR' : R < R') : Nb ν j R < Nb ν j R' :=
  Nv_lt_Nv hν hj (one_lt_upow hν hj.le hR).le
    (upow_lt_upow_left hν (by linarith) (by linarith) hRR')

/-- `D_j(R)` is strictly decreasing in `R` (paper §2). -/
theorem Db_strictAnti_R {ν j R R' : ℝ} (hν : 0 < ν) (hj : 0 ≤ j)
    (hR : 1 < R) (hRR' : R < R') : Db ν j R' < Db ν j R :=
  Dv_lt_Dv hν hj (one_lt_upow hν hj hR)
    (upow_lt_upow_left hν hj (by linarith) hRR')

/-! ### The coth form of the Dirichlet branch and monotonicity in the degree -/

theorem phi_eq_exp {w : ℝ} (hw : 0 < w) :
    phi w = w * (Real.exp (2 * w) + 1) / (Real.exp (2 * w) - 1) := by
  have hE2 : Real.exp (2 * w) = Real.exp w * Real.exp w := by
    rw [← Real.exp_add]; ring_nf
  have hE1 : 1 < Real.exp w := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 hw
  have hEne : Real.exp w ≠ 0 := (Real.exp_pos w).ne'
  have hs : Real.sinh w ≠ 0 := Real.sinh_ne_zero.2 hw.ne'
  have hd : Real.exp w * Real.exp w - 1 ≠ 0 := by nlinarith
  rw [phi, hE2, Real.sinh_eq, Real.cosh_eq, Real.exp_neg]
  rw [Real.sinh_eq, Real.exp_neg] at hs
  field_simp

/-- The identity `D_j(R) = (n-2)/2 + z coth z / log R` with
`z = log R (j + (n-2)/2)`; it exhibits the Dirichlet branch as a shifted
and scaled copy of `z coth z` and drives both its monotonicity in the
degree and the coupled limit of Lemma `lem:limits`. -/
theorem Db_eq_phi {ν j R : ℝ} (hν : 0 < ν) (hj : 0 ≤ j) (hR : 1 < R) :
    Db ν j R = ν / 2 + phi (Real.log R * (j + ν / 2)) / Real.log R := by
  have hα : 0 < Real.log R := Real.log_pos hR
  have hw : 0 < Real.log R * (j + ν / 2) := by
    apply mul_pos hα; linarith
  have h2w : 2 * (Real.log R * (j + ν / 2)) = Real.log R * (2 * j + ν) := by
    ring
  have hu : upow ν j R = Real.exp (Real.log R * (2 * j + ν)) := by
    rw [upow, Real.rpow_def_of_pos (by linarith)]
  have hu1 : 1 < upow ν j R := one_lt_upow hν hj hR
  have hune : upow ν j R - 1 ≠ 0 := by linarith
  have hαne : Real.log R ≠ 0 := hα.ne'
  rw [Db, Dv, phi_eq_exp hw, h2w, ← hu]
  field_simp
  ring

/-- The Dirichlet branch is strictly increasing in the spherical degree
("the mixed eigenvalues are strictly increasing in the spherical
degree", proof of Lemma `lem:cutoffs`). -/
theorem Db_strictMono_degree {ν j j' R : ℝ} (hν : 0 < ν) (hj : 0 ≤ j)
    (hjj' : j < j') (hR : 1 < R) : Db ν j R < Db ν j' R := by
  rw [Db_eq_phi hν hj hR, Db_eq_phi hν (le_trans hj hjj'.le) hR]
  have hα : 0 < Real.log R := Real.log_pos hR
  have h1 : phi (Real.log R * (j + ν / 2)) < phi (Real.log R * (j' + ν / 2)) := by
    apply phi_strictMonoOn
    · exact Set.mem_Ioi.2 (by apply mul_pos hα; linarith)
    · exact Set.mem_Ioi.2 (by apply mul_pos hα; linarith)
    · exact mul_lt_mul_of_pos_left (by linarith) hα
  have := div_lt_div_of_pos_right h1 hα
  linarith

/-! ### Limits of the branches as `R → ∞` (proof of Lemma `lem:infinity`) -/

theorem tendsto_upow_atTop {ν j : ℝ} (h : 0 < 2 * j + ν) :
    Tendsto (upow ν j) atTop atTop :=
  tendsto_rpow_atTop h

/-- `D_j(R) → j + n - 2` as `R → ∞` (Lemma `lem:infinity`). -/
theorem Db_tendsto_atTop {ν j : ℝ} (hν : 0 < ν) (hj : 0 ≤ j) :
    Tendsto (Db ν j) atTop (𝓝 (j + ν)) := by
  have key : Tendsto (fun u : ℝ => Dv ν j u) atTop (𝓝 (j + ν)) := by
    have h1 : Tendsto (fun u : ℝ => ((j + ν) + j * u⁻¹) / (1 - u⁻¹)) atTop
        (𝓝 (((j + ν) + j * 0) / (1 - 0))) :=
      (tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_inv_atTop_zero)).div
        (tendsto_const_nhds.sub tendsto_inv_atTop_zero) (by norm_num)
    have h2 : (((j + ν) + j * 0) / (1 - 0)) = j + ν := by norm_num
    rw [h2] at h1
    apply h1.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with u hu
    rw [Dv]
    have hu0 : u ≠ 0 := by linarith
    have hu1 : u - 1 ≠ 0 := by linarith
    field_simp
  exact key.comp (tendsto_upow_atTop (by linarith))

/-- `N_j(R) → j + n - 2` as `R → ∞` (Lemma `lem:infinity`). -/
theorem Nb_tendsto_atTop {ν j : ℝ} (hν : 0 < ν) (hj : 0 < j) :
    Tendsto (Nb ν j) atTop (𝓝 (j + ν)) := by
  have key : Tendsto (fun u : ℝ => Nv ν j u) atTop (𝓝 (j + ν)) := by
    have h1 : Tendsto (fun u : ℝ => j * (j + ν) * (1 - u⁻¹) / (j + (j + ν) * u⁻¹))
        atTop (𝓝 (j * (j + ν) * (1 - 0) / (j + (j + ν) * 0))) :=
      (tendsto_const_nhds.mul (tendsto_const_nhds.sub tendsto_inv_atTop_zero)).div
        (tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_inv_atTop_zero))
        (by simpa using hj.ne')
    have h2 : j * (j + ν) * (1 - 0) / (j + (j + ν) * 0) = j + ν := by
      rw [mul_zero, add_zero, sub_zero, mul_one, mul_comm j (j + ν),
        mul_div_assoc, div_self hj.ne', mul_one]
    rw [h2] at h1
    apply h1.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with u hu
    rw [Nv]
    have hu0 : u ≠ 0 := by linarith
    have hd : j * u + j + ν ≠ 0 := by nlinarith
    have hd' : j + (j + ν) * u⁻¹ ≠ 0 := by
      have h3 : 0 < u⁻¹ := inv_pos.2 (by linarith)
      have : 0 < j + (j + ν) * u⁻¹ := by nlinarith
      exact this.ne'
    field_simp
    ring
  exact key.comp (tendsto_upow_atTop (by linarith))

/-! ### Continuity of the branches in `R`

Used for the continuity of the profile (§2: "Since (eq:multiset) is
finite and its branches are continuous, `B_n^k(L)` is continuous"). -/

theorem continuousOn_upow (ν j : ℝ) :
    ContinuousOn (upow ν j) (Set.Ioi 0) := fun R hR =>
  (Real.continuousAt_rpow_const R _ (Or.inl (ne_of_gt (Set.mem_Ioi.1 hR)))).continuousWithinAt

theorem continuousOn_Nb {ν j : ℝ} (hν : 0 < ν) (hj : 0 ≤ j) :
    ContinuousOn (Nb ν j) (Set.Ioi 0) := by
  unfold Nb Nv
  apply ContinuousOn.div
  · exact continuousOn_const.mul ((continuousOn_upow ν j).sub continuousOn_const)
  · exact ((continuousOn_const.mul (continuousOn_upow ν j)).add
      continuousOn_const).add continuousOn_const
  · intro R hR
    have h1 : 0 < upow ν j R := by
      rw [upow]; exact Real.rpow_pos_of_pos (Set.mem_Ioi.1 hR) _
    have h2 : 0 < j * upow ν j R + j + ν := by nlinarith
    exact h2.ne'

theorem continuousOn_Db {ν j : ℝ} (hν : 0 < ν) (hj : 0 ≤ j) :
    ContinuousOn (Db ν j) (Set.Ioi 1) := by
  have hsub : Set.Ioi (1 : ℝ) ⊆ Set.Ioi 0 := fun x hx =>
    Set.mem_Ioi.2 (lt_trans one_pos (Set.mem_Ioi.1 hx))
  unfold Db Dv
  apply ContinuousOn.div
  · exact (continuousOn_const.mul ((continuousOn_upow ν j).mono hsub)).add
      continuousOn_const
  · exact ((continuousOn_upow ν j).mono hsub).sub continuousOn_const
  · intro R hR
    have h1 : 1 < upow ν j R := one_lt_upow hν hj (Set.mem_Ioi.1 hR)
    intro hcon
    rw [sub_eq_zero] at hcon
    rw [hcon] at h1
    exact lt_irrefl _ h1

/-- `N_j(1) = 0`: at zero meridian length the Neumann branches vanish
(used for "`B_n^k(L)` tends to zero as `L ↓ 0`"). -/
theorem Nb_one (ν j : ℝ) : Nb ν j 1 = 0 := by
  simp [Nb, Nv, upow, Real.one_rpow]

/-! ## §3: the roots `a_s`, `b_s` of eq:roots -/

theorem continuous_fs (s : ℝ) : Continuous (fs s) :=
  continuous_id.mul (continuous_tanh.comp (continuous_const.mul continuous_id))

/-- Existence of the root `a_s ∈ (1,2)` of `a tanh(s a) = 1` (eq:roots). -/
theorem exists_root_a {s : ℝ} (hs : 1 ≤ s) :
    ∃ a, a ∈ Set.Ioo (1 : ℝ) 2 ∧ fs s a = 1 := by
  have hcont : ContinuousOn (fs s) (Set.Icc 1 2) :=
    (continuous_fs s).continuousOn
  have h1 : fs s 1 < 1 := by
    have := Real.tanh_lt_one (s * 1)
    rw [fs]; linarith
  have h2 : 1 < fs s 2 := by
    -- `2 tanh(2s) > 1` since `1 - tanh(2s) ≤ 2 e^{-4s} ≤ 2 e^{-4} < 1/2`
    have hb := one_sub_tanh_le (s * 2)
    have hexp : Real.exp (-(2 * (s * 2))) ≤ Real.exp (-4) :=
      Real.exp_le_exp.2 (by linarith)
    have h4 : (4 : ℝ) + 1 ≤ Real.exp 4 := Real.add_one_le_exp 4
    have h5 : Real.exp (-4) = (Real.exp 4)⁻¹ := Real.exp_neg 4
    have h6 : Real.exp (-4) ≤ 1 / 5 := by
      rw [h5]
      rw [inv_le_iff_one_le_mul₀ (by positivity)]
      nlinarith
    rw [fs]
    nlinarith
  have key : (1 : ℝ) ∈ Set.Ioo (fs s 1) (fs s 2) := ⟨h1, h2⟩
  have := intermediate_value_Ioo (by norm_num : (1 : ℝ) ≤ 2) hcont key
  obtain ⟨a, ha, hfa⟩ := this
  exact ⟨a, ha, hfa⟩

/-- Existence of the root `b_s ∈ (1/2, 1)` of `tanh(s b) = b`, the form of
`b coth(s b) = 1` used in the paper (eq:roots). -/
theorem exists_root_b {s : ℝ} (hs : 2 ≤ s) :
    ∃ b, b ∈ Set.Ioo (1 / 2 : ℝ) 1 ∧ Real.tanh (s * b) = b := by
  have hcont : ContinuousOn (fun x => Real.tanh (s * x) - x) (Set.Icc (1 / 2) 1) :=
    ((continuous_tanh.comp (continuous_const.mul continuous_id)).sub
      continuous_id).continuousOn
  have h1 : 0 < Real.tanh (s * (1 / 2)) - 1 / 2 := by
    have hb := one_sub_tanh_le (s * (1 / 2))
    have hexp : Real.exp (-(2 * (s * (1 / 2)))) ≤ Real.exp (-2) :=
      Real.exp_le_exp.2 (by linarith)
    have he1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    have h6 : Real.exp (-2) ≤ 1 / 5 := by
      rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (by positivity)]
      nlinarith
    linarith
  have h2 : Real.tanh (s * 1) - 1 < 0 := by
    have := Real.tanh_lt_one (s * 1); linarith
  have key : (0 : ℝ) ∈ Set.Ioo (Real.tanh (s * 1) - 1)
      (Real.tanh (s * (1 / 2)) - 1 / 2) := ⟨h2, h1⟩
  have := intermediate_value_Ioo' (by norm_num : (1 / 2 : ℝ) ≤ 1) hcont key
  obtain ⟨b, hb, hfb⟩ := this
  exact ⟨b, hb, by linarith [sub_eq_zero.1 hfb]⟩

/-- Uniqueness of the root `a_s` ("`a_s` the unique root", eq:roots). -/
theorem root_a_unique {s a a' : ℝ} (hs : 0 < s) (ha : 0 ≤ a) (ha' : 0 ≤ a')
    (h1 : fs s a = 1) (h2 : fs s a' = 1) : a = a' :=
  (fs_strictMonoOn hs).injOn ha ha' (h1.trans h2.symm)

/-- `b coth(s b) = 1 ↔ b = tanh(s b)` for `b > 0` ("The second equation
is equivalent to `b_s = tanh(s b_s)`", §3). -/
theorem gs_eq_one_iff {s b : ℝ} (hs : 0 < s) (hb : 0 < b) :
    gs s b = 1 ↔ Real.tanh (s * b) = b := by
  have hsb : 0 < Real.sinh (s * b) := Real.sinh_pos_iff.2 (by positivity)
  have hcb : 0 < Real.cosh (s * b) := Real.cosh_pos _
  rw [gs, Real.tanh_eq_sinh_div_cosh, div_eq_one_iff_eq hsb.ne',
    div_eq_iff hcb.ne']
  constructor <;> intro h <;> linarith

/-- Uniqueness of the root `b_s` (eq:roots). -/
theorem root_b_unique {s b b' : ℝ} (hs : 0 < s) (hb : 0 < b) (hb' : 0 < b')
    (h1 : Real.tanh (s * b) = b) (h2 : Real.tanh (s * b') = b') : b = b' := by
  apply (gs_strictMonoOn hs).injOn (Set.mem_Ioi.2 hb) (Set.mem_Ioi.2 hb')
  rw [(gs_eq_one_iff hs hb).2 h1, (gs_eq_one_iff hs hb').2 h2]

/-! ## §4 of the paper, Lemma `lem:scalar`: the scalar inequality

Throughout, `E = e^{-2s}`.  The paper's second-order expansions
(eq:deltaexp, eq:epsilonexp) are replaced by the equivalent explicit
inequalities `δ_s ≤ 2E + 8E²` and `ε_s ≥ 2E + 4sE² - 8E²`; these carry
exactly the information the sign computation (eq:sign) uses. -/

theorem eight_mul_le_exp {s : ℝ} (hs : 28 ≤ s) : 8 * s ≤ Real.exp s := by
  have h1 : s / 2 + 1 ≤ Real.exp (s / 2) := Real.add_one_le_exp (s / 2)
  have h2 : Real.exp (s / 2) * Real.exp (s / 2) = Real.exp s := by
    rw [← Real.exp_add]; ring_nf
  have h3 : (s / 2 + 1) * (s / 2 + 1) ≤ Real.exp (s / 2) * Real.exp (s / 2) :=
    mul_self_le_mul_self (by linarith) h1
  nlinarith

theorem exp_le_two {x : ℝ} (_h0 : 0 ≤ x) (h : x ≤ 1 / 2) : Real.exp x ≤ 2 := by
  have h1 : 1 - x ≤ Real.exp (-x) := by
    have := Real.add_one_le_exp (-x); linarith
  have h2 : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos x, mul_le_mul_of_nonneg_left h1 (Real.exp_pos x).le]

/-- Base bound for the Neumann root: `δ_s / (2 + δ_s) = E e^{-2sδ_s}`
(eq:exactroots) gives `a_s - 1 ≤ 2 a_s E`. -/
theorem delta_le_base {s a : ℝ} (hs : 1 ≤ s) (ha1 : 1 < a) (ha2 : a < 2)
    (heq : fs s a = 1) : a - 1 ≤ 2 * a * Real.exp (-(2 * s)) := by
  have hane : a ≠ 0 := by linarith
  rw [fs] at heq
  have htanh : Real.tanh (s * a) = 1 / a := by
    rw [eq_div_iff hane, mul_comm]; exact heq
  have hb := one_sub_tanh_le (s * a)
  rw [htanh] at hb
  have hexp : Real.exp (-(2 * (s * a))) ≤ Real.exp (-(2 * s)) :=
    Real.exp_le_exp.2 (by nlinarith)
  have h3 : 1 - 1 / a ≤ 2 * Real.exp (-(2 * s)) := by linarith
  have h4 : a * (1 - 1 / a) = a - 1 := by field_simp
  have h5 := mul_le_mul_of_nonneg_left h3 (by linarith : (0 : ℝ) ≤ a)
  rw [h4] at h5
  linarith

/-- `δ_s < 4E` (§4: "gives `0 < δ_s, ε_s < 4E` for all large `s`"). -/
theorem delta_le_4E {s a : ℝ} (hs : 1 ≤ s) (ha1 : 1 < a) (ha2 : a < 2)
    (heq : fs s a = 1) : a - 1 ≤ 4 * Real.exp (-(2 * s)) := by
  have := delta_le_base hs ha1 ha2 heq
  nlinarith [Real.exp_pos (-(2 * s))]

/-- Second-order upper bound `δ_s ≤ 2E + 8E²` (the upper half of
eq:deltaexp). -/
theorem delta_le {s a : ℝ} (hs : 1 ≤ s) (ha1 : 1 < a) (ha2 : a < 2)
    (heq : fs s a = 1) :
    a - 1 ≤ 2 * Real.exp (-(2 * s)) + 8 * Real.exp (-(2 * s)) ^ 2 := by
  have h1 := delta_le_base hs ha1 ha2 heq
  have h2 := delta_le_4E hs ha1 ha2 heq
  nlinarith [Real.exp_pos (-(2 * s))]

/-- `ε_s < 4E` (§4). -/
theorem eps_le_4E {s b : ℝ} (hs : 28 ≤ s) (hb1 : 1 / 2 < b) (hb2 : b < 1)
    (heq : Real.tanh (s * b) = b) : 1 - b ≤ 4 * Real.exp (-(2 * s)) := by
  have h1 := one_sub_tanh_le (s * b)
  rw [heq] at h1
  have e1 : Real.exp (-(2 * (s * b))) ≤ Real.exp (-s) :=
    Real.exp_le_exp.2 (by nlinarith)
  have step1 : 1 - b ≤ 2 * Real.exp (-s) := by linarith
  have e2 : -(2 * (s * b)) ≤ -(2 * s) + 4 * s * Real.exp (-s) := by
    nlinarith [mul_le_mul_of_nonneg_left step1 (by linarith : (0 : ℝ) ≤ s)]
  have e3 : Real.exp (-(2 * (s * b)))
      ≤ Real.exp (-(2 * s)) * Real.exp (4 * s * Real.exp (-s)) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.2 e2
  have e4 : 4 * s * Real.exp (-s) ≤ 1 / 2 := by
    have h8 := eight_mul_le_exp hs
    have hprod : Real.exp s * Real.exp (-s) = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-s), mul_le_mul_of_nonneg_right h8 (Real.exp_pos (-s)).le]
  have e5 : Real.exp (4 * s * Real.exp (-s)) ≤ 2 :=
    exp_le_two (by positivity) e4
  have hE : 0 < Real.exp (-(2 * s)) := Real.exp_pos _
  nlinarith [mul_le_mul_of_nonneg_left e5 hE.le]

/-- Second-order lower bound `ε_s ≥ 2E + 4sE² - 8E²` (the lower half of
eq:epsilonexp). -/
theorem eps_ge {s b : ℝ} (hs : 28 ≤ s) (hb1 : 1 / 2 < b) (hb2 : b < 1)
    (heq : Real.tanh (s * b) = b) :
    2 * Real.exp (-(2 * s)) + 4 * s * Real.exp (-(2 * s)) ^ 2
        - 8 * Real.exp (-(2 * s)) ^ 2 ≤ 1 - b := by
  have hE : 0 < Real.exp (-(2 * s)) := Real.exp_pos _
  have heps4 := eps_le_4E hs hb1 hb2 heq
  have h1 := le_one_sub_tanh' (s * b)
  rw [heq] at h1
  have hsplit : Real.exp (-(2 * (s * b)))
      = Real.exp (-(2 * s)) * Real.exp (2 * s * (1 - b)) := by
    rw [← Real.exp_add]; ring_nf
  rw [hsplit] at h1
  have hXpos : 0 < Real.exp (2 * s * (1 - b)) := Real.exp_pos _
  have hX1 : 1 + 2 * s * (1 - b) ≤ Real.exp (2 * s * (1 - b)) := by
    have := Real.add_one_le_exp (2 * s * (1 - b)); linarith
  -- `2s(1-b) ≤ 8sE ≤ e^{-s} ≤ 1/2`, hence `X ≤ 2`
  have h8E : 8 * s * Real.exp (-(2 * s)) ≤ 1 / 2 := by
    have h8 := eight_mul_le_exp hs
    have hprod : Real.exp s * Real.exp (-(2 * s)) = Real.exp (-s) := by
      rw [← Real.exp_add]; ring_nf
    have hles : Real.exp (-s) ≤ 1 / 2 := by
      have e1 : Real.exp (-s) ≤ Real.exp (-2) := Real.exp_le_exp.2 (by linarith)
      have he1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
      have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      have e2 : Real.exp (-2) ≤ 1 / 2 := by
        rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (by positivity)]
        nlinarith
      linarith
    nlinarith [mul_le_mul_of_nonneg_right h8 hE.le]
  have hX2 : Real.exp (2 * s * (1 - b)) ≤ 2 := by
    apply exp_le_two (by nlinarith)
    nlinarith [mul_le_mul_of_nonneg_left heps4 (by linarith : (0 : ℝ) ≤ 2 * s)]
  have hEX_le : Real.exp (-(2 * s)) * Real.exp (2 * s * (1 - b))
      ≤ 2 * Real.exp (-(2 * s)) := by
    nlinarith [mul_le_mul_of_nonneg_left hX2 hE.le]
  have hEX_pos : 0 < Real.exp (-(2 * s)) * Real.exp (2 * s * (1 - b)) :=
    mul_pos hE hXpos
  have hEX_half : Real.exp (-(2 * s)) * Real.exp (2 * s * (1 - b)) ≤ 1 / 2 := by
    have hE5 : Real.exp (-(2 * s)) ≤ 1 / 5 := by
      have e1 : Real.exp (-(2 * s)) ≤ Real.exp (-2) :=
        Real.exp_le_exp.2 (by linarith)
      have he1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
      have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      have e2 : Real.exp (-2) ≤ 1 / 5 := by
        rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (by positivity)]
        nlinarith
      linarith
    linarith [hEX_le]
  -- `ε ≥ E`
  have hgeE : Real.exp (-(2 * s)) ≤ 1 - b := by
    have hXge1 : 1 ≤ Real.exp (2 * s * (1 - b)) := by
      have : (0 : ℝ) ≤ 2 * s * (1 - b) := by nlinarith
      nlinarith [hX1]
    have hEXgeE : Real.exp (-(2 * s))
        ≤ Real.exp (-(2 * s)) * Real.exp (2 * s * (1 - b)) := by
      nlinarith [mul_le_mul_of_nonneg_left hXge1 hE.le]
    nlinarith [h1, hEX_half, hEX_pos]
  -- assemble: `ε ≥ 2EX - 2(EX)² ≥ 2E(1 + 2sε) - 8E² ≥ 2E + 4sE² - 8E²`
  have t1 : 2 * Real.exp (-(2 * s)) + 4 * s * Real.exp (-(2 * s)) * (1 - b)
      ≤ 2 * (Real.exp (-(2 * s)) * Real.exp (2 * s * (1 - b))) := by
    nlinarith [mul_le_mul_of_nonneg_left hX1 hE.le]
  have t2 : (Real.exp (-(2 * s)) * Real.exp (2 * s * (1 - b))) ^ 2
      ≤ 4 * Real.exp (-(2 * s)) ^ 2 := by
    nlinarith [hEX_le, hEX_pos]
  have t3 : 4 * s * Real.exp (-(2 * s)) * Real.exp (-(2 * s))
      ≤ 4 * s * Real.exp (-(2 * s)) * (1 - b) := by
    apply mul_le_mul_of_nonneg_left hgeE
    positivity
  nlinarith [h1, t1, t2, t3]

/-- Quadratic binomial upper bound `(1+δ)^q ≤ 1 + qδ + q²δ²` for
`qδ ≤ 1` (used in the binomial expansion step of eq:sign). -/
theorem pow_one_add_le {δ : ℝ} (hδ : 0 ≤ δ) :
    ∀ q : ℕ, (q : ℝ) * δ ≤ 1 →
      (1 + δ) ^ q ≤ 1 + (q : ℝ) * δ + (q : ℝ) ^ 2 * δ ^ 2 := by
  intro q
  induction q with
  | zero => intro _; norm_num
  | succ q ih =>
      intro h
      have hqc : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
      have hq : (q : ℝ) * δ ≤ 1 := by
        push_cast at h
        nlinarith
      have ihq := ih hq
      have hmul : (1 + δ) ^ (q + 1)
          ≤ (1 + (q : ℝ) * δ + (q : ℝ) ^ 2 * δ ^ 2) * (1 + δ) := by
        rw [pow_succ]
        exact mul_le_mul_of_nonneg_right ihq (by linarith)
      have hcube : (q : ℝ) ^ 2 * δ ^ 3 ≤ (q : ℝ) * δ ^ 2 := by
        have h1 : (q : ℝ) * δ * ((q : ℝ) * δ ^ 2) ≤ 1 * ((q : ℝ) * δ ^ 2) :=
          mul_le_mul_of_nonneg_right hq (by positivity)
        nlinarith
      push_cast
      nlinarith [hmul, hcube]

/-- Quadratic binomial upper bound `(1-ε)^q ≤ 1 - qε + q²ε²` for
`0 ≤ ε ≤ 1` (used in the binomial expansion step of eq:sign). -/
theorem pow_one_sub_le {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ∀ q : ℕ, (1 - ε) ^ q ≤ 1 - (q : ℝ) * ε + (q : ℝ) ^ 2 * ε ^ 2 := by
  intro q
  induction q with
  | zero => norm_num
  | succ q ih =>
      have hqc : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
      have hmul : (1 - ε) ^ (q + 1)
          ≤ (1 - (q : ℝ) * ε + (q : ℝ) ^ 2 * ε ^ 2) * (1 - ε) := by
        rw [pow_succ]
        exact mul_le_mul_of_nonneg_right ih (by linarith)
      have hcube : (0 : ℝ) ≤ (q : ℝ) ^ 2 * ε ^ 2 * ε := by positivity
      push_cast
      nlinarith [hmul, hcube]

/-- **Lemma `lem:scalar`** (quantitative form): for `q ≥ 2`,
`s ≥ 16q + 28`, the roots of eq:roots satisfy `a_s^q + b_s^q < 2`. -/
theorem scalar_inequality {q : ℕ} (hq : 2 ≤ q) {s a b : ℝ}
    (hs : 16 * (q : ℝ) + 28 ≤ s)
    (ha1 : 1 < a) (ha2 : a < 2) (haeq : fs s a = 1)
    (hb1 : 1 / 2 < b) (hb2 : b < 1) (hbeq : Real.tanh (s * b) = b) :
    a ^ q + b ^ q < 2 := by
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hs28 : (28 : ℝ) ≤ s := by nlinarith
  have hs1 : (1 : ℝ) ≤ s := by linarith
  have hE : 0 < Real.exp (-(2 * s)) := Real.exp_pos _
  have hδ4 := delta_le_4E hs1 ha1 ha2 haeq
  have hδ := delta_le hs1 ha1 ha2 haeq
  have hε4 := eps_le_4E hs28 hb1 hb2 hbeq
  have hε := eps_ge hs28 hb1 hb2 hbeq
  -- `8sE ≤ 1`, hence `q(a-1) ≤ 4qE ≤ 4sE ≤ 1`
  have h8E : 8 * s * Real.exp (-(2 * s)) ≤ 1 := by
    have h8 := eight_mul_le_exp hs28
    have hprod : Real.exp s * Real.exp (-(2 * s)) = Real.exp (-s) := by
      rw [← Real.exp_add]; ring_nf
    have hle1 : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    nlinarith [mul_le_mul_of_nonneg_right h8 hE.le]
  have hqs : (q : ℝ) ≤ s := by nlinarith
  have hqE : (q : ℝ) * (a - 1) ≤ 1 := by
    have t := mul_le_mul_of_nonneg_left hδ4 (by positivity : (0 : ℝ) ≤ (q : ℝ))
    nlinarith [mul_le_mul_of_nonneg_right hqs (by positivity : (0 : ℝ) ≤ 4 * Real.exp (-(2 * s)))]
  -- binomial bounds
  have hA : a ^ q ≤ 1 + (q : ℝ) * (a - 1) + (q : ℝ) ^ 2 * (a - 1) ^ 2 := by
    have h := pow_one_add_le (by linarith : (0 : ℝ) ≤ a - 1) q hqE
    have e : (1 : ℝ) + (a - 1) = a := by ring
    rwa [e] at h
  have hB : b ^ q ≤ 1 - (q : ℝ) * (1 - b) + (q : ℝ) ^ 2 * (1 - b) ^ 2 := by
    have h := pow_one_sub_le (by linarith : (0 : ℝ) ≤ 1 - b)
      (by linarith : 1 - b ≤ 1) q
    have e : (1 : ℝ) - (1 - b) = b := by ring
    rwa [e] at h
  -- square bounds
  have hδsq : (a - 1) ^ 2 ≤ 16 * Real.exp (-(2 * s)) ^ 2 := by
    nlinarith
  have hεsq : (1 - b) ^ 2 ≤ 16 * Real.exp (-(2 * s)) ^ 2 := by
    nlinarith
  -- the gap: `δ - ε ≤ -(4s - 24) E²`
  have hgap : (a - 1) - (1 - b)
      ≤ -(4 * s * Real.exp (-(2 * s)) ^ 2) + 16 * Real.exp (-(2 * s)) ^ 2 := by
    linarith
  have t1 := mul_le_mul_of_nonneg_left hgap (by positivity : (0 : ℝ) ≤ (q : ℝ))
  have t2 := mul_le_mul_of_nonneg_left hδsq (by positivity : (0 : ℝ) ≤ (q : ℝ) ^ 2)
  have t3 := mul_le_mul_of_nonneg_left hεsq (by positivity : (0 : ℝ) ≤ (q : ℝ) ^ 2)
  -- positivity of the total gap coefficient
  have hEsq : 0 < Real.exp (-(2 * s)) ^ 2 := by positivity
  have hcoef : 32 * (q : ℝ) + 16 < 4 * s := by nlinarith
  have t4 : (q : ℝ) * (32 * (q : ℝ) + 16) * Real.exp (-(2 * s)) ^ 2
      < (q : ℝ) * (4 * s) * Real.exp (-(2 * s)) ^ 2 := by
    apply mul_lt_mul_of_pos_right _ hEsq
    apply mul_lt_mul_of_pos_left hcoef (by positivity)
  nlinarith [t1, t2, t3, t4, hA, hB]

/-! ## §3 of the paper: the coupled branch limit (Lemma `lem:limits`)

At the coupled scale `R_i = e^{s/i}`, `L_i = 2(e^{s/i} - 1)` (eq:scale)
the rescaled branches converge to `f_s` and `g_s`. -/

/-- The coupled scale `R_i = e^{s/i}` (eq:scale). -/
noncomputable def Ri (s : ℝ) (i : ℕ) : ℝ := Real.exp (s / i)

/-- The coupled length `L_i = 2(e^{s/i} - 1)` (eq:scale). -/
noncomputable def Li (s : ℝ) (i : ℕ) : ℝ := 2 * (Real.exp (s / i) - 1)

theorem Ri_eq (s : ℝ) (i : ℕ) : Ri s i = 1 + Li s i / 2 := by
  rw [Ri, Li]; ring

theorem one_lt_Ri {s : ℝ} (hs : 0 < s) {i : ℕ} (hi : 1 ≤ i) : 1 < Ri s i := by
  rw [Ri, ← Real.exp_zero]
  apply Real.exp_lt_exp.2
  have : (0 : ℝ) < i := by exact_mod_cast hi
  positivity

/-- `tanh y = (e^{2y} - 1)/(e^{2y} + 1)`. -/
theorem tanh_eq_exp' (y : ℝ) :
    Real.tanh y = (Real.exp (2 * y) - 1) / (Real.exp (2 * y) + 1) := by
  rw [tanh_eq_exp]
  have h1 : Real.exp (-(2 * y)) = (Real.exp (2 * y))⁻¹ := Real.exp_neg _
  have h2 : (0 : ℝ) < Real.exp (2 * y) := Real.exp_pos _
  rw [h1]
  rw [div_eq_div_iff (by positivity) (by positivity)]
  field_simp

/-- Lemma `lem:limits`, eq:glimit for `x > 0`: if `j_i/i → x` then
`D_{j_i}(R_i)/i → g_s(x) = x coth(sx)`. -/
theorem Db_coupled_limit {ν s x : ℝ} (hν : 0 < ν) (hs : 0 < s) (hx : 0 < x)
    (j : ℕ → ℝ) (hj : ∀ i, 0 ≤ j i)
    (hlim : Tendsto (fun i : ℕ => j i / i) atTop (𝓝 x)) :
    Tendsto (fun i : ℕ => Db ν (j i) (Ri s i) / i) atTop (𝓝 (gs s x)) := by
  -- the argument of `phi`
  have harg : Tendsto (fun i : ℕ => s * (j i / i) + s * (ν / 2) * (1 / i))
      atTop (𝓝 (s * x)) := by
    have h1 : Tendsto (fun i : ℕ => s * (j i / i)) atTop (𝓝 (s * x)) :=
      (tendsto_const_nhds.mul hlim)
    have h2 : Tendsto (fun i : ℕ => s * (ν / 2) * (1 / i)) atTop (𝓝 0) := by
      have := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
      simpa using tendsto_const_nhds.mul this
    simpa using h1.add h2
  have hphi : Tendsto (fun i : ℕ =>
      phi (s * (j i / i) + s * (ν / 2) * (1 / i))) atTop (𝓝 (phi (s * x))) := by
    have hc : ContinuousAt phi (s * x) :=
      (phi_hasDerivAt (mul_pos hs hx).ne').continuousAt
    exact hc.tendsto.comp harg
  have hmain : Tendsto (fun i : ℕ =>
      ν / 2 * (1 / i) + phi (s * (j i / i) + s * (ν / 2) * (1 / i)) / s)
      atTop (𝓝 (0 + phi (s * x) / s)) := by
    apply Tendsto.add
    · have := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
      simpa using tendsto_const_nhds.mul this
    · exact hphi.div_const s
  rw [gs_eq_phi hs.ne', ← zero_add (phi (s * x) / s)]
  apply hmain.congr'
  filter_upwards [eventually_ge_atTop 1] with i hi
  have hipos : (0 : ℝ) < i := by exact_mod_cast hi
  have hRi : 1 < Ri s i := one_lt_Ri hs hi
  rw [Db_eq_phi hν (hj i) hRi]
  rw [Ri, Real.log_exp]
  have e1 : s / i * (j i + ν / 2) = s * (j i / i) + s * (ν / 2) * (1 / i) := by
    field_simp
  rw [e1]
  field_simp

/-- Lemma `lem:limits`, eq:glimit at `x = 0`: the convention
`g_s(0) = 1/s`; in particular `D_0(R_i)/i → 1/s` ("At `x = 0`, the
Dirichlet formula gives `D_0(R_i)/i → 1/s`"). -/
theorem Db_coupled_limit_zero {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s)
    (j : ℕ → ℝ) (hj : ∀ i, 0 ≤ j i)
    (hlim : Tendsto (fun i : ℕ => j i / i) atTop (𝓝 0)) :
    Tendsto (fun i : ℕ => Db ν (j i) (Ri s i) / i) atTop (𝓝 (1 / s)) := by
  have harg : Tendsto (fun i : ℕ => s * (j i / i) + s * (ν / 2) * (1 / i))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun i : ℕ => s * (j i / i)) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul hlim)
    have h2 : Tendsto (fun i : ℕ => s * (ν / 2) * (1 / i)) atTop (𝓝 0) := by
      have := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
      simpa using tendsto_const_nhds.mul this
    simpa using h1.add h2
  have hargIn : Tendsto (fun i : ℕ => s * (j i / i) + s * (ν / 2) * (1 / i))
      atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ harg
    filter_upwards [eventually_ge_atTop 1] with i hi
    have hipos : (0 : ℝ) < i := by exact_mod_cast hi
    have h1 : 0 ≤ s * (j i / i) :=
      mul_nonneg hs.le (div_nonneg (hj i) hipos.le)
    have h2 : 0 < s * (ν / 2) * (1 / i) :=
      mul_pos (mul_pos hs (half_pos hν)) (one_div_pos.2 hipos)
    exact Set.mem_Ioi.2 (by linarith)
  have hphi : Tendsto (fun i : ℕ =>
      phi (s * (j i / i) + s * (ν / 2) * (1 / i))) atTop (𝓝 1) :=
    phi_tendsto_one.comp hargIn
  have hmain : Tendsto (fun i : ℕ =>
      ν / 2 * (1 / i) + phi (s * (j i / i) + s * (ν / 2) * (1 / i)) / s)
      atTop (𝓝 (0 + 1 / s)) := by
    apply Tendsto.add
    · have := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
      simpa using tendsto_const_nhds.mul this
    · exact hphi.div_const s
  rw [← zero_add (1 / s)]
  apply hmain.congr'
  filter_upwards [eventually_ge_atTop 1] with i hi
  have hipos : (0 : ℝ) < i := by exact_mod_cast hi
  have hRi : 1 < Ri s i := one_lt_Ri hs hi
  rw [Db_eq_phi hν (hj i) hRi]
  rw [Ri, Real.log_exp]
  have e1 : s / i * (j i + ν / 2) = s * (j i / i) + s * (ν / 2) * (1 / i) := by
    field_simp
  rw [e1]
  field_simp

/-- Lemma `lem:limits`, eq:flimit for `x > 0`: if `j_i/i → x` then
`N_{j_i}(R_i)/i → f_s(x) = x tanh(sx)`. -/
theorem Nb_coupled_limit {ν s x : ℝ} (hν : 0 < ν) (hs : 0 < s) (hx : 0 < x)
    (j : ℕ → ℝ) (hj : ∀ i, 0 ≤ j i)
    (hlim : Tendsto (fun i : ℕ => j i / i) atTop (𝓝 x)) :
    Tendsto (fun i : ℕ => Nb ν (j i) (Ri s i) / i) atTop (𝓝 (fs s x)) := by
  set U : ℝ := Real.exp (2 * s * x) with hU
  have hUpos : 0 < U := Real.exp_pos _
  have hone : Tendsto (fun i : ℕ => ν * (1 / (i : ℝ))) atTop (𝓝 0) := by
    have := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa using tendsto_const_nhds.mul this
  have hexp : Tendsto (fun i : ℕ => Real.exp (2 * s * (j i / i) + s * ν * (1 / i)))
      atTop (𝓝 U) := by
    apply Real.continuous_exp.continuousAt.tendsto.comp
    have h1 : Tendsto (fun i : ℕ => 2 * s * (j i / i)) atTop (𝓝 (2 * s * x)) :=
      tendsto_const_nhds.mul hlim
    have h2 : Tendsto (fun i : ℕ => s * ν * (1 / (i : ℝ))) atTop (𝓝 0) := by
      have := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
      simpa using tendsto_const_nhds.mul this
    simpa using h1.add h2
  have hnum : Tendsto (fun i : ℕ =>
      (j i / i) * (j i / i + ν * (1 / i)) *
        (Real.exp (2 * s * (j i / i) + s * ν * (1 / i)) - 1))
      atTop (𝓝 (x * (x + 0) * (U - 1))) :=
    (hlim.mul (hlim.add hone)).mul (hexp.sub tendsto_const_nhds)
  rw [add_zero] at hnum
  have hden : Tendsto (fun i : ℕ =>
      (j i / i) * Real.exp (2 * s * (j i / i) + s * ν * (1 / i)) +
        (j i / i) + ν * (1 / i))
      atTop (𝓝 (x * U + x + 0)) :=
    ((hlim.mul hexp).add hlim).add hone
  rw [add_zero] at hden
  have hdenne : x * U + x ≠ 0 := by
    have : 0 < x * U + x := by nlinarith
    exact this.ne'
  have hquot := hnum.div hden hdenne
  have hval : x * x * (U - 1) / (x * U + x) = fs s x := by
    rw [fs, tanh_eq_exp']
    have e1 : 2 * (s * x) = 2 * s * x := by ring
    rw [e1, ← hU]
    have hd2 : U + 1 ≠ 0 := by nlinarith
    field_simp
  rw [hval] at hquot
  apply hquot.congr'
  filter_upwards [eventually_ge_atTop 1] with i hi
  have hipos : (0 : ℝ) < i := by exact_mod_cast hi
  have hRi : 1 < Ri s i := one_lt_Ri hs hi
  have hu : upow ν (j i) (Ri s i)
      = Real.exp (2 * s * (j i / i) + s * ν * (1 / i)) := by
    rw [upow, Ri, ← Real.exp_log (show (0 : ℝ) < Real.exp (s / i) from Real.exp_pos _)]
    rw [Real.log_exp, ← Real.exp_mul]
    congr 1
    field_simp
  rw [Pi.div_apply, Nb, Nv, hu]
  have hupos : (0 : ℝ) < Real.exp (2 * s * (j i / i) + s * ν * (1 / i)) :=
    Real.exp_pos _
  have hdpos : 0 < j i * Real.exp (2 * s * (j i / i) + s * ν * (1 / i)) + j i + ν := by
    have := hj i
    nlinarith
  have hBpos : 0 < (j i / i) * Real.exp (2 * s * (j i / i) + s * ν * (1 / i))
      + (j i / i) + ν * (1 / i) := by
    have h1 : 0 ≤ (j i / i) * Real.exp (2 * s * (j i / i) + s * ν * (1 / i)) :=
      mul_nonneg (div_nonneg (hj i) hipos.le) hupos.le
    have h2 : 0 ≤ j i / i := div_nonneg (hj i) hipos.le
    have h3 : 0 < ν * (1 / (i : ℝ)) := by positivity
    linarith
  have hine : (i : ℝ) ≠ 0 := hipos.ne'
  rw [div_div, div_eq_div_iff hBpos.ne' (by positivity)]
  field_simp

/-! ## The Métras–Tschanz profile as a weighted order statistic (§1–2)

For `n = p + 2` and Steklov index `k ≥ 1`, put `ℓ₀ = max{ℓ : S_ℓ ≤ k}`
and form the weighted multiset `{D_0,…,D_{ℓ₀}, N_1,…,N_{ℓ₀+1}}`
(eq:multiset), every degree `j` occurring with weight `m_j`.  The
sharp-bound profile `B_n^k(L)` is its k-th smallest element, which we
realize by the Ky Fan min-max formula `min_{|T|=k} max T` over
sub-multisets; this transcription of the Métras–Tschanz extension
process makes both the counting arguments and the continuity of the
profile fully formalizable. -/

/-- `ℓ₀ = max{ℓ : S_ℓ ≤ k}` (§2). -/
def ell0 (p k : ℕ) : ℕ := Nat.findGreatest (fun ℓ => cumMult p ℓ ≤ k) k

theorem mult_zero {p : ℕ} (hp : 1 ≤ p) : mult p 0 = 1 := by
  rw [mult, show 0 + p = p by omega]
  rw [Nat.choose_self, Nat.choose_eq_zero_of_lt (by omega : p - 1 < p)]

theorem cumMult_zero {p : ℕ} (hp : 1 ≤ p) : cumMult p 0 = 1 := by
  simpa [cumMult] using mult_zero hp

theorem cumMult_ell0_le {p k : ℕ} (hp : 1 ≤ p) (hk : 1 ≤ k) :
    cumMult p (ell0 p k) ≤ k := by
  have h0 : cumMult p 0 ≤ k := by rw [cumMult_zero hp]; omega
  exact Nat.findGreatest_spec (P := fun ℓ => cumMult p ℓ ≤ k) (Nat.zero_le k) h0

theorem ell0_le (p k : ℕ) : ell0 p k ≤ k := Nat.findGreatest_le k

theorem lt_cumMult_ell0_succ (p k : ℕ) : k < cumMult p (ell0 p k + 1) := by
  rcases Nat.lt_or_ge (ell0 p k) k with h | h
  · have hng : ¬ (cumMult p (ell0 p k + 1) ≤ k) :=
      Nat.findGreatest_is_greatest (P := fun ℓ => cumMult p ℓ ≤ k) (n := k)
        (Nat.lt_succ_self (ell0 p k)) (by omega)
    omega
  · have h1 : ell0 p k = k := le_antisymm (ell0_le p k) h
    rw [h1]
    have h2 := lt_cumMult p (k + 1)
    omega

/-- The weighted multiset of branch functions (eq:multiset), each
degree `j` with weight `m_j`; the branches are evaluated at
`R = 1 + L/2`. -/
noncomputable def branchFuns (p k : ℕ) : Multiset (ℝ → ℝ) :=
  ((Multiset.range (ell0 p k + 1)).bind fun j =>
    Multiset.replicate (mult p j) fun L => Db p j (1 + L / 2)) +
  ((Multiset.range (ell0 p k + 1)).bind fun j =>
    Multiset.replicate (mult p (j + 1)) fun L => Nb p (j + 1) (1 + L / 2))

/-- The multiset of branch values at meridian length `L`. -/
noncomputable def branchVals (p k : ℕ) (L : ℝ) : Multiset ℝ :=
  (branchFuns p k).map fun f => f L

theorem sum_range_mult (p n : ℕ) :
    ((Multiset.range (n + 1)).map fun j => mult p j).sum = cumMult p n := rfl

theorem sum_range_mult_shift {p : ℕ} (hp : 1 ≤ p) (n : ℕ) :
    ((Multiset.range (n + 1)).map fun j => mult p (j + 1)).sum + 1
      = cumMult p (n + 1) := by
  have h1 : ((Multiset.range (n + 1)).map fun j => mult p (j + 1)).sum
      = ∑ j ∈ Finset.range (n + 1), mult p (j + 1) := rfl
  rw [h1, cumMult, Finset.sum_range_succ' (fun j => mult p j) (n + 1),
    mult_zero hp]

/-- The cardinality of eq:multiset: `S_{ℓ₀} + (S_{ℓ₀+1} - 1)`. -/
theorem card_branchVals {p : ℕ} (hp : 1 ≤ p) (k : ℕ) (L : ℝ) :
    Multiset.card (branchVals p k L) + 1
      = cumMult p (ell0 p k) + cumMult p (ell0 p k + 1) := by
  rw [branchVals, Multiset.card_map, branchFuns, Multiset.card_add,
    Multiset.card_bind, Multiset.card_bind]
  have e1 : ((Multiset.range (ell0 p k + 1)).map
      (Multiset.card ∘ fun j =>
        Multiset.replicate (mult p j) fun L => Db p j (1 + L / 2))).sum
      = cumMult p (ell0 p k) := by
    rw [← sum_range_mult p (ell0 p k)]
    congr 1
    apply Multiset.map_congr rfl
    intro j _
    simp [Multiset.card_replicate]
  have e2 : ((Multiset.range (ell0 p k + 1)).map
      (Multiset.card ∘ fun j =>
        Multiset.replicate (mult p (j + 1)) fun L => Nb p (j + 1) (1 + L / 2))).sum + 1
      = cumMult p (ell0 p k + 1) := by
    rw [← sum_range_mult_shift hp (ell0 p k)]
    congr 2
    apply Multiset.map_congr rfl
    intro j _
    simp [Multiset.card_replicate]
  omega

/-- The index `k` fits inside the multiset (needed for the order
statistic to exist): `k ≤ card` (from `S_{ℓ₀+1} ≥ k + 1`). -/
theorem le_card_branchVals {p : ℕ} (hp : 1 ≤ p) (k : ℕ) (L : ℝ) :
    k ≤ Multiset.card (branchVals p k L) := by
  have h1 := card_branchVals hp k L
  have h2 := lt_cumMult_ell0_succ p k
  have h3 : 1 ≤ cumMult p (ell0 p k) := by
    have hm := (cumMult_strictMono p).monotone (Nat.zero_le (ell0 p k))
    rw [cumMult_zero hp] at hm
    exact hm
  omega

/-! ### Fold-max / fold-min helpers for the order statistic -/

/-- Max of a multiset of reals, with default `0`. -/
noncomputable def msMax (T : Multiset ℝ) : ℝ := T.fold max 0

theorem le_msMax {T : Multiset ℝ} {a : ℝ} (h : a ∈ T) : a ≤ msMax T := by
  induction T using Multiset.induction_on with
  | empty => simp at h
  | cons b T ih =>
      rw [msMax, Multiset.fold_cons_left]
      rcases Multiset.mem_cons.1 h with rfl | h'
      · exact le_max_left _ _
      · exact le_trans (ih h') (le_max_right _ _)

theorem msMax_le {T : Multiset ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ a ∈ T, a ≤ c) : msMax T ≤ c := by
  induction T using Multiset.induction_on with
  | empty => simpa [msMax] using hc
  | cons b T ih =>
      rw [msMax, Multiset.fold_cons_left]
      exact max_le (h b (Multiset.mem_cons_self _ _))
        (ih fun a ha => h a (Multiset.mem_cons_of_mem ha))

theorem fold_min_le {M : Multiset ℝ} {D a : ℝ} (h : a ∈ M) :
    M.fold min D ≤ a := by
  induction M using Multiset.induction_on with
  | empty => simp at h
  | cons b M ih =>
      rw [Multiset.fold_cons_left]
      rcases Multiset.mem_cons.1 h with rfl | h'
      · exact min_le_left _ _
      · exact le_trans (min_le_right _ _) (ih h')

theorem fold_min_le_init (M : Multiset ℝ) (D : ℝ) : M.fold min D ≤ D := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons b M ih =>
      rw [Multiset.fold_cons_left]
      exact le_trans (min_le_right _ _) ih

theorem lt_fold_min {M : Multiset ℝ} {D c : ℝ} (hD : c < D)
    (h : ∀ a ∈ M, c < a) : c < M.fold min D := by
  induction M using Multiset.induction_on with
  | empty => simpa using hD
  | cons b M ih =>
      rw [Multiset.fold_cons_left]
      exact lt_min (h b (Multiset.mem_cons_self _ _))
        (ih fun a ha => h a (Multiset.mem_cons_of_mem ha))

theorem le_fold_min {M : Multiset ℝ} {D c : ℝ} (hD : c ≤ D)
    (h : ∀ a ∈ M, c ≤ a) : c ≤ M.fold min D := by
  induction M using Multiset.induction_on with
  | empty => simpa using hD
  | cons b M ih =>
      rw [Multiset.fold_cons_left]
      exact le_min (h b (Multiset.mem_cons_self _ _))
        (ih fun a ha => h a (Multiset.mem_cons_of_mem ha))

/-- **The sharp-bound profile `B_n^k(L)`** of Métras–Tschanz (§1): the
k-th weighted order statistic of the branch multiset (eq:multiset), in
min-max form. -/
noncomputable def profile (p k : ℕ) (L : ℝ) : ℝ :=
  (((branchVals p k L).powersetCard k).map msMax).fold min
    (msMax (branchVals p k L))

/-! ### The profile against a threshold: counting lemmas

These express that `profile p k` is the k-th smallest weighted branch
value; they encode the order-statistic mechanism used in
Lemma `lem:infinity` and in eq:overshoot. -/

/-- If at least `k` weighted branch values are `≤ T`, the k-th smallest
is `≤ T`. -/
theorem profile_le_of_count {p k : ℕ} {L T : ℝ} (hT : 0 ≤ T)
    (h : k ≤ Multiset.countP (fun x => x ≤ T) (branchVals p k L)) :
    profile p k L ≤ T := by
  set F := Multiset.filter (fun x => x ≤ T) (branchVals p k L) with hF
  have hcard : k ≤ Multiset.card F := by
    rw [hF, ← Multiset.countP_eq_card_filter]; exact h
  obtain ⟨T', hT'le, hT'card⟩ : ∃ T', T' ≤ F ∧ Multiset.card T' = k := by
    refine ⟨((F.toList.take k : List ℝ) : Multiset ℝ), ?_, ?_⟩
    · have h1 : ((F.toList.take k : List ℝ) : Multiset ℝ)
          ≤ (F.toList : Multiset ℝ) :=
        Multiset.coe_le.2 (F.toList.take_sublist k).subperm
      rwa [Multiset.coe_toList] at h1
    · rw [Multiset.coe_card, List.length_take, Multiset.length_toList]
      omega
  have hmem : T' ∈ (branchVals p k L).powersetCard k :=
    Multiset.mem_powersetCard.2
      ⟨le_trans hT'le (Multiset.filter_le _ _), hT'card⟩
  have h1 : msMax T' ≤ T := by
    apply msMax_le hT
    intro a ha
    have hmemF : a ∈ F := Multiset.mem_of_le hT'le ha
    rw [hF] at hmemF
    exact Multiset.of_mem_filter (p := fun x => x ≤ T) hmemF
  exact le_trans (fold_min_le (Multiset.mem_map_of_mem msMax hmem)) h1

/-- If fewer than `k` weighted branch values are `≤ T`, the k-th
smallest is `> T` (the mechanism of eq:overshoot). -/
theorem lt_profile_of_count {p k : ℕ} {L T : ℝ}
    (hk : k ≤ Multiset.card (branchVals p k L))
    (h : Multiset.countP (fun x => x ≤ T) (branchVals p k L) < k) :
    T < profile p k L := by
  have key : ∀ T' ≤ branchVals p k L, k ≤ Multiset.card T' →
      ∃ a ∈ T', T < a := by
    intro T' hle hcard
    by_contra hcon
    push Not at hcon
    have h1 : T' ≤ Multiset.filter (fun x => x ≤ T) (branchVals p k L) :=
      Multiset.le_filter.2 ⟨hle, hcon⟩
    have h2 := Multiset.card_le_card h1
    rw [← Multiset.countP_eq_card_filter] at h2
    omega
  apply lt_fold_min
  · obtain ⟨a, ha, hTa⟩ := key (branchVals p k L) le_rfl hk
    exact lt_of_lt_of_le hTa (le_msMax ha)
  · intro c hc
    obtain ⟨T', hT', rfl⟩ := Multiset.mem_map.1 hc
    obtain ⟨hle, hcard⟩ := Multiset.mem_powersetCard.1 hT'
    obtain ⟨a, ha, hTa⟩ := key T' hle (le_of_eq hcard.symm)
    exact lt_of_lt_of_le hTa (le_msMax ha)

/-- If fewer than `k` weighted branch values are `< T`, the k-th
smallest is `≥ T` (used for the exact identification in
Lemma `lem:infinity`). -/
theorem le_profile_of_count {p k : ℕ} {L T : ℝ}
    (hk : k ≤ Multiset.card (branchVals p k L))
    (h : Multiset.countP (fun x => x < T) (branchVals p k L) < k) :
    T ≤ profile p k L := by
  have key : ∀ T' ≤ branchVals p k L, k ≤ Multiset.card T' →
      ∃ a ∈ T', T ≤ a := by
    intro T' hle hcard
    by_contra hcon
    push Not at hcon
    have h1 : T' ≤ Multiset.filter (fun x => x < T) (branchVals p k L) :=
      Multiset.le_filter.2 ⟨hle, hcon⟩
    have h2 := Multiset.card_le_card h1
    rw [← Multiset.countP_eq_card_filter] at h2
    omega
  apply le_fold_min
  · obtain ⟨a, ha, hTa⟩ := key (branchVals p k L) le_rfl hk
    exact le_trans hTa (le_msMax ha)
  · intro c hc
    obtain ⟨T', hT', rfl⟩ := Multiset.mem_map.1 hc
    obtain ⟨hle, hcard⟩ := Multiset.mem_powersetCard.1 hT'
    obtain ⟨a, ha, hTa⟩ := key T' hle (le_of_eq hcard.symm)
    exact le_trans hTa (le_msMax ha)

/-! ### Continuity of the profile (§2: "Since (eq:multiset) is finite
and its branches are continuous, `B_n^k(L)` is continuous in `L`") -/

/-- Every function in the multiset eq:multiset is continuous on `(0,∞)`. -/
theorem branchFuns_continuousOn {p : ℕ} (hp : 1 ≤ p) (k : ℕ) :
    ∀ f ∈ branchFuns p k, ContinuousOn f (Set.Ioi 0) := by
  have hν : (0 : ℝ) < p := by exact_mod_cast hp
  have haff : ContinuousOn (fun L : ℝ => 1 + L / 2) (Set.Ioi 0) :=
    (continuous_const.add (continuous_id.div_const 2)).continuousOn
  intro f hf
  rw [branchFuns] at hf
  rcases Multiset.mem_add.1 hf with hf | hf
  · obtain ⟨j, _, hf⟩ := Multiset.mem_bind.1 hf
    rw [Multiset.eq_of_mem_replicate hf]
    have hmap : Set.MapsTo (fun L : ℝ => 1 + L / 2) (Set.Ioi 0) (Set.Ioi 1) := by
      intro L hL
      have := Set.mem_Ioi.1 hL
      exact Set.mem_Ioi.2 (by linarith)
    have := (continuousOn_Db (ν := p) (j := j) hν
      (by positivity)).comp haff hmap
    simpa [Function.comp] using this
  · obtain ⟨j, _, hf⟩ := Multiset.mem_bind.1 hf
    rw [Multiset.eq_of_mem_replicate hf]
    have hmap : Set.MapsTo (fun L : ℝ => 1 + L / 2) (Set.Ioi 0) (Set.Ioi 0) := by
      intro L hL
      have := Set.mem_Ioi.1 hL
      exact Set.mem_Ioi.2 (by linarith)
    have := (continuousOn_Nb (ν := p) (j := (j : ℝ) + 1) hν
      (by positivity)).comp haff hmap
    simpa [Function.comp] using this

theorem continuousOn_msMax_eval {S : Set ℝ} :
    ∀ T : Multiset (ℝ → ℝ), (∀ f ∈ T, ContinuousOn f S) →
      ContinuousOn (fun L => msMax (T.map fun f => f L)) S := by
  intro T
  induction T using Multiset.induction_on with
  | empty => intro _; simpa [msMax] using continuousOn_const
  | cons g T ih =>
      intro hT
      have h1 : ContinuousOn (fun L => msMax (T.map fun f => f L)) S :=
        ih fun f hf => hT f (Multiset.mem_cons_of_mem hf)
      have h2 : ContinuousOn g S := hT g (Multiset.mem_cons_self _ _)
      have e : (fun L => msMax ((g ::ₘ T).map fun f => f L))
          = fun L => max (g L) (msMax (T.map fun f => f L)) := by
        funext L
        rw [Multiset.map_cons, msMax, msMax, Multiset.fold_cons_left]
      rw [e]
      exact h2.sup h1

theorem continuousOn_foldmin_eval {S : Set ℝ} (g : ℝ → ℝ)
    (hg : ContinuousOn g S) :
    ∀ P : Multiset (Multiset (ℝ → ℝ)),
      (∀ T ∈ P, ∀ f ∈ T, ContinuousOn f S) →
      ContinuousOn (fun L =>
        ((P.map fun T => msMax (T.map fun f => f L))).fold min (g L)) S := by
  intro P
  induction P using Multiset.induction_on with
  | empty => intro _; simpa using hg
  | cons T P ih =>
      intro hP
      have h1 := ih fun T' hT' => hP T' (Multiset.mem_cons_of_mem hT')
      have h2 : ContinuousOn (fun L => msMax (T.map fun f => f L)) S :=
        continuousOn_msMax_eval T (hP T (Multiset.mem_cons_self _ _))
      have e : (fun L =>
            (((T ::ₘ P).map fun T' => msMax (T'.map fun f => f L))).fold min (g L))
          = fun L => min (msMax (T.map fun f => f L))
              (((P.map fun T' => msMax (T'.map fun f => f L))).fold min (g L)) := by
        funext L
        rw [Multiset.map_cons, Multiset.fold_cons_left]
      rw [e]
      exact h2.inf h1

/-- **Continuity of the profile** (§2): `B_n^k` is continuous on
`(0, ∞)`. -/
theorem continuousOn_profile {p : ℕ} (hp : 1 ≤ p) (k : ℕ) :
    ContinuousOn (profile p k) (Set.Ioi 0) := by
  have key : profile p k = fun L =>
      (((branchFuns p k).powersetCard k).map
        fun T => msMax (T.map fun f => f L)).fold min
          (msMax ((branchFuns p k).map fun f => f L)) := by
    funext L
    rw [profile, branchVals, Multiset.powersetCard_map, Multiset.map_map]
    rfl
  rw [key]
  apply continuousOn_foldmin_eval
  · exact continuousOn_msMax_eval _ (branchFuns_continuousOn hp k)
  · intro T hT f hf
    exact branchFuns_continuousOn hp k f
      (Multiset.mem_of_le (Multiset.mem_powersetCard.1 hT).1 hf)

/-! ### Attainment of the supremum on a compact subinterval

This is the compactness step in the proof of Proposition
`prop:diagnosis`: a function continuous on `(0,∞)`, eventually `≤ T`
both as `L ↓ 0` and as `L → ∞`, and exceeding `T` somewhere, attains its
supremum at a finite length. -/

/-- "The index `k` has finite critical length": the supremum of the
profile over `(0, ∞)` is attained at some finite `L` (§1). -/
def HasFiniteCriticalLength (F : ℝ → ℝ) : Prop :=
  ∃ Lmax > 0, ∀ L > 0, F L ≤ F Lmax

theorem hasFiniteCriticalLength_of_overshoot {F : ℝ → ℝ} {T L0 : ℝ}
    (hcont : ContinuousOn F (Set.Ioi 0)) (hL0 : 0 < L0) (hover : T < F L0)
    (h0 : ∀ᶠ L in 𝓝[>] (0 : ℝ), F L ≤ T)
    (hinf : ∀ᶠ L in atTop, F L ≤ T) :
    HasFiniteCriticalLength F := by
  rw [Filter.eventually_iff] at h0
  obtain ⟨η, hη, hη'⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h0
  have hηpos : (0 : ℝ) < η := Set.mem_Ioi.1 hη
  obtain ⟨M, hM⟩ := eventually_atTop.1 hinf
  set a := min (η / 2) L0 with ha
  set b := max (M + 1) L0 with hb
  have hapos : 0 < a := lt_min (by linarith) hL0
  have haL0 : a ≤ L0 := min_le_right _ _
  have hbL0 : L0 ≤ b := le_max_right _ _
  have hsub : Set.Icc a b ⊆ Set.Ioi 0 := fun x hx =>
    Set.mem_Ioi.2 (lt_of_lt_of_le hapos hx.1)
  have hne : (Set.Icc a b).Nonempty := ⟨L0, haL0, hbL0⟩
  obtain ⟨Lmax, hLmaxK, hLmax⟩ :=
    isCompact_Icc.exists_isMaxOn hne (hcont.mono hsub)
  refine ⟨Lmax, lt_of_lt_of_le hapos hLmaxK.1, ?_⟩
  intro L hL
  have hFL0 : F L0 ≤ F Lmax := hLmax ⟨haL0, hbL0⟩
  rcases lt_or_ge L a with hcase | hcase
  · -- small lengths: `F L ≤ T < F L0 ≤ F Lmax`
    have h1 : F L ≤ T := hη' ⟨hL, by
      calc L < a := hcase
        _ ≤ η / 2 := min_le_left _ _
        _ < η := by linarith⟩
    linarith
  · rcases le_or_gt L b with hcase2 | hcase2
    · exact hLmax ⟨hcase, hcase2⟩
    · have h1 : F L ≤ T := by
        apply hM
        calc M ≤ M + 1 := by linarith
          _ ≤ b := le_max_left _ _
          _ ≤ L := hcase2.le
      linarith

/-! ### Counting branch values below a threshold (eq:rank)

`countP` of the branch multiset decomposes into weighted sums over the
Dirichlet and Neumann degrees. -/

theorem countP_bind {α β : Type*} (s : Multiset α) (f : α → Multiset β)
    (p : β → Prop) [DecidablePred p] :
    Multiset.countP p (s.bind f) = (s.map fun a => Multiset.countP p (f a)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [Multiset.cons_bind, Multiset.countP_add, ih]

theorem countP_replicate {α : Type*} (n : ℕ) (a : α) (p : α → Prop)
    [DecidablePred p] :
    Multiset.countP p (Multiset.replicate n a) = if p a then n else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Multiset.replicate_succ, Multiset.countP_cons, ih]
      split_ifs <;> omega

/-- The weighted count of branch values satisfying a predicate, as a sum
over degrees (the concrete form of the weighted rank, eq:rank). -/
theorem countP_branchVals (p k : ℕ) (L : ℝ) (pr : ℝ → Prop) [DecidablePred pr] :
    Multiset.countP pr (branchVals p k L)
      = (∑ j ∈ Finset.range (ell0 p k + 1),
          if pr (Db p j (1 + L / 2)) then mult p j else 0)
      + ∑ j ∈ Finset.range (ell0 p k + 1),
          if pr (Nb p (j + 1) (1 + L / 2)) then mult p (j + 1) else 0 := by
  rw [branchVals, branchFuns, Multiset.map_add, Multiset.countP_add]
  congr 1
  · rw [Multiset.map_bind, countP_bind]
    have e : ∀ j : ℕ,
        Multiset.countP pr
          ((Multiset.replicate (mult p j) fun L' => Db p j (1 + L' / 2)).map
            fun f => f L)
        = if pr (Db p j (1 + L / 2)) then mult p j else 0 := by
      intro j
      rw [Multiset.map_replicate, countP_replicate]
    calc ((Multiset.range (ell0 p k + 1)).map fun j =>
          Multiset.countP pr
            ((Multiset.replicate (mult p j) fun L' => Db p j (1 + L' / 2)).map
              fun f => f L)).sum
        = ((Multiset.range (ell0 p k + 1)).map fun j : ℕ =>
            if pr (Db p j (1 + L / 2)) then mult p j else 0).sum := by
          congr 1
          exact Multiset.map_congr rfl fun j _ => e j
      _ = _ := rfl
  · rw [Multiset.map_bind, countP_bind]
    have e : ∀ j : ℕ,
        Multiset.countP pr
          ((Multiset.replicate (mult p (j + 1)) fun L' => Nb p (j + 1) (1 + L' / 2)).map
            fun f => f L)
        = if pr (Nb p (j + 1) (1 + L / 2)) then mult p (j + 1) else 0 := by
      intro j
      rw [Multiset.map_replicate, countP_replicate]
    calc ((Multiset.range (ell0 p k + 1)).map fun j =>
          Multiset.countP pr
            ((Multiset.replicate (mult p (j + 1)) fun L' =>
              Nb p (j + 1) (1 + L' / 2)).map fun f => f L)).sum
        = ((Multiset.range (ell0 p k + 1)).map fun j : ℕ =>
            if pr (Nb p (j + 1) (1 + L / 2)) then mult p (j + 1) else 0).sum := by
          congr 1
          exact Multiset.map_congr rfl fun j _ => e j
      _ = _ := rfl

/-! ### The discrete cutoffs (Lemma `lem:cutoffs`)

The paper's cutoffs `A_i = max{j : N_j(R_i) ≤ T_i}` and
`C_i = max{j : D_j(R_i) ≤ T_i}` satisfy `A_i/i → a_s`, `C_i/i → b_s`.
We formalize the (sufficient) upper halves as eventual degree bounds:
for any `x⁺` with `f_s(x⁺) > 1` (resp. `g_s(y⁺) > 1`), eventually every
degree contributing a Neumann (resp. Dirichlet) value `≤ T_i` is at most
`x⁺ i` (resp. `y⁺ i`).  Together with the root sandwich these are
exactly the paper's two-sided sandwich at `a_s ± ε`, `b_s ± ε`. -/

theorem div_lt_div_cancel_right {a b c : ℝ} (hc : 0 < c) (h : a / c < b / c) :
    a < b := by
  have := mul_lt_mul_of_pos_right h hc
  rwa [div_mul_cancel₀ _ hc.ne', div_mul_cancel₀ _ hc.ne'] at this

theorem tendsto_ceil_div {x : ℝ} (hx : 0 < x) :
    Tendsto (fun i : ℕ => ((⌈x * i⌉₊ : ℝ)) / i) atTop (𝓝 x) := by
  have hupper : Tendsto (fun i : ℕ => x + 2 * (1 / (i : ℝ))) atTop (𝓝 (x + 2 * 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_one_div_atTop_nhds_zero_nat)
  rw [mul_zero, add_zero] at hupper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · filter_upwards [eventually_ge_atTop 1] with i hi
    have hipos : (0 : ℝ) < i := by exact_mod_cast hi
    rw [le_div_iff₀ hipos]
    exact Nat.le_ceil _
  · filter_upwards [eventually_ge_atTop 1] with i hi
    have hipos : (0 : ℝ) < i := by exact_mod_cast hi
    rw [div_le_iff₀ hipos]
    have h1 : (⌈x * i⌉₊ : ℝ) < x * i + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2 : (1 : ℝ) ≤ i := by exact_mod_cast hi
    have h3 : (1 / (i : ℝ)) * i = 1 := by field_simp
    nlinarith [h1, h3]

theorem tendsto_T_div {c : ℝ} :
    Tendsto (fun i : ℕ => ((i : ℝ) + c) / i) atTop (𝓝 1) := by
  have h1 : Tendsto (fun i : ℕ => 1 + c * (1 / (i : ℝ))) atTop (𝓝 (1 + c * 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_one_div_atTop_nhds_zero_nat)
  rw [mul_zero, add_zero] at h1
  apply h1.congr'
  filter_upwards [eventually_ge_atTop 1] with i hi
  have hine : (i : ℝ) ≠ 0 := by
    have : (0 : ℝ) < i := by exact_mod_cast hi
    exact this.ne'
  field_simp

/-- Neumann cutoff (upper half of Lemma `lem:cutoffs`): if
`f_s(x⁺) > 1` then eventually every degree `j ≥ 1` with
`N_j(R_i) ≤ T_i = i + n - 2` satisfies `j ≤ x⁺ i`. -/
theorem eventually_N_degree_bound {p : ℕ} (hp : 1 ≤ p) {s xp : ℝ}
    (hs : 0 < s) (hxp : 0 < xp) (hfs : 1 < fs s xp) :
    ∀ᶠ i : ℕ in atTop, ∀ j : ℕ, 1 ≤ j →
      Nb p j (Ri s i) ≤ (i : ℝ) + p → (j : ℝ) ≤ xp * i := by
  have hν : (0 : ℝ) < p := by exact_mod_cast hp
  have hlim : Tendsto (fun i : ℕ => ((⌈xp * i⌉₊ : ℝ)) / i) atTop (𝓝 xp) :=
    tendsto_ceil_div hxp
  have hN := Nb_coupled_limit (ν := p) hν hs hxp
    (fun i => ((⌈xp * i⌉₊ : ℝ))) (fun i => Nat.cast_nonneg _) hlim
  have hev := (tendsto_T_div (c := (p : ℝ))).eventually_lt hN hfs
  filter_upwards [hev, eventually_ge_atTop 1] with i hlt hi
  intro j hj hNle
  by_contra hcon
  push Not at hcon
  have hipos : (0 : ℝ) < i := by exact_mod_cast hi
  have hRi : 1 < Ri s i := one_lt_Ri hs hi
  have h1 : ⌈xp * i⌉₊ ≤ j := Nat.ceil_le.2 hcon.le
  have hceil1 : 0 < ⌈xp * i⌉₊ := by
    rw [Nat.lt_ceil]
    push_cast
    positivity
  have hceilpos : (0 : ℝ) < (⌈xp * i⌉₊ : ℝ) := by exact_mod_cast hceil1
  have hmono : Nb p ((⌈xp * i⌉₊ : ℝ)) (Ri s i) ≤ Nb p j (Ri s i) := by
    rcases eq_or_lt_of_le ((Nat.cast_le (α := ℝ)).2 h1) with heq | hlt2
    · rw [heq]
    · exact (Nb_strictMono_degree hν hceilpos hlt2 hRi).le
  have h2 : (i : ℝ) + p < Nb p ((⌈xp * i⌉₊ : ℝ)) (Ri s i) :=
    div_lt_div_cancel_right hipos hlt
  linarith

/-- Dirichlet cutoff (upper half of Lemma `lem:cutoffs`): if
`g_s(y⁺) > 1` then eventually every degree `j ≥ 0` with
`D_j(R_i) ≤ T_i = i + n - 2` satisfies `j ≤ y⁺ i`. -/
theorem eventually_D_degree_bound {p : ℕ} (hp : 1 ≤ p) {s yp : ℝ}
    (hs : 0 < s) (hyp : 0 < yp) (hgs : 1 < gs s yp) :
    ∀ᶠ i : ℕ in atTop, ∀ j : ℕ,
      Db p j (Ri s i) ≤ (i : ℝ) + p → (j : ℝ) ≤ yp * i := by
  have hν : (0 : ℝ) < p := by exact_mod_cast hp
  have hlim : Tendsto (fun i : ℕ => ((⌈yp * i⌉₊ : ℝ)) / i) atTop (𝓝 yp) :=
    tendsto_ceil_div hyp
  have hD := Db_coupled_limit (ν := p) hν hs hyp
    (fun i => ((⌈yp * i⌉₊ : ℝ))) (fun i => Nat.cast_nonneg _) hlim
  have hev := (tendsto_T_div (c := (p : ℝ))).eventually_lt hD hgs
  filter_upwards [hev, eventually_ge_atTop 1] with i hlt hi
  intro j hDle
  by_contra hcon
  push Not at hcon
  have hipos : (0 : ℝ) < i := by exact_mod_cast hi
  have hRi : 1 < Ri s i := one_lt_Ri hs hi
  have h1 : ⌈yp * i⌉₊ ≤ j := Nat.ceil_le.2 hcon.le
  have hmono : Db p ((⌈yp * i⌉₊ : ℝ)) (Ri s i) ≤ Db p j (Ri s i) := by
    rcases eq_or_lt_of_le ((Nat.cast_le (α := ℝ)).2 h1) with heq | hlt2
    · rw [heq]
    · exact (Db_strictMono_degree hν (Nat.cast_nonneg _) hlt2 hRi).le
  have h2 : (i : ℝ) + p < Db p ((⌈yp * i⌉₊ : ℝ)) (Ri s i) :=
    div_lt_div_cancel_right hipos hlt
  linarith

/-! ## §2 of the paper: Lemma `lem:infinity`

For the diagnosis index `k_i = 2 S_{i-1}`, for all large `L` the profile
equals the Neumann branch `N_i(1 + L/2)`, and therefore
`B_n^{k_i}(L) → T_i = i + q - 1 = i + n - 2` as `L → ∞`. -/

theorem sum_ite_lt_range (f : ℕ → ℕ) {c n : ℕ} (hcn : c ≤ n) :
    (∑ j ∈ Finset.range n, if j < c then f j else 0)
      = ∑ j ∈ Finset.range c, f j := by
  rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
  have h0 : (∑ j ∈ Finset.Ico 0 c, if j < c then f j else 0)
        + (∑ j ∈ Finset.Ico c n, if j < c then f j else 0)
      = ∑ j ∈ Finset.Ico 0 n, if j < c then f j else 0 :=
    Finset.sum_Ico_consecutive _ (Nat.zero_le c) hcn
  have h1 : ∑ j ∈ Finset.Ico 0 c, (if j < c then f j else 0)
      = ∑ j ∈ Finset.Ico 0 c, f j :=
    Finset.sum_congr rfl fun j hj => if_pos (Finset.mem_Ico.1 hj).2
  have h2 : ∑ j ∈ Finset.Ico c n, (if j < c then f j else 0) = 0 :=
    Finset.sum_eq_zero fun j hj => if_neg (by
      have := (Finset.mem_Ico.1 hj).1; omega)
  omega

theorem sum_shift_range {p : ℕ} (hp : 1 ≤ p) (m : ℕ) :
    (∑ j ∈ Finset.range m, mult p (j + 1)) + 1 = cumMult p m := by
  cases m with
  | zero => simpa using (cumMult_zero hp).symm
  | succ n =>
      have h := sum_range_mult_shift hp n
      have e : ((Multiset.range (n + 1)).map fun j => mult p (j + 1)).sum
          = ∑ j ∈ Finset.range (n + 1), mult p (j + 1) := rfl
      rw [e] at h
      exact h

/-- `i - 1 ≤ ℓ₀(k_i)`: the branches `D_0,…,D_{i-1}, N_1,…,N_i` all occur
in the multiset eq:multiset at the diagnosis index. -/
theorem ell0_kDiag_ge (p i : ℕ) : i - 1 ≤ ell0 p (kDiag p i) := by
  apply Nat.le_findGreatest
  · have := lt_cumMult p (i - 1)
    rw [kDiag]
    omega
  · rw [kDiag]
    omega

/-- The exact strict count at large `R`: the weighted number of branch
values `< N_i` is `k_i - 1` ("Thus exactly `k_i - 1` occurrences precede
`N_i`", Lemma `lem:infinity`). -/
theorem countP_lt_Nb {p i : ℕ} (hp : 1 ≤ p) (hi : 1 ≤ i) {L : ℝ}
    (hR : 1 < 1 + L / 2)
    (hE1 : ∀ j : ℕ, j < i → Db p j (1 + L / 2) < Nb p i (1 + L / 2)) :
    Multiset.countP (fun x => x < Nb p i (1 + L / 2))
        (branchVals p (kDiag p i) L) + 1 = kDiag p i := by
  have hν : (0 : ℝ) < p := by exact_mod_cast hp
  have hℓ : i - 1 ≤ ell0 p (kDiag p i) := ell0_kDiag_ge p i
  rw [countP_branchVals]
  have hD : (∑ j ∈ Finset.range (ell0 p (kDiag p i) + 1),
      if Db p j (1 + L / 2) < Nb p i (1 + L / 2) then mult p j else 0)
      = cumMult p (i - 1) := by
    have e1 : ∀ j ∈ Finset.range (ell0 p (kDiag p i) + 1),
        (if Db p j (1 + L / 2) < Nb p i (1 + L / 2) then mult p j else 0)
          = if j < i then mult p j else 0 := by
      intro j _
      rcases lt_or_ge j i with hj | hj
      · rw [if_pos (hE1 j hj), if_pos hj]
      · have h1 : (j : ℝ) + p < Db p j (1 + L / 2) :=
          lt_Dv hν (Nat.cast_nonneg _) (one_lt_upow hν (Nat.cast_nonneg _) hR)
        have h2 : Nb p i (1 + L / 2) < (i : ℝ) + p :=
          Nv_lt hν (Nat.cast_nonneg _) (one_lt_upow hν (Nat.cast_nonneg _) hR)
        have h3 : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
        rw [if_neg (by push Not; linarith), if_neg (by omega)]
    rw [Finset.sum_congr rfl e1, sum_ite_lt_range _ (by omega)]
    rw [show i = (i - 1) + 1 by omega]
    rfl
  have hN : (∑ j ∈ Finset.range (ell0 p (kDiag p i) + 1),
      if Nb p (j + 1) (1 + L / 2) < Nb p i (1 + L / 2) then mult p (j + 1) else 0)
      + 1 = cumMult p (i - 1) := by
    have e1 : ∀ j ∈ Finset.range (ell0 p (kDiag p i) + 1),
        (if Nb p (j + 1) (1 + L / 2) < Nb p i (1 + L / 2) then mult p (j + 1) else 0)
          = if j < i - 1 then mult p (j + 1) else 0 := by
      intro j _
      rcases lt_or_ge (j + 1) i with hj | hj
      · have hcast : ((j : ℝ) + 1) < (i : ℝ) := by
          have : ((j + 1 : ℕ) : ℝ) < (i : ℕ) := by exact_mod_cast hj
          push_cast at this
          linarith
        have := Nb_strictMono_degree (ν := p) hν (by positivity) hcast hR
        rw [if_pos this, if_pos (by omega)]
      · have hle : ¬ (Nb p (j + 1) (1 + L / 2) < Nb p i (1 + L / 2)) := by
          rcases eq_or_lt_of_le hj with heq | hlt
          · have hcast : ((j : ℝ) + 1) = (i : ℝ) := by
              have : ((j + 1 : ℕ) : ℝ) = (i : ℕ) := by exact_mod_cast heq.symm
              push_cast at this
              linarith
            rw [hcast]
            exact lt_irrefl _
          · have hcast : (i : ℝ) < (j : ℝ) + 1 := by
              have : ((i : ℕ) : ℝ) < ((j + 1 : ℕ) : ℝ) := by exact_mod_cast hlt
              push_cast at this
              linarith
            have hipos : (0 : ℝ) < (i : ℕ) := by exact_mod_cast hi
            have := Nb_strictMono_degree (ν := p) hν hipos hcast hR
            push Not
            linarith
        rw [if_neg hle, if_neg (by omega)]
    rw [Finset.sum_congr rfl e1, sum_ite_lt_range _ (by omega)]
    exact sum_shift_range hp (i - 1)
  have hkd : kDiag p i = 2 * cumMult p (i - 1) := rfl
  omega

/-- The weighted number of branch values `≤ N_i` is at least `k_i`
(Lemma `lem:infinity`). -/
theorem countP_le_Nb {p i : ℕ} (hp : 1 ≤ p) (hi : 1 ≤ i) {L : ℝ}
    (hR : 1 < 1 + L / 2)
    (hE1 : ∀ j : ℕ, j < i → Db p j (1 + L / 2) < Nb p i (1 + L / 2)) :
    kDiag p i ≤ Multiset.countP (fun x => x ≤ Nb p i (1 + L / 2))
        (branchVals p (kDiag p i) L) := by
  have hν : (0 : ℝ) < p := by exact_mod_cast hp
  have hℓ : i - 1 ≤ ell0 p (kDiag p i) := ell0_kDiag_ge p i
  rw [countP_branchVals]
  have hD : (∑ j ∈ Finset.range (ell0 p (kDiag p i) + 1),
      if Db p j (1 + L / 2) ≤ Nb p i (1 + L / 2) then mult p j else 0)
      = cumMult p (i - 1) := by
    have e1 : ∀ j ∈ Finset.range (ell0 p (kDiag p i) + 1),
        (if Db p j (1 + L / 2) ≤ Nb p i (1 + L / 2) then mult p j else 0)
          = if j < i then mult p j else 0 := by
      intro j _
      rcases lt_or_ge j i with hj | hj
      · rw [if_pos (hE1 j hj).le, if_pos hj]
      · have h1 : (j : ℝ) + p < Db p j (1 + L / 2) :=
          lt_Dv hν (Nat.cast_nonneg _) (one_lt_upow hν (Nat.cast_nonneg _) hR)
        have h2 : Nb p i (1 + L / 2) < (i : ℝ) + p :=
          Nv_lt hν (Nat.cast_nonneg _) (one_lt_upow hν (Nat.cast_nonneg _) hR)
        have h3 : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
        rw [if_neg (by push Not; linarith), if_neg (by omega)]
    rw [Finset.sum_congr rfl e1, sum_ite_lt_range _ (by omega)]
    rw [show i = (i - 1) + 1 by omega]
    rfl
  have hN : (∑ j ∈ Finset.range (ell0 p (kDiag p i) + 1),
      if Nb p (j + 1) (1 + L / 2) ≤ Nb p i (1 + L / 2) then mult p (j + 1) else 0)
      + 1 = cumMult p i := by
    have e1 : ∀ j ∈ Finset.range (ell0 p (kDiag p i) + 1),
        (if Nb p (j + 1) (1 + L / 2) ≤ Nb p i (1 + L / 2) then mult p (j + 1) else 0)
          = if j < i then mult p (j + 1) else 0 := by
      intro j _
      rcases lt_or_ge j i with hj | hj
      · have hcond : Nb p (j + 1) (1 + L / 2) ≤ Nb p i (1 + L / 2) := by
          rcases eq_or_lt_of_le (by omega : j + 1 ≤ i) with heq | hlt
          · have hcast : ((j : ℝ) + 1) = (i : ℝ) := by
              have : ((j + 1 : ℕ) : ℝ) = (i : ℕ) := by exact_mod_cast heq
              push_cast at this
              linarith
            rw [hcast]
          · have hcast : ((j : ℝ) + 1) < (i : ℝ) := by
              have : ((j + 1 : ℕ) : ℝ) < (i : ℕ) := by exact_mod_cast hlt
              push_cast at this
              linarith
            exact (Nb_strictMono_degree (ν := p) hν (by positivity) hcast hR).le
        rw [if_pos hcond, if_pos hj]
      · have hcast : (i : ℝ) < (j : ℝ) + 1 := by
          have : ((i : ℕ) : ℝ) < ((j + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : i < j + 1)
          push_cast at this
          linarith
        have hipos : (0 : ℝ) < (i : ℕ) := by exact_mod_cast hi
        have hmono := Nb_strictMono_degree (ν := p) hν hipos hcast hR
        rw [if_neg (by push Not; linarith), if_neg (by omega)]
    rw [Finset.sum_congr rfl e1, sum_ite_lt_range _ (by omega)]
    exact sum_shift_range hp i
  have hmono := cumMult_strictMono p (by omega : i - 1 < i)
  have hkd : kDiag p i = 2 * cumMult p (i - 1) := rfl
  omega

theorem tendsto_R_atTop : Tendsto (fun L : ℝ => 1 + L / 2) atTop atTop := by
  have h1 : Tendsto (fun L : ℝ => L / 2) atTop atTop :=
    tendsto_id.atTop_div_const two_pos
  exact tendsto_atTop_add_const_left atTop 1 h1

/-- Eventually in `L`, each `D_j` with `j < i` lies strictly below `N_i`
(the separation step in the proof of Lemma `lem:infinity`). -/
theorem eventually_D_lt_N {p i : ℕ} (hp : 1 ≤ p) (hi : 1 ≤ i) :
    ∀ᶠ L : ℝ in atTop, ∀ j : ℕ, j < i →
      Db p j (1 + L / 2) < Nb p i (1 + L / 2) := by
  have hν : (0 : ℝ) < p := by exact_mod_cast hp
  have key : ∀ j : ℕ, j < i → ∀ᶠ R : ℝ in atTop, Db p j R < Nb p i R := by
    intro j hj
    have hji : (j : ℝ) + 1 ≤ i := by exact_mod_cast hj
    have h1 : ∀ᶠ R : ℝ in atTop, Db p j R < (i : ℝ) + p - 1 / 2 :=
      (Db_tendsto_atTop hν (Nat.cast_nonneg _)).eventually_lt_const
        (by linarith)
    have h2 : ∀ᶠ R : ℝ in atTop, (i : ℝ) + p - 1 / 2 < Nb p i R :=
      (Nb_tendsto_atTop hν (Nat.cast_pos.2 hi)).eventually_const_lt
        (by linarith)
    filter_upwards [h1, h2] with R hR1 hR2
    linarith
  have hall : ∀ᶠ R : ℝ in atTop, ∀ j ∈ Finset.range i, Db p j R < Nb p i R := by
    rw [eventually_all_finset]
    intro j hj
    exact key j (Finset.mem_range.1 hj)
  filter_upwards [tendsto_R_atTop.eventually hall] with L hL j hj
  exact hL j (Finset.mem_range.2 hj)

/-- **Lemma `lem:infinity`, first assertion**: for all sufficiently large
`L`, `B_n^{k_i}(L) = N_i(1 + L/2)`. -/
theorem profile_eq_Nb_eventually {p i : ℕ} (hp : 1 ≤ p) (hi : 1 ≤ i) :
    ∀ᶠ L : ℝ in atTop, profile p (kDiag p i) L = Nb p i (1 + L / 2) := by
  have hν : (0 : ℝ) < p := by exact_mod_cast hp
  filter_upwards [eventually_D_lt_N hp hi, eventually_gt_atTop (0 : ℝ)]
    with L hE1 hL
  have hR : 1 < 1 + L / 2 := by linarith
  have h1 := countP_lt_Nb hp hi hR hE1
  have h2 := countP_le_Nb hp hi hR hE1
  have hcard := le_card_branchVals hp (kDiag p i) L
  have hge : Nb p i (1 + L / 2) ≤ profile p (kDiag p i) L :=
    le_profile_of_count hcard (by omega)
  have hle : profile p (kDiag p i) L ≤ Nb p i (1 + L / 2) :=
    profile_le_of_count
      (Nv_nonneg hν (Nat.cast_nonneg _)
        (one_lt_upow hν (Nat.cast_nonneg _) hR).le) h2
  linarith

/-- **Lemma `lem:infinity`, eq:Ti**:
`lim_{L→∞} B_n^{k_i}(L) = T_i = i + q - 1 = i + n - 2`. -/
theorem profile_tendsto_Ti {p i : ℕ} (hp : 1 ≤ p) (hi : 1 ≤ i) :
    Tendsto (profile p (kDiag p i)) atTop (𝓝 ((i : ℝ) + p)) := by
  have hν : (0 : ℝ) < p := by exact_mod_cast hp
  have hN : Tendsto (fun L : ℝ => Nb p i (1 + L / 2)) atTop
      (𝓝 ((i : ℝ) + p)) :=
    (Nb_tendsto_atTop hν (Nat.cast_pos.2 hi)).comp tendsto_R_atTop
  apply hN.congr'
  filter_upwards [profile_eq_Nb_eventually hp hi] with L h
  exact h.symm

/-- Eventually as `L → ∞` the profile at the diagnosis index is `≤ T_i`
(needed for the compactness step of Proposition `prop:diagnosis`). -/
theorem profile_eventually_le_Ti {p i : ℕ} (hp : 1 ≤ p) (hi : 1 ≤ i) :
    ∀ᶠ L : ℝ in atTop, profile p (kDiag p i) L ≤ (i : ℝ) + p := by
  have hν : (0 : ℝ) < p := by exact_mod_cast hp
  filter_upwards [profile_eq_Nb_eventually hp hi, eventually_gt_atTop (0 : ℝ)]
    with L heq hL
  have hR : 1 < 1 + L / 2 := by linarith
  rw [heq]
  exact (Nv_lt hν (Nat.cast_nonneg _) (one_lt_upow hν (Nat.cast_nonneg _) hR)).le

/-- Near `L = 0` the profile is small ("`B_n^{k_i}(L)` tends to zero as
`L ↓ 0`", proof of Proposition `prop:diagnosis`); we only need the bound
by `T_i`.  The `S_{ℓ₀+1} - 1 ≥ k` Neumann values all tend to `0`. -/
theorem profile_eventually_le_Ti_zero {p : ℕ} (hp : 1 ≤ p) (k i : ℕ)
    (hi : 1 ≤ i) :
    ∀ᶠ L in 𝓝[>] (0 : ℝ), profile p k L ≤ (i : ℝ) + p := by
  have hν : (0 : ℝ) < p := by exact_mod_cast hp
  have hTpos : (0 : ℝ) < (i : ℝ) + p := by positivity
  -- the map `L ↦ 1 + L/2` into `𝓝[Ioi 0] 1`
  have hmap : Tendsto (fun L : ℝ => 1 + L / 2) (𝓝[>] (0 : ℝ))
      (𝓝[Set.Ioi (0 : ℝ)] 1) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hbase : Tendsto (fun L : ℝ => 1 + L / 2) (𝓝 0) (𝓝 (1 + 0 / 2)) :=
        (continuous_const.add (continuous_id.div_const 2)).tendsto 0
      rw [show (1 : ℝ) + 0 / 2 = 1 by norm_num] at hbase
      exact hbase.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with L hL
      have : (0 : ℝ) < L := hL
      exact Set.mem_Ioi.2 (by linarith)
  -- each Neumann branch tends to 0 as `L → 0⁺`
  have keyN : ∀ j : ℕ, ∀ᶠ L in 𝓝[>] (0 : ℝ),
      Nb p (j + 1) (1 + L / 2) ≤ (i : ℝ) + p := by
    intro j
    have hcw : ContinuousWithinAt (Nb p ((j : ℝ) + 1)) (Set.Ioi 0) 1 :=
      continuousOn_Nb hν (by positivity) 1 (Set.mem_Ioi.2 one_pos)
    have h0 : Tendsto (fun L : ℝ => Nb p ((j : ℝ) + 1) (1 + L / 2))
        (𝓝[>] (0 : ℝ)) (𝓝 (Nb p ((j : ℝ) + 1) 1)) := hcw.tendsto.comp hmap
    rw [Nb_one] at h0
    have := h0.eventually_lt_const hTpos
    filter_upwards [this] with L hL
    exact hL.le
  have hall : ∀ᶠ L in 𝓝[>] (0 : ℝ), ∀ j ∈ Finset.range (ell0 p k + 1),
      Nb p (j + 1) (1 + L / 2) ≤ (i : ℝ) + p := by
    rw [eventually_all_finset]
    intro j _
    exact keyN j
  filter_upwards [hall] with L hL
  apply profile_le_of_count hTpos.le
  rw [countP_branchVals]
  have hN : (∑ j ∈ Finset.range (ell0 p k + 1),
      if Nb p (j + 1) (1 + L / 2) ≤ (i : ℝ) + p then mult p (j + 1) else 0)
      = ∑ j ∈ Finset.range (ell0 p k + 1), mult p (j + 1) :=
    Finset.sum_congr rfl fun j hj => if_pos (hL j hj)
  have hshift := sum_shift_range hp (ell0 p k + 1)
  have hk := lt_cumMult_ell0_succ p k
  omega

/-! ## §4 of the paper: weighted rank and the overshoot (eq:rank,
eq:Sasymptotic, eq:ranklimits, eq:overshoot)

At the coupled length `L_i` the weighted number of branch values
`≤ T_i` is at most `S_{⌊y⁺i⌋} + S_{⌊x⁺i⌋} - 1`, and the polynomial
bounds on `S_J` (eq:Sasymptotic) turn the scalar inequality into
`𝓡_i < k_i` for all large `i`. -/

theorem sum_ite_lt_le (f : ℕ → ℕ) (c n : ℕ) :
    (∑ j ∈ Finset.range n, if j < c then f j else 0)
      ≤ ∑ j ∈ Finset.range c, f j := by
  rw [← Finset.sum_filter]
  apply Finset.sum_le_sum_of_subset
  intro j hj
  rw [Finset.mem_filter] at hj
  exact Finset.mem_range.2 hj.2

/-- The weighted-rank bound: given the degree cutoffs, the count of
branch values `≤ T_i` at the coupled length is `< k_i` provided the
polynomial comparison holds (the quantitative form of eq:rank +
eq:ranklimits). -/
theorem count_lt_kDiag {p i : ℕ} (hp : 1 ≤ p) (hi : 1 ≤ i) {s xp yp : ℝ}
    (hxp0 : 0 ≤ xp) (hyp0 : 0 ≤ yp)
    (hDb : ∀ j : ℕ, Db p j (Ri s i) ≤ (i : ℝ) + p → (j : ℝ) ≤ yp * i)
    (hNb : ∀ j : ℕ, 1 ≤ j → Nb p j (Ri s i) ≤ (i : ℝ) + p → (j : ℝ) ≤ xp * i)
    (hpoly : (yp * i + (p + 1)) ^ (p + 1) + (xp * i + (p + 1)) ^ (p + 1)
      < 2 * ((i : ℝ) - 1) ^ (p + 1)) :
    Multiset.countP (fun x => x ≤ (i : ℝ) + p)
      (branchVals p (kDiag p i) (Li s i)) < kDiag p i := by
  have hν : (0 : ℝ) < p := by exact_mod_cast hp
  have hipos : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
  set Jy : ℕ := ⌊yp * i⌋₊ with hJy
  set Jx : ℕ := ⌊xp * i⌋₊ with hJx
  rw [countP_branchVals]
  -- Dirichlet side: `≤ S_{Jy}`
  have hD : (∑ j ∈ Finset.range (ell0 p (kDiag p i) + 1),
      if Db p j (1 + Li s i / 2) ≤ (i : ℝ) + p then mult p j else 0)
      ≤ cumMult p Jy := by
    have step1 : ∀ j ∈ Finset.range (ell0 p (kDiag p i) + 1),
        (if Db p j (1 + Li s i / 2) ≤ (i : ℝ) + p then mult p j else 0)
          ≤ if j < Jy + 1 then mult p j else 0 := by
      intro j _
      by_cases hcond : Db p j (1 + Li s i / 2) ≤ (i : ℝ) + p
      · have h1 : (j : ℝ) ≤ yp * i := by
          apply hDb
          rwa [Ri_eq]
        have h2 : j ≤ Jy := Nat.le_floor h1
        rw [if_pos hcond, if_pos (by omega)]
      · rw [if_neg hcond]
        exact Nat.zero_le _
    calc (∑ j ∈ Finset.range (ell0 p (kDiag p i) + 1),
        if Db p j (1 + Li s i / 2) ≤ (i : ℝ) + p then mult p j else 0)
        ≤ ∑ j ∈ Finset.range (ell0 p (kDiag p i) + 1),
            if j < Jy + 1 then mult p j else 0 := Finset.sum_le_sum step1
      _ ≤ ∑ j ∈ Finset.range (Jy + 1), mult p j := sum_ite_lt_le _ _ _
      _ = cumMult p Jy := rfl
  -- Neumann side: `+ 1 ≤ S_{Jx}`
  have hN : (∑ j ∈ Finset.range (ell0 p (kDiag p i) + 1),
      if Nb p (j + 1) (1 + Li s i / 2) ≤ (i : ℝ) + p then mult p (j + 1) else 0)
      + 1 ≤ cumMult p Jx := by
    have step1 : ∀ j ∈ Finset.range (ell0 p (kDiag p i) + 1),
        (if Nb p (j + 1) (1 + Li s i / 2) ≤ (i : ℝ) + p then mult p (j + 1) else 0)
          ≤ if j < Jx then mult p (j + 1) else 0 := by
      intro j _
      by_cases hcond : Nb p (j + 1) (1 + Li s i / 2) ≤ (i : ℝ) + p
      · have h1 : ((j + 1 : ℕ) : ℝ) ≤ xp * i := by
          apply hNb (j + 1) (by omega)
          rw [Ri_eq]
          push_cast
          exact hcond
        have h2 : j + 1 ≤ Jx := Nat.le_floor h1
        rw [if_pos hcond, if_pos (by omega)]
      · rw [if_neg hcond]
        exact Nat.zero_le _
    have step2 : (∑ j ∈ Finset.range (ell0 p (kDiag p i) + 1),
        if j < Jx then mult p (j + 1) else 0)
        ≤ ∑ j ∈ Finset.range Jx, mult p (j + 1) := sum_ite_lt_le _ _ _
    have step3 := sum_shift_range hp Jx
    have step4 := Finset.sum_le_sum step1
    omega
  -- the polynomial comparison: `S_{Jy} + S_{Jx} < k_i` (eq:Sasymptotic +
  -- eq:ranklimits, in the quantitative form `q! S_J ≤ (J+q)^q + (J+p)^q`
  -- and `q! k_i ≥ 4 (i-1)^q`)
  have hSSk : cumMult p Jy + cumMult p Jx < kDiag p i := by
    -- `q! S_J ≤ (J+p+1)^q + (J+p)^q` in ℕ
    have hboundS : ∀ J : ℕ, (p + 1).factorial * cumMult p J
        ≤ (J + p + 1) ^ (p + 1) + (J + p) ^ (p + 1) := by
      intro J
      rw [cumMult_closed p hp J, Nat.mul_add]
      have c1 : (p + 1).factorial * (J + p + 1).choose (p + 1)
          ≤ (J + p + 1) ^ (p + 1) := by
        rw [← Nat.descFactorial_eq_factorial_mul_choose]
        exact Nat.descFactorial_le_pow _ _
      have c2 : (p + 1).factorial * (J + p).choose (p + 1)
          ≤ (J + p) ^ (p + 1) := by
        rw [← Nat.descFactorial_eq_factorial_mul_choose]
        exact Nat.descFactorial_le_pow _ _
      omega
    -- `q! k_i ≥ 4 (i-1)^q` in ℕ
    have hboundK : 4 * (i - 1) ^ (p + 1)
        ≤ (p + 1).factorial * kDiag p i := by
      have g1 : (i - 1) ^ (p + 1)
          ≤ (p + 1).factorial * (i + p - 1).choose (p + 1) := by
        rw [← Nat.descFactorial_eq_factorial_mul_choose]
        have := (i + p - 1).pow_sub_le_descFactorial (p + 1)
        rwa [show i + p - 1 + 1 - (p + 1) = i - 1 by omega] at this
      have g2 : (i + p - 1).choose (p + 1) ≤ (i + p).choose (p + 1) :=
        Nat.choose_le_choose _ (by omega)
      have g3 : kDiag p i = 2 * ((i + p).choose (p + 1) + (i + p - 1).choose (p + 1)) := by
        rw [kDiag, cumMult_closed p hp (i - 1),
          show i - 1 + p + 1 = i + p by omega, show i - 1 + p = i + p - 1 by omega]
      rw [g3]
      nlinarith [g1, g2, Nat.factorial_pos (p + 1)]
    -- assemble over ℝ
    have hcast : ((p + 1).factorial : ℝ) * ((cumMult p Jy : ℝ) + (cumMult p Jx : ℝ))
        < ((p + 1).factorial : ℝ) * (kDiag p i : ℝ) := by
      have hy1 : ((Jy : ℝ)) ≤ yp * i := Nat.floor_le (by positivity)
      have hx1 : ((Jx : ℝ)) ≤ xp * i := Nat.floor_le (by positivity)
      have hSy : ((p + 1).factorial : ℝ) * (cumMult p Jy : ℝ)
          ≤ 2 * (yp * i + (p + 1)) ^ (p + 1) := by
        have h1 := hboundS Jy
        have h2 : (((p + 1).factorial * cumMult p Jy : ℕ) : ℝ)
            ≤ (((Jy + p + 1) ^ (p + 1) + (Jy + p) ^ (p + 1) : ℕ) : ℝ) := by
          exact_mod_cast h1
        push_cast at h2
        have e1 : ((Jy : ℝ) + p + 1) ^ (p + 1) ≤ (yp * i + (p + 1)) ^ (p + 1) :=
          pow_le_pow_left₀ (by positivity) (by linarith) _
        have e2 : ((Jy : ℝ) + p) ^ (p + 1) ≤ (yp * i + (p + 1)) ^ (p + 1) :=
          pow_le_pow_left₀ (by positivity) (by linarith) _
        nlinarith
      have hSx : ((p + 1).factorial : ℝ) * (cumMult p Jx : ℝ)
          ≤ 2 * (xp * i + (p + 1)) ^ (p + 1) := by
        have h1 := hboundS Jx
        have h2 : (((p + 1).factorial * cumMult p Jx : ℕ) : ℝ)
            ≤ (((Jx + p + 1) ^ (p + 1) + (Jx + p) ^ (p + 1) : ℕ) : ℝ) := by
          exact_mod_cast h1
        push_cast at h2
        have e1 : ((Jx : ℝ) + p + 1) ^ (p + 1) ≤ (xp * i + (p + 1)) ^ (p + 1) :=
          pow_le_pow_left₀ (by positivity) (by linarith) _
        have e2 : ((Jx : ℝ) + p) ^ (p + 1) ≤ (xp * i + (p + 1)) ^ (p + 1) :=
          pow_le_pow_left₀ (by positivity) (by linarith) _
        nlinarith
      have hK : 4 * ((i : ℝ) - 1) ^ (p + 1)
          ≤ ((p + 1).factorial : ℝ) * (kDiag p i : ℝ) := by
        have h1 := hboundK
        have h2 : ((4 * (i - 1) ^ (p + 1) : ℕ) : ℝ)
            ≤ (((p + 1).factorial * kDiag p i : ℕ) : ℝ) := by
          exact_mod_cast h1
        push_cast [Nat.cast_sub hi] at h2
        exact h2
      nlinarith [hpoly, hSy, hSx, hK]
    have hfac : (0 : ℝ) < ((p + 1).factorial : ℝ) := by
      exact_mod_cast (p + 1).factorial_pos
    have := lt_of_mul_lt_mul_left hcast hfac.le
    exact_mod_cast this
  omega

/-! ## Proposition `prop:diagnosis` and Theorem `thm:main` -/

theorem Li_pos {s : ℝ} (hs : 0 < s) {i : ℕ} (hi : 1 ≤ i) : 0 < Li s i := by
  have h := one_lt_Ri hs hi
  rw [Ri] at h
  rw [Li]
  linarith

/-- The polynomial comparison of eq:ranklimits: if `yp^q + xp^q < 2`
then `(yp i + q)^q + (xp i + q)^q < 2 (i-1)^q` for all large `i`. -/
theorem eventually_poly {q : ℕ} {xp yp : ℝ}
    (hsum : yp ^ q + xp ^ q < 2) :
    ∀ᶠ i : ℕ in atTop,
      (yp * i + q) ^ q + (xp * i + q) ^ q < 2 * ((i : ℝ) - 1) ^ q := by
  have h1 : Tendsto (fun i : ℕ => (q : ℝ) * (1 / i)) atTop (𝓝 ((q : ℝ) * 0)) :=
    tendsto_const_nhds.mul tendsto_one_div_atTop_nhds_zero_nat
  rw [mul_zero] at h1
  have hA : Tendsto (fun i : ℕ => (yp + q * (1 / i)) ^ q + (xp + q * (1 / i)) ^ q)
      atTop (𝓝 ((yp + 0) ^ q + (xp + 0) ^ q)) :=
    ((tendsto_const_nhds.add h1).pow q).add ((tendsto_const_nhds.add h1).pow q)
  rw [add_zero, add_zero] at hA
  have h2 : Tendsto (fun i : ℕ => (1 : ℝ) - 1 / i) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub tendsto_one_div_atTop_nhds_zero_nat
  rw [sub_zero] at h2
  have hB : Tendsto (fun i : ℕ => 2 * ((1 : ℝ) - 1 / i) ^ q) atTop
      (𝓝 (2 * (1 : ℝ) ^ q)) := tendsto_const_nhds.mul (h2.pow q)
  rw [one_pow, mul_one] at hB
  have hev := hA.eventually_lt hB hsum
  filter_upwards [hev, eventually_ge_atTop 1] with i hlt hi
  have hipos : (0 : ℝ) < i := by exact_mod_cast hi
  have hipow : (0 : ℝ) < (i : ℝ) ^ q := by positivity
  have hine : (i : ℝ) ≠ 0 := hipos.ne'
  have e1 : yp * i + q = (yp + q * (1 / i)) * i := by field_simp
  have e2 : xp * i + q = (xp + q * (1 / i)) * i := by field_simp
  have e3 : (i : ℝ) - 1 = (1 - 1 / i) * i := by field_simp
  calc (yp * i + q) ^ q + (xp * i + q) ^ q
      = ((yp + q * (1 / i)) ^ q + (xp + q * (1 / i)) ^ q) * (i : ℝ) ^ q := by
        rw [e1, e2, mul_pow, mul_pow]; ring
    _ < (2 * ((1 : ℝ) - 1 / i) ^ q) * (i : ℝ) ^ q :=
        mul_lt_mul_of_pos_right hlt hipow
    _ = 2 * ((i : ℝ) - 1) ^ q := by rw [e3, mul_pow]; ring

/-- **eq:overshoot**: for a suitable coupled scale `s` (built from
Lemma `lem:scalar`), the profile at the diagnosis index exceeds its
infinite-length limit `T_i` at the finite length `L_i`, for all large
`i`. -/
theorem eventually_overshoot {p : ℕ} (hp : 1 ≤ p) :
    ∃ s : ℝ, 0 < s ∧ ∀ᶠ i : ℕ in atTop,
      ((i : ℝ) + p) < profile p (kDiag p i) (Li s i) := by
  have hq2 : 2 ≤ p + 1 := by omega
  set s : ℝ := 16 * ((p : ℝ) + 1) + 28 with hsdef
  have hple : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  have hs28 : (28 : ℝ) ≤ s := by rw [hsdef]; linarith
  have hs1 : (1 : ℝ) ≤ s := by linarith
  have hs0 : (0 : ℝ) < s := by linarith
  obtain ⟨a, ha, haeq⟩ := exists_root_a hs1
  obtain ⟨b, hb, hbeq⟩ := exists_root_b (s := s) (by linarith)
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  have hscalar : a ^ (p + 1) + b ^ (p + 1) < 2 :=
    scalar_inequality hq2 (by rw [hsdef]; push_cast; linarith)
      ha1 ha2 haeq hb1 hb2 hbeq
  -- a strict margin `ε > 0` keeping the scalar inequality
  have hcont : ContinuousAt
      (fun ε : ℝ => (a + ε) ^ (p + 1) + (b + ε) ^ (p + 1)) 0 := by
    apply Continuous.continuousAt
    exact ((continuous_const.add continuous_id).pow _).add
      ((continuous_const.add continuous_id).pow _)
  have hev0 : ∀ᶠ ε in 𝓝 (0 : ℝ),
      (a + ε) ^ (p + 1) + (b + ε) ^ (p + 1) < 2 := by
    have h0 : (a + 0) ^ (p + 1) + (b + 0) ^ (p + 1) < 2 := by
      simpa using hscalar
    exact hcont.eventually_lt continuousAt_const h0
  have hev0' := (hev0.filter_mono nhdsWithin_le_nhds).and
    (eventually_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)) (a := 0))
  obtain ⟨ε, hε2, hεpos⟩ := hev0'.exists
  rw [Set.mem_Ioi] at hεpos
  set xp := a + ε with hxpdef
  set yp := b + ε with hypdef
  have hxp0 : 0 < xp := by rw [hxpdef]; linarith
  have hyp0 : 0 < yp := by rw [hypdef]; linarith
  have hfs : 1 < fs s xp := by
    rw [← haeq]
    exact fs_strictMonoOn hs0 (Set.mem_Ici.2 (by linarith))
      (Set.mem_Ici.2 (by linarith)) (by rw [hxpdef]; linarith)
  have hgs : 1 < gs s yp := by
    have hgb : gs s b = 1 := (gs_eq_one_iff hs0 (by linarith)).2 hbeq
    rw [← hgb]
    exact gs_strictMonoOn hs0 (Set.mem_Ioi.2 (by linarith))
      (Set.mem_Ioi.2 hyp0) (by rw [hypdef]; linarith)
  have hpoly := eventually_poly (q := p + 1) (xp := xp) (yp := yp)
    (by rw [hxpdef, hypdef]; linarith)
  have hNbd := eventually_N_degree_bound hp hs0 hxp0 hfs
  have hDbd := eventually_D_degree_bound hp hs0 hyp0 hgs
  refine ⟨s, hs0, ?_⟩
  filter_upwards [hpoly, hNbd, hDbd, eventually_ge_atTop 1]
    with i hpoly' hNbd' hDbd' hi
  have hcount := count_lt_kDiag hp hi hxp0.le hyp0.le hDbd'
    (fun j hj hle => hNbd' j hj hle)
    (by push_cast at hpoly' ⊢; exact hpoly')
  have hcard := le_card_branchVals hp (kDiag p i) (Li s i)
  exact lt_profile_of_count hcard hcount

/-- **Proposition `prop:diagnosis`**: for every fixed `n = p + 2 ≥ 3`,
all sufficiently large diagnosis indices `k_i` have finite critical
length. -/
theorem eventually_diagnosis {p : ℕ} (hp : 1 ≤ p) :
    ∀ᶠ i : ℕ in atTop, HasFiniteCriticalLength (profile p (kDiag p i)) := by
  obtain ⟨s, hs0, hovershoot⟩ := eventually_overshoot hp
  filter_upwards [hovershoot, eventually_ge_atTop 1] with i hover hi
  exact hasFiniteCriticalLength_of_overshoot
    (continuousOn_profile hp (kDiag p i)) (Li_pos hs0 hi) hover
    (profile_eventually_le_Ti_zero hp (kDiag p i) i hi)
    (profile_eventually_le_Ti hp hi)

/-- **Theorem `thm:main`** (for `n = p + 2 ≥ 3`): there exists `K(n)`
such that every Steklov index `k ≥ K(n)` has finite critical length.

The block-propagation input (Lemma `lem:propagation`, which is
[MetrasTschanz, Lemma 17] and whose proof lives in the cited paper) is
supplied as the explicit hypothesis `propagation`; everything else in
the paper's proof is formalized above.  The two-dimensional case
(`p = 0`) is the cited Fan–Tam–Yu theorem and is outside this paper. -/
theorem eventual_finiteness {p : ℕ} (hp : 1 ≤ p)
    (propagation : ∀ i k : ℕ, 1 ≤ i → kDiag p i ≤ k → k < kDiag p (i + 1) →
      HasFiniteCriticalLength (profile p (kDiag p i)) →
      HasFiniteCriticalLength (profile p k)) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → HasFiniteCriticalLength (profile p k) := by
  obtain ⟨i₀, hi₀⟩ := eventually_atTop.1 (eventually_diagnosis hp)
  set i₁ := max i₀ 1 with hi₁def
  refine ⟨kDiag p i₁, ?_⟩
  intro k hk
  set I := Nat.findGreatest (fun i => kDiag p i ≤ k) k with hIdef
  have hi₁k : i₁ ≤ k := le_trans (le_kDiag p i₁) hk
  have hIge : i₁ ≤ I := Nat.le_findGreatest hi₁k hk
  have hIle : kDiag p I ≤ k :=
    Nat.findGreatest_spec (P := fun i => kDiag p i ≤ k) (m := i₁) hi₁k hk
  have hIsucc : k < kDiag p (I + 1) := by
    rcases Nat.lt_or_ge I k with h | h
    · by_contra hcon
      push Not at hcon
      exact Nat.findGreatest_is_greatest
        (P := fun i => kDiag p i ≤ k) (n := k)
        (Nat.lt_succ_self I) (by omega) hcon
    · have hIk : I = k := le_antisymm (Nat.findGreatest_le k) h
      rw [hIk]
      have := le_kDiag p (k + 1)
      omega
  have hI1 : 1 ≤ I := le_trans (le_trans (le_max_right i₀ 1) le_rfl) hIge
  have hdiag : HasFiniteCriticalLength (profile p (kDiag p I)) :=
    hi₀ I (le_trans (le_max_left i₀ 1) hIge)
  exact propagation I k hI1 hIle hIsucc hdiag

/-- Theorem `thm:main` in the dimension variable `n ≥ 3` itself
(`p = n - 2`). -/
theorem eventual_finiteness_dim {n : ℕ} (hn : 3 ≤ n)
    (propagation : ∀ i k : ℕ, 1 ≤ i →
      kDiag (n - 2) i ≤ k → k < kDiag (n - 2) (i + 1) →
      HasFiniteCriticalLength (profile (n - 2) (kDiag (n - 2) i)) →
      HasFiniteCriticalLength (profile (n - 2) k)) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → HasFiniteCriticalLength (profile (n - 2) k) :=
  eventual_finiteness (by omega) propagation

/-! ## Complements: literal forms of eq:multiplicity, lem:limits, lem:scalar -/

/-- **eq:multiplicity**, in cleared-denominator form: for `j ≥ 1`,
`m_j · j! · (n-2)! = (2j + n - 2) · (j + n - 3)!` with `p = n - 2`. -/
theorem mult_factorial_form {p j : ℕ} (hj : 1 ≤ j) :
    mult p j * (j.factorial * p.factorial)
      = (2 * j + p) * (j + p - 1).factorial := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have h1 : (j' + 1 + p).choose p * p.factorial * (j' + 1).factorial
      = (j' + 1 + p).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial
      (show p ≤ j' + 1 + p by omega)
    rwa [show j' + 1 + p - p = j' + 1 by omega] at this
  have h2 : (j' + p).choose p * p.factorial * j'.factorial
      = (j' + p).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (show p ≤ j' + p by omega)
    rwa [show j' + p - p = j' by omega] at this
  have e0 : mult p (j' + 1)
      = (j' + 1 + p).choose p + (j' + p).choose p := by
    rw [mult, show j' + 1 + p - 1 = j' + p by omega]
  have e1 : (j' + 1 + p).factorial = (j' + 1 + p) * (j' + p).factorial := by
    rw [show j' + 1 + p = (j' + p) + 1 by omega, Nat.factorial_succ]
  have e2 : (j' + 1).factorial = (j' + 1) * j'.factorial := Nat.factorial_succ j'
  have e3 : j' + 1 + p - 1 = j' + p := by omega
  rw [e0, e3, Nat.add_mul]
  have t1 : (j' + 1 + p).choose p * ((j' + 1).factorial * p.factorial)
      = (j' + 1 + p) * (j' + p).factorial := by
    calc (j' + 1 + p).choose p * ((j' + 1).factorial * p.factorial)
        = (j' + 1 + p).choose p * p.factorial * (j' + 1).factorial := by ring
      _ = (j' + 1 + p).factorial := h1
      _ = (j' + 1 + p) * (j' + p).factorial := e1
  have t2 : (j' + p).choose p * ((j' + 1).factorial * p.factorial)
      = (j' + 1) * (j' + p).factorial := by
    calc (j' + p).choose p * ((j' + 1).factorial * p.factorial)
        = (j' + 1) * ((j' + p).choose p * p.factorial * j'.factorial) := by
          rw [e2]; ring
      _ = (j' + 1) * (j' + p).factorial := by rw [h2]
  rw [t1, t2]
  ring

/-- Lemma `lem:limits`, eq:flimit at `x = 0` (with `f_s(0) = 0`), by the
squeeze `0 ≤ N_j(R_i)/i ≤ (j_i/i)(u_i - 1)`. -/
theorem Nb_coupled_limit_zero {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s)
    (j : ℕ → ℝ) (hj : ∀ i, 0 ≤ j i)
    (hlim : Tendsto (fun i : ℕ => j i / i) atTop (𝓝 0)) :
    Tendsto (fun i : ℕ => Nb ν (j i) (Ri s i) / i) atTop (𝓝 0) := by
  have hexp : Tendsto (fun i : ℕ => Real.exp (2 * s * (j i / i) + s * ν * (1 / i)))
      atTop (𝓝 (Real.exp 0)) := by
    apply Real.continuous_exp.continuousAt.tendsto.comp
    have h1 : Tendsto (fun i : ℕ => 2 * s * (j i / i)) atTop (𝓝 (2 * s * 0)) :=
      tendsto_const_nhds.mul hlim
    have h2 : Tendsto (fun i : ℕ => s * ν * (1 / (i : ℝ))) atTop (𝓝 (s * ν * 0)) :=
      tendsto_const_nhds.mul tendsto_one_div_atTop_nhds_zero_nat
    have := h1.add h2
    rw [mul_zero, mul_zero, add_zero] at this
    exact this
  rw [Real.exp_zero] at hexp
  have hupper : Tendsto (fun i : ℕ =>
      (j i / i) * (Real.exp (2 * s * (j i / i) + s * ν * (1 / i)) - 1))
      atTop (𝓝 (0 * (1 - 1))) :=
    hlim.mul (hexp.sub tendsto_const_nhds)
  rw [show (0 : ℝ) * (1 - 1) = 0 by ring] at hupper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · -- `0 ≤ N/i`
    filter_upwards [eventually_ge_atTop 1] with i hi
    have hipos : (0 : ℝ) < i := by exact_mod_cast hi
    have hRi : 1 < Ri s i := one_lt_Ri hs hi
    have h1 : 0 ≤ Nb ν (j i) (Ri s i) :=
      Nv_nonneg hν (hj i) (one_lt_upow hν (hj i) hRi).le
    positivity
  · -- `N/i ≤ (j/i)(u - 1)`
    filter_upwards [eventually_ge_atTop 1] with i hi
    have hipos : (0 : ℝ) < i := by exact_mod_cast hi
    have hRi : 1 < Ri s i := one_lt_Ri hs hi
    have hu : upow ν (j i) (Ri s i)
        = Real.exp (2 * s * (j i / i) + s * ν * (1 / i)) := by
      rw [upow, Ri, ← Real.exp_log (show (0 : ℝ) < Real.exp (s / i) from Real.exp_pos _)]
      rw [Real.log_exp, ← Real.exp_mul]
      congr 1
      field_simp
    have hu1 : 1 < upow ν (j i) (Ri s i) := one_lt_upow hν (hj i) hRi
    have hkey : Nb ν (j i) (Ri s i) ≤ j i * (upow ν (j i) (Ri s i) - 1) := by
      rw [Nb, Nv]
      set u := upow ν (j i) (Ri s i)
      have hd : 0 < j i * u + j i + ν := by nlinarith [hj i]
      rw [div_le_iff₀ hd]
      have h1 : 0 ≤ j i * (u - 1) := mul_nonneg (hj i) (by linarith)
      nlinarith [mul_nonneg (mul_nonneg (hj i) (hj i)) (mul_pos (lt_trans one_pos hu1) (sub_pos.2 hu1)).le]
    rw [div_le_iff₀ hipos]
    have e : (j i / i) * (Real.exp (2 * s * (j i / i) + s * ν * (1 / i)) - 1) * i
        = j i * (Real.exp (2 * s * (j i / i) + s * ν * (1 / i)) - 1) := by
      field_simp
    rw [e, ← hu]
    exact hkey

/-- **Lemma `lem:scalar`**, existential form as stated in the paper:
for every `q ≥ 2` there is `s > 1` whose roots (eq:roots) satisfy
`a_s^q + b_s^q < 2`. -/
theorem lem_scalar (q : ℕ) (hq : 2 ≤ q) :
    ∃ s : ℝ, 1 < s ∧ ∃ a b : ℝ, a ∈ Set.Ioo (1 : ℝ) 2 ∧ fs s a = 1 ∧
      b ∈ Set.Ioo (1 / 2 : ℝ) 1 ∧ Real.tanh (s * b) = b ∧
      a ^ q + b ^ q < 2 := by
  set s : ℝ := 16 * (q : ℝ) + 28 with hsdef
  have hqle : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  have hs1 : (1 : ℝ) < s := by rw [hsdef]; linarith
  obtain ⟨a, ha, haeq⟩ := exists_root_a hs1.le
  obtain ⟨b, hb, hbeq⟩ := exists_root_b (s := s) (by rw [hsdef]; linarith)
  refine ⟨s, hs1, a, b, ha, haeq, hb, hbeq, ?_⟩
  exact scalar_inequality hq (by rw [hsdef]) ha.1 ha.2 haeq hb.1 hb.2 hbeq

end SteklovLengths
