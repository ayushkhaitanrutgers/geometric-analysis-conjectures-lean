import Mathlib

/-!
# Infinite-Order Contact Does Not Force Containment for Nonintegral Stationary Varifolds

Formal certification of the paper `nonintegral_varifold_counterexample.tex`
("Infinite-Order Contact Does Not Force Containment for Nonintegral Stationary
Varifolds", on Question 30 (L30) of the problem list; the example refutes the
version of the question without the integrality hypothesis).

## The construction (§2 of the paper)

In `ℝ^{m+1}` (`Amb m := EuclideanSpace ℝ (Fin (m+1))`, with normal coordinate `0`),
set `h_j = 2⁻¹^{j+1}` (`hseq`), `a_j = e^{-4^{j+1}}` (`aseq`), let `P` be the
hyperplane `{x : x 0 = 0}` (`basePlane`) and `P_j = P + h_j e₀`.  The plane at height
`t` carries its `m`-dimensional area measure `planeMeasure m t`, the pushforward of
Lebesgue measure on `ℝ^m` under the isometric parametrization `emb m t : y ↦ (t, y)`.
The varifold's weight measure of eq. (2), `‖V‖ = |P| + ∑_j a_j |P_j|`, is `muV m`.
(The indices are shifted by one relative to the paper: `j ∈ ℕ` here corresponds to
`j ≥ 1` there; `hseq j = 2^{-(j+1)}`, `aseq j = e^{-4^{j+1}}`.)

## What is formalized, and how it matches the paper

Everything below is proved completely, with no axioms beyond Mathlib and no gaps.

* Radon / local finiteness ("the series of weight measures converges on compact
  sets"): instances `IsFiniteMeasureOnCompacts (muV m)` and
  `IsLocallyFiniteMeasure (muV m)`, via `summable_aseq` (`∑ a_j < ∞`).
* Support ("its support is contained in the countably rectifiable set `P ∪ ⋃_j P_j`",
  and "every such `P_j` belongs to `spt V`"): `support_muV` computes
  `spt ‖V‖ = {x : x 0 ∈ {0} ∪ {h_j}}` exactly, i.e. `spt ‖V‖ = P ∪ ⋃_j P_j`.
* Stationarity ("Every affine plane is stationary… thus `V` is stationary"): since
  every tangent plane of `V` is the common direction `P₀` of the parallel planes, the
  first variation is `δV(X) = ∫ div_{P₀} X d‖V‖` with `div_{P₀}` the tangential
  divergence (`tangentialDiv`, transcribing Simon, *GMT*, §16/§39).  Theorem
  `integral_tangentialDiv_planeMeasure` proves `δ|P_t|(X) = 0` for each plane (a
  genuine divergence-theorem computation, via Mathlib's integration by parts), and
  `stationary` proves `δV(X) = δ|P|(X) + ∑_j a_j δ|P_j|(X) = 0`, with the
  interchange justified by integrability, exactly as in the paper.
* Infinite-order contact (eq. (1), eq. (3), eq. (4) and the estimate
  `I(r) ≤ C_m r^{m+2} e^{-1/r²}`): `infDist_basePlane` identifies `dist(x, P)`;
  `contactIntegral` is `I(r)`; `tail_sum_le` is the superexponential tail bound
  `∑_{h_j<r} a_j ≤ C e^{-1/(2r²)}`; `Jint_le`/`contactIntegral_le` give
  `I(r) ≤ C_m r^{m+2} e^{-1/(2r²)}` (the same bound as the paper's up to the harmless
  factor `2` in the exponent), and `contactIntegral_isLittleO` /
  `contactIntegral_div_pow_tendsto` conclude `I(r) = o(r^N)` for every `N` — eq. (1).
* Non-containment ("the support is not contained in `P` in any neighborhood of the
  origin"): `support_not_locally_contained`, `support_not_subset_basePlane`, and
  `zero_mem_basePlane_inter_support` (`0 ∈ P ∩ spt V`).
* Non-integrality ("the multiplicity of `V` on `P_j` is `a_j ∉ ℤ`"): `muV_on_plane`
  shows `‖V‖ = a_j ⋅ (area)` on `P_j`, and `aseq_not_integer` shows `a_j ∉ ℤ`
  (`0 < a_j < 1`).
* Theorem 1, bundled: `infinite_order_contact_does_not_force_containment`.

## What is *not* formalizable in current Mathlib

Mathlib has no varifolds, no first variation, and no rectifiability; therefore
"stationary rectifiable varifold" cannot be stated abstractly.  We instead transcribe
the definitions concretely for this particular `V` (whose tangent planes are all equal
to `P₀`): the weight measure is `muV`, the first variation of `V` is the functional
`X ↦ ∫ tangentialDiv X d‖V‖` (this *is* `δV` for `V = |P| + ∑ a_j |P_j|`), and
rectifiability is witnessed by the explicit parametrizations `emb m t` together with
the support identity `support_muV`.  Under this (faithful) transcription every claim
of the paper is proved in full.
-/


open MeasureTheory Metric Filter Asymptotics Topology
open scoped ENNReal

namespace NonintegralVarifold

/-! ### The sequences `h_j` and `a_j` -/

/-- Heights of the parallel planes. -/
noncomputable def hseq (j : ℕ) : ℝ := (2:ℝ)⁻¹ ^ (j + 1)

/-- Weights of the parallel planes. -/
noncomputable def aseq (j : ℕ) : ℝ := Real.exp (-(4:ℝ) ^ (j + 1))

lemma hseq_pos (j : ℕ) : 0 < hseq j := by rw [hseq]; positivity

lemma hseq_ne_zero (j : ℕ) : hseq j ≠ 0 := (hseq_pos j).ne'

lemma aseq_pos (j : ℕ) : 0 < aseq j := Real.exp_pos _

lemma aseq_lt_one (j : ℕ) : aseq j < 1 := by
  rw [aseq, Real.exp_lt_one_iff]
  exact neg_lt_zero.2 (by positivity)

/-- The relation `a_j = e^{-h_j^{-2}}` from the paper. -/
lemma aseq_eq_exp_neg_inv_sq (j : ℕ) : aseq j = Real.exp (-((hseq j) ^ 2)⁻¹) := by
  have h2 : (hseq j) ^ 2 = ((4:ℝ) ^ (j+1))⁻¹ := by
    rw [hseq, pow_right_comm, ← inv_pow]
    norm_num
  rw [aseq, h2, inv_inv]

lemma hseq_tendsto : Tendsto hseq atTop (𝓝 0) := by
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 2⁻¹)
    (by norm_num : (2:ℝ)⁻¹ < 1)
  exact h.comp (tendsto_add_atTop_nat 1)

lemma aseq_le_geom (j : ℕ) : aseq j ≤ Real.exp (-1) ^ j := by
  rw [aseq, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.2
  have h4 : (j:ℝ) ≤ 4 ^ (j+1) := by
    calc (j:ℝ) ≤ 2 ^ j := by exact_mod_cast Nat.lt_two_pow_self.le
    _ ≤ 4 ^ j := pow_le_pow_left₀ (by norm_num) (by norm_num) j
    _ ≤ 4 ^ (j+1) := pow_le_pow_right₀ (by norm_num) (by omega)
  nlinarith
lemma summable_aseq : Summable aseq := by
  apply Summable.of_nonneg_of_le (fun j => (aseq_pos j).le) aseq_le_geom
  exact summable_geometric_of_lt_one (Real.exp_pos _).le
    (Real.exp_lt_one_iff.2 (by norm_num))

/-- The weights are not integers: `0 < a_j < 1`.  (Theorem 1: "V is not integral".) -/
theorem aseq_not_integer (j : ℕ) (n : ℤ) : aseq j ≠ (n : ℝ) := by
  intro h
  have h0 : (0:ℝ) < n := h ▸ aseq_pos j
  have h1 : (n:ℝ) < 1 := h ▸ aseq_lt_one j
  have : (0:ℤ) < n := by exact_mod_cast h0
  have : n < 1 := by exact_mod_cast h1
  omega

/-! ### The ambient space and the family of parallel planes -/

variable (m : ℕ)

/-- Ambient Euclidean space `ℝ^{m+1}`. -/
abbrev Amb := EuclideanSpace ℝ (Fin (m + 1))

/-- The base plane's model space `ℝ^m`. -/
abbrev Base := EuclideanSpace ℝ (Fin m)

/-- Extensionality via coordinates. -/
lemma ofLp_ext {k : ℕ} {x y : EuclideanSpace ℝ (Fin k)} (h : x.ofLp = y.ofLp) : x = y := by
  rw [← WithLp.toLp_ofLp 2 x, ← WithLp.toLp_ofLp 2 y, h]

/-- The linear isometry `ℝ^m ↪ ℝ^{m+1}` inserting a `0` first coordinate. -/
noncomputable def embL : Base m →ₗᵢ[ℝ] Amb m where
  toLinearMap :=
    { toFun := fun y => WithLp.toLp 2 (Fin.cons 0 y.ofLp)
      map_add' := by
        intro a b
        apply ofLp_ext
        simp only [WithLp.ofLp_add]
        funext j
        induction j using Fin.cases <;> simp
      map_smul' := by
        intro c a
        apply ofLp_ext
        simp only [WithLp.ofLp_smul, RingHom.id_apply]
        funext j
        induction j using Fin.cases <;> simp }
  norm_map' := by
    intro y
    have hsq : ‖(WithLp.toLp 2 (Fin.cons 0 y.ofLp) : Amb m)‖ ^ 2 = ‖y‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
        WithLp.ofLp_toLp, Fin.sum_univ_succ]
      simp
    calc ‖(WithLp.toLp 2 (Fin.cons 0 y.ofLp) : Amb m)‖
        = √(‖(WithLp.toLp 2 (Fin.cons 0 y.ofLp) : Amb m)‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ = √(‖y‖ ^ 2) := by rw [hsq]
      _ = ‖y‖ := Real.sqrt_sq (norm_nonneg _)

/-- The affine isometric parametrization of the plane at height `t`:
`y ↦ (t, y)`.  Its image is the plane `P_t = {x : x 0 = t}` (for `t = 0` the base plane `P`,
for `t = h_j` the plane `P_j` of the paper). -/
noncomputable def emb (t : ℝ) : Base m → Amb m :=
  fun y => EuclideanSpace.single 0 t + embL m y

variable {m}

lemma emb_ofLp (t : ℝ) (y : Base m) : (emb m t y).ofLp = Fin.cons t y.ofLp := by
  funext j
  induction j using Fin.cases with
  | zero => simp [emb, embL]
  | succ i => simp [emb, embL, Fin.succ_ne_zero]

lemma emb_ofLp_zero (t : ℝ) (y : Base m) : (emb m t y).ofLp 0 = t := by
  rw [emb_ofLp]; simp

lemma emb_ofLp_succ (t : ℝ) (y : Base m) (i : Fin m) :
    (emb m t y).ofLp i.succ = y.ofLp i := by
  rw [emb_ofLp]; simp

/-- Orthogonal projection onto the (model of the) plane: drop the first coordinate. -/
noncomputable def px (x : Amb m) : Base m := WithLp.toLp 2 (Fin.tail x.ofLp)

lemma px_ofLp (x : Amb m) (i : Fin m) : (px x).ofLp i = x.ofLp i.succ := by
  simp [px, Fin.tail]

lemma px_emb (t : ℝ) (y : Base m) : px (emb m t y) = y := by
  apply ofLp_ext
  funext i
  rw [px_ofLp, emb_ofLp_succ]

lemma emb_px_self (x : Amb m) : emb m (x.ofLp 0) (px x) = x := by
  apply ofLp_ext
  funext j
  induction j using Fin.cases with
  | zero => rw [emb_ofLp_zero]
  | succ i => rw [emb_ofLp_succ, px_ofLp]

/-- Pythagoras: the square norm splits into the normal and tangential parts. -/
lemma norm_sq_decomp (z : Amb m) : ‖z‖ ^ 2 = (z.ofLp 0) ^ 2 + ‖px z‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  simp [px_ofLp]

lemma abs_ofLp_zero_le_norm (z : Amb m) : |z.ofLp 0| ≤ ‖z‖ := by
  have h := norm_sq_decomp z
  have : (z.ofLp 0) ^ 2 ≤ ‖z‖ ^ 2 := by nlinarith [sq_nonneg ‖px z‖]
  calc |z.ofLp 0| = √((z.ofLp 0) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ √(‖z‖ ^ 2) := Real.sqrt_le_sqrt this
    _ = ‖z‖ := Real.sqrt_sq (norm_nonneg _)

lemma norm_px_le_norm (z : Amb m) : ‖px z‖ ≤ ‖z‖ := by
  have h := norm_sq_decomp z
  have : ‖px z‖ ^ 2 ≤ ‖z‖ ^ 2 := by nlinarith [sq_nonneg (z.ofLp 0)]
  calc ‖px z‖ = √(‖px z‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ √(‖z‖ ^ 2) := Real.sqrt_le_sqrt this
    _ = ‖z‖ := Real.sqrt_sq (norm_nonneg _)

lemma norm_emb (t : ℝ) (y : Base m) : ‖emb m t y‖ ^ 2 = t ^ 2 + ‖y‖ ^ 2 := by
  rw [norm_sq_decomp, emb_ofLp_zero, px_emb]

lemma emb_sub_emb (t : ℝ) (y z : Base m) :
    emb m t y - emb m t z = embL m (y - z) := by
  simp only [emb]
  rw [(embL m).map_sub]
  abel

lemma emb_isometry (t : ℝ) (y z : Base m) : dist (emb m t y) (emb m t z) = dist y z := by
  rw [dist_eq_norm, dist_eq_norm, emb_sub_emb, (embL m).norm_map]

lemma continuous_emb (t : ℝ) : Continuous (emb m t) :=
  continuous_const.add (embL m).continuous

lemma measurable_emb (t : ℝ) : Measurable (emb m t) :=
  (continuous_emb t).measurable

lemma contDiff_emb (t : ℝ) {n : WithTop ℕ∞} : ContDiff ℝ n (emb m t) := by
  unfold emb
  apply ContDiff.add contDiff_const
  rw [← (embL m).coe_toContinuousLinearMap]
  exact (embL m).toContinuousLinearMap.contDiff

lemma hasFDerivAt_emb (t : ℝ) (y : Base m) :
    HasFDerivAt (emb m t) (embL m).toContinuousLinearMap y := by
  apply HasFDerivAt.const_add
  have h := (embL m).toContinuousLinearMap.hasFDerivAt (x := y)
  simpa [(embL m).coe_toContinuousLinearMap] using h

lemma embL_single (i : Fin m) :
    embL m (EuclideanSpace.single i (1:ℝ)) = EuclideanSpace.single i.succ (1:ℝ) := by
  apply ofLp_ext
  funext j
  induction j using Fin.cases with
  | zero => simp [embL, (Fin.succ_ne_zero i).symm]
  | succ k => simp [embL, Fin.succ_inj, Pi.single_apply]

/-! ### The varifold's weight measure  (eq. (2) of the paper)

`|P_t|` is the `m`-dimensional area measure of the plane `P_t = {x : x 0 = t}`, realized as
the pushforward of Lebesgue measure on `ℝ^m` under the isometric parametrization `emb t`.
The weight measure of the varifold `V = |P| + ∑_j a_j |P_j|` is `muV`. -/

variable (m) in
/-- `m`-dimensional area measure of the affine plane at height `t`. -/
noncomputable def planeMeasure (t : ℝ) : Measure (Amb m) :=
  Measure.map (emb m t) volume

variable (m) in
/-- The weight measure `‖V‖ = |P| + ∑_{j} a_j |P_j|` of the varifold in eq. (2). -/
noncomputable def muV : Measure (Amb m) :=
  planeMeasure m 0 + Measure.sum (fun j => ENNReal.ofReal (aseq j) • planeMeasure m (hseq j))

lemma planeMeasure_apply (t : ℝ) {s : Set (Amb m)} (hs : MeasurableSet s) :
    planeMeasure m t s = volume ((emb m t) ⁻¹' s) :=
  Measure.map_apply (measurable_emb t) hs

lemma muV_apply {s : Set (Amb m)} (hs : MeasurableSet s) :
    muV m s = planeMeasure m 0 s + ∑' j, ENNReal.ofReal (aseq j) * planeMeasure m (hseq j) s := by
  rw [muV, Measure.add_apply, Measure.sum_apply _ hs]
  simp [Measure.smul_apply]

/-- The preimage of a closed ball under the parametrization of any plane lies in a fixed
closed ball of the model space. -/
lemma emb_preimage_closedBall_subset (t : ℝ) (x : Amb m) (R : ℝ) :
    (emb m t) ⁻¹' (closedBall x R) ⊆ closedBall (px x) R := by
  intro y hy
  simp only [Set.mem_preimage, mem_closedBall] at hy ⊢
  calc dist y (px x) = ‖px (emb m t y - x)‖ := by
        rw [dist_eq_norm]
        congr 1
        apply ofLp_ext
        funext i
        rw [px_ofLp, WithLp.ofLp_sub, WithLp.ofLp_sub]
        simp [emb_ofLp_succ, px_ofLp]
    _ ≤ ‖emb m t y - x‖ := norm_px_le_norm _
    _ = dist (emb m t y) x := (dist_eq_norm _ _).symm
    _ ≤ R := hy

lemma planeMeasure_closedBall_le (t : ℝ) (x : Amb m) (R : ℝ) :
    planeMeasure m t (closedBall x R) ≤ volume (closedBall (px x) R) := by
  rw [planeMeasure_apply t measurableSet_closedBall]
  exact measure_mono (emb_preimage_closedBall_subset t x R)

/-- Total plane weight `1 + ∑ a_j` is finite. -/
lemma total_weight_lt_top : (1 + ∑' j, ENNReal.ofReal (aseq j)) < ⊤ := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => (aseq_pos j).le) summable_aseq]
  exact ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, ENNReal.ofReal_lt_top⟩

lemma muV_closedBall_lt_top (x : Amb m) (R : ℝ) : muV m (closedBall x R) < ⊤ := by
  have hle : muV m (closedBall x R)
      ≤ (1 + ∑' j, ENNReal.ofReal (aseq j)) * volume (closedBall (px x) R) := by
    rw [muV_apply measurableSet_closedBall, add_mul, one_mul]
    apply add_le_add (planeMeasure_closedBall_le 0 x R)
    calc ∑' j, ENNReal.ofReal (aseq j) * planeMeasure m (hseq j) (closedBall x R)
        ≤ ∑' j, ENNReal.ofReal (aseq j) * volume (closedBall (px x) R) :=
          ENNReal.tsum_le_tsum (fun j => mul_le_mul' le_rfl (planeMeasure_closedBall_le _ x R))
      _ = (∑' j, ENNReal.ofReal (aseq j)) * volume (closedBall (px x) R) :=
          ENNReal.tsum_mul_right
  exact lt_of_le_of_lt hle (ENNReal.mul_lt_top total_weight_lt_top measure_closedBall_lt_top)

/-- The varifold is a (locally) Radon measure: finite on compact sets.
Certifies "the series of weight measures converges on compact sets" in the proof of Thm 1. -/
instance : IsFiniteMeasureOnCompacts (muV m) := by
  constructor
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  exact lt_of_le_of_lt (measure_mono hR) (muV_closedBall_lt_top 0 R)

instance : IsLocallyFiniteMeasure (muV m) := inferInstance

/-! ### The support of `‖V‖` -/

variable (m) in
/-- The base plane `P = ℝ^m × {0}`. -/
def basePlane : Set (Amb m) := {x | x.ofLp 0 = 0}

lemma emb_preimage_ball_eq (t : ℝ) (y : Base m) (ε : ℝ) :
    (emb m t) ⁻¹' (ball (emb m t y) ε) = ball y ε := by
  ext z
  simp only [Set.mem_preimage, mem_ball]
  rw [emb_isometry]

/-- Every point of the plane `P_t` lies in the support of its area measure. -/
lemma mem_support_planeMeasure (t : ℝ) (y : Base m) :
    emb m t y ∈ (planeMeasure m t).support := by
  rw [Measure.mem_support_iff_forall]
  intro U hU
  obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.1 hU
  calc (0:ℝ≥0∞) < planeMeasure m t (ball (emb m t y) ε) := by
        rw [planeMeasure_apply t measurableSet_ball, emb_preimage_ball_eq]
        exact measure_ball_pos volume y hε
    _ ≤ planeMeasure m t U := measure_mono hb

lemma planeMeasure_zero_le_muV : planeMeasure m 0 ≤ muV m :=
  Measure.le_add_right le_rfl

lemma smul_planeMeasure_le_muV (j : ℕ) :
    ENNReal.ofReal (aseq j) • planeMeasure m (hseq j) ≤ muV m :=
  Measure.le_add_left (Measure.le_sum _ j)

/-- Every point of the base plane belongs to `spt ‖V‖`. -/
lemma emb_zero_mem_support_muV (y : Base m) : emb m 0 y ∈ (muV m).support :=
  Measure.support_mono planeMeasure_zero_le_muV (mem_support_planeMeasure 0 y)

/-- Every point of the plane `P_j` belongs to `spt ‖V‖` (paper: "every such `P_j` belongs
to `spt V`"). -/
lemma emb_hseq_mem_support_muV (j : ℕ) (y : Base m) :
    emb m (hseq j) y ∈ (muV m).support := by
  apply Measure.support_mono (smul_planeMeasure_le_muV j)
  rw [Measure.mem_support_iff_forall]
  intro U hU
  have h := (Measure.mem_support_iff_forall _).1 (mem_support_planeMeasure (hseq j) y) U hU
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 (aseq_pos j)).ne' h.ne'

lemma zero_eq_emb : (0 : Amb m) = emb m 0 0 := by
  apply ofLp_ext
  funext j
  induction j using Fin.cases with
  | zero => rw [emb_ofLp_zero]; rfl
  | succ i => rw [emb_ofLp_succ]; rfl

/-- The origin lies in `P ∩ spt ‖V‖`  (Theorem 1: `0 ∈ P ∩ spt V`). -/
theorem zero_mem_basePlane_inter_support :
    (0 : Amb m) ∈ basePlane m ∩ (muV m).support := by
  constructor
  · simp [basePlane]
  · rw [zero_eq_emb]; exact emb_zero_mem_support_muV 0

/-- If a plane `P_t` misses a set at the level of first coordinates, its measure vanishes. -/
lemma planeMeasure_ball_eq_zero_of_ne (t : ℝ) (x : Amb m) (ε : ℝ)
    (h : ε ≤ |t - x.ofLp 0|) : planeMeasure m t (ball x ε) = 0 := by
  rw [planeMeasure_apply t measurableSet_ball]
  convert measure_empty (μ := (volume : Measure (Base m)))
  rw [Set.eq_empty_iff_forall_notMem]
  intro y hy
  rw [Set.mem_preimage, mem_ball, dist_eq_norm] at hy
  have hco : |t - x.ofLp 0| ≤ ‖emb m t y - x‖ := by
    have := abs_ofLp_zero_le_norm (emb m t y - x)
    rwa [WithLp.ofLp_sub, Pi.sub_apply, emb_ofLp_zero] at this
  linarith

/-- **The support of `‖V‖`** is exactly the union of the planes
`P ∪ ⋃_j P_j`; in particular it is contained in that countably rectifiable set.
Certifies "its support is contained in the countably rectifiable set `P ∪ ⋃_j P_j`". -/
theorem support_muV :
    (muV m).support = {x : Amb m | x.ofLp 0 ∈ insert (0:ℝ) (Set.range hseq)} := by
  apply Set.Subset.antisymm
  · intro x hx
    by_contra hxS
    -- the set of heights is compact, hence closed; pick a ball missing it
    have hS : IsClosed (insert (0:ℝ) (Set.range hseq)) :=
      hseq_tendsto.isCompact_insert_range.isClosed
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hS.isOpen_compl (x.ofLp 0) hxS
    have hzero : muV m (ball x ε) = 0 := by
      rw [muV_apply measurableSet_ball]
      have hbase : planeMeasure m 0 (ball x ε) = 0 := by
        apply planeMeasure_ball_eq_zero_of_ne
        by_contra hlt
        rw [not_le] at hlt
        exact hball (by rw [mem_ball, Real.dist_eq]; exact hlt) (Set.mem_insert _ _)
      have hj : ∀ j, planeMeasure m (hseq j) (ball x ε) = 0 := by
        intro j
        apply planeMeasure_ball_eq_zero_of_ne
        by_contra hlt
        rw [not_le] at hlt
        exact hball (by rw [mem_ball, Real.dist_eq]; exact hlt)
          (Set.mem_insert_of_mem _ ⟨j, rfl⟩)
      rw [hbase, zero_add, ENNReal.tsum_eq_zero.2 (fun j => by rw [hj j, mul_zero])]
    exact (Measure.notMem_support_iff_exists.2 ⟨ball x ε, ball_mem_nhds x hε, hzero⟩) hx
  · rintro x hx
    rcases hx with h0 | ⟨j, hj⟩
    · have := emb_zero_mem_support_muV (px x)
      rwa [← h0, emb_px_self] at this
    · have := emb_hseq_mem_support_muV j (px x)
      rwa [hj, emb_px_self] at this

/-- **Non-containment** (Theorem 1): in every ball around the origin the support of `‖V‖`
contains a point outside the plane `P`. -/
theorem support_not_locally_contained (ε : ℝ) (hε : 0 < ε) :
    ∃ x ∈ (muV m).support, x ∈ ball (0 : Amb m) ε ∧ x ∉ basePlane m := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (2:ℝ)⁻¹ < 1)
  refine ⟨emb m (hseq n) 0, emb_hseq_mem_support_muV n 0, ?_, ?_⟩
  · rw [mem_ball, dist_zero_right]
    have hnorm : ‖emb m (hseq n) 0‖ = hseq n := by
      have h := norm_emb (m := m) (hseq n) 0
      calc ‖emb m (hseq n) 0‖ = √(‖emb m (hseq n) 0‖ ^ 2) :=
            (Real.sqrt_sq (norm_nonneg _)).symm
        _ = √((hseq n) ^ 2) := by rw [h, norm_zero]; ring_nf
        _ = hseq n := Real.sqrt_sq (hseq_pos n).le
    rw [hnorm]
    calc hseq n = 2⁻¹ * 2⁻¹ ^ n := by rw [hseq, pow_succ]; ring
      _ < 2⁻¹ ^ n := mul_lt_of_lt_one_left (by positivity) (by norm_num)
      _ < ε := hn
  · simp only [basePlane, Set.mem_setOf_eq, emb_ofLp_zero]
    exact hseq_ne_zero n

/-- Restatement:  `spt ‖V‖ ⊄ P` in every neighborhood of the origin. -/
theorem support_not_subset_basePlane (ε : ℝ) (hε : 0 < ε) :
    ¬ ((muV m).support ∩ ball (0 : Amb m) ε ⊆ basePlane m) := by
  obtain ⟨x, hx, hxb, hxP⟩ := support_not_locally_contained (m := m) ε hε
  exact fun h => hxP (h ⟨hx, hxb⟩)

/-! ### Distance to the base plane -/

/-- The distance from a point to the base plane is the absolute value of its
first (normal) coordinate. -/
lemma infDist_basePlane (x : Amb m) : infDist x (basePlane m) = |x.ofLp 0| := by
  have hmem : x - EuclideanSpace.single 0 (x.ofLp 0) ∈ basePlane m := by
    simp [basePlane]
  apply le_antisymm
  · calc infDist x (basePlane m) ≤ dist x (x - EuclideanSpace.single 0 (x.ofLp 0)) :=
        infDist_le_dist_of_mem hmem
      _ = ‖EuclideanSpace.single (0 : Fin (m+1)) (x.ofLp 0)‖ := by
          rw [dist_eq_norm, sub_sub_cancel]
      _ = |x.ofLp 0| := by
          rw [PiLp.norm_single, Real.norm_eq_abs]
  · rw [le_infDist ⟨0, by simp [basePlane]⟩]
    intro y hy
    have h0 : y.ofLp 0 = 0 := hy
    calc |x.ofLp 0| = |(x - y).ofLp 0| := by rw [WithLp.ofLp_sub, Pi.sub_apply, h0, sub_zero]
      _ ≤ ‖x - y‖ := abs_ofLp_zero_le_norm _
      _ = dist x y := (dist_eq_norm x y).symm

/-! ### The contact integral `I(r)` and its superexponential smallness

`I(r) = ∫_{B_r(0)} dist(x, P)² d‖V‖(x)` is eq. (3) of the paper; the key estimate is
`I(r) ≤ C_m r^{m+2} e^{-1/(2r²)}` (the paper's display after eq. (4), with the harmless
constant `1/2` in the exponent), whence `I(r) = o(r^N)` for all `N` — eq. (1). -/

lemma measurable_normalCoordSq :
    Measurable (fun x : Amb m => ENNReal.ofReal ((x.ofLp 0) ^ 2)) := by
  apply ENNReal.measurable_ofReal.comp
  exact ((measurable_pi_apply 0).comp (WithLp.measurable_ofLp 2 _)).pow_const 2

lemma emb_preimage_ball_zero_subset (t r : ℝ) :
    (emb m t) ⁻¹' (ball (0 : Amb m) r) ⊆ ball (0 : Base m) r := by
  intro y hy
  rw [Set.mem_preimage, mem_ball, dist_zero_right] at hy
  rw [mem_ball, dist_zero_right]
  calc ‖y‖ = ‖px (emb m t y)‖ := by rw [px_emb]
    _ ≤ ‖emb m t y‖ := norm_px_le_norm _
    _ < r := hy

lemma emb_preimage_ball_zero_empty (t r : ℝ) (h : r ≤ |t|) :
    (emb m t) ⁻¹' (ball (0 : Amb m) r) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro y hy
  rw [Set.mem_preimage, mem_ball, dist_zero_right] at hy
  have : |t| ≤ ‖emb m t y‖ := by
    have h := abs_ofLp_zero_le_norm (emb m t y)
    rwa [emb_ofLp_zero] at h
  linarith

/-- The contribution of the plane at height `t ≥ 0` to the contact integral. -/
lemma plane_term_le (t r : ℝ) (ht : 0 ≤ t) :
    ∫⁻ x in ball (0 : Amb m) r, ENNReal.ofReal ((x.ofLp 0) ^ 2) ∂(planeMeasure m t)
      ≤ if t < r then ENNReal.ofReal (r ^ 2) * volume (ball (0 : Base m) r) else 0 := by
  rw [planeMeasure, setLIntegral_map measurableSet_ball measurable_normalCoordSq
    (measurable_emb t)]
  simp_rw [emb_ofLp_zero]
  rw [setLIntegral_const]
  split_ifs with hlt
  · exact mul_le_mul' (ENNReal.ofReal_le_ofReal (by nlinarith))
      (measure_mono (emb_preimage_ball_zero_subset t r))
  · rw [emb_preimage_ball_zero_empty t r (by rwa [abs_of_nonneg ht, ← not_lt]),
      measure_empty, mul_zero]

/-- The superexponential tail estimate: `∑_{h_j < r} a_j ≤ C e^{-1/(2r²)}`
(the paper's bound `∑_{j ≥ J} e^{-4^j} ≤ C e^{-4^J} ≤ C e^{-1/r²}`). -/
lemma tail_sum_le (r : ℝ) (hr : 0 < r) :
    ∑' j, (if hseq j < r then ENNReal.ofReal (aseq j) else 0)
      ≤ ENNReal.ofReal ((1 - Real.exp (-1))⁻¹ * Real.exp (-(2 * r ^ 2)⁻¹)) := by
  set B : ℝ := Real.exp (-1) with hB
  have hB0 : 0 ≤ B := (Real.exp_pos _).le
  have hB1 : B < 1 := Real.exp_lt_one_iff.2 (by norm_num)
  have key : ∀ j : ℕ, hseq j < r → aseq j ≤ Real.exp (-(2 * r ^ 2)⁻¹) * B ^ j := by
    intro j hj
    set A : ℝ := (2:ℝ) ^ (j + 1) with hA
    have hA1 : (1:ℝ) ≤ A := one_le_pow₀ (by norm_num)
    have hrA : 1 < r * A := by
      have h1 : (2:ℝ)⁻¹ ^ (j+1) * A = 1 := by
        rw [hA, ← mul_pow]
        norm_num
      have h2 : hseq j * A < r * A := by
        apply mul_lt_mul_of_pos_right hj
        linarith
      rw [hseq] at h2
      linarith [h1 ▸ h2]
    have hAsq : A ^ 2 = (4:ℝ) ^ (j + 1) := by
      rw [hA, pow_right_comm]
      norm_num
    have hj4 : (j : ℝ) ≤ 4 ^ (j+1) / 2 := by
      have : (j:ℝ) ≤ 2 ^ j := by exact_mod_cast Nat.lt_two_pow_self.le
      have h24 : (2:ℝ) ^ j ≤ 4 ^ j := pow_le_pow_left₀ (by norm_num) (by norm_num) j
      have h44 : (4:ℝ) ^ (j+1) = 4 * 4 ^ j := by ring
      nlinarith
    have hinv : (2 * r ^ 2)⁻¹ ≤ 4 ^ (j+1) / 2 := by
      have hr2 : (0:ℝ) < 2 * r ^ 2 := by positivity
      have hA2 : (1:ℝ) ≤ r ^ 2 * A ^ 2 := by nlinarith
      rw [inv_le_iff_one_le_mul₀ hr2]
      rw [← hAsq]
      nlinarith
    have hexp : (2 * r ^ 2)⁻¹ + (j:ℝ) ≤ (4:ℝ) ^ (j+1) := by linarith
    calc aseq j = Real.exp (-(4:ℝ) ^ (j+1)) := rfl
      _ ≤ Real.exp (-((2 * r ^ 2)⁻¹ + (j:ℝ))) := Real.exp_le_exp.2 (by linarith)
      _ = Real.exp (-(2 * r ^ 2)⁻¹) * B ^ j := by
          rw [hB, ← Real.exp_nat_mul, ← Real.exp_add]
          ring_nf
  calc ∑' j, (if hseq j < r then ENNReal.ofReal (aseq j) else 0)
      ≤ ∑' j, ENNReal.ofReal (Real.exp (-(2 * r ^ 2)⁻¹) * B ^ j) := by
        apply ENNReal.tsum_le_tsum
        intro j
        split_ifs with hj
        · exact ENNReal.ofReal_le_ofReal (key j hj)
        · exact bot_le
    _ = ENNReal.ofReal (∑' j, Real.exp (-(2 * r ^ 2)⁻¹) * B ^ j) := by
        rw [ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)
          ((summable_geometric_of_lt_one hB0 hB1).mul_left _)]
    _ = ENNReal.ofReal ((1 - B)⁻¹ * Real.exp (-(2 * r ^ 2)⁻¹)) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hB0 hB1, mul_comm]
    _ ≤ _ := le_refl _

variable (m) in
/-- The contact integral `I(r)` (eq. (3) of the paper), in `ℝ≥0∞`-valued form. -/
noncomputable def Jint (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in ball (0 : Amb m) r, ENNReal.ofReal ((x.ofLp 0) ^ 2) ∂(muV m)

variable (m) in
/-- `ω_m`, the volume of the unit `m`-ball. -/
noncomputable def unitBallVol : ℝ := (volume (ball (0 : Base m) 1)).toReal

variable (m) in
/-- The constant `C_m` in the paper's main estimate. -/
noncomputable def Cconst : ℝ := (1 - Real.exp (-1))⁻¹ * unitBallVol m

lemma unitBallVol_nonneg : 0 ≤ unitBallVol m := ENNReal.toReal_nonneg

lemma Cconst_nonneg : 0 ≤ Cconst m := by
  apply mul_nonneg _ unitBallVol_nonneg
  rw [inv_nonneg]
  have := Real.exp_lt_one_iff.2 (by norm_num : (-1:ℝ) < 0)
  linarith

/-- **The main estimate** `I(r) ≤ C_m r^{m+2} e^{-1/(2r²)}` (the paper's display after
eq. (4), with exponent `1/(2r²)` instead of `1/r²`; this loses nothing for eq. (1)). -/
theorem Jint_le (hm : 0 < m) (r : ℝ) (hr : 0 < r) :
    Jint m r ≤ ENNReal.ofReal (Cconst m * (r ^ (m + 2) * Real.exp (-(2 * r ^ 2)⁻¹))) := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  -- decompose the measure
  have hdecomp : Jint m r
      = (∫⁻ x in ball (0 : Amb m) r, ENNReal.ofReal ((x.ofLp 0) ^ 2) ∂(planeMeasure m 0))
        + ∑' j, ENNReal.ofReal (aseq j)
            * ∫⁻ x in ball (0 : Amb m) r, ENNReal.ofReal ((x.ofLp 0) ^ 2)
                ∂(planeMeasure m (hseq j)) := by
    rw [Jint, muV, Measure.restrict_add, lintegral_add_measure,
      Measure.restrict_sum _ measurableSet_ball, lintegral_sum_measure]
    congr 1
    refine tsum_congr fun j => ?_
    rw [Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]
  -- the base plane contributes zero
  have hbase : (∫⁻ x in ball (0 : Amb m) r, ENNReal.ofReal ((x.ofLp 0) ^ 2)
      ∂(planeMeasure m 0)) = 0 := by
    -- the integrand vanishes identically on the base plane
    rw [planeMeasure, setLIntegral_map measurableSet_ball measurable_normalCoordSq
      (measurable_emb 0)]
    simp_rw [emb_ofLp_zero]
    simp
  -- each parallel plane contributes at most `a_j · r² · vol(B_r^m)`, and only if `h_j < r`
  have hplanes : ∑' j, ENNReal.ofReal (aseq j)
      * ∫⁻ x in ball (0 : Amb m) r, ENNReal.ofReal ((x.ofLp 0) ^ 2)
          ∂(planeMeasure m (hseq j))
      ≤ (∑' j, (if hseq j < r then ENNReal.ofReal (aseq j) else 0))
        * (ENNReal.ofReal (r ^ 2) * volume (ball (0 : Base m) r)) := by
    rw [← ENNReal.tsum_mul_right]
    apply ENNReal.tsum_le_tsum
    intro j
    have h := plane_term_le (m := m) (hseq j) r (hseq_pos j).le
    split_ifs with hj
    · rw [if_pos hj] at h
      exact mul_le_mul' le_rfl h
    · rw [if_neg hj] at h
      rw [zero_mul]
      exact le_trans (mul_le_mul' le_rfl h) (by rw [mul_zero])
  -- volume of the m-ball of radius r
  have hvol : volume (ball (0 : Base m) r)
      = ENNReal.ofReal (r ^ m) * ENNReal.ofReal (unitBallVol m) := by
    rw [Measure.addHaar_ball volume (0 : Base m) hr.le, unitBallVol,
      ENNReal.ofReal_toReal measure_ball_lt_top.ne, finrank_euclideanSpace_fin]
  calc Jint m r ≤ 0 + (∑' j, (if hseq j < r then ENNReal.ofReal (aseq j) else 0))
        * (ENNReal.ofReal (r ^ 2) * volume (ball (0 : Base m) r)) := by
        rw [hdecomp, hbase]
        exact add_le_add le_rfl hplanes
    _ ≤ ENNReal.ofReal ((1 - Real.exp (-1))⁻¹ * Real.exp (-(2 * r ^ 2)⁻¹))
        * (ENNReal.ofReal (r ^ 2)
            * (ENNReal.ofReal (r ^ m) * ENNReal.ofReal (unitBallVol m))) := by
        rw [zero_add, hvol]
        exact mul_le_mul' (tail_sum_le r hr) le_rfl
    _ = ENNReal.ofReal ((1 - Real.exp (-1))⁻¹ * Real.exp (-(2 * r ^ 2)⁻¹)
          * (r ^ 2 * (r ^ m * unitBallVol m))) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul]
        apply mul_nonneg
        · have := Real.exp_lt_one_iff.2 (by norm_num : (-1:ℝ) < 0)
          have h2 : (0:ℝ) ≤ (1 - Real.exp (-1))⁻¹ := by rw [inv_nonneg]; linarith
          positivity
        · positivity
    _ = ENNReal.ofReal (Cconst m * (r ^ (m + 2) * Real.exp (-(2 * r ^ 2)⁻¹))) := by
        congr 1
        rw [Cconst]
        ring
  

variable (m) in
/-- The contact integral `I(r) = ∫_{B_r(0)} dist(x, P)² d‖V‖(x)`  (eq. (3) of the paper). -/
noncomputable def contactIntegral (r : ℝ) : ℝ :=
  ∫ x in ball (0 : Amb m) r, (infDist x (basePlane m)) ^ 2 ∂(muV m)

lemma contactIntegral_nonneg (r : ℝ) : 0 ≤ contactIntegral m r :=
  integral_nonneg fun _ => sq_nonneg _

lemma contactIntegral_eq_toReal (r : ℝ) : contactIntegral m r = (Jint m r).toReal := by
  rw [contactIntegral, Jint]
  have h1 : ∀ x : Amb m, (infDist x (basePlane m)) ^ 2 = (x.ofLp 0) ^ 2 := fun x => by
    rw [infDist_basePlane, sq_abs]
  simp_rw [h1]
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => sq_nonneg _)]
  exact (((measurable_pi_apply 0).comp (WithLp.measurable_ofLp 2 _)).pow_const
    2).aestronglyMeasurable

/-- The paper's main estimate for the Bochner form of `I(r)`. -/
theorem contactIntegral_le (hm : 0 < m) (r : ℝ) (hr : 0 < r) :
    contactIntegral m r ≤ Cconst m * (r ^ (m + 2) * Real.exp (-(2 * r ^ 2)⁻¹)) := by
  rw [contactIntegral_eq_toReal]
  apply ENNReal.toReal_le_of_le_ofReal _ (Jint_le hm r hr)
  have := Real.exp_pos (-(2 * r ^ 2)⁻¹)
  have := Cconst_nonneg (m := m)
  positivity

/-! ### `e^{-1/(2r²)}` beats every power of `r`  (paper: "`e^{-1/r²} = o(r^k)` for every `k`") -/

lemma tendsto_pow_mul_exp_neg_sq_half :
    ∀ k : ℕ, Tendsto (fun t : ℝ => t ^ k * Real.exp (-(t ^ 2 / 2))) atTop (𝓝 0) := by
  intro k
  -- first: `t^k e^{-t/2} → 0`
  have hhalf : Tendsto (fun t : ℝ => t ^ k * Real.exp (-(t / 2))) atTop (𝓝 0) := by
    have hcomp : Tendsto (fun t : ℝ => (2:ℝ) ^ k * ((t / 2) ^ k * Real.exp (-(t / 2))))
        atTop (𝓝 ((2:ℝ) ^ k * 0)) := by
      apply Tendsto.const_mul
      exact (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp
        (tendsto_id.atTop_div_const two_pos)
    rw [mul_zero] at hcomp
    apply hcomp.congr
    intro t
    rw [div_pow]
    field_simp
  -- then compare `e^{-t²/2} ≤ e^{-t/2}` for `t ≥ 1`
  apply squeeze_zero' ?_ ?_ hhalf
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
    have h0 : (0:ℝ) ≤ t := by linarith
    positivity
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
    have h0 : (0:ℝ) ≤ t := by linarith
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg h0 k)
    apply Real.exp_le_exp.2
    nlinarith

lemma tendsto_exp_neg_inv_sq_div_pow (k : ℕ) :
    Tendsto (fun r : ℝ => Real.exp (-(2 * r ^ 2)⁻¹) / r ^ k) (𝓝[>] 0) (𝓝 0) := by
  have hcomp : Tendsto (fun r : ℝ => (r⁻¹) ^ k * Real.exp (-((r⁻¹) ^ 2 / 2)))
      (𝓝[>] 0) (𝓝 0) :=
    (tendsto_pow_mul_exp_neg_sq_half k).comp tendsto_inv_nhdsGT_zero
  apply hcomp.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr0 : (0:ℝ) < r := hr
  have harg : ((r⁻¹) ^ 2 / 2) = (2 * r ^ 2)⁻¹ := by
    rw [inv_pow, mul_inv]
    ring
  rw [harg, inv_pow, div_eq_mul_inv, mul_comm]

/-- **Infinite-order contact** (eq. (1) of the paper, quantitative form):
`I(r)/r^N → 0` as `r → 0⁺`, for every `N`. -/
theorem contactIntegral_div_pow_tendsto (hm : 0 < m) (N : ℕ) :
    Tendsto (fun r => contactIntegral m r / r ^ N) (𝓝[>] 0) (𝓝 0) := by
  have hbound : Tendsto (fun r : ℝ => Cconst m * (Real.exp (-(2 * r ^ 2)⁻¹) / r ^ N))
      (𝓝[>] 0) (𝓝 (Cconst m * 0)) :=
    (tendsto_exp_neg_inv_sq_div_pow N).const_mul _
  rw [mul_zero] at hbound
  apply squeeze_zero' ?_ ?_ hbound
  · filter_upwards [self_mem_nhdsWithin] with r hr
    have hr0 : (0:ℝ) < r := hr
    exact div_nonneg (contactIntegral_nonneg _) (pow_nonneg hr0.le N)
  · filter_upwards [Ioo_mem_nhdsGT one_pos] with r hr1
    have hr0 : (0:ℝ) < r := hr1.1
    have h2 : contactIntegral m r ≤ Cconst m * Real.exp (-(2 * r ^ 2)⁻¹) := by
      have h1 := contactIntegral_le hm r hr0
      have hrpow : r ^ (m + 2) ≤ 1 := pow_le_one₀ hr0.le hr1.2.le
      have he := (Real.exp_pos (-(2 * r ^ 2)⁻¹)).le
      have h3 : r ^ (m + 2) * Real.exp (-(2 * r ^ 2)⁻¹) ≤ Real.exp (-(2 * r ^ 2)⁻¹) := by
        nlinarith
      have h4 := mul_le_mul_of_nonneg_left h3 (Cconst_nonneg (m := m))
      linarith
    calc contactIntegral m r / r ^ N
        ≤ (Cconst m * Real.exp (-(2 * r ^ 2)⁻¹)) / r ^ N := by gcongr
      _ = Cconst m * (Real.exp (-(2 * r ^ 2)⁻¹) / r ^ N) := by ring

/-- **Infinite-order contact** (eq. (1) of the paper, exactly as stated):
`I(r) = o(r^N)` as `r → 0⁺` for every `N ∈ ℕ`. -/
theorem contactIntegral_isLittleO (hm : 0 < m) (N : ℕ) :
    (fun r => contactIntegral m r) =o[𝓝[>] 0] (fun r : ℝ => r ^ N) := by
  rw [isLittleO_iff_tendsto']
  · exact contactIntegral_div_pow_tendsto hm N
  · filter_upwards [self_mem_nhdsWithin] with r hr h0
    exact absurd h0 (pow_ne_zero N (ne_of_gt hr))

/-! ### Stationarity  (paper: "Every affine plane is stationary" and `δV(X) = 0`)

All the planes `P`, `P_j` are parallel, with common tangent plane
`P₀ = span(e_1, …, e_m)` (in our coordinates, the directions `single i.succ 1`).
For a varifold all of whose tangent planes equal `P₀`, the first variation in the
direction of a compactly supported `C¹` vector field `X` is
`δV(X) = ∫ div_{P₀} X d‖V‖`, where `div_{P₀} X = ∑_{i=1}^m ∂_{e_i}⟨X, e_i⟩` is the
tangential divergence (Simon, *Lectures on GMT*, §16 and §39).  We transcribe this
definition and prove `δV(X) = 0` — a complete formal proof of the stationarity
computation in the paper, including the divergence theorem on each plane and the
absolutely convergent interchange of series and first variation. -/

variable (m) in
/-- The tangential divergence `div_P X = ∑_{i=1}^m ∂_{e_i} X^i` along the common tangent
plane of all the planes in the construction. -/
noncomputable def tangentialDiv (X : Amb m → Amb m) (x : Amb m) : ℝ :=
  ∑ i : Fin m, EuclideanSpace.proj i.succ (fderiv ℝ X x (EuclideanSpace.single i.succ 1))

lemma continuous_tangentialDiv {X : Amb m → Amb m} (hX : ContDiff ℝ 1 X) :
    Continuous (tangentialDiv m X) := by
  apply continuous_finsetSum
  intro i _
  exact (EuclideanSpace.proj i.succ).continuous.comp
    ((hX.continuous_fderiv one_ne_zero).clm_apply continuous_const)

lemma hasCompactSupport_tangentialDiv {X : Amb m → Amb m} (hXc : HasCompactSupport X) :
    HasCompactSupport (tangentialDiv m X) := by
  apply HasCompactSupport.intro hXc
  intro x hx
  have h0 : fderiv ℝ X x = 0 := by
    by_contra h
    exact hx (support_fderiv_subset ℝ (by simpa [Function.mem_support] using h))
  simp [tangentialDiv, h0]

/-- Integration by parts on the whole space: the integral of a directional derivative of a
compactly supported `C¹` function against an additive Haar measure vanishes.
(This is the divergence theorem underlying "every affine plane is stationary".) -/
lemma integral_fderiv_apply_eq_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {g : E → ℝ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) (v : E) : ∫ x, fderiv ℝ g x v ∂μ = 0 := by
  have hcont : Continuous fun x => fderiv ℝ g x v :=
    (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hsupp : HasCompactSupport fun x => fderiv ℝ g x v :=
    (hgc.fderiv ℝ).comp_left (g := fun L : E →L[ℝ] ℝ => L v) rfl
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := μ)
    (f := fun _ : E => (1:ℝ)) (g := g) (v := v)
    ?_ ?_ ?_ (fun x _ => differentiableAt_const 1)
    (fun x _ => (hg.differentiable one_ne_zero).differentiableAt)
  · simpa using h
  · have : (fun x => fderiv ℝ (fun _ : E => (1:ℝ)) x v * g x) = fun _ => 0 := by
      funext x
      simp
    rw [this]
    exact integrable_zero _ _ _
  · simpa using hcont.integrable_of_hasCompactSupport hsupp
  · simpa using hg.continuous.integrable_of_hasCompactSupport hgc

/-- Chain rule: the tangential partial derivatives of `X` along the plane at height `t`
are honest partial derivatives of the pulled-back components in the model space. -/
lemma proj_fderiv_eq (t : ℝ) {X : Amb m → Amb m} (hX : ContDiff ℝ 1 X) (i : Fin m)
    (y : Base m) :
    EuclideanSpace.proj i.succ (fderiv ℝ X (emb m t y) (EuclideanSpace.single i.succ 1))
      = fderiv ℝ (fun z => EuclideanSpace.proj i.succ (X (emb m t z))) y
          (EuclideanSpace.single i 1) := by
  have hXd : HasFDerivAt X (fderiv ℝ X (emb m t y)) (emb m t y) :=
    (hX.differentiable one_ne_zero).differentiableAt.hasFDerivAt
  have hcomp : HasFDerivAt (fun z => EuclideanSpace.proj i.succ (X (emb m t z)))
      ((EuclideanSpace.proj i.succ).comp
        ((fderiv ℝ X (emb m t y)).comp (embL m).toContinuousLinearMap)) y := by
    exact (EuclideanSpace.proj i.succ).hasFDerivAt.comp y (hXd.comp y (hasFDerivAt_emb t y))
  have hv : ((embL m).toContinuousLinearMap) (EuclideanSpace.single i (1:ℝ))
      = EuclideanSpace.single i.succ (1:ℝ) := by
    have h := congrFun ((embL m).coe_toContinuousLinearMap) (EuclideanSpace.single i (1:ℝ))
    rw [h]
    exact embL_single i
  rw [hcomp.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hv]

/-- **Each plane is stationary**: the tangential divergence of a compactly supported `C¹`
field integrates to zero over every plane of the construction  (paper: "Every affine
plane is stationary", `δ|P_j|(X) = 0`). -/
theorem integral_tangentialDiv_planeMeasure (t : ℝ) {X : Amb m → Amb m}
    (hX : ContDiff ℝ 1 X) (hXc : HasCompactSupport X) :
    ∫ x, tangentialDiv m X x ∂(planeMeasure m t) = 0 := by
  rw [planeMeasure, integral_map (measurable_emb t).aemeasurable
    (continuous_tangentialDiv hX).aestronglyMeasurable]
  -- the preimage of the support is compact in the model space
  have hpre : IsCompact ((emb m t) ⁻¹' (tsupport X)) := by
    obtain ⟨R, hR⟩ := hXc.isBounded.subset_closedBall 0
    apply IsCompact.of_isClosed_subset (isCompact_closedBall (px (0 : Amb m)) R)
      ((isClosed_tsupport X).preimage (continuous_emb t))
    exact (Set.preimage_mono hR).trans (emb_preimage_closedBall_subset t 0 R)
  -- component functions in the model space
  have hgC : ∀ i : Fin m, ContDiff ℝ 1 (fun z => EuclideanSpace.proj (Fin.succ i) (X (emb m t z))) :=
    fun i => by
      simpa [Function.comp_def] using
        ((EuclideanSpace.proj i.succ).contDiff.comp (hX.comp (contDiff_emb t)))
  have hgsupp : ∀ i : Fin m,
      HasCompactSupport (fun z => EuclideanSpace.proj (Fin.succ i) (X (emb m t z))) := by
    intro i
    apply HasCompactSupport.intro hpre
    intro y hy
    have hzero : X (emb m t y) = 0 := image_eq_zero_of_notMem_tsupport hy
    rw [hzero, map_zero]
  -- rewrite the integrand via the chain rule
  have hrw : (fun y => tangentialDiv m X (emb m t y))
      = fun y => ∑ i : Fin m,
          fderiv ℝ (fun z => EuclideanSpace.proj (Fin.succ i) (X (emb m t z))) y
            (EuclideanSpace.single i 1) := by
    funext y
    exact Finset.sum_congr rfl fun i _ => proj_fderiv_eq t hX i y
  rw [hrw, integral_finsetSum]
  · exact Finset.sum_eq_zero fun i _ =>
      integral_fderiv_apply_eq_zero volume (hgC i) (hgsupp i) _
  · intro i _
    have hcont : Continuous fun y =>
        fderiv ℝ (fun z => EuclideanSpace.proj (Fin.succ i) (X (emb m t z))) y
          (EuclideanSpace.single i 1) :=
      ((hgC i).continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hsupp : HasCompactSupport fun y =>
        fderiv ℝ (fun z => EuclideanSpace.proj (Fin.succ i) (X (emb m t z))) y
          (EuclideanSpace.single i 1) :=
      ((hgsupp i).fderiv ℝ).comp_left (g := fun L : Base m →L[ℝ] ℝ => L _) rfl
    exact hcont.integrable_of_hasCompactSupport hsupp

/-- **`V` is stationary** (Theorem 1): the first variation
`δV(X) = δ|P|(X) + ∑_j a_j δ|P_j|(X) = 0` vanishes for every compactly supported `C¹`
vector field `X`; the interchange of sum and integral is justified by absolute
convergence (integrability of `div_P X` against the Radon measure `‖V‖`). -/
theorem stationary {X : Amb m → Amb m} (hX : ContDiff ℝ 1 X) (hXc : HasCompactSupport X) :
    ∫ x, tangentialDiv m X x ∂(muV m) = 0 := by
  have hint : Integrable (tangentialDiv m X) (muV m) :=
    (continuous_tangentialDiv hX).integrable_of_hasCompactSupport
      (hasCompactSupport_tangentialDiv hXc)
  have h1 : Integrable (tangentialDiv m X) (planeMeasure m 0) :=
    hint.mono_measure planeMeasure_zero_le_muV
  have h2 : Integrable (tangentialDiv m X)
      (Measure.sum fun j => ENNReal.ofReal (aseq j) • planeMeasure m (hseq j)) :=
    hint.mono_measure (Measure.le_add_left le_rfl)
  have h3 : ∀ j : ℕ, ∫ x, tangentialDiv m X x
      ∂(ENNReal.ofReal (aseq j) • planeMeasure m (hseq j)) = 0 := by
    intro j
    rw [integral_smul_measure, integral_tangentialDiv_planeMeasure (hseq j) hX hXc,
      smul_zero]
  rw [muV, integral_add_measure h1 h2,
    integral_tangentialDiv_planeMeasure 0 hX hXc, integral_sum_measure h2,
    tsum_congr h3, tsum_zero, add_zero]

/-! ### The multiplicity of `V` on `P_j` is the non-integer `a_j`
(paper: "Finally, the multiplicity of `V` on `P_j` is `a_j = e^{-4^j} ∉ ℤ`.
Thus `V` is not an integral varifold.") -/

lemma hseq_strictAnti : StrictAnti hseq := by
  intro a b hab
  apply pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num)
  omega

/-- On any measurable piece of the plane `P_j`, the measure `‖V‖` is exactly
`a_j` times the `m`-dimensional area: the varifold has constant multiplicity `a_j` on
`P_j`, and `a_j ∉ ℤ` by `aseq_not_integer`. -/
theorem muV_on_plane (j : ℕ) {s : Set (Amb m)} (hs : MeasurableSet s)
    (hsub : s ⊆ {x : Amb m | x.ofLp 0 = hseq j}) :
    muV m s = ENNReal.ofReal (aseq j) * volume ((emb m (hseq j)) ⁻¹' s) := by
  have hplane : ∀ t : ℝ, t ≠ hseq j → planeMeasure m t s = 0 := by
    intro t ht
    rw [planeMeasure_apply t hs]
    convert measure_empty (μ := (volume : Measure (Base m)))
    rw [Set.eq_empty_iff_forall_notMem]
    intro y hy
    exact ht (by rw [← emb_ofLp_zero t y]; exact hsub hy)
  rw [muV_apply hs, hplane 0 (hseq_ne_zero j).symm, zero_add,
    tsum_eq_single j (fun k hk => by
      rw [hplane (hseq k) (fun h => hk (hseq_strictAnti.injective h)), mul_zero]),
    planeMeasure_apply _ hs]

/-! ### Theorem 1, bundled -/

/-- **Theorem 1 of the paper.**  For every `m ≥ 1` there are a locally finite (Radon)
measure `V` on `ℝ^{m+1}` — the weight measure of the stationary rectifiable varifold
`|P| + ∑_j a_j |P_j|` — and an `m`-plane `P` through `0 ∈ spt V` such that:

* `V` is stationary: its first variation `δV(X) = ∫ div_P X dV` vanishes for every
  compactly supported `C¹` vector field (all tangent planes of `V` are the direction
  of `P`, so `div_P` *is* the tangential divergence of the varifold);
* `V` has infinite-order contact with `P` at the origin:
  `∫_{B_r(0)} dist(x,P)² dV(x) = o(r^N)` for every `N` (eq. (1) with `M = P`);
* yet `spt V ⊄ P` in every neighborhood of the origin.

The final conjunct is the paper's non-integrality assertion: `V` carries a constant
multiplicity `mult j` on (every measurable piece of) each plane `P_j`, and no
`mult j` is an integer — so `V` is not an integral varifold
(witnesses: `muV_on_plane`, `aseq_not_integer`). -/
theorem infinite_order_contact_does_not_force_containment (m : ℕ) (hm : 0 < m) :
    ∃ (V : Measure (Amb m)) (P : Set (Amb m)),
      IsLocallyFiniteMeasure V
      ∧ (0 : Amb m) ∈ P ∩ V.support
      ∧ (∀ X : Amb m → Amb m, ContDiff ℝ 1 X → HasCompactSupport X →
          ∫ x, tangentialDiv m X x ∂V = 0)
      ∧ (∀ N : ℕ, (fun r => ∫ x in ball (0 : Amb m) r, infDist x P ^ 2 ∂V)
            =o[𝓝[>] 0] (fun r : ℝ => r ^ N))
      ∧ (∀ ε : ℝ, 0 < ε → ¬ (V.support ∩ ball (0 : Amb m) ε ⊆ P))
      ∧ (∃ mult : ℕ → ℝ, (∀ j : ℕ, ∀ n : ℤ, mult j ≠ (n : ℝ)) ∧
          ∀ j : ℕ, ∀ s : Set (Amb m), MeasurableSet s →
            s ⊆ {x : Amb m | x.ofLp 0 = hseq j} →
            V s = ENNReal.ofReal (mult j) * volume ((emb m (hseq j)) ⁻¹' s)) := by
  refine ⟨muV m, basePlane m, inferInstance, zero_mem_basePlane_inter_support,
    fun X hX hXc => stationary hX hXc, fun N => contactIntegral_isLittleO hm N,
    fun ε hε => support_not_subset_basePlane ε hε,
    aseq, fun j n => aseq_not_integer j n,
    fun j s hs hsub => muV_on_plane j hs hsub⟩

end NonintegralVarifold
