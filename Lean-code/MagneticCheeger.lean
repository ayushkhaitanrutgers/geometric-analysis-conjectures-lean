import Mathlib

/-!
# BV compactness and positivity of magnetic Cheeger constants

Lean certification of the paper `magnetic_cheeger_positivity.tex`
("BV compactness and positivity of magnetic Cheeger constants", 24 Aug 2026),
which proves the large-domain magnetic frustration conjecture of
Chakradhar–Gittins–Habib–Peyerimhoff and deduces positivity of both
magnetic Cheeger constants.

## What is formalized, and how

Mathlib currently has **no** BV functions on manifolds, no sets of finite
perimeter, no traces/gluing for BV maps, and no magnetic Steklov operator
(only one-dimensional `eVariationOn`).  Accordingly:

* The geometric data of the paper — the compact manifold `M` with smooth
  boundary, its smooth relative domains `D`, the quantities `|M|`, `|∂M|`,
  `|D|`, `|∂_I D|`, `|∂_E D|`, the set of magnetic energies
  `{∫_D |d^η τ| dvol : τ ∈ C^∞(D, S¹)}`, and the gauge condition
  `η ∈ 𝔅_M` — enter as the fields of the structure `MagneticSetting`.
  Each field is annotated with the tex statement it transcribes.

* The BV compactness Lemma 2.1 (`lem:compactness`) of the paper is the one
  step whose proof genuinely needs the missing BV machinery
  (Ambrosio–Fusco–Pallara trace/gluing and BV compactness on a compact
  manifold).  Its *statement* is transcribed as the predicate
  `MagneticSetting.VanishingVariationGivesGauge`, and it is taken as an
  explicit hypothesis of the main theorems.

* Everything downstream of Lemma 2.1 is proved **completely** in Lean:
  the contradiction/sequence-extraction proof of Theorem 1.1
  (`thm:large-domain`), including the near-minimizer selection from the
  frustration infimum, and the entire four-case proof of Corollary 3.1
  (`cor:cheeger`), giving positivity of both magnetic Cheeger constants
  (defined here as genuine infima, `sInf`) and of the Steklov eigenvalue
  lower bound.

* The elementary pointwise inequalities and algebraic identities used
  inside the proof of Lemma 2.1 (the `W^{1,1}` bound, the jump bound
  `≤ 2`, the limit of the key estimate (eq:key-estimate), the phase
  cancellation, the curvature cancellation `(dη)u = 0 ⇒ dη = 0`, and the
  final gauge formula `η = dσ/(iσ)`) are also proved completely.

The trivial instance `trivialSetting` at the end witnesses that the
hypothesis structure is consistent (non-vacuous).
-/

open Filter Topology

namespace MagneticCheegerPaper

/-- **The geometric data of the paper** (tex, Section 1 "Definitions and
statement").  `(M^m, g)` is a compact Riemannian manifold with nonempty
smooth boundary; `η` is a smooth real 1-form.  The fields transcribe:

* `Domain` — the nonempty smooth relative domains `D ⊆ M`;
* `volM = |M| > 0`, `perimM = |∂M| > 0` (the boundary is nonempty and
  smooth, hence has positive `(m-1)`-measure);
* `vol D = |D|` (positive, since `D` is a nonempty open domain), with
  `vol D ≤ |M|`;
* `perimI D = |∂_I D| = |∂D ∩ int M| ≥ 0`;
* `perimE D = |∂_E D| = |∂D ∩ ∂M| ≥ 0`, with `perimE D ≤ |∂M|`;
* `Energy D = { ∫_D |d^η τ| dvol : τ ∈ C^∞(D, S¹) }`, the set of magnetic
  energies over which the frustration infimum runs; it is nonempty (the
  constant map `τ = 1` has energy `∫_D |η|`) and consists of nonnegative
  numbers;
* `Gaugeable` — the proposition `η ∈ 𝔅_M`, i.e. `η = dτ/(iτ)` for some
  `τ ∈ C^∞(M, S¹)`;
* `whole` — the domain `D = M` itself, with `|M| = volM`, `∂_I M = ∅`,
  `∂_E M = ∂M`. -/
structure MagneticSetting where
  /-- The type of nonempty smooth relative domains `D ⊆ M`. -/
  Domain : Type*
  /-- `|M|`. -/
  volM : ℝ
  volM_pos : 0 < volM
  /-- `|∂M|`. -/
  perimM : ℝ
  perimM_pos : 0 < perimM
  /-- `|D|`. -/
  vol : Domain → ℝ
  vol_pos : ∀ D, 0 < vol D
  vol_le_volM : ∀ D, vol D ≤ volM
  /-- `|∂_I D| = |∂D ∩ int M|`. -/
  perimI : Domain → ℝ
  perimI_nonneg : ∀ D, 0 ≤ perimI D
  /-- `|∂_E D| = |∂D ∩ ∂M|`. -/
  perimE : Domain → ℝ
  perimE_nonneg : ∀ D, 0 ≤ perimE D
  perimE_le_perimM : ∀ D, perimE D ≤ perimM
  /-- `{ ∫_D |d^η τ| dvol : τ ∈ C^∞(D, S¹) }`. -/
  Energy : Domain → Set ℝ
  energy_nonempty : ∀ D, (Energy D).Nonempty
  energy_nonneg : ∀ D, ∀ e ∈ Energy D, 0 ≤ e
  /-- `η ∈ 𝔅_M`. -/
  Gaugeable : Prop
  /-- The domain `D = M`. -/
  whole : Domain
  vol_whole : vol whole = volM
  perimI_whole : perimI whole = 0
  perimE_whole : perimE whole = perimM

namespace MagneticSetting

variable (S : MagneticSetting)

/-- **Magnetic frustration** (tex, Section 1):
`ι^η(D) := inf { ∫_D |d^η τ| dvol : τ ∈ C^∞(D, S¹) }`. -/
noncomputable def frust (D : S.Domain) : ℝ := sInf (S.Energy D)

lemma frust_nonneg (D : S.Domain) : 0 ≤ S.frust D :=
  Real.sInf_nonneg (S.energy_nonneg D)

/-- Near-minimizer selection (tex, proof of Theorem 1.1: "Choose
`τ_j ∈ C^∞(D_j, S¹)` within `j⁻¹` of the infimum"): any bound strictly
above the frustration infimum is beaten by an actual energy. -/
lemma exists_energy_lt {D : S.Domain} {b : ℝ} (hb : S.frust D < b) :
    ∃ e ∈ S.Energy D, e < b :=
  exists_lt_of_csInf_lt (S.energy_nonempty D) hb

/-- **Statement of Lemma 2.1** (tex, `lem:compactness`, "Vanishing magnetic
variation produces a global gauge"): if smooth relative domains `D_j`
satisfy `|M \ D_j| → 0` and `|∂_I D_j| → 0`, and there are maps
`τ_j ∈ C^∞(D_j, S¹)` with `∫_{D_j} |d^η τ_j| dvol → 0`, then `η ∈ 𝔅_M`.

The paper's proof of this lemma is a BV compactness argument
(extension by `1`, the trace/gluing formula of Ambrosio–Fusco–Pallara,
BV compactness on a compact manifold, and elliptic bootstrap for the
limit equation `du + iηu = 0`).  None of that machinery exists in Mathlib
(no BV functions on manifolds, no finite-perimeter sets, no traces), so
this predicate is taken as a hypothesis of the theorems below; the
elementary pointwise steps of its proof are certified separately at the
end of this file. -/
def VanishingVariationGivesGauge : Prop :=
  ∀ (D : ℕ → S.Domain) (e : ℕ → ℝ),
    (∀ j, e j ∈ S.Energy (D j)) →
    Tendsto (fun j => S.volM - S.vol (D j)) atTop (𝓝 0) →
    Tendsto (fun j => S.perimI (D j)) atTop (𝓝 0) →
    Tendsto e atTop (𝓝 0) →
    S.Gaugeable

/-- **Theorem 1.1** (tex, `thm:large-domain`, "Large-domain magnetic
frustration") — the conjecture of Chakradhar–Gittins–Habib–Peyerimhoff.
Suppose `η ∉ 𝔅_M`.  There are constants `ε, δ > 0` such that every
nonempty smooth relative domain `D ⊆ M` with `|D| ≥ (1-ε)|M|` and
`|∂_I D| ≤ ε` satisfies `ι^η(D) ≥ δ`.

The proof is the paper's Section 3 argument, formalized in full: negate,
extract a sequence `D_j` with `|D_j| ≥ (1 - j⁻¹)|M|`, `|∂_I D_j| ≤ j⁻¹`,
`ι^η(D_j) < j⁻¹`, choose near-minimizing energies, squeeze all three
quantities to zero, and apply Lemma 2.1. -/
theorem large_domain_frustration (hBV : S.VanishingVariationGivesGauge)
    (hη : ¬ S.Gaugeable) :
    ∃ ε > 0, ∃ δ > 0, ∀ D : S.Domain,
      (1 - ε) * S.volM ≤ S.vol D → S.perimI D ≤ ε → δ ≤ S.frust D := by
  by_contra hcon
  push Not at hcon
  -- For every `j`, the negation with `ε = δ = 1/(j+1)` produces a bad domain.
  have key : ∀ j : ℕ, ∃ D : S.Domain,
      (1 - 1 / ((j : ℝ) + 1)) * S.volM ≤ S.vol D ∧
        S.perimI D ≤ 1 / ((j : ℝ) + 1) ∧ S.frust D < 1 / ((j : ℝ) + 1) := by
    intro j
    exact hcon (1 / ((j : ℝ) + 1)) (by positivity) (1 / ((j : ℝ) + 1)) (by positivity)
  choose D hD1 hD2 hD3 using key
  -- Choose `τ_j` (i.e. its energy `e j`) within reach of the infimum.
  have keyE : ∀ j : ℕ, ∃ e ∈ S.Energy (D j), e < 1 / ((j : ℝ) + 1) := fun j =>
    S.exists_energy_lt (hD3 j)
  choose e he helt using keyE
  have hone : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  -- `|M \ D_j| = |M| - |D_j| → 0`.
  have h1 : Tendsto (fun j => S.volM - S.vol (D j)) atTop (𝓝 0) := by
    have hub : ∀ j : ℕ, S.volM - S.vol (D j) ≤ S.volM * (1 / ((j : ℝ) + 1)) := by
      intro j
      nlinarith [hD1 j, S.volM_pos]
    have hg0 : Tendsto (fun j : ℕ => S.volM * (1 / ((j : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using hone.const_mul S.volM
    exact squeeze_zero (fun j => sub_nonneg.2 (S.vol_le_volM (D j))) hub hg0
  -- `|∂_I D_j| → 0`.
  have h2 : Tendsto (fun j => S.perimI (D j)) atTop (𝓝 0) :=
    squeeze_zero (fun j => S.perimI_nonneg (D j)) hD2 hone
  -- `∫_{D_j} |d^η τ_j| dvol → 0`.
  have h3 : Tendsto e atTop (𝓝 0) :=
    squeeze_zero (fun j => S.energy_nonneg (D j) (e j) (he j))
      (fun j => (helt j).le) hone
  -- Lemma 2.1 now yields `η ∈ 𝔅_M`, contradicting the hypothesis.
  exact hη (hBV D e he h1 h2 h3)

/-- **Corollary 3.1, first half, denominator-cleared form** (tex,
`cor:cheeger`, proof of `h^η(M) > 0`): there is `c > 0` with
`ι^η(D) + |∂_I D| ≥ c |D|` for every admissible `D`.

Hypothesis `hCheeger` transcribes positivity of the ordinary relative
Cheeger constant `h(M) > 0` of the compact manifold `M`, in the standard
two-sided form `|∂_I D| ≥ h(M) · min(|D|, |M \ D|)` — this packages the
paper's use of the Cheeger inequality both for `D` (first case) and for
`M \ D` (second case, "whose interior boundary agrees with that of `D`").
This geometric fact is not in Mathlib.

The proof is the paper's four-case analysis, formalized in full. -/
theorem cheeger_volume_bound (hBV : S.VanishingVariationGivesGauge)
    (hη : ¬ S.Gaugeable)
    (hCheeger : ∃ h > 0, ∀ D : S.Domain,
      h * min (S.vol D) (S.volM - S.vol D) ≤ S.perimI D) :
    ∃ c > 0, ∀ D : S.Domain, c * S.vol D ≤ S.frust D + S.perimI D := by
  obtain ⟨ε, hε, δ, hδ, hthm⟩ := S.large_domain_frustration hBV hη
  obtain ⟨h, hh, hchee⟩ := hCheeger
  have hvolM := S.volM_pos
  refine ⟨min h (min (h * ε) (min (δ / S.volM) (ε / S.volM))),
    lt_min hh (lt_min (mul_pos hh hε) (lt_min (div_pos hδ hvolM) (div_pos hε hvolM))),
    fun D => ?_⟩
  set c := min h (min (h * ε) (min (δ / S.volM) (ε / S.volM))) with hcdef
  have hc1 : c ≤ h := min_le_left _ _
  have hc2 : c ≤ h * ε := le_trans (min_le_right _ _) (min_le_left _ _)
  have hc3 : c ≤ δ / S.volM :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hc4 : c ≤ ε / S.volM :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hfr := S.frust_nonneg D
  have hv := S.vol_pos D
  have hvle := S.vol_le_volM D
  have hpI := S.perimI_nonneg D
  rcases le_or_gt (S.vol D) (S.volM / 2) with hA | hAbig
  · -- Case 1 (tex): `|D| ≤ |M|/2`, so the Cheeger inequality for `D` applies.
    have hmin : min (S.vol D) (S.volM - S.vol D) = S.vol D := min_eq_left (by linarith)
    have hch := hchee D
    rw [hmin] at hch
    have hstep : c * S.vol D ≤ h * S.vol D := mul_le_mul_of_nonneg_right hc1 hv.le
    linarith
  · rcases lt_or_ge (S.vol D) ((1 - ε) * S.volM) with hBmid | hClarge
    · -- Case 2 (tex): `|M|/2 < |D| < (1-ε)|M|`; apply the Cheeger inequality
      -- to `M \ D`, whose interior boundary agrees with that of `D`.
      have hmin : min (S.vol D) (S.volM - S.vol D) = S.volM - S.vol D :=
        min_eq_right (by linarith)
      have hch := hchee D
      rw [hmin] at hch
      have hgap : ε * S.volM ≤ S.volM - S.vol D := by nlinarith
      have hs1 : c * S.vol D ≤ h * ε * S.vol D := mul_le_mul_of_nonneg_right hc2 hv.le
      have hs2 : h * ε * S.vol D ≤ h * ε * S.volM :=
        mul_le_mul_of_nonneg_left hvle (mul_nonneg hh.le hε.le)
      have hs3 : h * (ε * S.volM) ≤ h * (S.volM - S.vol D) :=
        mul_le_mul_of_nonneg_left hgap hh.le
      nlinarith
    · rcases le_or_gt (S.perimI D) ε with hpsmall | hplarge
      · -- Case 4 (tex): `|D| ≥ (1-ε)|M|` and `|∂_I D| ≤ ε`; Theorem 1.1
        -- gives `ι^η(D) ≥ δ`.
        have hfrb := hthm D hClarge hpsmall
        have hs1 : c * S.vol D ≤ δ / S.volM * S.vol D :=
          mul_le_mul_of_nonneg_right hc3 hv.le
        have hs2 : δ / S.volM * S.vol D ≤ δ / S.volM * S.volM :=
          mul_le_mul_of_nonneg_left hvle (div_nonneg hδ.le hvolM.le)
        have hs3 : δ / S.volM * S.volM = δ := by
          field_simp
        linarith
      · -- Case 3 (tex): `|∂_I D| > ε`.
        have hs1 : c * S.vol D ≤ ε / S.volM * S.vol D :=
          mul_le_mul_of_nonneg_right hc4 hv.le
        have hs2 : ε / S.volM * S.vol D ≤ ε / S.volM * S.volM :=
          mul_le_mul_of_nonneg_left hvle (div_nonneg hε.le hvolM.le)
        have hs3 : ε / S.volM * S.volM = ε := by
          field_simp
        linarith

/-- **Corollary 3.1, second half, denominator-cleared form** (tex,
`cor:cheeger`, proof of `(h^η)'(M) > 0`): there is `c' > 0` with
`ι^η(D) + |∂_I D| ≥ c' |∂_E D|` for every admissible `D`.

Hypothesis `hJammes` transcribes the relative isoperimetric fact
`h'(M) := inf_{|D| ≤ |M|/2} |∂_I D| / |∂_E D| > 0` used in the Steklov
Cheeger inequality (Jammes, Ann. Inst. Fourier 65 (2015), Théorème 1);
this geometric fact is not in Mathlib.

The proof is the paper's two-case argument: for `|D| ≤ |M|/2` use
Jammes' bound directly; for `|D| > |M|/2` use
`ι^η(D) + |∂_I D| ≥ c|D| ≥ c|M|/2 ≥ (c|M| / (2|∂M|)) |∂_E D|`. -/
theorem cheeger_boundary_bound (hBV : S.VanishingVariationGivesGauge)
    (hη : ¬ S.Gaugeable)
    (hCheeger : ∃ h > 0, ∀ D : S.Domain,
      h * min (S.vol D) (S.volM - S.vol D) ≤ S.perimI D)
    (hJammes : ∃ h' > 0, ∀ D : S.Domain,
      S.vol D ≤ S.volM / 2 → h' * S.perimE D ≤ S.perimI D) :
    ∃ c' > 0, ∀ D : S.Domain, c' * S.perimE D ≤ S.frust D + S.perimI D := by
  obtain ⟨c, hc, hvolbd⟩ := S.cheeger_volume_bound hBV hη hCheeger
  obtain ⟨h', hh', hjam⟩ := hJammes
  have hvolM := S.volM_pos
  have hperimM := S.perimM_pos
  have hpM0 : S.perimM ≠ 0 := hperimM.ne'
  have hKpos : 0 < c * S.volM / (2 * S.perimM) :=
    div_pos (mul_pos hc hvolM) (by linarith)
  refine ⟨min h' (c * S.volM / (2 * S.perimM)), lt_min hh' hKpos, fun D => ?_⟩
  have hfr := S.frust_nonneg D
  have hpE := S.perimE_nonneg D
  have hpI := S.perimI_nonneg D
  rcases le_or_gt (S.vol D) (S.volM / 2) with hsmall | hbig
  · -- `|D| ≤ |M|/2`: Jammes' relative isoperimetric bound.
    have hj := hjam D hsmall
    have hs1 : min h' (c * S.volM / (2 * S.perimM)) * S.perimE D ≤ h' * S.perimE D :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) hpE
    linarith
  · -- `|D| > |M|/2`: `|∂_E D| ≤ |∂M|` and the volume-form bound.
    have hb := hvolbd D
    have hs1 : min h' (c * S.volM / (2 * S.perimM)) * S.perimE D ≤
        c * S.volM / (2 * S.perimM) * S.perimE D :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) hpE
    have hs2 : c * S.volM / (2 * S.perimM) * S.perimE D ≤
        c * S.volM / (2 * S.perimM) * S.perimM :=
      mul_le_mul_of_nonneg_left (S.perimE_le_perimM D) hKpos.le
    have hs3 : c * S.volM / (2 * S.perimM) * S.perimM = c * S.volM / 2 := by
      field_simp
    have hs4 : c * (S.volM / 2) ≤ c * S.vol D :=
      mul_le_mul_of_nonneg_left hbig.le hc.le
    linarith

/-- **The first magnetic Cheeger constant** (tex, Section 1, from CGHP):
`h^η(M) := inf_D (ι^η(D) + |∂_I D|) / |D|`, the infimum over all nonempty
smooth relative domains (every such domain has `|D| > 0`, so no quotient
degenerates). -/
noncomputable def cheegerH : ℝ :=
  sInf (Set.range fun D : S.Domain => (S.frust D + S.perimI D) / S.vol D)

/-- **The second magnetic Cheeger constant** (tex, Section 1, from CGHP):
`(h^η)'(M) := inf_D (ι^η(D) + |∂_I D|) / |∂_E D|`.  Per the paper, a
quotient with zero denominator is `+∞`, so domains with `|∂_E D| = 0` do
not constrain the infimum; we therefore take the infimum over domains with
`|∂_E D| > 0` (nonempty: `D = M` has `|∂_E M| = |∂M| > 0`). -/
noncomputable def cheegerH' : ℝ :=
  sInf {r : ℝ | ∃ D : S.Domain, 0 < S.perimE D ∧
    (S.frust D + S.perimI D) / S.perimE D = r}

/-- **Corollary 3.1, positivity of `h^η(M)`** (tex, `cor:cheeger`). -/
theorem cheegerH_pos (hBV : S.VanishingVariationGivesGauge)
    (hη : ¬ S.Gaugeable)
    (hCheeger : ∃ h > 0, ∀ D : S.Domain,
      h * min (S.vol D) (S.volM - S.vol D) ≤ S.perimI D) :
    0 < S.cheegerH := by
  obtain ⟨c, hc, hbd⟩ := S.cheeger_volume_bound hBV hη hCheeger
  have hle : c ≤ S.cheegerH := by
    refine le_csInf ⟨_, ⟨S.whole, rfl⟩⟩ ?_
    rintro b ⟨D, rfl⟩
    rw [le_div_iff₀ (S.vol_pos D)]
    exact hbd D
  linarith

/-- **Corollary 3.1, positivity of `(h^η)'(M)`** (tex, `cor:cheeger`). -/
theorem cheegerH'_pos (hBV : S.VanishingVariationGivesGauge)
    (hη : ¬ S.Gaugeable)
    (hCheeger : ∃ h > 0, ∀ D : S.Domain,
      h * min (S.vol D) (S.volM - S.vol D) ≤ S.perimI D)
    (hJammes : ∃ h' > 0, ∀ D : S.Domain,
      S.vol D ≤ S.volM / 2 → h' * S.perimE D ≤ S.perimI D) :
    0 < S.cheegerH' := by
  obtain ⟨c', hc', hbd⟩ := S.cheeger_boundary_bound hBV hη hCheeger hJammes
  have hwhole : 0 < S.perimE S.whole := by
    rw [S.perimE_whole]; exact S.perimM_pos
  have hle : c' ≤ S.cheegerH' := by
    refine le_csInf ⟨_, ⟨S.whole, hwhole, rfl⟩⟩ ?_
    rintro b ⟨D, hD, rfl⟩
    rw [le_div_iff₀ hD]
    exact hbd D
  linarith

/-- **Corollary 3.1, full conclusion** (tex, `cor:cheeger`):
if `η ∉ 𝔅_M` then `h^η(M) > 0`, `(h^η)'(M) > 0`, and hence
`h^η(M) · (h^η)'(M) > 0`. -/
theorem magnetic_cheeger_positivity (hBV : S.VanishingVariationGivesGauge)
    (hη : ¬ S.Gaugeable)
    (hCheeger : ∃ h > 0, ∀ D : S.Domain,
      h * min (S.vol D) (S.volM - S.vol D) ≤ S.perimI D)
    (hJammes : ∃ h' > 0, ∀ D : S.Domain,
      S.vol D ≤ S.volM / 2 → h' * S.perimE D ≤ S.perimI D) :
    0 < S.cheegerH ∧ 0 < S.cheegerH' ∧ 0 < S.cheegerH * S.cheegerH' := by
  have h1 := S.cheegerH_pos hBV hη hCheeger
  have h2 := S.cheegerH'_pos hBV hη hCheeger hJammes
  exact ⟨h1, h2, mul_pos h1 h2⟩

/-- **Corollary 3.1, final assertion** (tex, `cor:cheeger`): combined with
the Cheeger–Jammes estimate `σ₁^η(M) ≥ (1/8) h^η(M) (h^η)'(M)` of CGHP,
Theorem 2.5 (hypothesis `hCJ`; the magnetic Steklov operator is not in
Mathlib, so its first eigenvalue enters as the real number `σ₁`), the
lower bound is strictly positive: `σ₁^η(M) > 0`. -/
theorem magnetic_steklov_eigenvalue_pos (hBV : S.VanishingVariationGivesGauge)
    (hη : ¬ S.Gaugeable)
    (hCheeger : ∃ h > 0, ∀ D : S.Domain,
      h * min (S.vol D) (S.volM - S.vol D) ≤ S.perimI D)
    (hJammes : ∃ h' > 0, ∀ D : S.Domain,
      S.vol D ≤ S.volM / 2 → h' * S.perimE D ≤ S.perimI D)
    {σ₁ : ℝ} (hCJ : S.cheegerH * S.cheegerH' / 8 ≤ σ₁) :
    0 < σ₁ := by
  have h := S.magnetic_cheeger_positivity hBV hη hCheeger hJammes
  have h8 : (0 : ℝ) < S.cheegerH * S.cheegerH' / 8 :=
    div_pos h.2.2 (by norm_num)
  linarith

end MagneticSetting

/-! ## Pointwise steps inside the proof of Lemma 2.1

The following lemmas certify the elementary (non-BV) computations in the
paper's proof of Lemma 2.1, at the pointwise/sequence level at which they
are used. -/

/-- Tex, proof of Lemma 2.1, the `W^{1,1}` bound
`∫_{D_j} |dτ_j| ≤ ∫_{D_j} |d^η τ_j| + ∫_{D_j} |η|`: pointwise, with
`a = dτ` and `b = iητ` (so `|b| = |η|` since `|τ| = 1`), this is
`‖a‖ ≤ ‖a + b‖ + ‖b‖`. -/
lemma norm_le_norm_add_add (a b : ℂ) : ‖a‖ ≤ ‖a + b‖ + ‖b‖ := by
  calc ‖a‖ = ‖a + b - b‖ := by rw [add_sub_cancel_right]
    _ ≤ ‖a + b‖ + ‖b‖ := norm_sub_le _ _

/-- Tex, proof of Lemma 2.1, the jump bound `‖J_j‖(M) ≤ 2|∂_I D_j|`:
"the jump between the two circle-valued traces has norm at most two"
(and likewise for the jump between a trace and the extension value `1`). -/
lemma jump_norm_le_two (a b : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ‖a - b‖ ≤ 2 := by
  calc ‖a - b‖ ≤ ‖a‖ + ‖b‖ := norm_sub_le a b
    _ = 2 := by rw [ha, hb]; norm_num

/-- Tex, eq. (key-estimate) together with "The right-hand side tends to
zero": if `0 ≤ ‖𝒟^η u_j‖(M) ≤ ∫_{D_j}|d^η τ_j| + ‖η‖_∞ |M \ D_j|
+ 2 |∂_I D_j|` and each of the three terms tends to zero, then
`‖𝒟^η u_j‖(M) → 0`. -/
lemma key_estimate_limit {v a b c : ℕ → ℝ} (K : ℝ) (hv : ∀ j, 0 ≤ v j)
    (hbd : ∀ j, v j ≤ a j + K * b j + 2 * c j)
    (ha : Tendsto a atTop (𝓝 0)) (hb : Tendsto b atTop (𝓝 0))
    (hc : Tendsto c atTop (𝓝 0)) :
    Tendsto v atTop (𝓝 0) := by
  have hsum : Tendsto (fun j => a j + K * b j + 2 * c j) atTop (𝓝 0) := by
    have := (ha.add (hb.const_mul K)).add (hc.const_mul 2)
    simpa using this
  exact squeeze_zero hv hbd hsum

/-- Tex, proof of Lemma 2.1, the curvature cancellation: commuting weak
mixed derivatives in `du = -iηu` "gives `(dη)u = 0`.  Since `|u| = 1`, it
follows that `dη = 0`" — pointwise, `w·u = 0` with `‖u‖ = 1` forces
`w = 0`. -/
lemma curvature_vanishes (w u : ℂ) (hu : ‖u‖ = 1) (h : w * u = 0) :
    w = 0 := by
  rcases mul_eq_zero.1 h with hw | hu0
  · exact hw
  · rw [hu0, norm_zero] at hu
    exact absurd hu zero_ne_one

/-- Tex, proof of Lemma 2.1, the local phase cancellation: with `η = dφ`
on a chart, `d(e^{iφ}u) = e^{iφ}(iη u + du) = e^{iφ}(iηu - iηu) = 0`
pointwise once `du = -iηu`. -/
lemma phase_cancellation (η : ℝ) (u : ℂ) :
    Complex.I * η * u + -(Complex.I * η) * u = 0 := by ring

/-- Tex, proof of Lemma 2.1, conjugating the parallel equation
(eq:parallel): from `du = -iηu` (with `η` real) one gets
`dσ = iησ` for `σ = ū` — pointwise, `conj(-(iη)·u) = iη·conj u`. -/
lemma conj_parallel (η : ℝ) (u : ℂ) :
    (starRingEnd ℂ) (-(Complex.I * η) * u) =
      Complex.I * η * (starRingEnd ℂ) u := by
  rw [map_mul, map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

/-- Tex, proof of Lemma 2.1, `σ = ū` is again circle-valued:
`σ·u = ū·u = |u|² = 1` when `|u| = 1`. -/
lemma unimodular_conj_mul (u : ℂ) (hu : ‖u‖ = 1) :
    (starRingEnd ℂ) u * u = 1 := by
  rw [Complex.conj_mul']
  norm_cast
  rw [hu]
  norm_num

/-- Tex, proof of Lemma 2.1, the final gauge formula: from `dσ = iησ`
and `σ` circle-valued (in particular `σ ≠ 0`),
`η = dσ/(iσ)`, i.e. `(iησ)/(iσ) = η`; hence `η ∈ 𝔅_M`. -/
lemma gauge_formula (η : ℝ) (σ : ℂ) (hσ : ‖σ‖ = 1) :
    Complex.I * η * σ / (Complex.I * σ) = η := by
  have h0 : σ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hσ
    exact zero_ne_one hσ
  rw [div_eq_iff (mul_ne_zero Complex.I_ne_zero h0)]
  ring

/-! ## Consistency

A trivial instance of `MagneticSetting` (together with a proof of its
compactness hypothesis) witnesses that the hypothesis structure used
above is non-vacuous. -/

/-- A trivial model of the geometric data (consistency witness). -/
noncomputable def trivialSetting : MagneticSetting where
  Domain := Unit
  volM := 1
  volM_pos := one_pos
  perimM := 1
  perimM_pos := one_pos
  vol := fun _ => 1
  vol_pos := fun _ => one_pos
  vol_le_volM := fun _ => le_refl 1
  perimI := fun _ => 0
  perimI_nonneg := fun _ => le_refl 0
  perimE := fun _ => 1
  perimE_nonneg := fun _ => zero_le_one
  perimE_le_perimM := fun _ => le_refl 1
  Energy := fun _ => {0}
  energy_nonempty := fun _ => ⟨0, rfl⟩
  energy_nonneg := fun _ e he => by simp_all
  Gaugeable := True
  whole := ()
  vol_whole := rfl
  perimI_whole := rfl
  perimE_whole := rfl

example : trivialSetting.VanishingVariationGivesGauge :=
  fun _ _ _ _ _ _ => trivial

example : ¬ trivialSetting.Gaugeable → False := fun h => h trivial

end MagneticCheegerPaper
