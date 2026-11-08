module

public import LDPC.PaperLemmas.SharedQueries
public import LDPC.Helpers.SpotSampling

/-! The main folding argument, including
its explicit check-count loss. This is separate from the check-sampling test. -/
@[expose] public section
open scoped ProbabilityTheory
namespace SmoothLDPC.Protocol

variable {L R F : Type} [Fintype L] [DecidableEq L] [Nonempty L]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Field F] [DecidableEq F] [Fintype F] {G : TannerGraph L R}

omit [Fintype F] [Nonempty L] [Nonempty R] in
/-- A word's failed checks must touch its error relative to any original codeword. -/
theorem failed_checks_le_distance {c k : ℕ} (hreg : G.IsRegular c k)
    (H : G.WeightedSystem F) (w cw : L → F) (hcw : cw ∈ H.code) :
    (support (H.check w)).card ≤ c * distance w cw := by
  have h := badChecks_card_le_pairDistance hreg H w 0 cw 0 hcw H.code.zero_mem
  have hchecks : H.badChecks w 0 = support (H.check w) := by
    classical
    ext j
    simp only [TannerGraph.WeightedSystem.badChecks, Finset.mem_filter, Finset.mem_univ,
      true_and, mem_support]
    have hz : H.check (0 : L → F) j = 0 := by simp [TannerGraph.WeightedSystem.check]
    simp [hz]
  have hpair : pairDistance w 0 cw 0 = distance w cw := by
    simp [pairDistance, distance, support]
  rw [hchecks, hpair] at h
  exact h

omit [Nonempty L] [Nonempty R] in
/-- A fixed violated input check can cancel at at most one folding challenge. -/
theorem check_cancellation_probability (H : G.WeightedSystem F) (u v : L → F)
    (j : R) (hj : j ∈ H.badChecks u v) :
    Pr_{let r ← $ᵖ F}[H.check (u + r • v) j = 0] ≤ (Fintype.card F : ENNReal)⁻¹ := by
  classical
  apply LegacyProbability.prob_uniform_le_inv_of_card_le_one
  apply Finset.card_le_one.mpr
  intro r hr z hz
  have he (a : F) : H.check (u + a • v) j = H.check u j + a * H.check v j := by
    change H.checkMap (u + a • v) j = _
    simp [map_add, map_smul, TannerGraph.WeightedSystem.checkMap, smul_eq_mul]
  have hr' := (Finset.mem_filter.mp hr).2
  have hz' := (Finset.mem_filter.mp hz).2
  rw [he] at hr' hz'
  have hv : H.check v j ≠ 0 := by
    intro hv
    have hu : H.check u j = 0 := by simpa [hv] using hr'
    simp [TannerGraph.WeightedSystem.badChecks, hu, hv] at hj
  apply mul_right_cancel₀ hv
  linear_combination hr' - hz'

omit [Nonempty L] in
/-- Removing the few-violations premise by cancellation counting costs |R|/|F|. -/
theorem combined_folding_of_smooth (H : G.WeightedSystem F) {c k : ℕ} {α P ρ θ : ℚ}
    (hreg : G.IsRegular c k) (hc : 0 < c) (hs : IsSmooth H α P ρ)
    (hθ : θ ≤ ρ) (hthreshold : (c : ℚ) * θ ≤ α * Fintype.card R)
    (u v : L → F) (hfar : PairFar H.code P u v) :
    Pr_{let r ← $ᵖ F}[GoodFold H.code θ u v r] ≤
      (Fintype.card R : ENNReal) / Fintype.card F := by
  classical
  by_cases hb : ((H.badChecks u v).card : ℚ) ≤ α * Fintype.card R
  · have hle := LegacyProbability.Pr_le_Pr_of_implies ($ᵖ F)
      (GoodFold H.code θ u v) (GoodFold H.code ρ u v)
      (fun _ h => by obtain ⟨cw, hcw, hd⟩ := h; exact ⟨cw, hcw, hd.trans_le hθ⟩)
    apply (hle.trans (LegacyProbability.prob_uniform_le_inv_of_card_le_one _
      (theorem_8_card H hs u v hfar hb))).trans
    simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_right
      (show (1 : ENNReal) ≤ Fintype.card R by exact_mod_cast Fintype.card_pos)
      (show (0 : ENNReal) ≤ (Fintype.card F : ENNReal)⁻¹ from zero_le)
  · let W := H.badChecks u v
    have himp : ∀ r, GoodFold H.code θ u v r →
        ∃ j : W, H.check (u + r • v) j = 0 := by
      intro r hg
      obtain ⟨cw, hcw, hd⟩ := hg
      by_contra hn
      have hsub : W ⊆ support (H.check (u + r • v)) := by
        intro j hj
        apply (mem_support _ _).mpr
        exact fun hz => hn ⟨⟨j, hj⟩, hz⟩
      have hcount := (Finset.card_le_card hsub).trans
        (failed_checks_le_distance hreg H (u + r • v) cw hcw)
      have hcount' : (W.card : ℚ) ≤ c * distance (u + r • v) cw := by exact_mod_cast hcount
      have hstrict := mul_lt_mul_of_pos_left hd (show (0 : ℚ) < c by exact_mod_cast hc)
      exact hb (hcount'.trans (hstrict.le.trans hthreshold))
    have hle := LegacyProbability.Pr_le_Pr_of_implies ($ᵖ F) _ _ himp
    have hu := LegacyProbability.Pr_exists_le ($ᵖ F) (fun (j : W) r => H.check (u + r • v) j = 0)
    apply (hle.trans hu).trans
    calc
      _ ≤ ∑ _j : W, (Fintype.card F : ENNReal)⁻¹ :=
        Finset.sum_le_sum fun j _ => check_cancellation_probability H u v j j.property
      _ = (W.card : ENNReal) * (Fintype.card F : ENNReal)⁻¹ := by simp
      _ ≤ (Fintype.card R : ENNReal) * (Fintype.card F : ENNReal)⁻¹ :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_univ W) zero_le
      _ = _ := by rw [div_eq_mul_inv]

end SmoothLDPC.Protocol
