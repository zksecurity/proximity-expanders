module

public import LDPC.Helpers.MCAAgreement

/-! Smoothness to ArkLib's exact, closed-radius MCA event and parity-query soundness. -/
@[expose] public section
open scoped BigOperators ProbabilityTheory
namespace SmoothLDPC
namespace MCA
open CoreDefinitions LinearCode

variable {L R F : Type} [Fintype L] [DecidableEq L]
    [Field F] [DecidableEq F] [Fintype F]

/-- Once all nearby codewords align, MCA failure cancels a genuine error coordinate. -/
theorem cancellation_of_alignment [Nonempty L] (C : Submodule F (L → F)) (ρ : ℚ)
    (u v cu cv : L → F) (hcu : cu∈C) (hcv : cv∈C)
    (halign : ∀ (z : F) (c : L → F),c∈C → (distance (u+z • v) c:ℚ)≤ρ → c=cu+z • cv)
    (z : F) (hbad : Bad C ρ u v z) :
    ∃ i∈support (u-cu)∪support (v-cv),(u i-cu i)+z*(v i-cv i)=0 := by
  classical
  obtain ⟨T,hT,hfold,j,hj⟩ := hbad
  obtain ⟨cz,hcz,heq⟩ := (mem_projectedCodeSubmod_iff _ _ _).mp hfold
  have hag : ∀ i∈T,(u+z • v) i=cz i := by
    intro i hi
    simpa [projectedWord,AffineLineGenerator] using congrFun heq ⟨i,hi⟩
  have hc := halign z cz hcz (close_of_agreement ρ _ _ T hT hag)
  have hex : ∃ i∈T,i∈support (u-cu)∪support (v-cv) := by
    by_contra hn
    push Not at hn
    have hinputs : ∀ i∈T,u i=cu i ∧ v i=cv i := by
      intro i hi
      simpa [mem_support,sub_eq_zero] using hn i hi
    fin_cases j
    · apply hj
      rw [mem_projectedCodeSubmod_iff]
      refine ⟨cu,hcu,?_⟩
      funext i
      exact (hinputs i i.property).1
    · apply hj
      rw [mem_projectedCodeSubmod_iff]
      refine ⟨cv,hcv,?_⟩
      funext i
      exact (hinputs i i.property).2
  obtain ⟨i,hiT,hiS⟩ := hex
  refine ⟨i,hiS,?_⟩
  have hi := hag i hiT
  rw [hc] at hi
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] at hi
  linear_combination hi

open Classical in
/-- Each genuine mismatch coordinate cancels for at most one seed. -/
theorem card_bad_le_of_alignment [Nonempty L] (C : Submodule F (L → F)) (ρ : ℚ)
    (u v cu cv : L → F) (hcu : cu∈C) (hcv : cv∈C)
    (halign : ∀ (z : F) (c : L → F),c∈C → (distance (u+z • v) c:ℚ)≤ρ → c=cu+z • cv) :
    (Finset.univ.filter (Bad C ρ u v)).card≤pairDistance u v cu cv := by
  classical
  let S := support (u-cu)∪support (v-cv)
  let roots (i : L) : Finset F := Finset.univ.filter fun z => (u i-cu i)+z*(v i-cv i)=0
  have hr : ∀ i∈S,(roots i).card≤1 := by
    intro i hi
    apply Finset.card_le_one.mpr
    intro z hz w hw
    have hz' := (Finset.mem_filter.mp hz).2
    have hw' := (Finset.mem_filter.mp hw).2
    have hv : v i-cv i≠0 := by
      intro hv
      have hu : u i-cu i=0 := by simpa [hv] using hz'
      simp [S,mem_support,hu,hv] at hi
    apply mul_right_cancel₀ hv
    linear_combination hz'-hw'
  have hsub : Finset.univ.filter (Bad C ρ u v)⊆S.biUnion roots := by
    intro z hz
    obtain ⟨i,hi,hzero⟩ := cancellation_of_alignment C ρ u v cu cv hcu hcv halign z
      (Finset.mem_filter.mp hz).2
    exact Finset.mem_biUnion.mpr ⟨i,hi,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hzero⟩⟩
  calc
    _ ≤ (S.biUnion roots).card := Finset.card_le_card hsub
    _ ≤ ∑ i∈S,(roots i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i∈S,1 := Finset.sum_le_sum hr
    _ = _ := by simp [pairDistance,S]

variable [Fintype R] [DecidableEq R] {G : TannerGraph L R}

omit [Fintype F] in
/-- Two nearby folds align every nearby codeword; original distance gives injectivity
on the deleted coordinates. This lemma includes the closed-radius boundary. -/
theorem alignment_of_punctures (H : G.WeightedSystem F) (u v : L → F) (L₀ : Finset L)
    {ρ D d : ℚ} (hρ : ρ<D) (hd : HasDistance H.code d) (hp : (L₀.card:ℚ)<d)
    (hD : HasDistance (puncture (H.relaxedCode (H.badChecks u v)) (Finset.univ \ L₀)) D)
    {r₁ r₂ : F} (hne : r₁≠r₂)
    (h₁ : ∃ c∈H.code,(distance (u+r₁ • v) c:ℚ)≤ρ)
    (h₂ : ∃ c∈H.code,(distance (u+r₂ • v) c:ℚ)≤ρ) :
    ∃ cu∈H.code,∃ cv∈H.code,pairDistance u v cu cv≤L₀.card ∧
      ∀ (r : F) (c : L → F),c∈H.code → (distance (u+r • v) c:ℚ)≤ρ → c=cu+r • cv := by
  classical
  have huv := inputs_mem_relaxed_badChecks H u v
  have hag (r : F) (c : L → F) (hc : c∈H.code) (hclose : (distance (u+r • v) c:ℚ)≤ρ) :
      restrict (Finset.univ \ L₀) (u+r • v)=restrict (Finset.univ \ L₀) c :=
    agreement_of_close (code_le_relaxed H _) _ hD
      ((H.relaxedCode _).add_mem huv.1 ((H.relaxedCode _).smul_mem r huv.2)) hc
      (hclose.trans_lt hρ)
  obtain ⟨c₁,hc₁,he₁⟩ := h₁
  obtain ⟨c₂,hc₂,he₂⟩ := h₂
  obtain ⟨cu,hcu,cv,hcv,hagree⟩ := interpolate_agreement H.code (Finset.univ \ L₀)
    u v c₁ c₂ hne hc₁ hc₂ (hag _ _ hc₁ he₁) (hag _ _ hc₂ he₂)
  refine ⟨cu,hcu,cv,hcv,pairDistance_le_deleted L₀ _ _ _ _ hagree,?_⟩
  intro r c hc hclose
  have hrestriction := hag r c hc hclose
  apply hd.eq_of_distance_lt hc (H.code.add_mem hcu (H.code.smul_mem r hcv))
  have hsub : support (c-(cu+r • cv))⊆L₀ := by
    intro i hi
    by_contra hn
    have hiI : i∈Finset.univ \ L₀ := by simp [hn]
    have hiuv := hagree i hiI
    have hiw := congrFun hrestriction ⟨i,hiI⟩
    apply (mem_support _ _).mp hi
    change c i-(cu i+r*cv i)=0
    change u i+r*v i=c i at hiw
    rw [hiuv.1,hiuv.2] at hiw
    exact sub_eq_zero.mpr hiw.symm
  exact lt_of_le_of_lt (by exact_mod_cast Finset.card_le_card hsub) hp

end MCA
end SmoothLDPC
