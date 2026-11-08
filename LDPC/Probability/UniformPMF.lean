module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! Mathlib v4.33.1 uniform PMFs, vendored (renamed) because v4.35 moved them to `Measure`. -/

@[expose] public section

noncomputable section

open scoped Classical
open Finset NNReal ENNReal MeasureTheory

namespace PMF

variable {α : Type*}

open scoped NNReal ENNReal

section UniformOfFinset

/-- Uniform distribution taking the same non-zero probability on the nonempty finset `s` -/
def unifFinset (s : Finset α) (hs : s.Nonempty) : PMF α := by
  classical
  refine ofFinset (fun a => if a ∈ s then s.card⁻¹ else 0) s ?_ ?_
  · simp only [Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const, nsmul_eq_mul]
    have : (s.card : ℝ≥0∞) ≠ 0 := by
      simpa only [Ne, Nat.cast_eq_zero, Finset.card_eq_zero] using
        Finset.nonempty_iff_ne_empty.1 hs
    exact ENNReal.mul_inv_cancel this <| ENNReal.natCast_ne_top s.card
  · exact fun x hx => by simp only [hx, if_false]

variable {s : Finset α} (hs : s.Nonempty) {a : α}

open scoped Classical in
@[simp]
theorem unifFinset_apply (a : α) :
    unifFinset s hs a = if a ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0 :=
  rfl

theorem unifFinset_apply_of_mem (ha : a ∈ s) : unifFinset s hs a = (s.card : ℝ≥0∞)⁻¹ := by
  simp [ha]

theorem unifFinset_apply_of_notMem (ha : a ∉ s) : unifFinset s hs a = 0 := by simp [ha]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
theorem support_unifFinset : (unifFinset s hs).support = s :=
  Set.ext
    (by
      let ⟨a, ha⟩ := hs
      simp [mem_support_iff])

theorem mem_support_unifFinset_iff (a : α) : a ∈ (unifFinset s hs).support ↔ a ∈ s := by
  simp

section Measure

variable (t : Set α)

open scoped Classical in
@[simp]
theorem toOuterMeasure_unifFinset_apply :
    (unifFinset s hs).toOuterMeasure t = #{x ∈ s | x ∈ t} / #s :=
  calc
    (unifFinset s hs).toOuterMeasure t = ∑' x, if x ∈ t then unifFinset s hs x else 0 :=
      toOuterMeasure_apply (unifFinset s hs) t
    _ = ∑' x, if x ∈ s ∧ x ∈ t then (#s : ℝ≥0∞)⁻¹ else 0 :=
      tsum_congr fun x => by simp_rw [unifFinset_apply, ← ite_and, and_comm]
    _ = ∑ x ∈ s with x ∈ t, if x ∈ s ∧ x ∈ t then (#s : ℝ≥0∞)⁻¹ else 0 :=
      tsum_eq_sum fun _ hx => if_neg fun h => hx (Finset.mem_filter.2 h)
    _ = ∑ x ∈ s with x ∈ t, (#s : ℝ≥0∞)⁻¹ :=
      Finset.sum_congr rfl fun x hx => by
        have : x ∈ s ∧ x ∈ t := by simpa using hx
        simp only [this, and_self_iff, if_true]
    _ = #{x ∈ s | x ∈ t} / #s := by
        simp only [div_eq_mul_inv, Finset.sum_const, nsmul_eq_mul]

open scoped Classical in
@[simp]
theorem toMeasure_unifFinset_apply [MeasurableSpace α] (ht : MeasurableSet t) :
    (unifFinset s hs).toMeasure t = #{x ∈ s | x ∈ t} / #s :=
  (toMeasure_apply_eq_toOuterMeasure_apply _ ht).trans (toOuterMeasure_unifFinset_apply hs t)

end Measure

end UniformOfFinset

section UniformOfFintype

/-- The uniform pmf taking the same uniform value on all of the fintype `α` -/
def unifFintype (α : Type*) [Fintype α] [Nonempty α] : PMF α :=
  unifFinset Finset.univ Finset.univ_nonempty

variable [Fintype α] [Nonempty α]

@[simp]
theorem unifFintype_apply (a : α) : unifFintype α a = (Fintype.card α : ℝ≥0∞)⁻¹ := by
  simp [unifFintype, Finset.mem_univ, unifFinset_apply]

@[simp]
theorem support_unifFintype (α : Type*) [Fintype α] [Nonempty α] :
    (unifFintype α).support = ⊤ :=
  Set.ext fun x => by simp [mem_support_iff]

theorem mem_support_unifFintype (a : α) : a ∈ (unifFintype α).support := by simp

section Measure

variable (s : Set α)

theorem toOuterMeasure_unifFintype_apply [Fintype s] :
    (unifFintype α).toOuterMeasure s = Fintype.card s / Fintype.card α := by
  classical
  rw [unifFintype, toOuterMeasure_unifFinset_apply, Fintype.card_subtype,
    Finset.card_univ]

theorem toMeasure_unifFintype_apply [MeasurableSpace α] (hs : MeasurableSet s) [Fintype s] :
    (unifFintype α).toMeasure s = Fintype.card s / Fintype.card α := by
  classical
  simp [unifFintype, Fintype.card_subtype, hs]

end Measure

end UniformOfFintype

end PMF
