import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_452 :
    ∀ (k m : ℕ) (r : Fin k → (Fin m → ℚ)),
      (∀ i, r i ≠ 0) →
      (∃ j : Fin k, r j ∈ Submodule.span ℚ (r '' {l | l ≠ j})) →
      Nat.card {i : Fin k // r i ∉ Submodule.span ℚ (r '' {j | j ≠ i})} + 1 ≤
        Module.finrank ℚ (Submodule.span ℚ (Set.range r)) := by
  classical
  intro k m r h_nonzero ⟨j, h_redundant⟩
  let E : Set (Fin k) := {i | r i ∉ Submodule.span ℚ (r '' {q | q ≠ i})}
  have h_independent : LinearIndepOn ℚ r {j} := (linearIndepOn_singleton_iff ℚ).mpr (h_nonzero j)
  have h_univ : ({j} : Set (Fin k)) ⊆ Set.univ := Set.subset_univ _
  let T := h_independent.extend h_univ
  have h_span : Submodule.span ℚ (r '' T) = Submodule.span ℚ (Set.range r) := by
    simpa only [T, Set.image_univ] using h_independent.span_image_extend_eq_span_image h_univ
  have h_contained : E ⊆ T := by
    intro i hi
    by_contra h_not_mem
    have h_other : T ⊆ {q | q ≠ i} := by
      intro q hq h_eq
      subst q
      exact h_not_mem hq
    have h_in_span : r i ∈ Submodule.span ℚ (r '' T) := by
      rw [h_span]
      exact Submodule.subset_span (Set.mem_range_self i)
    exact hi (Submodule.span_mono (Set.image_mono h_other) h_in_span)
  have h_j_mem : j ∈ T := h_independent.subset_extend h_univ (by simp)
  have h_j_not_mem : j ∉ E := fun hj => hj h_redundant
  have h_proper : E ⊂ T := Set.ssubset_iff_subset_ne.mpr
    ⟨h_contained, fun h_eq => h_j_not_mem (h_eq.symm ▸ h_j_mem)⟩
  have h_card : E.ncard < T.ncard := Set.ncard_lt_ncard h_proper
  let : Fintype T := Fintype.ofFinite T
  let b : T → (Fin m → ℚ) := fun a => r a.val
  have h_b : LinearIndependent ℚ b := h_independent.linearIndepOn_extend h_univ
  have h_range : Set.range b = r '' T := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a.val, a.property, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  have h_rank := finrank_span_eq_card h_b
  rw [h_range, h_span, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at h_rank
  change E.ncard + 1 ≤ _
  rw [h_rank]
  exact Nat.succ_le_of_lt h_card
