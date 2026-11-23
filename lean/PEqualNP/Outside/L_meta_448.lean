import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_448 :
    ∀ (m k : ℕ) (H : SimpleGraph (Fin m))
      (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop),
      1 ≤ k →
      (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))),
        Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨
          (p = 2 * k + 1 ∧ x.val = v.val) ∨
          (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) →
      ∃ S : SimpleGraph (Fin (m + 2 * k * (m * m))),
        (∀ x y : Fin (m + 2 * k * (m * m)),
          S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧
            ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) := by
  intro m k H Q hk hQ
  let R (x y : Fin (m + 2 * k * (m * m))) : Prop :=
    ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧
      ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))
  have step_ne {u v : Fin m} {p : ℕ} {x : Fin (m + 2 * k * (m * m))}
      (hp : p ≤ 2 * k) (hx : Q u v p x) (hy : Q u v (p + 1) x) : False := by
    have hu := u.isLt
    have hv := v.isLt
    rcases (hQ u v p x).mp hx with h | h | h <;>
      rcases (hQ u v (p + 1) x).mp hy with h' | h' | h' <;> omega
  refine ⟨⟨R, ⟨?_⟩, ⟨?_⟩⟩, fun _ _ => Iff.rfl⟩
  · intro x y h
    obtain ⟨u, v, huv, ha, p, hp, hxy⟩ := h
    exact ⟨u, v, huv, ha, p, hp, hxy.elim Or.inr Or.inl⟩
  · intro x h
    obtain ⟨u, v, _, _, p, hp, hxy | hxy⟩ := h <;> exact step_ne hp hxy.1 hxy.2
