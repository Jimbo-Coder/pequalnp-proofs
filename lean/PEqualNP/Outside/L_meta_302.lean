import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_302_aux

theorem good_mem {m k : ℕ} {H : SimpleGraph (Fin m)}
    {Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop}
    (hQ : ∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔
      (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨
      (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p))
    {T : Finset (Fin m)} {T' : Finset (Fin (m + 2 * k * (m * m)))}
    (hT : ∀ u v : Fin m, H.Adj u v → u ∈ T ∨ v ∈ T)
    (hT' : ∀ x : Fin (m + 2 * k * (m * m)), x ∈ T' ↔ (∃ u ∈ T, x.val = u.val) ∨
      ∃ u v : Fin m, ∃ i : ℕ, i < 2 * k ∧ u < v ∧ H.Adj u v ∧
        x.val = m + 2 * k * (u.val * m + v.val) + i ∧ (i % 2 = 1 ↔ u ∈ T))
    {u v : Fin m} (huv : u < v) (hadj : H.Adj u v) {q : ℕ} {z : Fin (m + 2 * k * (m * m))}
    (hq : Q u v q z) (hgood : q % 2 = 0 ↔ u ∈ T) : z ∈ T' := by
  rw [hT']
  rcases (hQ u v q z).mp hq with ⟨rfl, hz⟩ | ⟨rfl, hz⟩ | ⟨h1, h2, hz⟩
  · exact Or.inl ⟨u, hgood.mp (by norm_num), hz⟩
  · have hu : u ∉ T := fun h => by have := hgood.mpr h; omega
    exact Or.inl ⟨v, (hT u v hadj).resolve_left hu, hz⟩
  · refine Or.inr ⟨u, v, q - 1, by omega, huv, hadj, by omega, ?_⟩
    rw [← hgood]
    constructor <;> intro h <;> omega

end PEqualNP.Outside.L_meta_302_aux

open PEqualNP.Outside.L_meta_302_aux in
theorem PEqualNP.Outside.L_meta_302 : ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop) (S : SimpleGraph (Fin (m + 2 * k * (m * m)))), 1 ≤ k → (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨ (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) → (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) → ∀ (T : Finset (Fin m)) (T' : Finset (Fin (m + 2 * k * (m * m)))), (∀ u v : Fin m, H.Adj u v → u ∈ T ∨ v ∈ T) → (∀ x : Fin (m + 2 * k * (m * m)), x ∈ T' ↔ (∃ u ∈ T, x.val = u.val) ∨ ∃ u v : Fin m, ∃ i : ℕ, i < 2 * k ∧ u < v ∧ H.Adj u v ∧ x.val = m + 2 * k * (u.val * m + v.val) + i ∧ (i % 2 = 1 ↔ u ∈ T)) → ∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y → x ∈ T' ∨ y ∈ T' := by
  intro m k H Q S _hk hQ hS T T' hT hT' x y hxy
  obtain ⟨u, v, huv, hadj, p, _hp, h⟩ := (hS x y).mp hxy
  by_cases hgp : (p % 2 = 0 ↔ u ∈ T)
  · rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact Or.inl (good_mem hQ hT hT' huv hadj h1 hgp)
    · exact Or.inr (good_mem hQ hT hT' huv hadj h1 hgp)
  · have hg1 : ((p + 1) % 2 = 0 ↔ u ∈ T) := by
      by_cases hu : u ∈ T
      · simp only [hu, iff_true] at hgp ⊢; omega
      · simp only [hu, iff_false] at hgp ⊢; omega
    rcases h with ⟨_, h2⟩ | ⟨_, h2⟩
    · exact Or.inr (good_mem hQ hT hT' huv hadj h2 hg1)
    · exact Or.inl (good_mem hQ hT hT' huv hadj h2 hg1)
