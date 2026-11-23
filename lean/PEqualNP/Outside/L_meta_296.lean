import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_296_aux

/-- Inner indices of different threads, or of different positions, never coincide. -/
theorem block_eq {m k u v u' v' p p' : ℕ} (hv : v < m) (hv' : v' < m)
    (hp1 : 1 ≤ p) (hp2 : p ≤ 2 * k) (hp1' : 1 ≤ p') (hp2' : p' ≤ 2 * k)
    (h : 2 * k * (u * m + v) + p = 2 * k * (u' * m + v') + p') :
    u = u' ∧ v = v' ∧ p = p' := by
  have hA : u * m + v = u' * m + v' := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have h1 : 2 * k * (u * m + v + 1) ≤ 2 * k * (u' * m + v') := Nat.mul_le_mul_left _ hlt
      rw [Nat.mul_add, Nat.mul_one] at h1
      omega
    · have h1 : 2 * k * (u' * m + v' + 1) ≤ 2 * k * (u * m + v) := Nat.mul_le_mul_left _ hlt
      rw [Nat.mul_add, Nat.mul_one] at h1
      omega
  rw [hA] at h
  have hpp : p = p' := by omega
  have huu : u = u' := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have h1 : (u + 1) * m ≤ u' * m := Nat.mul_le_mul_right _ hlt
      rw [Nat.add_mul, Nat.one_mul] at h1
      omega
    · have h1 : (u' + 1) * m ≤ u * m := Nat.mul_le_mul_right _ hlt
      rw [Nat.add_mul, Nat.one_mul] at h1
      omega
  subst huu
  exact ⟨rfl, by omega, hpp⟩

end PEqualNP.Outside.L_meta_296_aux

open PEqualNP.Outside.L_meta_296_aux in
theorem PEqualNP.Outside.L_meta_296 : ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop) (S : SimpleGraph (Fin (m + 2 * k * (m * m)))), 1 ≤ k → (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨ (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) → (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) → ∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), u < v → H.Adj u v → 1 ≤ p → p ≤ 2 * k → Q u v p x → (S.neighborSet x).ncard = 2 := by
  intro m k H Q S hk hQ hS u v p x huv hadj hp1 hp2 hx
  have hu := u.isLt
  have hv := v.isLt
  have huv' : u.val < v.val := huv
  have hxv : x.val + 1 = m + 2 * k * (u.val * m + v.val) + p := by
    have := (hQ u v p x).1 hx
    omega
  -- the vertex at a given position of the thread (u, v) is unique
  have uniq : ∀ (q : ℕ) (y y' : Fin (m + 2 * k * (m * m))), Q u v q y → Q u v q y' → y = y' := by
    intro q y y' hy hy'
    have h1 := (hQ u v q y).1 hy
    have h2 := (hQ u v q y').1 hy'
    apply Fin.ext
    omega
  -- x sits only at position p of the thread (u, v)
  have xpos : ∀ (u' v' : Fin m) (p' : ℕ), Q u' v' p' x → u' = u ∧ v' = v ∧ p' = p := by
    intro u' v' p' h'
    have hu' := u'.isLt
    have hv' := v'.isLt
    rcases (hQ u' v' p' x).1 h' with ⟨_, h3⟩ | ⟨_, h3⟩ | ⟨h1, h2, h3⟩
    · omega
    · omega
    · obtain ⟨e1, e2, e3⟩ := block_eq (m := m) (k := k) (u := u.val) (u' := u'.val)
        hv hv' hp1 hp2 h1 h2 (by omega)
      exact ⟨(Fin.ext e1).symm, (Fin.ext e2).symm, e3.symm⟩
  -- every position 0 .. 2k+1 of the thread is occupied
  have hN : ∀ q : ℕ, 1 ≤ q → q ≤ 2 * k →
      m + 2 * k * (u.val * m + v.val) + q - 1 < m + 2 * k * (m * m) := by
    intro q hq1 hq2
    have h1 : u.val * m + v.val + 1 ≤ m * m := by
      have h0 : (u.val + 1) * m ≤ m * m := Nat.mul_le_mul_right m hu
      rw [Nat.add_mul, Nat.one_mul] at h0
      omega
    have h2 : 2 * k * (u.val * m + v.val + 1) ≤ 2 * k * (m * m) := Nat.mul_le_mul_left _ h1
    rw [Nat.mul_add, Nat.mul_one] at h2
    omega
  have ex : ∀ q : ℕ, q ≤ 2 * k + 1 → ∃ y, Q u v q y := by
    intro q hq
    by_cases h0 : q = 0
    · exact ⟨⟨u.val, by omega⟩, (hQ u v q _).2 (Or.inl ⟨h0, rfl⟩)⟩
    by_cases h1 : q = 2 * k + 1
    · exact ⟨⟨v.val, by omega⟩, (hQ u v q _).2 (Or.inr (Or.inl ⟨h1, rfl⟩))⟩
    refine ⟨⟨m + 2 * k * (u.val * m + v.val) + q - 1, hN q (by omega) (by omega)⟩,
      (hQ u v q _).2 (Or.inr (Or.inr ⟨by omega, by omega, ?_⟩))⟩
    show m + 2 * k * (u.val * m + v.val) + q - 1 + 1 = m + 2 * k * (u.val * m + v.val) + q
    omega
  obtain ⟨a, ha⟩ := ex (p - 1) (by omega)
  obtain ⟨b, hb⟩ := ex (p + 1) (by omega)
  have hab : a ≠ b := by
    intro h
    subst h
    have h1 := (hQ u v (p - 1) a).1 ha
    have h2 := (hQ u v (p + 1) a).1 hb
    omega
  have hset : S.neighborSet x = {a, b} := by
    ext y
    simp only [SimpleGraph.mem_neighborSet, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hxy
      obtain ⟨u', v', -, -, p', -, h⟩ := (hS x y).1 hxy
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · obtain ⟨e1, e2, e3⟩ := xpos u' v' p' h1
        subst e1 e2 e3
        exact Or.inr (uniq _ _ _ h2 hb)
      · obtain ⟨e1, e2, e3⟩ := xpos u' v' (p' + 1) h2
        subst e1 e2
        have e4 : p' = p - 1 := by omega
        subst e4
        exact Or.inl (uniq _ _ _ h1 ha)
    · rintro (rfl | rfl)
      · refine (hS x _).2 ⟨u, v, huv, hadj, p - 1, by omega, Or.inr ⟨ha, ?_⟩⟩
        have e : p - 1 + 1 = p := by omega
        rw [e]
        exact hx
      · exact (hS x _).2 ⟨u, v, huv, hadj, p, hp2, Or.inl ⟨hx, hb⟩⟩
  rw [hset, Set.ncard_pair hab]
