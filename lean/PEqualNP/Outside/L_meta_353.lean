import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_353_aux

abbrev PT : Fin 7 → Finset (Fin 12) := ![{1, 2, 4, 5, 8, 11}, {0}, {1}, {4}, {6}, {8}, {9}]
abbrev RT : Fin 7 → Finset (Fin 12) := ![{0, 3, 6, 7, 9, 10}, {3}, {2}, {5}, {7}, {11}, {10}]

theorem fin_ind {P : Fin 7 → Prop} (h : ∀ i, (∀ j, j < i → P j) → P i) : ∀ i, P i :=
  fun i => (wellFounded_lt (α := Fin 7)).induction (C := P) i h

/-- A gate whose table row respects `X → Y` on the base sets inherits `val X → val Y`
from the earlier gates it reads. -/
theorem pres {σ : Equiv.Perm (Fin 7)} {PG RG : Fin 7 → Finset (Fin 7)}
    {val : Finset (Fin 12) → Fin 7 → Prop}
    (hPG : ∀ i : Fin 7, ∀ j ∈ PG i, j < i) (hRG : ∀ i : Fin 7, ∀ j ∈ RG i, j < i)
    (hv : ∀ (X : Finset (Fin 12)) (i : Fin 7), val X i ↔
      ((∃ v ∈ PT (σ i), v ∈ X) ∨ ∃ j ∈ PG i, val X j) ∧
      ((∃ v ∈ RT (σ i), v ∈ X) ∨ ∃ j ∈ RG i, val X j))
    (X Y : Finset (Fin 12)) (i : Fin 7)
    (hb : ((∃ v ∈ PT (σ i), v ∈ X) → ∃ v ∈ PT (σ i), v ∈ Y) ∧
      ((∃ v ∈ RT (σ i), v ∈ X) → ∃ v ∈ RT (σ i), v ∈ Y))
    (ih : ∀ j, j < i → val X j → val Y j) : val X i → val Y i := by
  intro h
  rw [hv] at h ⊢
  obtain ⟨hp, hr⟩ := h
  refine ⟨?_, ?_⟩
  · rcases hp with hp | ⟨j, hj, hjv⟩
    · exact Or.inl (hb.1 hp)
    · exact Or.inr ⟨j, hj, ih j (hPG i j hj) hjv⟩
  · rcases hr with hr | ⟨j, hj, hjv⟩
    · exact Or.inl (hb.2 hr)
    · exact Or.inr ⟨j, hj, ih j (hRG i j hj) hjv⟩

theorem hbase : ∀ r : Fin 7, r ≠ 6 →
    (((∃ v ∈ PT r, v ∈ ({9, 11} : Finset (Fin 12))) → ∃ v ∈ PT r, v ∈ ({6, 11} : Finset (Fin 12))) ∧
      ((∃ v ∈ RT r, v ∈ ({9, 11} : Finset (Fin 12))) → ∃ v ∈ RT r, v ∈ ({6, 11} : Finset (Fin 12)))) ∧
    (((∃ v ∈ PT r, v ∈ ({10, 11} : Finset (Fin 12))) → ∃ v ∈ PT r, v ∈ ({6, 11} : Finset (Fin 12))) ∧
      ((∃ v ∈ RT r, v ∈ ({10, 11} : Finset (Fin 12))) → ∃ v ∈ RT r, v ∈ ({6, 11} : Finset (Fin 12)))) := by
  decide

theorem row6P : ¬ ∃ v ∈ PT 6, v ∈ ({10, 11} : Finset (Fin 12)) := by decide
theorem row6R : ¬ ∃ v ∈ RT 6, v ∈ ({9, 11} : Finset (Fin 12)) := by decide

end PEqualNP.Outside.L_meta_353_aux

open PEqualNP.Outside.L_meta_353_aux in
theorem PEqualNP.Outside.L_meta_353 : ∀ E : List (Fin 12 × Fin 12), E = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 6), (2, 9), (3, 4), (3, 5), (4, 5), (4, 7), (5, 10), (6, 7), (6, 8), (7, 8), (8, 11), (9, 10), (9, 11), (10, 11)] → ∀ (σ : Equiv.Perm (Fin 7)) (PG RG : Fin 7 → Finset (Fin 7)) (OV : Finset (Fin 12)) (OG : Finset (Fin 7)) (val : Finset (Fin 12) → Fin 7 → Prop), (∀ i : Fin 7, ∀ j ∈ PG i, j < i) → (∀ i : Fin 7, ∀ j ∈ RG i, j < i) → (∀ (X : Finset (Fin 12)) (i : Fin 7), val X i ↔ (((∃ v ∈ (![{1, 2, 4, 5, 8, 11}, {0}, {1}, {4}, {6}, {8}, {9}] : Fin 7 → Finset (Fin 12)) (σ i), v ∈ X) ∨ ∃ j ∈ PG i, val X j) ∧ ((∃ v ∈ (![{0, 3, 6, 7, 9, 10}, {3}, {2}, {5}, {7}, {11}, {10}] : Fin 7 → Finset (Fin 12)) (σ i), v ∈ X) ∨ ∃ j ∈ RG i, val X j))) → ¬ ∀ X : Finset (Fin 12), ((∃ v ∈ OV, v ∈ X) ∨ ∃ j ∈ OG, val X j) ↔ ∃ e ∈ E, e.1 ∈ X ∧ e.2 ∈ X := by
  intro E hE σ PG RG OV OG val hPG hRG hval hout
  have hv : ∀ (X : Finset (Fin 12)) (i : Fin 7), val X i ↔
      ((∃ v ∈ PT (σ i), v ∈ X) ∨ ∃ j ∈ PG i, val X j) ∧
      ((∃ v ∈ RT (σ i), v ∈ X) ∨ ∃ j ∈ RG i, val X j) := hval
  -- the edge function on the test inputs
  have hsing : ∀ v : Fin 12, ¬ ∃ e ∈ E, e.1 ∈ ({v} : Finset (Fin 12)) ∧ e.2 ∈ ({v} : Finset (Fin 12)) := by
    subst hE; decide
  have hX1 : ∃ e ∈ E, e.1 ∈ ({9, 11} : Finset (Fin 12)) ∧ e.2 ∈ ({9, 11} : Finset (Fin 12)) := by
    subst hE; decide
  have hX2 : ∃ e ∈ E, e.1 ∈ ({10, 11} : Finset (Fin 12)) ∧ e.2 ∈ ({10, 11} : Finset (Fin 12)) := by
    subst hE; decide
  have hY1 : ¬ ∃ e ∈ E, e.1 ∈ ({6, 11} : Finset (Fin 12)) ∧ e.2 ∈ ({6, 11} : Finset (Fin 12)) := by
    subst hE; decide
  have hOV : ∀ v ∈ OV, False := fun v hvO =>
    hsing v ((hout {v}).mp (Or.inl ⟨v, hvO, Finset.mem_singleton_self v⟩))
  obtain ⟨j1, hj1, hv1⟩ : ∃ j ∈ OG, val {9, 11} j := by
    rcases (hout _).mpr hX1 with ⟨v, hvO, _⟩ | h
    · exact (hOV v hvO).elim
    · exact h
  obtain ⟨j2, hj2, hv2⟩ : ∃ j ∈ OG, val {10, 11} j := by
    rcases (hout _).mpr hX2 with ⟨v, hvO, _⟩ | h
    · exact (hOV v hvO).elim
    · exact h
  have hY : ∀ j ∈ OG, ¬ val {6, 11} j := fun j hj h => hY1 ((hout _).mp (Or.inr ⟨j, hj, h⟩))
  -- the gate on table row 6
  obtain ⟨i6, hs6⟩ : ∃ i6, σ i6 = 6 := ⟨σ.symm 6, by simp⟩
  have hσ : ∀ i, i ≠ i6 → σ i ≠ 6 := fun i hi h => hi (σ.injective (h.trans hs6.symm))
  -- before it, every gate satisfies both implications
  have hlow : ∀ i, i < i6 → (val {9, 11} i → val {6, 11} i) ∧ (val {10, 11} i → val {6, 11} i) :=
    fin_ind fun i ih hi =>
      ⟨pres hPG hRG hv _ _ i (hbase (σ i) (hσ i (ne_of_lt hi))).1
          fun j hj => (ih j hj (lt_trans hj hi)).1,
        pres hPG hRG hv _ _ i (hbase (σ i) (hσ i (ne_of_lt hi))).2
          fun j hj => (ih j hj (lt_trans hj hi)).2⟩
  -- the row-6 gate keeps at least one of them
  have h6 : (val {9, 11} i6 → val {6, 11} i6) ∨ (val {10, 11} i6 → val {6, 11} i6) := by
    by_contra hn
    push_neg at hn
    obtain ⟨⟨h1, hn1⟩, ⟨h2, _⟩⟩ := hn
    apply hn1
    rw [hv] at h1 h2 ⊢
    obtain ⟨_, hr1⟩ := h1
    obtain ⟨hp2, _⟩ := h2
    rw [hs6] at hr1 hp2 ⊢
    refine ⟨?_, ?_⟩
    · rcases hp2 with hb | ⟨j, hj, hjv⟩
      · exact (row6P hb).elim
      · exact Or.inr ⟨j, hj, (hlow j (hPG i6 j hj)).2 hjv⟩
    · rcases hr1 with hb | ⟨j, hj, hjv⟩
      · exact (row6R hb).elim
      · exact Or.inr ⟨j, hj, (hlow j (hRG i6 j hj)).1 hjv⟩
  rcases h6 with h | h
  · have hall : ∀ i, val {9, 11} i → val {6, 11} i := fin_ind fun i ih => by
      by_cases hi : i = i6
      · rw [hi]; exact h
      · exact pres hPG hRG hv _ _ i (hbase (σ i) (hσ i hi)).1 ih
    exact hY j1 hj1 (hall j1 hv1)
  · have hall : ∀ i, val {10, 11} i → val {6, 11} i := fin_ind fun i ih => by
      by_cases hi : i = i6
      · rw [hi]; exact h
      · exact pres hPG hRG hv _ _ i (hbase (σ i) (hσ i hi)).2 ih
    exact hY j2 hj2 (hall j2 hv2)
