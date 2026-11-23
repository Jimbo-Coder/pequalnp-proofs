import Mathlib
import PEqualNP.Defs

-- L-meta-931: each conjunct is settled by an exhaustive search on a sample of rows,
-- adapted from the search of L-meta-703. Each row pair is an edge of the graph against a
-- maximal independent set, so the sample pins down the monotone function exactly.


namespace PEqualNP.Outside.L_meta_931_aux

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

abbrev W := BitVec 128

def ops (x y : W) : List W := [x &&& y, x ||| y]

def sep (x : W) : BitVec 64 := ((x >>> 64) &&& ~~~x).setWidth 64

def cuts (ws : List W) : BitVec 64 := ws.foldr (fun w v => sep w ||| v) 0

def goal : W := (-1 : BitVec 64) ++ (0 : BitVec 64)

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))


theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 64) (w : W) : Prop :=
  w.getLsbD (64 + i.val) = true ∧ w.getLsbD i.val = false

theorem ops_differs (i : Fin 64) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  unfold differs at hd ⊢
  rcases hz with rfl | rfl <;> revert hd <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or] <;>
    cases a.getLsbD (64 + i.val) <;> cases a.getLsbD i.val <;>
    cases b.getLsbD (64 + i.val) <;> cases b.getLsbD i.val <;> simp

theorem goal_differs : ∀ i : Fin 64, differs i goal := by
  unfold differs
  decide

theorem cuts_spec (ws : List W) (i : Fin 64) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have hi : i.val < 128 := by omega
    simp [sep, i.isLt, differs, hi, Nat.add_comm]

theorem cuts_full {k : ℕ} {ws : List W} (h : live basicOps goal k ws.toFinset) :
    cuts ws = -1 := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (goal_differs ⟨j, hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 64)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp [basicOps, ops, BitVec.and_comm, BitVec.or_comm]

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def possible (w : List W) (z : W) : Bool :=
  z == 0 || z == BitVec.allOnes 128 || w.any (fun u => z == u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private def bit (k : Fin 128) (z : W) : Bool := z[k.val]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 128) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

private theorem read_wire (w : List W) (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

private theorem atom {ws : List W} {x : W} (hx : x = 0 ∨ x ∈ ws) : possible ws x := by
  rcases hx with rfl | hx
  · simp [possible]
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    exact .inr ⟨x, hx, .inl rfl⟩

private theorem pair {ws : List W} {x y : W} (hx : x = 0 ∨ x ∈ ws) (hy : y = 0 ∨ y ∈ ws) :
    possible ws (x &&& y) ∧ possible ws (x ||| y) := by
  rcases hx with rfl | hx
  · simpa [possible] using atom hy
  rcases hy with rfl | hy
  · simpa [possible] using atom (.inr hx)
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    constructor
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inl rfl⟩⟩
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inr rfl⟩⟩

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

set_option maxRecDepth 2000 in
private theorem gate_table (w ws : List W) (hw : w ⊆ ws) (g : Gate) (hg : legal g) :
    ∃ z, possible ws z ∧ ∀ k, step (w.map (bit k)) g = (w ++ [z]).map (bit k) := by
  have mem (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ ws :=
    (read_wire w i).imp_right (fun h => hw h)
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    rcases hop with rfl | rfl
    · exact ⟨BitVec.allOnes 128, by simp [possible], by simp [step, GateOp.eval, bit]; decide⟩
    · exact ⟨0, by simp [possible], by simp [step, GateOp.eval, bit]⟩
  | cons i tail =>
    cases tail with
    | nil =>
      rcases hop with rfl | rfl
      · exact ⟨_, atom (mem i),
          by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, atom (mem i),
          by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        rcases hop with rfl | rfl
        · exact ⟨_, (pair (mem i) (mem j)).1,
            by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
        · exact ⟨_, (pair (mem i) (mem j)).2,
            by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩

def represents (available : Finset W) (w : List W) : Prop :=
  ∀ u ∈ w, u = 0 ∨ u = BitVec.allOnes 128 ∨ u ∈ available

theorem classify {available : Finset W} {ws : List W} (hw : represents available ws)
    {z : W} (hz : possible ws z) :
    z = 0 ∨ z = BitVec.allOnes 128 ∨ z ∈ available ∨
      ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ z ∈ basicOps a b := by
  have lift {t : W} (h : t = 0 ∨ t = BitVec.allOnes 128 ∨ t ∈ available) :
      t = 0 ∨ t = BitVec.allOnes 128 ∨ t ∈ available ∨
        ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ t ∈ basicOps a b :=
    h.imp_right (Or.imp_right Or.inl)
  simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hz
  rcases hz with ((h | h) | ⟨x, hx, h | ⟨y, hy, h | h⟩⟩)
  · exact .inl h
  · exact .inr (.inl h)
  · subst z; exact lift (hw _ hx)
  · subst z
    rcases hw _ hx with rfl | rfl | hu
    · left; simp
    · rw [BitVec.allOnes_and]; exact lift (hw _ hy)
    rcases hw _ hy with rfl | rfl | hv
    · left; simp
    · rw [BitVec.and_allOnes]; exact .inr (.inr (.inl hu))
    by_cases h : x = y
    · subst h; rw [BitVec.and_self]; exact .inr (.inr (.inl hu))
    · exact .inr (.inr (.inr ⟨x, hu, y, hv, h, by simp [basicOps, ops]⟩))
  · subst z
    rcases hw _ hx with rfl | rfl | hu
    · rw [show (0 : W) ||| y = y by ext i hi; simp]; exact lift (hw _ hy)
    · right; left; exact BitVec.allOnes_or
    rcases hw _ hy with rfl | rfl | hv
    · rw [show x ||| (0 : W) = x by ext i hi; simp]; exact .inr (.inr (.inl hu))
    · right; left; exact BitVec.or_allOnes
    by_cases h : x = y
    · subst h; rw [BitVec.or_self]; exact .inr (.inr (.inl hu))
    · exact .inr (.inr (.inr ⟨x, hu, y, hv, h, by simp [basicOps, ops]⟩))

private theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : represents av w)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k goal) :
    build basicOps goal gs.length av := by
  induction gs generalizing w av with
  | nil =>
    have hval : w.getD out 0 = goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i, hi⟩
    have hr := read_wire w out
    rw [hval] at hr
    rcases hr with hz | hm
    · exact False.elim ((by decide : goal ≠ (0 : W)) hz)
    · rcases hw _ hm with h | h | h
      · exact False.elim ((by decide : goal ≠ (0 : W)) h)
      · exact False.elim ((by decide : goal ≠ BitVec.allOnes 128) h)
      · exact h
  | cons g gs ih =>
    obtain ⟨z, hz, hstep⟩ := gate_table w w (fun _ h => h) g (hg g (by simp))
    have fn := ih (fun g' h => hg g' (by simp [h])) (w ++ [z])
    have he' : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      intro k; simpa only [List.foldl_cons, hstep] using he k
    have appendOK (h : z = 0 ∨ z = BitVec.allOnes 128 ∨ z ∈ av) : represents av (w ++ [z]) := by
      intro u hu
      rcases List.mem_append.mp hu with old | fresh
      · exact hw _ old
      · have eq : u = z := List.mem_singleton.mp fresh
        exact eq ▸ h
    rcases classify hw hz with h | h | h | ⟨a, ha, b, hb, hab, hop⟩
    · exact Or.inl (fn av (appendOK (.inl h)) he')
    · exact Or.inl (fn av (appendOK (.inr (.inl h))) he')
    · exact Or.inl (fn av (appendOK (.inr (.inr h))) he')
    · refine Or.inr ⟨a, ha, b, hb, hab, z, hop, fn (insert z av) ?_ he'⟩
      intro u hu
      rcases List.mem_append.mp hu with hu | hu
      · exact (hw _ hu).imp_right (Or.imp_right (Finset.mem_insert_of_mem ·))
      · simp_all


def necessary (raw : List W) : Bool :=
  raw.all (fun a => (List.finRange 64).any (fun i => raw.all (fun b =>
    !(b.getLsbD (64 + i.val) && !b.getLsbD i.val) || b == a)))

theorem full_inputs {raw : List W} {s : Finset W} {k : ℕ} (hn : necessary raw = true)
    (hs : s ⊆ raw.toFinset) (hr : live basicOps goal k s) : s = raw.toFinset := by
  apply Finset.Subset.antisymm hs
  intro a ha
  obtain ⟨i, _, hAll⟩ := List.any_eq_true.mp (List.all_eq_true.mp hn a (List.mem_toFinset.mp ha))
  have hi (b : W) (hb : b ∈ raw) (hd : differs i b) : b = a := by
    have hrow := List.all_eq_true.mp hAll b hb
    obtain ⟨h1, h2⟩ := hd
    simpa [h1, h2] using hrow
  obtain ⟨b, hb, hd⟩ := live_separates (differs i) (goal_differs i) (ops_differs i) hr
  exact hi b (List.mem_toFinset.mp (hs hb)) hd ▸ hb

theorem input_rows (raw : List W) (k : Fin 128) :
    List.ofFn (fun i : Fin raw.length => bit k (raw.getD i.val 0)) = raw.map (bit k) := by
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp at h1
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]

theorem rows_eval (raw : List W) (f : (Fin raw.length → Bool) → Bool) (C : Circuit)
    (he : ∀ x : Fin raw.length → Bool, C.eval (List.ofFn x) = f x)
    (hrows : ∀ r : Fin 128, f (fun i => bit r (raw.getD i.val 0)) = bit r goal) (k : Fin 128) :
    (C.gates.foldl step (raw.map (bit k))).getD C.output false = bit k goal := by
  rw [← input_rows]
  exact (he _).trans (hrows k)

theorem initial_rep (raw : List W) : represents raw.toFinset raw := by
  intro u hu
  exact .inr (.inr (List.mem_toFinset.mpr hu))

theorem get_build (raw : List W) (f : (Fin raw.length → Bool) → Bool) (C : Circuit)
    (hg : Monotone2 C) (he : ∀ x : Fin raw.length → Bool, C.eval (List.ofFn x) = f x)
    (hrows : ∀ r : Fin 128, f (fun i => bit r (raw.getD i.val 0)) = bit r goal) :
    build basicOps goal C.gates.length raw.toFinset :=
  compile C.gates C.output hg raw raw.toFinset (initial_rep raw) (rows_eval raw f C he hrows)

theorem input_live (raw : List W) (hn : necessary raw = true) (k : ℕ)
    (hb : build basicOps goal k raw.toFinset) : live basicOps goal k raw.toFinset := by
  obtain ⟨S, hsub, hLive⟩ := compress hb
  exact full_inputs hn hsub hLive ▸ hLive

theorem extend_live {raw : List W} {m n : ℕ} (le : m ≤ n)
    (h : live basicOps goal m raw.toFinset) : live basicOps goal n raw.toFinset := by
  induction le with
  | refl => exact h
  | step _ ih => exact Or.inl ih


def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => ws == [goal]
  | k + 1, extra, ws => ws == [goal] ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps goal n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps goal k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk (by omega) (by omega) (cuts_full hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

theorem no_small (raw : List W) (f : (Fin raw.length → Bool) → Bool) (k extra : ℕ)
    (hnec : necessary raw = true) (hnd : raw.Nodup) (hroom : extra + raw.length = k + 1)
    (hsearch : optimized k extra raw = false)
    (hrows : ∀ r : Fin 128, f (fun i => bit r (raw.getD i.val 0)) = bit r goal)
    (C : Circuit) (hm : Monotone2 C) (hs : C.size ≤ k)
    (he : ∀ x : Fin raw.length → Bool, C.eval (List.ofFn x) = f x) : False := by
  have searched := optimized_complete k raw extra hnd hroom
    (extend_live hs (input_live raw hnec _ (get_build raw f C hm he hrows)))
  exact Bool.noConfusion (hsearch.symm.trans searched)

theorem no_small_few (raw : List W) (f : (Fin raw.length → Bool) → Bool) (k : ℕ)
    (hnec : necessary raw = true) (hnd : raw.Nodup) (hroom : k + 1 < raw.length)
    (hrows : ∀ r : Fin 128, f (fun i => bit r (raw.getD i.val 0)) = bit r goal)
    (C : Circuit) (hm : Monotone2 C) (hs : C.size ≤ k)
    (he : ∀ x : Fin raw.length → Bool, C.eval (List.ofFn x) = f x) : False := by
  have hl := extend_live hs (input_live raw hnec _ (get_build raw f C hm he hrows))
  have hc := live_card hl
  rw [List.toFinset_card_of_nodup hnd] at hc
  omega

theorem split_search (k extra : ℕ) (ws : List W) (L : List (W × W × List W))
    (h0 : (ws == [goal]) = false) (hL : pairs ws = L)
    (hall : ∀ t ∈ L, dispatch extra (optimized k) t.1 t.2.1 t.2.2 = false) :
    optimized (k + 1) extra ws = false := by
  subst hL
  simp only [optimized, h0, Bool.false_or]
  rw [List.any_eq_false]
  rintro ⟨a, b, r⟩ ht
  have h := hall _ ht
  simp only at h ⊢
  rw [h]
  simp


def raw0 : List W :=
  [0xfffffffffffffffffffffffffffffffd, 0xffffffffffffffff0000000000000002]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c0 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 2 → Bool, C.eval (List.ofFn x) = (fun x : Fin 2 → Bool => (x 0 && x 1)) x) → 1 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small_few raw0 _ 0 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) C hm (by omega) he

def raw1 : List W :=
  [0xfffffffffffffffffffffffffffffff5, 0xfffffffffffffff3000000000000000a, 0xc000000000000000a]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c1 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 3 → Bool, C.eval (List.ofFn x) = (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2)) x) → 2 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small_few raw1 _ 1 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) C hm (by omega) he

def raw2 : List W :=
  [0xfffffffffffffe3ffffffffffffffe49, 0xffffffffffffffc70000000000000092, 0x1f80000000000000124]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c2 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 3 → Bool, C.eval (List.ofFn x) = (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) x) → 4 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw2 _ 3 1 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw3 : List W :=
  [0xffffffffffffff0fffffffffffffff55, 0xffffffffffffff0f00000000000000aa, 0xf0ffffffffffffff33, 0xf000000000000000cc]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c3 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 4 → Bool, C.eval (List.ofFn x) = (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) x) → 3 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small_few raw3 _ 2 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) C hm (by omega) he

def raw4 : List W :=
  [0xffffffffffffffffffffffffffffffd5, 0xffffffffffffffc3000000000000002a, 0xc000000000000002a, 0x30000000000000002a]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c4 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 4 → Bool, C.eval (List.ofFn x) = (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) x) → 3 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small_few raw4 _ 2 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) C hm (by omega) he

def raw5 : List W :=
  [0xfffffffffffffe3f0000000000000092, 0xffffffffffffffc7fffffffffffffe49, 0x38ffffffffffffff6d, 0x1c000000000000001b6]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c5 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 4 → Bool, C.eval (List.ofFn x) = (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3)) x) → 4 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw5 _ 3 0 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw6 : List W :=
  [0xfffffffffffff1fffffffffffffff249, 0xfffffffffffffe070000000000000492, 0xe380000000000000924, 0x1c00000000000000db6]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c6 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 4 → Bool, C.eval (List.ofFn x) = (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2)) x) → 5 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw6 _ 4 1 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw7 : List W :=
  [0xfffffffffffff0fffffffffffffff555, 0xfffffffffffff00f0000000000000aaa, 0xf00000000000000aaa, 0xf00fffffffffffff333, 0xf000000000000000ccc]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c7 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4)) x) → 4 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small_few raw7 _ 3 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) C hm (by omega) he

def raw8 : List W :=
  [0xffffffffffffffffffffffffffffff55, 0xffffffffffffff0300000000000000aa, 0xc00000000000000aa, 0x3000000000000000aa, 0xc000000000000000aa]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c8 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4)) x) → 4 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small_few raw8 _ 3 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) C hm (by omega) he

def raw9 : List W :=
  [0xfffffffffffff1ff0000000000000492, 0xfffffffffffffe07fffffffffffff249, 0x38fffffffffffffb6d, 0x1c0fffffffffffffb6d, 0xe000000000000000db6]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c9 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) x) → 5 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw9 _ 4 0 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw10 : List W :=
  [0xffffffffff000fffffffffffff249249, 0xffffffffff03f03f0000000000492492, 0x3ffc00000000000924924, 0xfc0000ffffffffff1c71c7, 0xfc00000000000000e38e38]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c10 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4)) x) → 6 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw10 _ 5 1 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw11 : List W :=
  [0xffffffffffff00ff0000000000008888, 0xffffffffffff0f0fffffffffffff5555, 0xf0f0ffffffffffff3333, 0xf00000000000000aaaa, 0xf000000000000000cccc]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c11 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4)) x) → 5 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw11 _ 4 0 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw12 : List W :=
  [0xffffffffffff8fffffffffffffff9249, 0xfffffffffffff0070000000000002492, 0x70380000000000004924, 0x1c00000000000006db6, 0xe000000000000006db6]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c12 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2)) x) → 6 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw12 _ 5 1 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw13 : List W :=
  [0xffffffffffff81ff0000000000002492, 0xfffffffffffffe07ffffffffffff9249, 0xe380000000000004924, 0x1c0ffffffffffffdb6d, 0x70000000000000006db6]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c13 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4)) x) → 6 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw13 _ 5 1 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw14 : List W :=
  [0xfffffffffe007fff0000000000421084, 0xfffffffffe0f801ffffffffffe94a529, 0xf83e00000000001294a52, 0x1f07c00fffffffffe318c63, 0x1f000000000000001ce739c]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c14 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4)) x) → 7 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw14 _ 6 2 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw15 : List W :=
  [0xfffffffffe0003ff0000000000a5294a, 0xfffffffffe007c1fffffffffff18c631, 0xf83e0fffffffffe5294a5, 0x1f07c0000000000006318c6, 0x1ff800000000000018c6318]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c15 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4)) x) → 7 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw15 _ 6 2 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw16 : List W :=
  [0xffffffffc00fffffffffffffc2108421, 0xffffffffc1f0001f0000000014a5294a, 0x1f003e000000000294a5294, 0x3e007c00000000000c6318c6, 0x3e0f800000000000318c6318]

def b16_0 : W × W × List W :=
  (0xffffffffc00fffffffffffffc2108421, 0xffffffffc1f0001f0000000014a5294a, [0x1f003e000000000294a5294, 0x3e007c00000000000c6318c6, 0x3e0f800000000000318c6318])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s16_0 : dispatch 3 (optimized 6) b16_0.1 b16_0.2.1 b16_0.2.2 = false := by
  decide +kernel

def b16_1 : W × W × List W :=
  (0xffffffffc00fffffffffffffc2108421, 0x1f003e000000000294a5294, [0xffffffffc1f0001f0000000014a5294a, 0x3e007c00000000000c6318c6, 0x3e0f800000000000318c6318])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s16_1 : dispatch 3 (optimized 6) b16_1.1 b16_1.2.1 b16_1.2.2 = false := by
  decide +kernel

def b16_2 : W × W × List W :=
  (0xffffffffc00fffffffffffffc2108421, 0x3e007c00000000000c6318c6, [0xffffffffc1f0001f0000000014a5294a, 0x1f003e000000000294a5294, 0x3e0f800000000000318c6318])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s16_2 : dispatch 3 (optimized 6) b16_2.1 b16_2.2.1 b16_2.2.2 = false := by
  decide +kernel

def b16_3 : W × W × List W :=
  (0xffffffffc00fffffffffffffc2108421, 0x3e0f800000000000318c6318, [0xffffffffc1f0001f0000000014a5294a, 0x1f003e000000000294a5294, 0x3e007c00000000000c6318c6])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s16_3 : dispatch 3 (optimized 6) b16_3.1 b16_3.2.1 b16_3.2.2 = false := by
  decide +kernel

def b16_4 : W × W × List W :=
  (0xffffffffc1f0001f0000000014a5294a, 0x1f003e000000000294a5294, [0xffffffffc00fffffffffffffc2108421, 0x3e007c00000000000c6318c6, 0x3e0f800000000000318c6318])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s16_4 : dispatch 3 (optimized 6) b16_4.1 b16_4.2.1 b16_4.2.2 = false := by
  decide +kernel

def b16_5 : W × W × List W :=
  (0xffffffffc1f0001f0000000014a5294a, 0x3e007c00000000000c6318c6, [0xffffffffc00fffffffffffffc2108421, 0x1f003e000000000294a5294, 0x3e0f800000000000318c6318])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s16_5 : dispatch 3 (optimized 6) b16_5.1 b16_5.2.1 b16_5.2.2 = false := by
  decide +kernel

def b16_6 : W × W × List W :=
  (0xffffffffc1f0001f0000000014a5294a, 0x3e0f800000000000318c6318, [0xffffffffc00fffffffffffffc2108421, 0x1f003e000000000294a5294, 0x3e007c00000000000c6318c6])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s16_6 : dispatch 3 (optimized 6) b16_6.1 b16_6.2.1 b16_6.2.2 = false := by
  decide +kernel

def b16_7 : W × W × List W :=
  (0x1f003e000000000294a5294, 0x3e007c00000000000c6318c6, [0xffffffffc00fffffffffffffc2108421, 0xffffffffc1f0001f0000000014a5294a, 0x3e0f800000000000318c6318])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s16_7 : dispatch 3 (optimized 6) b16_7.1 b16_7.2.1 b16_7.2.2 = false := by
  decide +kernel

def b16_8 : W × W × List W :=
  (0x1f003e000000000294a5294, 0x3e0f800000000000318c6318, [0xffffffffc00fffffffffffffc2108421, 0xffffffffc1f0001f0000000014a5294a, 0x3e007c00000000000c6318c6])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s16_8 : dispatch 3 (optimized 6) b16_8.1 b16_8.2.1 b16_8.2.2 = false := by
  decide +kernel

def b16_9 : W × W × List W :=
  (0x3e007c00000000000c6318c6, 0x3e0f800000000000318c6318, [0xffffffffc00fffffffffffffc2108421, 0xffffffffc1f0001f0000000014a5294a, 0x1f003e000000000294a5294])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s16_9 : dispatch 3 (optimized 6) b16_9.1 b16_9.2.1 b16_9.2.2 = false := by
  decide +kernel

theorem search16 : optimized 7 3 raw16 = false :=
  split_search 6 3 raw16 [b16_0, b16_1, b16_2, b16_3, b16_4, b16_5, b16_6, b16_7, b16_8, b16_9]
    (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨s16_0, (List.forall_mem_cons.2 ⟨s16_1, (List.forall_mem_cons.2 ⟨s16_2, (List.forall_mem_cons.2 ⟨s16_3, (List.forall_mem_cons.2 ⟨s16_4, (List.forall_mem_cons.2 ⟨s16_5, (List.forall_mem_cons.2 ⟨s16_6, (List.forall_mem_cons.2 ⟨s16_7, (List.forall_mem_cons.2 ⟨s16_8, (List.forall_mem_cons.2 ⟨s16_9, (fun _ h => nomatch h)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c16 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4)) x) → 8 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw16 _ 7 3 (by decide +kernel) (by decide +kernel) (by decide)
    (search16) (by decide +kernel) C hm (by omega) he

def raw17 : List W :=
  [0xffffffffff0000ffffffffffff555555, 0xffffffffff0000ff0000000000aaaaaa, 0xff00ffffffffff333333, 0xff000000000000cccccc, 0xff0000ffffffffff0f0f0f, 0xff00000000000000f0f0f0]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c17 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5)) x) → 5 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small_few raw17 _ 4 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) C hm (by omega) he

def raw18 : List W :=
  [0xffffffffffff0fffffffffffffff5555, 0xffffffffffff000f000000000000aaaa, 0xf0000000000000aaaa, 0xf00000000000000aaaa, 0xf000ffffffffffff3333, 0xf000000000000000cccc]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c18 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) x) → 5 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small_few raw18 _ 4 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) C hm (by omega) he

def raw19 : List W :=
  [0xffffffffff000fff0000000000492492, 0xffffffffff03f03fffffffffff249249, 0xfc0ffffffffffb6db6d, 0x3f0000000000000db6db6, 0xfc0000ffffffffff1c71c7, 0xfc00000000000000e38e38]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c19 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) x) → 6 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw19 _ 5 0 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw20 : List W :=
  [0xffffffffffff00ffffffffffffff5555, 0xffffffffffff000f000000000000aaaa, 0xf0000000000000aaaa, 0xff00ffffffffffff3333, 0xf00000000000000cccc, 0xf000000000000000cccc]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c20 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5)) x) → 5 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small_few raw20 _ 4 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) C hm (by omega) he

def raw21 : List W :=
  [0xfffffffffffffffffffffffffffffd55, 0xfffffffffffffc0300000000000002aa, 0xc00000000000002aa, 0x3000000000000002aa, 0xc000000000000002aa, 0x30000000000000002aa]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c21 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5)) x) → 5 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small_few raw21 _ 4 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) C hm (by omega) he

def raw22 : List W :=
  [0xffffffffffff8fff0000000000002492, 0xfffffffffffff007ffffffffffff9249, 0x38ffffffffffffdb6d, 0x1c0ffffffffffffdb6d, 0xe00ffffffffffffdb6d, 0x70000000000000006db6]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c22 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5)) x) → 6 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw22 _ 5 0 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw23 : List W :=
  [0xffffffffc003ffffffffffffc9249249, 0xffffffffc0fc003f0000000012492492, 0xfc0fc00000000024924924, 0x3f0000000000036db6db6, 0x3f000000ffffffffc71c71c7, 0x3f0000000000000038e38e38]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c23 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5)) x) → 7 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw23 _ 6 1 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw24 : List W :=
  [0xffffffffffff81ff0000000000002492, 0xfffffffffffffe07ffffffffffff9249, 0x38ffffffffffffdb6d, 0x1c0ffffffffffffdb6d, 0xe000000000000006db6, 0x70000000000000006db6]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c24 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)) x) → 6 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw24 _ 5 0 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw25 : List W :=
  [0xfffffffffe007fff0000000000842108, 0xfffffffffe0f801ffffffffffe5294a5, 0x1f003e0fffffffffe318c63, 0x7c00ffffffffff7bdef7, 0xf80000000000001ad6b5a, 0x1f000000000000001ce739c]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c25 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)) x) → 7 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw25 _ 6 1 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw26 : List W :=
  [0xfffffffffff00ffffffffffffff55555, 0xfffffffffff0f00f0000000000088888, 0xf000000000000aaaaa, 0xf0000000000000aaaaa, 0xff000fffffffffff33333, 0xf000000000000000ccccc]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c26 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) x) → 6 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw26 _ 5 0 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw27 : List W :=
  [0xffffffffc0000fffffffffffc9249249, 0xffffffffc003f03f0000000012492492, 0x3ffc00000000024924924, 0x3ffc0000ffffffffc71c71c7, 0xfc00000000000038e38e38, 0x3f0000000000000038e38e38]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c27 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) x) → 7 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw27 _ 6 1 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw28 : List W :=
  [0xfffffffffe0003ff0000000000a5294a, 0xfffffffffe007c1f00000000014a5294, 0xf83e0fffffffffe5294a5, 0x1f07c00fffffffffe318c63, 0xf80000000000001ad6b5a, 0x1f000000000000001ce739c]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c28 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5)) x) → 7 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw28 _ 6 1 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw29 : List W :=
  [0xfffffffffffc7ffffffffffffffc9249, 0xffffffffffff80070000000000012492, 0x380380000000000024924, 0x1c00000000000036db6, 0xe000000000000036db6, 0x70000000000000036db6]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c29 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2)) x) → 7 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw29 _ 6 1 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw30 : List W :=
  [0xfffffffffffc0fff0000000000012492, 0xfffffffffffff007fffffffffffc9249, 0x70380000000000024924, 0x1c0fffffffffffedb6d, 0xe00fffffffffffedb6d, 0x380000000000000036db6]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c30 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5)) x) → 7 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw30 _ 6 1 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw31 : List W :=
  [0xffffffffc00fffff0000000008421084, 0xffffffffc1f0001fffffffffd294a529, 0x1f003e00000000025294a52, 0x3e007c00ffffffffc6318c63, 0xf8000fffffffff7bdef7b, 0x3e0000000000000039ce739c]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c31 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5)) x) → 8 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw31 _ 7 2 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw32 : List W :=
  [0xffffffffff000fff0000000000444444, 0xffffffffff0ff00f0000000000222222, 0xf0f0f0ffffffffff111111, 0xf00ffffffffffbbbbbb, 0xf0000ffffffffffdddddd, 0xf000000000000000eeeeee]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c32 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5)) x) → 8 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw32 _ 7 2 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw33 : List W :=
  [0xffffffffc0007fff0000000010842108, 0xffffffffc1ff801fffffffffca5294a5, 0xf83e00000000025294a52, 0x3e007c00ffffffffc6318c63, 0x1f000000000000035ad6b5a, 0x3e0000000000000039ce739c]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c33 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5)) x) → 8 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw33 _ 7 2 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw34 : List W :=
  [0xffffffffc0007fff0000000008421084, 0xffffffffc00f801fffffffffd294a529, 0xf83e00000000025294a52, 0x3ff07c00ffffffffc6318c63, 0x1f000000000000039ce739c, 0x3e0000000000000039ce739c]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c34 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) x) → 8 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw34 _ 7 2 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw35 : List W :=
  [0xfffffff00003fffffffffff249249249, 0xfffffff000fc003f0000000492492492, 0xfc0fc00000000924924924, 0x3f03f0000000000c30c30c30, 0xfff000000fffffff1c71c71c7, 0xfc00000000000000e38e38e38]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c35 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5)) x) → 8 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw35 _ 7 2 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw36 : List W :=
  [0xffffffffc0007fff0000000014a5294a, 0xffffffffc00f801fffffffffe318c631, 0x1f003e0ffffffffca5294a5, 0x7c00ffffffffeb5ad6b5, 0x3e0f8000000000000c6318c6, 0x3ff0000000000000318c6318]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c36 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5)) x) → 8 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw36 _ 7 2 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw37 : List W :=
  [0xffc000000003ffffffc9249249249249, 0xffc0000007fc01ff0012492492492492, 0x7fffe000024924924924924, 0x1ffff8000000ffc0e070381c0e07, 0x3fe00ff800000000070381c0e07038, 0x3ffff00000000000381c0e070381c0]

def b37_0 : W × W × List W :=
  (0xffc000000003ffffffc9249249249249, 0xffc0000007fc01ff0012492492492492, [0x7fffe000024924924924924, 0x1ffff8000000ffc0e070381c0e07, 0x3fe00ff800000000070381c0e07038, 0x3ffff00000000000381c0e070381c0])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s37_0 : dispatch 3 (optimized 7) b37_0.1 b37_0.2.1 b37_0.2.2 = false := by
  decide +kernel

def b37_1 : W × W × List W :=
  (0xffc000000003ffffffc9249249249249, 0x7fffe000024924924924924, [0xffc0000007fc01ff0012492492492492, 0x1ffff8000000ffc0e070381c0e07, 0x3fe00ff800000000070381c0e07038, 0x3ffff00000000000381c0e070381c0])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s37_1 : dispatch 3 (optimized 7) b37_1.1 b37_1.2.1 b37_1.2.2 = false := by
  decide +kernel

def b37_2 : W × W × List W :=
  (0xffc000000003ffffffc9249249249249, 0x1ffff8000000ffc0e070381c0e07, [0xffc0000007fc01ff0012492492492492, 0x7fffe000024924924924924, 0x3fe00ff800000000070381c0e07038, 0x3ffff00000000000381c0e070381c0])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s37_2 : dispatch 3 (optimized 7) b37_2.1 b37_2.2.1 b37_2.2.2 = false := by
  decide +kernel

def b37_3 : W × W × List W :=
  (0xffc000000003ffffffc9249249249249, 0x3fe00ff800000000070381c0e07038, [0xffc0000007fc01ff0012492492492492, 0x7fffe000024924924924924, 0x1ffff8000000ffc0e070381c0e07, 0x3ffff00000000000381c0e070381c0])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s37_3 : dispatch 3 (optimized 7) b37_3.1 b37_3.2.1 b37_3.2.2 = false := by
  decide +kernel

def b37_4 : W × W × List W :=
  (0xffc000000003ffffffc9249249249249, 0x3ffff00000000000381c0e070381c0, [0xffc0000007fc01ff0012492492492492, 0x7fffe000024924924924924, 0x1ffff8000000ffc0e070381c0e07, 0x3fe00ff800000000070381c0e07038])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s37_4 : dispatch 3 (optimized 7) b37_4.1 b37_4.2.1 b37_4.2.2 = false := by
  decide +kernel

def b37_5 : W × W × List W :=
  (0xffc0000007fc01ff0012492492492492, 0x7fffe000024924924924924, [0xffc000000003ffffffc9249249249249, 0x1ffff8000000ffc0e070381c0e07, 0x3fe00ff800000000070381c0e07038, 0x3ffff00000000000381c0e070381c0])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s37_5 : dispatch 3 (optimized 7) b37_5.1 b37_5.2.1 b37_5.2.2 = false := by
  decide +kernel

def b37_6 : W × W × List W :=
  (0xffc0000007fc01ff0012492492492492, 0x1ffff8000000ffc0e070381c0e07, [0xffc000000003ffffffc9249249249249, 0x7fffe000024924924924924, 0x3fe00ff800000000070381c0e07038, 0x3ffff00000000000381c0e070381c0])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s37_6 : dispatch 3 (optimized 7) b37_6.1 b37_6.2.1 b37_6.2.2 = false := by
  decide +kernel

def b37_7 : W × W × List W :=
  (0xffc0000007fc01ff0012492492492492, 0x3fe00ff800000000070381c0e07038, [0xffc000000003ffffffc9249249249249, 0x7fffe000024924924924924, 0x1ffff8000000ffc0e070381c0e07, 0x3ffff00000000000381c0e070381c0])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s37_7 : dispatch 3 (optimized 7) b37_7.1 b37_7.2.1 b37_7.2.2 = false := by
  decide +kernel

def b37_8 : W × W × List W :=
  (0xffc0000007fc01ff0012492492492492, 0x3ffff00000000000381c0e070381c0, [0xffc000000003ffffffc9249249249249, 0x7fffe000024924924924924, 0x1ffff8000000ffc0e070381c0e07, 0x3fe00ff800000000070381c0e07038])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s37_8 : dispatch 3 (optimized 7) b37_8.1 b37_8.2.1 b37_8.2.2 = false := by
  decide +kernel

def b37_9 : W × W × List W :=
  (0x7fffe000024924924924924, 0x1ffff8000000ffc0e070381c0e07, [0xffc000000003ffffffc9249249249249, 0xffc0000007fc01ff0012492492492492, 0x3fe00ff800000000070381c0e07038, 0x3ffff00000000000381c0e070381c0])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s37_9 : dispatch 3 (optimized 7) b37_9.1 b37_9.2.1 b37_9.2.2 = false := by
  decide +kernel

def b37_10 : W × W × List W :=
  (0x7fffe000024924924924924, 0x3fe00ff800000000070381c0e07038, [0xffc000000003ffffffc9249249249249, 0xffc0000007fc01ff0012492492492492, 0x1ffff8000000ffc0e070381c0e07, 0x3ffff00000000000381c0e070381c0])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s37_10 : dispatch 3 (optimized 7) b37_10.1 b37_10.2.1 b37_10.2.2 = false := by
  decide +kernel

def b37_11 : W × W × List W :=
  (0x7fffe000024924924924924, 0x3ffff00000000000381c0e070381c0, [0xffc000000003ffffffc9249249249249, 0xffc0000007fc01ff0012492492492492, 0x1ffff8000000ffc0e070381c0e07, 0x3fe00ff800000000070381c0e07038])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s37_11 : dispatch 3 (optimized 7) b37_11.1 b37_11.2.1 b37_11.2.2 = false := by
  decide +kernel

def b37_12 : W × W × List W :=
  (0x1ffff8000000ffc0e070381c0e07, 0x3fe00ff800000000070381c0e07038, [0xffc000000003ffffffc9249249249249, 0xffc0000007fc01ff0012492492492492, 0x7fffe000024924924924924, 0x3ffff00000000000381c0e070381c0])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s37_12 : dispatch 3 (optimized 7) b37_12.1 b37_12.2.1 b37_12.2.2 = false := by
  decide +kernel

def b37_13 : W × W × List W :=
  (0x1ffff8000000ffc0e070381c0e07, 0x3ffff00000000000381c0e070381c0, [0xffc000000003ffffffc9249249249249, 0xffc0000007fc01ff0012492492492492, 0x7fffe000024924924924924, 0x3fe00ff800000000070381c0e07038])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s37_13 : dispatch 3 (optimized 7) b37_13.1 b37_13.2.1 b37_13.2.2 = false := by
  decide +kernel

def b37_14 : W × W × List W :=
  (0x3fe00ff800000000070381c0e07038, 0x3ffff00000000000381c0e070381c0, [0xffc000000003ffffffc9249249249249, 0xffc0000007fc01ff0012492492492492, 0x7fffe000024924924924924, 0x1ffff8000000ffc0e070381c0e07])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s37_14 : dispatch 3 (optimized 7) b37_14.1 b37_14.2.1 b37_14.2.2 = false := by
  decide +kernel

theorem search37 : optimized 8 3 raw37 = false :=
  split_search 7 3 raw37 [b37_0, b37_1, b37_2, b37_3, b37_4, b37_5, b37_6, b37_7, b37_8, b37_9, b37_10, b37_11, b37_12, b37_13, b37_14]
    (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨s37_0, (List.forall_mem_cons.2 ⟨s37_1, (List.forall_mem_cons.2 ⟨s37_2, (List.forall_mem_cons.2 ⟨s37_3, (List.forall_mem_cons.2 ⟨s37_4, (List.forall_mem_cons.2 ⟨s37_5, (List.forall_mem_cons.2 ⟨s37_6, (List.forall_mem_cons.2 ⟨s37_7, (List.forall_mem_cons.2 ⟨s37_8, (List.forall_mem_cons.2 ⟨s37_9, (List.forall_mem_cons.2 ⟨s37_10, (List.forall_mem_cons.2 ⟨s37_11, (List.forall_mem_cons.2 ⟨s37_12, (List.forall_mem_cons.2 ⟨s37_13, (List.forall_mem_cons.2 ⟨s37_14, (fun _ h => nomatch h)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c37 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) x) → 9 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw37 _ 8 3 (by decide +kernel) (by decide +kernel) (by decide)
    (search37) (by decide +kernel) C hm (by omega) he

def raw38 : List W :=
  [0xffffffffc00003ff0000000018c6318c, 0xffffffffc0007c1f0000000025294a52, 0xf83e0ffffffffe318c631, 0x1f07c00ffffffffca5294a5, 0x3e0f8000000000000c6318c6, 0x3ff0000000000000318c6318]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c38 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5)) x) → 8 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw38 _ 7 2 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw39 : List W :=
  [0xfffffff801fffffffffffff842108421, 0xfffffff83e00001f0000000294a5294a, 0x3e0003e000000005294a5294, 0x7c0007c00000000018c6318c6, 0x7c00f800000000006318c6318, 0x1f0000000000007bdef7bde]

def b39_0 : W × W × List W :=
  (0xfffffff801fffffffffffff842108421, 0xfffffff83e00001f0000000294a5294a, [0x3e0003e000000005294a5294, 0x7c0007c00000000018c6318c6, 0x7c00f800000000006318c6318, 0x1f0000000000007bdef7bde])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s39_0 : dispatch 3 (optimized 7) b39_0.1 b39_0.2.1 b39_0.2.2 = false := by
  decide +kernel

def b39_1 : W × W × List W :=
  (0xfffffff801fffffffffffff842108421, 0x3e0003e000000005294a5294, [0xfffffff83e00001f0000000294a5294a, 0x7c0007c00000000018c6318c6, 0x7c00f800000000006318c6318, 0x1f0000000000007bdef7bde])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s39_1 : dispatch 3 (optimized 7) b39_1.1 b39_1.2.1 b39_1.2.2 = false := by
  decide +kernel

def b39_2 : W × W × List W :=
  (0xfffffff801fffffffffffff842108421, 0x7c0007c00000000018c6318c6, [0xfffffff83e00001f0000000294a5294a, 0x3e0003e000000005294a5294, 0x7c00f800000000006318c6318, 0x1f0000000000007bdef7bde])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s39_2 : dispatch 3 (optimized 7) b39_2.1 b39_2.2.1 b39_2.2.2 = false := by
  decide +kernel

def b39_3 : W × W × List W :=
  (0xfffffff801fffffffffffff842108421, 0x7c00f800000000006318c6318, [0xfffffff83e00001f0000000294a5294a, 0x3e0003e000000005294a5294, 0x7c0007c00000000018c6318c6, 0x1f0000000000007bdef7bde])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s39_3 : dispatch 3 (optimized 7) b39_3.1 b39_3.2.1 b39_3.2.2 = false := by
  decide +kernel

def b39_4 : W × W × List W :=
  (0xfffffff801fffffffffffff842108421, 0x1f0000000000007bdef7bde, [0xfffffff83e00001f0000000294a5294a, 0x3e0003e000000005294a5294, 0x7c0007c00000000018c6318c6, 0x7c00f800000000006318c6318])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s39_4 : dispatch 3 (optimized 7) b39_4.1 b39_4.2.1 b39_4.2.2 = false := by
  decide +kernel

def b39_5 : W × W × List W :=
  (0xfffffff83e00001f0000000294a5294a, 0x3e0003e000000005294a5294, [0xfffffff801fffffffffffff842108421, 0x7c0007c00000000018c6318c6, 0x7c00f800000000006318c6318, 0x1f0000000000007bdef7bde])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s39_5 : dispatch 3 (optimized 7) b39_5.1 b39_5.2.1 b39_5.2.2 = false := by
  decide +kernel

def b39_6 : W × W × List W :=
  (0xfffffff83e00001f0000000294a5294a, 0x7c0007c00000000018c6318c6, [0xfffffff801fffffffffffff842108421, 0x3e0003e000000005294a5294, 0x7c00f800000000006318c6318, 0x1f0000000000007bdef7bde])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s39_6 : dispatch 3 (optimized 7) b39_6.1 b39_6.2.1 b39_6.2.2 = false := by
  decide +kernel

def b39_7 : W × W × List W :=
  (0xfffffff83e00001f0000000294a5294a, 0x7c00f800000000006318c6318, [0xfffffff801fffffffffffff842108421, 0x3e0003e000000005294a5294, 0x7c0007c00000000018c6318c6, 0x1f0000000000007bdef7bde])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s39_7 : dispatch 3 (optimized 7) b39_7.1 b39_7.2.1 b39_7.2.2 = false := by
  decide +kernel

def b39_8 : W × W × List W :=
  (0xfffffff83e00001f0000000294a5294a, 0x1f0000000000007bdef7bde, [0xfffffff801fffffffffffff842108421, 0x3e0003e000000005294a5294, 0x7c0007c00000000018c6318c6, 0x7c00f800000000006318c6318])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s39_8 : dispatch 3 (optimized 7) b39_8.1 b39_8.2.1 b39_8.2.2 = false := by
  decide +kernel

def b39_9 : W × W × List W :=
  (0x3e0003e000000005294a5294, 0x7c0007c00000000018c6318c6, [0xfffffff801fffffffffffff842108421, 0xfffffff83e00001f0000000294a5294a, 0x7c00f800000000006318c6318, 0x1f0000000000007bdef7bde])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s39_9 : dispatch 3 (optimized 7) b39_9.1 b39_9.2.1 b39_9.2.2 = false := by
  decide +kernel

def b39_10 : W × W × List W :=
  (0x3e0003e000000005294a5294, 0x7c00f800000000006318c6318, [0xfffffff801fffffffffffff842108421, 0xfffffff83e00001f0000000294a5294a, 0x7c0007c00000000018c6318c6, 0x1f0000000000007bdef7bde])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s39_10 : dispatch 3 (optimized 7) b39_10.1 b39_10.2.1 b39_10.2.2 = false := by
  decide +kernel

def b39_11 : W × W × List W :=
  (0x3e0003e000000005294a5294, 0x1f0000000000007bdef7bde, [0xfffffff801fffffffffffff842108421, 0xfffffff83e00001f0000000294a5294a, 0x7c0007c00000000018c6318c6, 0x7c00f800000000006318c6318])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s39_11 : dispatch 3 (optimized 7) b39_11.1 b39_11.2.1 b39_11.2.2 = false := by
  decide +kernel

def b39_12 : W × W × List W :=
  (0x7c0007c00000000018c6318c6, 0x7c00f800000000006318c6318, [0xfffffff801fffffffffffff842108421, 0xfffffff83e00001f0000000294a5294a, 0x3e0003e000000005294a5294, 0x1f0000000000007bdef7bde])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s39_12 : dispatch 3 (optimized 7) b39_12.1 b39_12.2.1 b39_12.2.2 = false := by
  decide +kernel

def b39_13 : W × W × List W :=
  (0x7c0007c00000000018c6318c6, 0x1f0000000000007bdef7bde, [0xfffffff801fffffffffffff842108421, 0xfffffff83e00001f0000000294a5294a, 0x3e0003e000000005294a5294, 0x7c00f800000000006318c6318])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s39_13 : dispatch 3 (optimized 7) b39_13.1 b39_13.2.1 b39_13.2.2 = false := by
  decide +kernel

def b39_14 : W × W × List W :=
  (0x7c00f800000000006318c6318, 0x1f0000000000007bdef7bde, [0xfffffff801fffffffffffff842108421, 0xfffffff83e00001f0000000294a5294a, 0x3e0003e000000005294a5294, 0x7c0007c00000000018c6318c6])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s39_14 : dispatch 3 (optimized 7) b39_14.1 b39_14.2.1 b39_14.2.2 = false := by
  decide +kernel

theorem search39 : optimized 8 3 raw39 = false :=
  split_search 7 3 raw39 [b39_0, b39_1, b39_2, b39_3, b39_4, b39_5, b39_6, b39_7, b39_8, b39_9, b39_10, b39_11, b39_12, b39_13, b39_14]
    (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨s39_0, (List.forall_mem_cons.2 ⟨s39_1, (List.forall_mem_cons.2 ⟨s39_2, (List.forall_mem_cons.2 ⟨s39_3, (List.forall_mem_cons.2 ⟨s39_4, (List.forall_mem_cons.2 ⟨s39_5, (List.forall_mem_cons.2 ⟨s39_6, (List.forall_mem_cons.2 ⟨s39_7, (List.forall_mem_cons.2 ⟨s39_8, (List.forall_mem_cons.2 ⟨s39_9, (List.forall_mem_cons.2 ⟨s39_10, (List.forall_mem_cons.2 ⟨s39_11, (List.forall_mem_cons.2 ⟨s39_12, (List.forall_mem_cons.2 ⟨s39_13, (List.forall_mem_cons.2 ⟨s39_14, (fun _ h => nomatch h)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c39 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4)) x) → 9 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw39 _ 8 3 (by decide +kernel) (by decide +kernel) (by decide)
    (search39) (by decide +kernel) C hm (by omega) he

def raw40 : List W :=
  [0xfffffff8000fffff0000000108421084, 0xfffffff83ff0001ffffffff8c6318c63, 0x1f003e000000006318c6318, 0x7c0007c00fffffffa5294a529, 0x7c00f800000000004a5294a52, 0x3e0000000000000739ce739c]

def b40_0 : W × W × List W :=
  (0xfffffff8000fffff0000000108421084, 0xfffffff83ff0001ffffffff8c6318c63, [0x1f003e000000006318c6318, 0x7c0007c00fffffffa5294a529, 0x7c00f800000000004a5294a52, 0x3e0000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s40_0 : dispatch 3 (optimized 7) b40_0.1 b40_0.2.1 b40_0.2.2 = false := by
  decide +kernel

def b40_1 : W × W × List W :=
  (0xfffffff8000fffff0000000108421084, 0x1f003e000000006318c6318, [0xfffffff83ff0001ffffffff8c6318c63, 0x7c0007c00fffffffa5294a529, 0x7c00f800000000004a5294a52, 0x3e0000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s40_1 : dispatch 3 (optimized 7) b40_1.1 b40_1.2.1 b40_1.2.2 = false := by
  decide +kernel

def b40_2 : W × W × List W :=
  (0xfffffff8000fffff0000000108421084, 0x7c0007c00fffffffa5294a529, [0xfffffff83ff0001ffffffff8c6318c63, 0x1f003e000000006318c6318, 0x7c00f800000000004a5294a52, 0x3e0000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s40_2 : dispatch 3 (optimized 7) b40_2.1 b40_2.2.1 b40_2.2.2 = false := by
  decide +kernel

def b40_3 : W × W × List W :=
  (0xfffffff8000fffff0000000108421084, 0x7c00f800000000004a5294a52, [0xfffffff83ff0001ffffffff8c6318c63, 0x1f003e000000006318c6318, 0x7c0007c00fffffffa5294a529, 0x3e0000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s40_3 : dispatch 3 (optimized 7) b40_3.1 b40_3.2.1 b40_3.2.2 = false := by
  decide +kernel

def b40_4 : W × W × List W :=
  (0xfffffff8000fffff0000000108421084, 0x3e0000000000000739ce739c, [0xfffffff83ff0001ffffffff8c6318c63, 0x1f003e000000006318c6318, 0x7c0007c00fffffffa5294a529, 0x7c00f800000000004a5294a52])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s40_4 : dispatch 3 (optimized 7) b40_4.1 b40_4.2.1 b40_4.2.2 = false := by
  decide +kernel

def b40_5 : W × W × List W :=
  (0xfffffff83ff0001ffffffff8c6318c63, 0x1f003e000000006318c6318, [0xfffffff8000fffff0000000108421084, 0x7c0007c00fffffffa5294a529, 0x7c00f800000000004a5294a52, 0x3e0000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s40_5 : dispatch 3 (optimized 7) b40_5.1 b40_5.2.1 b40_5.2.2 = false := by
  decide +kernel

def b40_6 : W × W × List W :=
  (0xfffffff83ff0001ffffffff8c6318c63, 0x7c0007c00fffffffa5294a529, [0xfffffff8000fffff0000000108421084, 0x1f003e000000006318c6318, 0x7c00f800000000004a5294a52, 0x3e0000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s40_6 : dispatch 3 (optimized 7) b40_6.1 b40_6.2.1 b40_6.2.2 = false := by
  decide +kernel

def b40_7 : W × W × List W :=
  (0xfffffff83ff0001ffffffff8c6318c63, 0x7c00f800000000004a5294a52, [0xfffffff8000fffff0000000108421084, 0x1f003e000000006318c6318, 0x7c0007c00fffffffa5294a529, 0x3e0000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s40_7 : dispatch 3 (optimized 7) b40_7.1 b40_7.2.1 b40_7.2.2 = false := by
  decide +kernel

def b40_8 : W × W × List W :=
  (0xfffffff83ff0001ffffffff8c6318c63, 0x3e0000000000000739ce739c, [0xfffffff8000fffff0000000108421084, 0x1f003e000000006318c6318, 0x7c0007c00fffffffa5294a529, 0x7c00f800000000004a5294a52])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s40_8 : dispatch 3 (optimized 7) b40_8.1 b40_8.2.1 b40_8.2.2 = false := by
  decide +kernel

def b40_9 : W × W × List W :=
  (0x1f003e000000006318c6318, 0x7c0007c00fffffffa5294a529, [0xfffffff8000fffff0000000108421084, 0xfffffff83ff0001ffffffff8c6318c63, 0x7c00f800000000004a5294a52, 0x3e0000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s40_9 : dispatch 3 (optimized 7) b40_9.1 b40_9.2.1 b40_9.2.2 = false := by
  decide +kernel

def b40_10 : W × W × List W :=
  (0x1f003e000000006318c6318, 0x7c00f800000000004a5294a52, [0xfffffff8000fffff0000000108421084, 0xfffffff83ff0001ffffffff8c6318c63, 0x7c0007c00fffffffa5294a529, 0x3e0000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s40_10 : dispatch 3 (optimized 7) b40_10.1 b40_10.2.1 b40_10.2.2 = false := by
  decide +kernel

def b40_11 : W × W × List W :=
  (0x1f003e000000006318c6318, 0x3e0000000000000739ce739c, [0xfffffff8000fffff0000000108421084, 0xfffffff83ff0001ffffffff8c6318c63, 0x7c0007c00fffffffa5294a529, 0x7c00f800000000004a5294a52])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s40_11 : dispatch 3 (optimized 7) b40_11.1 b40_11.2.1 b40_11.2.2 = false := by
  decide +kernel

def b40_12 : W × W × List W :=
  (0x7c0007c00fffffffa5294a529, 0x7c00f800000000004a5294a52, [0xfffffff8000fffff0000000108421084, 0xfffffff83ff0001ffffffff8c6318c63, 0x1f003e000000006318c6318, 0x3e0000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s40_12 : dispatch 3 (optimized 7) b40_12.1 b40_12.2.1 b40_12.2.2 = false := by
  decide +kernel

def b40_13 : W × W × List W :=
  (0x7c0007c00fffffffa5294a529, 0x3e0000000000000739ce739c, [0xfffffff8000fffff0000000108421084, 0xfffffff83ff0001ffffffff8c6318c63, 0x1f003e000000006318c6318, 0x7c00f800000000004a5294a52])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s40_13 : dispatch 3 (optimized 7) b40_13.1 b40_13.2.1 b40_13.2.2 = false := by
  decide +kernel

def b40_14 : W × W × List W :=
  (0x7c00f800000000004a5294a52, 0x3e0000000000000739ce739c, [0xfffffff8000fffff0000000108421084, 0xfffffff83ff0001ffffffff8c6318c63, 0x1f003e000000006318c6318, 0x7c0007c00fffffffa5294a529])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s40_14 : dispatch 3 (optimized 7) b40_14.1 b40_14.2.1 b40_14.2.2 = false := by
  decide +kernel

theorem search40 : optimized 8 3 raw40 = false :=
  split_search 7 3 raw40 [b40_0, b40_1, b40_2, b40_3, b40_4, b40_5, b40_6, b40_7, b40_8, b40_9, b40_10, b40_11, b40_12, b40_13, b40_14]
    (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨s40_0, (List.forall_mem_cons.2 ⟨s40_1, (List.forall_mem_cons.2 ⟨s40_2, (List.forall_mem_cons.2 ⟨s40_3, (List.forall_mem_cons.2 ⟨s40_4, (List.forall_mem_cons.2 ⟨s40_5, (List.forall_mem_cons.2 ⟨s40_6, (List.forall_mem_cons.2 ⟨s40_7, (List.forall_mem_cons.2 ⟨s40_8, (List.forall_mem_cons.2 ⟨s40_9, (List.forall_mem_cons.2 ⟨s40_10, (List.forall_mem_cons.2 ⟨s40_11, (List.forall_mem_cons.2 ⟨s40_12, (List.forall_mem_cons.2 ⟨s40_13, (List.forall_mem_cons.2 ⟨s40_14, (fun _ h => nomatch h)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c40 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4)) x) → 9 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw40 _ 8 3 (by decide +kernel) (by decide +kernel) (by decide)
    (search40) (by decide +kernel) C hm (by omega) he

def raw41 : List W :=
  [0xfffffc000003ffff000000a28a28a28a, 0xfffffc003ffc003ffffffd1451451451, 0xfc0fc00000024924924924, 0xfc003f000fffffc5145145145, 0x3f03f0000000000006186186186, 0x3ffc00000000000038e38e38e38]

def b41_0 : W × W × List W :=
  (0xfffffc000003ffff000000a28a28a28a, 0xfffffc003ffc003ffffffd1451451451, [0xfc0fc00000024924924924, 0xfc003f000fffffc5145145145, 0x3f03f0000000000006186186186, 0x3ffc00000000000038e38e38e38])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s41_0 : dispatch 3 (optimized 7) b41_0.1 b41_0.2.1 b41_0.2.2 = false := by
  decide +kernel

def b41_1 : W × W × List W :=
  (0xfffffc000003ffff000000a28a28a28a, 0xfc0fc00000024924924924, [0xfffffc003ffc003ffffffd1451451451, 0xfc003f000fffffc5145145145, 0x3f03f0000000000006186186186, 0x3ffc00000000000038e38e38e38])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s41_1 : dispatch 3 (optimized 7) b41_1.1 b41_1.2.1 b41_1.2.2 = false := by
  decide +kernel

def b41_2 : W × W × List W :=
  (0xfffffc000003ffff000000a28a28a28a, 0xfc003f000fffffc5145145145, [0xfffffc003ffc003ffffffd1451451451, 0xfc0fc00000024924924924, 0x3f03f0000000000006186186186, 0x3ffc00000000000038e38e38e38])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s41_2 : dispatch 3 (optimized 7) b41_2.1 b41_2.2.1 b41_2.2.2 = false := by
  decide +kernel

def b41_3 : W × W × List W :=
  (0xfffffc000003ffff000000a28a28a28a, 0x3f03f0000000000006186186186, [0xfffffc003ffc003ffffffd1451451451, 0xfc0fc00000024924924924, 0xfc003f000fffffc5145145145, 0x3ffc00000000000038e38e38e38])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s41_3 : dispatch 3 (optimized 7) b41_3.1 b41_3.2.1 b41_3.2.2 = false := by
  decide +kernel

def b41_4 : W × W × List W :=
  (0xfffffc000003ffff000000a28a28a28a, 0x3ffc00000000000038e38e38e38, [0xfffffc003ffc003ffffffd1451451451, 0xfc0fc00000024924924924, 0xfc003f000fffffc5145145145, 0x3f03f0000000000006186186186])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s41_4 : dispatch 3 (optimized 7) b41_4.1 b41_4.2.1 b41_4.2.2 = false := by
  decide +kernel

def b41_5 : W × W × List W :=
  (0xfffffc003ffc003ffffffd1451451451, 0xfc0fc00000024924924924, [0xfffffc000003ffff000000a28a28a28a, 0xfc003f000fffffc5145145145, 0x3f03f0000000000006186186186, 0x3ffc00000000000038e38e38e38])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s41_5 : dispatch 3 (optimized 7) b41_5.1 b41_5.2.1 b41_5.2.2 = false := by
  decide +kernel

def b41_6 : W × W × List W :=
  (0xfffffc003ffc003ffffffd1451451451, 0xfc003f000fffffc5145145145, [0xfffffc000003ffff000000a28a28a28a, 0xfc0fc00000024924924924, 0x3f03f0000000000006186186186, 0x3ffc00000000000038e38e38e38])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s41_6 : dispatch 3 (optimized 7) b41_6.1 b41_6.2.1 b41_6.2.2 = false := by
  decide +kernel

def b41_7 : W × W × List W :=
  (0xfffffc003ffc003ffffffd1451451451, 0x3f03f0000000000006186186186, [0xfffffc000003ffff000000a28a28a28a, 0xfc0fc00000024924924924, 0xfc003f000fffffc5145145145, 0x3ffc00000000000038e38e38e38])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s41_7 : dispatch 3 (optimized 7) b41_7.1 b41_7.2.1 b41_7.2.2 = false := by
  decide +kernel

def b41_8 : W × W × List W :=
  (0xfffffc003ffc003ffffffd1451451451, 0x3ffc00000000000038e38e38e38, [0xfffffc000003ffff000000a28a28a28a, 0xfc0fc00000024924924924, 0xfc003f000fffffc5145145145, 0x3f03f0000000000006186186186])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s41_8 : dispatch 3 (optimized 7) b41_8.1 b41_8.2.1 b41_8.2.2 = false := by
  decide +kernel

def b41_9 : W × W × List W :=
  (0xfc0fc00000024924924924, 0xfc003f000fffffc5145145145, [0xfffffc000003ffff000000a28a28a28a, 0xfffffc003ffc003ffffffd1451451451, 0x3f03f0000000000006186186186, 0x3ffc00000000000038e38e38e38])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s41_9 : dispatch 3 (optimized 7) b41_9.1 b41_9.2.1 b41_9.2.2 = false := by
  decide +kernel

def b41_10 : W × W × List W :=
  (0xfc0fc00000024924924924, 0x3f03f0000000000006186186186, [0xfffffc000003ffff000000a28a28a28a, 0xfffffc003ffc003ffffffd1451451451, 0xfc003f000fffffc5145145145, 0x3ffc00000000000038e38e38e38])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s41_10 : dispatch 3 (optimized 7) b41_10.1 b41_10.2.1 b41_10.2.2 = false := by
  decide +kernel

def b41_11 : W × W × List W :=
  (0xfc0fc00000024924924924, 0x3ffc00000000000038e38e38e38, [0xfffffc000003ffff000000a28a28a28a, 0xfffffc003ffc003ffffffd1451451451, 0xfc003f000fffffc5145145145, 0x3f03f0000000000006186186186])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s41_11 : dispatch 3 (optimized 7) b41_11.1 b41_11.2.1 b41_11.2.2 = false := by
  decide +kernel

def b41_12 : W × W × List W :=
  (0xfc003f000fffffc5145145145, 0x3f03f0000000000006186186186, [0xfffffc000003ffff000000a28a28a28a, 0xfffffc003ffc003ffffffd1451451451, 0xfc0fc00000024924924924, 0x3ffc00000000000038e38e38e38])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s41_12 : dispatch 3 (optimized 7) b41_12.1 b41_12.2.1 b41_12.2.2 = false := by
  decide +kernel

def b41_13 : W × W × List W :=
  (0xfc003f000fffffc5145145145, 0x3ffc00000000000038e38e38e38, [0xfffffc000003ffff000000a28a28a28a, 0xfffffc003ffc003ffffffd1451451451, 0xfc0fc00000024924924924, 0x3f03f0000000000006186186186])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s41_13 : dispatch 3 (optimized 7) b41_13.1 b41_13.2.1 b41_13.2.2 = false := by
  decide +kernel

def b41_14 : W × W × List W :=
  (0x3f03f0000000000006186186186, 0x3ffc00000000000038e38e38e38, [0xfffffc000003ffff000000a28a28a28a, 0xfffffc003ffc003ffffffd1451451451, 0xfc0fc00000024924924924, 0xfc003f000fffffc5145145145])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s41_14 : dispatch 3 (optimized 7) b41_14.1 b41_14.2.1 b41_14.2.2 = false := by
  decide +kernel

theorem search41 : optimized 8 3 raw41 = false :=
  split_search 7 3 raw41 [b41_0, b41_1, b41_2, b41_3, b41_4, b41_5, b41_6, b41_7, b41_8, b41_9, b41_10, b41_11, b41_12, b41_13, b41_14]
    (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨s41_0, (List.forall_mem_cons.2 ⟨s41_1, (List.forall_mem_cons.2 ⟨s41_2, (List.forall_mem_cons.2 ⟨s41_3, (List.forall_mem_cons.2 ⟨s41_4, (List.forall_mem_cons.2 ⟨s41_5, (List.forall_mem_cons.2 ⟨s41_6, (List.forall_mem_cons.2 ⟨s41_7, (List.forall_mem_cons.2 ⟨s41_8, (List.forall_mem_cons.2 ⟨s41_9, (List.forall_mem_cons.2 ⟨s41_10, (List.forall_mem_cons.2 ⟨s41_11, (List.forall_mem_cons.2 ⟨s41_12, (List.forall_mem_cons.2 ⟨s41_13, (List.forall_mem_cons.2 ⟨s41_14, (fun _ h => nomatch h)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c41 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5)) x) → 9 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw41 _ 8 3 (by decide +kernel) (by decide +kernel) (by decide)
    (search41) (by decide +kernel) C hm (by omega) he

def raw42 : List W :=
  [0xffffffff0000ffffffffffff55555555, 0xffffffff000000ff00000000aaaaaaaa, 0xff0000000000aaaaaaaa, 0xff0000ffffffff33333333, 0xff000000000000cccccccc, 0xff000000ffffffff0f0f0f0f, 0xff00000000000000f0f0f0f0]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c42 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) → 6 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small_few raw42 _ 5 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) C hm (by omega) he

def raw43 : List W :=
  [0xfffffffffff0fffffffffffffff55555, 0xfffffffffff0000f00000000000aaaaa, 0xf000000000000aaaaa, 0xf0000000000000aaaaa, 0xf00000000000000aaaaa, 0xf0000fffffffffff33333, 0xf000000000000000ccccc]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c43 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 5 && x 6)) x) → 6 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small_few raw43 _ 5 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) C hm (by omega) he

def raw44 : List W :=
  [0xffffffffc003ffff0000000012492492, 0xffffffffc0fc003fffffffffc9249249, 0xfc0ffffffffedb6db6d, 0x3f000ffffffffedb6db6d, 0xfc00000000000036db6db6, 0x3f000000ffffffffc71c71c7, 0x3f0000000000000038e38e38]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c44 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 5 && x 6)) x) → 7 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw44 _ 6 0 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw45 : List W :=
  [0xfffffffffff00ffffffffffffff55555, 0xfffffffffff0000f00000000000aaaaa, 0xf000000000000aaaaa, 0xf0000000000000aaaaa, 0xff000fffffffffff33333, 0xf00000000000000ccccc, 0xf000000000000000ccccc]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c45 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6)) x) → 6 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small_few raw45 _ 5 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) C hm (by omega) he

def raw46 : List W :=
  [0xf000000000fffffff249249249249249, 0xf000000fff000fff0492492492492492, 0xffffff0000924924924924924, 0xfff000000000f1c71c71c71c71c7, 0xfff0000000000e38e38e38e38e38, 0xfff000000000000f03f03f03f03f03f, 0xfff0000000000000fc0fc0fc0fc0fc0]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c46 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) → 8 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw46 _ 7 1 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw47 : List W :=
  [0xffffff000000ffff0000008888888888, 0xffffff0000ff00ffffffff5555555555, 0xff00ff00ffffff3333333333, 0xff0000000000aaaaaaaaaa, 0xff000000000000cccccccccc, 0xff00000000ffffff0f0f0f0f0f, 0xff00000000000000f0f0f0f0f0]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c47 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 5 && x 6)) x) → 7 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw47 _ 6 0 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw48 : List W :=
  [0xffffffffc0000fff0000000012492492, 0xffffffffc003f03fffffffffc9249249, 0xfc0ffffffffedb6db6d, 0x3f0000000000036db6db6, 0x3ffc0000ffffffffc71c71c7, 0xfc00000000000038e38e38, 0x3f0000000000000038e38e38]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c48 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5) || (x 4 && x 6)) x) → 7 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw48 _ 6 0 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw49 : List W :=
  [0xfffffffffffffffffffffffffffff555, 0xfffffffffffff0030000000000000aaa, 0xc0000000000000aaa, 0x300000000000000aaa, 0xc00000000000000aaa, 0x3000000000000000aaa, 0xc000000000000000aaa]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c49 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6)) x) → 6 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small_few raw49 _ 5 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) C hm (by omega) he

def raw50 : List W :=
  [0xfffffffffffc7fff0000000000012492, 0xffffffffffff8007fffffffffffc9249, 0x38fffffffffffedb6d, 0x1c0fffffffffffedb6d, 0xe00fffffffffffedb6d, 0x7000fffffffffffedb6d, 0x380000000000000036db6]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c50 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6)) x) → 7 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw50 _ 6 0 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw51 : List W :=
  [0xfffffff000fffffffffffff249249249, 0xfffffff03f00003f0000000492492492, 0x3f000fc00000000924924924, 0x3f0000000000db6db6db6, 0xfc00000000000db6db6db6, 0xfc0000000fffffff1c71c71c7, 0xfc00000000000000e38e38e38]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c51 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 5 && x 6)) x) → 8 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw51 _ 7 1 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw52 : List W :=
  [0xfffffffffffc0fff0000000000012492, 0xfffffffffffff007fffffffffffc9249, 0x38fffffffffffedb6d, 0x1c0fffffffffffedb6d, 0xe00fffffffffffedb6d, 0x70000000000000036db6, 0x380000000000000036db6]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c52 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6)) x) → 7 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw52 _ 6 0 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw53 : List W :=
  [0xffffffffc00fffff0000000010842108, 0xffffffffc1f0001fffffffffca5294a5, 0x3e0003e0ffffffffc6318c63, 0x7c00ffffffffef7bdef7, 0xf8000ffffffffef7bdef7, 0x1f000000000000035ad6b5a, 0x3e0000000000000039ce739c]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c53 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6)) x) → 8 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw53 _ 7 1 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw54 : List W :=
  [0xffffffffff00ffffffffffffff555555, 0xffffffffff0f000f0000000000888888, 0xf00000000000aaaaaa, 0xf000000000000aaaaaa, 0xf0000000000000aaaaaa, 0xff0000ffffffffff333333, 0xf000000000000000cccccc]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c54 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 5 && x 6)) x) → 7 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw54 _ 6 0 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw55 : List W :=
  [0xfffffff00003ffff0000000492492492, 0xfffffff03ffc003ffffffff249249249, 0xfc0fc00000000924924924, 0x3f000fffffffb6db6db6d, 0x3f0000000000000db6db6db6, 0xfc0000000fffffff1c71c71c7, 0xfc00000000000000e38e38e38]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c55 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 5 && x 6)) x) → 8 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw55 _ 7 1 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw56 : List W :=
  [0xf00000003fffffff0210842108421084, 0xf00000ffc00003fff4a5294a5294a529, 0xffc00ffc00094a5294a5294a52, 0x3ff003ff00000f18c6318c6318c63, 0x3ff00000000000e739ce739ce739c, 0xffc000000000000f07c1f07c1f07c1f, 0xffc0000000000000f83e0f83e0f83e0]

def b56_0 : W × W × List W :=
  (0xf00000003fffffff0210842108421084, 0xf00000ffc00003fff4a5294a5294a529, [0xffc00ffc00094a5294a5294a52, 0x3ff003ff00000f18c6318c6318c63, 0x3ff00000000000e739ce739ce739c, 0xffc000000000000f07c1f07c1f07c1f, 0xffc0000000000000f83e0f83e0f83e0])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s56_0 : dispatch 2 (optimized 7) b56_0.1 b56_0.2.1 b56_0.2.2 = false := by
  decide +kernel

def b56_1 : W × W × List W :=
  (0xf00000003fffffff0210842108421084, 0xffc00ffc00094a5294a5294a52, [0xf00000ffc00003fff4a5294a5294a529, 0x3ff003ff00000f18c6318c6318c63, 0x3ff00000000000e739ce739ce739c, 0xffc000000000000f07c1f07c1f07c1f, 0xffc0000000000000f83e0f83e0f83e0])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s56_1 : dispatch 2 (optimized 7) b56_1.1 b56_1.2.1 b56_1.2.2 = false := by
  decide +kernel

def b56_2 : W × W × List W :=
  (0xf00000003fffffff0210842108421084, 0x3ff003ff00000f18c6318c6318c63, [0xf00000ffc00003fff4a5294a5294a529, 0xffc00ffc00094a5294a5294a52, 0x3ff00000000000e739ce739ce739c, 0xffc000000000000f07c1f07c1f07c1f, 0xffc0000000000000f83e0f83e0f83e0])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s56_2 : dispatch 2 (optimized 7) b56_2.1 b56_2.2.1 b56_2.2.2 = false := by
  decide +kernel

def b56_3 : W × W × List W :=
  (0xf00000003fffffff0210842108421084, 0x3ff00000000000e739ce739ce739c, [0xf00000ffc00003fff4a5294a5294a529, 0xffc00ffc00094a5294a5294a52, 0x3ff003ff00000f18c6318c6318c63, 0xffc000000000000f07c1f07c1f07c1f, 0xffc0000000000000f83e0f83e0f83e0])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s56_3 : dispatch 2 (optimized 7) b56_3.1 b56_3.2.1 b56_3.2.2 = false := by
  decide +kernel

def b56_4 : W × W × List W :=
  (0xf00000003fffffff0210842108421084, 0xffc000000000000f07c1f07c1f07c1f, [0xf00000ffc00003fff4a5294a5294a529, 0xffc00ffc00094a5294a5294a52, 0x3ff003ff00000f18c6318c6318c63, 0x3ff00000000000e739ce739ce739c, 0xffc0000000000000f83e0f83e0f83e0])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s56_4 : dispatch 2 (optimized 7) b56_4.1 b56_4.2.1 b56_4.2.2 = false := by
  decide +kernel

def b56_5 : W × W × List W :=
  (0xf00000003fffffff0210842108421084, 0xffc0000000000000f83e0f83e0f83e0, [0xf00000ffc00003fff4a5294a5294a529, 0xffc00ffc00094a5294a5294a52, 0x3ff003ff00000f18c6318c6318c63, 0x3ff00000000000e739ce739ce739c, 0xffc000000000000f07c1f07c1f07c1f])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s56_5 : dispatch 2 (optimized 7) b56_5.1 b56_5.2.1 b56_5.2.2 = false := by
  decide +kernel

def b56_6 : W × W × List W :=
  (0xf00000ffc00003fff4a5294a5294a529, 0xffc00ffc00094a5294a5294a52, [0xf00000003fffffff0210842108421084, 0x3ff003ff00000f18c6318c6318c63, 0x3ff00000000000e739ce739ce739c, 0xffc000000000000f07c1f07c1f07c1f, 0xffc0000000000000f83e0f83e0f83e0])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s56_6 : dispatch 2 (optimized 7) b56_6.1 b56_6.2.1 b56_6.2.2 = false := by
  decide +kernel

def b56_7 : W × W × List W :=
  (0xf00000ffc00003fff4a5294a5294a529, 0x3ff003ff00000f18c6318c6318c63, [0xf00000003fffffff0210842108421084, 0xffc00ffc00094a5294a5294a52, 0x3ff00000000000e739ce739ce739c, 0xffc000000000000f07c1f07c1f07c1f, 0xffc0000000000000f83e0f83e0f83e0])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s56_7 : dispatch 2 (optimized 7) b56_7.1 b56_7.2.1 b56_7.2.2 = false := by
  decide +kernel

def b56_8 : W × W × List W :=
  (0xf00000ffc00003fff4a5294a5294a529, 0x3ff00000000000e739ce739ce739c, [0xf00000003fffffff0210842108421084, 0xffc00ffc00094a5294a5294a52, 0x3ff003ff00000f18c6318c6318c63, 0xffc000000000000f07c1f07c1f07c1f, 0xffc0000000000000f83e0f83e0f83e0])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s56_8 : dispatch 2 (optimized 7) b56_8.1 b56_8.2.1 b56_8.2.2 = false := by
  decide +kernel

def b56_9 : W × W × List W :=
  (0xf00000ffc00003fff4a5294a5294a529, 0xffc000000000000f07c1f07c1f07c1f, [0xf00000003fffffff0210842108421084, 0xffc00ffc00094a5294a5294a52, 0x3ff003ff00000f18c6318c6318c63, 0x3ff00000000000e739ce739ce739c, 0xffc0000000000000f83e0f83e0f83e0])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s56_9 : dispatch 2 (optimized 7) b56_9.1 b56_9.2.1 b56_9.2.2 = false := by
  decide +kernel

def b56_10 : W × W × List W :=
  (0xf00000ffc00003fff4a5294a5294a529, 0xffc0000000000000f83e0f83e0f83e0, [0xf00000003fffffff0210842108421084, 0xffc00ffc00094a5294a5294a52, 0x3ff003ff00000f18c6318c6318c63, 0x3ff00000000000e739ce739ce739c, 0xffc000000000000f07c1f07c1f07c1f])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s56_10 : dispatch 2 (optimized 7) b56_10.1 b56_10.2.1 b56_10.2.2 = false := by
  decide +kernel

def b56_11 : W × W × List W :=
  (0xffc00ffc00094a5294a5294a52, 0x3ff003ff00000f18c6318c6318c63, [0xf00000003fffffff0210842108421084, 0xf00000ffc00003fff4a5294a5294a529, 0x3ff00000000000e739ce739ce739c, 0xffc000000000000f07c1f07c1f07c1f, 0xffc0000000000000f83e0f83e0f83e0])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s56_11 : dispatch 2 (optimized 7) b56_11.1 b56_11.2.1 b56_11.2.2 = false := by
  decide +kernel

def b56_12 : W × W × List W :=
  (0xffc00ffc00094a5294a5294a52, 0x3ff00000000000e739ce739ce739c, [0xf00000003fffffff0210842108421084, 0xf00000ffc00003fff4a5294a5294a529, 0x3ff003ff00000f18c6318c6318c63, 0xffc000000000000f07c1f07c1f07c1f, 0xffc0000000000000f83e0f83e0f83e0])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s56_12 : dispatch 2 (optimized 7) b56_12.1 b56_12.2.1 b56_12.2.2 = false := by
  decide +kernel

def b56_13 : W × W × List W :=
  (0xffc00ffc00094a5294a5294a52, 0xffc000000000000f07c1f07c1f07c1f, [0xf00000003fffffff0210842108421084, 0xf00000ffc00003fff4a5294a5294a529, 0x3ff003ff00000f18c6318c6318c63, 0x3ff00000000000e739ce739ce739c, 0xffc0000000000000f83e0f83e0f83e0])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s56_13 : dispatch 2 (optimized 7) b56_13.1 b56_13.2.1 b56_13.2.2 = false := by
  decide +kernel

def b56_14 : W × W × List W :=
  (0xffc00ffc00094a5294a5294a52, 0xffc0000000000000f83e0f83e0f83e0, [0xf00000003fffffff0210842108421084, 0xf00000ffc00003fff4a5294a5294a529, 0x3ff003ff00000f18c6318c6318c63, 0x3ff00000000000e739ce739ce739c, 0xffc000000000000f07c1f07c1f07c1f])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s56_14 : dispatch 2 (optimized 7) b56_14.1 b56_14.2.1 b56_14.2.2 = false := by
  decide +kernel

def b56_15 : W × W × List W :=
  (0x3ff003ff00000f18c6318c6318c63, 0x3ff00000000000e739ce739ce739c, [0xf00000003fffffff0210842108421084, 0xf00000ffc00003fff4a5294a5294a529, 0xffc00ffc00094a5294a5294a52, 0xffc000000000000f07c1f07c1f07c1f, 0xffc0000000000000f83e0f83e0f83e0])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s56_15 : dispatch 2 (optimized 7) b56_15.1 b56_15.2.1 b56_15.2.2 = false := by
  decide +kernel

def b56_16 : W × W × List W :=
  (0x3ff003ff00000f18c6318c6318c63, 0xffc000000000000f07c1f07c1f07c1f, [0xf00000003fffffff0210842108421084, 0xf00000ffc00003fff4a5294a5294a529, 0xffc00ffc00094a5294a5294a52, 0x3ff00000000000e739ce739ce739c, 0xffc0000000000000f83e0f83e0f83e0])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s56_16 : dispatch 2 (optimized 7) b56_16.1 b56_16.2.1 b56_16.2.2 = false := by
  decide +kernel

def b56_17 : W × W × List W :=
  (0x3ff003ff00000f18c6318c6318c63, 0xffc0000000000000f83e0f83e0f83e0, [0xf00000003fffffff0210842108421084, 0xf00000ffc00003fff4a5294a5294a529, 0xffc00ffc00094a5294a5294a52, 0x3ff00000000000e739ce739ce739c, 0xffc000000000000f07c1f07c1f07c1f])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s56_17 : dispatch 2 (optimized 7) b56_17.1 b56_17.2.1 b56_17.2.2 = false := by
  decide +kernel

def b56_18 : W × W × List W :=
  (0x3ff00000000000e739ce739ce739c, 0xffc000000000000f07c1f07c1f07c1f, [0xf00000003fffffff0210842108421084, 0xf00000ffc00003fff4a5294a5294a529, 0xffc00ffc00094a5294a5294a52, 0x3ff003ff00000f18c6318c6318c63, 0xffc0000000000000f83e0f83e0f83e0])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s56_18 : dispatch 2 (optimized 7) b56_18.1 b56_18.2.1 b56_18.2.2 = false := by
  decide +kernel

def b56_19 : W × W × List W :=
  (0x3ff00000000000e739ce739ce739c, 0xffc0000000000000f83e0f83e0f83e0, [0xf00000003fffffff0210842108421084, 0xf00000ffc00003fff4a5294a5294a529, 0xffc00ffc00094a5294a5294a52, 0x3ff003ff00000f18c6318c6318c63, 0xffc000000000000f07c1f07c1f07c1f])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s56_19 : dispatch 2 (optimized 7) b56_19.1 b56_19.2.1 b56_19.2.2 = false := by
  decide +kernel

def b56_20 : W × W × List W :=
  (0xffc000000000000f07c1f07c1f07c1f, 0xffc0000000000000f83e0f83e0f83e0, [0xf00000003fffffff0210842108421084, 0xf00000ffc00003fff4a5294a5294a529, 0xffc00ffc00094a5294a5294a52, 0x3ff003ff00000f18c6318c6318c63, 0x3ff00000000000e739ce739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s56_20 : dispatch 2 (optimized 7) b56_20.1 b56_20.2.1 b56_20.2.2 = false := by
  decide +kernel

theorem search56 : optimized 8 2 raw56 = false :=
  split_search 7 2 raw56 [b56_0, b56_1, b56_2, b56_3, b56_4, b56_5, b56_6, b56_7, b56_8, b56_9, b56_10, b56_11, b56_12, b56_13, b56_14, b56_15, b56_16, b56_17, b56_18, b56_19, b56_20]
    (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨s56_0, (List.forall_mem_cons.2 ⟨s56_1, (List.forall_mem_cons.2 ⟨s56_2, (List.forall_mem_cons.2 ⟨s56_3, (List.forall_mem_cons.2 ⟨s56_4, (List.forall_mem_cons.2 ⟨s56_5, (List.forall_mem_cons.2 ⟨s56_6, (List.forall_mem_cons.2 ⟨s56_7, (List.forall_mem_cons.2 ⟨s56_8, (List.forall_mem_cons.2 ⟨s56_9, (List.forall_mem_cons.2 ⟨s56_10, (List.forall_mem_cons.2 ⟨s56_11, (List.forall_mem_cons.2 ⟨s56_12, (List.forall_mem_cons.2 ⟨s56_13, (List.forall_mem_cons.2 ⟨s56_14, (List.forall_mem_cons.2 ⟨s56_15, (List.forall_mem_cons.2 ⟨s56_16, (List.forall_mem_cons.2 ⟨s56_17, (List.forall_mem_cons.2 ⟨s56_18, (List.forall_mem_cons.2 ⟨s56_19, (List.forall_mem_cons.2 ⟨s56_20, (fun _ h => nomatch h)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c56 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) → 9 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw56 _ 8 2 (by decide +kernel) (by decide +kernel) (by decide)
    (search56) (by decide +kernel) C hm (by omega) he

def raw57 : List W :=
  [0xfffffff00003fffffffffff249249249, 0xfffffff000fc003f0000000492492492, 0xfc0fc00000000924924924, 0x3f0000000000db6db6db6, 0xfff000000fffffff1c71c71c7, 0x3f0000000000000e38e38e38, 0xfc00000000000000e38e38e38]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c57 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6)) x) → 8 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw57 _ 7 1 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw58 : List W :=
  [0xffffffffc0007fff0000000010842108, 0xffffffffc1ff801fffffffffca5294a5, 0x3e0003e0ffffffffc6318c63, 0x7c00ffffffffef7bdef7, 0xf80000000000035ad6b5a, 0x1f000000000000035ad6b5a, 0x3e0000000000000039ce739c]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c58 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6)) x) → 8 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw58 _ 7 1 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw59 : List W :=
  [0xffff000000ffffff0000808080808080, 0xffff0000ff0000ffffff555555555555, 0xff0000ff00ffff333333333333, 0xff0000ff0000ffff0f0f0f0f0f0f, 0xff0000000000aaaaaaaaaaaa, 0xff000000000000cccccccccccc, 0xff00000000000000f0f0f0f0f0f0]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c59 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) x) → 8 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw59 _ 7 1 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw60 : List W :=
  [0xfffffff00003ffff0000000492492492, 0xfffffff000fc003f0000000a28a28a28, 0x3f000fc0fffffff249249249, 0x3f000fffffffb6db6db6d, 0xfc0fc0000fffffff1c71c71c7, 0x3f0000000000000db6db6db6, 0xfc00000000000000e38e38e38]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c60 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6)) x) → 8 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw60 _ 7 1 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw61 : List W :=
  [0xffffffffff000fffffffffffff555555, 0xffffffffff00f00f0000000000888888, 0xf00000000000aaaaaa, 0xf000000000000aaaaaa, 0xfff000ffffffffff333333, 0xf00000000000000cccccc, 0xf000000000000000cccccc]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c61 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 4 && x 6)) x) → 7 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw61 _ 6 0 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw62 : List W :=
  [0xffffffffc0007fffffffffffd294a529, 0xffffffffc00f801f000000000c6318c6, 0x3e0000000002d6b5ad6, 0x7c00000000002d6b5ad6, 0x1ff800000000000318c6318, 0x3ff00000ffffffffc6318c63, 0x3e0000000000000039ce739c]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c62 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 5 && x 6)) x) → 8 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw62 _ 7 1 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw63 : List W :=
  [0xfffffff00003fffffffffff555555555, 0xfffffff00000003f0000000aaaaaaaaa, 0xfc00000000aaaaaaaaa, 0x3f0000000000aaaaaaaaa, 0x3ffc0000fffffff0c30c30c3, 0xfc0fc0000000000030c30c30c, 0xfff0000000000000c30c30c30]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c63 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 8 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw63 _ 7 1 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw64 : List W :=
  [0xffc000000003ffffffc9249249249249, 0xffc0000007fc01ff0012492492492492, 0x7fffe000024924924924924, 0x1ffff800000000070381c0e07038, 0x3fe00ff8000000ffc0e070381c0e07, 0x1ff000000000fff8fc7e3f1f8fc7, 0x3fe00000000000003f1f8fc7e3f1f8]

def b64_0 : W × W × List W :=
  (0xffc000000003ffffffc9249249249249, 0xffc0000007fc01ff0012492492492492, [0x7fffe000024924924924924, 0x1ffff800000000070381c0e07038, 0x3fe00ff8000000ffc0e070381c0e07, 0x1ff000000000fff8fc7e3f1f8fc7, 0x3fe00000000000003f1f8fc7e3f1f8])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s64_0 : dispatch 2 (optimized 7) b64_0.1 b64_0.2.1 b64_0.2.2 = false := by
  decide +kernel

def b64_1 : W × W × List W :=
  (0xffc000000003ffffffc9249249249249, 0x7fffe000024924924924924, [0xffc0000007fc01ff0012492492492492, 0x1ffff800000000070381c0e07038, 0x3fe00ff8000000ffc0e070381c0e07, 0x1ff000000000fff8fc7e3f1f8fc7, 0x3fe00000000000003f1f8fc7e3f1f8])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s64_1 : dispatch 2 (optimized 7) b64_1.1 b64_1.2.1 b64_1.2.2 = false := by
  decide +kernel

def b64_2 : W × W × List W :=
  (0xffc000000003ffffffc9249249249249, 0x1ffff800000000070381c0e07038, [0xffc0000007fc01ff0012492492492492, 0x7fffe000024924924924924, 0x3fe00ff8000000ffc0e070381c0e07, 0x1ff000000000fff8fc7e3f1f8fc7, 0x3fe00000000000003f1f8fc7e3f1f8])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s64_2 : dispatch 2 (optimized 7) b64_2.1 b64_2.2.1 b64_2.2.2 = false := by
  decide +kernel

def b64_3 : W × W × List W :=
  (0xffc000000003ffffffc9249249249249, 0x3fe00ff8000000ffc0e070381c0e07, [0xffc0000007fc01ff0012492492492492, 0x7fffe000024924924924924, 0x1ffff800000000070381c0e07038, 0x1ff000000000fff8fc7e3f1f8fc7, 0x3fe00000000000003f1f8fc7e3f1f8])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s64_3 : dispatch 2 (optimized 7) b64_3.1 b64_3.2.1 b64_3.2.2 = false := by
  decide +kernel

def b64_4 : W × W × List W :=
  (0xffc000000003ffffffc9249249249249, 0x1ff000000000fff8fc7e3f1f8fc7, [0xffc0000007fc01ff0012492492492492, 0x7fffe000024924924924924, 0x1ffff800000000070381c0e07038, 0x3fe00ff8000000ffc0e070381c0e07, 0x3fe00000000000003f1f8fc7e3f1f8])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s64_4 : dispatch 2 (optimized 7) b64_4.1 b64_4.2.1 b64_4.2.2 = false := by
  decide +kernel

def b64_5 : W × W × List W :=
  (0xffc000000003ffffffc9249249249249, 0x3fe00000000000003f1f8fc7e3f1f8, [0xffc0000007fc01ff0012492492492492, 0x7fffe000024924924924924, 0x1ffff800000000070381c0e07038, 0x3fe00ff8000000ffc0e070381c0e07, 0x1ff000000000fff8fc7e3f1f8fc7])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s64_5 : dispatch 2 (optimized 7) b64_5.1 b64_5.2.1 b64_5.2.2 = false := by
  decide +kernel

def b64_6 : W × W × List W :=
  (0xffc0000007fc01ff0012492492492492, 0x7fffe000024924924924924, [0xffc000000003ffffffc9249249249249, 0x1ffff800000000070381c0e07038, 0x3fe00ff8000000ffc0e070381c0e07, 0x1ff000000000fff8fc7e3f1f8fc7, 0x3fe00000000000003f1f8fc7e3f1f8])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s64_6 : dispatch 2 (optimized 7) b64_6.1 b64_6.2.1 b64_6.2.2 = false := by
  decide +kernel

def b64_7 : W × W × List W :=
  (0xffc0000007fc01ff0012492492492492, 0x1ffff800000000070381c0e07038, [0xffc000000003ffffffc9249249249249, 0x7fffe000024924924924924, 0x3fe00ff8000000ffc0e070381c0e07, 0x1ff000000000fff8fc7e3f1f8fc7, 0x3fe00000000000003f1f8fc7e3f1f8])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s64_7 : dispatch 2 (optimized 7) b64_7.1 b64_7.2.1 b64_7.2.2 = false := by
  decide +kernel

def b64_8 : W × W × List W :=
  (0xffc0000007fc01ff0012492492492492, 0x3fe00ff8000000ffc0e070381c0e07, [0xffc000000003ffffffc9249249249249, 0x7fffe000024924924924924, 0x1ffff800000000070381c0e07038, 0x1ff000000000fff8fc7e3f1f8fc7, 0x3fe00000000000003f1f8fc7e3f1f8])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s64_8 : dispatch 2 (optimized 7) b64_8.1 b64_8.2.1 b64_8.2.2 = false := by
  decide +kernel

def b64_9 : W × W × List W :=
  (0xffc0000007fc01ff0012492492492492, 0x1ff000000000fff8fc7e3f1f8fc7, [0xffc000000003ffffffc9249249249249, 0x7fffe000024924924924924, 0x1ffff800000000070381c0e07038, 0x3fe00ff8000000ffc0e070381c0e07, 0x3fe00000000000003f1f8fc7e3f1f8])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s64_9 : dispatch 2 (optimized 7) b64_9.1 b64_9.2.1 b64_9.2.2 = false := by
  decide +kernel

def b64_10 : W × W × List W :=
  (0xffc0000007fc01ff0012492492492492, 0x3fe00000000000003f1f8fc7e3f1f8, [0xffc000000003ffffffc9249249249249, 0x7fffe000024924924924924, 0x1ffff800000000070381c0e07038, 0x3fe00ff8000000ffc0e070381c0e07, 0x1ff000000000fff8fc7e3f1f8fc7])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s64_10 : dispatch 2 (optimized 7) b64_10.1 b64_10.2.1 b64_10.2.2 = false := by
  decide +kernel

def b64_11 : W × W × List W :=
  (0x7fffe000024924924924924, 0x1ffff800000000070381c0e07038, [0xffc000000003ffffffc9249249249249, 0xffc0000007fc01ff0012492492492492, 0x3fe00ff8000000ffc0e070381c0e07, 0x1ff000000000fff8fc7e3f1f8fc7, 0x3fe00000000000003f1f8fc7e3f1f8])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s64_11 : dispatch 2 (optimized 7) b64_11.1 b64_11.2.1 b64_11.2.2 = false := by
  decide +kernel

def b64_12 : W × W × List W :=
  (0x7fffe000024924924924924, 0x3fe00ff8000000ffc0e070381c0e07, [0xffc000000003ffffffc9249249249249, 0xffc0000007fc01ff0012492492492492, 0x1ffff800000000070381c0e07038, 0x1ff000000000fff8fc7e3f1f8fc7, 0x3fe00000000000003f1f8fc7e3f1f8])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s64_12 : dispatch 2 (optimized 7) b64_12.1 b64_12.2.1 b64_12.2.2 = false := by
  decide +kernel

def b64_13 : W × W × List W :=
  (0x7fffe000024924924924924, 0x1ff000000000fff8fc7e3f1f8fc7, [0xffc000000003ffffffc9249249249249, 0xffc0000007fc01ff0012492492492492, 0x1ffff800000000070381c0e07038, 0x3fe00ff8000000ffc0e070381c0e07, 0x3fe00000000000003f1f8fc7e3f1f8])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s64_13 : dispatch 2 (optimized 7) b64_13.1 b64_13.2.1 b64_13.2.2 = false := by
  decide +kernel

def b64_14 : W × W × List W :=
  (0x7fffe000024924924924924, 0x3fe00000000000003f1f8fc7e3f1f8, [0xffc000000003ffffffc9249249249249, 0xffc0000007fc01ff0012492492492492, 0x1ffff800000000070381c0e07038, 0x3fe00ff8000000ffc0e070381c0e07, 0x1ff000000000fff8fc7e3f1f8fc7])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s64_14 : dispatch 2 (optimized 7) b64_14.1 b64_14.2.1 b64_14.2.2 = false := by
  decide +kernel

def b64_15 : W × W × List W :=
  (0x1ffff800000000070381c0e07038, 0x3fe00ff8000000ffc0e070381c0e07, [0xffc000000003ffffffc9249249249249, 0xffc0000007fc01ff0012492492492492, 0x7fffe000024924924924924, 0x1ff000000000fff8fc7e3f1f8fc7, 0x3fe00000000000003f1f8fc7e3f1f8])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s64_15 : dispatch 2 (optimized 7) b64_15.1 b64_15.2.1 b64_15.2.2 = false := by
  decide +kernel

def b64_16 : W × W × List W :=
  (0x1ffff800000000070381c0e07038, 0x1ff000000000fff8fc7e3f1f8fc7, [0xffc000000003ffffffc9249249249249, 0xffc0000007fc01ff0012492492492492, 0x7fffe000024924924924924, 0x3fe00ff8000000ffc0e070381c0e07, 0x3fe00000000000003f1f8fc7e3f1f8])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s64_16 : dispatch 2 (optimized 7) b64_16.1 b64_16.2.1 b64_16.2.2 = false := by
  decide +kernel

def b64_17 : W × W × List W :=
  (0x1ffff800000000070381c0e07038, 0x3fe00000000000003f1f8fc7e3f1f8, [0xffc000000003ffffffc9249249249249, 0xffc0000007fc01ff0012492492492492, 0x7fffe000024924924924924, 0x3fe00ff8000000ffc0e070381c0e07, 0x1ff000000000fff8fc7e3f1f8fc7])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s64_17 : dispatch 2 (optimized 7) b64_17.1 b64_17.2.1 b64_17.2.2 = false := by
  decide +kernel

def b64_18 : W × W × List W :=
  (0x3fe00ff8000000ffc0e070381c0e07, 0x1ff000000000fff8fc7e3f1f8fc7, [0xffc000000003ffffffc9249249249249, 0xffc0000007fc01ff0012492492492492, 0x7fffe000024924924924924, 0x1ffff800000000070381c0e07038, 0x3fe00000000000003f1f8fc7e3f1f8])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s64_18 : dispatch 2 (optimized 7) b64_18.1 b64_18.2.1 b64_18.2.2 = false := by
  decide +kernel

def b64_19 : W × W × List W :=
  (0x3fe00ff8000000ffc0e070381c0e07, 0x3fe00000000000003f1f8fc7e3f1f8, [0xffc000000003ffffffc9249249249249, 0xffc0000007fc01ff0012492492492492, 0x7fffe000024924924924924, 0x1ffff800000000070381c0e07038, 0x1ff000000000fff8fc7e3f1f8fc7])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s64_19 : dispatch 2 (optimized 7) b64_19.1 b64_19.2.1 b64_19.2.2 = false := by
  decide +kernel

def b64_20 : W × W × List W :=
  (0x1ff000000000fff8fc7e3f1f8fc7, 0x3fe00000000000003f1f8fc7e3f1f8, [0xffc000000003ffffffc9249249249249, 0xffc0000007fc01ff0012492492492492, 0x7fffe000024924924924924, 0x1ffff800000000070381c0e07038, 0x3fe00ff8000000ffc0e070381c0e07])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s64_20 : dispatch 2 (optimized 7) b64_20.1 b64_20.2.1 b64_20.2.2 = false := by
  decide +kernel

theorem search64 : optimized 8 2 raw64 = false :=
  split_search 7 2 raw64 [b64_0, b64_1, b64_2, b64_3, b64_4, b64_5, b64_6, b64_7, b64_8, b64_9, b64_10, b64_11, b64_12, b64_13, b64_14, b64_15, b64_16, b64_17, b64_18, b64_19, b64_20]
    (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨s64_0, (List.forall_mem_cons.2 ⟨s64_1, (List.forall_mem_cons.2 ⟨s64_2, (List.forall_mem_cons.2 ⟨s64_3, (List.forall_mem_cons.2 ⟨s64_4, (List.forall_mem_cons.2 ⟨s64_5, (List.forall_mem_cons.2 ⟨s64_6, (List.forall_mem_cons.2 ⟨s64_7, (List.forall_mem_cons.2 ⟨s64_8, (List.forall_mem_cons.2 ⟨s64_9, (List.forall_mem_cons.2 ⟨s64_10, (List.forall_mem_cons.2 ⟨s64_11, (List.forall_mem_cons.2 ⟨s64_12, (List.forall_mem_cons.2 ⟨s64_13, (List.forall_mem_cons.2 ⟨s64_14, (List.forall_mem_cons.2 ⟨s64_15, (List.forall_mem_cons.2 ⟨s64_16, (List.forall_mem_cons.2 ⟨s64_17, (List.forall_mem_cons.2 ⟨s64_18, (List.forall_mem_cons.2 ⟨s64_19, (List.forall_mem_cons.2 ⟨s64_20, (fun _ h => nomatch h)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c64 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) x) → 9 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw64 _ 8 2 (by decide +kernel) (by decide +kernel) (by decide)
    (search64) (by decide +kernel) C hm (by omega) he

def raw65 : List W :=
  [0xf0000000000fffff05294a5294a5294a, 0xf00000003ff003fff8c6318c6318c631, 0xffc00ffc00f294a5294a5294a5, 0x3ff003ff000000318c6318c6318c6, 0x3ffffc00000000c6318c6318c6318, 0xffc000000000000f07c1f07c1f07c1f, 0xffc0000000000000f83e0f83e0f83e0]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c65 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4) || (x 5 && x 6)) x) → 9 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw65 _ 8 2 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw66 : List W :=
  [0xfffffc0000003ffffffffd5ab56ad5ab, 0xfffffc00001fc07f0000022448912244, 0xfe03f80000002850a142850, 0x7f01fc000fffffcc993264c99, 0x3f80fe00000fffffc3870e1c387, 0x7f0000000000003366cd9b366, 0x3f800000000000003c78f1e3c78]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c66 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6)) x) → 8 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw66 _ 7 1 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw67 : List W :=
  [0xffffffffffe3ffffffffffffffe49249, 0xfffffffffffc00070000000000092492, 0x1c00380000000000124924, 0x1c000000000001b6db6, 0xe0000000000001b6db6, 0x700000000000001b6db6, 0x3800000000000001b6db6]

def b67_0 : W × W × List W :=
  (0xffffffffffe3ffffffffffffffe49249, 0xfffffffffffc00070000000000092492, [0x1c00380000000000124924, 0x1c000000000001b6db6, 0xe0000000000001b6db6, 0x700000000000001b6db6, 0x3800000000000001b6db6])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s67_0 : dispatch 1 (optimized 6) b67_0.1 b67_0.2.1 b67_0.2.2 = false := by
  decide +kernel

def b67_1 : W × W × List W :=
  (0xffffffffffe3ffffffffffffffe49249, 0x1c00380000000000124924, [0xfffffffffffc00070000000000092492, 0x1c000000000001b6db6, 0xe0000000000001b6db6, 0x700000000000001b6db6, 0x3800000000000001b6db6])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s67_1 : dispatch 1 (optimized 6) b67_1.1 b67_1.2.1 b67_1.2.2 = false := by
  decide +kernel

def b67_2 : W × W × List W :=
  (0xffffffffffe3ffffffffffffffe49249, 0x1c000000000001b6db6, [0xfffffffffffc00070000000000092492, 0x1c00380000000000124924, 0xe0000000000001b6db6, 0x700000000000001b6db6, 0x3800000000000001b6db6])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s67_2 : dispatch 1 (optimized 6) b67_2.1 b67_2.2.1 b67_2.2.2 = false := by
  decide +kernel

def b67_3 : W × W × List W :=
  (0xffffffffffe3ffffffffffffffe49249, 0xe0000000000001b6db6, [0xfffffffffffc00070000000000092492, 0x1c00380000000000124924, 0x1c000000000001b6db6, 0x700000000000001b6db6, 0x3800000000000001b6db6])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s67_3 : dispatch 1 (optimized 6) b67_3.1 b67_3.2.1 b67_3.2.2 = false := by
  decide +kernel

def b67_4 : W × W × List W :=
  (0xffffffffffe3ffffffffffffffe49249, 0x700000000000001b6db6, [0xfffffffffffc00070000000000092492, 0x1c00380000000000124924, 0x1c000000000001b6db6, 0xe0000000000001b6db6, 0x3800000000000001b6db6])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s67_4 : dispatch 1 (optimized 6) b67_4.1 b67_4.2.1 b67_4.2.2 = false := by
  decide +kernel

def b67_5 : W × W × List W :=
  (0xffffffffffe3ffffffffffffffe49249, 0x3800000000000001b6db6, [0xfffffffffffc00070000000000092492, 0x1c00380000000000124924, 0x1c000000000001b6db6, 0xe0000000000001b6db6, 0x700000000000001b6db6])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s67_5 : dispatch 1 (optimized 6) b67_5.1 b67_5.2.1 b67_5.2.2 = false := by
  decide +kernel

def b67_6 : W × W × List W :=
  (0xfffffffffffc00070000000000092492, 0x1c00380000000000124924, [0xffffffffffe3ffffffffffffffe49249, 0x1c000000000001b6db6, 0xe0000000000001b6db6, 0x700000000000001b6db6, 0x3800000000000001b6db6])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s67_6 : dispatch 1 (optimized 6) b67_6.1 b67_6.2.1 b67_6.2.2 = false := by
  decide +kernel

def b67_7 : W × W × List W :=
  (0xfffffffffffc00070000000000092492, 0x1c000000000001b6db6, [0xffffffffffe3ffffffffffffffe49249, 0x1c00380000000000124924, 0xe0000000000001b6db6, 0x700000000000001b6db6, 0x3800000000000001b6db6])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s67_7 : dispatch 1 (optimized 6) b67_7.1 b67_7.2.1 b67_7.2.2 = false := by
  decide +kernel

def b67_8 : W × W × List W :=
  (0xfffffffffffc00070000000000092492, 0xe0000000000001b6db6, [0xffffffffffe3ffffffffffffffe49249, 0x1c00380000000000124924, 0x1c000000000001b6db6, 0x700000000000001b6db6, 0x3800000000000001b6db6])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s67_8 : dispatch 1 (optimized 6) b67_8.1 b67_8.2.1 b67_8.2.2 = false := by
  decide +kernel

def b67_9 : W × W × List W :=
  (0xfffffffffffc00070000000000092492, 0x700000000000001b6db6, [0xffffffffffe3ffffffffffffffe49249, 0x1c00380000000000124924, 0x1c000000000001b6db6, 0xe0000000000001b6db6, 0x3800000000000001b6db6])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s67_9 : dispatch 1 (optimized 6) b67_9.1 b67_9.2.1 b67_9.2.2 = false := by
  decide +kernel

def b67_10 : W × W × List W :=
  (0xfffffffffffc00070000000000092492, 0x3800000000000001b6db6, [0xffffffffffe3ffffffffffffffe49249, 0x1c00380000000000124924, 0x1c000000000001b6db6, 0xe0000000000001b6db6, 0x700000000000001b6db6])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s67_10 : dispatch 1 (optimized 6) b67_10.1 b67_10.2.1 b67_10.2.2 = false := by
  decide +kernel

def b67_11 : W × W × List W :=
  (0x1c00380000000000124924, 0x1c000000000001b6db6, [0xffffffffffe3ffffffffffffffe49249, 0xfffffffffffc00070000000000092492, 0xe0000000000001b6db6, 0x700000000000001b6db6, 0x3800000000000001b6db6])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s67_11 : dispatch 1 (optimized 6) b67_11.1 b67_11.2.1 b67_11.2.2 = false := by
  decide +kernel

def b67_12 : W × W × List W :=
  (0x1c00380000000000124924, 0xe0000000000001b6db6, [0xffffffffffe3ffffffffffffffe49249, 0xfffffffffffc00070000000000092492, 0x1c000000000001b6db6, 0x700000000000001b6db6, 0x3800000000000001b6db6])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s67_12 : dispatch 1 (optimized 6) b67_12.1 b67_12.2.1 b67_12.2.2 = false := by
  decide +kernel

def b67_13 : W × W × List W :=
  (0x1c00380000000000124924, 0x700000000000001b6db6, [0xffffffffffe3ffffffffffffffe49249, 0xfffffffffffc00070000000000092492, 0x1c000000000001b6db6, 0xe0000000000001b6db6, 0x3800000000000001b6db6])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s67_13 : dispatch 1 (optimized 6) b67_13.1 b67_13.2.1 b67_13.2.2 = false := by
  decide +kernel

def b67_14 : W × W × List W :=
  (0x1c00380000000000124924, 0x3800000000000001b6db6, [0xffffffffffe3ffffffffffffffe49249, 0xfffffffffffc00070000000000092492, 0x1c000000000001b6db6, 0xe0000000000001b6db6, 0x700000000000001b6db6])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s67_14 : dispatch 1 (optimized 6) b67_14.1 b67_14.2.1 b67_14.2.2 = false := by
  decide +kernel

def b67_15 : W × W × List W :=
  (0x1c000000000001b6db6, 0xe0000000000001b6db6, [0xffffffffffe3ffffffffffffffe49249, 0xfffffffffffc00070000000000092492, 0x1c00380000000000124924, 0x700000000000001b6db6, 0x3800000000000001b6db6])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s67_15 : dispatch 1 (optimized 6) b67_15.1 b67_15.2.1 b67_15.2.2 = false := by
  decide +kernel

def b67_16 : W × W × List W :=
  (0x1c000000000001b6db6, 0x700000000000001b6db6, [0xffffffffffe3ffffffffffffffe49249, 0xfffffffffffc00070000000000092492, 0x1c00380000000000124924, 0xe0000000000001b6db6, 0x3800000000000001b6db6])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s67_16 : dispatch 1 (optimized 6) b67_16.1 b67_16.2.1 b67_16.2.2 = false := by
  decide +kernel

def b67_17 : W × W × List W :=
  (0x1c000000000001b6db6, 0x3800000000000001b6db6, [0xffffffffffe3ffffffffffffffe49249, 0xfffffffffffc00070000000000092492, 0x1c00380000000000124924, 0xe0000000000001b6db6, 0x700000000000001b6db6])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s67_17 : dispatch 1 (optimized 6) b67_17.1 b67_17.2.1 b67_17.2.2 = false := by
  decide +kernel

def b67_18 : W × W × List W :=
  (0xe0000000000001b6db6, 0x700000000000001b6db6, [0xffffffffffe3ffffffffffffffe49249, 0xfffffffffffc00070000000000092492, 0x1c00380000000000124924, 0x1c000000000001b6db6, 0x3800000000000001b6db6])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s67_18 : dispatch 1 (optimized 6) b67_18.1 b67_18.2.1 b67_18.2.2 = false := by
  decide +kernel

def b67_19 : W × W × List W :=
  (0xe0000000000001b6db6, 0x3800000000000001b6db6, [0xffffffffffe3ffffffffffffffe49249, 0xfffffffffffc00070000000000092492, 0x1c00380000000000124924, 0x1c000000000001b6db6, 0x700000000000001b6db6])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s67_19 : dispatch 1 (optimized 6) b67_19.1 b67_19.2.1 b67_19.2.2 = false := by
  decide +kernel

def b67_20 : W × W × List W :=
  (0x700000000000001b6db6, 0x3800000000000001b6db6, [0xffffffffffe3ffffffffffffffe49249, 0xfffffffffffc00070000000000092492, 0x1c00380000000000124924, 0x1c000000000001b6db6, 0xe0000000000001b6db6])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s67_20 : dispatch 1 (optimized 6) b67_20.1 b67_20.2.1 b67_20.2.2 = false := by
  decide +kernel

theorem search67 : optimized 7 1 raw67 = false :=
  split_search 6 1 raw67 [b67_0, b67_1, b67_2, b67_3, b67_4, b67_5, b67_6, b67_7, b67_8, b67_9, b67_10, b67_11, b67_12, b67_13, b67_14, b67_15, b67_16, b67_17, b67_18, b67_19, b67_20]
    (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨s67_0, (List.forall_mem_cons.2 ⟨s67_1, (List.forall_mem_cons.2 ⟨s67_2, (List.forall_mem_cons.2 ⟨s67_3, (List.forall_mem_cons.2 ⟨s67_4, (List.forall_mem_cons.2 ⟨s67_5, (List.forall_mem_cons.2 ⟨s67_6, (List.forall_mem_cons.2 ⟨s67_7, (List.forall_mem_cons.2 ⟨s67_8, (List.forall_mem_cons.2 ⟨s67_9, (List.forall_mem_cons.2 ⟨s67_10, (List.forall_mem_cons.2 ⟨s67_11, (List.forall_mem_cons.2 ⟨s67_12, (List.forall_mem_cons.2 ⟨s67_13, (List.forall_mem_cons.2 ⟨s67_14, (List.forall_mem_cons.2 ⟨s67_15, (List.forall_mem_cons.2 ⟨s67_16, (List.forall_mem_cons.2 ⟨s67_17, (List.forall_mem_cons.2 ⟨s67_18, (List.forall_mem_cons.2 ⟨s67_19, (List.forall_mem_cons.2 ⟨s67_20, (fun _ h => nomatch h)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c67 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2)) x) → 8 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw67 _ 7 1 (by decide +kernel) (by decide +kernel) (by decide)
    (search67) (by decide +kernel) C hm (by omega) he

def raw68 : List W :=
  [0xffffffffffe07fff0000000000092492, 0xffffffffffff8007ffffffffffe49249, 0x380380000000000124924, 0x1c0fffffffffff6db6d, 0xe00fffffffffff6db6d, 0x7000fffffffffff6db6d, 0x1c000000000000001b6db6]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c68 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6)) x) → 8 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw68 _ 7 1 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw69 : List W :=
  [0xfffffff801ffffff0000000108421084, 0xfffffff83e00001ffffffffa5294a529, 0x3e0003e000000004a5294a52, 0x7c0007c00fffffff8c6318c63, 0xf8000fffffffef7bdef7b, 0x1f00000fffffffef7bdef7b, 0x7c00000000000000739ce739c]

def b69_0 : W × W × List W :=
  (0xfffffff801ffffff0000000108421084, 0xfffffff83e00001ffffffffa5294a529, [0x3e0003e000000004a5294a52, 0x7c0007c00fffffff8c6318c63, 0xf8000fffffffef7bdef7b, 0x1f00000fffffffef7bdef7b, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s69_0 : dispatch 2 (optimized 7) b69_0.1 b69_0.2.1 b69_0.2.2 = false := by
  decide +kernel

def b69_1 : W × W × List W :=
  (0xfffffff801ffffff0000000108421084, 0x3e0003e000000004a5294a52, [0xfffffff83e00001ffffffffa5294a529, 0x7c0007c00fffffff8c6318c63, 0xf8000fffffffef7bdef7b, 0x1f00000fffffffef7bdef7b, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s69_1 : dispatch 2 (optimized 7) b69_1.1 b69_1.2.1 b69_1.2.2 = false := by
  decide +kernel

def b69_2 : W × W × List W :=
  (0xfffffff801ffffff0000000108421084, 0x7c0007c00fffffff8c6318c63, [0xfffffff83e00001ffffffffa5294a529, 0x3e0003e000000004a5294a52, 0xf8000fffffffef7bdef7b, 0x1f00000fffffffef7bdef7b, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s69_2 : dispatch 2 (optimized 7) b69_2.1 b69_2.2.1 b69_2.2.2 = false := by
  decide +kernel

def b69_3 : W × W × List W :=
  (0xfffffff801ffffff0000000108421084, 0xf8000fffffffef7bdef7b, [0xfffffff83e00001ffffffffa5294a529, 0x3e0003e000000004a5294a52, 0x7c0007c00fffffff8c6318c63, 0x1f00000fffffffef7bdef7b, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s69_3 : dispatch 2 (optimized 7) b69_3.1 b69_3.2.1 b69_3.2.2 = false := by
  decide +kernel

def b69_4 : W × W × List W :=
  (0xfffffff801ffffff0000000108421084, 0x1f00000fffffffef7bdef7b, [0xfffffff83e00001ffffffffa5294a529, 0x3e0003e000000004a5294a52, 0x7c0007c00fffffff8c6318c63, 0xf8000fffffffef7bdef7b, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s69_4 : dispatch 2 (optimized 7) b69_4.1 b69_4.2.1 b69_4.2.2 = false := by
  decide +kernel

def b69_5 : W × W × List W :=
  (0xfffffff801ffffff0000000108421084, 0x7c00000000000000739ce739c, [0xfffffff83e00001ffffffffa5294a529, 0x3e0003e000000004a5294a52, 0x7c0007c00fffffff8c6318c63, 0xf8000fffffffef7bdef7b, 0x1f00000fffffffef7bdef7b])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s69_5 : dispatch 2 (optimized 7) b69_5.1 b69_5.2.1 b69_5.2.2 = false := by
  decide +kernel

def b69_6 : W × W × List W :=
  (0xfffffff83e00001ffffffffa5294a529, 0x3e0003e000000004a5294a52, [0xfffffff801ffffff0000000108421084, 0x7c0007c00fffffff8c6318c63, 0xf8000fffffffef7bdef7b, 0x1f00000fffffffef7bdef7b, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s69_6 : dispatch 2 (optimized 7) b69_6.1 b69_6.2.1 b69_6.2.2 = false := by
  decide +kernel

def b69_7 : W × W × List W :=
  (0xfffffff83e00001ffffffffa5294a529, 0x7c0007c00fffffff8c6318c63, [0xfffffff801ffffff0000000108421084, 0x3e0003e000000004a5294a52, 0xf8000fffffffef7bdef7b, 0x1f00000fffffffef7bdef7b, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s69_7 : dispatch 2 (optimized 7) b69_7.1 b69_7.2.1 b69_7.2.2 = false := by
  decide +kernel

def b69_8 : W × W × List W :=
  (0xfffffff83e00001ffffffffa5294a529, 0xf8000fffffffef7bdef7b, [0xfffffff801ffffff0000000108421084, 0x3e0003e000000004a5294a52, 0x7c0007c00fffffff8c6318c63, 0x1f00000fffffffef7bdef7b, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s69_8 : dispatch 2 (optimized 7) b69_8.1 b69_8.2.1 b69_8.2.2 = false := by
  decide +kernel

def b69_9 : W × W × List W :=
  (0xfffffff83e00001ffffffffa5294a529, 0x1f00000fffffffef7bdef7b, [0xfffffff801ffffff0000000108421084, 0x3e0003e000000004a5294a52, 0x7c0007c00fffffff8c6318c63, 0xf8000fffffffef7bdef7b, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s69_9 : dispatch 2 (optimized 7) b69_9.1 b69_9.2.1 b69_9.2.2 = false := by
  decide +kernel

def b69_10 : W × W × List W :=
  (0xfffffff83e00001ffffffffa5294a529, 0x7c00000000000000739ce739c, [0xfffffff801ffffff0000000108421084, 0x3e0003e000000004a5294a52, 0x7c0007c00fffffff8c6318c63, 0xf8000fffffffef7bdef7b, 0x1f00000fffffffef7bdef7b])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s69_10 : dispatch 2 (optimized 7) b69_10.1 b69_10.2.1 b69_10.2.2 = false := by
  decide +kernel

def b69_11 : W × W × List W :=
  (0x3e0003e000000004a5294a52, 0x7c0007c00fffffff8c6318c63, [0xfffffff801ffffff0000000108421084, 0xfffffff83e00001ffffffffa5294a529, 0xf8000fffffffef7bdef7b, 0x1f00000fffffffef7bdef7b, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s69_11 : dispatch 2 (optimized 7) b69_11.1 b69_11.2.1 b69_11.2.2 = false := by
  decide +kernel

def b69_12 : W × W × List W :=
  (0x3e0003e000000004a5294a52, 0xf8000fffffffef7bdef7b, [0xfffffff801ffffff0000000108421084, 0xfffffff83e00001ffffffffa5294a529, 0x7c0007c00fffffff8c6318c63, 0x1f00000fffffffef7bdef7b, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s69_12 : dispatch 2 (optimized 7) b69_12.1 b69_12.2.1 b69_12.2.2 = false := by
  decide +kernel

def b69_13 : W × W × List W :=
  (0x3e0003e000000004a5294a52, 0x1f00000fffffffef7bdef7b, [0xfffffff801ffffff0000000108421084, 0xfffffff83e00001ffffffffa5294a529, 0x7c0007c00fffffff8c6318c63, 0xf8000fffffffef7bdef7b, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s69_13 : dispatch 2 (optimized 7) b69_13.1 b69_13.2.1 b69_13.2.2 = false := by
  decide +kernel

def b69_14 : W × W × List W :=
  (0x3e0003e000000004a5294a52, 0x7c00000000000000739ce739c, [0xfffffff801ffffff0000000108421084, 0xfffffff83e00001ffffffffa5294a529, 0x7c0007c00fffffff8c6318c63, 0xf8000fffffffef7bdef7b, 0x1f00000fffffffef7bdef7b])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s69_14 : dispatch 2 (optimized 7) b69_14.1 b69_14.2.1 b69_14.2.2 = false := by
  decide +kernel

def b69_15 : W × W × List W :=
  (0x7c0007c00fffffff8c6318c63, 0xf8000fffffffef7bdef7b, [0xfffffff801ffffff0000000108421084, 0xfffffff83e00001ffffffffa5294a529, 0x3e0003e000000004a5294a52, 0x1f00000fffffffef7bdef7b, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s69_15 : dispatch 2 (optimized 7) b69_15.1 b69_15.2.1 b69_15.2.2 = false := by
  decide +kernel

def b69_16 : W × W × List W :=
  (0x7c0007c00fffffff8c6318c63, 0x1f00000fffffffef7bdef7b, [0xfffffff801ffffff0000000108421084, 0xfffffff83e00001ffffffffa5294a529, 0x3e0003e000000004a5294a52, 0xf8000fffffffef7bdef7b, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s69_16 : dispatch 2 (optimized 7) b69_16.1 b69_16.2.1 b69_16.2.2 = false := by
  decide +kernel

def b69_17 : W × W × List W :=
  (0x7c0007c00fffffff8c6318c63, 0x7c00000000000000739ce739c, [0xfffffff801ffffff0000000108421084, 0xfffffff83e00001ffffffffa5294a529, 0x3e0003e000000004a5294a52, 0xf8000fffffffef7bdef7b, 0x1f00000fffffffef7bdef7b])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s69_17 : dispatch 2 (optimized 7) b69_17.1 b69_17.2.1 b69_17.2.2 = false := by
  decide +kernel

def b69_18 : W × W × List W :=
  (0xf8000fffffffef7bdef7b, 0x1f00000fffffffef7bdef7b, [0xfffffff801ffffff0000000108421084, 0xfffffff83e00001ffffffffa5294a529, 0x3e0003e000000004a5294a52, 0x7c0007c00fffffff8c6318c63, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s69_18 : dispatch 2 (optimized 7) b69_18.1 b69_18.2.1 b69_18.2.2 = false := by
  decide +kernel

def b69_19 : W × W × List W :=
  (0xf8000fffffffef7bdef7b, 0x7c00000000000000739ce739c, [0xfffffff801ffffff0000000108421084, 0xfffffff83e00001ffffffffa5294a529, 0x3e0003e000000004a5294a52, 0x7c0007c00fffffff8c6318c63, 0x1f00000fffffffef7bdef7b])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s69_19 : dispatch 2 (optimized 7) b69_19.1 b69_19.2.1 b69_19.2.2 = false := by
  decide +kernel

def b69_20 : W × W × List W :=
  (0x1f00000fffffffef7bdef7b, 0x7c00000000000000739ce739c, [0xfffffff801ffffff0000000108421084, 0xfffffff83e00001ffffffffa5294a529, 0x3e0003e000000004a5294a52, 0x7c0007c00fffffff8c6318c63, 0xf8000fffffffef7bdef7b])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s69_20 : dispatch 2 (optimized 7) b69_20.1 b69_20.2.1 b69_20.2.2 = false := by
  decide +kernel

theorem search69 : optimized 8 2 raw69 = false :=
  split_search 7 2 raw69 [b69_0, b69_1, b69_2, b69_3, b69_4, b69_5, b69_6, b69_7, b69_8, b69_9, b69_10, b69_11, b69_12, b69_13, b69_14, b69_15, b69_16, b69_17, b69_18, b69_19, b69_20]
    (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨s69_0, (List.forall_mem_cons.2 ⟨s69_1, (List.forall_mem_cons.2 ⟨s69_2, (List.forall_mem_cons.2 ⟨s69_3, (List.forall_mem_cons.2 ⟨s69_4, (List.forall_mem_cons.2 ⟨s69_5, (List.forall_mem_cons.2 ⟨s69_6, (List.forall_mem_cons.2 ⟨s69_7, (List.forall_mem_cons.2 ⟨s69_8, (List.forall_mem_cons.2 ⟨s69_9, (List.forall_mem_cons.2 ⟨s69_10, (List.forall_mem_cons.2 ⟨s69_11, (List.forall_mem_cons.2 ⟨s69_12, (List.forall_mem_cons.2 ⟨s69_13, (List.forall_mem_cons.2 ⟨s69_14, (List.forall_mem_cons.2 ⟨s69_15, (List.forall_mem_cons.2 ⟨s69_16, (List.forall_mem_cons.2 ⟨s69_17, (List.forall_mem_cons.2 ⟨s69_18, (List.forall_mem_cons.2 ⟨s69_19, (List.forall_mem_cons.2 ⟨s69_20, (fun _ h => nomatch h)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c69 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 6)) x) → 9 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw69 _ 8 2 (by decide +kernel) (by decide +kernel) (by decide)
    (search69) (by decide +kernel) C hm (by omega) he

def raw70 : List W :=
  [0xffffffffffe00fff0000000000092492, 0xfffffffffffff007ffffffffffe49249, 0x70380000000000124924, 0x1c0fffffffffff6db6d, 0xe00fffffffffff6db6d, 0x3800000000000001b6db6, 0x1c000000000000001b6db6]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c70 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6)) x) → 8 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw70 _ 7 1 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw71 : List W :=
  [0xfffffffff000ffff0000000004444444, 0xfffffffff0ff000f0000000002222222, 0xf0f00f0fffffffff1111111, 0xf00fffffffffbbbbbbb, 0xf000fffffffffbbbbbbb, 0xf00000fffffffffddddddd, 0xf000000000000000eeeeeee]

def b71_0 : W × W × List W :=
  (0xfffffffff000ffff0000000004444444, 0xfffffffff0ff000f0000000002222222, [0xf0f00f0fffffffff1111111, 0xf00fffffffffbbbbbbb, 0xf000fffffffffbbbbbbb, 0xf00000fffffffffddddddd, 0xf000000000000000eeeeeee])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s71_0 : dispatch 2 (optimized 7) b71_0.1 b71_0.2.1 b71_0.2.2 = false := by
  decide +kernel

def b71_1 : W × W × List W :=
  (0xfffffffff000ffff0000000004444444, 0xf0f00f0fffffffff1111111, [0xfffffffff0ff000f0000000002222222, 0xf00fffffffffbbbbbbb, 0xf000fffffffffbbbbbbb, 0xf00000fffffffffddddddd, 0xf000000000000000eeeeeee])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s71_1 : dispatch 2 (optimized 7) b71_1.1 b71_1.2.1 b71_1.2.2 = false := by
  decide +kernel

def b71_2 : W × W × List W :=
  (0xfffffffff000ffff0000000004444444, 0xf00fffffffffbbbbbbb, [0xfffffffff0ff000f0000000002222222, 0xf0f00f0fffffffff1111111, 0xf000fffffffffbbbbbbb, 0xf00000fffffffffddddddd, 0xf000000000000000eeeeeee])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s71_2 : dispatch 2 (optimized 7) b71_2.1 b71_2.2.1 b71_2.2.2 = false := by
  decide +kernel

def b71_3 : W × W × List W :=
  (0xfffffffff000ffff0000000004444444, 0xf000fffffffffbbbbbbb, [0xfffffffff0ff000f0000000002222222, 0xf0f00f0fffffffff1111111, 0xf00fffffffffbbbbbbb, 0xf00000fffffffffddddddd, 0xf000000000000000eeeeeee])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s71_3 : dispatch 2 (optimized 7) b71_3.1 b71_3.2.1 b71_3.2.2 = false := by
  decide +kernel

def b71_4 : W × W × List W :=
  (0xfffffffff000ffff0000000004444444, 0xf00000fffffffffddddddd, [0xfffffffff0ff000f0000000002222222, 0xf0f00f0fffffffff1111111, 0xf00fffffffffbbbbbbb, 0xf000fffffffffbbbbbbb, 0xf000000000000000eeeeeee])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s71_4 : dispatch 2 (optimized 7) b71_4.1 b71_4.2.1 b71_4.2.2 = false := by
  decide +kernel

def b71_5 : W × W × List W :=
  (0xfffffffff000ffff0000000004444444, 0xf000000000000000eeeeeee, [0xfffffffff0ff000f0000000002222222, 0xf0f00f0fffffffff1111111, 0xf00fffffffffbbbbbbb, 0xf000fffffffffbbbbbbb, 0xf00000fffffffffddddddd])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s71_5 : dispatch 2 (optimized 7) b71_5.1 b71_5.2.1 b71_5.2.2 = false := by
  decide +kernel

def b71_6 : W × W × List W :=
  (0xfffffffff0ff000f0000000002222222, 0xf0f00f0fffffffff1111111, [0xfffffffff000ffff0000000004444444, 0xf00fffffffffbbbbbbb, 0xf000fffffffffbbbbbbb, 0xf00000fffffffffddddddd, 0xf000000000000000eeeeeee])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s71_6 : dispatch 2 (optimized 7) b71_6.1 b71_6.2.1 b71_6.2.2 = false := by
  decide +kernel

def b71_7 : W × W × List W :=
  (0xfffffffff0ff000f0000000002222222, 0xf00fffffffffbbbbbbb, [0xfffffffff000ffff0000000004444444, 0xf0f00f0fffffffff1111111, 0xf000fffffffffbbbbbbb, 0xf00000fffffffffddddddd, 0xf000000000000000eeeeeee])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s71_7 : dispatch 2 (optimized 7) b71_7.1 b71_7.2.1 b71_7.2.2 = false := by
  decide +kernel

def b71_8 : W × W × List W :=
  (0xfffffffff0ff000f0000000002222222, 0xf000fffffffffbbbbbbb, [0xfffffffff000ffff0000000004444444, 0xf0f00f0fffffffff1111111, 0xf00fffffffffbbbbbbb, 0xf00000fffffffffddddddd, 0xf000000000000000eeeeeee])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s71_8 : dispatch 2 (optimized 7) b71_8.1 b71_8.2.1 b71_8.2.2 = false := by
  decide +kernel

def b71_9 : W × W × List W :=
  (0xfffffffff0ff000f0000000002222222, 0xf00000fffffffffddddddd, [0xfffffffff000ffff0000000004444444, 0xf0f00f0fffffffff1111111, 0xf00fffffffffbbbbbbb, 0xf000fffffffffbbbbbbb, 0xf000000000000000eeeeeee])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s71_9 : dispatch 2 (optimized 7) b71_9.1 b71_9.2.1 b71_9.2.2 = false := by
  decide +kernel

def b71_10 : W × W × List W :=
  (0xfffffffff0ff000f0000000002222222, 0xf000000000000000eeeeeee, [0xfffffffff000ffff0000000004444444, 0xf0f00f0fffffffff1111111, 0xf00fffffffffbbbbbbb, 0xf000fffffffffbbbbbbb, 0xf00000fffffffffddddddd])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s71_10 : dispatch 2 (optimized 7) b71_10.1 b71_10.2.1 b71_10.2.2 = false := by
  decide +kernel

def b71_11 : W × W × List W :=
  (0xf0f00f0fffffffff1111111, 0xf00fffffffffbbbbbbb, [0xfffffffff000ffff0000000004444444, 0xfffffffff0ff000f0000000002222222, 0xf000fffffffffbbbbbbb, 0xf00000fffffffffddddddd, 0xf000000000000000eeeeeee])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s71_11 : dispatch 2 (optimized 7) b71_11.1 b71_11.2.1 b71_11.2.2 = false := by
  decide +kernel

def b71_12 : W × W × List W :=
  (0xf0f00f0fffffffff1111111, 0xf000fffffffffbbbbbbb, [0xfffffffff000ffff0000000004444444, 0xfffffffff0ff000f0000000002222222, 0xf00fffffffffbbbbbbb, 0xf00000fffffffffddddddd, 0xf000000000000000eeeeeee])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s71_12 : dispatch 2 (optimized 7) b71_12.1 b71_12.2.1 b71_12.2.2 = false := by
  decide +kernel

def b71_13 : W × W × List W :=
  (0xf0f00f0fffffffff1111111, 0xf00000fffffffffddddddd, [0xfffffffff000ffff0000000004444444, 0xfffffffff0ff000f0000000002222222, 0xf00fffffffffbbbbbbb, 0xf000fffffffffbbbbbbb, 0xf000000000000000eeeeeee])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s71_13 : dispatch 2 (optimized 7) b71_13.1 b71_13.2.1 b71_13.2.2 = false := by
  decide +kernel

def b71_14 : W × W × List W :=
  (0xf0f00f0fffffffff1111111, 0xf000000000000000eeeeeee, [0xfffffffff000ffff0000000004444444, 0xfffffffff0ff000f0000000002222222, 0xf00fffffffffbbbbbbb, 0xf000fffffffffbbbbbbb, 0xf00000fffffffffddddddd])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s71_14 : dispatch 2 (optimized 7) b71_14.1 b71_14.2.1 b71_14.2.2 = false := by
  decide +kernel

def b71_15 : W × W × List W :=
  (0xf00fffffffffbbbbbbb, 0xf000fffffffffbbbbbbb, [0xfffffffff000ffff0000000004444444, 0xfffffffff0ff000f0000000002222222, 0xf0f00f0fffffffff1111111, 0xf00000fffffffffddddddd, 0xf000000000000000eeeeeee])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s71_15 : dispatch 2 (optimized 7) b71_15.1 b71_15.2.1 b71_15.2.2 = false := by
  decide +kernel

def b71_16 : W × W × List W :=
  (0xf00fffffffffbbbbbbb, 0xf00000fffffffffddddddd, [0xfffffffff000ffff0000000004444444, 0xfffffffff0ff000f0000000002222222, 0xf0f00f0fffffffff1111111, 0xf000fffffffffbbbbbbb, 0xf000000000000000eeeeeee])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s71_16 : dispatch 2 (optimized 7) b71_16.1 b71_16.2.1 b71_16.2.2 = false := by
  decide +kernel

def b71_17 : W × W × List W :=
  (0xf00fffffffffbbbbbbb, 0xf000000000000000eeeeeee, [0xfffffffff000ffff0000000004444444, 0xfffffffff0ff000f0000000002222222, 0xf0f00f0fffffffff1111111, 0xf000fffffffffbbbbbbb, 0xf00000fffffffffddddddd])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s71_17 : dispatch 2 (optimized 7) b71_17.1 b71_17.2.1 b71_17.2.2 = false := by
  decide +kernel

def b71_18 : W × W × List W :=
  (0xf000fffffffffbbbbbbb, 0xf00000fffffffffddddddd, [0xfffffffff000ffff0000000004444444, 0xfffffffff0ff000f0000000002222222, 0xf0f00f0fffffffff1111111, 0xf00fffffffffbbbbbbb, 0xf000000000000000eeeeeee])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s71_18 : dispatch 2 (optimized 7) b71_18.1 b71_18.2.1 b71_18.2.2 = false := by
  decide +kernel

def b71_19 : W × W × List W :=
  (0xf000fffffffffbbbbbbb, 0xf000000000000000eeeeeee, [0xfffffffff000ffff0000000004444444, 0xfffffffff0ff000f0000000002222222, 0xf0f00f0fffffffff1111111, 0xf00fffffffffbbbbbbb, 0xf00000fffffffffddddddd])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s71_19 : dispatch 2 (optimized 7) b71_19.1 b71_19.2.1 b71_19.2.2 = false := by
  decide +kernel

def b71_20 : W × W × List W :=
  (0xf00000fffffffffddddddd, 0xf000000000000000eeeeeee, [0xfffffffff000ffff0000000004444444, 0xfffffffff0ff000f0000000002222222, 0xf0f00f0fffffffff1111111, 0xf00fffffffffbbbbbbb, 0xf000fffffffffbbbbbbb])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s71_20 : dispatch 2 (optimized 7) b71_20.1 b71_20.2.1 b71_20.2.2 = false := by
  decide +kernel

theorem search71 : optimized 8 2 raw71 = false :=
  split_search 7 2 raw71 [b71_0, b71_1, b71_2, b71_3, b71_4, b71_5, b71_6, b71_7, b71_8, b71_9, b71_10, b71_11, b71_12, b71_13, b71_14, b71_15, b71_16, b71_17, b71_18, b71_19, b71_20]
    (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨s71_0, (List.forall_mem_cons.2 ⟨s71_1, (List.forall_mem_cons.2 ⟨s71_2, (List.forall_mem_cons.2 ⟨s71_3, (List.forall_mem_cons.2 ⟨s71_4, (List.forall_mem_cons.2 ⟨s71_5, (List.forall_mem_cons.2 ⟨s71_6, (List.forall_mem_cons.2 ⟨s71_7, (List.forall_mem_cons.2 ⟨s71_8, (List.forall_mem_cons.2 ⟨s71_9, (List.forall_mem_cons.2 ⟨s71_10, (List.forall_mem_cons.2 ⟨s71_11, (List.forall_mem_cons.2 ⟨s71_12, (List.forall_mem_cons.2 ⟨s71_13, (List.forall_mem_cons.2 ⟨s71_14, (List.forall_mem_cons.2 ⟨s71_15, (List.forall_mem_cons.2 ⟨s71_16, (List.forall_mem_cons.2 ⟨s71_17, (List.forall_mem_cons.2 ⟨s71_18, (List.forall_mem_cons.2 ⟨s71_19, (List.forall_mem_cons.2 ⟨s71_20, (fun _ h => nomatch h)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c71 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6)) x) → 9 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw71 _ 8 2 (by decide +kernel) (by decide +kernel) (by decide)
    (search71) (by decide +kernel) C hm (by omega) he

def raw72 : List W :=
  [0xfffffff8000fffff0000000210842108, 0xfffffff83ff0001ffffffff94a5294a5, 0x1f003e000000004a5294a52, 0x7c0007c00fffffff8c6318c63, 0xf8000fffffffdef7bdef7, 0x3e00000000000006b5ad6b5a, 0x7c00000000000000739ce739c]

def b72_0 : W × W × List W :=
  (0xfffffff8000fffff0000000210842108, 0xfffffff83ff0001ffffffff94a5294a5, [0x1f003e000000004a5294a52, 0x7c0007c00fffffff8c6318c63, 0xf8000fffffffdef7bdef7, 0x3e00000000000006b5ad6b5a, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s72_0 : dispatch 2 (optimized 7) b72_0.1 b72_0.2.1 b72_0.2.2 = false := by
  decide +kernel

def b72_1 : W × W × List W :=
  (0xfffffff8000fffff0000000210842108, 0x1f003e000000004a5294a52, [0xfffffff83ff0001ffffffff94a5294a5, 0x7c0007c00fffffff8c6318c63, 0xf8000fffffffdef7bdef7, 0x3e00000000000006b5ad6b5a, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s72_1 : dispatch 2 (optimized 7) b72_1.1 b72_1.2.1 b72_1.2.2 = false := by
  decide +kernel

def b72_2 : W × W × List W :=
  (0xfffffff8000fffff0000000210842108, 0x7c0007c00fffffff8c6318c63, [0xfffffff83ff0001ffffffff94a5294a5, 0x1f003e000000004a5294a52, 0xf8000fffffffdef7bdef7, 0x3e00000000000006b5ad6b5a, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s72_2 : dispatch 2 (optimized 7) b72_2.1 b72_2.2.1 b72_2.2.2 = false := by
  decide +kernel

def b72_3 : W × W × List W :=
  (0xfffffff8000fffff0000000210842108, 0xf8000fffffffdef7bdef7, [0xfffffff83ff0001ffffffff94a5294a5, 0x1f003e000000004a5294a52, 0x7c0007c00fffffff8c6318c63, 0x3e00000000000006b5ad6b5a, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s72_3 : dispatch 2 (optimized 7) b72_3.1 b72_3.2.1 b72_3.2.2 = false := by
  decide +kernel

def b72_4 : W × W × List W :=
  (0xfffffff8000fffff0000000210842108, 0x3e00000000000006b5ad6b5a, [0xfffffff83ff0001ffffffff94a5294a5, 0x1f003e000000004a5294a52, 0x7c0007c00fffffff8c6318c63, 0xf8000fffffffdef7bdef7, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s72_4 : dispatch 2 (optimized 7) b72_4.1 b72_4.2.1 b72_4.2.2 = false := by
  decide +kernel

def b72_5 : W × W × List W :=
  (0xfffffff8000fffff0000000210842108, 0x7c00000000000000739ce739c, [0xfffffff83ff0001ffffffff94a5294a5, 0x1f003e000000004a5294a52, 0x7c0007c00fffffff8c6318c63, 0xf8000fffffffdef7bdef7, 0x3e00000000000006b5ad6b5a])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s72_5 : dispatch 2 (optimized 7) b72_5.1 b72_5.2.1 b72_5.2.2 = false := by
  decide +kernel

def b72_6 : W × W × List W :=
  (0xfffffff83ff0001ffffffff94a5294a5, 0x1f003e000000004a5294a52, [0xfffffff8000fffff0000000210842108, 0x7c0007c00fffffff8c6318c63, 0xf8000fffffffdef7bdef7, 0x3e00000000000006b5ad6b5a, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s72_6 : dispatch 2 (optimized 7) b72_6.1 b72_6.2.1 b72_6.2.2 = false := by
  decide +kernel

def b72_7 : W × W × List W :=
  (0xfffffff83ff0001ffffffff94a5294a5, 0x7c0007c00fffffff8c6318c63, [0xfffffff8000fffff0000000210842108, 0x1f003e000000004a5294a52, 0xf8000fffffffdef7bdef7, 0x3e00000000000006b5ad6b5a, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s72_7 : dispatch 2 (optimized 7) b72_7.1 b72_7.2.1 b72_7.2.2 = false := by
  decide +kernel

def b72_8 : W × W × List W :=
  (0xfffffff83ff0001ffffffff94a5294a5, 0xf8000fffffffdef7bdef7, [0xfffffff8000fffff0000000210842108, 0x1f003e000000004a5294a52, 0x7c0007c00fffffff8c6318c63, 0x3e00000000000006b5ad6b5a, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s72_8 : dispatch 2 (optimized 7) b72_8.1 b72_8.2.1 b72_8.2.2 = false := by
  decide +kernel

def b72_9 : W × W × List W :=
  (0xfffffff83ff0001ffffffff94a5294a5, 0x3e00000000000006b5ad6b5a, [0xfffffff8000fffff0000000210842108, 0x1f003e000000004a5294a52, 0x7c0007c00fffffff8c6318c63, 0xf8000fffffffdef7bdef7, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s72_9 : dispatch 2 (optimized 7) b72_9.1 b72_9.2.1 b72_9.2.2 = false := by
  decide +kernel

def b72_10 : W × W × List W :=
  (0xfffffff83ff0001ffffffff94a5294a5, 0x7c00000000000000739ce739c, [0xfffffff8000fffff0000000210842108, 0x1f003e000000004a5294a52, 0x7c0007c00fffffff8c6318c63, 0xf8000fffffffdef7bdef7, 0x3e00000000000006b5ad6b5a])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s72_10 : dispatch 2 (optimized 7) b72_10.1 b72_10.2.1 b72_10.2.2 = false := by
  decide +kernel

def b72_11 : W × W × List W :=
  (0x1f003e000000004a5294a52, 0x7c0007c00fffffff8c6318c63, [0xfffffff8000fffff0000000210842108, 0xfffffff83ff0001ffffffff94a5294a5, 0xf8000fffffffdef7bdef7, 0x3e00000000000006b5ad6b5a, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s72_11 : dispatch 2 (optimized 7) b72_11.1 b72_11.2.1 b72_11.2.2 = false := by
  decide +kernel

def b72_12 : W × W × List W :=
  (0x1f003e000000004a5294a52, 0xf8000fffffffdef7bdef7, [0xfffffff8000fffff0000000210842108, 0xfffffff83ff0001ffffffff94a5294a5, 0x7c0007c00fffffff8c6318c63, 0x3e00000000000006b5ad6b5a, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s72_12 : dispatch 2 (optimized 7) b72_12.1 b72_12.2.1 b72_12.2.2 = false := by
  decide +kernel

def b72_13 : W × W × List W :=
  (0x1f003e000000004a5294a52, 0x3e00000000000006b5ad6b5a, [0xfffffff8000fffff0000000210842108, 0xfffffff83ff0001ffffffff94a5294a5, 0x7c0007c00fffffff8c6318c63, 0xf8000fffffffdef7bdef7, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s72_13 : dispatch 2 (optimized 7) b72_13.1 b72_13.2.1 b72_13.2.2 = false := by
  decide +kernel

def b72_14 : W × W × List W :=
  (0x1f003e000000004a5294a52, 0x7c00000000000000739ce739c, [0xfffffff8000fffff0000000210842108, 0xfffffff83ff0001ffffffff94a5294a5, 0x7c0007c00fffffff8c6318c63, 0xf8000fffffffdef7bdef7, 0x3e00000000000006b5ad6b5a])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s72_14 : dispatch 2 (optimized 7) b72_14.1 b72_14.2.1 b72_14.2.2 = false := by
  decide +kernel

def b72_15 : W × W × List W :=
  (0x7c0007c00fffffff8c6318c63, 0xf8000fffffffdef7bdef7, [0xfffffff8000fffff0000000210842108, 0xfffffff83ff0001ffffffff94a5294a5, 0x1f003e000000004a5294a52, 0x3e00000000000006b5ad6b5a, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s72_15 : dispatch 2 (optimized 7) b72_15.1 b72_15.2.1 b72_15.2.2 = false := by
  decide +kernel

def b72_16 : W × W × List W :=
  (0x7c0007c00fffffff8c6318c63, 0x3e00000000000006b5ad6b5a, [0xfffffff8000fffff0000000210842108, 0xfffffff83ff0001ffffffff94a5294a5, 0x1f003e000000004a5294a52, 0xf8000fffffffdef7bdef7, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s72_16 : dispatch 2 (optimized 7) b72_16.1 b72_16.2.1 b72_16.2.2 = false := by
  decide +kernel

def b72_17 : W × W × List W :=
  (0x7c0007c00fffffff8c6318c63, 0x7c00000000000000739ce739c, [0xfffffff8000fffff0000000210842108, 0xfffffff83ff0001ffffffff94a5294a5, 0x1f003e000000004a5294a52, 0xf8000fffffffdef7bdef7, 0x3e00000000000006b5ad6b5a])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s72_17 : dispatch 2 (optimized 7) b72_17.1 b72_17.2.1 b72_17.2.2 = false := by
  decide +kernel

def b72_18 : W × W × List W :=
  (0xf8000fffffffdef7bdef7, 0x3e00000000000006b5ad6b5a, [0xfffffff8000fffff0000000210842108, 0xfffffff83ff0001ffffffff94a5294a5, 0x1f003e000000004a5294a52, 0x7c0007c00fffffff8c6318c63, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s72_18 : dispatch 2 (optimized 7) b72_18.1 b72_18.2.1 b72_18.2.2 = false := by
  decide +kernel

def b72_19 : W × W × List W :=
  (0xf8000fffffffdef7bdef7, 0x7c00000000000000739ce739c, [0xfffffff8000fffff0000000210842108, 0xfffffff83ff0001ffffffff94a5294a5, 0x1f003e000000004a5294a52, 0x7c0007c00fffffff8c6318c63, 0x3e00000000000006b5ad6b5a])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s72_19 : dispatch 2 (optimized 7) b72_19.1 b72_19.2.1 b72_19.2.2 = false := by
  decide +kernel

def b72_20 : W × W × List W :=
  (0x3e00000000000006b5ad6b5a, 0x7c00000000000000739ce739c, [0xfffffff8000fffff0000000210842108, 0xfffffff83ff0001ffffffff94a5294a5, 0x1f003e000000004a5294a52, 0x7c0007c00fffffff8c6318c63, 0xf8000fffffffdef7bdef7])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s72_20 : dispatch 2 (optimized 7) b72_20.1 b72_20.2.1 b72_20.2.2 = false := by
  decide +kernel

theorem search72 : optimized 8 2 raw72 = false :=
  split_search 7 2 raw72 [b72_0, b72_1, b72_2, b72_3, b72_4, b72_5, b72_6, b72_7, b72_8, b72_9, b72_10, b72_11, b72_12, b72_13, b72_14, b72_15, b72_16, b72_17, b72_18, b72_19, b72_20]
    (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨s72_0, (List.forall_mem_cons.2 ⟨s72_1, (List.forall_mem_cons.2 ⟨s72_2, (List.forall_mem_cons.2 ⟨s72_3, (List.forall_mem_cons.2 ⟨s72_4, (List.forall_mem_cons.2 ⟨s72_5, (List.forall_mem_cons.2 ⟨s72_6, (List.forall_mem_cons.2 ⟨s72_7, (List.forall_mem_cons.2 ⟨s72_8, (List.forall_mem_cons.2 ⟨s72_9, (List.forall_mem_cons.2 ⟨s72_10, (List.forall_mem_cons.2 ⟨s72_11, (List.forall_mem_cons.2 ⟨s72_12, (List.forall_mem_cons.2 ⟨s72_13, (List.forall_mem_cons.2 ⟨s72_14, (List.forall_mem_cons.2 ⟨s72_15, (List.forall_mem_cons.2 ⟨s72_16, (List.forall_mem_cons.2 ⟨s72_17, (List.forall_mem_cons.2 ⟨s72_18, (List.forall_mem_cons.2 ⟨s72_19, (List.forall_mem_cons.2 ⟨s72_20, (fun _ h => nomatch h)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c72 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6)) x) → 9 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw72 _ 8 2 (by decide +kernel) (by decide +kernel) (by decide)
    (search72) (by decide +kernel) C hm (by omega) he

def raw73 : List W :=
  [0xfffffff8000ffffffffffff94a5294a5, 0xfffffff83ff0001f0000000210842108, 0x1f003e000000004a5294a52, 0x7c0000000006b5ad6b5a, 0xf800000000006b5ad6b5a, 0x7fe000000fffffff8c6318c63, 0x7c00000000000000739ce739c]

def b73_0 : W × W × List W :=
  (0xfffffff8000ffffffffffff94a5294a5, 0xfffffff83ff0001f0000000210842108, [0x1f003e000000004a5294a52, 0x7c0000000006b5ad6b5a, 0xf800000000006b5ad6b5a, 0x7fe000000fffffff8c6318c63, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s73_0 : dispatch 2 (optimized 7) b73_0.1 b73_0.2.1 b73_0.2.2 = false := by
  decide +kernel

def b73_1 : W × W × List W :=
  (0xfffffff8000ffffffffffff94a5294a5, 0x1f003e000000004a5294a52, [0xfffffff83ff0001f0000000210842108, 0x7c0000000006b5ad6b5a, 0xf800000000006b5ad6b5a, 0x7fe000000fffffff8c6318c63, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s73_1 : dispatch 2 (optimized 7) b73_1.1 b73_1.2.1 b73_1.2.2 = false := by
  decide +kernel

def b73_2 : W × W × List W :=
  (0xfffffff8000ffffffffffff94a5294a5, 0x7c0000000006b5ad6b5a, [0xfffffff83ff0001f0000000210842108, 0x1f003e000000004a5294a52, 0xf800000000006b5ad6b5a, 0x7fe000000fffffff8c6318c63, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s73_2 : dispatch 2 (optimized 7) b73_2.1 b73_2.2.1 b73_2.2.2 = false := by
  decide +kernel

def b73_3 : W × W × List W :=
  (0xfffffff8000ffffffffffff94a5294a5, 0xf800000000006b5ad6b5a, [0xfffffff83ff0001f0000000210842108, 0x1f003e000000004a5294a52, 0x7c0000000006b5ad6b5a, 0x7fe000000fffffff8c6318c63, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s73_3 : dispatch 2 (optimized 7) b73_3.1 b73_3.2.1 b73_3.2.2 = false := by
  decide +kernel

def b73_4 : W × W × List W :=
  (0xfffffff8000ffffffffffff94a5294a5, 0x7fe000000fffffff8c6318c63, [0xfffffff83ff0001f0000000210842108, 0x1f003e000000004a5294a52, 0x7c0000000006b5ad6b5a, 0xf800000000006b5ad6b5a, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s73_4 : dispatch 2 (optimized 7) b73_4.1 b73_4.2.1 b73_4.2.2 = false := by
  decide +kernel

def b73_5 : W × W × List W :=
  (0xfffffff8000ffffffffffff94a5294a5, 0x7c00000000000000739ce739c, [0xfffffff83ff0001f0000000210842108, 0x1f003e000000004a5294a52, 0x7c0000000006b5ad6b5a, 0xf800000000006b5ad6b5a, 0x7fe000000fffffff8c6318c63])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s73_5 : dispatch 2 (optimized 7) b73_5.1 b73_5.2.1 b73_5.2.2 = false := by
  decide +kernel

def b73_6 : W × W × List W :=
  (0xfffffff83ff0001f0000000210842108, 0x1f003e000000004a5294a52, [0xfffffff8000ffffffffffff94a5294a5, 0x7c0000000006b5ad6b5a, 0xf800000000006b5ad6b5a, 0x7fe000000fffffff8c6318c63, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s73_6 : dispatch 2 (optimized 7) b73_6.1 b73_6.2.1 b73_6.2.2 = false := by
  decide +kernel

def b73_7 : W × W × List W :=
  (0xfffffff83ff0001f0000000210842108, 0x7c0000000006b5ad6b5a, [0xfffffff8000ffffffffffff94a5294a5, 0x1f003e000000004a5294a52, 0xf800000000006b5ad6b5a, 0x7fe000000fffffff8c6318c63, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s73_7 : dispatch 2 (optimized 7) b73_7.1 b73_7.2.1 b73_7.2.2 = false := by
  decide +kernel

def b73_8 : W × W × List W :=
  (0xfffffff83ff0001f0000000210842108, 0xf800000000006b5ad6b5a, [0xfffffff8000ffffffffffff94a5294a5, 0x1f003e000000004a5294a52, 0x7c0000000006b5ad6b5a, 0x7fe000000fffffff8c6318c63, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s73_8 : dispatch 2 (optimized 7) b73_8.1 b73_8.2.1 b73_8.2.2 = false := by
  decide +kernel

def b73_9 : W × W × List W :=
  (0xfffffff83ff0001f0000000210842108, 0x7fe000000fffffff8c6318c63, [0xfffffff8000ffffffffffff94a5294a5, 0x1f003e000000004a5294a52, 0x7c0000000006b5ad6b5a, 0xf800000000006b5ad6b5a, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s73_9 : dispatch 2 (optimized 7) b73_9.1 b73_9.2.1 b73_9.2.2 = false := by
  decide +kernel

def b73_10 : W × W × List W :=
  (0xfffffff83ff0001f0000000210842108, 0x7c00000000000000739ce739c, [0xfffffff8000ffffffffffff94a5294a5, 0x1f003e000000004a5294a52, 0x7c0000000006b5ad6b5a, 0xf800000000006b5ad6b5a, 0x7fe000000fffffff8c6318c63])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s73_10 : dispatch 2 (optimized 7) b73_10.1 b73_10.2.1 b73_10.2.2 = false := by
  decide +kernel

def b73_11 : W × W × List W :=
  (0x1f003e000000004a5294a52, 0x7c0000000006b5ad6b5a, [0xfffffff8000ffffffffffff94a5294a5, 0xfffffff83ff0001f0000000210842108, 0xf800000000006b5ad6b5a, 0x7fe000000fffffff8c6318c63, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s73_11 : dispatch 2 (optimized 7) b73_11.1 b73_11.2.1 b73_11.2.2 = false := by
  decide +kernel

def b73_12 : W × W × List W :=
  (0x1f003e000000004a5294a52, 0xf800000000006b5ad6b5a, [0xfffffff8000ffffffffffff94a5294a5, 0xfffffff83ff0001f0000000210842108, 0x7c0000000006b5ad6b5a, 0x7fe000000fffffff8c6318c63, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s73_12 : dispatch 2 (optimized 7) b73_12.1 b73_12.2.1 b73_12.2.2 = false := by
  decide +kernel

def b73_13 : W × W × List W :=
  (0x1f003e000000004a5294a52, 0x7fe000000fffffff8c6318c63, [0xfffffff8000ffffffffffff94a5294a5, 0xfffffff83ff0001f0000000210842108, 0x7c0000000006b5ad6b5a, 0xf800000000006b5ad6b5a, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s73_13 : dispatch 2 (optimized 7) b73_13.1 b73_13.2.1 b73_13.2.2 = false := by
  decide +kernel

def b73_14 : W × W × List W :=
  (0x1f003e000000004a5294a52, 0x7c00000000000000739ce739c, [0xfffffff8000ffffffffffff94a5294a5, 0xfffffff83ff0001f0000000210842108, 0x7c0000000006b5ad6b5a, 0xf800000000006b5ad6b5a, 0x7fe000000fffffff8c6318c63])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s73_14 : dispatch 2 (optimized 7) b73_14.1 b73_14.2.1 b73_14.2.2 = false := by
  decide +kernel

def b73_15 : W × W × List W :=
  (0x7c0000000006b5ad6b5a, 0xf800000000006b5ad6b5a, [0xfffffff8000ffffffffffff94a5294a5, 0xfffffff83ff0001f0000000210842108, 0x1f003e000000004a5294a52, 0x7fe000000fffffff8c6318c63, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s73_15 : dispatch 2 (optimized 7) b73_15.1 b73_15.2.1 b73_15.2.2 = false := by
  decide +kernel

def b73_16 : W × W × List W :=
  (0x7c0000000006b5ad6b5a, 0x7fe000000fffffff8c6318c63, [0xfffffff8000ffffffffffff94a5294a5, 0xfffffff83ff0001f0000000210842108, 0x1f003e000000004a5294a52, 0xf800000000006b5ad6b5a, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s73_16 : dispatch 2 (optimized 7) b73_16.1 b73_16.2.1 b73_16.2.2 = false := by
  decide +kernel

def b73_17 : W × W × List W :=
  (0x7c0000000006b5ad6b5a, 0x7c00000000000000739ce739c, [0xfffffff8000ffffffffffff94a5294a5, 0xfffffff83ff0001f0000000210842108, 0x1f003e000000004a5294a52, 0xf800000000006b5ad6b5a, 0x7fe000000fffffff8c6318c63])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s73_17 : dispatch 2 (optimized 7) b73_17.1 b73_17.2.1 b73_17.2.2 = false := by
  decide +kernel

def b73_18 : W × W × List W :=
  (0xf800000000006b5ad6b5a, 0x7fe000000fffffff8c6318c63, [0xfffffff8000ffffffffffff94a5294a5, 0xfffffff83ff0001f0000000210842108, 0x1f003e000000004a5294a52, 0x7c0000000006b5ad6b5a, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s73_18 : dispatch 2 (optimized 7) b73_18.1 b73_18.2.1 b73_18.2.2 = false := by
  decide +kernel

def b73_19 : W × W × List W :=
  (0xf800000000006b5ad6b5a, 0x7c00000000000000739ce739c, [0xfffffff8000ffffffffffff94a5294a5, 0xfffffff83ff0001f0000000210842108, 0x1f003e000000004a5294a52, 0x7c0000000006b5ad6b5a, 0x7fe000000fffffff8c6318c63])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s73_19 : dispatch 2 (optimized 7) b73_19.1 b73_19.2.1 b73_19.2.2 = false := by
  decide +kernel

def b73_20 : W × W × List W :=
  (0x7fe000000fffffff8c6318c63, 0x7c00000000000000739ce739c, [0xfffffff8000ffffffffffff94a5294a5, 0xfffffff83ff0001f0000000210842108, 0x1f003e000000004a5294a52, 0x7c0000000006b5ad6b5a, 0xf800000000006b5ad6b5a])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s73_20 : dispatch 2 (optimized 7) b73_20.1 b73_20.2.1 b73_20.2.2 = false := by
  decide +kernel

theorem search73 : optimized 8 2 raw73 = false :=
  split_search 7 2 raw73 [b73_0, b73_1, b73_2, b73_3, b73_4, b73_5, b73_6, b73_7, b73_8, b73_9, b73_10, b73_11, b73_12, b73_13, b73_14, b73_15, b73_16, b73_17, b73_18, b73_19, b73_20]
    (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨s73_0, (List.forall_mem_cons.2 ⟨s73_1, (List.forall_mem_cons.2 ⟨s73_2, (List.forall_mem_cons.2 ⟨s73_3, (List.forall_mem_cons.2 ⟨s73_4, (List.forall_mem_cons.2 ⟨s73_5, (List.forall_mem_cons.2 ⟨s73_6, (List.forall_mem_cons.2 ⟨s73_7, (List.forall_mem_cons.2 ⟨s73_8, (List.forall_mem_cons.2 ⟨s73_9, (List.forall_mem_cons.2 ⟨s73_10, (List.forall_mem_cons.2 ⟨s73_11, (List.forall_mem_cons.2 ⟨s73_12, (List.forall_mem_cons.2 ⟨s73_13, (List.forall_mem_cons.2 ⟨s73_14, (List.forall_mem_cons.2 ⟨s73_15, (List.forall_mem_cons.2 ⟨s73_16, (List.forall_mem_cons.2 ⟨s73_17, (List.forall_mem_cons.2 ⟨s73_18, (List.forall_mem_cons.2 ⟨s73_19, (List.forall_mem_cons.2 ⟨s73_20, (fun _ h => nomatch h)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c73 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 5 && x 6)) x) → 9 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw73 _ 8 2 (by decide +kernel) (by decide +kernel) (by decide)
    (search73) (by decide +kernel) C hm (by omega) he

def raw74 : List W :=
  [0xfffffff8000fffff0000000108421084, 0xfffffff801f0001ffffffffa5294a529, 0x1f003e000000004a5294a52, 0x7fe007c00fffffff8c6318c63, 0xf8000fffffffef7bdef7b, 0x3e0000000000000739ce739c, 0x7c00000000000000739ce739c]

def b74_0 : W × W × List W :=
  (0xfffffff8000fffff0000000108421084, 0xfffffff801f0001ffffffffa5294a529, [0x1f003e000000004a5294a52, 0x7fe007c00fffffff8c6318c63, 0xf8000fffffffef7bdef7b, 0x3e0000000000000739ce739c, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s74_0 : dispatch 2 (optimized 7) b74_0.1 b74_0.2.1 b74_0.2.2 = false := by
  decide +kernel

def b74_1 : W × W × List W :=
  (0xfffffff8000fffff0000000108421084, 0x1f003e000000004a5294a52, [0xfffffff801f0001ffffffffa5294a529, 0x7fe007c00fffffff8c6318c63, 0xf8000fffffffef7bdef7b, 0x3e0000000000000739ce739c, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s74_1 : dispatch 2 (optimized 7) b74_1.1 b74_1.2.1 b74_1.2.2 = false := by
  decide +kernel

def b74_2 : W × W × List W :=
  (0xfffffff8000fffff0000000108421084, 0x7fe007c00fffffff8c6318c63, [0xfffffff801f0001ffffffffa5294a529, 0x1f003e000000004a5294a52, 0xf8000fffffffef7bdef7b, 0x3e0000000000000739ce739c, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s74_2 : dispatch 2 (optimized 7) b74_2.1 b74_2.2.1 b74_2.2.2 = false := by
  decide +kernel

def b74_3 : W × W × List W :=
  (0xfffffff8000fffff0000000108421084, 0xf8000fffffffef7bdef7b, [0xfffffff801f0001ffffffffa5294a529, 0x1f003e000000004a5294a52, 0x7fe007c00fffffff8c6318c63, 0x3e0000000000000739ce739c, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s74_3 : dispatch 2 (optimized 7) b74_3.1 b74_3.2.1 b74_3.2.2 = false := by
  decide +kernel

def b74_4 : W × W × List W :=
  (0xfffffff8000fffff0000000108421084, 0x3e0000000000000739ce739c, [0xfffffff801f0001ffffffffa5294a529, 0x1f003e000000004a5294a52, 0x7fe007c00fffffff8c6318c63, 0xf8000fffffffef7bdef7b, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s74_4 : dispatch 2 (optimized 7) b74_4.1 b74_4.2.1 b74_4.2.2 = false := by
  decide +kernel

def b74_5 : W × W × List W :=
  (0xfffffff8000fffff0000000108421084, 0x7c00000000000000739ce739c, [0xfffffff801f0001ffffffffa5294a529, 0x1f003e000000004a5294a52, 0x7fe007c00fffffff8c6318c63, 0xf8000fffffffef7bdef7b, 0x3e0000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s74_5 : dispatch 2 (optimized 7) b74_5.1 b74_5.2.1 b74_5.2.2 = false := by
  decide +kernel

def b74_6 : W × W × List W :=
  (0xfffffff801f0001ffffffffa5294a529, 0x1f003e000000004a5294a52, [0xfffffff8000fffff0000000108421084, 0x7fe007c00fffffff8c6318c63, 0xf8000fffffffef7bdef7b, 0x3e0000000000000739ce739c, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s74_6 : dispatch 2 (optimized 7) b74_6.1 b74_6.2.1 b74_6.2.2 = false := by
  decide +kernel

def b74_7 : W × W × List W :=
  (0xfffffff801f0001ffffffffa5294a529, 0x7fe007c00fffffff8c6318c63, [0xfffffff8000fffff0000000108421084, 0x1f003e000000004a5294a52, 0xf8000fffffffef7bdef7b, 0x3e0000000000000739ce739c, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s74_7 : dispatch 2 (optimized 7) b74_7.1 b74_7.2.1 b74_7.2.2 = false := by
  decide +kernel

def b74_8 : W × W × List W :=
  (0xfffffff801f0001ffffffffa5294a529, 0xf8000fffffffef7bdef7b, [0xfffffff8000fffff0000000108421084, 0x1f003e000000004a5294a52, 0x7fe007c00fffffff8c6318c63, 0x3e0000000000000739ce739c, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s74_8 : dispatch 2 (optimized 7) b74_8.1 b74_8.2.1 b74_8.2.2 = false := by
  decide +kernel

def b74_9 : W × W × List W :=
  (0xfffffff801f0001ffffffffa5294a529, 0x3e0000000000000739ce739c, [0xfffffff8000fffff0000000108421084, 0x1f003e000000004a5294a52, 0x7fe007c00fffffff8c6318c63, 0xf8000fffffffef7bdef7b, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s74_9 : dispatch 2 (optimized 7) b74_9.1 b74_9.2.1 b74_9.2.2 = false := by
  decide +kernel

def b74_10 : W × W × List W :=
  (0xfffffff801f0001ffffffffa5294a529, 0x7c00000000000000739ce739c, [0xfffffff8000fffff0000000108421084, 0x1f003e000000004a5294a52, 0x7fe007c00fffffff8c6318c63, 0xf8000fffffffef7bdef7b, 0x3e0000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s74_10 : dispatch 2 (optimized 7) b74_10.1 b74_10.2.1 b74_10.2.2 = false := by
  decide +kernel

def b74_11 : W × W × List W :=
  (0x1f003e000000004a5294a52, 0x7fe007c00fffffff8c6318c63, [0xfffffff8000fffff0000000108421084, 0xfffffff801f0001ffffffffa5294a529, 0xf8000fffffffef7bdef7b, 0x3e0000000000000739ce739c, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s74_11 : dispatch 2 (optimized 7) b74_11.1 b74_11.2.1 b74_11.2.2 = false := by
  decide +kernel

def b74_12 : W × W × List W :=
  (0x1f003e000000004a5294a52, 0xf8000fffffffef7bdef7b, [0xfffffff8000fffff0000000108421084, 0xfffffff801f0001ffffffffa5294a529, 0x7fe007c00fffffff8c6318c63, 0x3e0000000000000739ce739c, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s74_12 : dispatch 2 (optimized 7) b74_12.1 b74_12.2.1 b74_12.2.2 = false := by
  decide +kernel

def b74_13 : W × W × List W :=
  (0x1f003e000000004a5294a52, 0x3e0000000000000739ce739c, [0xfffffff8000fffff0000000108421084, 0xfffffff801f0001ffffffffa5294a529, 0x7fe007c00fffffff8c6318c63, 0xf8000fffffffef7bdef7b, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s74_13 : dispatch 2 (optimized 7) b74_13.1 b74_13.2.1 b74_13.2.2 = false := by
  decide +kernel

def b74_14 : W × W × List W :=
  (0x1f003e000000004a5294a52, 0x7c00000000000000739ce739c, [0xfffffff8000fffff0000000108421084, 0xfffffff801f0001ffffffffa5294a529, 0x7fe007c00fffffff8c6318c63, 0xf8000fffffffef7bdef7b, 0x3e0000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s74_14 : dispatch 2 (optimized 7) b74_14.1 b74_14.2.1 b74_14.2.2 = false := by
  decide +kernel

def b74_15 : W × W × List W :=
  (0x7fe007c00fffffff8c6318c63, 0xf8000fffffffef7bdef7b, [0xfffffff8000fffff0000000108421084, 0xfffffff801f0001ffffffffa5294a529, 0x1f003e000000004a5294a52, 0x3e0000000000000739ce739c, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s74_15 : dispatch 2 (optimized 7) b74_15.1 b74_15.2.1 b74_15.2.2 = false := by
  decide +kernel

def b74_16 : W × W × List W :=
  (0x7fe007c00fffffff8c6318c63, 0x3e0000000000000739ce739c, [0xfffffff8000fffff0000000108421084, 0xfffffff801f0001ffffffffa5294a529, 0x1f003e000000004a5294a52, 0xf8000fffffffef7bdef7b, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s74_16 : dispatch 2 (optimized 7) b74_16.1 b74_16.2.1 b74_16.2.2 = false := by
  decide +kernel

def b74_17 : W × W × List W :=
  (0x7fe007c00fffffff8c6318c63, 0x7c00000000000000739ce739c, [0xfffffff8000fffff0000000108421084, 0xfffffff801f0001ffffffffa5294a529, 0x1f003e000000004a5294a52, 0xf8000fffffffef7bdef7b, 0x3e0000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s74_17 : dispatch 2 (optimized 7) b74_17.1 b74_17.2.1 b74_17.2.2 = false := by
  decide +kernel

def b74_18 : W × W × List W :=
  (0xf8000fffffffef7bdef7b, 0x3e0000000000000739ce739c, [0xfffffff8000fffff0000000108421084, 0xfffffff801f0001ffffffffa5294a529, 0x1f003e000000004a5294a52, 0x7fe007c00fffffff8c6318c63, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s74_18 : dispatch 2 (optimized 7) b74_18.1 b74_18.2.1 b74_18.2.2 = false := by
  decide +kernel

def b74_19 : W × W × List W :=
  (0xf8000fffffffef7bdef7b, 0x7c00000000000000739ce739c, [0xfffffff8000fffff0000000108421084, 0xfffffff801f0001ffffffffa5294a529, 0x1f003e000000004a5294a52, 0x7fe007c00fffffff8c6318c63, 0x3e0000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s74_19 : dispatch 2 (optimized 7) b74_19.1 b74_19.2.1 b74_19.2.2 = false := by
  decide +kernel

def b74_20 : W × W × List W :=
  (0x3e0000000000000739ce739c, 0x7c00000000000000739ce739c, [0xfffffff8000fffff0000000108421084, 0xfffffff801f0001ffffffffa5294a529, 0x1f003e000000004a5294a52, 0x7fe007c00fffffff8c6318c63, 0xf8000fffffffef7bdef7b])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s74_20 : dispatch 2 (optimized 7) b74_20.1 b74_20.2.1 b74_20.2.2 = false := by
  decide +kernel

theorem search74 : optimized 8 2 raw74 = false :=
  split_search 7 2 raw74 [b74_0, b74_1, b74_2, b74_3, b74_4, b74_5, b74_6, b74_7, b74_8, b74_9, b74_10, b74_11, b74_12, b74_13, b74_14, b74_15, b74_16, b74_17, b74_18, b74_19, b74_20]
    (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨s74_0, (List.forall_mem_cons.2 ⟨s74_1, (List.forall_mem_cons.2 ⟨s74_2, (List.forall_mem_cons.2 ⟨s74_3, (List.forall_mem_cons.2 ⟨s74_4, (List.forall_mem_cons.2 ⟨s74_5, (List.forall_mem_cons.2 ⟨s74_6, (List.forall_mem_cons.2 ⟨s74_7, (List.forall_mem_cons.2 ⟨s74_8, (List.forall_mem_cons.2 ⟨s74_9, (List.forall_mem_cons.2 ⟨s74_10, (List.forall_mem_cons.2 ⟨s74_11, (List.forall_mem_cons.2 ⟨s74_12, (List.forall_mem_cons.2 ⟨s74_13, (List.forall_mem_cons.2 ⟨s74_14, (List.forall_mem_cons.2 ⟨s74_15, (List.forall_mem_cons.2 ⟨s74_16, (List.forall_mem_cons.2 ⟨s74_17, (List.forall_mem_cons.2 ⟨s74_18, (List.forall_mem_cons.2 ⟨s74_19, (List.forall_mem_cons.2 ⟨s74_20, (fun _ h => nomatch h)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c74 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6)) x) → 9 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw74 _ 8 2 (by decide +kernel) (by decide +kernel) (by decide)
    (search74) (by decide +kernel) C hm (by omega) he

def raw75 : List W :=
  [0xfffffc0000fffffffffffc9249249249, 0xfffffc003f00003f0000012492492492, 0x3f000fc00000024924924924, 0xfc003f0000000030c30c30c30, 0xfc00000000036db6db6db6, 0x3ffc0000000fffffc71c71c71c7, 0x3f0000000000000038e38e38e38]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c75 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 5 && x 6)) x) → 9 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw75 _ 8 2 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw76 : List W :=
  [0xfffffff8000fffff0000000294a5294a, 0xfffffff83ff0001ffffffff842108421, 0x3e0fffffffd6b5ad6b5, 0x7c00fffffffd6b5ad6b5, 0xf8000fffffffd6b5ad6b5, 0x7c1f00000000000018c6318c6, 0x7fe00000000000006318c6318]

def b76_0 : W × W × List W :=
  (0xfffffff8000fffff0000000294a5294a, 0xfffffff83ff0001ffffffff842108421, [0x3e0fffffffd6b5ad6b5, 0x7c00fffffffd6b5ad6b5, 0xf8000fffffffd6b5ad6b5, 0x7c1f00000000000018c6318c6, 0x7fe00000000000006318c6318])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s76_0 : dispatch 2 (optimized 7) b76_0.1 b76_0.2.1 b76_0.2.2 = false := by
  decide +kernel

def b76_1 : W × W × List W :=
  (0xfffffff8000fffff0000000294a5294a, 0x3e0fffffffd6b5ad6b5, [0xfffffff83ff0001ffffffff842108421, 0x7c00fffffffd6b5ad6b5, 0xf8000fffffffd6b5ad6b5, 0x7c1f00000000000018c6318c6, 0x7fe00000000000006318c6318])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s76_1 : dispatch 2 (optimized 7) b76_1.1 b76_1.2.1 b76_1.2.2 = false := by
  decide +kernel

def b76_2 : W × W × List W :=
  (0xfffffff8000fffff0000000294a5294a, 0x7c00fffffffd6b5ad6b5, [0xfffffff83ff0001ffffffff842108421, 0x3e0fffffffd6b5ad6b5, 0xf8000fffffffd6b5ad6b5, 0x7c1f00000000000018c6318c6, 0x7fe00000000000006318c6318])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s76_2 : dispatch 2 (optimized 7) b76_2.1 b76_2.2.1 b76_2.2.2 = false := by
  decide +kernel

def b76_3 : W × W × List W :=
  (0xfffffff8000fffff0000000294a5294a, 0xf8000fffffffd6b5ad6b5, [0xfffffff83ff0001ffffffff842108421, 0x3e0fffffffd6b5ad6b5, 0x7c00fffffffd6b5ad6b5, 0x7c1f00000000000018c6318c6, 0x7fe00000000000006318c6318])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s76_3 : dispatch 2 (optimized 7) b76_3.1 b76_3.2.1 b76_3.2.2 = false := by
  decide +kernel

def b76_4 : W × W × List W :=
  (0xfffffff8000fffff0000000294a5294a, 0x7c1f00000000000018c6318c6, [0xfffffff83ff0001ffffffff842108421, 0x3e0fffffffd6b5ad6b5, 0x7c00fffffffd6b5ad6b5, 0xf8000fffffffd6b5ad6b5, 0x7fe00000000000006318c6318])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s76_4 : dispatch 2 (optimized 7) b76_4.1 b76_4.2.1 b76_4.2.2 = false := by
  decide +kernel

def b76_5 : W × W × List W :=
  (0xfffffff8000fffff0000000294a5294a, 0x7fe00000000000006318c6318, [0xfffffff83ff0001ffffffff842108421, 0x3e0fffffffd6b5ad6b5, 0x7c00fffffffd6b5ad6b5, 0xf8000fffffffd6b5ad6b5, 0x7c1f00000000000018c6318c6])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s76_5 : dispatch 2 (optimized 7) b76_5.1 b76_5.2.1 b76_5.2.2 = false := by
  decide +kernel

def b76_6 : W × W × List W :=
  (0xfffffff83ff0001ffffffff842108421, 0x3e0fffffffd6b5ad6b5, [0xfffffff8000fffff0000000294a5294a, 0x7c00fffffffd6b5ad6b5, 0xf8000fffffffd6b5ad6b5, 0x7c1f00000000000018c6318c6, 0x7fe00000000000006318c6318])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s76_6 : dispatch 2 (optimized 7) b76_6.1 b76_6.2.1 b76_6.2.2 = false := by
  decide +kernel

def b76_7 : W × W × List W :=
  (0xfffffff83ff0001ffffffff842108421, 0x7c00fffffffd6b5ad6b5, [0xfffffff8000fffff0000000294a5294a, 0x3e0fffffffd6b5ad6b5, 0xf8000fffffffd6b5ad6b5, 0x7c1f00000000000018c6318c6, 0x7fe00000000000006318c6318])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s76_7 : dispatch 2 (optimized 7) b76_7.1 b76_7.2.1 b76_7.2.2 = false := by
  decide +kernel

def b76_8 : W × W × List W :=
  (0xfffffff83ff0001ffffffff842108421, 0xf8000fffffffd6b5ad6b5, [0xfffffff8000fffff0000000294a5294a, 0x3e0fffffffd6b5ad6b5, 0x7c00fffffffd6b5ad6b5, 0x7c1f00000000000018c6318c6, 0x7fe00000000000006318c6318])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s76_8 : dispatch 2 (optimized 7) b76_8.1 b76_8.2.1 b76_8.2.2 = false := by
  decide +kernel

def b76_9 : W × W × List W :=
  (0xfffffff83ff0001ffffffff842108421, 0x7c1f00000000000018c6318c6, [0xfffffff8000fffff0000000294a5294a, 0x3e0fffffffd6b5ad6b5, 0x7c00fffffffd6b5ad6b5, 0xf8000fffffffd6b5ad6b5, 0x7fe00000000000006318c6318])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s76_9 : dispatch 2 (optimized 7) b76_9.1 b76_9.2.1 b76_9.2.2 = false := by
  decide +kernel

def b76_10 : W × W × List W :=
  (0xfffffff83ff0001ffffffff842108421, 0x7fe00000000000006318c6318, [0xfffffff8000fffff0000000294a5294a, 0x3e0fffffffd6b5ad6b5, 0x7c00fffffffd6b5ad6b5, 0xf8000fffffffd6b5ad6b5, 0x7c1f00000000000018c6318c6])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s76_10 : dispatch 2 (optimized 7) b76_10.1 b76_10.2.1 b76_10.2.2 = false := by
  decide +kernel

def b76_11 : W × W × List W :=
  (0x3e0fffffffd6b5ad6b5, 0x7c00fffffffd6b5ad6b5, [0xfffffff8000fffff0000000294a5294a, 0xfffffff83ff0001ffffffff842108421, 0xf8000fffffffd6b5ad6b5, 0x7c1f00000000000018c6318c6, 0x7fe00000000000006318c6318])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s76_11 : dispatch 2 (optimized 7) b76_11.1 b76_11.2.1 b76_11.2.2 = false := by
  decide +kernel

def b76_12 : W × W × List W :=
  (0x3e0fffffffd6b5ad6b5, 0xf8000fffffffd6b5ad6b5, [0xfffffff8000fffff0000000294a5294a, 0xfffffff83ff0001ffffffff842108421, 0x7c00fffffffd6b5ad6b5, 0x7c1f00000000000018c6318c6, 0x7fe00000000000006318c6318])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s76_12 : dispatch 2 (optimized 7) b76_12.1 b76_12.2.1 b76_12.2.2 = false := by
  decide +kernel

def b76_13 : W × W × List W :=
  (0x3e0fffffffd6b5ad6b5, 0x7c1f00000000000018c6318c6, [0xfffffff8000fffff0000000294a5294a, 0xfffffff83ff0001ffffffff842108421, 0x7c00fffffffd6b5ad6b5, 0xf8000fffffffd6b5ad6b5, 0x7fe00000000000006318c6318])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s76_13 : dispatch 2 (optimized 7) b76_13.1 b76_13.2.1 b76_13.2.2 = false := by
  decide +kernel

def b76_14 : W × W × List W :=
  (0x3e0fffffffd6b5ad6b5, 0x7fe00000000000006318c6318, [0xfffffff8000fffff0000000294a5294a, 0xfffffff83ff0001ffffffff842108421, 0x7c00fffffffd6b5ad6b5, 0xf8000fffffffd6b5ad6b5, 0x7c1f00000000000018c6318c6])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s76_14 : dispatch 2 (optimized 7) b76_14.1 b76_14.2.1 b76_14.2.2 = false := by
  decide +kernel

def b76_15 : W × W × List W :=
  (0x7c00fffffffd6b5ad6b5, 0xf8000fffffffd6b5ad6b5, [0xfffffff8000fffff0000000294a5294a, 0xfffffff83ff0001ffffffff842108421, 0x3e0fffffffd6b5ad6b5, 0x7c1f00000000000018c6318c6, 0x7fe00000000000006318c6318])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s76_15 : dispatch 2 (optimized 7) b76_15.1 b76_15.2.1 b76_15.2.2 = false := by
  decide +kernel

def b76_16 : W × W × List W :=
  (0x7c00fffffffd6b5ad6b5, 0x7c1f00000000000018c6318c6, [0xfffffff8000fffff0000000294a5294a, 0xfffffff83ff0001ffffffff842108421, 0x3e0fffffffd6b5ad6b5, 0xf8000fffffffd6b5ad6b5, 0x7fe00000000000006318c6318])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s76_16 : dispatch 2 (optimized 7) b76_16.1 b76_16.2.1 b76_16.2.2 = false := by
  decide +kernel

def b76_17 : W × W × List W :=
  (0x7c00fffffffd6b5ad6b5, 0x7fe00000000000006318c6318, [0xfffffff8000fffff0000000294a5294a, 0xfffffff83ff0001ffffffff842108421, 0x3e0fffffffd6b5ad6b5, 0xf8000fffffffd6b5ad6b5, 0x7c1f00000000000018c6318c6])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s76_17 : dispatch 2 (optimized 7) b76_17.1 b76_17.2.1 b76_17.2.2 = false := by
  decide +kernel

def b76_18 : W × W × List W :=
  (0xf8000fffffffd6b5ad6b5, 0x7c1f00000000000018c6318c6, [0xfffffff8000fffff0000000294a5294a, 0xfffffff83ff0001ffffffff842108421, 0x3e0fffffffd6b5ad6b5, 0x7c00fffffffd6b5ad6b5, 0x7fe00000000000006318c6318])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s76_18 : dispatch 2 (optimized 7) b76_18.1 b76_18.2.1 b76_18.2.2 = false := by
  decide +kernel

def b76_19 : W × W × List W :=
  (0xf8000fffffffd6b5ad6b5, 0x7fe00000000000006318c6318, [0xfffffff8000fffff0000000294a5294a, 0xfffffff83ff0001ffffffff842108421, 0x3e0fffffffd6b5ad6b5, 0x7c00fffffffd6b5ad6b5, 0x7c1f00000000000018c6318c6])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s76_19 : dispatch 2 (optimized 7) b76_19.1 b76_19.2.1 b76_19.2.2 = false := by
  decide +kernel

def b76_20 : W × W × List W :=
  (0x7c1f00000000000018c6318c6, 0x7fe00000000000006318c6318, [0xfffffff8000fffff0000000294a5294a, 0xfffffff83ff0001ffffffff842108421, 0x3e0fffffffd6b5ad6b5, 0x7c00fffffffd6b5ad6b5, 0xf8000fffffffd6b5ad6b5])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s76_20 : dispatch 2 (optimized 7) b76_20.1 b76_20.2.1 b76_20.2.2 = false := by
  decide +kernel

theorem search76 : optimized 8 2 raw76 = false :=
  split_search 7 2 raw76 [b76_0, b76_1, b76_2, b76_3, b76_4, b76_5, b76_6, b76_7, b76_8, b76_9, b76_10, b76_11, b76_12, b76_13, b76_14, b76_15, b76_16, b76_17, b76_18, b76_19, b76_20]
    (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨s76_0, (List.forall_mem_cons.2 ⟨s76_1, (List.forall_mem_cons.2 ⟨s76_2, (List.forall_mem_cons.2 ⟨s76_3, (List.forall_mem_cons.2 ⟨s76_4, (List.forall_mem_cons.2 ⟨s76_5, (List.forall_mem_cons.2 ⟨s76_6, (List.forall_mem_cons.2 ⟨s76_7, (List.forall_mem_cons.2 ⟨s76_8, (List.forall_mem_cons.2 ⟨s76_9, (List.forall_mem_cons.2 ⟨s76_10, (List.forall_mem_cons.2 ⟨s76_11, (List.forall_mem_cons.2 ⟨s76_12, (List.forall_mem_cons.2 ⟨s76_13, (List.forall_mem_cons.2 ⟨s76_14, (List.forall_mem_cons.2 ⟨s76_15, (List.forall_mem_cons.2 ⟨s76_16, (List.forall_mem_cons.2 ⟨s76_17, (List.forall_mem_cons.2 ⟨s76_18, (List.forall_mem_cons.2 ⟨s76_19, (List.forall_mem_cons.2 ⟨s76_20, (fun _ h => nomatch h)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c76 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 5 && x 6)) x) → 9 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw76 _ 8 2 (by decide +kernel) (by decide +kernel) (by decide)
    (search76) (by decide +kernel) C hm (by omega) he

def raw77 : List W :=
  [0xfffffff8000fffff0000000294a5294a, 0xfffffff801f0001ffffffffc6318c631, 0x3e0003e0fffffff94a5294a5, 0x7c00fffffffd6b5ad6b5, 0xf8000fffffffd6b5ad6b5, 0x7c1f00000000000018c6318c6, 0x7fe00000000000006318c6318]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c77 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 5 && x 6)) x) → 9 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw77 _ 8 2 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw78 : List W :=
  [0xfffffc000003ffff0000020820820820, 0xfffffc003ffc003f0000012492492492, 0xfc0fc0fc0fffffc9249249249, 0x3f00003f000fffffc71c71c71c7, 0x3f000000fffffedb6db6db6d, 0xfc00000000000036db6db6db6, 0x3f0000000000000038e38e38e38]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c78 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) x) → 9 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw78 _ 8 2 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw79 : List W :=
  [0xfffffff800007fff0000000210842108, 0xfffffff801ff801ffffffff94a5294a5, 0xf83e000000004a5294a52, 0x7fe007c00fffffff8c6318c63, 0x1f0000000000006b5ad6b5a, 0x3e0000000000000739ce739c, 0x7c00000000000000739ce739c]

def b79_0 : W × W × List W :=
  (0xfffffff800007fff0000000210842108, 0xfffffff801ff801ffffffff94a5294a5, [0xf83e000000004a5294a52, 0x7fe007c00fffffff8c6318c63, 0x1f0000000000006b5ad6b5a, 0x3e0000000000000739ce739c, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s79_0 : dispatch 2 (optimized 7) b79_0.1 b79_0.2.1 b79_0.2.2 = false := by
  decide +kernel

def b79_1 : W × W × List W :=
  (0xfffffff800007fff0000000210842108, 0xf83e000000004a5294a52, [0xfffffff801ff801ffffffff94a5294a5, 0x7fe007c00fffffff8c6318c63, 0x1f0000000000006b5ad6b5a, 0x3e0000000000000739ce739c, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s79_1 : dispatch 2 (optimized 7) b79_1.1 b79_1.2.1 b79_1.2.2 = false := by
  decide +kernel

def b79_2 : W × W × List W :=
  (0xfffffff800007fff0000000210842108, 0x7fe007c00fffffff8c6318c63, [0xfffffff801ff801ffffffff94a5294a5, 0xf83e000000004a5294a52, 0x1f0000000000006b5ad6b5a, 0x3e0000000000000739ce739c, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s79_2 : dispatch 2 (optimized 7) b79_2.1 b79_2.2.1 b79_2.2.2 = false := by
  decide +kernel

def b79_3 : W × W × List W :=
  (0xfffffff800007fff0000000210842108, 0x1f0000000000006b5ad6b5a, [0xfffffff801ff801ffffffff94a5294a5, 0xf83e000000004a5294a52, 0x7fe007c00fffffff8c6318c63, 0x3e0000000000000739ce739c, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s79_3 : dispatch 2 (optimized 7) b79_3.1 b79_3.2.1 b79_3.2.2 = false := by
  decide +kernel

def b79_4 : W × W × List W :=
  (0xfffffff800007fff0000000210842108, 0x3e0000000000000739ce739c, [0xfffffff801ff801ffffffff94a5294a5, 0xf83e000000004a5294a52, 0x7fe007c00fffffff8c6318c63, 0x1f0000000000006b5ad6b5a, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s79_4 : dispatch 2 (optimized 7) b79_4.1 b79_4.2.1 b79_4.2.2 = false := by
  decide +kernel

def b79_5 : W × W × List W :=
  (0xfffffff800007fff0000000210842108, 0x7c00000000000000739ce739c, [0xfffffff801ff801ffffffff94a5294a5, 0xf83e000000004a5294a52, 0x7fe007c00fffffff8c6318c63, 0x1f0000000000006b5ad6b5a, 0x3e0000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s79_5 : dispatch 2 (optimized 7) b79_5.1 b79_5.2.1 b79_5.2.2 = false := by
  decide +kernel

def b79_6 : W × W × List W :=
  (0xfffffff801ff801ffffffff94a5294a5, 0xf83e000000004a5294a52, [0xfffffff800007fff0000000210842108, 0x7fe007c00fffffff8c6318c63, 0x1f0000000000006b5ad6b5a, 0x3e0000000000000739ce739c, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s79_6 : dispatch 2 (optimized 7) b79_6.1 b79_6.2.1 b79_6.2.2 = false := by
  decide +kernel

def b79_7 : W × W × List W :=
  (0xfffffff801ff801ffffffff94a5294a5, 0x7fe007c00fffffff8c6318c63, [0xfffffff800007fff0000000210842108, 0xf83e000000004a5294a52, 0x1f0000000000006b5ad6b5a, 0x3e0000000000000739ce739c, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s79_7 : dispatch 2 (optimized 7) b79_7.1 b79_7.2.1 b79_7.2.2 = false := by
  decide +kernel

def b79_8 : W × W × List W :=
  (0xfffffff801ff801ffffffff94a5294a5, 0x1f0000000000006b5ad6b5a, [0xfffffff800007fff0000000210842108, 0xf83e000000004a5294a52, 0x7fe007c00fffffff8c6318c63, 0x3e0000000000000739ce739c, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s79_8 : dispatch 2 (optimized 7) b79_8.1 b79_8.2.1 b79_8.2.2 = false := by
  decide +kernel

def b79_9 : W × W × List W :=
  (0xfffffff801ff801ffffffff94a5294a5, 0x3e0000000000000739ce739c, [0xfffffff800007fff0000000210842108, 0xf83e000000004a5294a52, 0x7fe007c00fffffff8c6318c63, 0x1f0000000000006b5ad6b5a, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s79_9 : dispatch 2 (optimized 7) b79_9.1 b79_9.2.1 b79_9.2.2 = false := by
  decide +kernel

def b79_10 : W × W × List W :=
  (0xfffffff801ff801ffffffff94a5294a5, 0x7c00000000000000739ce739c, [0xfffffff800007fff0000000210842108, 0xf83e000000004a5294a52, 0x7fe007c00fffffff8c6318c63, 0x1f0000000000006b5ad6b5a, 0x3e0000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s79_10 : dispatch 2 (optimized 7) b79_10.1 b79_10.2.1 b79_10.2.2 = false := by
  decide +kernel

def b79_11 : W × W × List W :=
  (0xf83e000000004a5294a52, 0x7fe007c00fffffff8c6318c63, [0xfffffff800007fff0000000210842108, 0xfffffff801ff801ffffffff94a5294a5, 0x1f0000000000006b5ad6b5a, 0x3e0000000000000739ce739c, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s79_11 : dispatch 2 (optimized 7) b79_11.1 b79_11.2.1 b79_11.2.2 = false := by
  decide +kernel

def b79_12 : W × W × List W :=
  (0xf83e000000004a5294a52, 0x1f0000000000006b5ad6b5a, [0xfffffff800007fff0000000210842108, 0xfffffff801ff801ffffffff94a5294a5, 0x7fe007c00fffffff8c6318c63, 0x3e0000000000000739ce739c, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s79_12 : dispatch 2 (optimized 7) b79_12.1 b79_12.2.1 b79_12.2.2 = false := by
  decide +kernel

def b79_13 : W × W × List W :=
  (0xf83e000000004a5294a52, 0x3e0000000000000739ce739c, [0xfffffff800007fff0000000210842108, 0xfffffff801ff801ffffffff94a5294a5, 0x7fe007c00fffffff8c6318c63, 0x1f0000000000006b5ad6b5a, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s79_13 : dispatch 2 (optimized 7) b79_13.1 b79_13.2.1 b79_13.2.2 = false := by
  decide +kernel

def b79_14 : W × W × List W :=
  (0xf83e000000004a5294a52, 0x7c00000000000000739ce739c, [0xfffffff800007fff0000000210842108, 0xfffffff801ff801ffffffff94a5294a5, 0x7fe007c00fffffff8c6318c63, 0x1f0000000000006b5ad6b5a, 0x3e0000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s79_14 : dispatch 2 (optimized 7) b79_14.1 b79_14.2.1 b79_14.2.2 = false := by
  decide +kernel

def b79_15 : W × W × List W :=
  (0x7fe007c00fffffff8c6318c63, 0x1f0000000000006b5ad6b5a, [0xfffffff800007fff0000000210842108, 0xfffffff801ff801ffffffff94a5294a5, 0xf83e000000004a5294a52, 0x3e0000000000000739ce739c, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s79_15 : dispatch 2 (optimized 7) b79_15.1 b79_15.2.1 b79_15.2.2 = false := by
  decide +kernel

def b79_16 : W × W × List W :=
  (0x7fe007c00fffffff8c6318c63, 0x3e0000000000000739ce739c, [0xfffffff800007fff0000000210842108, 0xfffffff801ff801ffffffff94a5294a5, 0xf83e000000004a5294a52, 0x1f0000000000006b5ad6b5a, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s79_16 : dispatch 2 (optimized 7) b79_16.1 b79_16.2.1 b79_16.2.2 = false := by
  decide +kernel

def b79_17 : W × W × List W :=
  (0x7fe007c00fffffff8c6318c63, 0x7c00000000000000739ce739c, [0xfffffff800007fff0000000210842108, 0xfffffff801ff801ffffffff94a5294a5, 0xf83e000000004a5294a52, 0x1f0000000000006b5ad6b5a, 0x3e0000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s79_17 : dispatch 2 (optimized 7) b79_17.1 b79_17.2.1 b79_17.2.2 = false := by
  decide +kernel

def b79_18 : W × W × List W :=
  (0x1f0000000000006b5ad6b5a, 0x3e0000000000000739ce739c, [0xfffffff800007fff0000000210842108, 0xfffffff801ff801ffffffff94a5294a5, 0xf83e000000004a5294a52, 0x7fe007c00fffffff8c6318c63, 0x7c00000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s79_18 : dispatch 2 (optimized 7) b79_18.1 b79_18.2.1 b79_18.2.2 = false := by
  decide +kernel

def b79_19 : W × W × List W :=
  (0x1f0000000000006b5ad6b5a, 0x7c00000000000000739ce739c, [0xfffffff800007fff0000000210842108, 0xfffffff801ff801ffffffff94a5294a5, 0xf83e000000004a5294a52, 0x7fe007c00fffffff8c6318c63, 0x3e0000000000000739ce739c])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s79_19 : dispatch 2 (optimized 7) b79_19.1 b79_19.2.1 b79_19.2.2 = false := by
  decide +kernel

def b79_20 : W × W × List W :=
  (0x3e0000000000000739ce739c, 0x7c00000000000000739ce739c, [0xfffffff800007fff0000000210842108, 0xfffffff801ff801ffffffff94a5294a5, 0xf83e000000004a5294a52, 0x7fe007c00fffffff8c6318c63, 0x1f0000000000006b5ad6b5a])

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s79_20 : dispatch 2 (optimized 7) b79_20.1 b79_20.2.1 b79_20.2.2 = false := by
  decide +kernel

theorem search79 : optimized 8 2 raw79 = false :=
  split_search 7 2 raw79 [b79_0, b79_1, b79_2, b79_3, b79_4, b79_5, b79_6, b79_7, b79_8, b79_9, b79_10, b79_11, b79_12, b79_13, b79_14, b79_15, b79_16, b79_17, b79_18, b79_19, b79_20]
    (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨s79_0, (List.forall_mem_cons.2 ⟨s79_1, (List.forall_mem_cons.2 ⟨s79_2, (List.forall_mem_cons.2 ⟨s79_3, (List.forall_mem_cons.2 ⟨s79_4, (List.forall_mem_cons.2 ⟨s79_5, (List.forall_mem_cons.2 ⟨s79_6, (List.forall_mem_cons.2 ⟨s79_7, (List.forall_mem_cons.2 ⟨s79_8, (List.forall_mem_cons.2 ⟨s79_9, (List.forall_mem_cons.2 ⟨s79_10, (List.forall_mem_cons.2 ⟨s79_11, (List.forall_mem_cons.2 ⟨s79_12, (List.forall_mem_cons.2 ⟨s79_13, (List.forall_mem_cons.2 ⟨s79_14, (List.forall_mem_cons.2 ⟨s79_15, (List.forall_mem_cons.2 ⟨s79_16, (List.forall_mem_cons.2 ⟨s79_17, (List.forall_mem_cons.2 ⟨s79_18, (List.forall_mem_cons.2 ⟨s79_19, (List.forall_mem_cons.2 ⟨s79_20, (fun _ h => nomatch h)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c79 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6)) x) → 9 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw79 _ 8 2 (by decide +kernel) (by decide +kernel) (by decide)
    (search79) (by decide +kernel) C hm (by omega) he

def raw80 : List W :=
  [0xfffffc000003ffff0000012492492492, 0xfffffc003ffc003ffffffc9249249249, 0xfc0fc00000024924924924, 0xfc003f0000000028a28a28a28, 0x3f0000000000036db6db6db6, 0x3ffc0000000fffffc71c71c71c7, 0x3f0000000000000038e38e38e38]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c80 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 5 && x 6)) x) → 9 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw80 _ 8 2 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw81 : List W :=
  [0xfffffc000003fffffffffc9249249249, 0xfffffc0000fc003f0000012492492492, 0xfc0fc00000024924924924, 0x3f03f0000000030c30c30c30, 0x3ffff000000fffffc71c71c71c7, 0xfc00000000000038e38e38e38, 0x3f0000000000000038e38e38e38]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c81 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6)) x) → 9 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw81 _ 8 2 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw82 : List W :=
  [0xfffffc000003ffff0000012492492492, 0xfffffc003ffc003ffffffc9249249249, 0xfc0000fc0fffffc5145145145, 0x3f000fffffedb6db6db6d, 0x3f000fc00000000006186186186, 0x3f0000000000036db6db6db6, 0x3ffc00000000000038e38e38e38]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c82 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 4 && x 6)) x) → 9 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw82 _ 8 2 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw83 : List W :=
  [0xfffffff800007ffffffffffa5294a529, 0xfffffff8000f801f00000005294a5294, 0x1f003e0000000018c6318c6, 0x7c0000000005ad6b5ad6, 0x7fe0f8000fffffff8c6318c63, 0x3ff0000000000006318c6318, 0x7c00000000000000739ce739c]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c83 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5) || (x 4 && x 6)) x) → 9 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw83 _ 8 2 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

def raw84 : List W :=
  [0xfffffc000003ffff0000014514514514, 0xfffffc0000fc003f00000228a28a28a2, 0x3f000fc0fffffe1861861861, 0x3f000fffffebaebaebaeb, 0xfc0fc0000fffffcd34d34d34d, 0x3f03f000000000000e38e38e38e, 0x3ffc00000000000030c30c30c30]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem c84 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 9 ≤ C.size := by
  intro C hm he
  by_contra hlt
  exact no_small raw84 _ 8 2 (by decide +kernel) (by decide +kernel) (by decide)
    (by decide +kernel) (by decide +kernel) C hm (by omega) he

end PEqualNP.Outside.L_meta_931_aux

theorem PEqualNP.Outside.L_meta_931 : (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 2 → Bool, C.eval (List.ofFn x) = (fun x : Fin 2 → Bool => (x 0 && x 1)) x) → 1 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 3 → Bool, C.eval (List.ofFn x) = (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2)) x) → 2 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 3 → Bool, C.eval (List.ofFn x) = (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) x) → 4 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 4 → Bool, C.eval (List.ofFn x) = (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) x) → 3 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 4 → Bool, C.eval (List.ofFn x) = (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) x) → 3 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 4 → Bool, C.eval (List.ofFn x) = (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3)) x) → 4 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 4 → Bool, C.eval (List.ofFn x) = (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2)) x) → 5 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4)) x) → 4 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4)) x) → 4 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) x) → 5 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4)) x) → 6 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4)) x) → 5 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2)) x) → 6 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4)) x) → 6 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4)) x) → 7 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4)) x) → 7 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4)) x) → 8 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5)) x) → 5 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) x) → 5 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) x) → 6 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5)) x) → 5 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5)) x) → 5 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5)) x) → 6 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5)) x) → 7 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)) x) → 6 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)) x) → 7 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) x) → 6 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) x) → 7 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5)) x) → 7 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2)) x) → 7 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5)) x) → 7 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5)) x) → 8 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5)) x) → 8 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5)) x) → 8 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) x) → 8 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5)) x) → 8 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5)) x) → 8 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) x) → 9 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5)) x) → 8 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4)) x) → 9 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4)) x) → 9 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5)) x) → 9 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) → 6 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 5 && x 6)) x) → 6 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 5 && x 6)) x) → 7 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6)) x) → 6 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) → 8 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 5 && x 6)) x) → 7 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5) || (x 4 && x 6)) x) → 7 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6)) x) → 6 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6)) x) → 7 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 5 && x 6)) x) → 8 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6)) x) → 7 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6)) x) → 8 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 5 && x 6)) x) → 7 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 5 && x 6)) x) → 8 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) → 9 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6)) x) → 8 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6)) x) → 8 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) x) → 8 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6)) x) → 8 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 4 && x 6)) x) → 7 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 5 && x 6)) x) → 8 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 8 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) x) → 9 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4) || (x 5 && x 6)) x) → 9 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6)) x) → 8 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2)) x) → 8 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6)) x) → 8 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 6)) x) → 9 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6)) x) → 8 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6)) x) → 9 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6)) x) → 9 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 5 && x 6)) x) → 9 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6)) x) → 9 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 5 && x 6)) x) → 9 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 5 && x 6)) x) → 9 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 5 && x 6)) x) → 9 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) x) → 9 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6)) x) → 9 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 5 && x 6)) x) → 9 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6)) x) → 9 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 4 && x 6)) x) → 9 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5) || (x 4 && x 6)) x) → 9 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 9 ≤ C.size) :=
  ⟨PEqualNP.Outside.L_meta_931_aux.c0, PEqualNP.Outside.L_meta_931_aux.c1, PEqualNP.Outside.L_meta_931_aux.c2, PEqualNP.Outside.L_meta_931_aux.c3, PEqualNP.Outside.L_meta_931_aux.c4, PEqualNP.Outside.L_meta_931_aux.c5, PEqualNP.Outside.L_meta_931_aux.c6, PEqualNP.Outside.L_meta_931_aux.c7, PEqualNP.Outside.L_meta_931_aux.c8, PEqualNP.Outside.L_meta_931_aux.c9, PEqualNP.Outside.L_meta_931_aux.c10, PEqualNP.Outside.L_meta_931_aux.c11, PEqualNP.Outside.L_meta_931_aux.c12, PEqualNP.Outside.L_meta_931_aux.c13, PEqualNP.Outside.L_meta_931_aux.c14, PEqualNP.Outside.L_meta_931_aux.c15, PEqualNP.Outside.L_meta_931_aux.c16, PEqualNP.Outside.L_meta_931_aux.c17, PEqualNP.Outside.L_meta_931_aux.c18, PEqualNP.Outside.L_meta_931_aux.c19, PEqualNP.Outside.L_meta_931_aux.c20, PEqualNP.Outside.L_meta_931_aux.c21, PEqualNP.Outside.L_meta_931_aux.c22, PEqualNP.Outside.L_meta_931_aux.c23, PEqualNP.Outside.L_meta_931_aux.c24, PEqualNP.Outside.L_meta_931_aux.c25, PEqualNP.Outside.L_meta_931_aux.c26, PEqualNP.Outside.L_meta_931_aux.c27, PEqualNP.Outside.L_meta_931_aux.c28, PEqualNP.Outside.L_meta_931_aux.c29, PEqualNP.Outside.L_meta_931_aux.c30, PEqualNP.Outside.L_meta_931_aux.c31, PEqualNP.Outside.L_meta_931_aux.c32, PEqualNP.Outside.L_meta_931_aux.c33, PEqualNP.Outside.L_meta_931_aux.c34, PEqualNP.Outside.L_meta_931_aux.c35, PEqualNP.Outside.L_meta_931_aux.c36, PEqualNP.Outside.L_meta_931_aux.c37, PEqualNP.Outside.L_meta_931_aux.c38, PEqualNP.Outside.L_meta_931_aux.c39, PEqualNP.Outside.L_meta_931_aux.c40, PEqualNP.Outside.L_meta_931_aux.c41, PEqualNP.Outside.L_meta_931_aux.c42, PEqualNP.Outside.L_meta_931_aux.c43, PEqualNP.Outside.L_meta_931_aux.c44, PEqualNP.Outside.L_meta_931_aux.c45, PEqualNP.Outside.L_meta_931_aux.c46, PEqualNP.Outside.L_meta_931_aux.c47, PEqualNP.Outside.L_meta_931_aux.c48, PEqualNP.Outside.L_meta_931_aux.c49, PEqualNP.Outside.L_meta_931_aux.c50, PEqualNP.Outside.L_meta_931_aux.c51, PEqualNP.Outside.L_meta_931_aux.c52, PEqualNP.Outside.L_meta_931_aux.c53, PEqualNP.Outside.L_meta_931_aux.c54, PEqualNP.Outside.L_meta_931_aux.c55, PEqualNP.Outside.L_meta_931_aux.c56, PEqualNP.Outside.L_meta_931_aux.c57, PEqualNP.Outside.L_meta_931_aux.c58, PEqualNP.Outside.L_meta_931_aux.c59, PEqualNP.Outside.L_meta_931_aux.c60, PEqualNP.Outside.L_meta_931_aux.c61, PEqualNP.Outside.L_meta_931_aux.c62, PEqualNP.Outside.L_meta_931_aux.c63, PEqualNP.Outside.L_meta_931_aux.c64, PEqualNP.Outside.L_meta_931_aux.c65, PEqualNP.Outside.L_meta_931_aux.c66, PEqualNP.Outside.L_meta_931_aux.c67, PEqualNP.Outside.L_meta_931_aux.c68, PEqualNP.Outside.L_meta_931_aux.c69, PEqualNP.Outside.L_meta_931_aux.c70, PEqualNP.Outside.L_meta_931_aux.c71, PEqualNP.Outside.L_meta_931_aux.c72, PEqualNP.Outside.L_meta_931_aux.c73, PEqualNP.Outside.L_meta_931_aux.c74, PEqualNP.Outside.L_meta_931_aux.c75, PEqualNP.Outside.L_meta_931_aux.c76, PEqualNP.Outside.L_meta_931_aux.c77, PEqualNP.Outside.L_meta_931_aux.c78, PEqualNP.Outside.L_meta_931_aux.c79, PEqualNP.Outside.L_meta_931_aux.c80, PEqualNP.Outside.L_meta_931_aux.c81, PEqualNP.Outside.L_meta_931_aux.c82, PEqualNP.Outside.L_meta_931_aux.c83, PEqualNP.Outside.L_meta_931_aux.c84⟩
