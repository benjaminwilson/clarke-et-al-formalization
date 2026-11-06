import OfflineMemory.Model

namespace OfflineMemory

variable {n : Nat} {V : Type} [DecidableEq V]

@[simp] theorem delta_self {α : Type} [DecidableEq α] (x : α) : delta x x = 1 := by
  simp [delta]

@[simp] theorem delta_of_ne {α : Type} [DecidableEq α] {x y : α} (h : x ≠ y) :
    delta x y = 0 := by simp [delta, h]

theorem init_matched (initialValues: Fin n → V) : Matched (initialState initialValues) := by
  intro x
  rcases x with ⟨a, v, t⟩
  simp [initialState, delta, eq_comm]

/-- An OpResponse that is honest wrt a matched State transitions to a matched State.
Corresponds to the statement A_{i-1} ∧ E_i → A_i in our exposition. -/
theorem honest_steps_matched_to_matched {s : State n V} {op : OpResponse n V}
    (hA : Matched s) (hH : Honest s op) : Matched (step s op) := by
  intro x
  rcases x with ⟨b, c⟩
  by_cases ha : b = op.address
  · subst b
    simp only [step, getPut, put, get]
    rw [hA (op.address, c)]
    simp [Honest] at hH
    simp [hH, delta, eq_comm, Nat.add_assoc]
  · simp only [step, getPut, put, get]
    rw [hA (b, c)]
    simp [delta, ha]

/-- The exposition's dishonest `A → B` proposition. -/
theorem dishonest_steps_matched_to_unmatched {s : State n V} {op : OpResponse n V}
    (hA : Matched s) (hH : ¬ Honest s op) : Unmatched (step s op) := by
  have ht : op.resp.2 < max s.timer (op.resp.2 + 1) := by omega
  have hne : (op.address, op.resp) ≠
      (op.address, (op.valueWritten, max s.timer (op.resp.2 + 1))) := by
    intro he
    have he' := congrArg (fun x : AddrValueTimestamp n V => x.2.2) he
    simp only at he'
    omega
  have hb := hA (op.address, op.resp)
  have hNotLast : s.last op.address ≠ op.resp := by
    intro he
    exact hH (by simpa [Honest] using he)
  simp only [delta_of_ne hNotLast, Nat.add_zero] at hb
  refine ⟨(op.address, op.resp), ?_, ht⟩
  simp [step, getPut, put, get, delta_of_ne hne, hb]

/-- The exposition's `B → B` proposition. -/
theorem unmatched_steps_to_unmatched {s : State n V} (hB : Unmatched s) (op : OpResponse n V) :
    Unmatched (step s op) := by
  obtain ⟨x, hcount, htime⟩ := hB
  have ht : x.2.2 < max s.timer (op.resp.2 + 1) := by omega
  have hne : x ≠ (op.address, (op.valueWritten, max s.timer (op.resp.2 + 1))) := by
    intro he
    have he' := congrArg (fun x : AddrValueTimestamp n V => x.2.2) he
    simp only at he'
    omega
  refine ⟨x, ?_, ht⟩
  simp only [step, getPut, put, get, delta_of_ne hne, Nat.add_zero]
  omega

/-- Repeated use of Proposition `B → B`: a unmatched survives any suffix. -/
theorem run_unmatched {s : State n V} (hB : Unmatched s)
    (ops : List (OpResponse n V)) : Unmatched (run s ops) := by
  induction ops generalizing s with
  | nil => exact hB
  | cons op ops ih => exact ih (unmatched_steps_to_unmatched hB op)

/-- Repeated use of Proposition `A → A` along an honest prefix. -/
theorem honest_run_matched {s : State n V} (hA : Matched s)
    (ops : List (OpResponse n V)) (hH : AllHonest s ops) : Matched (run s ops) := by
  induction ops generalizing s with
  | nil => exact hA
  | cons op ops ih => exact ih (honest_steps_matched_to_matched hA hH.1) hH.2

/-- The two paths in the exposition's transition diagram. Starting in `A`,
either all operations are honest and `A` survives, or a first dishonest one
creates `B`, which then survives the entire remaining suffix. -/
theorem run_classification {s : State n V} (hA : Matched s)
    (ops : List (OpResponse n V)) :
    (AllHonest s ops ∧ Matched (run s ops)) ∨
    (¬ AllHonest s ops ∧ Unmatched (run s ops)) := by
  induction ops generalizing s with
  | nil => exact Or.inl ⟨True.intro, hA⟩
  | cons op ops ih =>
    by_cases hH : Honest s op
    · rcases ih (honest_steps_matched_to_matched hA hH) with h | h
      · exact Or.inl ⟨⟨hH, h.1⟩, h.2⟩
      · exact Or.inr ⟨fun hh => h.1 hh.2, h.2⟩
    · exact Or.inr ⟨fun hh => hH hh.1,
        run_unmatched (dishonest_steps_matched_to_unmatched hA hH) ops⟩

/-- Proposition `check()` part (a) in the exposition: from `A_k`, acceptance is
equivalent to honesty of every read in the final check(). -/
theorem matched_imp_check_acc_iff_honest (s : State n V) (replies : Fin n → ValueTimestamp V)
    (hA : Matched s) : Accepts (check s replies) ↔ CheckIsHonest s replies := by
  constructor
  · intro h a
    have ha := hA (a, replies a)
    have hc := h (a, replies a)
    simp only [check, delta_self] at hc
    by_cases heq : replies a = s.last a
    · exact heq
    · simp only [delta_of_ne (Ne.symm heq)] at ha
      omega
  · intro h x
    have ha := hA x
    simpa only [check, h x.1] using ha.symm

/-- Proposition `check()` part (b) in the exposition: an Unmatched cannot be repaired
by the final check(), which only increases read multiplicities. -/
theorem check_unmatched_rejects (s : State n V) (replies : Fin n → ValueTimestamp V)
    (hB : Unmatched s) : ¬ Accepts (check s replies) := by
  obtain ⟨x, hlt, _⟩ := hB
  intro h
  have hc := h x
  change s.reads x + delta (replies x.1) x.2 = s.writes x at hc
  omega

/-- **Final theorem in the exposition:** `check()` accepts iff every operation
`E_1,...,E_{k+1}` is honest, where `k = ops.length`. Recall that E_0 =
initialize() can not be dishonest, by definition, and that E_{k+1} corresponds
to the final check().  Allows for any sequence of operations and arbitrary
adversarial responses (including in check()). -/
theorem check_accepts_iff_all_honest (initialValues : Fin n → V)
    (ops : List (OpResponse n V)) (resps : Fin n → ValueTimestamp V) :
    Accepts (check (run (initialState initialValues) ops) resps) ↔
      ExecutionHonest initialValues ops resps := by
  change Accepts (check (run (initialState initialValues) ops) resps) ↔
    AllHonest (initialState initialValues) ops ∧
      CheckIsHonest (run (initialState initialValues) ops) resps
  rcases run_classification (init_matched initialValues) ops with h | h
  · constructor
    · intro hacc
      exact ⟨h.1, (matched_imp_check_acc_iff_honest _ resps h.2).mp hacc⟩
    · intro hh
      exact (matched_imp_check_acc_iff_honest _ resps h.2).mpr hh.2
  · constructor
    · intro hacc
      exact False.elim (check_unmatched_rejects _ resps h.2 hacc)
    · intro hh
      exact False.elim (h.1 hh.1)

end OfflineMemory
