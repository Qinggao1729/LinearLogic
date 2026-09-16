module

public import Foundation.Vorspiel.Multiset

@[expose] public section

namespace Multiset

/-- Principal-versus-side case analysis for sequent equations: if `s + ⦃a⦄ = t + ⦃b⦄`
then either the two distinguished elements coincide and the contexts agree, or each
element occurs in the other's context. This drives the case organization of cut
admissibility ("principal cases" versus "commutative cases"). -/
lemma add_atom_eq_add_atom {s t : Multiset α} {a b : α} (h : s + ⦃a⦄ = t + ⦃b⦄) :
    (a = b ∧ s = t) ∨ ∃ u, s = u + ⦃b⦄ ∧ t = u + ⦃a⦄ := by
  rw [add_atom_eq_cons, add_atom_eq_cons] at h
  rcases cons_eq_cons.mp h with ⟨rfl, rfl⟩ | ⟨-, u, rfl, rfl⟩
  · exact .inl ⟨rfl, rfl⟩
  · exact .inr ⟨u, by rw [add_atom_eq_cons], by rw [add_atom_eq_cons]⟩

/-- A sum with a distinguished element is an atom iff the context is empty and the
elements agree. Degenerate case of the principal-versus-side analysis, used for the
identity cases of cut admissibility. -/
lemma add_atom_eq_atom {s : Multiset α} {a b : α} : s + ⦃a⦄ = ⦃b⦄ ↔ a = b ∧ s = 0 := by
  rw [add_atom_eq_cons, atom_eq_singleton, eq_comm, singleton_eq_cons_iff]
  exact ⟨fun ⟨h₁, h₂⟩ ↦ ⟨h₁.symm, h₂⟩, fun ⟨h₁, h₂⟩ ↦ ⟨h₁.symm, h₂⟩⟩

/-- Variant of `add_atom_eq_add_atom` for a block of `n` identical elements: if
`s + n • ⦃a⦄ = t + ⦃b⦄` then either `b` is one of the `n` copies of `a`, or `b` occurs in
`s`. This drives the case analysis of the persistent multicut. -/
lemma add_nsmul_atom_eq_add_atom {s t : Multiset α} {a b : α} {n : ℕ}
    (h : s + n • ⦃a⦄ = t + ⦃b⦄) :
    (b = a ∧ 0 < n ∧ t = s + (n - 1) • ⦃a⦄) ∨ ∃ u, s = u + ⦃b⦄ ∧ t = u + n • ⦃a⦄ := by
  have hb : b ∈ s + n • ⦃a⦄ := by
    rw [h, add_atom_eq_cons]; exact mem_cons_self b t
  rcases mem_add.mp hb with hb | hb
  · obtain ⟨u, rfl⟩ := exists_cons_of_mem hb
    have h' : u + n • ⦃a⦄ + ⦃b⦄ = t + ⦃b⦄ := by
      rw [← h, ← add_atom_eq_cons]; abel
    exact .inr ⟨u, by rw [add_atom_eq_cons], (add_right_cancel h').symm⟩
  · have hab : b = a ∧ n ≠ 0 := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp at hb
      · constructor
        · have : b ∈ ⦃a⦄ := by
            have : n • (⦃a⦄ : Multiset α) = replicate n a := by
              simp [atom_eq_singleton, nsmul_singleton]
            rw [this] at hb
            simpa [atom_eq_singleton] using eq_of_mem_replicate hb
          simpa using this
        · omega
    obtain ⟨rfl, hn⟩ := hab
    have hsucc : n • (⦃b⦄ : Multiset α) = (n - 1) • ⦃b⦄ + ⦃b⦄ := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega]
      rw [succ_nsmul]
    have h' : s + (n - 1) • ⦃b⦄ + ⦃b⦄ = t + ⦃b⦄ := by
      rw [← h, hsucc]; abel
    exact .inl ⟨rfl, Nat.pos_of_ne_zero hn, (add_right_cancel h').symm⟩

/-- Locate a distinguished element in a sum of two contexts: if `s₁ + s₂ = t + ⦃a⦄` then
`a` occurs in `s₁` or in `s₂`. Used for the commutative cases of rules with two premises
that split the context. -/
lemma add_eq_add_atom {s₁ s₂ t : Multiset α} {a : α} (h : s₁ + s₂ = t + ⦃a⦄) :
    (∃ u, s₁ = u + ⦃a⦄ ∧ t = u + s₂) ∨ ∃ u, s₂ = u + ⦃a⦄ ∧ t = s₁ + u := by
  have ha : a ∈ s₁ + s₂ := by rw [h, add_atom_eq_cons]; exact mem_cons_self a t
  rcases mem_add.mp ha with ha | ha
  · obtain ⟨u, rfl⟩ := exists_cons_of_mem ha
    have h' : u + s₂ + ⦃a⦄ = t + ⦃a⦄ := by rw [← h, ← add_atom_eq_cons]; abel
    exact .inl ⟨u, by rw [add_atom_eq_cons], (add_right_cancel h').symm⟩
  · obtain ⟨u, rfl⟩ := exists_cons_of_mem ha
    have h' : s₁ + u + ⦃a⦄ = t + ⦃a⦄ := by rw [← h, ← add_atom_eq_cons]; abel
    exact .inr ⟨u, by rw [add_atom_eq_cons], (add_right_cancel h').symm⟩

/-- Distribute a block of `n` identical elements over a sum of two contexts: if
`s₁ + s₂ = t + n • ⦃a⦄` then the `n` copies of `a` can be apportioned between `s₁` and
`s₂`. Used for the multiplicative case of the persistent multicut, where a context split
divides the copies between the two premises. -/
lemma add_eq_add_nsmul_atom [DecidableEq α] {s₁ s₂ t : Multiset α} {a : α} {n : ℕ}
    (h : s₁ + s₂ = t + n • ⦃a⦄) :
    ∃ u₁ u₂ n₁ n₂, s₁ = u₁ + n₁ • ⦃a⦄ ∧ s₂ = u₂ + n₂ • ⦃a⦄ ∧ t = u₁ + u₂ ∧ n = n₁ + n₂ := by
  have hcount : ∀ b, s₁.count b + s₂.count b = t.count b + n * ⦃a⦄.count b := by
    intro b
    simpa [count_nsmul] using congrArg (count b) h
  have hn : min n (s₁.count a) + (n - min n (s₁.count a)) = n := by omega
  have hn₂ : n - min n (s₁.count a) ≤ s₂.count a := by
    have := hcount a
    simp [atom_eq_singleton] at this
    omega
  have h₁ : min n (s₁.count a) • ⦃a⦄ ≤ s₁ := le_iff_count.mpr fun b ↦ by
    by_cases hba : b = a
    · subst hba; simp [count_nsmul, atom_eq_singleton]
    · simp [atom_eq_singleton, hba]
  have h₂ : (n - min n (s₁.count a)) • ⦃a⦄ ≤ s₂ := le_iff_count.mpr fun b ↦ by
    by_cases hba : b = a
    · subst hba; simp [count_nsmul, atom_eq_singleton]; omega
    · simp [atom_eq_singleton, hba]
  have h₃ : t = s₁ - min n (s₁.count a) • ⦃a⦄ + (s₂ - (n - min n (s₁.count a)) • ⦃a⦄) := by
    ext b
    have hb := hcount b
    by_cases hba : b = a
    · subst hba
      simp only [count_sub, count_add, count_nsmul, atom_eq_singleton] at hb ⊢
      simp at hb ⊢
      omega
    · simp only [count_sub, count_add, count_nsmul, atom_eq_singleton] at hb ⊢
      simp [hba] at hb ⊢
      omega
  exact ⟨s₁ - min n (s₁.count a) • ⦃a⦄, s₂ - (n - min n (s₁.count a)) • ⦃a⦄,
    min n (s₁.count a), n - min n (s₁.count a),
    (Multiset.sub_add_cancel h₁).symm, (Multiset.sub_add_cancel h₂).symm, h₃, hn.symm⟩

/-- Restrict an explicit traversal, retaining the requested multiplicities. -/
def Traversal.restrict [DecidableEq α] {Γ Δ : Multiset α}
    (t : Γ.Traversal) (h : Δ ≤ Γ) : Δ.Traversal :=
  match t with
  | .zero => Traversal.zero.cast (le_antisymm (zero_le _) h)
  | .succ (s := Γ) A t =>
    if ha : A ∈ Δ then
      (t.restrict (Δ := Δ.erase A)
        (erase_le_iff_le_cons.mpr (by simpa [add_atom_eq_cons] using h))).succ A |>.cast (by
          simpa [add_atom_eq_cons] using cons_erase ha)
    else
      t.restrict ((le_cons_of_notMem ha).mp (by simpa [add_atom_eq_cons] using h))

end Multiset
