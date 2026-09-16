module

public import LinearLogic.LL.Propositional
public import LinearLogic.Vorspiel.Multiset

/-!
# Cut elimination for propositional linear logic

Structural cut elimination for $\mathbf{LL^0}$ following [Pfe12]: we introduce the
cut-free judgment `⇒! Γ` (the same rules as `⊢! Γ` minus `cut`, the `⇒` judgment of
[Pfe12] Section 1), prove that cut is admissible for cut-free derivations by a nested structural
induction ([Pfe12, Theorems 4 and 5]), and obtain cut elimination by a straightforward
induction replacing each `cut` by the admissible one ([Pfe12, Theorems 3 and 6]). The
main results are `hauptsatz`, its traditional phrasing `hauptsatz'` via the predicate
`Derivation.IsCutFree` (whose agreement with `⇒` is `cutFreeDerivable_iff`), and
`consistency`.

[Pfe12] works in a dyadic, two-sided intuitionistic calculus `Γ ; Δ ⊢ A` whose persistent
zone `Γ` makes contraction implicit. This file adapts the proof to the one-sided classical
`𝐋𝐋⁰`, where contraction on `？`-formulas is an explicit rule; consequently Pfenning's
persistent cut `cut!` becomes a *multicut* (`cutBang_admissible`), eliminating a promoted
`A` against `n` copies of `？∼A` at once, and the induction ordering flips from his
`cut! > cut` to `cut > cutBang` (see the docstrings below).

## References
- [Frank Pfenning, *Structural cut elimination in linear logic*][Pfe94]
- [Pfe12] Frank Pfenning, *Lecture notes on cut elimination*, 15-816 Linear Logic,
  Lecture 7, February 8, 2012.
  <https://www.cs.cmu.edu/~fp/courses/15816-s12/lectures/07-cutelim.pdf>
-/

@[expose] public section

namespace FFL.Propositional.LinearLogic

namespace Formula

/-- Number of connectives of a formula: the outermost measure of the nested induction for
cut admissibility — "first on the structure of `A`" in [Pfe12, Theorems 4 and 5]. -/
def complexity : Formula → ℕ
  |  atom _ => 0
  | natom _ => 0
  |   A ⨂ B => A.complexity + B.complexity + 1
  |   A ⅋ B => A.complexity + B.complexity + 1
  |   A ⨁ B => A.complexity + B.complexity + 1
  |  A ＆ B => A.complexity + B.complexity + 1
  |     ！A => A.complexity + 1
  |     ？A => A.complexity + 1

@[simp] lemma complexity_neg (A : Formula) : (∼A).complexity = A.complexity := by
  match A with
  |  atom X => rfl
  | natom X => rfl
  |   A ⨂ B => simp [complexity, complexity_neg A, complexity_neg B]
  |   A ⅋ B => simp [complexity, complexity_neg A, complexity_neg B]
  |   A ⨁ B => simp [complexity, complexity_neg A, complexity_neg B]
  |  A ＆ B => simp [complexity, complexity_neg A, complexity_neg B]
  |     ！A => simp [complexity, complexity_neg A]
  |     ？A => simp [complexity, complexity_neg A]

lemma IsQuest.exists_quest {A : Formula} (h : A.IsQuest) : ∃ B, A = ？B := by
  cases h with | @intro B => exact ⟨B, rfl⟩

end Formula

namespace LL

/-- Cut-free derivations: the rules of `Derivation` minus the cut rule. This is the `⇒`
judgment introduced in [Pfe12] Section 1 ("we write `Γ ; Δ ⇒ A` if we can prove `Γ ; Δ ⊢ A`
without the use of the cut or cut! rules").

- [Pfe12, Section 1] -/
inductive CutFree : Sequent → Type _
  /-- axiom  -/
  | ax (p : ℕ) : CutFree ⦃.atom p, .natom p⦄
  /-- structural rules -/
  | weakening : CutFree Γ → CutFree (Γ + ⦃？A⦄)
  | contraction : CutFree (Γ + ⦃？A⦄ + ⦃？A⦄) → CutFree (Γ + ⦃？A⦄)
  /-- multiplicative rules -/
  | tensor : CutFree (Γ + ⦃A⦄) → CutFree (Δ + ⦃B⦄) → CutFree (Γ + Δ + ⦃A ⨂ B⦄)
  | par : CutFree (Γ + ⦃A⦄ + ⦃B⦄) → CutFree (Γ + ⦃A ⅋ B⦄)
  /-- additive rules -/
  | plusLeft : CutFree (Γ + ⦃A⦄) → CutFree (Γ + ⦃A ⨁ B⦄)
  | plusRight : CutFree (Γ + ⦃B⦄) → CutFree (Γ + ⦃A ⨁ B⦄)
  | with : CutFree (Γ + ⦃A⦄) → CutFree (Γ + ⦃B⦄) → CutFree (Γ + ⦃A ＆ B⦄)
  /-- exponential rules -/
  | dereliction : CutFree (Γ + ⦃A⦄) → CutFree (Γ + ⦃？A⦄)
  | bang : CutFree (Γ + ⦃A⦄) → (_ : Sequent.IsQuest Γ := by simp) → CutFree (Γ + ⦃！A⦄)

scoped prefix:45 "⇒! " => CutFree

/-- Cut-free derivability. -/
abbrev CutFreeDerivable (Γ : Sequent) : Prop := Nonempty (CutFree Γ)

scoped prefix:45 "⇒ " => CutFreeDerivable

namespace CutFree

def cast (d : ⇒! Γ) (e : Γ = Δ := by abel) : ⇒! Δ := e ▸ d

def rotate (d : ⇒! ⦃A⦄ + Γ) : ⇒! Γ + ⦃A⦄ := d.cast

def swap (d : ⇒! ⦃A⦄ + ⦃B⦄) : ⇒! ⦃B⦄ + ⦃A⦄ := d.cast

/-- Height of a cut-free derivation: the innermost measure of the nested induction for
cut admissibility — "simultaneously on the structures of `D` and `E`" in [Pfe12,
Theorems 4 and 5]; we realize "one shrinks while the other stays fixed" as a decreasing
sum of heights. -/
def height : ⇒! Γ → ℕ
  |          ax _ => 0
  |   weakening d => d.height + 1
  | contraction d => d.height + 1
  |  tensor d₁ d₂ => max d₁.height d₂.height + 1
  |         par d => d.height + 1
  |    plusLeft d => d.height + 1
  |   plusRight d => d.height + 1
  |   .with d₁ d₂ => max d₁.height d₂.height + 1
  | dereliction d => d.height + 1
  |      bang d _ => d.height + 1

@[simp] lemma height_cast (d : ⇒! Γ) (e : Γ = Δ) : (d.cast e).height = d.height := by
  subst e; rfl

@[simp] lemma height_ax (p : ℕ) : (ax p).height = 0 := rfl
@[simp] lemma height_weakening {Γ : Sequent} {A : Formula} (d : ⇒! Γ) :
    (d.weakening (A := A)).height = d.height + 1 := rfl
@[simp] lemma height_contraction {Γ : Sequent} {A : Formula} (d : ⇒! Γ + ⦃？A⦄ + ⦃？A⦄) :
    d.contraction.height = d.height + 1 := rfl
@[simp] lemma height_tensor {Γ Δ : Sequent} {A B : Formula} (d₁ : ⇒! Γ + ⦃A⦄)
    (d₂ : ⇒! Δ + ⦃B⦄) : (d₁.tensor d₂).height = max d₁.height d₂.height + 1 := rfl
@[simp] lemma height_par {Γ : Sequent} {A B : Formula} (d : ⇒! Γ + ⦃A⦄ + ⦃B⦄) :
    d.par.height = d.height + 1 := rfl
@[simp] lemma height_plusLeft {Γ : Sequent} {A B : Formula} (d : ⇒! Γ + ⦃A⦄) :
    (d.plusLeft (B := B)).height = d.height + 1 := rfl
@[simp] lemma height_plusRight {Γ : Sequent} {A B : Formula} (d : ⇒! Γ + ⦃B⦄) :
    (d.plusRight (A := A)).height = d.height + 1 := rfl
@[simp] lemma height_with {Γ : Sequent} {A B : Formula} (d₁ : ⇒! Γ + ⦃A⦄)
    (d₂ : ⇒! Γ + ⦃B⦄) : (d₁.with d₂).height = max d₁.height d₂.height + 1 := rfl
@[simp] lemma height_dereliction {Γ : Sequent} {A : Formula} (d : ⇒! Γ + ⦃A⦄) :
    d.dereliction.height = d.height + 1 := rfl
@[simp] lemma height_bang {Γ : Sequent} {A : Formula} (d : ⇒! Γ + ⦃A⦄)
    (h : Sequent.IsQuest Γ) : (d.bang h).height = d.height + 1 := rfl

/-- Every cut-free derivation is a derivation — the remark after [Pfe12, Theorem 6]: "the
opposite implication also holds, because the exact proofs can be copied from the cut-free
to the system with cut". -/
def toDerivation : ⇒! Γ → ⊢! Γ
  |          ax p => .ax p
  |   weakening d => d.toDerivation.weakening
  | contraction d => d.toDerivation.contraction
  |  tensor d₁ d₂ => d₁.toDerivation.tensor d₂.toDerivation
  |         par d => d.toDerivation.par
  |    plusLeft d => d.toDerivation.plusLeft
  |   plusRight d => d.toDerivation.plusRight
  |   .with d₁ d₂ => d₁.toDerivation.with d₂.toDerivation
  | dereliction d => d.toDerivation.dereliction
  |      bang d h => d.toDerivation.bang h

end CutFree

/-! ### Structural helper lemmas

Weakening and contraction by a whole multiset of `？`-formulas, derived from the primitive
structural rules. These have no counterpart in [Pfe12]: there the persistent zone `Γ` of
the dyadic sequent absorbs them ("the persistent resources `Γ` are propagated from the
conclusion of all rules to all premises", Section 3). In the one-sided calculus they surface in
the `cutBang` cases, where [Pfe12]'s implicit zone duplication (`copy`) becomes explicit
contraction of the promotion context. -/

theorem CutFreeDerivable.wkQuests :
    ∀ (Θ : Sequent), Θ.IsQuest → ∀ {Γ : Sequent}, (⇒ Γ) → ⇒ Γ + Θ := by
  intro Θ
  induction Θ using Multiset.induction_on with
  | empty => intro _ Γ d; simpa using d
  | cons A Θ ih =>
    intro h Γ d
    rcases Sequent.IsQuest.cons.mp h with ⟨hA, hΘ⟩
    obtain ⟨B, rfl⟩ := hA.exists_quest
    rcases ih hΘ d with ⟨e⟩
    exact ⟨e.weakening.cast (by rw [← Multiset.add_atom_eq_cons]; abel)⟩

theorem CutFreeDerivable.ctrQuests :
    ∀ (Θ : Sequent), Θ.IsQuest → ∀ {Γ : Sequent}, (⇒ Γ + Θ + Θ) → ⇒ Γ + Θ := by
  intro Θ
  induction Θ using Multiset.induction_on with
  | empty => intro _ Γ d; simpa using d
  | cons A Θ ih =>
    intro h Γ d
    rcases Sequent.IsQuest.cons.mp h with ⟨hA, hΘ⟩
    obtain ⟨B, rfl⟩ := hA.exists_quest
    rcases d with ⟨e⟩
    have e' : ⇒ (Γ + ⦃？B⦄ + ⦃？B⦄) + Θ + Θ :=
      ⟨e.cast (by rw [← Multiset.add_atom_eq_cons]; abel)⟩
    rcases ih hΘ e' with ⟨f⟩
    exact ⟨((f.cast (show (Γ + ⦃？B⦄ + ⦃？B⦄) + Θ = Γ + Θ + ⦃？B⦄ + ⦃？B⦄ by abel)).contraction).cast
      (by rw [← Multiset.add_atom_eq_cons]; abel)⟩

/-! ### Cut admissibility

The heart of the development, [Pfe12, Theorem 5] (whose purely linear cases are [Pfe12,
Theorem 4]): cut and the persistent cut are admissible for cut-free derivations, by a
nested structural induction — "first on the structure of `A`, second on the order between
the two kinds of cut, and third simultaneously on the structures of `D` and `E`". The case
organization follows [Pfe12]: identity cases, principal cases, and commutative cases, plus
the copy case for the persistent cut. -/

deriving instance DecidableEq for Formula

/-- The last inference of the first premise of a cut, when it introduces the cut formula
by a non-exponential logical rule: the data of the premises of that inference. Passing
this view to `cutAuxR` lets the second premise be analyzed while remembering that the cut
formula is principal on the left — the situation of the principal cases of [Pfe12,
Theorem 4]. Exponential and identity principal cases are handled separately
(`cutBangAux`, `cutBangSwapAux`, and the `ax` case of `cutAux`). -/
inductive PrincipalView : Formula → Sequent → Type _
  | tensor : (⇒! Γ₁ + ⦃B⦄) → (⇒! Γ₂ + ⦃C⦄) → PrincipalView (B ⨂ C) (Γ₁ + Γ₂)
  | par : (⇒! Γ + ⦃B⦄ + ⦃C⦄) → PrincipalView (B ⅋ C) Γ
  | plusLeft : (⇒! Γ + ⦃B⦄) → PrincipalView (B ⨁ C) Γ
  | plusRight : (⇒! Γ + ⦃C⦄) → PrincipalView (B ⨁ C) Γ
  | with : (⇒! Γ + ⦃B⦄) → (⇒! Γ + ⦃C⦄) → PrincipalView (B ＆ C) Γ

mutual

/-- Workhorse for `cut_admissible`, with the sequent indices generalized so that the two
derivations can be analyzed by `cases`. The case organization is that of [Pfe12,
Theorems 4 and 5]: identity cases (`ax`), principal cases (the two last rules introduce
`A` and `∼A`), and commutative cases (the cut formula is a side formula of the last rule
of either premise, and the cut is pushed past it). -/
theorem cutAux {S₁ S₂ : Sequent} (d₁ : ⇒! S₁) (d₂ : ⇒! S₂) {Γ Δ : Sequent} {A : Formula}
    (h₁ : S₁ = Γ + ⦃A⦄) (h₂ : S₂ = Δ + ⦃∼A⦄) {k₁ k₂ : ℕ}
    (hk₁ : d₁.height = k₁ := by rfl) (_hk₂ : d₂.height = k₂ := by rfl) : ⇒ Γ + Δ := by
  cases d₁ with
  | ax p =>
    -- identity case of [Pfe12, Theorem 4]: the cut disappears outright
    rcases Multiset.add_atom_eq_add_atom h₁ with ⟨hA, hΓ⟩ | ⟨u, hu₁, hu₂⟩
    · subst hA; subst hΓ
      exact ⟨d₂.cast (h₂.trans (by simp; abel))⟩
    · obtain ⟨hA, rfl⟩ := Multiset.add_atom_eq_atom.mp hu₁.symm
      subst hA; subst hu₂
      exact ⟨d₂.cast (h₂.trans (by simp; abel))⟩
  | weakening d =>
    rename_i Γ' C
    rcases Multiset.add_atom_eq_add_atom h₁ with ⟨hA, hΓ⟩ | ⟨u, hu₁, hu₂⟩
    · -- principal `A = ？C`: hunt the dual promotion in the second premise
      subst hA; subst hΓ
      exact cutBangSwapAux d₂ d.weakening h₂
    · subst hu₂
      rcases cutAux (Γ := u) d d₂ hu₁ h₂ with ⟨e⟩
      exact ⟨e.weakening.cast (by abel)⟩
  | contraction d =>
    rename_i Γ' C
    rcases Multiset.add_atom_eq_add_atom h₁ with ⟨hA, hΓ⟩ | ⟨u, hu₁, hu₂⟩
    · subst hA; subst hΓ
      exact cutBangSwapAux d₂ d.contraction h₂
    · subst hu₂
      rcases cutAux (Γ := u + ⦃？C⦄ + ⦃？C⦄) d d₂ (by rw [hu₁]; abel) h₂ with ⟨e⟩
      have f : ⇒! (u + Δ) + ⦃？C⦄ + ⦃？C⦄ := e.cast (by abel)
      exact ⟨f.contraction.cast (by abel)⟩
  | tensor dl dr =>
    rename_i Γ₁ B Γ₂ C
    rcases Multiset.add_atom_eq_add_atom h₁ with ⟨hA, hΓ⟩ | ⟨u, hu₁, hu₂⟩
    · subst hA; subst hΓ
      exact cutAuxR d₂ (.tensor dl dr) h₂
    · subst hu₂
      rcases Multiset.add_eq_add_atom hu₁ with ⟨v, hv₁, hv₂⟩ | ⟨v, hv₁, hv₂⟩
      · rcases cutAux (Γ := v + ⦃B⦄) dl d₂ (by rw [hv₁]; abel) h₂ with ⟨e⟩
        have f : ⇒! (v + Δ) + ⦃B⦄ := e.cast (by abel)
        exact ⟨(f.tensor dr).cast (by rw [hv₂]; abel)⟩
      · rcases cutAux (Γ := v + ⦃C⦄) dr d₂ (by rw [hv₁]; abel) h₂ with ⟨e⟩
        have f : ⇒! (v + Δ) + ⦃C⦄ := e.cast (by abel)
        exact ⟨(dl.tensor f).cast (by rw [hv₂]; abel)⟩
  | par d =>
    rename_i Γ' B C
    rcases Multiset.add_atom_eq_add_atom h₁ with ⟨hA, hΓ⟩ | ⟨u, hu₁, hu₂⟩
    · subst hA; subst hΓ
      exact cutAuxR d₂ (.par d) h₂
    · -- commutative case: push the cut past `par` in the first premise
      subst hu₂
      rcases cutAux (Γ := u + ⦃B⦄ + ⦃C⦄) d d₂ (by rw [hu₁]; abel) h₂ with ⟨e⟩
      have f : ⇒! (u + Δ) + ⦃B⦄ + ⦃C⦄ := e.cast (by abel)
      exact ⟨f.par.cast (by abel)⟩
  | plusLeft d =>
    rename_i Γ' B C
    rcases Multiset.add_atom_eq_add_atom h₁ with ⟨hA, hΓ⟩ | ⟨u, hu₁, hu₂⟩
    · subst hA; subst hΓ
      exact cutAuxR d₂ (.plusLeft d) h₂
    · subst hu₂
      rcases cutAux (Γ := u + ⦃B⦄) d d₂ (by rw [hu₁]; abel) h₂ with ⟨e⟩
      have f : ⇒! (u + Δ) + ⦃B⦄ := e.cast (by abel)
      exact ⟨f.plusLeft.cast (by abel)⟩
  | plusRight d =>
    rename_i Γ' C B
    rcases Multiset.add_atom_eq_add_atom h₁ with ⟨hA, hΓ⟩ | ⟨u, hu₁, hu₂⟩
    · subst hA; subst hΓ
      exact cutAuxR d₂ (.plusRight d) h₂
    · subst hu₂
      rcases cutAux (Γ := u + ⦃C⦄) d d₂ (by rw [hu₁]; abel) h₂ with ⟨e⟩
      have f : ⇒! (u + Δ) + ⦃C⦄ := e.cast (by abel)
      exact ⟨f.plusRight.cast (by abel)⟩
  | «with» dl dr =>
    rename_i Γ' B C
    rcases Multiset.add_atom_eq_add_atom h₁ with ⟨hA, hΓ⟩ | ⟨u, hu₁, hu₂⟩
    · subst hA; subst hΓ
      exact cutAuxR d₂ (.with dl dr) h₂
    · subst hu₂
      rcases cutAux (Γ := u + ⦃B⦄) dl d₂ (by rw [hu₁]; abel) h₂ with ⟨e₁⟩
      rcases cutAux (Γ := u + ⦃C⦄) dr d₂ (by rw [hu₁]; abel) h₂ with ⟨e₂⟩
      have f₁ : ⇒! (u + Δ) + ⦃B⦄ := e₁.cast (by abel)
      have f₂ : ⇒! (u + Δ) + ⦃C⦄ := e₂.cast (by abel)
      exact ⟨(f₁.with f₂).cast (by abel)⟩
  | dereliction d =>
    rename_i Γ' C
    rcases Multiset.add_atom_eq_add_atom h₁ with ⟨hA, hΓ⟩ | ⟨u, hu₁, hu₂⟩
    · subst hA; subst hΓ
      exact cutBangSwapAux d₂ d.dereliction h₂
    · subst hu₂
      rcases cutAux (Γ := u + ⦃C⦄) d d₂ (by rw [hu₁]; abel) h₂ with ⟨e⟩
      have f : ⇒! (u + Δ) + ⦃C⦄ := e.cast (by abel)
      exact ⟨f.dereliction.cast (by abel)⟩
  | bang d hq =>
    rename_i Γ' B
    rcases Multiset.add_atom_eq_add_atom h₁ with ⟨hA, hΓ⟩ | ⟨u, hu₁, hu₂⟩
    · -- principal `A = ！B`: the reduction of [Pfe12] Section 3 turning a cut on `！B` into a
      -- persistent cut on `B`
      subst hA; subst hΓ
      exact cutBangAux (Δ := Δ) (A := B) (n := 1) d₂ hq d (h₂.trans (by simp [one_nsmul]))
    · -- `A` is a side formula of a promotion, hence a `？`-formula; hunt the dual
      -- promotion in the second premise
      subst hu₂
      have hAq : A.IsQuest := hq A (by rw [hu₁]; exact Multiset.mem_add.mpr (.inr (by simp)))
      obtain ⟨C, rfl⟩ := hAq.exists_quest
      exact cutBangSwapAux d₂ ((d.bang hq).cast (by rw [hu₁]; abel)) h₂
termination_by (A.complexity, 3, k₁ + k₂)
decreasing_by
  all_goals try subst_vars
  all_goals try simp [Prod.lex_def, Formula.complexity]
  all_goals omega

/-- Second phase of the linear principal cases of [Pfe12, Theorem 4]: the cut formula is
known to be introduced by the last non-exponential rule of the first premise, recorded in
`v`; analyze the second premise. Commutative cases push the cut past the last rule of
`d₂`; when `∼A` is principal in `d₂` as well, the principal reductions fire, cutting the
immediate subformulas via `cutAux` at strictly smaller cut formulas. -/
theorem cutAuxR {S₂ : Sequent} (d₂ : ⇒! S₂) {Γ Δ : Sequent} {A : Formula}
    (v : PrincipalView A Γ) (h₂ : S₂ = Δ + ⦃∼A⦄) {k₂ : ℕ}
    (hk₂ : d₂.height = k₂ := by rfl) : ⇒ Γ + Δ := by
  cases d₂ with
  | ax p =>
    rcases Multiset.add_atom_eq_add_atom h₂ with ⟨hA, hΔ⟩ | ⟨u, hu₁, hu₂⟩
    · have h : Formula.atom p = A := by simpa using congrArg (∼·) hA
      subst h; nomatch v
    · obtain ⟨hA, rfl⟩ := Multiset.add_atom_eq_atom.mp hu₁.symm
      have h : A = Formula.natom p := by simpa using congrArg (∼·) hA
      subst h; nomatch v
  | weakening d =>
    rename_i Δ' D
    rcases Multiset.add_atom_eq_add_atom h₂ with ⟨hA, hΔ⟩ | ⟨u, hu₁, hu₂⟩
    · have h : (！∼D : Formula) = A := by simpa using congrArg (∼·) hA
      subst h; nomatch v
    · subst hu₂
      rcases cutAuxR d v hu₁ with ⟨e⟩
      exact ⟨e.weakening.cast (by abel)⟩
  | contraction d =>
    rename_i Δ' D
    rcases Multiset.add_atom_eq_add_atom h₂ with ⟨hA, hΔ⟩ | ⟨u, hu₁, hu₂⟩
    · have h : (！∼D : Formula) = A := by simpa using congrArg (∼·) hA
      subst h; nomatch v
    · subst hu₂
      rcases cutAuxR (Δ := u + ⦃？D⦄ + ⦃？D⦄) d v (by rw [hu₁]; abel) with ⟨e⟩
      have f : ⇒! (Γ + u) + ⦃？D⦄ + ⦃？D⦄ := e.cast (by abel)
      exact ⟨f.contraction.cast (by abel)⟩
  | tensor el er =>
    rename_i Δ₁ B Δ₂ C
    rcases Multiset.add_atom_eq_add_atom h₂ with ⟨hA, hΔ⟩ | ⟨u, hu₁, hu₂⟩
    · -- principal reduction `⅋`/`⨂` (cf. the `⊸` reduction of [Pfe12] Section 2)
      have h : (∼B ⅋ ∼C : Formula) = A := by simpa using congrArg (∼·) hA
      subst h
      cases v with
      | par e =>
        rcases cutAux (Γ := Γ + ⦃∼C⦄) (Δ := Δ₁) (A := ∼B) e el (by abel) (by simp)
          with ⟨f⟩
        rcases cutAux (Γ := Γ + Δ₁) (Δ := Δ₂) (A := ∼C)
          (f.cast (by abel) : ⇒! (Γ + Δ₁) + ⦃∼C⦄) er rfl (by simp) with ⟨g⟩
        exact ⟨g.cast (by rw [← hΔ]; abel)⟩
    · subst hu₂
      rcases Multiset.add_eq_add_atom hu₁ with ⟨w, hw₁, hw₂⟩ | ⟨w, hw₁, hw₂⟩
      · rcases cutAuxR (Δ := w + ⦃B⦄) el v (by rw [hw₁]; abel) with ⟨e⟩
        have f : ⇒! (Γ + w) + ⦃B⦄ := e.cast (by abel)
        exact ⟨(f.tensor er).cast (by rw [hw₂]; abel)⟩
      · rcases cutAuxR (Δ := w + ⦃C⦄) er v (by rw [hw₁]; abel) with ⟨e⟩
        have f : ⇒! (Γ + w) + ⦃C⦄ := e.cast (by abel)
        exact ⟨(el.tensor f).cast (by rw [hw₂]; abel)⟩
  | par e =>
    rename_i Δ' B C
    rcases Multiset.add_atom_eq_add_atom h₂ with ⟨hA, hΔ⟩ | ⟨u, hu₁, hu₂⟩
    · have h : (∼B ⨂ ∼C : Formula) = A := by simpa using congrArg (∼·) hA
      subst h
      cases v with
      | tensor f₁ f₂ =>
        rename_i Γ₁ Γ₂
        rcases cutAux (Γ := Γ₁) (Δ := Δ' + ⦃C⦄) (A := ∼B) f₁
          (e.cast (by abel) : ⇒! (Δ' + ⦃C⦄) + ⦃B⦄) rfl (by simp) with ⟨f⟩
        rcases cutAux (Γ := Γ₂) (Δ := Γ₁ + Δ') (A := ∼C) f₂
          (f.cast (by abel) : ⇒! (Γ₁ + Δ') + ⦃C⦄) rfl (by simp) with ⟨g⟩
        exact ⟨g.cast (by rw [← hΔ]; abel)⟩
    · subst hu₂
      rcases cutAuxR (Δ := u + ⦃B⦄ + ⦃C⦄) e v (by rw [hu₁]; abel) with ⟨f⟩
      have g : ⇒! (Γ + u) + ⦃B⦄ + ⦃C⦄ := f.cast (by abel)
      exact ⟨g.par.cast (by abel)⟩
  | plusLeft e =>
    rename_i Δ' B C
    rcases Multiset.add_atom_eq_add_atom h₂ with ⟨hA, hΔ⟩ | ⟨u, hu₁, hu₂⟩
    · have h : (∼B ＆ ∼C : Formula) = A := by simpa using congrArg (∼·) hA
      subst h
      cases v with
      | «with» f₁ f₂ =>
        rcases cutAux (Γ := Γ) (Δ := Δ') (A := ∼B) f₁ e rfl (by simp) with ⟨f⟩
        exact ⟨f.cast (by rw [hΔ])⟩
    · subst hu₂
      rcases cutAuxR (Δ := u + ⦃B⦄) e v (by rw [hu₁]; abel) with ⟨f⟩
      exact ⟨((f.cast (by abel) : ⇒! (Γ + u) + ⦃B⦄).plusLeft).cast (by abel)⟩
  | plusRight e =>
    rename_i Δ' C B
    rcases Multiset.add_atom_eq_add_atom h₂ with ⟨hA, hΔ⟩ | ⟨u, hu₁, hu₂⟩
    · have h : (∼B ＆ ∼C : Formula) = A := by simpa using congrArg (∼·) hA
      subst h
      cases v with
      | «with» f₁ f₂ =>
        rcases cutAux (Γ := Γ) (Δ := Δ') (A := ∼C) f₂ e rfl (by simp) with ⟨f⟩
        exact ⟨f.cast (by rw [hΔ])⟩
    · subst hu₂
      rcases cutAuxR (Δ := u + ⦃C⦄) e v (by rw [hu₁]; abel) with ⟨f⟩
      exact ⟨((f.cast (by abel) : ⇒! (Γ + u) + ⦃C⦄).plusRight).cast (by abel)⟩
  | «with» e₁ e₂ =>
    rename_i Δ' B C
    rcases Multiset.add_atom_eq_add_atom h₂ with ⟨hA, hΔ⟩ | ⟨u, hu₁, hu₂⟩
    · have h : (∼B ⨁ ∼C : Formula) = A := by simpa using congrArg (∼·) hA
      subst h
      cases v with
      | plusLeft f =>
        rcases cutAux (Γ := Γ) (Δ := Δ') (A := ∼B) f e₁ rfl (by simp) with ⟨g⟩
        exact ⟨g.cast (by rw [hΔ])⟩
      | plusRight f =>
        rcases cutAux (Γ := Γ) (Δ := Δ') (A := ∼C) f e₂ rfl (by simp) with ⟨g⟩
        exact ⟨g.cast (by rw [hΔ])⟩
    · subst hu₂
      rcases cutAuxR (Δ := u + ⦃B⦄) e₁ v (by rw [hu₁]; abel) with ⟨f₁⟩
      rcases cutAuxR (Δ := u + ⦃C⦄) e₂ v (by rw [hu₁]; abel) with ⟨f₂⟩
      have g₁ : ⇒! (Γ + u) + ⦃B⦄ := f₁.cast (by abel)
      have g₂ : ⇒! (Γ + u) + ⦃C⦄ := f₂.cast (by abel)
      exact ⟨(g₁.with g₂).cast (by abel)⟩
  | dereliction e =>
    rename_i Δ' D
    rcases Multiset.add_atom_eq_add_atom h₂ with ⟨hA, hΔ⟩ | ⟨u, hu₁, hu₂⟩
    · have h : (！∼D : Formula) = A := by simpa using congrArg (∼·) hA
      subst h; nomatch v
    · subst hu₂
      rcases cutAuxR (Δ := u + ⦃D⦄) e v (by rw [hu₁]; abel) with ⟨f⟩
      exact ⟨((f.cast (by abel) : ⇒! (Γ + u) + ⦃D⦄).dereliction).cast (by abel)⟩
  | bang e hq' =>
    rename_i Δ' B
    rcases Multiset.add_atom_eq_add_atom h₂ with ⟨hA, hΔ⟩ | ⟨u, hu₁, hu₂⟩
    · have h : (？∼B : Formula) = A := by simpa using congrArg (∼·) hA
      subst h; nomatch v
    · -- `∼A` inside a promotion context would make `A` exponential, contradicting `v`
      have hq'' : (∼A).IsQuest := hq' (∼A) (by rw [hu₁]; simp)
      obtain ⟨E, hE⟩ := hq''.exists_quest
      have h : A = ！∼E := by simpa using congrArg (∼·) hE
      subst h; nomatch v
termination_by (A.complexity, 2, k₂)
decreasing_by
  all_goals simp_wf
  all_goals try subst_vars
  all_goals try simp [Prod.lex_def, Formula.complexity]
  all_goals omega

/-- Hunt for the promotion dual to a `？`-formula cut: the cut formula is `？C`, principal
or absorbed on the left, so `∼？C = ！∼C` is traced through the second premise until its
introducing promotion, where the persistent multicut `cutBangAux` takes over. Together
these realize the `(cut!_A)` cases of [Pfe12, Theorem 5] in the one-sided setting. -/
theorem cutBangSwapAux {S₂ : Sequent} (d₂ : ⇒! S₂) {Γ Δ : Sequent} {C : Formula}
    (d₁ : ⇒! Γ + ⦃？C⦄) (h₂ : S₂ = Δ + ⦃！∼C⦄) {k₂ : ℕ}
    (hk₂ : d₂.height = k₂ := by rfl) : ⇒ Γ + Δ := by
  cases d₂ with
  | ax p =>
    rcases Multiset.add_atom_eq_add_atom h₂ with ⟨hA, hΔ⟩ | ⟨u, hu₁, hu₂⟩
    · exact Formula.noConfusion hA
    · obtain ⟨hA, rfl⟩ := Multiset.add_atom_eq_atom.mp hu₁.symm
      exact Formula.noConfusion hA
  | weakening d =>
    rename_i Δ' D
    rcases Multiset.add_atom_eq_add_atom h₂ with ⟨hA, hΔ⟩ | ⟨u, hu₁, hu₂⟩
    · exact Formula.noConfusion hA
    · subst hu₂
      rcases cutBangSwapAux d d₁ hu₁ with ⟨e⟩
      exact ⟨e.weakening.cast (by abel)⟩
  | contraction d =>
    rename_i Δ' D
    rcases Multiset.add_atom_eq_add_atom h₂ with ⟨hA, hΔ⟩ | ⟨u, hu₁, hu₂⟩
    · exact Formula.noConfusion hA
    · subst hu₂
      rcases cutBangSwapAux (Δ := u + ⦃？D⦄ + ⦃？D⦄) d d₁ (by rw [hu₁]; abel) with ⟨e⟩
      have f : ⇒! (Γ + u) + ⦃？D⦄ + ⦃？D⦄ := e.cast (by abel)
      exact ⟨f.contraction.cast (by abel)⟩
  | tensor el er =>
    rename_i Δ₁ B Δ₂ D
    rcases Multiset.add_atom_eq_add_atom h₂ with ⟨hA, hΔ⟩ | ⟨u, hu₁, hu₂⟩
    · exact Formula.noConfusion hA
    · subst hu₂
      rcases Multiset.add_eq_add_atom hu₁ with ⟨w, hw₁, hw₂⟩ | ⟨w, hw₁, hw₂⟩
      · rcases cutBangSwapAux (Δ := w + ⦃B⦄) el d₁ (by rw [hw₁]; abel) with ⟨e⟩
        have f : ⇒! (Γ + w) + ⦃B⦄ := e.cast (by abel)
        exact ⟨(f.tensor er).cast (by rw [hw₂]; abel)⟩
      · rcases cutBangSwapAux (Δ := w + ⦃D⦄) er d₁ (by rw [hw₁]; abel) with ⟨e⟩
        have f : ⇒! (Γ + w) + ⦃D⦄ := e.cast (by abel)
        exact ⟨(el.tensor f).cast (by rw [hw₂]; abel)⟩
  | par e =>
    rename_i Δ' B D
    rcases Multiset.add_atom_eq_add_atom h₂ with ⟨hA, hΔ⟩ | ⟨u, hu₁, hu₂⟩
    · exact Formula.noConfusion hA
    · subst hu₂
      rcases cutBangSwapAux (Δ := u + ⦃B⦄ + ⦃D⦄) e d₁ (by rw [hu₁]; abel) with ⟨f⟩
      have g : ⇒! (Γ + u) + ⦃B⦄ + ⦃D⦄ := f.cast (by abel)
      exact ⟨g.par.cast (by abel)⟩
  | plusLeft e =>
    rename_i Δ' B D
    rcases Multiset.add_atom_eq_add_atom h₂ with ⟨hA, hΔ⟩ | ⟨u, hu₁, hu₂⟩
    · exact Formula.noConfusion hA
    · subst hu₂
      rcases cutBangSwapAux (Δ := u + ⦃B⦄) e d₁ (by rw [hu₁]; abel) with ⟨f⟩
      exact ⟨((f.cast (by abel) : ⇒! (Γ + u) + ⦃B⦄).plusLeft).cast (by abel)⟩
  | plusRight e =>
    rename_i Δ' D B
    rcases Multiset.add_atom_eq_add_atom h₂ with ⟨hA, hΔ⟩ | ⟨u, hu₁, hu₂⟩
    · exact Formula.noConfusion hA
    · subst hu₂
      rcases cutBangSwapAux (Δ := u + ⦃D⦄) e d₁ (by rw [hu₁]; abel) with ⟨f⟩
      exact ⟨((f.cast (by abel) : ⇒! (Γ + u) + ⦃D⦄).plusRight).cast (by abel)⟩
  | «with» e₁ e₂ =>
    rename_i Δ' B D
    rcases Multiset.add_atom_eq_add_atom h₂ with ⟨hA, hΔ⟩ | ⟨u, hu₁, hu₂⟩
    · exact Formula.noConfusion hA
    · subst hu₂
      rcases cutBangSwapAux (Δ := u + ⦃B⦄) e₁ d₁ (by rw [hu₁]; abel) with ⟨f₁⟩
      rcases cutBangSwapAux (Δ := u + ⦃D⦄) e₂ d₁ (by rw [hu₁]; abel) with ⟨f₂⟩
      have g₁ : ⇒! (Γ + u) + ⦃B⦄ := f₁.cast (by abel)
      have g₂ : ⇒! (Γ + u) + ⦃D⦄ := f₂.cast (by abel)
      exact ⟨(g₁.with g₂).cast (by abel)⟩
  | dereliction e =>
    rename_i Δ' D
    rcases Multiset.add_atom_eq_add_atom h₂ with ⟨hA, hΔ⟩ | ⟨u, hu₁, hu₂⟩
    · exact Formula.noConfusion hA
    · subst hu₂
      rcases cutBangSwapAux (Δ := u + ⦃D⦄) e d₁ (by rw [hu₁]; abel) with ⟨f⟩
      exact ⟨((f.cast (by abel) : ⇒! (Γ + u) + ⦃D⦄).dereliction).cast (by abel)⟩
  | bang e hq' =>
    rename_i Δ' B
    rcases Multiset.add_atom_eq_add_atom h₂ with ⟨hA, hΔ⟩ | ⟨u, hu₁, hu₂⟩
    · -- the promotion introducing `！∼C`: hand over to the persistent multicut,
      -- [Pfe12] Section 3's reduction of a cut on `！(∼C)` to a persistent cut on `∼C`
      have hB : B = ∼C := by simpa using hA
      subst hB
      rcases cutBangAux (Δ := Γ) (A := ∼C) (n := 1) d₁ hq' e (by simp [one_nsmul]) with ⟨f⟩
      exact ⟨f.cast (by rw [← hΔ]; abel)⟩
    · -- `！∼C` inside a promotion context is impossible
      have := hq' (！∼C) (by rw [hu₁]; simp)
      simp at this
termination_by (C.complexity + 1, 1, k₂)
decreasing_by
  all_goals simp_wf
  all_goals try subst_vars
  all_goals try simp [Prod.lex_def]
  all_goals omega

/-- Workhorse for `cutBang_admissible`, with the second sequent index generalized; the
persistent-cut cases of [Pfe12, Theorem 5]. The recursion analyzes `d₂` only: `d₁` is the
fixed promotable derivation, duplicated on demand — [Pfe12] Section 3: "we need two copies of
`D`, which is okay since `D` does not use any ephemeral resources". The copy case of
[Pfe12] appears as the dereliction case below, generating the nested persistent cut and
ordinary cut; contraction and weakening of a copy merely adjust the multiplicity `n`. -/
theorem cutBangAux {S₂ : Sequent} (d₂ : ⇒! S₂) {Γ Δ : Sequent} {A : Formula}
    (hΓ : Γ.IsQuest) (d₁ : ⇒! Γ + ⦃A⦄) {n : ℕ} (h₂ : S₂ = Δ + n • ⦃？∼A⦄) {k₂ : ℕ}
    (hk₂ : d₂.height = k₂ := by rfl) : ⇒ Γ + Δ := by
  rcases n with _ | n
  · -- no copies: [Pfe12]'s persistent cut with an unused persistent formula; weaken
    rcases CutFreeDerivable.wkQuests Γ hΓ ⟨d₂.cast (by simpa using h₂)⟩ with ⟨e⟩
    exact ⟨e.cast (by abel)⟩
  · cases d₂ with
    | ax p =>
      have hm : (？∼A : Formula) ∈ (⦃.atom p, .natom p⦄ : Sequent) := by
        rw [h₂, succ_nsmul]; simp
      simp only [Multiset.mem_add, Multiset.mem_atom_iff] at hm
      rcases hm with hm | hm <;> exact Formula.noConfusion hm
    | weakening d =>
      rename_i Δ' D
      rcases Multiset.add_nsmul_atom_eq_add_atom h₂.symm with ⟨hP, -, hctx⟩ | ⟨u, hΔ, hctx⟩
      · obtain rfl : D = ∼A := by simpa using hP
        simp only [Nat.add_sub_cancel] at hctx
        exact cutBangAux d hΓ d₁ hctx
      · subst hΔ
        rcases cutBangAux d hΓ d₁ hctx with ⟨e⟩
        exact ⟨e.weakening.cast (by abel)⟩
    | contraction d =>
      rename_i Δ' D
      rcases Multiset.add_nsmul_atom_eq_add_atom h₂.symm with ⟨hP, -, hctx⟩ | ⟨u, hΔ, hctx⟩
      · have hD : D = ∼A := by simpa using hP
        simp only [Nat.add_sub_cancel] at hctx
        exact cutBangAux (n := n + 1 + 1) d hΓ d₁
          (by rw [hD, hctx, succ_nsmul, succ_nsmul]; abel)
      · subst hΔ
        rcases cutBangAux (Δ := u + ⦃？D⦄ + ⦃？D⦄) d hΓ d₁ (by rw [hctx]; abel) with ⟨e⟩
        have f : ⇒! (Γ + u) + ⦃？D⦄ + ⦃？D⦄ := e.cast (by abel)
        exact ⟨f.contraction.cast (by abel)⟩
    | dereliction d =>
      rename_i Δ' D
      rcases Multiset.add_nsmul_atom_eq_add_atom h₂.symm with ⟨hP, -, hctx⟩ | ⟨u, hΔ, hctx⟩
      · -- the copy case of [Pfe12] Section 3: two nested cuts, `cutBangAux` on the subderivation
        -- and `cutAux` on the strictly smaller formula `A`, then contract `Γ`
        have hD : D = ∼A := by simpa using hP
        simp only [Nat.add_sub_cancel] at hctx
        rcases cutBangAux (Δ := Δ + ⦃∼A⦄) d hΓ d₁ (by rw [hD, hctx]; abel) with ⟨e⟩
        rcases cutAux (Γ := Γ) (Δ := Γ + Δ) d₁
          (e.cast (by abel) : ⇒! (Γ + Δ) + ⦃∼A⦄) rfl rfl with ⟨f⟩
        rcases CutFreeDerivable.ctrQuests Γ hΓ (Γ := Δ) ⟨f.cast (by abel)⟩ with ⟨g⟩
        exact ⟨g.cast (by abel)⟩
      · subst hΔ
        rcases cutBangAux (Δ := u + ⦃D⦄) d hΓ d₁ (by rw [hctx]; abel) with ⟨e⟩
        exact ⟨((e.cast (by abel) : ⇒! (Γ + u) + ⦃D⦄).dereliction).cast (by abel)⟩
    | tensor el er =>
      rename_i Δ₁ B Δ₂ D
      rcases Multiset.add_nsmul_atom_eq_add_atom h₂.symm with ⟨hP, -, -⟩ | ⟨u, hΔ, hctx⟩
      · exact Formula.noConfusion hP
      · subst hΔ
        obtain ⟨u₁, u₂, n₁, n₂, hs₁, hs₂, hu, -⟩ := Multiset.add_eq_add_nsmul_atom hctx
        rcases cutBangAux (Δ := u₁ + ⦃B⦄) (n := n₁) el hΓ d₁ (by rw [hs₁]; abel) with ⟨e₁⟩
        rcases cutBangAux (Δ := u₂ + ⦃D⦄) (n := n₂) er hΓ d₁ (by rw [hs₂]; abel) with ⟨e₂⟩
        have f : ⇒! (Γ + u₁) + (Γ + u₂) + ⦃B ⨂ D⦄ :=
          (e₁.cast (by abel)).tensor (e₂.cast (by abel))
        rcases CutFreeDerivable.ctrQuests Γ hΓ (Γ := u₁ + u₂ + ⦃B ⨂ D⦄)
          ⟨f.cast (by abel)⟩ with ⟨g⟩
        exact ⟨g.cast (by rw [hu]; abel)⟩
    | par d =>
      rename_i Δ' B D
      rcases Multiset.add_nsmul_atom_eq_add_atom h₂.symm with ⟨hP, -, -⟩ | ⟨u, hΔ, hctx⟩
      · exact Formula.noConfusion hP
      · subst hΔ
        rcases cutBangAux (Δ := u + ⦃B⦄ + ⦃D⦄) d hΓ d₁ (by rw [hctx]; abel) with ⟨e⟩
        have f : ⇒! (Γ + u) + ⦃B⦄ + ⦃D⦄ := e.cast (by abel)
        exact ⟨f.par.cast (by abel)⟩
    | plusLeft d =>
      rename_i Δ' B D
      rcases Multiset.add_nsmul_atom_eq_add_atom h₂.symm with ⟨hP, -, -⟩ | ⟨u, hΔ, hctx⟩
      · exact Formula.noConfusion hP
      · subst hΔ
        rcases cutBangAux (Δ := u + ⦃B⦄) d hΓ d₁ (by rw [hctx]; abel) with ⟨e⟩
        exact ⟨((e.cast (by abel) : ⇒! (Γ + u) + ⦃B⦄).plusLeft).cast (by abel)⟩
    | plusRight d =>
      rename_i Δ' D B
      rcases Multiset.add_nsmul_atom_eq_add_atom h₂.symm with ⟨hP, -, -⟩ | ⟨u, hΔ, hctx⟩
      · exact Formula.noConfusion hP
      · subst hΔ
        rcases cutBangAux (Δ := u + ⦃D⦄) d hΓ d₁ (by rw [hctx]; abel) with ⟨e⟩
        exact ⟨((e.cast (by abel) : ⇒! (Γ + u) + ⦃D⦄).plusRight).cast (by abel)⟩
    | «with» dl dr =>
      rename_i Δ' B D
      rcases Multiset.add_nsmul_atom_eq_add_atom h₂.symm with ⟨hP, -, -⟩ | ⟨u, hΔ, hctx⟩
      · exact Formula.noConfusion hP
      · subst hΔ
        rcases cutBangAux (Δ := u + ⦃B⦄) dl hΓ d₁ (by rw [hctx]; abel) with ⟨e₁⟩
        rcases cutBangAux (Δ := u + ⦃D⦄) dr hΓ d₁ (by rw [hctx]; abel) with ⟨e₂⟩
        have f₁ : ⇒! (Γ + u) + ⦃B⦄ := e₁.cast (by abel)
        have f₂ : ⇒! (Γ + u) + ⦃D⦄ := e₂.cast (by abel)
        exact ⟨(f₁.with f₂).cast (by abel)⟩
    | bang d hq' =>
      -- the promotion case: the copies are absorbed into the promotion context, and the
      -- result can be re-promoted since both contexts are `？`-multisets — the very case
      -- the persistent zone of [Pfe12] (here: the multicut) exists to make structural
      rename_i Δ' B
      rcases Multiset.add_nsmul_atom_eq_add_atom h₂.symm with ⟨hP, -, -⟩ | ⟨u, hΔ, hctx⟩
      · exact Formula.noConfusion hP
      · subst hΔ
        rcases cutBangAux (Δ := u + ⦃B⦄) d hΓ d₁ (by rw [hctx]; abel) with ⟨e⟩
        have hu : (Γ + u).IsQuest := by
          intro x hx
          rcases Multiset.mem_add.mp hx with hx | hx
          · exact hΓ x hx
          · exact hq' x (by rw [hctx]; exact Multiset.mem_add.mpr (.inl hx))
        exact ⟨((e.cast (by abel) : ⇒! (Γ + u) + ⦃B⦄).bang hu).cast (by abel)⟩
termination_by (A.complexity + 1, 0, k₂)
decreasing_by
  all_goals simp_wf
  all_goals try subst_vars
  all_goals try simp [Prod.lex_def]
  all_goals omega

end

/-- The cut rule is admissible for cut-free derivations: the `(cut_A)` half of [Pfe12,
Theorem 5]; its non-exponential cases are exactly [Pfe12, Theorem 4] (Admissibility of Cut
for the purely linear sequent calculus).

- [Pfe12, Theorem 4, Theorem 5] -/
theorem cut_admissible (d₁ : ⇒! Γ + ⦃A⦄) (d₂ : ⇒! Δ + ⦃∼A⦄) : ⇒ Γ + Δ :=
  cutAux d₁ d₂ rfl rfl

/-- The persistent (multi)cut is admissible for cut-free derivations: the `(cut!_A)` half
of [Pfe12, Theorem 5], adapted to the one-sided calculus. Pfenning's
`Γ ; · ⇒ A  and  Γ, A ; Δ ⇒ C  imply  Γ ; Δ ⇒ C` becomes: a promotable `A` (context `Γ`
all-`？`) may be cut against `n` copies of `？∼A` at once. The multiplicity `n` replaces
the persistent zone: where [Pfe12]'s copy case regenerates the persistent formula, here
contraction on `？∼A` bumps `n` while the derivation shrinks. Consequently the ordering of
the two cut kinds *flips* relative to [Pfe12] (`cut! > cut` there): here `cut`'s principal
`！`-case dispatches to `cutBang` at the same cut formula, while `cutBang`'s dereliction
case — the analogue of [Pfe12]'s copy case, which generates the problematic second cut —
calls `cut` at the strictly smaller formula `A`.

- [Pfe12, Theorem 5] -/
theorem cutBang_admissible (hΓ : Γ.IsQuest) (d₁ : ⇒! Γ + ⦃A⦄) {n : ℕ}
    (d₂ : ⇒! Δ + n • ⦃？∼A⦄) : ⇒ Γ + Δ :=
  cutBangAux d₂ hΓ d₁ rfl

/-- **Cut elimination** (Hauptsatz) for `𝐋𝐋⁰`: every derivable sequent has a cut-free
derivation. This is [Pfe12, Theorem 6] (and Theorem 1), by the argument of [Pfe12,
Theorem 3]: a straightforward induction over the given derivation, appealing to the
admissibility of cut in the case of `cut`.

- [Pfe12, Theorem 1, Theorem 3, Theorem 6] -/
theorem hauptsatz : ∀ {Γ : Sequent}, ⊢! Γ → ⇒ Γ
  | _,          .ax p => ⟨.ax p⟩
  | _,     .cut d₁ d₂ =>
    have ⟨e₁⟩ := hauptsatz d₁
    have ⟨e₂⟩ := hauptsatz d₂
    cut_admissible e₁ e₂
  | _,   .weakening d => have ⟨e⟩ := hauptsatz d; ⟨e.weakening⟩
  | _, .contraction d => have ⟨e⟩ := hauptsatz d; ⟨e.contraction⟩
  | _,  .tensor d₁ d₂ =>
    have ⟨e₁⟩ := hauptsatz d₁
    have ⟨e₂⟩ := hauptsatz d₂
    ⟨e₁.tensor e₂⟩
  | _,         .par d => have ⟨e⟩ := hauptsatz d; ⟨e.par⟩
  | _,    .plusLeft d => have ⟨e⟩ := hauptsatz d; ⟨e.plusLeft⟩
  | _,   .plusRight d => have ⟨e⟩ := hauptsatz d; ⟨e.plusRight⟩
  | _,   .with d₁ d₂ =>
    have ⟨e₁⟩ := hauptsatz d₁
    have ⟨e₂⟩ := hauptsatz d₂
    ⟨e₁.with e₂⟩
  | _, .dereliction d => have ⟨e⟩ := hauptsatz d; ⟨e.dereliction⟩
  | _,     .bang d hq => have ⟨e⟩ := hauptsatz d; ⟨e.bang hq⟩

/-! ### Adequacy of the cut-free judgment

`CutFree` is, by construction, `Derivation` with the `cut` constructor removed. To make
the correspondence with the informal reading of [Pfe12] Section 1 — "`Γ ⇒` iff `Γ` is provable
*without the use of the cut rule*" — explicit, we also record cut-freeness as a predicate
on ordinary derivations, and prove that a sequent is `CutFree`-derivable iff it has an
ordinary derivation none of whose nodes is a `cut`. -/

/-- Cut-freeness as a predicate on ordinary derivations: no node of the derivation tree
is a `cut`. This is the direct formalization of the informal notion; compare
`FirstOrder.Derivation.IsCutFree` in Foundation. -/
inductive Derivation.IsCutFree : {Γ : Sequent} → (⊢! Γ) → Prop
  | ax (p : ℕ) : IsCutFree (.ax p)
  | weakening {d : ⊢! Γ} : IsCutFree d → IsCutFree (d.weakening (A := A))
  | contraction {d : ⊢! Γ + ⦃？A⦄ + ⦃？A⦄} : IsCutFree d → IsCutFree d.contraction
  | tensor {d₁ : ⊢! Γ + ⦃A⦄} {d₂ : ⊢! Δ + ⦃B⦄} :
      IsCutFree d₁ → IsCutFree d₂ → IsCutFree (d₁.tensor d₂)
  | par {d : ⊢! Γ + ⦃A⦄ + ⦃B⦄} : IsCutFree d → IsCutFree d.par
  | plusLeft {d : ⊢! Γ + ⦃A⦄} : IsCutFree d → IsCutFree (d.plusLeft (B := B))
  | plusRight {d : ⊢! Γ + ⦃B⦄} : IsCutFree d → IsCutFree (d.plusRight (A := A))
  | with {d₁ : ⊢! Γ + ⦃A⦄} {d₂ : ⊢! Γ + ⦃B⦄} :
      IsCutFree d₁ → IsCutFree d₂ → IsCutFree (d₁.with d₂)
  | dereliction {d : ⊢! Γ + ⦃A⦄} : IsCutFree d → IsCutFree d.dereliction
  | bang {d : ⊢! Γ + ⦃A⦄} (h : Γ.IsQuest) : IsCutFree d → IsCutFree (d.bang h)

/-- The embedding of cut-free derivations into ordinary derivations produces derivations
without `cut` nodes. -/
lemma CutFree.isCutFree_toDerivation : ∀ {Γ : Sequent} (e : ⇒! Γ),
    e.toDerivation.IsCutFree
  | _,          .ax p => .ax p
  | _,   .weakening e => .weakening e.isCutFree_toDerivation
  | _, .contraction e => .contraction e.isCutFree_toDerivation
  | _,  .tensor e₁ e₂ => .tensor e₁.isCutFree_toDerivation e₂.isCutFree_toDerivation
  | _,         .par e => .par e.isCutFree_toDerivation
  | _,    .plusLeft e => .plusLeft e.isCutFree_toDerivation
  | _,   .plusRight e => .plusRight e.isCutFree_toDerivation
  | _,    .with e₁ e₂ => .with e₁.isCutFree_toDerivation e₂.isCutFree_toDerivation
  | _, .dereliction e => .dereliction e.isCutFree_toDerivation
  | _,     .bang e hq => .bang hq e.isCutFree_toDerivation

/-- Conversely, an ordinary derivation without `cut` nodes yields a cut-free
derivation. -/
lemma CutFreeDerivable.of_isCutFree {Γ : Sequent} {d : ⊢! Γ} (h : d.IsCutFree) : ⇒ Γ := by
  induction h with
  | ax p => exact ⟨.ax p⟩
  | weakening _ ih => rcases ih with ⟨e⟩; exact ⟨e.weakening⟩
  | contraction _ ih => rcases ih with ⟨e⟩; exact ⟨e.contraction⟩
  | tensor _ _ ih₁ ih₂ => rcases ih₁ with ⟨e₁⟩; rcases ih₂ with ⟨e₂⟩; exact ⟨e₁.tensor e₂⟩
  | par _ ih => rcases ih with ⟨e⟩; exact ⟨e.par⟩
  | plusLeft _ ih => rcases ih with ⟨e⟩; exact ⟨e.plusLeft⟩
  | plusRight _ ih => rcases ih with ⟨e⟩; exact ⟨e.plusRight⟩
  | «with» _ _ ih₁ ih₂ => rcases ih₁ with ⟨e₁⟩; rcases ih₂ with ⟨e₂⟩; exact ⟨e₁.with e₂⟩
  | dereliction _ ih => rcases ih with ⟨e⟩; exact ⟨e.dereliction⟩
  | bang hq _ ih => rcases ih with ⟨e⟩; exact ⟨e.bang hq⟩

/-- **Adequacy**: a sequent is cut-freely derivable iff some ordinary derivation of it
contains no `cut` node. This pins the judgment `⇒` of the formalization to the informal
definition of cut-freeness. -/
lemma cutFreeDerivable_iff {Γ : Sequent} : (⇒ Γ) ↔ ∃ d : ⊢! Γ, d.IsCutFree :=
  ⟨fun ⟨e⟩ ↦ ⟨e.toDerivation, e.isCutFree_toDerivation⟩,
    fun ⟨_, h⟩ ↦ CutFreeDerivable.of_isCutFree h⟩

/-- **Cut elimination**, in its traditional phrasing: every derivable sequent has a
derivation that nowhere uses the cut rule.

- [Pfe12, Theorem 6] -/
theorem hauptsatz' {Γ : Sequent} (d : ⊢! Γ) : ∃ d' : ⊢! Γ, d'.IsCutFree :=
  cutFreeDerivable_iff.mp (hauptsatz d)

/-! ### Consequences -/

lemma CutFree.ne_zero : ∀ {Γ : Sequent}, ⇒! Γ → Γ ≠ 0 := by
  intro Γ d
  induction d <;> simp [Multiset.add_atom_eq_cons]

/-- **Consistency**: the empty sequent is not derivable — the analogue of [Pfe12,
Corollary 7] for the one-sided calculus (there: `⊬ 0`; here `𝐋𝐋⁰` has no units, so the
empty sequent plays the role of an unprovable conclusion): by cut elimination a derivation
could be assumed cut-free, but every cut-free rule concludes a nonempty sequent.

- [Pfe12, Corollary 7] -/
theorem consistency : ¬⊢ (0 : Sequent) := by
  rintro ⟨d⟩
  rcases hauptsatz d with ⟨e⟩
  exact e.ne_zero rfl

end LL

end FFL.Propositional.LinearLogic

end
