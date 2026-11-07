/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe03_BackwardProofs_Demo


/- # LoVe Exercise 3: Backward Proofs

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe

namespace BackwardProofs


/- ## Question 1: Connectives and Quantifiers

1.1. Carry out the following proofs using basic tactics such as `intro`,
`apply`, and `exact`.

Hint: Some strategies for carrying out such proofs are described at the end of
Section 3.3 in the Hitchhiker's Guide. -/

theorem I (a : Prop) :
    a → a :=
  by
    intro n
    exact n

theorem K (a b : Prop) :
    a → b → b :=
  by
    intro _ m
    exact m

theorem C (a b c : Prop) :
    (a → b → c) → b → a → c :=
  by
    intro f m n
    exact f n m

theorem proj_fst (a : Prop) :
    a → a → a :=
  by
    intro n _
    exact n

/- Please give a different answer than for `proj_fst`: -/

theorem proj_snd (a : Prop) :
    a → a → a :=
  by
    intro _ n
    exact n

theorem some_nonsense (a b c : Prop) :
    (a → b → c) → a → (a → c) → b → c :=
  by
    intro _ n g _
    exact g n

/- 1.2. Prove the contraposition rule using basic tactics. -/

theorem contrapositive (a b : Prop) :
    (a → b) → ¬ b → ¬ a :=
  by
    intro f not_b a
    apply not_b
    exact f a

/- 1.3. Prove the distributivity of `∀` over `∧` using basic tactics.

Hint: This exercise is tricky, especially the right-to-left direction. Some
forward reasoning, like in the proof of `and_swap_braces` in the lecture, might
be necessary. -/

theorem forall_and {α : Type} (p q : α → Prop) :
    (∀x, p x ∧ q x) ↔ (∀x, p x) ∧ (∀x, q x) :=
  by
    apply Iff.intro
    { intro f
      apply And.intro
      { intro x
        have ⟨ h, _ ⟩ := f x
        exact h }
      { intro x
        have ⟨ _, h ⟩ := f x
        exact h } }
    { intro h x
      have ⟨ hl, hr ⟩ := h
      apply And.intro
      { exact hl x }
      { exact hr x } }


/- ## Question 2: Natural Numbers

2.1. Prove the following recursive equations on the first argument of the
`mul` operator defined in lecture 1. -/

#check mul

theorem mul_zero (n : ℕ) :
    mul 0 n = 0 :=
  by
    induction n with
    | zero => rfl
    | succ k ih =>
      simp [mul, ih]
      ac_rfl

#check add_succ
theorem mul_succ (m n : ℕ) :
    mul (Nat.succ m) n = add (mul m n) n :=
  by
    induction n with
    | zero => simp [mul, add]
    | succ k ih => simp [mul, add, add_succ, ih, add_assoc]

/- 2.2. Prove commutativity and associativity of multiplication using the
`induction` tactic. Choose the induction variable carefully. -/

theorem mul_comm (m n : ℕ) :
    mul m n = mul n m :=
  by
    induction m with
    | zero => simp [mul, mul_zero]
    | succ k ih => simp [mul_succ, mul, ih, add_comm]

theorem mul_assoc (l m n : ℕ) :
    mul (mul l m) n = mul l (mul m n) :=
  by
    induction n with
    | zero => rfl
    | succ k ih => simp [mul_comm _ (k + 1), mul_succ, mul_add, mul_comm k, ih]

/- 2.3. Prove the symmetric variant of `mul_add` using `rw`. To apply
commutativity at a specific position, instantiate the rule by passing some
arguments (e.g., `mul_comm _ l`). -/

theorem add_mul (l m n : ℕ) :
    mul (add l m) n = add (mul n l) (mul n m) :=
  by
    induction n with
    | zero => simp [mul, mul_zero, add]
    | succ k ih => simp [mul_comm _ (k + 1), mul_add]


/- ## Question 3 (**optional**): Intuitionistic Logic

Intuitionistic logic is extended to classical logic by assuming a classical
axiom. There are several possibilities for the choice of axiom. In this
question, we are concerned with the logical equivalence of three different
axioms: -/

def ExcludedMiddle : Prop :=
  ∀a : Prop, a ∨ ¬ a

def Peirce : Prop :=
  ∀a b : Prop, ((a → b) → a) → a

def DoubleNegation : Prop :=
  ∀a : Prop, (¬¬ a) → a

/- For the proofs below, avoid using theorems from Lean's `Classical` namespace.

3.1 (**optional**). Prove the following implication using tactics.

Hint: You will need `Or.elim` and `False.elim`. You can use
`rw [ExcludedMiddle]` to unfold the definition of `ExcludedMiddle`,
and similarly for `Peirce`. -/

theorem Peirce_of_EM :
    ExcludedMiddle → Peirce :=
  by
    intro excluded_middle a b f
    apply Or.elim (excluded_middle a)
    { intro
      assumption }
    { intro not_a
      apply f
      intro n
      apply False.elim
      exact not_a n }

/- 3.2 (**optional**). Prove the following implication using tactics. -/

theorem DN_of_Peirce :
    Peirce → DoubleNegation :=
  by
    intro peirce a not_not_a
    apply peirce a False
    intro not_a
    apply False.elim
    apply not_not_a
    exact not_a

/- We leave the remaining implication for the homework: -/

namespace SorryTheorems

theorem not_or {a b : Prop} (h : ¬(a ∨ b)) :
    ¬a ∧ ¬b :=
  by
    apply And.intro
    { intro n
      apply h
      apply Or.intro_left
      exact n }
    { intro n
      apply h
      apply Or.intro_right
      exact n }

theorem EM_of_DN :
    DoubleNegation → ExcludedMiddle :=
  by
    intro double_negation a
    apply double_negation (a ∨ ¬a)
    intro h
    have ⟨not_a, not_not_a⟩ := not_or h
    have n := double_negation a not_not_a
    exact not_a n

end SorryTheorems

end BackwardProofs

end LoVe
