/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe03_BackwardProofs_ExerciseSheet


/- # LoVe Homework 4 (10 points): Forward Proofs

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1 (4 points): Logic Puzzles

Consider the following tactical proof: -/

theorem about_Impl :
    ∀a b : Prop, ¬ a ∨ b → a → b :=
  by
    intros a b hor ha
    apply Or.elim hor
    { intro hna
      apply False.elim
      apply hna
      exact ha }
    { intro hb
      exact hb }

/- 1.1 (2 points). Prove the same theorem again, this time by providing a proof
term.

Hint: There is an easy way. -/

theorem about_Impl_term :
    ∀a b : Prop, ¬ a ∨ b → a → b :=
  fun _ _ h_or x ↦
    match h_or with
    | Or.inl not_a => False.elim (not_a x)
    | Or.inr b => b

/- 1.2 (2 points). Prove the same theorem again, this time by providing a
structured proof, with `fix`, `assume`, and `show`. -/

theorem about_Impl_struct :
    ∀a b : Prop, ¬ a ∨ b → a → b :=
  fix a : Prop
  fix b : Prop
  fix h_or : ¬a ∨ b
  fix x : a
  show b from
    match h_or with
    | Or.inl not_a => False.elim (not_a x)
    | Or.inr y => y


/- ## Question 2 (6 points): Connectives and Quantifiers

2.1 (3 points). Supply a structured proof of the commutativity of `∨` under a
`∀` quantifier, using no other theorems than the introduction and elimination
rules for `∀`, `∨`, and `↔`. -/

theorem Or_comm_under_All {α : Type} (p q : α → Prop) :
    (∀x, p x ∨ q x) ↔ (∀x, q x ∨ p x) :=
  Iff.intro
    ( fix f : ∀x, p x ∨ q x
      fix x : α
      show q x ∨ p x from
        match f x with
        | Or.inl p_x => Or.inr p_x
        | Or.inr q_x => Or.inl q_x)
    ( fix f : ∀x, q x ∨ p x
      fix x : α
      show p x ∨ q x from
        match f x with
        | Or.inl q_x => Or.inr q_x
        | Or.inr p_x => Or.inl p_x)

/- 2.2 (3 points). We have proved or stated three of the six possible
implications between `ExcludedMiddle`, `Peirce`, and `DoubleNegation` in the
exercise of lecture 3. Prove the three missing implications using structured
proofs, exploiting the three theorems we already have. -/

namespace BackwardProofs

#check Peirce_of_EM
#check DN_of_Peirce
#check SorryTheorems.EM_of_DN

theorem Peirce_of_DN :
    DoubleNegation → Peirce :=
  fix dn : DoubleNegation
  have em : ExcludedMiddle := SorryTheorems.EM_of_DN dn
  show Peirce from
    Peirce_of_EM em

theorem EM_of_Peirce :
    Peirce → ExcludedMiddle :=
  fix peirce : Peirce
  have dn : DoubleNegation := DN_of_Peirce peirce
  show ExcludedMiddle from
    SorryTheorems.EM_of_DN dn

theorem DN_of_EM :
    ExcludedMiddle → DoubleNegation :=
  fix em : ExcludedMiddle
  have peirce : Peirce := Peirce_of_EM em
  show DoubleNegation from
    DN_of_Peirce peirce

end BackwardProofs

end LoVe
