/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe03_BackwardProofs_ExerciseSheet


/- # LoVe Homework 3 (10 points): Backward Proofs

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe

namespace BackwardProofs


/- ## Question 1 (5 points): Connectives and Quantifiers

1.1 (4 points). Complete the following proofs using basic tactics such as
`intro`, `apply`, and `exact`.

Hint: Some strategies for carrying out such proofs are described at the end of
Section 3.3 in the Hitchhiker's Guide. -/

theorem B (a b c : Prop) :
    (a → b) → (c → a) → c → b :=
  by
    intro f g x
    exact f (g x)

theorem S (a b c : Prop) :
    (a → b → c) → (a → b) → a → c :=
  by
    intro f g x
    exact f x (g x)

theorem more_nonsense (a b c d : Prop) :
    ((a → b) → c → d) → c → b → d :=
  by
    intro f x y
    exact f (fun _ => y) x

theorem even_more_nonsense (a b c : Prop) :
    (a → b) → (a → c) → a → b → c :=
  by
    intro _ g x _
    exact g x

/- 1.2 (1 point). Prove the following theorem using basic tactics. -/

theorem weak_peirce (a b : Prop) :
    ((((a → b) → a) → a) → b) → b :=
  by
    intro f
    apply f
    intro g
    apply g
    intro x
    apply f
    intro
    exact x


/- ## Question 2 (5 points): Logical Connectives

2.1 (1 point). Prove the following property about double negation using basic
tactics.

Hints:

* Keep in mind that `¬ a` is defined as `a → False`. You can start by invoking
  `simp [Not]` if this helps you.

* You will need to apply the elimination rule for `False` at a key point in the
  proof. -/

theorem herman (a : Prop) :
    ¬¬ (¬¬ a → a) :=
  by
    intro h
    apply h
    intro not_not_a
    apply False.elim
    apply not_not_a
    intro x
    apply h
    intro _
    exact x

/- 2.2 (2 points). Prove the missing link in our chain of classical axiom
implications.

Hints:

* One way to find the definitions of `DoubleNegation` and `ExcludedMiddle`
  quickly is to

  1. hold the Control (on Linux and Windows) or Command (on macOS) key pressed;
  2. move the cursor to the identifier `DoubleNegation` or `ExcludedMiddle`;
  3. click the identifier.

* You can use `rw DoubleNegation` to unfold the definition of
  `DoubleNegation`, and similarly for the other definitions.

* You will need to apply the double negation hypothesis for `a ∨ ¬ a`. You will
  also need the left and right introduction rules for `∨` at some point. -/

#check DoubleNegation
#check ExcludedMiddle

theorem EM_of_DN :
    DoubleNegation → ExcludedMiddle :=
  by
    intro double_negation a
    apply double_negation (a ∨ ¬a)
    simp

/- 2.3 (2 points). We have proved three of the six possible implications
between `ExcludedMiddle`, `Peirce`, and `DoubleNegation`. State and prove the
three missing implications, exploiting the three theorems we already have. -/

#check Peirce_of_EM
#check DN_of_Peirce
#check EM_of_DN

-- enter your solution here

theorem EM_of_Peirce : Peirce → ExcludedMiddle := EM_of_DN ∘ DN_of_Peirce

theorem Peirce_of_DN :
    DoubleNegation → Peirce :=
  by
    intro double_negation a b f
    apply double_negation a
    intro not_a
    apply not_a
    apply f
    intro x
    apply False.elim
    exact not_a x

theorem DN_of_EM :
    ExcludedMiddle → DoubleNegation :=
  by
    intro excluded_middle a not_not_a
    cases excluded_middle a with
    | inl => assumption
    | inr not_a =>
      apply False.elim
      exact not_not_a not_a

end BackwardProofs

end LoVe
