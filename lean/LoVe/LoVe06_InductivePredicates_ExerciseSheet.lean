/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe06_InductivePredicates_Demo


/- # LoVe Exercise 6: Inductive Predicates

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Even and Odd

The `Even` predicate is `True` for even numbers and `False` for odd numbers. -/

#check Even

/- We define `Odd` as the negation of `Even`: -/

def Odd (n : ℕ) : Prop :=
  ¬ Even n

/- 1.1. Prove that 1 is odd and register this fact as a simp rule.

Hint: `cases` or `induction` is useful to reason about hypotheses of the form
`Even …`. -/

@[simp] theorem Odd_1 :
    Odd 1 :=
  by
    simp [Odd]
    intro h
    cases h

/- 1.2. Prove that 3 and 5 are odd. -/

-- enter your answer here

theorem Odd_add_two (n : ℕ) :
    Odd n → Odd (n + 2) :=
  by
    intro h_odd h_even_add_two
    apply h_odd
    cases h_even_add_two
    assumption

@[simp] theorem Odd_3 : Odd 3 := Odd_add_two 1 Odd_1

@[simp] theorem Odd_5 : Odd 5 := Odd_add_two 3 Odd_3


/- 1.3. Complete the following proof by structural induction. -/

theorem Even_two_times :
    ∀m : ℕ, Even (2 * m)
  | 0     => Even.zero
  | m + 1 => Even.add_two (2 * m) (Even_two_times m)

/- ## Question 2: Tennis Games

Recall the inductive type of tennis scores from the demo: -/

#check Score

/- 2.1. Define an inductive predicate that returns `True` if the server is
ahead of the receiver and that returns `False` otherwise. -/

inductive ServAhead : Score → Prop
  | byScore {m n : ℕ} : m > n → ServAhead (Score.vs m n)
  | byAdv : ServAhead Score.advServ
  | byGame : ServAhead Score.gameServ

/- 2.2. Validate your predicate definition by proving the following theorems. -/

theorem ServAhead_vs {m n : ℕ} (hgt : m > n) :
    ServAhead (Score.vs m n) :=
  ServAhead.byScore hgt

theorem ServAhead_advServ :
    ServAhead Score.advServ :=
  ServAhead.byAdv

theorem not_ServAhead_advRecv :
    ¬ ServAhead Score.advRecv :=
  by
    intro h
    cases h

theorem ServAhead_gameServ :
    ServAhead Score.gameServ :=
  ServAhead.byGame

theorem not_ServAhead_gameRecv :
    ¬ ServAhead Score.gameRecv :=
  by
    intro h
    cases h

/- 2.3. Compare the above theorem statements with your definition. What do you
observe? -/

-- enter your answer here


/- ## Question 3: Binary Trees

3.1. Prove the converse of `IsFull_mirror`. You may exploit already proved
theorems (e.g., `IsFull_mirror`, `mirror_mirror`). -/

#check IsFull_mirror
#check mirror_mirror

theorem mirror_eq_nil_iff {α : Type} (t : Tree α) :
    mirror t = Tree.nil ↔ t = Tree.nil :=
  by
    apply Iff.intro
    { intro h
      cases t with
      | nil => rfl
      | node => simp [mirror] at h }
    { intro h
      rw [h]
      rfl }

theorem mirror_IsFull {α : Type} :
    ∀t : Tree α, IsFull (mirror t) → IsFull t :=
  by
    intro t
    induction t with
    | nil => simp [mirror]
    | node v left right ih_l ih_r =>
      simp [mirror]
      intro h
      cases h with
      | node _ _ _ hr hl hiff =>
        apply IsFull.node
        { apply ih_l
          assumption }
        { apply ih_r
          assumption }
        { apply Iff.intro
          { intro h
            simp [h, mirror, mirror_eq_nil_iff] at hiff
            exact hiff }
          { intro h
            simp [h, mirror, mirror_eq_nil_iff] at hiff
            exact hiff }}


/- 3.2. Define a `map` function on binary trees, similar to `List.map`. -/

def Tree.map {α β : Type} (f : α → β) : Tree α → Tree β
  | .nil => .nil
  | .node v l r => .node (f v) (Tree.map f l) (Tree.map f r)

/- 3.3. Prove the following theorem by case distinction. -/

theorem Tree.map_eq_empty_iff {α β : Type} (f : α → β) :
    ∀t : Tree α, Tree.map f t = Tree.nil ↔ t = Tree.nil :=
  by
    intro t
    apply Iff.intro
    { cases t with
      | nil => simp
      | node => simp [Tree.map] }
    { intro h
      simp [h, Tree.map] }

/- 3.4 (**optional**). Prove the following theorem by rule induction. -/

theorem map_IsFull {α β : Type} (f : α → β) :
    ∀t : Tree α, IsFull t → IsFull (Tree.map f t) :=
  by
    intro t h
    induction t with
    | nil => exact IsFull.nil
    | node v left right ih_l ih_r =>
      cases h with
      | node _ _ _ _ _ hiff =>
        apply IsFull.node
        { apply ih_l
          assumption }
        { apply ih_r
          assumption }
        { simp [Tree.map_eq_empty_iff]
          exact hiff }

end LoVe
