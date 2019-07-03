/-
Copyright (c) 2019 Jesse Michael Han. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Jesse Michael Han 

Monadic parsing in Lean, following the paper of Hutton and Meijer.

A related implementation for character buffers (due to Gabriel Ebner) is in data.buffer.
-/

import tactic category.traversable tactic.slice .fol' .parse_formula'

namespace char

notation `[]` := list.nil

meta def check_is_valid_char : tactic unit := `[norm_num[is_valid_char]]

/-- char.mk' will automatically attempt to use `check_is_valid_char` to produce the validity certificate -/
def mk' (n : ℕ) (H : is_valid_char n . check_is_valid_char) : char :=
char.mk n H

def alpha : list char := "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ".data

def numeric : list char := "0123456789".data

def alphanumeric := alpha ++ numeric

section whitespace_chars

def cr := mk' 0x0D

def newline : char := mk' 0x0a

def space : char := ' '

def thin_space : char := ' '

def hair_space : char := ' '

def no_break_space : char := ' '

def medium_mathematical_space : char := ' '

def ideographic_space : char := '　'

def zero_width_no_break_space := '﻿'

def zero_width_space := '​'

def punctuation_space := ' '

def figure_space := ' '

def six_per_em_space := ' '

def four_per_em_space := ' '

def three_per_em_space := ' '

def em_space := ' '

def en_space := ' '

def em_quad := ' '

def en_quad := ' '

def mongolian_vowel_separator := '᠎'

def ogham_space_mark := ' '

def tab := char.mk' 0x09

def narrow_no_break_space := ' '

def whitespace_chars : list char :=
  [cr,
   newline,
   space,
   thin_space,
   hair_space,
   tab,
   zero_width_space,
   zero_width_no_break_space,
   narrow_no_break_space,
   medium_mathematical_space,
   ideographic_space,
   punctuation_space,
   figure_space,
   six_per_em_space,
   four_per_em_space,
   three_per_em_space,
   em_quad,
   en_quad,
   en_space,
   em_space,
   mongolian_vowel_separator,
   no_break_space]

end whitespace_chars

end char

@[reducible]meta def parser' := state_t string

meta def parser_tactic := parser' tactic

namespace parser_tactic
section parser_tactic
variables {α : Type}

meta def mk (run : string → tactic (α × string)) : parser_tactic α :=
state_t.mk run

meta def run (p : parser_tactic α) : string → tactic (α × string) :=
state_t.run p

/-- For testing parsers on strings -/
meta def run' {α} [has_to_tactic_format α] (p : parser_tactic α) (arg : string) : tactic unit :=
  p.run arg >>= tactic.trace

meta instance monad_parser_tactic : monad parser_tactic :=
by change _root_.monad (state_t _ _); apply_instance

meta instance alternative_parser_tactic : alternative parser_tactic :=
by change _root_.alternative (state_t _ _); apply_instance

meta def fail : parser_tactic α := parser_tactic.mk $ λ _, tactic.failed

meta def trace_state : parser_tactic unit :=
parser_tactic.mk $ λ str, tactic.trace str >> return ((), str)

meta def skip : parser_tactic unit :=
parser_tactic.mk $ λ str, return ((), str)

meta def trace (msg : string) : parser_tactic unit :=
parser_tactic.mk $ λ str, tactic.trace msg >> return ((), str)

end parser_tactic
end parser_tactic

open parser_tactic

namespace parser_tactic

meta def item : parser_tactic char :=
parser_tactic.mk $ λ str,
  match str with
  | ⟨[]⟩      := tactic.failed
  | ⟨(x::xs)⟩ := return (x, ⟨xs⟩)
  end

meta def to_string : parser_tactic char → parser_tactic string :=
λ p, do x <- p, return x.to_string

meta def to_string' : parser_tactic (list char) → parser_tactic string :=
λ p, do x <- p, return $ string_imp.mk x

meta instance : has_coe (parser_tactic (char)) (parser_tactic string) :=
⟨to_string⟩

meta instance list_char_coe : has_coe (parser_tactic (list char)) (parser_tactic string) :=
⟨to_string'⟩

meta def sat (P : char → Prop) [decidable_pred P] : parser_tactic char :=
item >>= λ x, (if P x then return x else fail)

def eq_any (cs : list char) : char → Prop :=
λ c, cs.foldr (λ x, λ b, (= c) x ⊔ b)  ⊥ 

@[simp]lemma eq_any_cons {c} {cs} : eq_any (c::cs) = λ x, c = x ∨ eq_any cs x := rfl

instance eq_any_decidable_pred : ∀ {cs}, decidable_pred (eq_any cs) :=
begin
  intro cs, induction cs with c cs ih, unfold eq_any, tidy, apply_instance,
  intro x, haveI : decidable (eq_any cs x) := by apply ih,
  by_cases c = x,
    { exact decidable.is_true (by simp*) },
    { by_cases (eq_any cs x),
          { simp*, apply_instance },
          { simp*, apply_instance }}
end

/- note: we'll never need this, but it's basically free -/
def eq_all (cs : list char) : char → Prop :=
λ c, cs.foldr (λ x, λ b, (= c) x ⊓ b)  ⊤

@[simp]lemma eq_all_cons {c} {cs} : eq_all (c::cs) = λ x, c = x ∧ eq_all cs x := rfl

instance eq_all_decidable_pred : ∀ {cs}, decidable_pred (eq_all cs) :=
begin
  intro cs, induction cs with c cs ih, unfold eq_all, tidy, apply_instance,
  intro x, haveI : decidable (eq_all cs x) := by apply ih,
  by_cases c = x,
    { by_cases (eq_all cs x),
          { simp*, apply_instance },
          { simp*, apply_instance }},
    { exact decidable.is_false (by simp*) }
end

meta def ch  (c : char) : parser_tactic char := sat (= c)

meta def chs (cs : list char) : parser_tactic char := sat (eq_any cs)

meta def not_chs (cs : list char) : parser_tactic char := sat (λ c, ¬ eq_any cs c)

meta def str : string → parser_tactic string
| ⟨[]⟩    := pure ""
| ⟨x::xs⟩ := do y <- ch x,
               z <- str ⟨xs⟩,
               return $ y.to_string ++ z

meta def nil_if_fail {α} : parser_tactic α → parser_tactic (list α) := 
λ p, (p >>= return ∘ return) <|> return []

meta def list.mcons {m} [monad m] {α} (x : α) (xs : list α) : m (list α) :=
return (x::xs)

meta def repeat {α} (p : parser_tactic α) : parser_tactic (list α) :=
(do a  <- p,
    as <- repeat,
    return (a::as)) <|> return []

meta def repeat1 {α : Type} : parser_tactic α → parser_tactic (list α) :=
λ p, list.cons <$> p <*> repeat p

meta def sepby_aux {α β} : parser_tactic α → parser_tactic β → parser_tactic (list α) :=
λ p sep,
  list.cons <$> p <*> repeat (sep *> p)

meta def sepby {α β} : parser_tactic α → parser_tactic β → parser_tactic (list α) :=
λ p sep,
  (sepby_aux p sep) <|> return []

meta def chainl_aux {α} : parser_tactic α → parser_tactic (α → α → α) → α → parser_tactic α :=
λ p op a,
  do f <- op,
     b <- p,
     chainl_aux p op (f a b) <|> return a

meta def chainl {α} : parser_tactic α → parser_tactic (α → α → α) → α → parser_tactic α :=
λ p op a, (p >>= chainl_aux p op) <|> return a

meta def chainr_aux {α} : parser_tactic α → parser_tactic (α → α → α) → α → parser_tactic α :=
λ p op a,
  do f <- op,
     b <- (p >>= chainr_aux p op),
     chainr_aux p op (f a b) <|> return a

meta def chainr {α} : parser_tactic α → parser_tactic (α → α → α) → α → parser_tactic α :=
λ p op a, (p >>= chainr_aux p op) <|> return a

/- Lexical combinators -/

meta def space : parser_tactic string := repeat (sat (= ' '))

meta def whitespace : parser_tactic string := repeat (chs char.whitespace_chars)

meta def not_whitespace : parser_tactic string := repeat (not_chs char.whitespace_chars)

/-- `token p` runs p, then consumes as many spaces as possible before discarding them. -/
meta def token {α} (p : parser_tactic α) : parser_tactic α := p <* space

/-- `token' p runs p, then consumes as much whitespace as possible before discarding it. -/
meta def token' {α} (p : parser_tactic α) : parser_tactic α := p <* whitespace

meta def symbol : string → parser_tactic string := token ∘ str

/-- An alphanumeric token is a string of alphanumeric characters which must begin with an alpha character. -/
meta def alphanumeric_token : parser_tactic string :=
string.append <$> (chs char.alpha) <*> (repeat (chs char.alphanumeric) <* whitespace)

meta def apply {α} (p : parser_tactic α) : string → tactic (α × string) := (space *> p).run

section parse_fol
open fol

meta def parse_preformula_aux : parser_tactic (preformula L_empty 0) :=
token' (str "∀") >> parse_preformula_aux >>= (λ x, return (preformula.all x)) <|>
(repeat item) *> return (&0 ≃ &0)

meta instance {k} : has_to_tactic_format (preformula L_empty k)  :=
⟨begin intro f, have := (reflected.has_to_tactic_format f).1 ,
       apply this, apply_instance end⟩

-- fol.preterm.var : Π {L : Language}, ℕ → preterm L 0
-- fol.preterm.func : Π {L : Language} {l : ℕ}, L.functions l → preterm L l
-- fol.preterm.app : Π {L : Language} {l : ℕ}, preterm L (l + 1) → preterm L 0 → preterm L l

-- fol.preformula.falsum : Π {L : Language}, preformula L 0
-- fol.preformula.equal : Π {L : Language}, term L → term L → preformula L 0
-- fol.preformula.rel : Π {L : Language} {l : ℕ}, L.relations l → preformula L l
-- fol.preformula.apprel : Π {L : Language} {l : ℕ}, preformula L (l + 1) → term L → preformula L l
-- fol.preformula.imp : Π {L : Language}, preformula L 0 → preformula L 0 → preformula L 0
-- fol.preformula.all : Π {L : Language}, preformula L 0 → preformula L 0

-- ∀ x, x = x ∧ (f x y = 3)

meta def parse_eq : parser_tactic $ term L_empty → term L_empty → preformula L_empty 0 :=
(token (ch '=' >> return preformula.equal))

meta def parser_var : parser_tactic $ sorry := sorry

meta def parse_preterm {k} : parser_tactic (preterm L_empty k) := sorry

meta def parse_preformula {k} : parser_tactic (preformula L_empty k) := sorry

end parse_fol



section tests

run_cmd run' (repeat alphanumeric_token) "a1 a3 b3 b4 x12 xasd1"
run_cmd run' (token $ (str "foo")) "foo    bar"
run_cmd run' (sepby (str "foo") (str " ")) "foo foo foo foo"
run_cmd run' (repeat (str "foo")) "barfoofoobarbarbarfoo"
-- run_cmd run' (repeat1 (str "foo")) "barfoofoobarbarbarfoo" -- fails as it should
run_cmd run' (repeat1 (str "foo")) "foofoofoobarbarbarfoo" 
run_cmd run' (str "foo") "foobarbaz"  -- (foo, barbaz)

end tests

end parser_tactic
