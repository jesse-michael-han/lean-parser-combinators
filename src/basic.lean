/-
Copyright (c) 2019 Jesse Michael Han. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Jesse Michael Han 

Monadic parsing in Lean, following Hutton-Meijer's 'Monadic Parsing in Haskell` (doi: 10.1017/S0956796898003050).

A related implementation for character buffers, due to Gabriel Ebner, is in data.buffer.
-/

import tactic category.traversable tactic.slice -- .fol' .parse_formula'

namespace char

notation `[]` := list.nil
notation h :: t  := list.cons h t
notation `[` l:(foldr `, ` (h t, list.cons h t) list.nil `]`) := l

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

meta def lift {α} (val : tactic α) : parser_tactic α := state_t.lift val

meta def run (p : parser_tactic α) : string → tactic (α × string) :=
state_t.run p

meta def run_parser (p : parser_tactic α) : string → parser_tactic α :=
λ arg, lift (do (a,b) <- p.run arg, return a)

/-- For testing parsers on strings -/
meta def run' {α} [has_to_tactic_format α] (p : parser_tactic α) (arg : string) : tactic unit :=
  p.run arg >>= tactic.trace

meta instance monad_parser_tactic : monad parser_tactic :=
by change _root_.monad (state_t _ _); apply_instance

meta instance alternative_parser_tactic : alternative parser_tactic :=
by change _root_.alternative (state_t _ _); apply_instance

meta instance : has_append (parser_tactic string) :=
⟨λ p₁ p₂, do a <- p₁, b <- p₂, return $ a ++ b⟩ 

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

/--
`item0` is like `item`, but does not consume anything (leaves the state unchanged).
-/
meta def item0 : parser_tactic char :=
parser_tactic.mk $ λ str,
  match str with
  | ⟨[]⟩      := tactic.failed
  | ⟨(x::xs)⟩ := return (x, ⟨x::xs⟩)
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

meta def not_ch (c : char) : parser_tactic char := not_chs $ [c]

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

/--
`not_str arg` consumes and returns the longest prefix which does not match `arg`.
Upon encountering `arg`, `not_str arg`  consumes and discards it.
-/
meta def not_str : string → parser_tactic string := λ arg,
repeat $ (succeeds $ str arg) >>= (λ b, if b then fail else item)

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



/--
`delimiter_aux arg_left arg_right k` believes that it has passed `k` copies of `arg_left`, and is expecting `k` copies of `arg_right`.

Upon encountering a copy of `arg_right`, it calls itself, decrementing the counter by 1.
-/
/-
TODO(jesse) refactor this to consume extra characters to the right instead of left
-/
meta def delimiter_aux (arg_left : string) (arg_right : string) : Π k : ℕ, parser_tactic string
| 0 := (not_str arg_left ++ str arg_left ++ delimiter_aux 1) <|> return ""
| (k + 1) := (not_str arg_left ++ str arg_left ++ delimiter_aux (k + 2))
             <|> ((not_str arg_right) ++ str arg_right) ++ delimiter_aux k

/-- `delimiter arg_left arg_right parses the delimiters, then returns their interior as a string -/
meta def delimiter (arg_left arg_right : string) : parser_tactic string :=
delimiter_aux arg_left arg_right 0

/--
`delimiter' p arg_right arg_left` parses the delimiters, then runs p on their interior.
-/
meta def delimiter' {α} (p : parser_tactic α) (arg_right) (arg_left) : parser_tactic α :=
delimiter arg_right arg_left >>= p.run_parser

/-
Note that "match any except for arg_right" is not right, because it will not fail even if a delimiter is never found
So we need a parser that succeeds if and only if a match for e.g. ')' is found, then returns the consumed characters as a string
-/

meta def apply {α} (p : parser_tactic α) : string → tactic (α × string) := (space *> p).run

-- section parse_fol
-- open fol

-- meta instance {k} : has_to_tactic_format (preformula L_empty k)  :=
-- ⟨begin intro f, have := (reflected.has_to_tactic_format f).1 ,
--        apply this, apply_instance end⟩

-- meta def parse_preformula_aux : parser_tactic (preformula L_empty 0) :=
-- token' (str "∀") >> parse_preformula_aux >>= (λ x, return (preformula.all x)) <|>
-- (repeat item) *> return (&0 ≃ &0)

-- -- as vars are encountered, they are pushed onto the stack
-- -- the de Bruijn index assigned to an encountered free variable is its position in the stack.
-- -- a named variable is captured by the nearest quantifier with the same name

-- meta structure formula_state (k : ℕ) :=
-- (bound_var : list name)
-- (free_var : list name)
-- (result : preformula L_empty k)

-- #check formula_state.mk

-- -- meta def formula_state.var {k : ℕ} (σ : formula_state k) : tactic (list name) :=
-- -- σ.bound_var >>= (λ x, (σ.free_var >>= (λ y, return (x ++ y))))

-- meta def parse_preformula {k : ℕ} (σ : formula_state k) : parser_tactic (formula_state 0) :=
-- do token' (str "∀"),
--    v <- (alphanumeric_token),
--    let foo := ℕ in
--    return (formula_state.mk (σ.bound_var ++ [v]) (σ.free_var) foo )
-- -- TODO(jesse) finish this

-- -- @formula_state.mk 0 (σ.bound_var.append ([↑v] : list _)) σ.free_var (parse_preformula >>= _

-- -- meta def parse_preformula : parser_tactic (Σk, preformula L_empty k) :=
-- -- do token' (str "∀") >> (parse_preformula >>= λ x, return ⟨x.fst, x.2⟩)

-- -- run_cmd run' parse_preformula_aux "∀ ∀ ∀ ∀ foo"

-- -- fol.preterm.var : Π {L : Language}, ℕ → preterm L 0
-- -- fol.preterm.func : Π {L : Language} {l : ℕ}, L.functions l → preterm L l
-- -- fol.preterm.app : Π {L : Language} {l : ℕ}, preterm L (l + 1) → preterm L 0 → preterm L l

-- -- fol.preformula.falsum : Π {L : Language}, preformula L 0
-- -- fol.preformula.equal : Π {L : Language}, term L → term L → preformula L 0
-- -- fol.preformula.rel : Π {L : Language} {l : ℕ}, L.relations l → preformula L l
-- -- fol.preformula.apprel : Π {L : Language} {l : ℕ}, preformula L (l + 1) → term L → preformula L l
-- -- fol.preformula.imp : Π {L : Language}, preformula L 0 → preformula L 0 → preformula L 0
-- -- fol.preformula.all : Π {L : Language}, preformula L 0 → preformula L 0

-- -- ∀ x, x = x ∧ (f x y = 3)

-- meta def parse_eq : parser_tactic $ term L_empty → term L_empty → preformula L_empty 0 :=
-- (token (ch '=' >> return preformula.equal))

-- meta def parser_var : parser_tactic $ sorry := sorry

-- meta def parse_preterm {k} : parser_tactic (preterm L_empty k) := sorry

-- meta def parse_preformula {k} : parser_tactic (preformula L_empty k) := sorry

-- end parse_fol

section tests

run_cmd run' (delimiter "HELLO" "GOODBYE") "HELLO TOM GOODBYE TOM"

run_cmd run' (delimiter "(" ")") "(1 + 2) + 3"

run_cmd run' (delimiter "[" "]") "[a + b + [c + d] + [e + [f]]] + 3"

run_cmd run' (delimiter "[" "]") "[]] + 3"

run_cmd run' (delimiter "[" "]") "[1 + 2 + 3" -- returns nothing as it should

run_cmd run' (delimiter "[" "]") "[a + b + [c + d] + [e + [f]]] + 3"

run_cmd run' (not_str "HEWWO") "DUH HEWWO"

run_cmd run' (repeat alphanumeric_token) "a1 a3 b3 b4 x12 xasd1"

run_cmd run' (token $ (str "foo")) "foo    bar"

run_cmd run' (sepby (str "foo") (str " ")) "foo foo foo foo"

run_cmd run' (repeat (str "foo")) "barfoofoobarbarbarfoo"

-- run_cmd run' (repeat1 (str "foo")) "barfoofoobarbarbarfoo" -- fails as it should

run_cmd run' (repeat1 (str "foo")) "foofoofoobarbarbarfoo" 

run_cmd run' (str "foo") "foobarbaz"  -- (foo, barbaz)

end tests

end parser_tactic
