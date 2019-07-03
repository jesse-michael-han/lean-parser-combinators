/-
Copyright (c) 2019 Jesse Michael Han. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Jesse Michael Han 

Monadic parsing in Lean, following the paper of Hutton and Meijer.

A related implementation for character buffers (due to Gabriel Ebner) is in data.buffer.
-/

import tactic category.traversable tactic.slice

@[reducible]meta def parser' := state_t string

meta def parser_tactic := parser' tactic

namespace parser_tactic
section parser_tactic
variables {α : Type}

meta def mk (run : string → tactic (α × string)) : parser_tactic α :=
state_t.mk run

meta def run (p : parser_tactic α) : string → tactic (α × string) :=
state_t.run p

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
λ p, do x <- p, return x.to_string

meta instance : has_coe (parser_tactic (char)) (parser_tactic string) :=
⟨to_string⟩

meta instance list_char_coe : has_coe (parser_tactic (list char)) (parser_tactic string) :=
⟨to_string'⟩

meta def sat (P : char → Prop) [decidable_pred P] : parser_tactic char :=
item >>= λ x, (if P x then return x else fail)

meta def char (c : char) : parser_tactic char := sat (= c)

meta def char' (c : _root_.char) : parser_tactic string := (sat (= c)).to_string

meta def str : string → parser_tactic string
| ⟨[]⟩    := pure ""
| ⟨x::xs⟩ := do y <- char x,
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
λ p, p >> repeat p

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

meta def token {α} (p : parser_tactic α) : parser_tactic α := p <* space

meta def symbol : string → parser_tactic string := token ∘ str

meta def apply {α} (p : parser_tactic α) : string → tactic (α × string) := (space *> p).run

section tests

run_cmd (token $ (str "foo")).run "foo    bar" >>= tactic.trace
run_cmd (sepby (str "foo") (str " ")).run "foo foo foo foo" >>= tactic.trace
-- run_cmd (repeat1 (str "foo")).run "barfoofoobarbarbarfoo" >>= tactic.trace -- fails as it should
run_cmd (repeat (str "foo")).run "barfoofoobarbarbarfoo" >>= tactic.trace
run_cmd (repeat1 (str "foo")).run "foofoofoobarbarbarfoo" >>= tactic.trace
run_cmd (str "foo").run "foobarbaz" >>= tactic.trace -- (foo, barbaz)

end tests

end parser_tactic
