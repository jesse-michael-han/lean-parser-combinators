/-
Copyright (c) 2019 Jesse Michael Han. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Jesse Michael Han 

Monadic parsing in Lean, following Hutton-Meijer's 'Monadic Parsing in Haskell` (doi: 10.1017/S0956796898003050).

A related implementation for character buffers, due to Gabriel Ebner, is in data.buffer.
-/

import tactic category.traversable tactic.slice -- .fol' .parse_formula'

import init.data.string tactic.explode

section miscellany

lemma forall_iff_of_eq {α} {P Q : α → Prop} (h : P = Q) : (∀ x, P x ↔ Q x) :=
λ _, h ▸ iff_of_eq rfl

lemma mem_cons_iff {α} (xs : list α) (x y : α) : y ∈ (x::xs) ↔ y = x ∨ y ∈ xs :=
(set.mem_union x (eq y) (λ (x : α), list.mem y xs))

example {α β} (xs : list α) {x : α} (f : α → β) (H_mem : x ∈ xs) : f x ∈ xs.map f := list.mem_map_of_mem f H_mem

end miscellany

namespace char

notation `[]` := list.nil
notation h :: t  := list.cons h t
notation `[` l:(foldr `, ` (h t, list.cons h t) list.nil `]`) := l

instance : has_zero string := ⟨""⟩

meta def check_is_valid_char : tactic unit := `[norm_num[is_valid_char]]

/-- char.mk' will automatically attempt to use `check_is_valid_char` to produce the validity certificate -/
def mk' (n : ℕ) (H : is_valid_char n . check_is_valid_char) : char :=
char.mk n H

def lower : list char := "abcdefghijklmnopqrstuvwxyz".data

def upper : list char := "ABCDEFGHIJKLMNOPQRSTUVWXYZ".data

lemma is_upper_of_mem_upper {c} (H : c ∈ upper) : is_upper c :=
by {unfold is_upper upper, repeat{cases H, subst H, omega}, cases H }

lemma to_lower_upper_eq_lower : upper.map to_lower = lower := dec_trivial

lemma mem_lower_of_to_lower_upper {c} (H : c ∈ upper) : c.to_lower ∈ lower :=
by {rw[<-to_lower_upper_eq_lower], exact list.mem_map_of_mem _ ‹_›}

def lowercase : {c // c ∈ upper} → {c // c ∈ lower} :=
λ ⟨c,H⟩, ⟨char.to_lower c, mem_lower_of_to_lower_upper H⟩

def alpha : list char := lower ++ upper

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

namespace string

def to_lower (arg : string) : string := ⟨arg.data.map char.to_lower⟩

def reverse (arg : string) : string :=
⟨arg.data.reverse⟩

end string


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

/--
`run parser p arg` runs `p` as if `arg` were the current state.

It returns the result of p, leaving the actual state unchanged.
-/
meta def run_parser (p : parser_tactic α) : string → parser_tactic α :=
λ arg, lift (do (a,b) <- p.run arg, return a)

meta instance monad_parser_tactic : monad parser_tactic :=
by change _root_.monad (state_t _ _); apply_instance

meta instance alternative_parser_tactic : alternative parser_tactic :=
by change _root_.alternative (state_t _ _); apply_instance

meta instance : has_append (parser_tactic string) :=
⟨λ p₁ p₂, do a <- p₁, b <- p₂, return $ a ++ b⟩ 

meta def fail : parser_tactic α := parser_tactic.mk $ λ _, tactic.failed

meta def trace_state : parser_tactic unit :=
parser_tactic.mk $ λ str, tactic.trace str >> return ((), str)

meta def get_state : parser_tactic string :=
state_t.get

meta def run_parser' (p : parser_tactic α) : parser_tactic string → parser_tactic α :=
λ q, q >>= run_parser p

meta def skip : parser_tactic unit :=
parser_tactic.mk $ λ str, return ((), str)

meta def trace (msg : string) : parser_tactic unit :=
parser_tactic.mk $ λ str, tactic.trace msg >> return ((), str)

meta def try_core (p : parser_tactic α) : parser_tactic (option α) :=
mk $ (λ arg, do r <- tactic.try_core (p.run arg),
      match r with
      | none     := return (none, arg)
      | (some x) := return (some x.1, x.2)
      end)

meta def try (p : parser_tactic α) : parser_tactic unit :=
try_core p >>= λ r, match r with
                    | none := skip
                    | some x := return ()
                    end

meta def to_tactic (p : parser_tactic α) : string → tactic α :=
λ arg, (p.run arg) >>= return ∘ prod.fst

meta instance : has_coe (parser_tactic α) (string → tactic α) :=
⟨to_tactic⟩

meta def parser_tactic_format {α} [H : has_to_format α] : α × string → format :=
λ ⟨r,σ⟩,
    format.line ++ ("Result:") ++
    format.line ++ format.line ++ (format.nest 5 $ to_fmt r) ++
    format.line ++ format.line ++
    "──────────────────────────────────────" ++
    format.line ++ format.line ++ ("State:") ++
    format.line ++ format.line ++ (format.nest 5 $ to_fmt σ)

/-- For testing parsers on strings -/
meta def run' {α} [has_to_format α] (p : parser_tactic α) (arg : string) : tactic unit :=
  p.run arg >>= λ fmt, return $ _root_.trace_fmt (parser_tactic_format fmt) (λ _, ())

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

meta instance parser_to_string : has_coe (parser_tactic (char)) (parser_tactic string) :=
⟨to_string⟩

meta instance list_char_coe : has_coe (parser_tactic (list char)) (parser_tactic string) :=
⟨to_string'⟩

meta def sat (P : char → Prop) [decidable_pred P] : parser_tactic char :=
item >>= λ x, (if P x then return x else fail)

section eq_any
variables {α : Type*} [decidable_eq α]

def eq_any (cs : list α) : α → Prop :=
λ c, cs.foldr (λ x, λ b, (= c) x ⊔ b)  ⊥ 

@[simp]lemma eq_any_cons {c : α} {cs} : eq_any (c::cs) = λ x, c = x ∨ eq_any cs x := rfl

instance eq_any_decidable_pred : ∀ {cs : list α}, decidable_pred (eq_any cs) :=
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
def eq_all (cs : list α) : α → Prop :=
λ c, cs.foldr (λ x, λ b, (= c) x ⊓ b)  ⊤

@[simp]lemma eq_all_cons {c : α} {cs} : eq_all (c::cs) = λ x, c = x ∧ eq_all cs x := rfl

instance eq_all_decidable_pred : ∀ {cs : list α}, decidable_pred (eq_all cs) :=
begin
  intro cs, induction cs with c cs ih, unfold eq_all, tidy, apply_instance,
  intro x, haveI : decidable (eq_all cs x) := by apply ih,
  by_cases c = x,
    { by_cases (eq_all cs x),
          { simp*, apply_instance },
          { simp*, apply_instance }},
    { exact decidable.is_false (by simp*) }
end

end eq_any

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

meta def fail_if_nil : parser_tactic string → parser_tactic string :=
λ p, do x <- p, guard (x ≠ ""), return x

meta def fail_if_state_nil {α} (p : parser_tactic α) : parser_tactic α :=
(get_state >>= λ arg, guard (arg ≠ "")) >> p

meta def list.mcons {m} [monad m] {α} (x : α) (xs : list α) : m (list α) :=
return (x::xs)

meta def repeat {α} (p : parser_tactic α) : parser_tactic (list α) :=
(do a  <- p,
    as <- repeat,
    return (a::as)) <|> return []

meta def repeat1 {α : Type} : parser_tactic α → parser_tactic (list α) :=
λ p, list.cons <$> p <*> repeat p

/--
`succeeds' p` runs p, but does not change the state.
-/
meta def succeeds' {α} (p : parser_tactic α) : parser_tactic bool :=
succeeds $ get_state >>= (run_parser p)

/--
`not_str arg` consumes and returns the longest prefix which does not match `arg`.
-/
meta def not_str : string → parser_tactic string := λ arg,
repeat $ (succeeds $ str arg) >>= (λ b, if b then fail else item)

meta def not_strs : list string → parser_tactic string := λ arg,
repeat $ succeeds (list.mfirst str arg) >>= (λ b, if b then fail else item)

meta def sepby_aux {α β} : parser_tactic α → parser_tactic β → parser_tactic (list α) :=
λ p sep,
  list.cons <$> p <*> repeat (sep *> p)

meta def sepby {α β} : parser_tactic α → parser_tactic β → parser_tactic (list α) :=
λ p sep,
  (sepby_aux p sep) <|> return []

/-
The choice operator (++) from Hutton-Meijer does not have a direct analogue in this framework, since we use `tactic` as the monad instead of `list`.

However, the deterministic choice operator (+++):
1. fails iff both p and q fail
2. if p succeeds, returns the result of p
3. if p fails, runs q

and therefore (+++) is emulated by the orelse (<|>) combinator.
-/

/-
c.f. Hutton-Meijer:

chainl :: Parser a -> Parser (a -> a -> a) -> a -> Parser a
chainl p op a = (p ‘chainl1‘ op) +++ return a

chainl1 :: Parser a -> Parser (a -> a -> a) -> Parser a
p ‘chainl1‘ op = do {a <- p; rest a}
                 where
                   rest a = (do f <- op
                                b <- p
                                rest (f a b))
                            +++ return a
-/

meta def chainl_rest {α} (p : parser_tactic α) (op : parser_tactic (α → α → α)) : α → parser_tactic α :=
λ a,
  (do f <- op,
     b <- p,
     chainl_rest (f a b)) <|> return a

meta def chainl1 {α} (p : parser_tactic α) (op : parser_tactic (α → α → α)) : parser_tactic α :=
do a <- p, chainl_rest p op a

meta def chainl {α} : parser_tactic α → parser_tactic (α → α → α) → α → parser_tactic α :=
λ p op a, (chainl1 p op) <|> return a

meta def chainr_rest {α} (p : parser_tactic α) (op : parser_tactic (α → α → α)) : α → parser_tactic α :=
λ a,
  (do f <- op,
     b <- p,
     chainr_rest (f b a)) <|> return a

meta def chainr1 {α} (p : parser_tactic α) (op : parser_tactic (α → α → α)) : parser_tactic α :=
do a <- p, chainr_rest p op a

meta def chainr {α} : parser_tactic α → parser_tactic (α → α → α) → α → parser_tactic α :=
λ p op a, (chainr1 p op) <|> return a

/- Lexical combinators -/

meta def space : parser_tactic string := repeat (sat (= ' '))

meta def whitespace : parser_tactic string := repeat (chs char.whitespace_chars)

meta def not_whitespace : parser_tactic string := repeat (not_chs char.whitespace_chars)

/-- `token p` runs p, then consumes as many spaces as possible before discarding them. -/
meta def token {α} (p : parser_tactic α) : parser_tactic α := p <* space

/-- `token' p runs p, then consumes as much whitespace as possible before discarding it. -/
meta def token' {α} (p : parser_tactic α) : parser_tactic α := p <* whitespace

meta def symb : string → parser_tactic string := token ∘ str

/-- An alphanumeric token is a string of alphanumeric characters which must begin with an alpha character. -/
meta def alphanumeric_token : parser_tactic string :=
string.append <$> (sat char.is_alpha) <*> (repeat (sat char.is_alphanum) <* whitespace)

meta def digit : parser_tactic char  := chs char.numeric

/--
`delimiter_aux arg_left arg_right k` believes that it has passed `k` copies of `arg_left`, and is expecting `k` copies of `arg_right`.

Upon encountering a copy of `arg_right`, it calls itself, decrementing the counter by 1.

If it never encounters an opening `arg_left`, it returns the empty string.
-/

/-
running delimiter on (foo (bar )) baz produces (foo (bar )).
-/
/-
TODO(jesse) refactor this to consume extra characters to the right instead of left
-/
meta def delimiter_aux (arg_left : string) (arg_right : string) : Π k : ℕ, parser_tactic string
| 0       := (not_str arg_left ++ str arg_left ++ delimiter_aux 1)
              <|> return ""
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

meta def delimiter'' (arg_left arg_right : string) : parser_tactic string :=
do r <- (delimiter arg_left arg_right),
   r' <- run_parser (symb arg_left >> get_state) r,
   run_parser ((symb arg_right.reverse) >> get_state >>= return ∘ string.reverse) r'.reverse

meta def between (arg_left arg_right : string) : parser_tactic string :=
  (str arg_left ++ not_strs [arg_left, arg_right] ++ (between <|> return "") ++ not_strs [arg_left, arg_right] ++ str arg_right)

meta def apply {α} (p : parser_tactic α) : string → tactic (α × string) := (space *> p).run

--TODO(jesse) fix this so it also consumes the corresponding prefix of the actual state
meta def case_insensitive (p : string → parser_tactic string) : string → parser_tactic string :=
λ arg, do s <- get_state, run_parser (p arg.to_lower) s.to_lower

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

run_cmd (fail_if_nil $ str "h").run' "hewwo" -- succeeds as it should

-- run_cmd (fail_if_nil $ str "").run' "hewwo" -- fails as it should

-- run_cmd run' (fail_if_state_nil $ skip) "" -- fails as it should

run_cmd run' (fail_if_state_nil $ skip) "foo" -- succeeds as it should

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

run_cmd run' (repeat $ fail_if_nil $ token $ not_whitespace) "foo₁ foo₂ foo₃ foo₄ foo₅"

run_cmd (repeat $ str "a" <|> str "b").run' "bbababbaabaaaa" -- if one branch fails, the state is unchanged and passed to the other branch

end tests

end parser_tactic

open parser_tactic

namespace arith_expr

section arith_expr

open arith_expr

def from_base_10_aux : ℕ → list ℕ → ℕ
| _      []          := 0
| 0      (x::xs)     := x
| (n+1)  (x::xs)     := (10^n) * x + from_base_10_aux n xs

def from_base_10 : list ℕ → ℕ := λ xs, from_base_10_aux xs.length xs

meta def digit' : parser_tactic ℕ :=
do x <- digit,
   if (x = '0') then return 0 else
   if (x = '1') then return 1 else
   if (x = '2') then return 2 else
   if (x = '3') then return 3 else
   if (x = '4') then return 4 else
   if (x = '5') then return 5 else
   if (x = '6') then return 6 else
   if (x = '7') then return 7 else
   if (x = '8') then return 8 else
   if (x = '9') then return 9 else
   fail

meta def number : parser_tactic ℕ := (repeat digit') >>= return ∘ from_base_10

meta def parse_number (arg : string) : tactic unit :=
do n <- number.to_tactic arg,
   tactic.exact `(n)

mutual inductive addop,mulop,digit,factor,term,expr
with addop : Type
     | plus             : addop
     | minus            : addop
with mulop : Type
     | mult             : mulop
     | div              : mulop
with digit : Type
     | zero             : digit
     | one              : digit
     | two              : digit
     | three            : digit
     | four             : digit
     | five             : digit
     | six              : digit
     | seven            : digit
     | eight            : digit
     | nine             : digit
with factor : Type
     | of_digit         : digit → factor
     | of_expr          : expr  → factor
with term : Type
     | of_factor        : factor → term
     | of_mulop         : mulop → term → factor → term
with expr : Type
     | of_term          : term → expr
     | of_addop         : addop → expr → term → expr

def term.of_digit := term.of_factor ∘ factor.of_digit

def expr.of_digit := expr.of_term ∘ term.of_digit

meta mutual def eval_addop,eval_mulop,eval_digit,eval_factor,eval_term,eval_expr
with eval_addop                : addop → ℕ → ℕ → ℕ
     | addop.plus              := (nat.add)
     | addop.minus             := (nat.sub)
with eval_mulop                : mulop → ℕ → ℕ → ℕ
     | mulop.mult              := (nat.mul)
     | mulop.div               := (nat.div)
with eval_digit                : digit → ℕ
     | digit.zero              := 0
     | digit.one               := 1
     | digit.two               := 2
     | digit.three             := 3
     | digit.four              := 4
     | digit.five              := 5
     | digit.six               := 6
     | digit.seven             := 7
     | digit.eight             := 8
     | digit.nine              := 9
with eval_factor               : factor → ℕ
     | (factor.of_digit k)     := eval_digit k         
     | (factor.of_expr e)      := eval_expr e
with eval_term                 : term → ℕ
     | (term.of_factor f)      := eval_factor f
     | (term.of_mulop op t f)  := (eval_mulop op) (eval_term t) (eval_factor f)
with eval_expr                 : expr → ℕ
     | (expr.of_term t)        := eval_term t
     | (expr.of_addop op e t)  := (eval_addop op) (eval_expr e) (eval_term t)

meta def nat.to_fmt : ℕ → format := nat.has_to_format.to_format

meta instance format_digit : has_to_format digit :=
⟨λ x, nat.to_fmt (eval_digit x)⟩

meta instance format_factor : has_to_format factor :=
⟨λ x, nat.to_fmt (eval_factor x)⟩

meta instance format_term : has_to_format term :=
⟨λ x, nat.to_fmt (eval_term x)⟩

meta instance format_expr : has_to_format expr := 
⟨λ x, nat.to_fmt (eval_expr x)⟩



meta mutual def parse_addop,parse_mulop,parse_digit,parse_factor,parse_term,parse_expr
with parse_addop                : string → tactic (addop × string)
| arg := (token (str "+" >> return addop.plus <|> str "-" >> return addop.minus)).run arg
with parse_mulop                : string → tactic (mulop × string)
| arg := (token (str "*" >> return mulop.mult <|> str "/" >> return mulop.div)).run arg
with parse_digit                : string → tactic (digit × string)
| arg := (token $ trace "HEWWO" >>    trace_state >> do  x <- parser_tactic.digit,
   trace $ x.to_string ++ " WAS THE DIGIT I PARSED",
   if (x = '0') then return digit.zero else
   if (x = '1') then return digit.one else
   if (x = '2') then return digit.two else
   if (x = '3') then return digit.three else
   if (x = '4') then return digit.four else
   if (x = '5') then return digit.five else
   if (x = '6') then return digit.six else
   if (x = '7') then return digit.seven else
   if (x = '8') then return digit.eight else
   if (x = '9') then return digit.nine else
   fail).run arg
with parse_factor               : string → tactic (factor × string)
| arg := (fail_if_state_nil $ (trace "hello" >> (token $ (mk parse_digit) >>= return ∘ factor.of_digit <|> (mk parse_expr) >>= return ∘ factor.of_expr))).run arg
with parse_term                 : string → tactic (term × string)
| arg := (token $
            (do
               trace "hola",
               b <- succeeds' (do not_str "*" >> str "*"),
               if b then (do t <- (mk parse_term),
                            op <- (mk parse_mulop),
                            f  <- (mk parse_factor),
                            return $ term.of_mulop op t f)
                     else (mk parse_factor) >>= return ∘ term.of_factor
                -- e   <- (mk parse_expr),
                -- op  <- (mk parse_addop),
                -- t   <- (mk parse_term),
                -- return $ expr.of_addop op e t
             )).run arg
with parse_expr                 : string → tactic (expr × string)
| arg := (token $
            (do
               trace "bonjour",
               b <- succeeds' (do not_str "+" >> str "+"),
               if b then -- return (expr.of_digit digit.one)
                           (do p <- not_str "+",
                             e <- (mk parse_expr).run_parser p,
                            op <- (mk parse_addop),
                            t  <- (mk parse_term),
                            return $ expr.of_addop op e t)
                     else (mk parse_term) >>= return ∘ expr.of_term
                -- e   <- (mk parse_expr),
                -- op  <- (mk parse_addop),
                -- t   <- (mk parse_term),
                -- return $ expr.of_addop op e t
             )
                ).run arg

meta def parse_arith_expr : parser_tactic expr := mk parse_expr

run_cmd (mk parse_expr).run' "9 + 1 + 1"

-- run_cmd (parse_arith_expr >> parse_arith_expr).run' "1"

-- run_cmd (
-- do b <- succeeds' (do not_str "+" >> str "+"),
--    trace_state,
--    if b then (do d₁ <- (mk parse_digit),
--                  op <- (mk parse_addop),
--                  d₂ <- (mk parse_digit),
--                  return $ expr.of_addop op (expr.of_digit d₁) (term.of_digit d₂)

--              )
--         else (mk parse_digit) >>= return ∘ expr.of_digit


--   ).run' "8 + 7"

end arith_expr

end arith_expr

namespace calculator


section calculator

open calculator

def from_base_10_aux : ℕ → list ℤ → ℤ
| _ []               := 0
| 0 (x::xs)          := x
| (n+1) (x::xs)      := (10^n) * x + from_base_10_aux n xs

def from_base_10 : list ℤ → ℤ := λ xs, from_base_10_aux xs.length xs

meta def digit' : parser_tactic ℤ :=
do x <- digit,
   if (x = '0') then return 0 else
   if (x = '1') then return 1 else
   if (x = '2') then return 2 else
   if (x = '3') then return 3 else
   if (x = '4') then return 4 else
   if (x = '5') then return 5 else
   if (x = '6') then return 6 else
   if (x = '7') then return 7 else
   if (x = '8') then return 8 else
   if (x = '9') then return 9 else
   fail

meta def number : parser_tactic ℤ := (repeat digit') >>= return ∘ from_base_10

meta def parse_number (arg : string) : tactic unit :=
do n <- number.to_tactic arg,
   tactic.exact `(n)

mutual inductive addop,mulop,digit,factor,term,expr
with addop : Type
     | plus             : addop
     | minus            : addop
with mulop : Type
     | mult             : mulop
     | div              : mulop
with digit : Type
     | zero             : digit
     | one              : digit
     | two              : digit
     | three            : digit
     | four             : digit
     | five             : digit
     | six              : digit
     | seven            : digit
     | eight            : digit
     | nine             : digit
with factor : Type
     | of_digit         : digit → factor
     | of_expr          : expr  → factor
with term : Type
     | of_factor        : factor → term
     | of_mulop         : mulop → term → factor → term
with expr : Type
     | of_term          : term → expr
     | of_addop         : addop → expr → term → expr

def term.of_digit := term.of_factor ∘ factor.of_digit

def expr.of_digit := expr.of_term ∘ term.of_digit

meta mutual def eval_addop,eval_mulop,eval_digit,eval_factor,eval_term,eval_expr
with eval_addop                : addop → ℕ → ℕ → ℕ
     | addop.plus              := (nat.add)
     | addop.minus             := (nat.sub)
with eval_mulop                : mulop → ℕ → ℕ → ℕ
     | mulop.mult              := (nat.mul)
     | mulop.div               := (nat.div)
with eval_digit                : digit → ℕ
     | digit.zero              := 0
     | digit.one               := 1
     | digit.two               := 2
     | digit.three             := 3
     | digit.four              := 4
     | digit.five              := 5
     | digit.six               := 6
     | digit.seven             := 7
     | digit.eight             := 8
     | digit.nine              := 9
with eval_factor               : factor → ℕ
     | (factor.of_digit k)     := eval_digit k         
     | (factor.of_expr e)      := eval_expr e
with eval_term                 : term → ℕ
     | (term.of_factor f)      := eval_factor f
     | (term.of_mulop op t f)  := (eval_mulop op) (eval_term t) (eval_factor f)
with eval_expr                 : expr → ℕ
     | (expr.of_term t)        := eval_term t
     | (expr.of_addop op e t)  := (eval_addop op) (eval_expr e) (eval_term t)

meta def nat.to_fmt : ℕ → format := nat.has_to_format.to_format

meta instance format_digit : has_to_format digit :=
⟨λ x, nat.to_fmt (eval_digit x)⟩

meta instance format_factor : has_to_format factor :=
⟨λ x, nat.to_fmt (eval_factor x)⟩

meta instance format_term : has_to_format term :=
⟨λ x, nat.to_fmt (eval_term x)⟩

meta instance format_expr : has_to_format expr := 
⟨λ x, nat.to_fmt (eval_expr x)⟩

/-
c.f. Hutton-Meijer:

expr :: Parser Int
addop :: Parser (Int -> Int -> Int)
mulop :: Parser (Int -> Int -> Int)

expr = chainl1 term addop
term = chainl1 factor mulop
factor = digit +++ (do symb "("; n <- expr; symb ")"; return n)
digit = (do <- token (sat isDigit); return(ord x - ord '0'))
addop = (do symb "+"; return (+)) <|> (do symb "-"; return (-)))
multop = (do symb "*"; return (*)) <|> (do symb "/"; return (/)))

Since mutual recursion in Lean seems to require use of the equation compiler,
we hack around this by exposing the underlying `parser_tactic.run` function,
later recovering the parser with `parser_tactic.mk`.
-/

meta mutual def parse_addop,parse_mulop,parse_digit,parse_factor,parse_term,parse_expr
with parse_addop                : string → tactic ((ℤ → ℤ → ℤ) × string)
| arg := (symb "+" >> return (+) <|> symb "-" >> return (λ x y : ℤ, x - y)).run arg
with parse_mulop                : string → tactic ((ℤ → ℤ → ℤ) × string)
| arg := (symb "*" >> return (*) <|> symb "/" >> return (λ x y : ℤ, x / y)).run arg
with parse_digit                : string → tactic (ℤ × string)
| arg := (token $ digit').run arg
with parse_factor               : string → tactic (ℤ × string)
| arg := (mk parse_digit <|> do symb "(", e <- (mk parse_expr), symb ")", return e).run arg
with parse_term                 : string → tactic (ℤ × string)
| arg := (chainl1 (mk parse_factor) (mk parse_mulop)).run arg
with parse_expr                 : string → tactic (ℤ × string)
| arg := (chainl1 (mk parse_term) (mk parse_addop)).run arg

meta def calculator : parser_tactic ℤ := mk parse_expr

run_cmd calculator.run' "(2 * (3 + 5 + (2 * 2)))"
-- 24

run_cmd calculator.run' "9 - 9 * 0 * 3 + 4 - 7"
-- 6

end calculator

end calculator

section parse_tree_from_list

inductive my_tree : Type
| node : option string → my_tree
| join : list my_tree → option string → my_tree
open my_tree

meta def my_tree_format : my_tree → format
| (node none)           := "• "
| (node $ some st)      := st ++ " "
| (join xs none)        := "{• || " ++ format.join ((xs.map my_tree_format).intersperse "  |  ") ++ "}"
| (join xs $ some st)   := " {" ++ st ++ " || " ++ format.join ((xs.map my_tree_format).intersperse "  |  ") ++ "}"

meta instance : has_to_format my_tree := ⟨my_tree_format⟩


/-
(a, b, c, (d, e), f) should be parsed as

  none -------┐ 
 / | \ \      | 
a  b c  none  f
        |  \
        d   e
-/

meta mutual def my_tree_parser₁,my_tree_parser₂
with my_tree_parser₁ : string → tactic (my_tree × string)
| arg := ((do int <- (fail_if_nil $ delimiter'' "(" ")"),
               ts  <- (run_parser (mk my_tree_parser₂) int),
               return (my_tree.join ts none))
            <|>
           (do x <- not_str ",",
               return $ my_tree.node x)).run arg
with my_tree_parser₂ : string → tactic (list my_tree × string)
| arg := (sepby (mk my_tree_parser₁) (symb ",")).run arg

meta def my_tree_parser : parser_tactic my_tree := mk my_tree_parser₁

run_cmd my_tree_parser.run' "(a, b, c)"
/- {• || a   |  b   |  c } -/
run_cmd my_tree_parser.run' "(a,(b,c))"
/- {• || a   |  {• || b   |  c }} -/
run_cmd my_tree_parser.run' "((a,b),c)"
/- {• || {• || a   |  b }  |  c } -/
run_cmd my_tree_parser.run' "(a, b, c, (d, e), f)"
/- {• || a   |  b   |  c   |  {• || d   |  e }  |  f } -/

section formatting_tests

example : my_tree := node none
def example_tree : my_tree := join [node none, node none, node none] "foo"

def example_tree2 : my_tree := join [join [node "a", node "b"] none, node "foo"] "bar"

run_cmd (return example_tree : parser_tactic my_tree).run' "ab"
run_cmd (return example_tree2: parser_tactic my_tree).run' "ab"

end formatting_tests

end parse_tree_from_list
