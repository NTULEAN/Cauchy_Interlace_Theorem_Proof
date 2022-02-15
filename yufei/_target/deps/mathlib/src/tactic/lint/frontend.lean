/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Robert Y. Lewis, Gabriel Ebner
-/
import meta.rb_map
import tactic.lint.basic

/-!
# Linter frontend and commands

This file defines the linter commands which spot common mistakes in the code.
* `#lint`: check all declarations in the current file
* `#lint_mathlib`: check all declarations in mathlib (so excluding core or other projects,
  and also excluding the current file)
* `#lint_all`: check all declarations in the environment (the current file and all
  imported files)

For a list of default / non-default linters, see the "Linting Commands" user command doc entry.

The command `#list_linters` prints a list of the names of all available linters.

You can append a `*` to any command (e.g. `#lint_mathlib*`) to omit the slow tests (4).

You can append a `-` to any command (e.g. `#lint_mathlib-`) to run a silent lint
that suppresses the output if all checks pass.
A silent lint will fail if any test fails.

You can append a `+` to any command (e.g. `#lint_mathlib+`) to run a verbose lint
that reports the result of each linter, including  the successes.

You can append a sequence of linter names to any command to run extra tests, in addition to the
default ones. e.g. `#lint doc_blame_thm` will run all default tests and `doc_blame_thm`.

You can append `only name1 name2 ...` to any command to run a subset of linters, e.g.
`#lint only unused_arguments`

You can add custom linters by defining a term of type `linter` in the `linter` namespace.
A linter defined with the name `linter.my_new_check` can be run with `#lint my_new_check`
or `lint only my_new_check`.
If you add the attribute `@[linter]` to `linter.my_new_check` it will run by default.

Adding the attribute `@[nolint doc_blame unused_arguments]` to a declaration
omits it from only the specified linter checks.

## Tags

sanity check, lint, cleanup, command, tactic
-/

open tactic expr native
setup_tactic_parser

/--
Verbosity for the linter output.
* `low`: only print failing checks, print nothing on success.
* `medium`: only print failing checks, print confirmation on success.
* `high`: print output of every check.
-/
@[derive [decidable_eq, inhabited]]
inductive lint_verbosity | low | medium | high

/-- `get_checks slow extra use_only` produces a list of linters.
`extras` is a list of names that should resolve to declarations with type `linter`.
If `use_only` is true, it only uses the linters in `extra`.
Otherwise, it uses all linters in the environment tagged with `@[linter]`.
If `slow` is false, it only uses the fast default tests. -/
meta def get_checks (slow : bool) (extra : list name) (use_only : bool) :
  tactic (list (name × linter)) := do
  default ← if use_only then return [] else attribute.get_instances `linter >>= get_linters,
  let default := if slow then default else default.filter (λ l, l.2.is_fast),
  list.append default <$> get_linters extra

/--
`lint_core all_decls non_auto_decls checks` applies the linters `checks` to the list of
declarations.
If `auto_decls` is false for a linter (default) the linter is applied to `non_auto_decls`.
If `auto_decls` is true, then it is applied to `all_decls`.
The resulting list has one element for each linter, containing the linter as
well as a map from declaration name to warning.
-/
meta def lint_core (all_decls non_auto_decls : list declaration) (checks : list (name × linter)) :
  tactic (list (name × linter × rb_map name string)) := do
checks.mmap $ λ ⟨linter_name, linter⟩, do
  let test_decls := if linter.auto_decls then all_decls else non_auto_decls,
  test_decls ← test_decls.mfilter (λ decl, should_be_linted linter_name decl.to_name),
  s ← read,
  let results := test_decls.map_async_chunked $ λ decl, prod.mk decl.to_name $
      match linter.test decl s with
      | result.success w _ := w
      | result.exception msg _ _ :=
        some $ "LINTER FAILED:\n" ++ msg.elim "(no message)" (λ msg, to_string $ msg ())
      end,
  let results := results.foldl (λ (results : rb_map name string) warning,
    match warning with
    | (decl_name, some w) := results.insert decl_name w
    | (_, none) := results
    end) mk_rb_map,
  pure (linter_name, linter, results)

/-- Sorts a map with declaration keys as names by line number. -/
meta def sort_results {α} (e : environment) (results : rb_map name α) : list (name × α) :=
list.reverse $ rb_lmap.values $ rb_lmap.of_list $
  results.fold [] $ λ decl linter_warning results,
    (((e.decl_pos decl).get_or_else ⟨0,0⟩).line, (decl, linter_warning)) :: results

/-- Formats a linter warning as `#check` command with comment. -/
meta def print_warning (decl_name : name) (warning : string) : format :=
"#check @" ++ to_fmt decl_name ++ " /- " ++ warning ++ " -/"

private def workflow_command_replacements : char → string
| '%' := "%25"
| '\n' := "%0A"
| c := to_string c

/--
Escape characters that may not be used in a workflow commands, following
https://github.com/actions/toolkit/blob/7257597d731b34d14090db516d9ea53439300e98/packages/core/src/command.ts#L92-L105
-/
def escape_workflow_command (s : string) : string :=
"".intercalate $ s.to_list.map workflow_command_replacements

/--
Prints a workflow command to emit an error understood by github in an actions workflow.
This enables CI to tag the parts of the file where linting failed with annotations, and makes it
easier for mathlib contributors to see what needs fixing.
See https://docs.github.com/en/actions/learn-github-actions/workflow-commands-for-github-actions#setting-an-error-message
-/
meta def print_workflow_command (env : environment) (linter_name decl_name : name)
 (warning : string) : option string := do
  po ← env.decl_pos decl_name,
  ol ← env.decl_olean decl_name,
  return $ sformat!"\n::error file={ol},line={po.line},col={po.column},title=" ++
    sformat!"Warning from {linter_name} linter::" ++
    sformat!"{escape_workflow_command $ to_string decl_name} - {escape_workflow_command warning}"

/-- Formats a map of linter warnings using `print_warning`, sorted by line number. -/
meta def print_warnings (env : environment) (emit_workflow_commands : bool) (linter_name : name)
  (results : rb_map name string) : format :=
format.intercalate format.line $ (sort_results env results).map $
  λ ⟨decl_name, warning⟩, let form := print_warning decl_name warning in
    if emit_workflow_commands then
      form ++ (print_workflow_command env linter_name decl_name warning).get_or_else ""
    else form

/--
Formats a map of linter warnings grouped by filename with `-- filename` comments.
The first `drop_fn_chars` characters are stripped from the filename.
-/
meta def grouped_by_filename (e : environment) (results : rb_map name string) (drop_fn_chars := 0)
  (formatter: rb_map name string → format) : format :=
let results := results.fold (rb_map.mk string (rb_map name string)) $
  λ decl_name linter_warning results,
    let fn := (e.decl_olean decl_name).get_or_else "" in
    results.insert fn (((results.find fn).get_or_else mk_rb_map).insert
      decl_name linter_warning) in
let l := results.to_list.reverse.map (λ ⟨fn, results⟩,
  ("-- " ++ fn.popn drop_fn_chars ++ "\n" ++ formatter results : format)) in
format.intercalate "\n\n" l ++ "\n"

/--
Formats the linter results as Lean code with comments and `#check` commands.
-/
meta def format_linter_results
  (env : environment)
  (results : list (name × linter × rb_map name string))
  (decls non_auto_decls : list declaration)
  (group_by_filename : option ℕ)
  (where_desc : string) (slow : bool) (verbose : lint_verbosity) (num_linters : ℕ)
  -- whether to include codes understood by github to create file annotations
  (emit_workflow_commands : bool := ff) :
  format := do
let formatted_results := results.map $ λ ⟨linter_name, linter, results⟩,
  let report_str : format := to_fmt "/- The `" ++ to_fmt linter_name ++ "` linter reports: -/\n" in
  if ¬ results.empty then
    let warnings := match group_by_filename with
      | none := print_warnings env emit_workflow_commands linter_name results
      | some dropped :=
        grouped_by_filename env results dropped
          (print_warnings env emit_workflow_commands linter_name)
      end in
    report_str ++ "/- " ++ linter.errors_found ++ " -/\n" ++ warnings ++ "\n"
  else if verbose = lint_verbosity.high then
    "/- OK: " ++ linter.no_errors_found ++ " -/"
  else format.nil,
let s := format.intercalate "\n" (formatted_results.filter (λ f, ¬ f.is_nil)),
let s := if verbose = lint_verbosity.low then s else
  format!("/- Checking {non_auto_decls.length} declarations (plus " ++
  "{decls.length - non_auto_decls.length} automatically generated ones) {where_desc} " ++
  "with {num_linters} linters -/\n\n") ++ s,
let s := if slow then s else s ++ "/- (slow tests skipped) -/\n",
s

/-- The common denominator of `#lint[|mathlib|all]`.
The different commands have different configurations for `l`,
`group_by_filename` and `where_desc`.
If `slow` is false, doesn't do the checks that take a lot of time.
If `verbose` is false, it will suppress messages from passing checks.
By setting `checks` you can customize which checks are performed.

Returns a `name_set` containing the names of all declarations that fail any check in `check`,
and a `format` object describing the failures. -/
meta def lint_aux (decls : list declaration) (group_by_filename : option ℕ)
    (where_desc : string) (slow : bool) (verbose : lint_verbosity) (checks : list (name × linter)) :
  tactic (name_set × format) := do
e ← get_env,
let non_auto_decls := decls.filter (λ d, ¬ d.is_auto_or_internal e),
results ← lint_core decls non_auto_decls checks,
let s := format_linter_results e results decls non_auto_decls
  group_by_filename where_desc slow verbose checks.length,
let ns := name_set.of_list (do (_,_,rs) ← results, rs.keys),
pure (ns, s)

/-- Return the message printed by `#lint` and a `name_set` containing all declarations that fail. -/
meta def lint (slow : bool := tt) (verbose : lint_verbosity := lint_verbosity.medium)
  (extra : list name := []) (use_only : bool := ff) : tactic (name_set × format) := do
  checks ← get_checks slow extra use_only,
  e ← get_env,
  let l := e.filter (λ d, e.in_current_file d.to_name),
  lint_aux l none "in the current file" slow verbose checks

/-- Returns the declarations in the folder `proj_folder`. -/
meta def lint_project_decls (proj_folder : string) : tactic (list declaration) := do
e ← get_env,
pure $ e.filter $ λ d, e.is_prefix_of_file proj_folder d.to_name

/-- Returns the linter message by running the linter on all declarations in project `proj_name` in
folder `proj_folder`. It also returns a `name_set` containing all declarations that fail.

To add a linter command for your own project, write
```
open lean.parser lean tactic interactive
@[user_command] meta def lint_my_project_cmd (_ : parse $ tk "#lint_my_project") : parser unit :=
do str ← get_project_dir n k, lint_cmd_aux (@lint_project str "my project")
```
Here `n` is the name of any declaration in the project (like `` `lint_my_project_cmd`` and `k` is
the number of characters in the filename of `n` *after* the `src/` directory
(so e.g. the number of characters in `tactic/lint/frontend.lean`).
Warning: the linter will not work in the file where `n` is declared.
-/
meta def lint_project (proj_folder proj_name : string) (slow : bool := tt)
  (verbose : lint_verbosity := lint_verbosity.medium)
  (extra : list name := []) (use_only : bool := ff) : tactic (name_set × format) := do
checks ← get_checks slow extra use_only,
decls ← lint_project_decls proj_folder,
lint_aux decls proj_folder.length ("in " ++ proj_name ++ " (only in imported files)")
  slow verbose checks

/-- Return the message printed by `#lint_all` and a `name_set` containing all declarations
that fail. -/
meta def lint_all (slow : bool := tt) (verbose : lint_verbosity := lint_verbosity.medium)
  (extra : list name := []) (use_only : bool := ff) : tactic (name_set × format) := do
  checks ← get_checks slow extra use_only,
  e ← get_env,
  let l := e.get_decls,
  lint_aux l (some 0) "in all imported files (including this one)" slow verbose checks

/-- Parses an optional `only`, followed by a sequence of zero or more identifiers.
Prepends `linter.` to each of these identifiers. -/
meta def parse_lint_additions : parser (bool × list name) :=
prod.mk <$> only_flag <*> (list.map (name.append `linter) <$> ident*)

/--
Parses a "-" or "+", returning `lint_verbosity.low` or `lint_verbosity.high` respectively,
or returns `none`.
-/
meta def parse_verbosity : parser (option lint_verbosity) :=
tk "-" >> return lint_verbosity.low <|>
tk "+" >> return lint_verbosity.high <|>
return none

/-- The common denominator of `lint_cmd`, `lint_mathlib_cmd`, `lint_all_cmd` -/
meta def lint_cmd_aux
  (scope : bool → lint_verbosity → list name → bool → tactic (name_set × format)) :
  parser unit :=
do verbosity ← parse_verbosity,
   fast_only ← optional (tk "*"),
   -- allow either order of *-
   verbosity ← if verbosity.is_some then return verbosity else parse_verbosity,
   let verbosity := verbosity.get_or_else lint_verbosity.medium,
   (use_only, extra) ← parse_lint_additions,
   (failed, s) ← scope fast_only.is_none verbosity extra use_only,
   when (¬ s.is_nil) $ trace s,
   when (verbosity = lint_verbosity.low ∧ ¬ failed.empty) $
    fail "Linting did not succeed",
   when (verbosity = lint_verbosity.medium ∧ failed.empty) $
    trace "/- All linting checks passed! -/"

/-- The command `#lint` at the bottom of a file will warn you about some common mistakes
in that file. Usage: `#lint`, `#lint linter_1 linter_2`, `#lint only linter_1 linter_2`.
`#lint-` will suppress the output if all checks pass.
`#lint+` will enable verbose output.

Use the command `#list_linters` to see all available linters. -/
@[user_command] meta def lint_cmd (_ : parse $ tk "#lint") : parser unit :=
lint_cmd_aux @lint

/-- The command `#lint_mathlib` checks all of mathlib for certain mistakes.
Usage: `#lint_mathlib`, `#lint_mathlib linter_1 linter_2`, `#lint_mathlib only linter_1 linter_2`.
`#lint_mathlib-` will suppress the output if all checks pass.
`lint_mathlib+` will enable verbose output.

Use the command `#list_linters` to see all available linters. -/
@[user_command] meta def lint_mathlib_cmd (_ : parse $ tk "#lint_mathlib") : parser unit :=
do str ← get_mathlib_dir, lint_cmd_aux (@lint_project str "mathlib")

/-- The command `#lint_all` checks all imported files for certain mistakes.
Usage: `#lint_all`, `#lint_all linter_1 linter_2`, `#lint_all only linter_1 linter_2`.
`#lint_all-` will suppress the output if all checks pass.
`lint_all+` will enable verbose output.

Use the command `#list_linters` to see all available linters. -/
@[user_command] meta def lint_all_cmd (_ : parse $ tk "#lint_all") : parser unit :=
lint_cmd_aux @lint_all

/-- The command `#list_linters` prints a list of all available linters. -/
@[user_command] meta def list_linters (_ : parse $ tk "#list_linters") : parser unit :=
do env ← get_env,
let ns := env.decl_filter_map $ λ dcl,
    if (dcl.to_name.get_prefix = `linter) && (dcl.type = `(linter)) then some dcl.to_name else none,
   trace "Available linters:\n  linters marked with (*) are in the default lint set\n",
   ns.mmap' $ λ n, do
     b ← has_attribute' `linter n,
     trace $ n.pop_prefix.to_string ++ if b then " (*)" else ""

/--
Invoking the hole command `lint` ("Find common mistakes in current file") will print text that
indicates mistakes made in the file above the command. It is equivalent to copying and pasting the
output of `#lint`. On large files, it may take some time before the output appears.
-/
@[hole_command] meta def lint_hole_cmd : hole_command :=
{ name := "Lint",
  descr := "Lint: Find common mistakes in current file.",
  action := λ es, do (_, s) ← lint, return [(s.to_string,"")] }

add_tactic_doc
{ name                     := "Lint",
  category                 := doc_category.hole_cmd,
  decl_names               := [`lint_hole_cmd],
  tags                     := ["linting"] }
