module

public import Lean.Meta.Tactic.Grind.RegisterCommand
public import Lean.Meta.Tactic.Simp.RegisterCommand

namespace Valaig

scoped macro:50 "rlet" pat:term ":=" expr:term rest:term : term =>
  `(match _ : $expr:term with
      | $pat => $rest)

scoped macro:50 "rlet" h:ident ":" pat:term ":=" expr:term rest:term : term =>
  `(match $h:ident : $expr:term with
      | $pat => $rest)

scoped macro:50 "rlet" pat:term "←" expr:term  rest:term : term =>
  `(match _ : $expr:term with
      | none => none
      | some $pat => $rest)

scoped macro:50 "rlet" h:ident ":" pat:term "←" expr:term  rest:term : term =>
  `(match $h:ident : $expr:term with
      | none => none
      | some $pat => $rest)

namespace Aig

register_grind_attr grind_valaig_defs
register_simp_attr simp_valaig_defs

scoped macro "simp_defs" : tactic => `(tactic| (simp [simp_valaig_defs]))
scoped macro "simp_all_defs" : tactic => `(tactic| (simp_all [simp_valaig_defs]))

set_option hygiene false in
scoped macro "grind_defs" : tactic => `(tactic| (grind [grind_valaig_defs]))

end Aig
