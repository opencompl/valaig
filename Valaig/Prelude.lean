module

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

scoped macro_rules
| `(tactic| get_elem_tactic_extensible) => `(tactic| grind)

end Aig
