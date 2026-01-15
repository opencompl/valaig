macro:50 "rlet" pat:term ":=" expr:term rest:term : term =>
  `(match _ : $expr:term with
      | $pat => $rest)

macro:50 "rlet" h:ident ":" pat:term ":=" expr:term rest:term : term =>
  `(match $h:ident : $expr:term with
      | $pat => $rest)

macro:50 "rlet" pat:term "←" expr:term  rest:term : term =>
  `(match _ : $expr:term with
      | none => none
      | some $pat => $rest)

macro:50 "rlet" h:ident ":" pat:term "←" expr:term  rest:term : term =>
  `(match $h:ident : $expr:term with
      | none => none
      | some $pat => $rest)
