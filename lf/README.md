# Basics

This highlights the fact we really can do _Test-Driven Development_ in Coq (or any DT language for that matter:

```
Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.

Proof. simpl. reflexivity.  Qed.
```

The `Example` introduces a new _subgoal_

```
1 subgoal (ID 3)

  ============================
  next_weekday (next_weekday saturday) = tuesday
```

which is proved by the following statements.

Equivalent code in idris is in [Basics.idr](Basics.idr). Note the main differences:

* Constructor names are capitalized in order to prevent ambiguities in name resolutions. By default, lower case identifiers are _variables_
* Proof construction is given in the _same language_ than the type and function declarations.
* Namespaces require qualified names to prevent ambiguities inside the namespace which is more cumbersome than in Coq
