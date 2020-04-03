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

# Induction

Idris code in [Induction.idr](Induction.idr)

Compare proof by induction in Coq

```
Theorem plus_n_O : forall n:nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)    reflexivity.
  - (* n = S n' *) simpl. rewrite <- IHn'. reflexivity.  Qed.

```

with Idris:

```
plus_n_0 : (n:Nat) -> (n + 0 = n)
plus_n_0 Z = Refl
plus_n_0 (S k) =
  let ind = plus_n_0 k
  in rewrite ind in Refl
```

* Induction hypothesis is "just" calling the function recursively with a smaller element

Proof of `minus_diag` is slightly more involved in Idris:

```
minus_diag : (n:Nat) -> {auto prf: LTE n n} -> (n - n = 0)
minus_diag Z = Refl
minus_diag (S k) {prf = LTESucc prf' } = minus_diag k
```

The `prf` argument is needed by `(-)` (`minus`) definition: To substract to `Nat`s one has to prove the first argument is greater than or equal to the second argument. We build a proof for the inductive case by pattern-matching on the structure of `prf` which is defined by:

```
λΠ> :doc LTE
Data type Prelude.Nat.LTE : (n : Nat) -> (m : Nat) -> Type
    Proofs that n is less than or equal to m
    Arguments:
        n : Nat  -- the smaller number

        m : Nat  -- the larger number

    The function is: public export
Constructors:
    LTEZero : LTE 0 right
        Zero is the smallest Nat

        The function is: public export
    LTESucc : LTE left right -> LTE (S left) (S right)
        If n <= m, then n + 1 <= m + 1
```

The `auto` qualifier instructs the typechecker to look for the proof in the environment.
