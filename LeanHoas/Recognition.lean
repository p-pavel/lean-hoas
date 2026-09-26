import LeanHoas.Setup

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "You Have Built This Before" =>
%%%
number := false
tag := "built-this-before"
%%%

Take the rules language inside a billing, pricing, or workflow system. Often
nobody planned it; it just grew. It starts with plain expressions:

```
price * quantity
```

Then someone needs a local value:{margin}[Spreadsheet `LET`, SQL `WITH`, or
an assignment followed by `return` all have this shape.]

```
let discount = customer.discount in price * (1 - discount)
```

or a condition checked for each item:

```
orders.filter(order => order.total > limit)
```

Now one part of the expression introduces a name, `discount` or `order`,
and another part uses it. That is variable binding. If you have built such a
system, you have implemented it, perhaps without calling it that, and you
have met its questions. Which `order` does this `order` refer to when rules
are nested? What happens when one rule is plugged into another and both use
the name `order`? When are two rules the same rule with different names?
These questions have standard answers and standard names: scope, capture,
α-equivalence, substitution. The next chapters use them.{margin}[Embedding
Python or JavaScript borrows their variable binding, but turns rules into
opaque code: you can run them, but not inspect, store, check, or transform
them. The idea of this book is to borrow the host's binding and keep the
rules as data.]

Now throw away prices, orders, and workflows, and keep only the mechanism
that causes the trouble: names, where they are introduced, and where they
are used. That core is the λ-calculus (lambda calculus), and it has three
constructs:

 * `var x` is a use of the name `x`.
 * `lam x b` introduces `x` and lets the body `b` refer to it: a function
   with parameter `x`, traditionally written `λx. b`, in Lean `fun x => b`.
 * `app f a` applies a function to an argument.

In these terms, `order => order.total > limit` is `lam order b`, where the
body `b` is `order.total > limit`. Each `order` inside `b` is a
`var order`, and handing that function to `filter` is an `app`. Likewise,
`let x = e in b` behaves like `app (lam x b) e`: make a one-parameter
function with body `b`, and call it on `e`.

The λ-calculus does not solve anyone's business problem. It isolates the
part of it we want to study, the way a laboratory organism keeps the
mechanism of interest and little else. The next chapter builds it in Lean,
names first, and shows where it breaks.
