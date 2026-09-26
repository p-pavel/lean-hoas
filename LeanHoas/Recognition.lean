import LeanHoas.Setup

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "You Have Built This Before" =>
%%%
number := false
tag := "built-this-before"
%%%

Take the rules language inside a billing, pricing, or workflow system. Often
nobody planned it; it just grew. This section retells its usual history,
because the history is the problem this book is about.

# Expressions Are Easy

It starts with plain expressions:

```
price * quantity
```

Every programmer knows what to do. Parse the text into a tree, an _abstract
syntax tree_:

```
Mul(Field("price"), Field("quantity"))
```

Then write an evaluator: a recursive function over the tree, one case per
kind of node. Printing, validation, and simple optimizations are recursive
functions of the same shape. It works, and it feels clean. Every subtree
means something on its own, and the meaning of a node depends only on the
meanings of its children.

# The Edge

Then someone needs a local value:{margin}[Spreadsheet `LET`, SQL `WITH`, or
an assignment followed by `return` all have this shape.]

```
let discount = customer.discount in price * (1 - discount)
```

or a condition checked for each item:

```
orders.filter(order => order.total > limit)
```

It looks like one more kind of node. It is not. Now one part of the
expression introduces a name, `discount` or `order`, and another part uses
it. On its own, `order.total > limit` means nothing: it depends on which
`order` is meant, and that is decided somewhere above it in the tree.
Subtrees are no longer self-contained, and every operation on the tree, not
just evaluation, now has to know where each name came from.

This is the edge between expressions and computation. Crossing it is not a
matter of more careful programming; the problem itself changes. It has a
name, _variable binding_, and a construct that introduces a name, such as
`let` or `order =>`, is a _binder_.

# Now What?

Typically the evaluator grows an environment, a map from names to values,
extended on the way into each binder. Then the reports start:

 * A rule that works alone breaks when nested, because an inner `order`
   hides an outer one. Or a callback runs later, after a shared environment
   has moved on, and sees the wrong `order`. Both are questions of _scope_:
   which binder does a use of a name belong to?
 * Someone inlines one rule into another, and both use the name `x`. The
   inlined rule silently starts referring to the wrong thing. Inlining is
   _substitution_, and this failure is called _capture_; the first chapter
   reproduces it in a few lines.
 * Caching, deduplication, and change detection treat two rules as different
   although they differ only in the names chosen. Deciding when two rules
   are the same up to renaming is called _α-equivalence_.

These are not signs of sloppy work. They are what this problem looks like
when it is solved without its vocabulary.

# The Usual Ways Out

Teams react in a few predictable ways. Some forbid nesting, reserve magic
names like `$it` or `$1`, or prefix every name to keep them apart: fixes that
hold until the next requirement. Some replace names with numbers, such as
slot positions or ids. Renaming problems disappear, and off-by-one errors
take their place; that route has a name too, _de Bruijn indices_, and it is
the second chapter.

And many give up and embed a general-purpose language such as Python,
JavaScript, or Lua. Binding is then correct, because the host language does
it. But the rules become opaque code: they can be run, but no longer
inspected, stored, compared, or transformed.

The last route has the right instinct. Letting the host language do the
binding is the idea of this book. What it gives up, rules that remain data,
is what the book wins back: first by storing host-language functions inside
the syntax tree, which is where the name _higher-order abstract syntax_
comes from, and then by making that work inside Lean's logic.

# The Core

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
