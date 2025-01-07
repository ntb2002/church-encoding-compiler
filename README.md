# Project 4: Church Encoding Compiler for Scheme
## CIS352 -- Spring 2024

In this project, you will implement a compiler for a significant
subset of Scheme to the lambda calculus. In other words, you will
write a function `church-compile`, which accepts as input a Scheme
expression (defined below) and generates as output an S-expression
corresponding to a lambda calculus term (in the style we have shown in
class). To test your code, we then convert the output of your function
to Racket using `eval` (a construct that allows us to convert an
S-expression to Racket code to execute).

To be very clear, you will receive inputs that look like this (further
specified below):

```
'(+ 1 1)
```

And you will output things that look like this:

```
'(((lambda (n)
    (lambda (k) 
      (lambda (f) (lambda (x) ((k f) ((n f) x))))))
	  (lambda (f) (lambda (x) (f x))))
  (lambda (f) (lambda (x) (f x))))
```

Our tests then execute these lambda calculus terms and convert them
back to numbers/booleans as appropriate (using, e.g., `church->nat`).

## Input language

The input language will be given as S-expressions that have the
following structure:

```
e ::= (letrec ([x (lambda (x ...) e)]) e)
    | (let ([x e] ...) e)
    | (let* ([x e] ...) e)
    | (lambda (x ...) e)
    | (e e ...)
    | x
    | (and e ...) | (or e ...)
    | (if e e e)
    | (prim e) | (prim e e)
    | datum

datum ::= nat | (quote ()) | #t | #f
nat ::= 0 | 1 | 2 | ...
x is a symbol
prim is a primitive function.
```

In other words, you must support let (with any number of bindings,
including zero), let*, lambda, application, variables, and/or
(short-circuiting as necessary), if, applications of unary and binary
primitive functions, and constants (called "datums").

You must support the following primitive functions:

```
+ * - = add1 sub1 cons car cdr null? not zero?
```

Your input language has semantics identical to Scheme / Racket, except:
 + All numbers will be naturals
 + You will not be provided code that yields any kind of error in Racket
 + You do not need to treat non-boolean values as #t at if, and, or forms
 + primitive operations are either strictly unary (add1 sub1 null? zero? not car cdr),
   or binary (+ - * = cons) rather than k-ary
 + There will be no variadic functions or applications---but any fixed arity is allowed

There are some bonus tests that require you to implement -, =, and
sub1. These are more challenging, and thus extra credit. Encodings for
those functions are not given in the slides in class, but they can be
looked up online (or puzzled out for yourself).

Note that implementing letrec correctly involves using a fixed-point
combinator (such as the Y/Z combinator). We will discuss this
transformation in class and give hints. If you are stuck on this,
watch the YouTube lecture I post "Fixed Points." It is intended
precisely to help you tackle this case.

## Output language:

Your `church-compile` function should generate S-expressions in the lambda calculus:

e ::= (lambda (x) e)
    | (e e)
    | x
where x is a symbol? representing a variable



