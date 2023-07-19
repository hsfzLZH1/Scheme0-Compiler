# Scheme0-Compiler
A Compiler from Scheme0 to x86-64 written in Scheme.

This compiler accepts valid Scheme0 programs and rejects invalid ones.

I owe many thanks to @[luke36](https://github.com/luke36) for his help.

## 

The grammar for Scheme0, a subset of Scheme:

```
Program  --> Expr
Expr     --> constant
          |  var
          |  (quote datum)
          |  (if Expr Expr)
          |  (if Expr Expr Expr)
          |  (and Expr*)
          |  (or Expr*)
          |  (begin Expr* Expr)
          |  (lambda (var*) Expr+)
          |  (let ([var Expr]*) Expr+)
          |  (letrec ([var Expr]*) Expr+)
          |  (set! var Expr)
          |  (prim Expr*)
          |  (Expr Expr*)

datum    --> constant | (datum*) | #(datum*)
constant --> #t | #f | () | fixnum
```

where:

- `fixnum` is an exact integer (61-bit in this implementation);

- `var` is an arbitrary symbol (no names are reserved);

- Valid `prim` names and argument counts are given by the following table:

|        name         | arguments |
|:-------------------:|:---------:|
|      `fixnum?`      |     1     |
|       `+ - *`       |     2     |
|     `boolean?`      |     1     |
|    `<= < = > >=`    |     2     |
|        `not`        |     1     |
|    `null? pair?`    |     1     |
|      `car cdr`      |     1     |
|       `cons`        |     2     |
| `set-car! set-cdr!` |     2     |
|      `vector?`      |     1     |
|   `vector-length`   |     1     |
|    `vector-ref`     |     2     |
|    `vector-set!`    |     3     |
|        `eq?`        |     2     |
|    `procedure?`     |     1     |
|       `void`        |     0     |

## 

To use the compiler,

```
scheme
> (load "test.scm")
> (test-one Scheme0-Program)
```

x86-64 will be generated in `t.s` in the same directory.

## 

Todolist:

- Handle simple bindings in pass `purify-letrec` ;

- Add some optimization passes.
