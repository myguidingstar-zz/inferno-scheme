This project is for a scheme interpreter and any applications written in scheme.
This is basically a scheme interpreter that meets the `r4rs` "standard" (almost) with aspirations to meet the `r5rs` standard.
The last part of `r5rs` that will likely be implemented (if ever) is the macro support.
Also, unlike `r4rs` and `r5rs`, but like `r7rs`, this interpreter is case-sensitive.
Thus (eq? 'abc 'AbC) => #f.

## Current Status ##
  * `r4rs`: all essential procedures except
    * (call-with-current-continuation)
  * `r5rs`: all non-optional features but
    * (char-ready?)
    * (call-with-current-continuation)
    * (values)
    * (call-with-values)
    * (dynamic-wind)
    * (define-syntax)
    * (let-syntax)
    * (letrec-syntax)
    * (syntax-rules)
  * Enhancements:
    * (<-=)
    * (=<-)
    * (alt)
    * (channel)
    * (close-inout-port)
    * (open-inout-file)
    * (open-input-string)
    * (popen cmd-string)
    * (readfile)
    * (readline)
    * (quit)
    * (sleep)
    * (spawn)
  * Bugs/Limitations
    * No complex numbers
    * No compiler
    * Error handling should be better
    * Proper tail calls only partial with little testing

The implementation is not the cleanest thing in the world as it's the largest thing I've ever written in Limbo.
But it seems to work pretty well for a relatively quick hack.
It currently totals about 4600 lines of Limbo code divided into 5 modules:
  1. cell.b - core cell, pair, and environment routines
  1. sform.b - functions that implement special forms
  1. builtin.b - functions that implement built-in procedures
  1. scheme.b - top-level REPL functions
  1. extension.b - Inferno scheme extensions

Some procedures are implemented in scheme, rather than directly as built-in functions.
They are located in /lib/scheme/library.scm.