;;; To use the driver for Assignment 1, create a file containing:
;;;
 (eval-when (compile load eval)
   (optimize-level 2)
   (case-sensitive #t)
 )

 (load "match.scm")
 (load "helpers.scm")
 (load "fmts.pretty")     ; inform pretty-print about new forms
 (load "driver.scm")

 (load "a15.scm")
 (load "a15-wrapper.scm")   ; defines syntactic forms and procedures
                          ; needed to output of each pass

(compiler-passes '(
parse-scheme
convert-complex-datum
uncover-assigned
purify-letrec
convert-assignments
optimize-direct-call
remove-anonymous-lambda
sanitize-binding-forms
uncover-free
convert-closures
optimize-known-call
introduce-procedure-primitives
lift-letrec
normalize-context
specify-representation
uncover-locals
remove-let
verify-uil
remove-complex-opera*
flatten-set!
impose-calling-conventions
expose-allocation-pointer
uncover-frame-conflict
pre-assign-frame
assign-new-frame
(iterate
finalize-frame-locations
select-instructions
uncover-register-conflict
assign-registers
(break when everybody-home?)
assign-frame)
discard-call-live
finalize-locations
expose-frame-var
expose-memory-operands
expose-basic-blocks
optimize-jumps
flatten-program
generate-x86-64
))

 (load "tests15.scm")

;;;
;;; Load this into Chez Scheme, and type (test-all) to run all of the
;;; valid tests, or (test-all-invalid) to run all of the invalid tests.
;;; Use test-one or test-one-invalid to run an individual test.

(define-who everybody-home?
(define all-home?
(lambda (body)
(match body
[(locals (,local* ...)
(ulocals (,ulocal* ...)
(spills (,spill* ...)
(locate (,home* ...)
(frame-conflict ,ct ,tail))))) #f]
[(locate (,home* ...) ,tail) #t]
[,x (error who "invalid Body ˜s" x)])))
(lambda (x)
(match x
[(letrec ([,label* (lambda () ,body*)] ...) ,body)
(andmap all-home? `(,body ,body* ...))]
[,x (error who "invalid Program ˜s" x)])))
