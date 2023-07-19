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

;;;

(define parse-scheme
  (lambda (program)
    (letrec (

[argsnum-list
  `((+ 2) (- 2) (* 2) (car 1) (cdr 1) (cons 2) (make-vector 1) (vector-length 1) (vector-ref 2) (void 0)
    (<= 2) (< 2) (= 2) (>= 2) (> 2) (boolean? 1) (eq? 2) (fixnum? 1) (null? 1) (pair? 1) (vector? 1) (procedure? 1)    (set-car! 2) (set-cdr! 2) (vector-set! 3))]

[var->uvar
  (lambda (x)
    (unique-name x))]

[Expr-env
  (lambda (env)
    (lambda (x) (Expr env x)))]

[datum?
  (lambda (x)
    (cond [(or (eqv? x #t) (eqv? x #f) (eqv? x '())) #t]
          [(int64? x) (if (fixnum-range? x) #t #f)]
          [(list? x) (let ([tf (map datum? x)]) (not (memv #f tf)))]
          [(vector? x) (let ([tf (map datum? (vector->list x))]) (not (memv #f tf)))]))]

[Expr
  (lambda (env expr)
    (match expr
      [,x (guard (assq x env))
        (cadr (assq x env))]
      [(,x ,expr* ...) (guard (assq x env))
        (let ([expr2 (map (Expr-env env) expr*)])
          `(,(cadr (assq x env)) ,@expr2))]
      [#t `(quote ,expr)]
      [#f `(quote ,expr)]
      [() `(quote ,expr)]
      [,x (guard (int64? x))
        (if (fixnum-range? x) `(quote ,expr)
          (format-error Expr "Integer ~s out of fixnum range" x))]
      [(quote ,x) (guard (datum? x)) expr]
      [(if ,p ,t ,f)
        `(if ,(Expr env p) ,(Expr env t) ,(Expr env f))]
      [(if ,p ,t)
        `(if ,(Expr env p) ,(Expr env t) (void))]
      [(begin ,[(Expr-env env) -> expr*] ...)
	(make-begin expr*)]
      [(lambda ,var* ,expr* ...)
        (if (eq? (length (unique var*)) (length var*)) (void)
	  (format-error Expr "Same name variable in lambda form ~s" expr))
        (let ([uvar* (map var->uvar var*)])
	  `(lambda ,uvar* ,(Expr (append `((,var* ,uvar*) ...) env) (make-begin expr*))))]
      [(let ([,var* ,[(Expr-env env) -> expr*]] ...) ,expr ...)
        (if (eq? (length (unique var*)) (length var*)) (void)
          (format-error Expr "Same name variable in let form ~s" expr))
        (let ([uvar* (map var->uvar var*)])
	  `(let ([,uvar* ,expr*] ...) ,(Expr (append `((,var* ,uvar*) ...) env) (make-begin expr))))]
      [(letrec ([,var* ,expr*] ...) ,expr ...)
        (if (eq? (length (unique var*)) (length var*)) (void)
          (format-error Expr "Same name variable in letrec form ~s" expr))
        (let* ([uvar* (map var->uvar var*)]
	       [env2 (append `((,var* ,uvar*) ...) env)]
	       [expr2 (map (lambda (x) (Expr env2 x)) expr*)])
	  `(letrec ([,uvar* ,expr2] ...) ,(Expr env2 (make-begin expr))))]
      [(set! ,var ,expr)
        (if (assq var env)
	  `(set! ,(cadr (assq var env)) ,(Expr env expr))
	  (format-error Expr "Unbounded variable ~s" var))]
      [(and ,expr0 ...)
        (cond [(null? expr0) '(quote #t)]
	      [(null? (cdr expr0)) (let ([t (unique-name 't)])
				     `(let ([,t ,(Expr env (car expr0))])
					(if ,t ,t (quote #f))))]
	      [else `(if ,(Expr env (car expr0))
	              ,(Expr env `(and ,@(cdr expr0)))
	              (quote #f))])]
      [(or ,expr0 ...)
        (if (null? expr0) '(quote #f)
	  (let ([t (unique-name 't)])
	    `(let ([,t ,(Expr env (car expr0))])
	      (if ,t ,t
		,(Expr env `(or ,@(cdr expr0)))))))]
      [(not ,expr)
        `(if ,(Expr env expr) (quote #f) (quote #t))]
      [(,prim ,expr* ...) (guard (memv prim prim-list))
	(if (eq? (length expr*) (cadr (assq prim argsnum-list))) (void)
	  (format-error Expr "Incorrect argument number of ~s : ~s" prim expr))
	(let ([expr2 (map (lambda (x) (Expr env x)) expr*)])
	  `(,prim ,@expr2))]
      [(,[(Expr-env env) -> expr] ,[(Expr-env env) -> expr*] ...)
	`(,expr ,@expr*)]
      [,x (format-error Expr "Unmatched ~s" expr)]))])
    (Expr '() program))))

;;;

(define convert-complex-datum
  (lambda (program)
    (letrec (

[binds '()]

[Expr
  (lambda (program)
    (match program
      [(quote ,i) (guard (not (pair? i)) (not (vector? i))) program]
      [(quote ,i)
        (let [(u (unique-name 'pv))]
          (set! binds (cons `(,u ,(datum->code i)) binds))
          u)]
      [,x (guard (pair? x)) (map Expr x)]
      [,x x]))]

[datum->code
  (lambda (datum)
    (cond [(pair? datum) `(cons ,(datum->code (car datum)) ,(datum->code (cdr datum)))]
          [(vector? datum)
            (let ([u (unique-name 'vec)])
              `(let ([,u (make-vector (quote ,(vector-length datum)))])
                 (begin ,@(Vec datum 0 u) ,u)))]
          [else `(quote ,datum)]))]

[Vec
  (lambda (vec n uvar)
    (if (< n (vector-length vec))
      (cons `(vector-set! ,uvar (quote ,n) ,(datum->code (vector-ref vec n))) (Vec vec (+ n 1) uvar))
      '()))])

    (set! binds '())
    (let ([body (Expr program)])
      `(let ,binds ,body)))))

;;;

(define uncover-assigned
  (lambda (program)
    (letrec (

[Expr
  ;returns (program-added-assign-forms assigned-uvar-list)
  (lambda (program)
    (match program
      [(let ([,uvar* ,expr*] ...) ,body)
        (let-values ([(prog* uls*) (map-Expr expr*)]
                     [(prog uls) (Expr body)])
          (values `(let ([,uvar* ,prog*] ...) (assigned ,(intersection uvar* (unique (append uls* uls))) ,prog))
                  (append uls uls*)))]
      [(letrec ([,uvar* ,expr*] ...) ,body)
        (let-values ([(prog* uls*) (map-Expr expr*)]
                     [(prog uls) (Expr body)])
          (values `(letrec ([,uvar* ,prog*] ...) (assigned ,(intersection uvar* (unique (append uls* uls))) ,prog))
                  (append uls uls*)))]
      [(lambda ,uvar ,body)
        (let-values ([(prog uls) (Expr body)])
          (values `(lambda ,uvar (assigned ,(intersection uvar (unique uls)) ,prog)) uls))]
      [(set! ,x ,expr)
        (let-values ([(prog uls) (Expr expr)])
          (values `(set! ,x ,prog) (cons x uls)))]
      [,x (guard (pair? x)) (map-Expr x)]
      [,x (values x '())]))]

[map-Expr
  (lambda (ls)
    (cond [(null? ls) (values '() '())]
          [else (let-values ([(p1 l1) (Expr (car ls))]
                             [(p2 l2) (map-Expr (cdr ls))])
                  (values (cons p1 p2) (append l1 l2)))]))])

    (let-values ([(prog assinged) (Expr program)]) prog))))

;;;

(define purify-letrec
  (lambda (program)
    (letrec (

[divide-lc
  (lambda (x* e* ls)
    (if (null? x*) (values '() '() '() '())
      (let-values ([(xl2 el2 xc2 ec2) (divide-lc (cdr x*) (cdr e*) ls)])
        (match (car e*)
          [(lambda ,uvar ,b) (guard (not (memv (car x*) ls)))
            (values (cons (car x*) xl2) (cons (car e*) el2) xc2 ec2)]
          [,x (values xl2 el2 (cons (car x*) xc2) (cons (car e*) ec2))]))))]

[make-set!
  (lambda (a* b*)
    (cond [(null? a*) '()]
          [else (cons `(set! ,(car a*) ,(car b*)) (make-set! (cdr a*) (cdr b*)))]))])

    (match program
      [(letrec ([,x* ,[e*]] ...) (assigned ,ls ,[b]))
        (let-values ([(xl el xc ec) (divide-lc x* e* ls)])
	  (cond [(null? x*) b]
		[(null? xc) `(letrec ([,xl ,el] ...) ,b)]
		[(null? xl)
		  (let ([tc (map (lambda (x) (unique-name 't)) xc)])
		    `(let ([,xc (void)] ...)
                      (assigned ,xc
                        (begin
                          (let ([,tc ,ec] ...) (assigned () ,(make-begin (make-set! xc tc))))
                          ,b))))]
		[#t
		  (let ([tc (map (lambda (x) (unique-name 't)) xc)])
                    `(let ([,xc (void)] ...)
                      (assigned ,xc
			(letrec ([,xl ,el] ...)
                          (begin
                            (let ([,tc ,ec] ...) (assigned () ,(make-begin (make-set! xc tc))))
                            ,b)))))]))]
      [,x (guard (pair? x)) (map purify-letrec x)]
      [,x x]))))

;;;

(define convert-assignments
  (lambda (program)
    (letrec (

[Expr
  (lambda (program assigns)
    (match program
      [(let ([,uvar* ,[(lambda (x) (Expr x assigns)) -> def*]] ...) (assigned ,ls ,expr))
        (let* ([var-tmp (map (lambda (x) (cons x (unique-name (string->symbol (extract-root x))))) ls)]
               [ls2 (map (lambda (x) `(cons ,(cdr (assq x var-tmp)) (void))) ls)]
               [uvar2 (map (lambda (x) (if (assq x var-tmp) (cdr (assq x var-tmp)) x)) uvar*)])
          `(let ([,uvar2 ,def*] ...)
            (let ([,ls ,ls2] ...)
              ,(Expr expr (append assigns ls)))))]
      [(lambda (,uvar* ...) (assigned ,ls ,expr))
        (let* ([var-tmp (map (lambda (x) (cons x (unique-name (string->symbol (extract-root x))))) ls)]
               [ls2 (map (lambda (x) `(cons ,(cdr (assq x var-tmp)) (void))) ls)]
               [uvar2 (map (lambda (x) (if (assq x var-tmp) (cdr (assq x var-tmp)) x)) uvar*)])
          `(lambda ,uvar2
             (let ([,ls ,ls2] ...)
               ,(Expr expr (append assigns ls)))))]
      [(set! ,x ,expr)
        (if (memv x assigns)
          `(set-car! ,x ,(Expr expr assigns))
          `(set! ,x ,(Expr expr assigns)))]
      [,x (guard (pair? x)) (map (lambda (p) (Expr p assigns)) x)]
      [,x (if (memv x assigns) `(car ,x) x)]))])

    (rm-empty-let (Expr program '())))))

;;;

(define optimize-direct-call
  (lambda (program)
    (match program
      [((lambda ,args* ,body) ,actual* ...) (guard (= (length args*) (length actual*)))
	(optimize-direct-call `(let ([,args* ,actual*] ...) ,body))]
      [,x (guard (pair? x))
	(map optimize-direct-call x)]
      [,x x])))

;;;

(define remove-anonymous-lambda
  (lambda (program)
    (letrec (

[Lambda
  (lambda (program)
    (match program
      [(lambda ,args* ,[remove-anonymous-lambda -> body])
        `(lambda ,args* ,body)]
      [,x (remove-anonymous-lambda program)]))])

    (match program
      [(lambda ,args* ,[body])
        (let ([anon (unique-name 'anon)])
          `(letrec ([,anon (lambda ,args* ,body)]) ,anon))]
      [(let ([,u* ,[Lambda -> b*]] ...) ,[body])
        `(let ([,u* ,b*] ...) ,body)]
      [(letrec ([,u* ,[Lambda -> b*]] ...) ,[body])
        `(letrec ([,u* ,b*] ...) ,body)]
      [,x (guard (pair? x))
	(map remove-anonymous-lambda x)]
      [,x x]))))

;;;

(define sanitize-binding-forms
  (lambda (program)
    (letrec (   

[Expr-1
  (lambda (program)
    (match program
      [(let ,binds ,[body])
        (let-values ([(rec lett) (Expr binds)])
          `(letrec ,rec (let ,lett ,body)))]
      [,x (guard (pair? x))
        (map Expr-1 x)]
      [,x x]))]

[Expr
  ;returns (values in-letrec in-let)
  (lambda (binds)
    (cond [(null? binds) (values '() '())]
          [else (let-values ([(rec lett) (Expr (cdr binds))])
                  (match (cadar binds)
                    [(lambda ,args* ,[Expr-1 -> body])
                      (values (cons `(,(caar binds) (lambda ,args* ,body)) rec) lett)]
                    [,[Expr-1 -> x]
                      (values rec (cons `(,(caar binds) ,x) lett))]))]))])

    (rm-empty-let (Expr-1 program)))))

(define rm-empty-let
  (lambda (program)
    (match program
      [(let () ,b) (rm-empty-let b)]
      [(letrec () ,b) (rm-empty-let b)]
      [,x (guard (pair? x)) (map rm-empty-let x)]
      [,x x])))

;;;

(define uncover-free
  (lambda (program)
    (letrec (

[Expr
  ;returns (values expr uvar-used uvar-let)
  (lambda (body)
    (match body
      [(letrec () ,t)
        (let-values ([(expr used lett) (Expr t)])
          (values `(letrec () ,expr) used lett))]
      [(letrec ([,l (lambda ,u ,b)] [,label* (lambda ,uvar* ,body*)] ...) ,t)
        (let-values ([(le lu ll) (Expr b)]
		     [(re ru rl) (Expr `(letrec ([,label* (lambda ,uvar* ,body*)] ...) ,t))])
	  (values (match re
	            [(letrec ,binds ,expr) `(letrec ,(cons `(,l (lambda ,u (free ,(unique (rm (rm lu ll) u)) ,le))) binds) ,expr)])
		  (append lu ru)
		  (append ll rl `(,l) u)))]
      [(let () ,t)
        (let-values ([(expr used lett) (Expr t)])
	  (values `(let () ,expr) used lett))]
      [(let ([,uvar ,expr] [,uvar* ,expr*] ...) ,t)
        (let-values ([(le lu ll) (Expr expr)]
		     [(re ru rl) (Expr `(let ([,uvar* ,expr*] ...) ,t))])
	  (values (match re
		    [(let ,binds ,expr) `(let ,(cons `(,uvar ,le) binds) ,expr)])
		  (append lu ru)
		  (append ll rl `(,uvar))))]
      [(if ,p ,t ,f)
        (let-values ([(pe pu pl) (Expr p)]
		     [(te tu tl) (Expr t)]
		     [(fe fu fl) (Expr f)])
	  (values `(if ,pe ,te ,fe) (append pu tu fu) (append pl tl fl)))]
      [(begin ,expr* ...)
        (let-values ([(e u l) (Expr-1 expr*)])
	  (values (make-begin e) u l))]
      [(quote ,i) (values body '() '())]
      [(,prim ,args* ...) (guard (memv prim prim-list))
	(let-values ([(e u l) (Expr-1 args*)])
	  (values `(,prim ,@e) u l))]
      [(,expr* ...) (Expr-1 expr*)]
      [,x (guard (uvar? x)) (values x `(,x) '())]))]
[Expr-1
  ;return (values (fixed-letrec-expr used lett))
  (lambda (ls)
    (cond [(null? ls) (values '() '() '())]
          [else (let-values ([(le lu ll) (Expr (car ls))]
                             [(re ru rl) (Expr-1 (cdr ls))])
                  (values (cons le re) (append lu ru) (append ll rl)))]))])
    (let-values ([(e u l) (Expr program)]) e))))

;;;

(define convert-closures
  (lambda (program)
    (match program
      [(letrec () ,[t])
        `(letrec () (closures () ,t))]
      [(letrec ([,l (lambda ,u (free ,free* ,[b]))] ,binds* ...) ,t)
        (let ([expr (convert-closures `(letrec ,binds* ,t))]
	      [cp (unique-name 'cp)])
	  (match expr
	    [(letrec ,binds (closures ,ls ,tail))
	      `(letrec ,(cons `(,(unique-label l) (lambda ,(cons cp u) (bind-free ,(cons cp free*) ,b))) binds)
		 (closures ,(cons `(,l ,(unique-label l) ,@free*) ls) ,tail))]))]
      [(let ([,uvar* ,[expr*]] ...) ,[t])
        `(let [(,uvar* ,expr*) ...] ,t)]
      [(if ,[p] ,[t] ,[f])
        `(if ,p ,t ,f)]
      [(begin ,[expr*] ...)
        `(begin ,@expr*)]
      [(quote ,i) `(quote ,i)]
      [(,prim ,args* ...) (guard (memv prim prim-list))
        `(,prim ,@(map convert-closures args*))]
      [(,[expr] ,[expr*] ...)
        (if (pair? expr) 
          (let ([tmp (unique-name 'tmp)])
            `(let ([,tmp ,expr]) (,tmp ,tmp ,@expr*)))
	  `(,expr ,expr ,@expr*))]
      [,x (guard (uvar? x)) x])))

;;;

(define optimize-known-call
  (lambda (program)
    (letrec (

[Expr
  (lambda (program closure-ls)
    (match program
      [(letrec ([,label* (lambda ,uvar* ,body*)] ...) (closures ,ls ,body))
        (let ([f (lambda (p) (Expr p (append ls closure-ls)))])
          `(letrec ([,label* (lambda ,uvar* ,(map f body*))] ...) (closures ,ls ,(f body))))]
      [(,expr ,[(lambda (p) (Expr p closure-ls)) -> expr*] ...)
        (if (assq expr closure-ls)
          `(,(cadr (assq expr closure-ls)) ,@expr*)
          `(,expr ,@expr*))]
      [,x (guard (pair? x))
        (map (lambda (p) (Expr p closure-ls)) x)]
      [,x x]))])

    (Expr program '()))))

;;;

(define introduce-procedure-primitives
  (lambda (program)
    (letrec (

[Expr
  (lambda (program ls)
    (match program
      [(closures () ,b) `(let () ,(Expr b ls))]
      [(closures ([,u ,l ,f* ...] ,res* ...) ,b)
        (let ([prog (Expr `(closures ,res* ,b) ls)])
          (match prog
            [(let ,lett ,tail)
              `(let ,(cons `(,u (make-procedure ,l (quote ,(length f*)))) lett)
                 ,(make-begin `(,@(proc-set! u 0 f* ls) ,tail)))]))]
      [(letrec () ,b) `(letrec () (let () ,(Expr b ls)))]
      [(letrec ([,l (lambda ,args (bind-free ,bfls ,b))] ,res* ...) ,body)
        (let ([prog (Expr `(letrec ,res* ,body) ls)])
          (match prog
            [(letrec ,binds* ,tail)
              `(letrec ,(cons `(,l (lambda ,args ,(Expr b bfls))) binds*) ,tail)]))]
      [(let [(,uvar* ,expr*) ...] ,b)
        `(let ([,uvar* ,(map (lambda (p) (Expr p ls)) expr*)] ...) ,(Expr b ls))]
      [,x (guard (pair? x) (memv (car x) `(quote if begin ,@prim-list)))
        (map (lambda (p) (Expr p ls)) x)]
      [(,expr ,args* ...)
        (if (label? expr) `(,expr ,@(map (lambda (p) (Expr p ls)) args*))
        `((procedure-code ,(Expr expr ls)) ,@(map (lambda (p) (Expr p ls)) args*)))]
      [,x (if (and (uvar? x) (memv x ls))
            `(procedure-ref ,(car ls) (quote ,(- (length ls) (length (memv x ls)) 1))) x)]))]

[proc-set!
  (lambda (u n frees ls)
    (cond [(null? frees) '()]
          [else (cons `(procedure-set! ,u (quote ,n)
                                       ,(if (memv (car frees) ls)
                                          `(procedure-ref ,(car ls) (quote ,(- (length ls) (length (memv (car frees) ls)) 1)))
                                          (car frees)))
                      (proc-set! u (+ n 1) (cdr frees) ls))]))])

    (Expr program '()))))

;;;

(define lift-letrec
  (lambda (program)
    (letrec (

[binds '()]

[Expr
  (lambda (expr)
    (match expr
      [(letrec ([,label* (lambda ,uvar* ,[expr*])] ...) ,t)
        (set! binds (append binds `([,label* (lambda ,uvar* ,expr*)] ...)))
        (Expr t)]
      [,x (guard (pair? x))
        (map Expr x)]
      [,x x]))])

    (let ([expr (Expr program)])
      `(letrec ,binds ,expr)))))

;;;

(define normalize-context
  (lambda (program)
    (letrec (

[Value-prim '(+ - * car cdr cons make-vector vector-length vector-ref void make-procedure procedure-ref procedure-code)]

[Pred-prim '(<= < = >= > boolean? eq? fixnum? null? pair? vector? procedure?)]

[Effect-prim '(set-car! set-cdr! vector-set! procedure-set!)]

[Value
  (lambda (expr)
    (match expr
      [(begin ,[Effect -> e*] ... ,[t])
        `(begin ,e* ... ,t)]
      [(if ,[Pred -> p] ,[t] ,[f])
        `(if ,p ,t ,f)]
      [(let ([,uvar* ,[expr*]] ...) ,[t])
        `(let ([,uvar* ,expr*] ...) ,t)]
      [(quote ,i) `(quote ,i)]
      [(,vop ,arg* ...) (guard (memv vop Value-prim))
        `(,vop ,@(map Value arg*))]
      [(,pop ,arg* ...) (guard (memv pop Pred-prim))
        `(if (,pop ,@(map Value arg*)) '#t '#f)]
      [(,eop ,arg* ...) (guard (memv eop Effect-prim))
        `(begin (,eop ,@(map Value arg*)) (void))]
      [(,[expr*] ...)
        `(,expr* ...)]
      [,x x]))]

[Pred
  (lambda (expr)
    (match expr
      [(begin ,[Effect -> e*] ... ,[t])
        `(begin ,e* ... ,t)]
      [(if ,[p] ,[t] ,[f])
        `(if ,p ,t ,f)]
      [(let ([,uvar* ,[Value -> expr*]] ...) ,[t])
        `(let ([,uvar* ,expr*] ...) ,t)]
      [(quote ,i) (if (eqv? i '#f) `(false) `(true))]
      [(,pop ,arg* ...) (guard (memv pop Pred-prim))
        `(,pop ,@(map Value arg*))]
      [(,eop ,arg* ...) (guard (memv eop Effect-prim))
        `(begin (,eop ,@(map Value arg*)) (true))]
      [(,[Value -> expr*] ...)
        `(if (eq? (,expr* ...) '#f) (false) (true))]
      [,x `(if (eq? ,x '#f) (false) (true))]))]

[Effect
  (lambda (expr)
    (match expr
      [(begin ,[e*] ... ,[t])
        `(begin ,e* ... ,t)]
      [(if ,[Pred -> p] ,[t] ,[f])
        `(if ,p ,t ,f)]
      [(let ([,uvar* ,[Value -> expr*]] ...) ,[t])
        `(let ([,uvar* ,expr*] ...) ,t)]
      [(quote ,i) `(nop)]
      [(,vop ,arg* ...) (guard (memv vop Value-prim))
        (make-nopless-begin (map Effect arg*))]
      [(,pop ,arg* ...) (guard (memv pop Pred-prim))
        (make-nopless-begin (map Effect arg*))]
      [(,eop ,arg* ...) (guard (memv eop Effect-prim))
        `(,eop ,@(map Value arg*))]
      [(,[Value -> expr*] ...)
        `(,expr* ...)]
      [,x `(nop)]))])

    (match program
      [(letrec ([,label* (lambda ,uvar* ,[Value -> body*])] ...) ,[Value -> body])
        `(letrec ([,label* (lambda ,uvar* ,body*)] ...) ,body)]))))

;;;

(define specify-representation
  (lambda (program)
    (letrec (

[Body
  (lambda (body)
    (match body
      [(quote ,i)
        (cond [(int64? i) (fxsll i shift-fixnum)]
	      [(eqv? i #f) $false]
	      [(eqv? i #t) $true]
	      [else $nil])]
      [(void) $void]
      [(* ,[x] ,[y])
        (cond [(int64? x) `(* ,(sra x shift-fixnum) ,y)]
	      [(int64? y) `(* ,x ,(sra y shift-fixnum))]
	      [else `(* ,x (sra ,y ,shift-fixnum))])]
      [(,op ,[x] ,[y]) (guard (memv op '(+ - < <= > >= =)))
        `(,op ,x ,y)]
      [(boolean? ,[x]) `(= (logand ,x ,mask-boolean) ,tag-boolean)]
      [(fixnum? ,[x]) `(= (logand ,x ,mask-fixnum) ,tag-fixnum)]
      [(pair? ,[x]) `(= (logand ,x ,mask-pair) ,tag-pair)]
      [(vector? ,[x]) `(= (logand ,x ,mask-vector) ,tag-vector)]
      [(procedure? ,[x]) `(= (logand ,x ,mask-procedure) ,tag-procedure)]
      [(null? ,[x]) `(= ,x ,$nil)]
      [(eq? ,[x] ,[y]) `(= ,x ,y)]
      [(car ,[x]) `(mref ,x ,(- disp-car tag-pair))]
      [(cdr ,[x]) `(mref ,x ,(- disp-cdr tag-pair))]
      [(set-car! ,[x] ,[y])
        `(mset! ,x ,(- disp-car tag-pair) ,y)]
      [(set-cdr! ,[x] ,[y])
        `(mset! ,x ,(- disp-cdr tag-pair) ,y)]
      [(cons ,[x] ,[y])
        (let ([tmp (unique-name 'tmp)] [tmp-car (unique-name 'ta)] [tmp-cdr (unique-name 'td)])
          `(let ([,tmp-car ,x] [,tmp-cdr ,y])
	     (let ([,tmp (+ (alloc ,size-pair) ,tag-pair)])
	       (begin (mset! ,tmp (- ,disp-car ,tag-pair) ,tmp-car)
		      (mset! ,tmp (- ,disp-cdr ,tag-pair) ,tmp-cdr)
		      ,tmp))))]
      [(vector-ref ,[x] ,[y])
        (if (int64? y) `(mref ,x ,(+ y (- disp-vector-data tag-vector)))
	  `(mref ,x (+ ,y ,(- disp-vector-data tag-vector))))]
      [(procedure-ref ,[x] ,[y])
        (if (int64? y) `(mref ,x ,(+ y (- disp-procedure-data tag-procedure)))
	  `(mref ,x (+ ,y ,(- disp-procedure-data tag-procedure))))]
      [(vector-set! ,[x] ,[y] ,[z])
        (if (int64? y) `(mset! ,x ,(+ y (- disp-vector-data tag-vector)) ,z)
	  `(mset! ,x (+ ,y ,(- disp-vector-data tag-vector)) ,z))]
      [(procedure-set! ,[x] ,[y] ,[z])
        (if (int64? y) `(mset! ,x ,(+ y (- disp-procedure-data tag-procedure)) ,z)
	  `(mset! ,x (+ ,y ,(- disp-procedure-data tag-procedure)) ,z))]
      [(vector-length ,[x])
        `(mref ,x ,(- disp-vector-length tag-vector))]
      [(procedure-code ,[x])
        `(mref ,x ,(- disp-procedure-code tag-procedure))]
      [(make-vector ,[x])
        (if (int64? x)
	  (let ([tmp (unique-name 'tmp)])
	    `(let ([,tmp (+ (alloc ,(+ x disp-vector-data)) ,tag-vector)])
	       (begin (mset! ,tmp ,(- disp-vector-length tag-vector) ,x) ,tmp)))
	  (let ([tmp1 (unique-name 'tmp)] [tmp2 (unique-name 'tmp)])
	    `(let ([,tmp1 ,x])
	       (let ([,tmp2 (+ (alloc (+ ,tmp1 ,disp-vector-data)) ,tag-vector)])
		 (begin (mset! ,tmp2 ,(- disp-vector-length tag-vector) ,tmp1) ,tmp2)))))]
      [(make-procedure ,[x] ,[y])
       (if (label? x)
          (let ([tmp (unique-name 'tmp)])
	    `(let ([,tmp (+ (alloc ,(+ y disp-procedure-data)) ,tag-procedure)])
	       (begin (mset! ,tmp ,(- disp-procedure-code tag-procedure) ,x) ,tmp)))
	  (let ([tmp1 (unique-name 'tmp)] [tmp2 (unique-name 'tmp)])
	    `(let ([,tmp1 ,x])
	       (let ([,tmp2 (+ (alloc ,(+ y disp-procedure-data)) ,tag-procedure)])
		 (begin (mset! ,tmp2 ,(- disp-procedure-code tag-procedure) ,tmp1) ,tmp2)))))]
      [,x (guard (pair? x)) (map Body x)]
      [,x x]))])

    (match program
      [(letrec ([,label* (lambda ,uvar* ,[Body -> body*])] ...) ,[Body -> body])
        `(letrec ([,label* (lambda ,uvar* ,body*)] ...) ,body)]))))

;;;

(define uncover-locals
  (lambda (program)
    (letrec (

[Body
  (lambda (body)
    (match body
      [(let ([,uvar* ,val*] ...) ,t)
        (append (Body t) uvar* (mymap-append Body val*))]
      [,x (guard (pair? x))
        (mymap-append Body x)]
      [,x '()]))]

[Body-1
  (lambda (body)
    `(locals ,(Body body) ,body))])

    (match program
      [(letrec ([,label* (lambda ,uvar* ,[Body-1 -> body*])] ...) ,[Body-1 -> body])
        `(letrec ([,label* (lambda ,uvar* ,body*)] ...) ,body)]))))

;;;

(define remove-let
  (lambda (program)
    (letrec (

[Body
  (lambda (body)
    (match body
      [(let ,ls ,[t])
        (make-begin `(,@(let->set! ls) ,t))]
      [,x (guard (pair? x))
        (map Body x)]
      [,x x]))]

[let->set!
  (lambda (ls)
    (if (null? ls) '()
      (cons (Body `(set! ,(caar ls) ,(cadar ls))) (let->set! (cdr ls)))))])

    (match program
      [(letrec ([,label* (lambda ,uvar* (locals ,x* ,[Body -> body*]))] ...) (locals ,x ,[Body -> body]))
        `(letrec ([,label* (lambda ,uvar* (locals ,x* ,body*))] ...) (locals ,x ,body))]))))

;;;

(define verify-uil (lambda (program) program))

;;;

(define remove-complex-opera*
  (lambda (program)
    (letrec (

[Body
  ;returns (values expr new-uvar*)
  (lambda (body)
    (match body
      [(locals ,uvar* ,tail)
        (let-values ([(expr uvar) (Body tail)])
	  `(locals ,(append uvar* uvar) ,expr))]
      [(begin ,e* ... ,c)
        (cond [(null? e*) (Body c)]
	      [else (let-values ([(expr1 uvar1) (Body (car e*))]
				 [(expr2 uvar2) (Body `(begin ,@(cdr e*) ,c))])
		      (values (make-begin `(,expr1 ,expr2)) (append uvar1 uvar2)))])]
      [(if ,p ,t ,f)
        (let-values ([(ep up) (Body p)]
		     [(et ut) (Body t)]
		     [(ef uf) (Body f)])
	  (values `(if ,ep ,et ,ef) (append up ut uf)))]
      [(set! ,x ,y)
        (if (not (pair? y)) (values body '())
	  (let-values ([(expr uvar) (Body y)])
	    (values `(set! ,x ,expr) uvar)))]
      [(,op ,a ,b) (guard (memv op '(+ - * logand logor sra < <= = >= >)))
	    (cond [(and (pair? a) (pair? b))
		    (let ([u (unique-name 's)] [v (unique-name 's)])
		      (let-values ([(eu uu) (Body `(set! ,u ,a))]
				   [(ev uv) (Body `(set! ,v ,b))])
			(values (make-begin `(,eu ,ev (,op ,u ,v))) (append uu uv `(,u ,v)))))]
		  [(pair? a)
		    (let ([u (unique-name 's)])
		      (let-values ([(eu uu) (Body `(set! ,u ,a))])
			(values (make-begin `(,eu (,op ,u ,b))) (append uu `(,u)))))]
		  [(pair? b)
		    (let ([v (unique-name 's)])
		      (let-values ([(ev uv) (Body `(set! ,v ,b))])
			(values (make-begin `(,ev (,op ,a ,v))) (append uv `(,v)))))]
		  [else (values body '())])]
      [(alloc ,x)
        (cond [(pair? x)
	        (let ([u (unique-name 'm)])
		  (let-values ([(eu uu) (Body `(set! ,u ,x))])
		    (values (make-begin `(,eu (alloc ,u))) (append uu `(,u)))))]
	      [else (values body '())])]
      [(mset! ,bexpr ,oexpr ,expr)
        (let ([b (unique-name 'm)] [o (unique-name 'm)] [e (unique-name 'm)])
	  (let-values ([(eb ub) (Body `(set! ,b ,bexpr))]
		       [(eo uo) (Body `(set! ,o ,oexpr))]
		       [(ee ue) (Body `(set! ,e ,expr))])
	    (values (make-begin `(,eb ,eo ,ee (mset! ,b ,o ,e))) (append ub uo ue `(,b ,o ,e)))))]
      [(mref ,bexpr ,oexpr)
        (cond [(and (pair? bexpr) (pair? oexpr))
	        (let ([u (unique-name 'm)] [v (unique-name 'm)])
		  (let-values ([(eu uu) (Body `(set! ,u ,bexpr))]
			       [(ev uv) (Body `(set! ,v ,oexpr))])
		    (values (make-begin `(,eu ,ev (mref ,u ,v))) (append uu uv `(,u ,v)))))]
	      [(pair? bexpr)
	        (let ([u (unique-name 'm)])
		  (let-values ([(eu uu) (Body `(set! ,u ,bexpr))])
		    (values (make-begin `(,eu (mref ,u ,oexpr))) (append uu `(,u)))))]
	      [(pair? oexpr)
	        (let ([v (unique-name 'm)])
		  (let-values ([(ev uv) (Body `(set! ,v ,oexpr))])
		    (values (make-begin `(,ev (mref ,bexpr ,v))) (append uv `(,v)))))]
	      [else (values body '())])]
      [(nop) (values body '())]
      [(true) (values body '())]
      [(false) (values body '())]
      [(,triv ,arg* ...)
        (let-values ([(expr uvar nuvar) (Call arg*)])
	  (if (pair? triv)
	    (let ([u (unique-name 'f)])
	      (let-values ([(et ut) (Body `(set! ,u ,triv))])
		(values (make-begin `(,@expr ,et (,u ,@uvar))) (append nuvar ut `(,u)))))
	    (values (make-begin `(,@expr (,triv ,@uvar))) nuvar)))]
      [,x (values x '())]))]

[Call
  ;returns (values expr uvar new-uvar)
  (lambda (args)
    (cond [(null? args) (values '() '() '())]
          [else (let ([u (unique-name 'tmp)])
                  (let-values ([(e1 n1) (Body `(set! ,u ,(car args)))]
                               [(e2 u2 n2) (Call (cdr args))])
                    (values `(,e1 ,@e2) `(,u ,@u2) (append n1 n2 `(,u)))))]))])

    (match program
      [(letrec ([,label* (lambda ,uvar-list* ,[Body -> body*])] ...) ,[Body -> body])
        `(letrec ([,label* (lambda ,uvar-list* ,body*)] ...) ,body)]))))

;;;

(define flatten-set!
  (lambda (program)
    (letrec (

[fix-set!
  (lambda (body)
    (match body
      [(locals ,uvar* ,b)
        `(locals ,uvar* ,(fix-set! b))]
      [(set! ,x ,y)
        (match y
          [(if ,[fix-set! -> p] ,t ,f)
            `(if ,p ,(fix-set! `(set! ,x ,t)) ,(fix-set! `(set! ,x ,f)))]
          [(begin ,[fix-set! -> e*] ... ,c)
            (make-begin `(,@e* ,(fix-set! `(set! ,x ,c))))]
          [,z `(set! ,x ,y)])]
      [(if ,[p] ,[t] ,[f])
        `(if ,p ,t ,f)]
      [(begin ,[e*] ...)
        `(begin ,@e*)]
      [,x x]
    ))])

    (match program
      [(letrec ([,label* (lambda ,uvar-list* ,[fix-set! -> body*])] ...) ,[fix-set! -> body])
        `(letrec ([,label* (lambda ,uvar-list* ,body*)] ...) ,body)]))))

;;;

(define expose-allocation-pointer
  (lambda (program)
    (letrec (

[Body
  (lambda (body)
    (match body
      [(set! ,x (alloc ,expr))
        (let ([ap allocation-pointer-register])
          `(begin (set! ,x ,ap) (set! ,ap (+ ,ap ,expr))))]
      [,x (guard (pair? x))
        (map Body x)]
      [,x x]))])

    (match program
      [(letrec ([,label* (lambda () ,[Body -> body*])] ...) ,[Body -> body])
        `(letrec ([,label* (lambda () ,body*)] ...) ,body)]))))

;;;

(define impose-calling-conventions
  (lambda (program)
    (letrec (

[Lambda
  (lambda (body)
    (letrec ([rp (unique-name 'rp)] [new-frames '()]
	     [Tail
	       (lambda (body)
		 (match body
		   [(if ,[nonTail -> p] ,[t] ,[f])
		     `(if ,p ,t ,f)]
		   [(begin ,[nonTail -> e*] ... ,[t])
		     `(begin ,@e* ,t)]
		   [(,proc ,arg* ...) (guard (or (label? proc) (uvar? proc)))
		     	(let-values ([(expr loc) (Args-rev arg* parameter-registers 0)])
			  (make-begin (append (reverse expr)
			    `((set! ,return-address-register ,rp))
			    `((,proc ,@loc ,frame-pointer-register ,allocation-pointer-register ,rp ,return-address-register)))))]
		   [,expr
		     `(begin (set! ,return-value-register ,expr) (,rp ,frame-pointer-register ,allocation-pointer-register ,return-value-register))]
		 ))]
	     [nonTail
	       (lambda (body)
		 (match body
		   [(if ,[p] ,[t] ,[f])
		     `(if ,p ,t ,f)]
		   [(begin ,[e*] ... ,[t])
		     `(begin ,@e* ,t)]
		   [(,proc ,arg* ...) (guard (or (label? proc) (uvar? proc)))
		     	(let-values ([(expr loc) (Args-nontail arg* parameter-registers 0)])
			  (set! new-frames (cons (rm loc parameter-registers) new-frames))
			  (let ([retp (unique-label 'retp)])
			    `(return-point ,retp
			      ,(make-begin (append (reverse expr)
			        `((set! ,return-address-register ,retp))
			        `((,proc ,@loc ,frame-pointer-register ,return-address-register ,allocation-pointer-register)))))))]
		   [(set! ,x (,proc ,arg* ...)) (guard (not (memv proc '(+ - * logand logor sra alloc mref))))
		     (make-begin `(,(nonTail `(,proc ,@arg*)) (set! ,x ,return-value-register)))]
		   [,x x]))])
      (match body
	[(lambda ,args (locals ,uvar ,[Tail -> t]))
	  (let ([exprs (Args args parameter-registers 0)])
	    `(locals ,(append uvar `(,rp) args (mymap-append (lambda (x) x) new-frames)) (new-frames ,new-frames 
	       ,(make-begin (append `((set! ,rp ,return-address-register)) exprs `(,t))))))])
    ))]

[Args
  ;returns set!-expression-list
  (lambda (args para-reg n)
    (cond [(null? args) '()]
          [(null? para-reg)
            (cons `(set! ,(car args) ,(index->frame-var n)) (Args (cdr args) para-reg (+ n 1)))]
          [else (cons `(set! ,(car args) ,(car para-reg)) (Args (cdr args) (cdr para-reg) n))]))]

[Args-rev
  ;returns (values set!-expression-list location-list)
  (lambda (args para-reg n)
    (cond [(null? args) (values '() '())]
          [(null? para-reg)
            (let-values ([(expr loc) (Args-rev (cdr args) para-reg (+ n 1))])
              (values (cons `(set! ,(index->frame-var n) ,(car args)) expr) (cons (index->frame-var n) loc)))]
          [else (let-values ([(expr loc) (Args-rev (cdr args) (cdr para-reg) n)])
                  (values (cons `(set! ,(car para-reg) ,(car args)) expr) (cons (car para-reg) loc)))]))]

[Args-nontail
  ;returns (values set!-expression-list uvar-list)
  (lambda (args para-reg n)
    (cond [(null? args) (values '() '())]
          [(null? para-reg)
            (let-values ([(expr loc) (Args-nontail (cdr args) para-reg (+ n 1))])
              (let ([nfv (unique-name 'nfv)])
                (values (cons `(set! ,nfv ,(car args)) expr) (cons nfv loc))))]
          [else (let-values ([(expr loc) (Args-nontail (cdr args) (cdr para-reg) n)])
                  (values (cons `(set! ,(car para-reg) ,(car args)) expr) (cons (car para-reg) loc)))]))])

    (match program
      [(letrec ([,label* ,[Lambda -> lambda-expr*]] ...) ,body)
        `(letrec ([,label* (lambda () ,lambda-expr*)] ...) ,(Lambda `(lambda () ,body)))]))))

;;;

(define uncover-frame-conflict
  (lambda (program)
    (letrec (

[G '()]
[call-live-uf '()]
[call-live-u '()]

[Body
  (lambda (body live-set)
    (match body
      [(locals (,uvar* ...) (new-frames ,frame ,tail))
	(set! G (map (lambda (x) `(,x)) uvar*))
	(set! call-live-uf '())
	(set! call-live-u '())
	(Body tail '())
	`(locals ,uvar* (new-frames ,frame (spills ,call-live-u (frame-conflict ,G (call-live ,call-live-uf ,tail)))))]
      [(begin ,clause* ... ,t) 
        (cond [(null? clause*) (Body t live-set)]
	      [(eqv? (caar clause*) 'return-point)
	        (let ([ls (Body `(begin ,@(cdr clause*) ,t) live-set)]
		      [ls2 (Body (caddar clause*) '())])
		  ;add ls into call-live
		  (set! call-live-uf (union call-live-uf (mymap-append (lambda (x) (if (or (uvar? x) (frame-var? x)) `(,x) '())) ls)))
		  (set! call-live-u (union call-live-u (mymap-append (lambda (x) (if (uvar? x) `(,x) '())) ls)))
		  (union ls ls2))]
              [else (let ([ls (Body `(begin ,@(cdr clause*) ,t) live-set)])
		      (Body (car clause*) ls))])]
      [(if ,pred ,t ,f)
        (let ([tls (Body t live-set)] [fls (Body f live-set)])
	  (Body pred (union tls fls)))]
      [(true) live-set]
      [(false) live-set]
      [(nop) live-set]
      [(,relop ,x ,y) (guard (memv relop '(< <= > >= =))) ; x and y is in use
	(let ([ls live-set])
	  (if (or (uvar? x) (frame-var? x)) (set! ls (set-cons x ls)))
	  (if (or (uvar? y) (frame-var? y)) (set! ls (set-cons y ls)))
	  ls)]
      [(set! ,x (,op ,y ,z))
        (let ([ls (remv x live-set)]) ; all live conflicts with x
	  (if (or (uvar? x) (frame-var? x)) (map (lambda (y) (add-conflicts x y)) ls))
	  (if (or (uvar? y) (frame-var? y)) (set! ls (set-cons y ls)))
	  (if (or (uvar? z) (frame-var? z)) (set! ls (set-cons z ls)))
	  ls)]
      [(set! ,x ,y)
        (let ([ls (remv x live-set)])
	  (if (or (uvar? x) (frame-var? x)) (map (lambda (y) (add-conflicts x y)) ls))
	  (if (or (uvar? y) (frame-var? y)) (set-cons y ls) ls))]
      [,x (union live-set (mymap-append (lambda (y) (if (or (uvar? y) (frame-var? y)) `(,y) '())) x))]
    ))]

[add-conflicts
  (lambda (x y)
    (if (and (uvar? x) (or (uvar? y) (frame-var? y)))
      (let ([s (assq x G)])
        (set-cdr! s (cdr (set-cons y s)))))
    (if (and (uvar? y) (or (uvar? x) (frame-var? x)))
      (let ([s (assq y G)])
        (set-cdr! s (cdr (set-cons x s))))))]

[Body-1 (lambda (x) (Body x '()))])

    (match program
      [(letrec ([,label* (lambda () ,[Body-1 -> body*])] ...) ,[Body-1 -> body])
        `(letrec ([,label* (lambda () ,body*)] ...) ,body)]))))

;;;

(define pre-assign-frame
  (lambda (program)
    (letrec (

[Body
  (lambda (body)
    (match body
      [(locals (,uvar* ...) (new-frames ,frame (spills (,list* ...) (locate ,ls (frame-conflict ,g (call-live ,uf ,tail))))))
        (cond [(null? list*) `(locals ,uvar* (new-frames ,frame (locate ,ls (frame-conflict ,g (call-live ,uf ,tail)))))]
              [else (let ([u (car list*)])
                      (Body `(locals ,(remv u uvar*) (new-frames ,frame (spills ,(cdr list*)
                       (locate ,(cons `(,u ,(frame-alloc (assq u g) ls 0)) ls) (frame-conflict ,g (call-live ,uf ,tail))))))))])]
      [(locals ,uvar (new-frames ,frame (spills (,list* ...) ,res)))
        (Body `(locals ,uvar (new-frames ,frame (spills ,list* (locate () ,res)))))]))])

    (match program
      [(letrec ([,label* (lambda () ,[Body -> body*])] ...) ,[Body -> body])
        `(letrec ([,label* (lambda () ,body*)] ...) ,body)]))))

;;;

(define assign-new-frame
  (lambda (program)
    (letrec (

[frame-size 0]

[Body
  (lambda (body)
    (match body
      [(locals ,uvar (new-frames ,frame (locate ,loclist (frame-conflict ,g (call-live ,call-live-uf ,t)))))
        (set! frame-size (+ 1 (max-frame call-live-uf loclist)))
        `(locals ,(rm uvar (mymap-append (lambda (x) x) frame)) (ulocals ()
           (locate (,@loclist ,@(mymap-append new-fr-1 frame))
             (frame-conflict ,g ,(Body t)))))]
      [(begin ,[Body -> e*] ... ,[Body -> t])
        `(begin ,e* ... ,t)]
      [(if ,[Body -> p] ,[Body -> t] ,[Body -> f])
        `(if ,p ,t ,f)]
      [(return-point ,res* ...)
        (let ([fp frame-pointer-register])
          `(begin (set! ,fp (+ ,fp ,(fxsll frame-size align-shift)))
                  (return-point ,res* ...)
                  (set! ,fp (- ,fp ,(fxsll frame-size align-shift)))))]
      [,x x]))]

[max-frame
  (lambda (uf ref)
    (cond [(null? uf) 0]
          [else (let ([maxx (max-frame (cdr uf) ref)]
                      [nww (frame-var->index (if (uvar? (car uf)) (cadr (assq (car uf) ref)) (car uf)))])
                  (if (< nww maxx) maxx nww))]))]

[new-fr-1 (lambda (ls) (new-fr ls frame-size))]

[new-fr
  (lambda (ls n)
    (cond [(null? ls) '()]
          [else (cons `(,(car ls) ,(index->frame-var n)) (new-fr (cdr ls) (+ n 1)))]))])

    (match program
      [(letrec ([,label* (lambda () ,[Body -> body*])] ...) ,[Body -> body])
        `(letrec ([,label* (lambda () ,body*)] ...) ,body)]))))

;;;

(define select-instructions
  (lambda (program)
    (letrec (

[relrev (lambda (x) (cadr (assq x '((< >) (> <) (= =) (<= >=) (>= <=)))))]

[Body
  ;returns (values (list of instructions) (list of new unspillable var))
  (lambda (body)
    (match body
      [(locals (,uvar* ...) (ulocals (,uuvar* ...) (locate ,loclist (frame-conflict ,g ,tail))))
        (let-values ([(t u) (Body tail)])
	  `(locals ,uvar* (ulocals ,(append u uuvar*) (locate ,loclist (frame-conflict ,g ,t)))))]
      [(locate ,loclist ,tail) body]
      [(begin ,c* ... ,t)
        (cond [(null? c*) (Body t)]
	      [else (let-values ([(ls2 u2) (Body `(begin ,@(cdr c*) ,t))]
				 [(ls1 u1) (Body (car c*))])
		      (match ls2
			[(begin ,x* ...) (values `(begin ,ls1 ,@x*) (append u1 u2))]
			[,x (values `(begin ,ls1 ,ls2) (append u1 u2))]))])]
      [(if ,pred ,t ,f)
        (let-values ([(lsp up) (Body pred)]
		     [(lst ut) (Body t)]
		     [(lsf uf) (Body f)])
	  (values `(if ,lsp ,lst ,lsf) (append up ut uf)))]
      [(return-point ,rp-label ,t)
        (let-values ([(lst ut) (Body t)])
	  (values `(return-point ,rp-label ,lst) ut))]
      [(true) (values body '())]
      [(false) (values body '())]
      [(nop) (values body '())]
      [(,relop ,x ,y) (guard (memv relop '(< <= > >= =)))
	(cond [(and (int64? y) (not (int32? y)))
                (let ([u (unique-name 't)] [v (unique-name 't)])
                  (values `(begin (set! ,u ,x) (set! ,v ,y) (,relop ,u ,v)) `(,u ,v)))]
	      [(or (register? x) (uvar? x) (and (frame-var? x) (int32? y)))
	        (values body '())]
	      [(and (or (register? y) (uvar? y) (and (frame-var? y) (int32? x)))
	            (or (int32? x) (not (int64? x))))
	        (values `(,(relrev relop) ,y ,x) '())]
	      [else
                (let ([u (unique-name 't)])
                  (values `(begin (set! ,u ,x) (,relop ,u ,y)) `(,u)))])]
      [(set! ,x (mref ,y ,z))
        (if (frame-var? x)
	  (cond [(or (and (register? y) (or (int32? z) (register? z))) (and (int32? y) (register? z)))
		  (let ([w (unique-name 'p)])
		    (values `(begin (set! ,w (mref ,y ,z)) (set! ,x ,w)) `(,w)))]
		[(register? y)
		  (let ([w (unique-name 'p)] [v (unique-name 'p)])
		    (values `(begin (set! ,v ,z) (set! ,w (mref ,y ,v)) (set! ,x ,w)) `(,v ,w)))]
		[(register? z)
		  (let ([w (unique-name 'p)] [u (unique-name 'p)])
		    (values `(begin (set! ,u ,y) (set! ,w (mref ,u ,z)) (set! ,x ,w)) `(,u ,w)))]
		[else
		  (let ([u (unique-name 'p)] [v (unique-name 'p)] [w (unique-name 'p)])
		    (values `(begin (set! ,u ,y) (set! ,v ,z) (set! ,w (mref ,u ,v)) (set! ,x ,w)) `(,u ,v ,w)))])
	  (cond [(or (and (register? y) (or (int32? z) (register? z))) (and (int32? y) (register? z)))
		  (values body '())]
                [(register? y)
                  (let ([v (unique-name 'p)])
                    (values `(begin (set! ,v ,z) (set! ,x (mref ,y ,v))) `(,v)))]
                [(register? z)
                  (let ([u (unique-name 'p)])
                    (values `(begin (set! ,u ,y) (set! ,x (mref ,u ,z))) `(,u)))]
                [else
                  (let ([u (unique-name 'p)] [v (unique-name 'p)])
                    (values `(begin (set! ,u ,y) (set! ,v ,z) (set! ,x (mref ,u ,v))) `(,u ,v)))]))]
        ;(let ([u (unique-name 'p)] [v (unique-name 'p)] [w (unique-name 'p)])
	;  (values `(begin (set! ,u ,y) (set! ,v ,z) (set! ,w (mref ,u ,v)) (set! ,x ,w)) `(,u ,v ,w)))]
      [(set! ,x (,unop ,y ,z)) (guard (memv unop '(- sra)))
	(cond [(and (int64? z) (not (int32? z)))
                (let ([u (unique-name 't)] [v (unique-name 't)])
                  (values `(begin (set! ,u ,y) (set! ,v ,z) (set! ,u (- ,u ,v)) (set! ,x ,u)) `(,u ,v)))]
	      [(and (eqv? x y) (not (and (frame-var? x) (frame-var? z))))
	        (values body '())]
	      [else
		(let ([u (unique-name 't)])
                  (values `(begin (set! ,u ,y) (set! ,u (,unop ,u ,z)) (set! ,x ,u)) `(,u)))])]
      [(set! ,x (,op ,y ,z))
	(cond [(and (int64? z) (not (int32? z)))
	        (let ([u (unique-name 't)] [v (unique-name 't)])
                  (values `(begin (set! ,u ,y) (set! ,v ,z) (set! ,u (,op ,u ,v)) (set! ,x ,u)) `(,u ,v)))]
	      [(and (eqv? x y) (not (and (eqv? op '*) (frame-var? x))) (not (and (frame-var? x) (frame-var? z))))
	        (values body '())]
	      [(and (eqv? x z) (not (and (eqv? op '*) (frame-var? x))) (not (and (frame-var? x) (frame-var? y)))
		    (or (int32? y) (not (int64? y))))
	        (values `(set! ,x (,op ,z ,y)) '())]
	      [else
	        (let ([u (unique-name 't)])
	          (values `(begin (set! ,u ,y) (set! ,u (,op ,u ,z)) (set! ,x ,u)) `(,u)))])]
      [(set! ,x ,y)
        (cond [(and (frame-var? x) (or (label? y) (and (int64? y) (not (int32? y))) (frame-var? y)))
	        (let ([u (unique-name 't)])
		  (values `(begin (set! ,u ,y) (set! ,x ,u)) `(,u)))]
	      [else (values `(set! ,x ,y) '())])]
      [(mset! ,y ,z ,x)
        (if (frame-var? x)
          (cond [(or (and (register? y) (or (int32? z) (register? z))) (and (int32? y) (register? z)))
                  (let ([w (unique-name 'p)])
                    (values `(begin (set! ,w ,x) (mset! ,y ,z ,w)) `(,w)))]
                [(register? y)
                  (let ([w (unique-name 'p)] [v (unique-name 'p)])
                    (values `(begin (set! ,w ,x) (set! ,v ,z) (mset! ,y ,v ,w)) `(,v ,w)))]
                [(register? z)
                  (let ([w (unique-name 'p)] [u (unique-name 'p)])
                    (values `(begin (set! ,w ,x) (set! ,u ,y) (mset! ,u ,z ,w)) `(,u ,w)))]
                [else
                  (let ([u (unique-name 'p)] [v (unique-name 'p)] [w (unique-name 'p)])
                    (values `(begin (set! ,w ,x) (set! ,u ,y) (set! ,v ,z) (mset! ,y ,z ,w)) `(,u ,v ,w)))])
          (cond [(or (and (register? y) (or (int32? z) (register? z))) (and (int32? y) (register? z)))
                  (values body '())]
                [(register? y)
                  (let ([v (unique-name 'p)])
                    (values `(begin (set! ,v ,z) (mset! ,y ,v ,x)) `(,v)))]
                [(register? z)
                  (let ([u (unique-name 'p)])
                    (values `(begin (set! ,u ,y) (mset! ,u ,z ,x)) `(,u)))]
                [else
                  (let ([u (unique-name 'p)] [v (unique-name 'p)])
                    (values `(begin (set! ,u ,y) (set! ,v ,z) (mset! ,u ,v ,x)) `(,u ,v)))]))]
        ;(let ([u (unique-name 'p)] [v (unique-name 'p)] [w (unique-name 'p)])
	;  (values `(begin (set! ,u ,base) (set! ,v ,offset) (set! ,w ,expr) (mset! ,u ,v ,w)) `(,u ,v ,w)))]
      [,x (values x '())]))])

    (match program
      [(letrec ([,label* (lambda () ,[Body -> body*])] ...) ,[Body -> body])
        `(letrec ([,label* (lambda () ,body*)] ...) ,body)]))))

;;;

(define uncover-register-conflict
  (lambda (program)
    (letrec (

[G '()]

[Body
  ;return live-set
  (lambda (body live-set)
    (match body
      [(locals (,uvar* ...) (ulocals (,uuvar* ...) (locate (,uf* ...) (frame-conflict ,g ,tail))))
        (set! G (map (lambda (x) `(,x)) (append uvar* uuvar*)))
	(Body tail '())
	`(locals ,uvar* (ulocals ,uuvar* (locate ,uf* (frame-conflict ,g (register-conflict ,G ,tail)))))]
      [(locate ([,uvar* ,loc*] ...) ,tail) body]
      [(begin ,clause* ... ,t) 
        (cond [(null? clause*) (Body t live-set)]
              [else (let ([ls (Body `(begin ,@(cdr clause*) ,t) live-set)])
		      (Body (car clause*) ls))])]
      [(if ,pred ,t ,f)
        (let ([tls (Body t live-set)] [fls (Body f live-set)])
	  (Body pred (union tls fls)))]
      [(return-point ,rp-label ,t) (Body t live-set)] ;;;;;;;;;;;;;may be wrong!!!!!!!!!!!
      [(true) live-set]
      [(false) live-set]
      [(nop) live-set]
      [(,relop ,x ,y) (guard (memv relop '(< <= > >= =))) ; x and y is in use
	(let ([ls live-set])
	  (if (or (uvar? x) (register? x)) (set! ls (set-cons x ls)))
	  (if (or (uvar? y) (register? y)) (set! ls (set-cons y ls)))
	  ls)]
      [(set! ,x (,op ,y ,z))
        (let ([ls (remv x live-set)]) ; all live conflicts with x
	  (if (or (uvar? x) (register? x)) (map (lambda (y) (add-conflicts x y)) ls))
	  (if (or (uvar? y) (register? y)) (set! ls (set-cons y ls)))
	  (if (or (uvar? z) (register? z)) (set! ls (set-cons z ls)))
	  ls)]
      [(set! ,x ,y)
        (let ([ls (remv x live-set)])
	  (if (or (uvar? x) (register? x)) (map (lambda (y) (add-conflicts x y)) ls))
	  (if (or (uvar? y) (register? y)) (set-cons y ls) ls))]
      [,x (union live-set (mymap-append (lambda (y) (if (or (uvar? y) (register? y)) `(,y) '())) x))]
    ))]

[add-conflicts
  (lambda (x y)
    (if (and (uvar? x) (or (uvar? y) (register? y)))
      (let ([s (assq x G)])
        (set-cdr! s (cdr (set-cons y s)))))
    (if (and (uvar? y) (or (uvar? x) (register? x)))
      (let ([s (assq y G)])
        (set-cdr! s (cdr (set-cons x s))))))])

    (match program
      [(letrec ([,label* (lambda () ,body*)] ...) ,body)
        `(letrec ([,label* (lambda () ,(map (lambda (b) (Body b '())) body*))] ...)
	   ,(Body body '()))]))))
;;;

(define assign-registers
  (lambda (program)
    (letrec (

[uuvar '()]
[spilled '()]

[Body
  ;returns ([uvar assigned-reg] ...)
  (lambda (body)
    (match body
      [(locals (,uvar* ...) (ulocals (,uuvar* ...) (locate ,loclist (frame-conflict ,g (register-conflict ,G ,tail)))))
        (set! uuvar uuvar*)
        (set! spilled '())
        (let ([assign-list (Body G)])
          (if (null? spilled) `(locate ,(append assign-list loclist) ,tail)
          `(locals ,(rm uvar* spilled) (ulocals ,uuvar* (spills ,spilled
             (locate ,loclist (frame-conflict ,g ,tail)))))))]
      [(locate ,loclist ,tail) body]
      [,G
        (cond [(null? G) '()]
              [else (let* ([u (find-uvar G)]
                           [adju (assq u G)]
                           [gg (remv adju G)]
                           [g (map (lambda (x) (remv u x)) gg)]
                           [ls (Body g)]
                           [adjur (cons u (map (lambda (x)
                                         (cond [(register? x) x]
                                               [(assq x ls) (cadr (assq x ls))]
                                               [else x])) (cdr adju)))])
                      (if (find-reg adjur registers) (cons `(,u ,(find-reg adjur registers)) ls)
                        (begin (set! spilled (cons u spilled)) ls)))])]))]

[find-uvar
  (lambda (G)
    (let ([lowdeg (find-low-degree G)])
      (if (null? lowdeg)
        (car (mymap-append (lambda (x) (if (memv (car x) uuvar) '() `(,(car x)))) G))
        lowdeg)))]

[find-low-degree
  (lambda (G)
    (cond [(null? G) '()]
          [(<= (length (car G)) (length registers)) (caar G)]
          [else (find-low-degree (cdr G))]))]

[find-reg
  (lambda (adju reg)
    (cond [(null? reg) #f]
          [(memv (car reg) adju) (find-reg adju (cdr reg))]
          [else (car reg)]))])

    (match program
      [(letrec ([,label* (lambda () ,[Body -> body*])] ...) ,[Body -> body])
        `(letrec ([,label* (lambda () ,body*)] ...) ,body)]))))

;;;

(define assign-frame
  (lambda (program)
    (letrec (

[Body
  (lambda (body)
    (match body
      [(locals (,uvar* ...) (ulocals (,uuvar* ...) (spills (,list* ...) (locate ,ls (frame-conflict ,g ,tail)))))
        (cond [(null? list*) `(locals ,uvar* (ulocals ,uuvar* (locate ,ls (frame-conflict ,g ,tail))))]
              [else (let ([u (car list*)])
                      (Body `(locals ,uvar* (ulocals ,uuvar* (spills ,(cdr list*)
                       (locate ,(cons `(,u ,(frame-alloc (assq u g) ls 0)) ls) (frame-conflict ,g ,tail)))))))])]
      [(locate ,loclist ,tail) body]))])

    (match program
      [(letrec ([,label* (lambda () ,[Body -> body*])] ...) ,[Body -> body])
        `(letrec ([,label* (lambda () ,body*)] ...) ,body)]))))

(define frame-alloc
  (lambda (adj form x)
    (if (find-frame? adj form (index->frame-var x))
      (frame-alloc adj form (+ x 1))
      (index->frame-var x))))

(define find-frame?
  (lambda (adj form u)
    (cond [(null? adj) #f]
	  [(eqv? (car adj) u) adj]
	  [(and (assq (car adj) form) (eqv? (cadr (assq (car adj) form)) u)) adj]
	  [else (find-frame? (cdr adj) form u)])))

;;;

(define finalize-frame-locations
  (lambda (program)
    (letrec (

[f-ref '()]

[Body
  (lambda (body)
    (match body
      [(locals (,uvar* ...) (ulocals (,uuvar* ...) (locate ,ls (frame-conflict ,g ,tail))))
        (set! f-ref ls)
        `(locals ,uvar* (ulocals ,uuvar* (locate ,ls (frame-conflict ,g ,(Body tail)))))]
      [(locate ,ls ,t) body]
      [(set! ,x ,y) (guard (not (pair? x)) (not (pair? y)))
        (let ([xx (if (assq x f-ref) (cadr (assq x f-ref)) x)]
              [yy (if (assq y f-ref) (cadr (assq y f-ref)) y)])
          (cond [(eqv? xx yy) '(nop)]
                [else `(set! ,xx ,yy)]))]
      [,x (guard (pair? x)) (map Body x)]
      [,x (guard (assq x f-ref)) (cadr (assq x f-ref))]
      [,x x]))])

    (match program
      [(letrec ([,label* (lambda () ,[Body -> body*])] ...) ,body)
        `(letrec ([,label* (lambda () ,body*)] ...) ,(Body body))]))))

;;;

(define discard-call-live
  (lambda (program)
    (letrec (

[Body
  (lambda (body)
    (match body
      [(locate ,x ,[tail]) `(locate ,x ,tail)]
      [(begin ,[clause*] ... ,[t]) `(begin ,@clause* ,t)]
      [(if ,[pred] ,[t] ,[f]) `(if ,pred ,t ,f)]
      [(return-point ,rp-label ,[tail]) `(return-point ,rp-label ,tail)]
      [,x (guard (and (pair? x) (or (frame-var? (car x)) (uvar? (car x)) (label? (car x))))) `(,(car x))]
      [,x x]))])

    (match program
      [(letrec ([,label* (lambda () ,[Body -> body*])] ...) ,[Body -> body])
        `(letrec ([,label* (lambda () ,body*)] ...) ,body)]))))

;;;

(define finalize-locations
  (lambda (program)
    (letrec (

[ref-list '()]

[Body
  (lambda (body)
    (match body
      [(locate ([,uvar* ,loc*] ...) ,tail)
        (set! ref-list (make-ref uvar* loc*))
        (Body tail)]
      [(set! ,x ,y) (guard (not (pair? x)) (not (pair? y)))
        (let ([xx (if (uvar? x) (cadr (memv x ref-list)) x)]
              [yy (if (uvar? y) (cadr (memv y ref-list)) y)])
          (cond [(eqv? xx yy) '(nop)]
                [else `(set! ,xx ,yy)]))]
      [,x (guard (pair? x)) (map Body x)]
      [,x (guard (uvar? x)) (cadr (memv x ref-list))]
      [,x x]))]

[make-ref
  (lambda (uvar* loc*)
    (cond [(null? uvar*) '()]
          [else `(,(car uvar*) ,(car loc*) ,@(make-ref (cdr uvar*) (cdr loc*)))]))])

    (match program
      [(letrec ([,label* (lambda () ,[Body -> body*])] ...) ,body)
        `(letrec ([,label* (lambda () ,body*)] ...) ,(Body body))]))))

;;;

(define expose-memory-operands
  (lambda (program)
    (letrec (

[Body
  (lambda (body)
    (match body
      [(mset! ,base ,offset ,t)
        (cond [(and (register? base) (int32? offset)) `(set! ,(make-disp-opnd base offset) ,t)]
              [(and (int32? base) (register? offset)) `(set! ,(make-disp-opnd offset base) ,t)]
              [(and (register? base) (register? offset)) `(set! ,(make-index-opnd base offset) ,t)]
              [else "ff"])]
      [(set! ,x (mref ,base ,offset))
        (cond [(and (register? base) (int32? offset)) `(set! ,x ,(make-disp-opnd base offset))]
              [(and (int32? base) (register? offset)) `(set! ,x ,(make-disp-opnd offset base))]
              [(and (register? base) (register? offset)) `(set! ,x ,(make-index-opnd base offset))]
              [else "ff"])]
      [,x (guard (pair? x)) (map Body x)]
      [,x x]))])

    (match program
      [(letrec ([,label* (lambda () ,[Body -> body*])] ...) ,[Body -> body])
        `(letrec ([,label* (lambda () ,body*)] ...) ,body)]))))

;;;

(define expose-frame-var
  (lambda (program)
    (letrec (

[Body
  (lambda (body)
    (let-values ([(program offset) (Body-1 body 0)])
      program))]

[Body-1
  (lambda (body offset)
    (match body
      [(begin ,e* ... ,c)
        (cond [(null? e*) (Body-1 c offset)]
	      [else (let*-values ([(ep eo) (Body-1 `(begin ,@e*) offset)]
				  [(cp co) (Body-1 c eo)])
		      (values (make-begin `(,ep ,cp)) co))])]
      [(if ,p ,t ,f)
        (let*-values ([(pp po) (Body-1 p offset)]
		      [(tp to) (Body-1 t po)]
		      [(fp fo) (Body-1 f po)])
	  (if (= to fo)
	    (values `(if ,pp ,tp ,fp) to)
	    (values "Error" "E")))]
      [(return-point ,rp-label ,t)
        (let-values ([(tp to) (Body-1 t offset)])
	  (values `(return-point ,rp-label ,tp) to))]
      [(set! ,fp (,op ,x ,y)) (guard (eqv? fp frame-pointer-register))
	(cond [(eqv? op '+) (values body (+ offset y))]
	      [(eqv? op '-) (values body (- offset y))]
	      [else (values "Invalid fp operation" "I")])]
      [(set! ,x (mref ,y ,z)) (values body offset)]
      [(set! ,x (,op ,xx ,y))
        (let ([a (if (frame-var? x) (make-disp-opnd frame-pointer-register (- (fxsll (frame-var->index x) align-shift) offset)) x)]
	      [b (if (frame-var? y) (make-disp-opnd frame-pointer-register (- (fxsll (frame-var->index y) align-shift) offset)) y)])
	  (values `(set! ,a (,op ,a ,b)) offset))]
      [(set! ,x ,y)
        (let ([a (if (frame-var? x) (make-disp-opnd frame-pointer-register (- (fxsll (frame-var->index x) align-shift) offset)) x)]
	      [b (if (frame-var? y) (make-disp-opnd frame-pointer-register (- (fxsll (frame-var->index y) align-shift) offset)) y)])
	  (values `(set! ,a ,b) offset))]
      [(,relop ,x ,y) (guard (memv relop '(< <= > >= =)))
	(let ([a (if (frame-var? x) (make-disp-opnd frame-pointer-register (- (fxsll (frame-var->index x) align-shift) offset)) x)]
              [b (if (frame-var? y) (make-disp-opnd frame-pointer-register (- (fxsll (frame-var->index y) align-shift) offset)) y)])
          (values `(,relop ,a ,b) offset))]
      [(not (,relop ,x ,y)) (guard (memv relop '(< <= > >= =)))
        (let ([a (if (frame-var? x) (make-disp-opnd frame-pointer-register (- (fxsll (frame-var->index x) align-shift) offset)) x)]
              [b (if (frame-var? y) (make-disp-opnd frame-pointer-register (- (fxsll (frame-var->index y) align-shift) offset)) y)])
          (values `(not (,relop ,a ,b)) offset))]
      [(,x) (guard (frame-var? x))
	(values `(,(make-disp-opnd frame-pointer-register (- (fxsll (frame-var->index x) align-shift) offset))) offset)]
      [,x (values body offset)]))])

    (match program
      [(letrec ([,label* (lambda () ,[Body -> body*])] ...) ,[Body -> body])
        `(letrec ([,label* (lambda () ,body*)] ...) ,body)]))))

;;;

(define expose-basic-blocks
  (lambda (program)
    (letrec (

[Lambda
  (lambda (lambda-expr)
    (match lambda-expr
      [(,label (lambda () ,tail))
        (let-values ([(lexpr lbind) (Tail tail)])
        `((,label (lambda () ,(make-begin lexpr))) ,@lbind))]))]

[Tail
  (lambda (tail)
    (match tail
      [(,x) (values `(,tail) '())]
      [(if ,pred ,t ,f)
        (let ([tl (unique-label 'c)] [fl (unique-label 'a)])
          (let-values ([(texpr tbind) (Tail t)] [(fexpr fbind) (Tail f)]
                       [(pexpr pbind) (Pred pred tl fl)])
            (values pexpr `((,tl (lambda () ,(make-begin texpr))) (,fl (lambda () ,(make-begin fexpr))) ,@pbind ,@tbind ,@fbind))))]
      [(begin ,effect* ... ,t)
        (cond [(null? effect*) (Tail t)]
              [else (let-values ([(rexpr rbind) (Tail `(begin ,@(cdr effect*) ,t))])
                      (let-values ([(eexpr ebind) (Effect (car effect*) rexpr)])
                        (values eexpr `(,@ebind ,@rbind))))])]))]

[Pred
  (lambda (pred tlabel flabel)
    (match pred
      [(true) (values `((,tlabel)) `())]
      [(false) (values `((,flabel)) `())]
      [(,rop ,x ,y) (guard (not (eqv? rop 'begin)))
        (values `((if (,rop ,x ,y) (,tlabel) (,flabel))) `())]
      [(if ,pred ,t ,f)
        (let ([tl (unique-label 'c)] [fl (unique-label 'a)])
          (let-values ([(texpr tbind) (Pred t tlabel flabel)] [(fexpr fbind) (Pred f tlabel flabel)]
                       [(pexpr pbind) (Pred pred tl fl)])
             (values pexpr `((,tl (lambda () ,(make-begin texpr))) (,fl (lambda () ,(make-begin fexpr))) ,@pbind ,@tbind ,@fbind))))]
      [(begin ,effect* ... ,p)
        (cond [(null? effect*) (Pred p tlabel flabel)]
              [else (let-values ([(rexpr rbind) (Pred `(begin ,@(cdr effect*) ,p) tlabel flabel)])
                      (let-values ([(eexpr ebind) (Effect (car effect*) rexpr)])
                        (values eexpr `(,@ebind ,@rbind))))])]
    ))]

[Effect
  ;returns (values expr bindings)
  (lambda (effect follow-expr)
    (match effect
      [(nop) (values follow-expr `())]
      [(set! ,x* ...) (values `(,effect ,@follow-expr) `())]
      [(if ,pred ,t ,f)
        (let ([tl (unique-label 'c)] [fl (unique-label 'a)] [j (unique-label 'j)])
          (let-values ([(texpr tbind) (Effect t `((,j)))] [(fexpr fbind) (Effect f `((,j)))]
                       [(pexpr pbind) (Pred pred tl fl)])
             (values pexpr
                     `((,j (lambda () ,(make-begin follow-expr)))
                       (,tl (lambda () ,(make-begin texpr))) (,fl (lambda () ,(make-begin fexpr)))
                       ,@pbind ,@tbind ,@fbind))))]
      [(begin ,effect* ... ,e)
       (cond [(null? effect*) (Effect e follow-expr)]
             [else (let-values ([(rexpr rbind) (Effect `(begin ,@(cdr effect*) ,e) follow-expr)])
                      (let-values ([(eexpr ebind) (Effect (car effect*) rexpr)])
                        (values eexpr `(,@ebind ,@rbind))))])]
      [(return-point ,rp-label ,t)
        (let-values ([(texpr tbind) (Tail t)])
          (values texpr `(,@tbind (,rp-label (lambda () ,(make-begin follow-expr))))))]
    ))])

    (match program
      [(letrec ([,label-def** ...] ...) ,tail)
        (let-values ([(texpr tbind) (Tail tail)])
	  `(letrec (,@tbind ,@(mymap-append Lambda label-def**)) ,(make-begin texpr)))]))))

;;;

(define optimize-jumps
  (lambda (program)
    (letrec (

[direct-jump '()]

[scan-binds
  (lambda (binds)
    (cond [(null? binds) '()]
          [else (match (car binds)
                  [(,l (lambda () (,j))) (guard (label? j) (not (eqv? l (finalize-label j))))
                    (set! direct-jump (cons `(,l ,j) direct-jump))
                    (scan-binds (cdr binds))]
                  [,x (cons (car binds) (scan-binds (cdr binds)))])]))]

[finalize-jump
  (lambda (body)
    (cond [(pair? body) (map finalize-jump body)]
          [(label? body) (finalize-label body)]
          [else body]))]

[finalize-label
  (lambda (l)
    (if (assq l direct-jump)
      (finalize-label (cadr (assq l direct-jump)))
      l))])

    (match program
      [(letrec ,binds ,t)
        (set! direct-jump '())
	(set! binds (scan-binds binds))
	(match binds
	  [([,l* (lambda () ,[finalize-jump -> t*])] ...)
	    `(letrec ([,l* (lambda () ,t*)] ...) ,(finalize-jump t))])]))))

;;;

(define flatten-program
  (lambda (program)
    (letrec (

[tmp-prog '()]

[fix-jump
  (lambda (program)
    (cond [(null? program) '()]
          [else (let* ([cdr-prog (fix-jump (cdr program))]
                       [retval-dflt (cons (car program) cdr-prog)])
                  (match (car program)
                    [(if (,reexpr* ...) (jump ,l))
                      (if (null? cdr-prog) retval-dflt
                        (match (car cdr-prog)
                          [,l2 (guard (label? l2) (eqv? l l2)) cdr-prog]
                          [(jump ,l2) (if (null? (cdr cdr-prog)) retval-dflt
                                        (match (cadr cdr-prog)
                                          [,l3 (guard (label? l3))
        (cond [(eqv? l l3) (cons `(if (not ,reexpr*) (jump ,l2)) (cdr cdr-prog))]
              [else (cons (car program) cdr-prog)])]
                                          [,x retval-dflt]))]
                          [,x retval-dflt]))]
                    [(jump ,l) (guard (label? l))
                      (if (null? cdr-prog) retval-dflt
                        (if (and (label? (car cdr-prog)) (eqv? (car cdr-prog) l)) cdr-prog retval-dflt))]
                    [,x retval-dflt])
                )]))]

[Tail
  (lambda (tail)
    (match tail
      [(begin ,x) (match x
        [(begin ,y* ...) (Tail x)]
        [(if ,y* ...) (Tail x)]
        [(,y) `((jump ,@x))])]
      [(begin ,y ,x* ...) (cons y (Tail `(begin ,@x*)))]
      [(if (,reexpr* ...) (,l1) (,l2))
        `((if ,reexpr* (jump ,l1)) (jump ,l2))]
      [(,x) `((jump ,x))]))]

[Lambda
  (lambda (lambda-expr)
    (match lambda-expr
      [(,label (lambda () ,tail)) `(,label ,@(Tail tail))]))])

      (match program
        [(letrec ([,label-def** ...] ...) ,tail)
          (set! tmp-prog `(code ,@(Tail tail) ,@(mymap-append Lambda label-def**)))])
      (fix-jump tmp-prog))))

;;;

(define generate-x86-64
  (lambda (program)
    (letrec (

[mymap
  (lambda (f x)
    (if (null? x) '() (cons (f (car x)) (mymap f (cdr x)))))]

[disp2 ;output
  (lambda (statement)
    (match statement
      [(set! ,x ,y) (guard (not (pair? y)) (not (label? y)))
        (mymap display `("movq " ,(to-str y) ", " ,(to-str x)))]
      [(set! ,x ,y) (guard (not (pair? y)) (label? y))
        (mymap display `("leaq " ,(rand->x86-64-arg y) ", " ,(to-str x)))]
      [(set! ,x (,op ,xx ,y))
        (mymap display `(,(cond [(eqv? op '+) "addq "]
				[(eqv? op '-) "subq "]
				[(eqv? op '*) "imulq "]
				[(eqv? op 'logand) "andq "]
				[(eqv? op 'logor) "orq "]
				[(eqv? op 'sra) "sarq "]) 
	                 ,(to-str y) ", " ,(to-str x)))]
      [(jump ,l) (guard (label? l))
	(mymap display `("jmp " ,(to-str l)))]
      [(jump ,r) ; r is reg or fvar
	(mymap display `("jmp *" ,(to-str r)))]
      [(if (not (,rop ,x ,y)) (jump ,l))
        (mymap display `("cmpq " ,(to-str y) ", " ,(to-str x) "\n"
	                 ,(cond [(eqv? rop '=) "jne "]
			       [(eqv? rop '>) "jle "]
			       [(eqv? rop '>=) "jl "]
			       [(eqv? rop '<) "jge "]
			       [(eqv? rop '<=) "jg "]) ,(to-str l)))]
      [(if (,rop ,x ,y) (jump ,l))
        (mymap display `("cmpq " ,(to-str y) ", " ,(to-str x) "\n"
                         ,(cond [(eqv? rop '=) "je "]
                               [(eqv? rop '<=) "jle "]
                               [(eqv? rop '<) "jl "]
                               [(eqv? rop '>=) "jge "]
                               [(eqv? rop '>) "jg "]) ,(to-str l)))]
      [,x (mymap display `(,(to-str x) ":"))] ; a label
    )
    (display "\n"))])

    (match program
      [(code ,st* ...) (emit-program (mymap disp2 st*))]))))

;;;

(define mymap-append
  (lambda (f x)
    (if (null? x) '() (append (f (car x)) (mymap-append f (cdr x))))))

(define to-str 
  (lambda (x) 
    (cond [(label? x) (label->x86-64-label x)]
	  [else (rand->x86-64-arg x)])))

;set minus
(define rm
  (lambda (ls x)
    (cond [(null? x) ls]
	  [else (remv (car x) (rm ls (cdr x)))])))

(define (make-nopless-begin x*)
(let ([x* (remove '(nop) x*)])
(if (null? x*)
'(nop)
(make-begin x*))))

(define unique
  (lambda (x)
    (cond [(null? x) '()]
	  [else (set-cons (car x) (unique (cdr x)))])))

(define prim-list '(+ - * car cdr cons make-vector vector-length vector-ref void
                    <= < = >= > boolean? eq? fixnum? null? pair? vector? procedure?
                    set-car! set-cdr! vector-set!))
