#lang racket
;; Assignment 4: A church-compiler for Scheme, to Lambda-calculus
;; IMMEDIATELY read the README, please

(provide church-compile
         ; provided conversions, used by test scripts:
         church->nat
         church->bool
         church->listof)

;; Input language:
;
; e ::= (letrec ([x (lambda (x ...) e)]) e)    
;     | (let ([x e] ...) e)  
;     | (let* ([x e] ...) e)
;     | (lambda (x ...) e)
;     | (e e ...)    
;     | x  
;     | (and e ...) | (or e ...)s
;     | (if e e e)
;     | (prim e) | (prim e e)
;     | datum
; datum ::= nat | (quote ()) | #t | #f 
; nat ::= 0 | 1 | 2 | ... 
; x is a symbol
; prim is a primitive operation in list prims
; The following are *extra credit*: -, =, sub1  
(define prims '(+ * - = add1 sub1 cons car cdr null? not zero?))

; This input language has semantics identical to Scheme / Racket, except:
;   + You will not be provided code that yields any kind of error in Racket
;   + You do not need to treat non-boolean values as #t at if, and, or forms
;   + primitive operations are either strictly unary (add1 sub1 null? zero? not car cdr), 
;                                           or binary (+ - * = cons)
;   + There will be no variadic functions or applications---but any fixed arity is allowed

;; Output language:

; e ::= (lambda (x) e)
;     | (e e)
;     | x
;
; also as interpreted by Racket


;; Using the following decoding functions:

; A church-encoded nat is a function taking an f, and x, returning (f^n x)
(define (church->nat c-nat)
  ((c-nat add1) 0))

; A church-encoded bool is a function taking a true-thunk and false-thunk,
;   returning (true-thunk) when true, and (false-thunk) when false
(define (church->bool c-bool)
  ((c-bool (lambda (_) #t)) (lambda (_) #f)))

; A church-encoded cons-cell is a function taking a when-cons callback, and a when-null callback (thunk),
;   returning when-cons applied on the car and cdr elements
; A church-encoded cons-cell is a function taking a when-cons callback, and a when-null callback (thunk),
;   returning the when-null thunk, applied on a dummy value (arbitrary value that will be thrown away)
(define ((church->listof T) c-lst)
  ; when it's a pair, convert the element with T, and the tail with (church->listof T)
  ((c-lst (lambda (a) (lambda (b) (cons (T a) ((church->listof T) b)))))
   ; when it's null, return Racket's null
   (lambda (_) '())))


;; Write your church-compiling code below:

; churchify recursively walks the AST and converts each expression in the input language (defined above)
;   to an equivalent (when converted back via each church->XYZ) expression in the output language (defined above)

(define church-true '(lambda (x) (lambda (y) (x '()))))

(define church-false '(lambda (x) (lambda (y) (y '()))))

(define church-null 
  (lambda (c) (lambda (n) (n '()))))

(define (gen-n n)
  (define (h x)
    (if (= x 0) 'x `(f ,(h (sub1 x)))))
  `(lambda (f) (lambda (x) ,(h n))))

(define church-not `(lambda (bool) (if bool #f #t)))


;; Primitive Operation Church Encodings
(define church-primitives
  (hash
   '+ `(lambda (m) (lambda (n) (lambda (f) (lambda (x) ((m f) ((n f) x))))))
   '* `(lambda (m) (lambda (n) (lambda (f) (lambda (x) ((m (n f)) x)))))
   'add1 `(lambda (n) (lambda (f) (lambda (x) (f ((n f) x)))))
   'sub1 `(lambda (n) (lambda (f) (lambda (x) 
                                    ((((n (lambda (g) (lambda (h) (h (g f)))))
                                       (lambda (u) x))
                                      (lambda (u) u)))))
            'zero? `(lambda (n) ((n (lambda (x) church-false)) church-true))
            'not `(lambda (b) ((b church-false) church-true)))))

(define church-Y-combinator `((lambda (u) (u u)) (lambda (y) (lambda (mk) (mk (lambda (x) (((y y) mk) x)))))))
(define church_- `(lambda (a) (lambda (b)((b (lambda (b)(lambda (c)(lambda (d)(((b (lambda (e) (lambda (h) (h (e c)))))(lambda (y) d))(lambda (y) y)))))) a))))


(define (churchify e)
  (match e
    ; Recursively-defined functions
    [`(letrec ([,f (lambda (,args ...) ,e0)]) ,e1)
     (churchify `(let ([,f (church-Y-combinator (lambda (,f) (lambda ,args ,e0)))]) ,e1))]

    [#t church-true]
    [#f church-false] 
    [`cons (churchify '(lambda (x y) (lambda (f z) (f x y))))]
    [`(car ,lst) `((,(churchify lst) (lambda (b) (lambda (c) b))) (lambda (_) a))] 
    [`(cdr ,lst) `((,(churchify lst) (lambda (b) (lambda (c) c))) (lambda (_) a))]   
    
    
    [`(if ,e0 ,e1 ,e2) (churchify `((,e0 (lambda (_) ,e1)) (lambda (_) ,e2)))]
    [`(let () ,e) (churchify e)]
    [`(let ([,es ,eas] ...) ,e-b)
     (churchify `((lambda ,es ,e-b) ,@eas))]

    [`(null? ,x) (churchify `((lambda (a) (a (lambda (b c) #f) (lambda (_) #t))) ,x))]
    [`(zero? ,x) (churchify `((lambda (n) (n (lambda (_) #f) #t)) ,x))]
    [`(- ,e0 ,e1) `((,church_- ,(churchify e0)) ,(churchify e1))]

    [`(lambda () ,e) `(lambda (_) ,(churchify e))]
    [`(lambda (,x) ,e-b) `(lambda (,x) ,(churchify e-b))]
    [`(lambda (,x . ,x-rst) ,e-b)
     (churchify `(lambda (,x) (lambda ,x-rst ,e-b)))]

    [`(,e) `(,(churchify e) (lambda (x) x))]
    [`(,e ,e0) `(,(churchify e) ,(churchify e0))] 

    ;; Remember that let is a left-left (immediately-applied) lambda

    ;; 0-binding let
    [`(let () ,e1) (churchify e1)] ;; just churchify e1, do the same for let*
    ;; 1 or more binding let
    [`(let ([,ex ,es] ...) ,eb)
     (churchify `((lambda ,ex ,eb) ,@es))]   ;; potential problem

    ;; 0-binding let* (handled same as 0-binding let)
    [`(let* ([,x0 ,e0] ,rest ...) ,e1) (churchify `(let ([,x0 ,e0]) (let* ,rest ,e1)))]
    [`(let* () ,e1) (churchify e1)]
         
    ;; 0-arg lambda
    [`(lambda () ,e) (churchify e)]
    ;; 1 argument lambdas
    [`(lambda (,x) ,e) `(lambda (,x) ,(churchify e))]
    ;; multi-arg lambda
    [`(lambda (,x . ,rest) ,y)
     (churchify `(lambda (,x) (lambda ,rest ,y)))]

    ;; and
    [`(and) (churchify church-true)]
    [`(and ,x) (churchify x)]
    [`(and ,e0 ,rest ...) (churchify `(if ,e0 (and ,@rest) #f))]

    ;; or
    [`(or) (churchify church-false)]
    [`(or ,x) (churchify x)]
    [`(or ,x ,rest ...)
     (churchify 
      `(if ,x 
           ,x 
           ,(if (null? rest) 
                x 
                `(or ,@rest))))]
    [`(not ,x) (churchify `(church-not ,x))]


    ;; the empty list and booleans (see class slides / video about these)

    [''() church-null]
    [(? (lambda (x) (eq? x '()))) church-null] 

    [(? number? n) (gen-n n)]

    ; Untagged (0-argument) application (again, see slides)
    [`(,fun)
     (churchify fun)]
    [`(,fun ,arg) `(,(churchify fun) ,(churchify arg))]
    [`(,fun ,arg . ,rest)
     (churchify `((,fun ,arg) ,@rest))]

    [(? symbol? x) 
     (if (hash-has-key? church-primitives x)
         (hash-ref church-primitives x)
         x)]))

(define (church-compile e)
  (churchify
   `(let ([church-Y-combinator ,church-Y-combinator] [church-not ,church-not]),e)))
