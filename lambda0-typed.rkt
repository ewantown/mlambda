#lang racket

(define sub# 0) (define uni# 0) (define ret# 0) (define rec# 0) (define lim# 0)
(define (reset-stats)
  (set! sub# 0) (set! uni# 0) (set! ret# 0) (set! rec# 0))
(define (print-stats) 
  (print (list 'subs# sub# 'uni# uni# 'ret# ret# 'rec# rec#)))

(define (meval sexp)
  (letrec ((sub (lambda (a x e)
                  "Substitute a for x in e."
                  (begin (set! sub# (add1 sub#)))
                  (match e
                    ;; Implicit definition of syntax
                    [`(callcc ,f) `(callcc ,(sub a x f))]
                    [`(dropcc ,t) `(dropcc ,(sub a x t))]
                    [`(ρ ,p)    `(ρ ,(sub a x p))]
                    [`(σ ,f)    `(σ ,(sub a x f))]                                        
                    [`(□ ,p)    `(□ ,(sub a x p))]
                    [`(▷ ,p ,q) `(▷ ,(sub a x p) ,(sub a x q))]
                    [`(ε ,p)    `(ε ,(sub a x p))]
                    [`(→ ,y ,b) `(→ ,y ,(if (eq? x y) b (sub a x b)))]
                    [`(,l ,r)   `(,(sub a x l) ,(sub a x r))]
                    [_           (if (eq? e x) a e)])))
           (ret (λ (v bound? cc)
                  "Apply continuation to value v (i.e. return)."
                  (begin (set! ret# (add1 ret#)))
                  (match cc
                    ['• v]
                    [`((ε •) . ,k)
                     (match v
                       [`(□ ,p) (rec p bound? k)] [_ (error "Not □: " v)])]
                    [`((▷  • ,r) . ,k) (rec r bound? `((▷ ,v •) . ,k))]
                    [`((▷ ,l  •) . ,k)
                     (let [(lv (match l [`(□ ,lv) lv] [_ (error "Not □: " l)]))
                           (rv (match v [`(□ ,rv) rv] [_ (error "Not □: " v)]))]
                       (rec `(□ (,lv ,rv)) bound? k))]
                    [`((• ,r) . ,k)
                     (let* [(x (match v [`(→ ,x ,b) x] [_ (error "Not →:" v)]))
                            (b (match v [`(→ ,x ,b) b]))]
                       (rec (sub r x b) (λ (y) (or (eq? x y) (bound? y))) k))]
                    [_ (error "Ill-formed continuation:" cc)])))
           (rec (λ (e bound? cc)
                  "Interpret expression e in the current context."
                  (begin (set! rec# (add1 rec#)))
                  ;; (trace e cc)
                  (match e
                    ;; Continuations
                    [`(callcc ,f)
                     (let* [(• (gensym))
                            (u (sub • '• (uni cc)))]
                       (rec `(,f (→ ,• ,u)) bound? '•))]
                    [`(dropcc ,t) (rec `(callcc (→ ,(gensym) ,t)) bound? cc)]

                    ;; Delimited continuations
                    [`(ρ ,e) (rec e bound? `((ρ •) . ,cc))]                    
                    [`(σ ,f)
                     (let* [(• (gensym))
                            (u (sub • '• (car (lim cc))))]
                       (rec `(,f (→ ,• ,u)) bound? (cdr (lim cc))))]                                          
                    
                    ;; Self-interpreter
                    [`(ε ,t) (rec t bound? `((ε •) . ,cc))]
                    
                    ;; Code values                    
                    [`(□ ,t) (ret `(□ ,t) bound? cc)]
                    [`(▷ ,l ,r) (rec l bound? `((▷ • ,r) . ,cc))]

                    ;; λ-calculus (untyped call-by-name) base
                    [`(→ ,x ,b)
                     (let [(y (if (bound? x) (gensym) x))]
                       (ret `(→ ,y ,(if (bound? x) (sub y x b) b)) bound? cc))]
                    [`(,l ,r) (rec l bound? `((• ,r) . ,cc))]
                    [_ (error "Ill-formed expression: " e)])))
           (lim (λ (cc)
                  "Delimit current continuation"
                  (begin (set! lim# (add1 ret#)))
                  (match cc
                    ['• `(• . •)]
                    [`(,e . ((ρ •) . ,k)) `(,e . ,k)]
                    [`(,e . ,k) (lim k)]
                    [_ (error "Ill-formed continuation:" cc)])))
           (uni (λ (cc)
                  "Collapse current continuation into 1-place-open expression."
                  (begin (set! uni# (add1 uni#)))
                  (match cc
                    ['• '•]
                    [`(,e . ,k) (sub e '• (uni k))]
                    [_ (error "Ill-formed continuation:" cc)])))           
           (trace (λ (e cc)
                    (newline) (newline)
                    (print (uni cc)) (newline) (newline)
                    (print e) (newline) (newline))))
    (rec sexp (λ (_) #f) '•)))

;; Code combinators
;; (→ x (→ y (▷ x y)))      :: □(A -> B) -> (□A -> □B) =: axiom K
;; (→ x (□ x))              ::  A -> □A                =: axiom N (when x :: A)
;; (→ x (□ x))              :: □A -> □□A               =: axiom 4 (when x :: □A)
;; (→ x (ε x))              :: □A -> A                 =: axiom T

;; This method, passing a defunctionalized continuation as list of one-place
;; open expressions, then "rolling it up" into a single closed expression,
;; gives us one representation, for both the abstract syntax tree and
;; a self-interpreter-determined path from the root of the abstract syntax tree
;; (or delimiter) to a point in the abstract syntax (sub)tree.
;; We then make this representation available in both object and meta system.

;; Meta-theoretically, we use the path-at-a-point to make the evaluation
;; strategy of the object-system self-interpreter independent of the evaluation
;; strategy of the (defining) metalanguage (racket) interpreter.

;; By binding a metatheoretic variable to the end of a path, and making
;; the variable available as parameter to an object-system representation
;; of the path as a lambda term, we make the path to any given point in
;; the computation available within the system at that point, as a "backward"
;; path from the point to the root (delimiter) of the abstract syntax (sub)tree.

;; That enables a node in the object system AST to encode a program which
;; captures the position of the node in the flow of execution, as a path through
;; the AST, then via its children independently determines the root of the AST,
;; effectively specifying the next instruction to execute. Subtrees of such a
;; node (in the body of the function supplied to callcc) may "return" by
;; invoking the parameter-supplied path-cum-function on a value, or they may
;; "jump" by not invoking the path-cum-function at all. 
;; reinstate the captured root as root - ie. completing the path with a value at
;; the capture-point, thus "returning" a value to that point.


(define-syntax test
  (syntax-rules ()
    [(_ name prop) (when (not prop) (error "Test failed: " name))]))

(define squine0 '((→ x (▷ x (□ x))) (□ (→ x (▷ x (□ x))))))
(define squine1 '(□ ((→ x (▷ x (□ x))) (□ (→ x (▷ x (□ x)))))))
(test 'squine-test-0 (not (equal? squine0 (meval squine0))))
(test 'squine-test-1 (equal? squine1 (meval squine0)))
(test 'squine-test-2 (equal? squine1 (meval (meval squine1))))
(test 'squine-test-3 (equal? squine1 (meval `(ε ,squine1))))

;; Object-lang
(define zero '(→ f (→ x x)))
  
(define next '(→ n (→ f (→ x (f ((n f) x))))))
  
(define prev '(→ n (→ f (→ x (((n (→ g (→ h (h (g f))))) (→ o x)) (→ i i))))))

(define iszero '(→ f ((f (→ z (→ x (→ y y)))) (→ x (→ y x)))))
  
(define ifzero `((→ p (→ a (→ b ((p a) b)))) ,iszero))

(define Y '(→ f ((→ x (f (x x))) (→ x (f (x x))))))
(define plus `(→ f (→ n (→ m (((,ifzero n) m) ((f (,prev n)) (,next m)))))))

(define addo `(,Y ,plus))
(define addo2 `(ε (▷ (□ ,Y) (□ ,plus))))
(define addo3 `(((→ y (→ x (ε (▷ (□ y) (□ x))))) ,Y) ,plus))

;; □(□A -> A) -> A
(define sfix '(→ e ((→ x ((ε x) x)) (▷ (□ (→ t (→ y (t (▷ y (□ y)))))) e))))

;; □(N -> (N -> N)) -> (N -> (N -> N))
(define splus `(→ e (→ n (→ m (((,ifzero n) m) (((ε e) (,prev n)) (,next m)))))))
;; ... applying the rule requires interpreting an expression for the rule

;; N -> (N -> N)
(define saddo `(,sfix (□ ,splus)))
                    

(define addm (λ (i j) (number (meval `((,addo ,(numeral i)) ,(numeral j))))))


;;(define infer `(→ e (→ p (→ q (→ k (((ε e) (□ (p q))) (□ q)))))));; ??? 
;;(define inference `(,sfix (□ ,infer))) ;; ???

;; Meta-lang
(define numeral
  (λ (n) (if (< 0 n) `(,next ,(numeral (sub1 n))) zero)))

(define translate
  (λ (s) (match s
           [`(□ ,t) `,t]
           [`(→ ,x ,b) `(λ (,x) ,(translate b))]
           [`(,l ,r) `(,(translate l) ,(translate r))]           
           [_ s])))

(define number
  (λ (e)
    (if (number? e)
        e
        (((eval (translate (meval e))) (λ (x) (add1 (number x)))) 0))))

;; Example for callcc
(test 'dropcc-test
      (let [(sexp `(((,ifzero (((,ifzero ,(numeral 1))
                                ,zero)
                               (dropcc ,(numeral 3))))
                     ,(numeral 1))
                    ,zero))]
        (= 3 (number (meval sexp)))))

(test 'callcc-test
      (let [(sexp `(((,ifzero (((,ifzero ,(numeral 1))
                                ,zero)
                               (callcc (→ c (c (→ x ,zero))))))
                     ,(numeral 1))
                    ,zero))]
        (= 0 (number (meval sexp)))))
