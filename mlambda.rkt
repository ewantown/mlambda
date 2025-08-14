#lang racket

;; Call this language M-λ, i.e. "meta-lambda"

;; _Syntax:_                    .  _Semantics:_
;; <sym>   ≡ x: (symbol? x)     .      
;; <wff> ::= (-> <sym> <wff>)   .  := abstraction
;;         | (<wff> <wff>)      .  := application (call-by-name)
;;         | - - - - - - - - -  .
;;         | (□ <wff>)          .  := quotation
;;         | (▷ <wff> <wff>)    .  := quote-combination - the "Kleene" operator
;;         | (ε <wff>)          .  := evaluation
;;         | - - - - - - - - -  .
;;         | (ρ <wff>)          .  := "reset" (continuation delimiter)
;;         | (σ <wff>)          .  := "shift" (delim. continuation introducer)
;;         | (callcc <wff>)     .  := "control" (global continuation introducer)
;;         | (dropcc <wff>)     .  := "abort"   (global continuation eliminator)


(define (meval sexp)
  "Interpreter for M-λ"
  (letrec ((sub (lambda (a x e)
                  "Substitute 'a' for 'x' in 'e'."
                  (match e
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
                  "Apply continuation to value v."
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
                  "Substitutionally interpret e in the current context."
                  (match e
                    ;; Delimited continuation handling
                    [`(ρ ,e) (rec e bound? `((ρ •) . ,cc))]
                    [`(σ ,f)
                     (let* [(• (gensym))
                            (u (sub • '• (car (lim cc))))]
                       (rec `(,f (→ ,• ,u)) bound? (cdr (lim cc))))]
                    
                    ;; Global continuation handling
                    [`(callcc ,f)
                     (let* [(• (gensym))
                            (u (sub • '• (uni cc)))]
                       (rec `(,f (→ ,• ,u)) bound? '•))]
                    [`(dropcc ,t) (rec `(callcc (→ ,(gensym) ,t)) bound? cc)]

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
                  "Delimit continuation"
                  (match cc
                    ['• `(• . •)]
                    [`(,e . ((ρ •) . ,k)) `(,e . ,k)]
                    [`(,e . ,k) (lim k)]
                    [_ (error "Ill-formed continuation:" cc)])))
           (uni (λ (cc)
                  "Collapse continuation into one-place-open expression."
                  (match cc
                    ['• '•]
                    [`(,e . ,k) (sub e '• (uni k))]
                    [_ (error "Ill-formed continuation:" cc)])))
           (trace (λ (e cc)
                    (newline) (newline)
                    (print (uni cc)) (newline) (newline)
                    (print e) (newline) (newline))))
    (rec sexp (λ (_) #f) '•)))

;; Code combinators - cf. extended Curry-Howard, modal logic S4:
;; (→ x (→ y (▷ x y)))      :: □(A -> B) -> (□A -> □B) =: axiom K
;; (→ x (□ x))              ::  A -> □A                =: axiom N (when x :: A)
;; (→ x (□ x))              :: □A -> □□A               =: axiom 4 (when x :: □A)
;; (→ x (ε x))              :: □A -> A                 =: axiom T

;; Commentary:
;;
;; The method of passing a defunctionalized continuation as list of one-place
;; open expressions, then "rolling it up" into a single closed expression,
;; gives us one representation, for both the abstract syntax tree and
;; a self-interpreter-determined path from the root of the abstract syntax tree
;; (or delimiter) to a point in the abstract syntax (sub)tree.
;; We then make this representation available in both object and meta systems.

;; Meta-theoretically, we use the defunctionalized path-at-a-point to make the
;; evaluation strategy of the object-system self-interpreter independent of the
;; evaluation strategy of the (defining) metalanguage (i.e. Racket) interpreter.

;; By binding a meta-theoretic variable to the open end of a given path, and
;; making the variable available as parameter to an object-system representation
;; of the path as a lambda term, we make the path (to any given point) in
;; the computation available within the system (at that point), as a "backward"
;; path from the point (delimiter) to the root of the abstract syntax (sub)tree.

;; That enables a node in the object system AST to encode a program which
;; captures the position of the node in the flow of execution, as a path through
;; the AST, then via its children independently determines the root of the AST,
;; by effectively specifying the next instruction to execute. Subtrees of such
;; a global continuation node (in the body of the abstraction given to callcc), 
;; "continue" by applying the path-cum-function-parameter, or simply
;; "jump" by never invoking the path-cum-function-parameter at all.


(define-syntax test
  (syntax-rules ()
    [(_ name prop) (when (not prop) (error "Test failed: " name))]))

;; Staged Quines
;; squine0 is not a Quine in M-λ, as it evaluates to the quotation of itself
;; but the value of squine0, i.e. squine1, is a Quine in M-λ
(define squine0 '((→ x (▷ x (□ x))) (□ (→ x (▷ x (□ x))))))
(define squine1 '(□ ((→ x (▷ x (□ x))) (□ (→ x (▷ x (□ x)))))))
(define squine2 '(□ (□ ((→ x (▷ x (□ x))) (□ (→ x (▷ x (□ x))))))))
;; ...
(test 'squine-test-0a (not (equal? squine0 (meval squine0))))
(test 'squine-test-0b (equal? squine1 (meval squine0)))
(test 'squine-test-1a (equal? squine1 (meval squine1)))
(test 'squine-test-1b (equal? squine1 (meval (meval squine1))))
;; 1c exhibits a unique congruence, due to the relation of squine0 and squine1
(test 'squine-test-1c (equal? squine1 (meval `(ε ,squine1))))
(test 'squine-test-2a (equal? squine2 (meval squine2)))
;; the congruence does not hold for n > 1
(test 'squine-test-2b (not (equal? squine2 (meval `(ε ,squine2)))))
(test 'squine-test-2c (equal? squine1 (meval `(ε ,squine2))))


;; Basic encoding of arithmetic in object system
(define zero '(→ f (→ x x)))

(define succ '(→ n (→ f (→ x (f ((n f) x))))))

(define prev '(→ n (→ f (→ x (((n (→ g (→ h (h (g f))))) (→ o x)) (→ i i))))))

(define iszero '(→ f ((f (→ z (→ x (→ y y)))) (→ x (→ y x)))))

(define ifzero `((→ p (→ a (→ b ((p a) b)))) ,iszero))

(define Y '(→ f ((→ g (f (g g))) (→ g (f (g g))))))
(define plus `(→ f (→ n (→ m (((,ifzero n) m) ((f (,prev n)) (,succ m)))))))
(define addo `(,Y ,plus))


;; Staged recursion, via sfix construct from Kleene second fixpoint theorem
(define sfix ;; □(□A -> A) -> A
  '(→ e ((→ x ((ε x) x)) (▷ (□ (→ t (→ y (t (▷ y (□ y)))))) e))))

(define splus ;; □(N -> (N -> N)) -> (N -> (N -> N))
  `(→ e (→ n (→ m (((,ifzero n) m) (((ε e) (,prev n)) (,succ m)))))))
;; Notice: applying the rule requires interpreting an expression for the rule

(define saddo ;; N -> (N -> N)
  `(,sfix (□ ,splus)))


;; Some meta-linguistic utilities
(define numeral
  (λ (n) (if (< 0 n) `(,succ ,(numeral (sub1 n))) zero)))

(define number
  (λ (e)
    (if (number? e)
        e
        (((eval (translate (meval e))) (λ (x) (add1 (number x)))) 0))))

(define translate
  (λ (s) (match s
           [`(□ ,t) `,t]
           [`(→ ,x ,b) `(λ (,x) ,(translate b))]
           [`(,l ,r) `(,(translate l) ,(translate r))]
           [_ s])))

(define addm  (λ (i j) (number (meval `((,addo ,(numeral i)) ,(numeral j))))))
(define saddm (λ (i j) (number (meval `((,saddo ,(numeral i)) ,(numeral j))))))


;; Tests

(test 'adding-test1 (= 5 (addm 1 4) (saddm 1 4)))
(test 'adding-test2 (= 12 (addm 5 7) (saddm 8 4)))

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
