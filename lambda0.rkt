#lang racket

(define (meval sexp)
  (letrec ((trace (λ (e cc)
                    (newline) (newline)
                    (print (uni cc)) (newline) (newline)
                    (print e) (newline) (newline)))
           (sub (lambda (a x e)
                  "Substitute a for x in e."
                  (match e                    
                    [`(□ ,p)    `(□ ,(sub a x p))]
                    [`(▷ ,p ,q) `(▷ ,(sub a x p) ,(sub a x q))]
                    [`(→ ,y ,b) `(→ ,y ,(if (eq? x y) b (sub a x b)))]
                    [`(,l ,r)   `(,(sub a x l) ,(sub a x r))]
                    [_           (if (eq? x e) a e)])))
           (uni (λ (cc)
                  "Collapse current continuation into incomplete expression."
                  (match cc
                    ['• '•]
                    [`(,e . ,k) (sub e '• (uni k))]
                    [_ (error "Bad continuation:" cc)])))
           (ret (λ (v bound? cc)
                  "Apply the current continuation to value v."
                  (match cc
                    ['• v]
                    [`((• ,r) . ,k)
                     (let* [(x (match v [`(→ ,x ,b) x] [_ (error "Not →:" v)]))
                            (b (match v [`(→ ,x ,b) b]))]
                       (rec (sub r x b) (λ (y) (or (eq? x y) (bound? y))) k))]
                    [`((▷  • ,r) . ,k) (rec r bound? `((▷ ,v •) . ,k))]
                    [`((▷ ,l  •) . ,k)
                     (let [(lv (match l [`(□ ,lv) lv] [_ (error "Not □: " l)]))
                           (rv (match v [`(□ ,rv) rv] [_ (error "Not □: " v)]))]
                       (ret `(□ (,lv ,rv)) bound? k))]
                    [`((ε •) . ,k)
                     (match v
                       [`(□ ,p) (rec p bound? k)] [_ (error "Not □: " v)])]
                    [_ (error "Ill-formed continuation:" cc)])))
           (rec (λ (e bound? cc)
                  "Interpret expression e in the current context."
                  (trace e cc)
                  (match e
                    ;; Code values                    
                    [`(□ ,t) (ret `(□ ,t) bound? cc)]
                    [`(▷ ,l ,r) (rec l bound? `((▷ • ,r) . ,cc))]
                                         
                    ;; Self-interpreter
                    [`(ε ,t) (rec t bound? `((ε •) . ,cc))]

                    ;; Continuations
                    [`(callcc ,t)
                     (let* [(• (gensym))
                            (u (sub • '• (uni cc)))]
                       (rec `(,t (→ ,• (dropcc ,u))) bound? '•))]
                    [`(dropcc ,t) (rec `(callcc (→ ,(gensym) ,t)) bound? cc)]
                                        
                    ;; λ-calculus fragment (call-by-name):
                    [`(→ ,x ,b)
                     (let [(y (if (bound? x) (gensym) x))]
                       (ret `(→ ,y ,(if (bound? x) (sub y x b) b)) bound? cc))]
                    [`(,l ,r) (rec l bound? `((• ,r) . ,cc))]
                    [_ (error "Ill-formed expression: " e)]))))
    (rec sexp (λ (_) #f) '•)))

;; Code combinators
;; (→ x (→ y (▷ x y)))      :: □(A -> B) -> (□A -> □B) =: axiom K
;; (→ x (□ x))              ::  A -> □A                =: axiom N (when x :: A)
;; (→ x (□ x))              :: □A -> □□A               =: axiom 4 (when x :: □A)
;; (→ x (ε x))              :: □A -> A                 =: axiom T

(define-syntax test
  (syntax-rules ()
    [(_ name prop) (when (not prop) (error "Test failed: " name))]))

(define squine0 '((→ x (▷ x (□ x))) (□ (→ x (▷ x (□ x))))))
(define squine1 '(□ ((→ x (▷ x (□ x))) (□ (→ x (▷ x (□ x)))))))
(test 'squine-test-0 (not (equal? squine0 (meval squine0))))
(test 'squine-test-1 (equal? squine1 (meval squine0)))
(test 'squine-test-2 (equal? squine1 (meval (meval squine1))))
(test 'squine-test-3 (equal? squine1 (meval `(ε ,squine1))))

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

;; Object-lang
(define zero '(→ f (→ x x)))
  
(define next '(→ n (→ f (→ x (f ((n f) x))))))
  
(define prev '(→ n (→ f (→ x (((n (→ g (→ h (h (g f))))) (→ o x)) (→ i i))))))

(define iszero '(→ f ((f (→ z (→ x (→ y y)))) (→ x (→ y x)))))
  
(define branch '(→ p (→ a (→ b ((p a) b)))))
  
(define ifzero `(,branch ,iszero))

(define Y '(→ f ((→ x (f (x x))) (→ x (f (x x))))))

(define +nf `(→ f (→ n (→ m (((,ifzero n) m) ((f (,prev n)) (,next m)))))))

(define addo `(,Y ,+nf))

(define addm (λ (i j) (number (meval `((,addo ,(numeral i)) ,(numeral j))))))
