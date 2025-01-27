#lang racket

(define-syntax test
  (syntax-rules ()
      [(_ name prop) (when (not prop) (error "Test failed: " name))]))

(define (meval sexp)
  (letrec ((trace (λ (e cc)
                    (print (uni cc)) (newline) (newline)
                    (print e) (newline) (newline)))                    
           (sub (lambda (a x e)
                  "Substitute a for x in e."
                  (match e
                    [`(λ (,y) ,b) `(λ (,y) ,(if (eq? x y) b (sub a x b)))]
                    [`(→ ,l ,r)   `(→ ,(sub a x l) ,(sub a x r))]
                    [`(□ ,p)      `(□ ,(sub a x p))]
                    [`(,l ,r)     `(,(sub a x l) ,(sub a x r))]
                    [_             (if (eq? x e) a e)])))
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
                     (let* [(x (match v [`(λ (,x) ,b) x] [_ (error "Not λ:" v)]))
                            (b (match v [`(λ (,x) ,b) b]))]
                       (rec (sub r x b) (λ (y) (or (eq? x y) (bound? y))) k))]
                    [`((meval •) . ,k)
                     (match v
                       [`(□ ,p) (rec p bound? k)] [_ (error "Not □: " v)])]
                    [_ (error "Bad continuation:" cc)])))
           (rec (λ (e bound? cc)
                  "Interpret expression e in the current context."
                  (trace e cc)
                  (match e
                    ;; Continuations
                    [`(callcc ,t)
                     (let* [(• (gensym))
                            (u (sub • '• (uni cc)))]
                       (rec `(,t (λ (,•) (dropcc ,u))) bound? '•))]
                    [`(dropcc ,t) (rec `(callcc (λ (,(gensym)) ,t)) bound? cc)]
                    
                    ;; Code combinators
                    [`(□ ,t) (ret `(□ ,t) bound? cc)]
                    [`(→ (□ ,l) (□ ,r)) (ret `(□ (,l ,r)) bound? cc)]
                    
                    ;; Self-interpreter
                    [`(meval ,t) (rec t bound? `((meval •) . ,cc))]

                    ;; λ-calculus fragment (call-by-name):
                    [`(λ (,x) ,b)
                     (let [(y (if (bound? x) (gensym) x))]
                       (ret `(λ (,y) ,(if (bound? x) (sub y x b) b)) bound? cc))]
                    [`(,l ,r) (rec l bound? `((• ,r) . ,cc))]
                    [`,s (ret `(□ ,s) bound? cc)] ;; ???
                    [_ (error "Ill-formed: " e)]))))
    (rec sexp (λ (_) #f) '•)))

;; Modal fragment:
;; (λ (x) (□ x)) ::  A ->  □A  := axiom N (when x :: A)
;; (λ (x) (□ x)) :: □A -> □□A  := axiom 4 (when x :: □A)      
;; (λ (x) (meval x)) :: □A -> A := axiom T
;; (λ (x) (λ (y) (→ (□ x) (□ y)))) :: □(A -> B) -> (□A -> □B) =: axiom K
                    

(define a '(λ (x) (λ (y) (□ (x y)))))
(define b '(λ (x) (□ x)))

(define sd '(λ (x) ((meval x) x)))
(define qf `(lambda (t) (λ (y) (t ((,a y) (,b y))))))
;(define sfix `(λ (e) (,sd ((,a (□ ,qf)) e))))
;; (define sfix `(λ (e) ((λ (x) ((meval x) x))
;;                       (□ ((λ (t) (λ (y) (t (meval (□ (y (□ y))))))) e)))))

(define quine
  ((λ (x) (list x (list 'quote x))) '(λ (x) (list x (list 'quote x)))))

;; (□ ((□ A -> Z) -> Z)) -> (□ ((□ A -> Z) -> Z))
(define squine '(□ ((λ (x) (→ x (□ x))) (□ (λ (x) (→ x (□ x)))))))
(test 'squine-test (equal? squine (meval `(meval ,squine))))

;; (define sfix
;;   '(λ (e)
;;      ((λ (x) ((meval x) x))
;;       (((λ (x) (λ (y) (combine x y)))
;;         (combine '(λ (t) (λ (y) (t (combine y (mention y)))))))
;;        e))))
       
;; (define sfix ; a splices quoted forms, b quotes
;;   '(λ (a)
;;      (λ (b)
;;        (λ (x)
;;          ((comp `'(,x ,x)) ((a '(λ (t) (λ (y) (t ((a y) (b y)))))) x))))))

;(define a
;  `(λ (q) (λ (p) (',(comp q)))))

  
;; (define comp
;;   (λ (sexp)
;;     (letrec ((rec (λ (e bound?)
;;                     (match e
;;                       [`',c `',c]
;;                       [`(comp ,c) (comp (eval c))]                      
;;                       [`(λ (,x) ,b)
;;                        (let [(y (if (bound? x) (gensym) x))]
;;                          `(λ (,y) ,(if (bound? x) (sub y x b) b)))]
;;                       [`(,l ,r)
;;                        (let* [(f (rec l (λ (_) #f)))
;;                               (x (match f [`(λ (,x) ,b) x]))
;;                               (b (match f [`(λ (,x) ,b) b]))]
;;                          (rec (sub r x b) (λ (y) (or (eq? x y) (bound? y)))))]
;;                       [_ e]))))
;;       (rec sexp (λ (_) #f)))))



;(λ (x) (λ (y) (eval (comp '(if x x y)))))
;(λ (x) (λ (y) (comp (eval '(if x x y)))))

;; Object-lang
(define zero
  '(λ (f) (λ (x) x)))

(define next
  '(λ (n) (λ (f) (λ (x) (f ((n f) x))))))

(define prev
  '(λ (n) (λ (f) (λ (x) (((n (λ (g) (λ (h) (h (g f))))) (λ (_) x)) (λ (i) i))))))

(define iszero
  '(λ (f) ((f (λ (z) (λ (x) (λ (y) y)))) (λ (x) (λ (y) x)))))

(define branch
  '(λ (p) (λ (a) (λ (b) ((p a) b)))))

(define ifzero `(,branch ,iszero))

;; Y :: (A -> B) -> B, corresponds to "Curry's Paradox"
;; x :: (C -> A)
;; => x :: ((C -> A) -> A)
;; => x :: (((C -> A) -> A) -> A)
;; show-stopper: x :: C := (C -> A)
;; i.e. self-denotative definition of generic (monadic) "computation" type
(define Y '(λ (f) ((λ (x) (f (x x))) (λ (x) (f (x x))))))

;; (define sfix
;;   `(λ (e) ((λ (x) ((meval x) x))
;;            (□ ((λ (t) (λ (y) (t (meval (□ (y (□ y))))))) e)))))

(define sfix '(λ ()))
;; Generalization (Y as degenerate case)
;; [`(sfix ,q) (comp `(,(comp ,q) '(sfix ,q)))]


;; Meta-lang
(define numeral
  (λ (n) (if (< 0 n) `(,next ,(numeral (sub1 n))) zero)))

(define number
  (λ (e)
    (if (number? e) e (((eval (meval e)) (λ (x) (add1 (number x)))) 0))))

(define addm (λ (i j) (number (meval `((,addo ,(numeral i)) ,(numeral j))))))



;; (define sfix
;;   '(λ (e) ((λ (x) ((meval x) x))
;;            (((λ (x) (λ (y) ((x) (y))))
;;              ((λ (t) (λ (y) (t (((λ (w) (λ (v) ((w) (v)))) y) ((λ (l) (l)) y)))))))
;;             e))))

;; staged adder
(define addo
  `(,Y (λ (f) (λ (n) (λ (m) (((,ifzero n) m) ((f (,prev n)) (,next m))))))))

(define sadd
  `(,sfix
    (□ (λ (s) (λ (n) (((,ifzero n) (,next ,zero)) (,next ((meval s) (,prev n)))))))))








;; All equivalent ??
;;(((eval (comp (if #t '(λ (x) (λ (y) x)) '(λ (x) (λ (y) y))))) 1) 2)
;;(((eval (eval '(comp '(if #t '(λ (x) (λ (y) x)) '(λ (x) (λ (y) y)))))) 1) 2)
;;(((eval (eval (comp ''(if #t '(λ (x) (λ (y) x)) '(λ (x) (λ (y) y)))))) 1) 2)
;;(((eval (comp '(comp (if #t '(λ (x) (λ (y) x)) '(λ (x) (λ (y) y)))))) 1) 2)


;; ((((λ (p)
;;      (λ (x)
;;        (λ (y)
;;          (eval (comp `(if (,p ,x) ,x ,y))))))
;;    (λ (x) x))
;;   #t)
;;  #f)

;; ((((λ (p)
;;      (λ (x)
;;        (λ (y)
;;          (eval (comp `(if (,p ,x) ,x ,y))))))
;;    (λ (x) x))
;;   #f)
;;  #t) ;=> t

;; ((((λ (p)
;;      (λ (x)
;;        (λ (y)
;;          (comp (eval `((,p (λ (z) (,x z))) (λ (z) (,y z))))))))
;;    (λ (x) x))
;;   (λ (x) (λ (y) x)))
;;  (λ (x) (λ (y) y)))

;; ((((λ (p)
;;      (λ (x)
;;        (λ (y)
;;          (comp (eval `((,p ,x) ,x ,y))))))
;;    '(λ (x) x))
;;   ''(λ (x) (λ (y) y)))
;;  ''(λ (x) (λ (y) x)))





;'(((λ (x) (λ (y) x)) (λ (x) x)) (λ (x) (λ (f) (f x))))


;(number (comp `(((dropcc ,zero) (λ (x) x)) ,(numeral 1))))

;(number (comp `(((,ifzero ((dropcc ,(numeral 1)) (λ (x) x))) ,(numeral 0)) ,(numeral 2))))
;(number (comp `((callcc (λ (_) ,zero)) ,(numeral 1))))


;(number (comp `((dropcc ,(numeral 2)) (dropcc ,(numeral 1)))))



;; NOTES

;; want to find the type of \ulcorner (3) \urcorner in (3)
;; use reflection on the syntax-semantics interface as our guide
;; simultaneous use and mention of a sentence corresponds to

;; the type of \ulcorner (3) \urcorner in (3) is the type of a continuation
;; the continuation is just an "incomplete" /token/ - one with a "hole" in it
;; that token is obtained by quotational-reproduction of the complete expression
;; and thus regards self-denotation as akin to /cataphoric reference/
;; Tortoise accepts the reproduction, and asks Achilles to "fill the hole"
;; i.e. invoke the continuation on a /quotation/ of the complete expression

;; Relate:
;; - Curry's paradox
;; - Kleene's second recursion theorem (quines)
;; - Godel's translation of intuitionistic logic into S4



