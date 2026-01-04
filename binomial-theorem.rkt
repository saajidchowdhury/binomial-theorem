#lang racket

;; Lines 27-460 are Proust, a proof assistant written by Prabhakar Ragde, with contribution by Astra Kolomatskaia (August 2020)
;; Lines 464-646 by Saajid Chowdhury, my solutions to MAT250 homework problems given by Astra Kolomatskaia
;; Lines 650-2228 by Saajid Chowdhury, several lemmas and my proof of the binomial theorem, which states:
;; ((exp (plus a b) n) = (sum Z n (λ i => (mult (choose n i) (mult (exp a (sub n i)) (exp b i))))))

(define (pe x) (parse-expr x))
(define (ppe x) (pretty-print-expr x))
(define (d x y) (def x y))
(define (cd) (clear-defs))
(define (co x) (check-one x))
(define (ro x) (reduce-one x))
(define (cp x) (def x) (check-one x))
(define (tc x T) (type-check empty x T))
(define (ts x) (type-synth empty x))
(define (pphelper deftypes)
  (cond
    [(empty? deftypes) ""]
    [else (format "~a~n~n~a"
          (format "~a : ~a"
          (ppe (first (first deftypes)))
          (ppe (second (first deftypes))))
          (pphelper (rest deftypes)))]))
(define (ppdt) (printf (pphelper deftypes)))

(struct Lam (var body) #:transparent)
(struct App (rator rand) #:transparent)
(struct Ann (expr type) #:transparent)
(struct Arrow (var domain range) #:transparent)
(struct Type () #:transparent)
(struct Teq (left right) #:transparent)
(struct Eq-refl (val) #:transparent)
(struct Eq-elim (x P px y peq) #:transparent)
(struct True () #:transparent)
(struct False () #:transparent)
(struct Bool-ind (P tp fp b) #:transparent)
(struct Bool () #:transparent)
(struct Z () #:transparent)
(struct S (k) #:transparent)
(struct Nat-ind (expr1 expr2 expr3 expr4) #:transparent)
(struct Nat () #:transparent)
(struct Exists (var domain range) #:transparent)
(struct Exists-intro (e1 e2) #:transparent)
(struct Exists-elim (e1 e2) #:transparent)

(define (parse-expr s)
  (match s
    [`(λ ,(? symbol? x) => ,e) (Lam x (parse-expr e))]
    [`(∀ (,(? symbol? x) : ,t) -> ,e) (Arrow x (parse-expr t) (parse-expr e))]
    [`(∀ (,(? symbol? x) : ,t) ,(? list? a) ... -> ,e) (Arrow x (parse-expr t) (parse-expr `(∀ ,@a -> ,e)))]
    [`(,t1 -> ,t2) (Arrow '_ (parse-expr t1) (parse-expr t2))]
    [`(,t1 -> ,t2 -> ,r ...) (Arrow '_ (parse-expr t1) (parse-expr `(,t2 -> ,@r)))]
    [`(,e : ,t) (Ann (parse-expr e) (parse-expr t))]
    ['Type (Type)]
    [`(eq-refl ,a) (Eq-refl (parse-expr a))]
    [`(eq-elim ,t1 ,t2 ,t3 ,t4 ,t5)
     (Eq-elim (parse-expr t1) (parse-expr t2) (parse-expr t3) (parse-expr t4) (parse-expr t5))]
    [`(,t1 = ,t2) (Teq (parse-expr t1) (parse-expr t2))]
    ['true (True)]
    ['false (False)]
    [`(bool-ind ,t1 ,t2 ,t3 ,t4)
     (Bool-ind (parse-expr t1) (parse-expr t2) (parse-expr t3) (parse-expr t4))]
    ['Bool (Bool)]
    ['Z (Z)]
    [`(S ,k) (S (parse-expr k))]
    [`(nat-ind ,t1 ,t2 ,t3 ,t4) (Nat-ind (parse-expr t1) (parse-expr t2) (parse-expr t3) (parse-expr t4))]
    ['Nat (Nat)]
    [`(∃ (,(? symbol? x) : ,t) -> ,e) (Exists x (parse-expr t) (parse-expr e))]
    [`(∃ (,(? symbol? x) : ,t) ,(? list? a) ... -> ,e) (Exists x (parse-expr t) (parse-expr `(∃ ,@a -> ,e)))]
    [`(∃-intro ,e1 ,e2) (Exists-intro (parse-expr e1) (parse-expr e2))]
    [`(∃-elim ,e1 ,e2) (Exists-elim (parse-expr e1) (parse-expr e2))]
    [`(,e1 ,e2) (App (parse-expr e1) (parse-expr e2))]
    [`(,e1 ,e2 ,e3 ,r ...) (parse-expr `((,e1 ,e2) ,e3 ,@r))]
    ['_ (error 'parse "cannot use underscore\n")]
    [(? symbol? x) x]
    [else (error 'parse "bad syntax: ~a\n" s)]))

(define (pretty-print-expr e)
  (match e
    [(Lam x b) (format "(λ ~a => ~a)" x (pretty-print-expr b))]
    [(App e1 e2) (format "(~a ~a)" (pretty-print-expr e1) (pretty-print-expr e2))]
    [(? symbol? x) (symbol->string x)]
    [(Ann e t) (format "(~a : ~a)" (pretty-print-expr e) (pretty-print-expr t))]
    [(Arrow '_ t1 t2) (format "(~a -> ~a)" (pretty-print-expr t1) (pretty-print-expr t2))]
    [(Arrow x t1 t2) (format "(∀ (~a : ~a) -> ~a)" x (pretty-print-expr t1) (pretty-print-expr t2))]
    [(Type) "Type"]
    [(Eq-refl a) (format "(eq-refl ~a)" (pretty-print-expr a))]
    [(Eq-elim e1 e2 e3 e4 e5)
     (format "(eq-elim ~a ~a ~a ~a ~a)" (pretty-print-expr e1) (pretty-print-expr e2)
             (pretty-print-expr e3) (pretty-print-expr e4) (pretty-print-expr e5))]
    [(Teq t1 t2) (format "(~a = ~a)" (pretty-print-expr t1) (pretty-print-expr t2))]
    [(True) "true"]
    [(False) "false"]
    [(Bool-ind t1 t2 t3 t4)
     (format "(bool-ind ~a ~a ~a ~a)"
             (pretty-print-expr t1) (pretty-print-expr t2) (pretty-print-expr t3) (pretty-print-expr t4))]
    [(Bool) "Bool"]
    [(Z) "Z"]
    [(S k) (format "(S ~a)" (pretty-print-expr k))]
    [(Nat-ind t1 t2 t3 t4) (format "(nat-ind ~a ~a ~a ~a)" (pretty-print-expr t1) (pretty-print-expr t2) (pretty-print-expr t3) (pretty-print-expr t4))]
    [(Nat) "Nat"]
    [(Exists x t1 t2) (format "(∃ (~a : ~a) -> ~a)" x (pretty-print-expr t1) (pretty-print-expr t2))]
    [(Exists-intro e1 e2) (format "(∃-intro ~a ~a)" (pretty-print-expr e1) (pretty-print-expr e2))]
    [(Exists-elim e1 e2) (format "(∃-elim ~a ~a)" (pretty-print-expr e1) (pretty-print-expr e2))]
    ))

(define (pretty-print-context ctx)
  (cond
    [(empty? ctx) ""]
    [else (string-append (format "\n~a : ~a" (first (first ctx)) (pretty-print-expr (second (first ctx))))
                         (pretty-print-context (rest ctx)))]))

(define (subst oldx newx expr)
  (match expr
    [(? symbol? x) (if (equal? x oldx) newx x)]
    [(Arrow '_ t w) (Arrow '_ (subst oldx newx t) (subst oldx newx w))]
    [(Arrow x t w)
       (cond
         [(equal? x oldx) expr]
         [(var-used? x (list newx) false)
            (define repx (refresh x (list newx w)))
            (Arrow repx (subst oldx newx t) (subst oldx newx (subst x repx w)))]
         [else (Arrow x (subst oldx newx t) (subst oldx newx w))])]
    [(Lam '_ b) (Lam '_ (subst oldx newx b))]
    [(Lam x b)
       (cond
         [(equal? x oldx) expr]
         [(var-used? x (list newx) false)
            (define repx (refresh x (list newx b)))
            (Lam repx (subst oldx newx (subst x repx b)))]
         [else (Lam x (subst oldx newx b))])]
    [(App f a) (App (subst oldx newx f) (subst oldx newx a))]
    [(Ann e t) (Ann (subst oldx newx e) (subst oldx newx t))]
    [(Type) (Type)]
    [(Eq-refl a) (Eq-refl (subst oldx newx a))]
    [(Eq-elim e1 e2 e3 e4 e5)
      (Eq-elim (subst oldx newx e1) (subst oldx newx e2) (subst oldx newx e3)
               (subst oldx newx e4) (subst oldx newx e5))]
    [(Teq a b) (Teq (subst oldx newx a) (subst oldx newx b))]
    [(True) (True)]
    [(False) (False)]
    [(Bool-ind t1 t2 t3 t4)
       (Bool-ind (subst oldx newx t1) (subst oldx newx t2) (subst oldx newx t3) (subst oldx newx t4))]
    [(Bool) (Bool)]
    [(Z) (Z)]
    [(S k) (S (subst oldx newx k))]
    [(Nat-ind t1 t2 t3 t4)
       (Nat-ind (subst oldx newx t1) (subst oldx newx t2) (subst oldx newx t3) (subst oldx newx t4))
       ]
    [(Nat) (Nat)]
    [(Exists x t w)
       (cond
         [(equal? x oldx) expr]
         [(var-used? x (list newx) false)
            (define repx (refresh x (list newx w)))
            (Exists repx (subst oldx newx t) (subst oldx newx (subst x repx w)))]
         [else (Exists x (subst oldx newx t) (subst oldx newx w))])]
    [(Exists-intro e1 e2) (Exists-intro (subst oldx newx e1) (subst oldx newx e2))]
    [(Exists-elim e1 e2) (Exists-intro (subst oldx newx e1) (subst oldx newx e2))]))

(define (refresh x lst)
  (if (var-used? x lst true) (refresh (freshen x) lst) x))

(define (freshen x) (string->symbol (string-append (symbol->string x) "_")))

(define (var-used? x lst check-binders?)
  (ormap (lambda (expr) (vu-helper x expr check-binders?)) lst))

(define (vu-helper x expr check-binders?)
  (match expr
    [(? symbol? y) (equal? x y)]
    [(Arrow '_ tt tw) (var-used? x (list tt tw) check-binders?)]
    [(Arrow y tt tw)
       (cond
         [check-binders? (or (equal? x y) (var-used? x (list tt tw) check-binders?))]
         [else (if (equal? x y) false (var-used? x (list tt tw) check-binders?))])]
    [(Lam '_ b) (vu-helper x b check-binders?)]
    [(Lam y b)
       (cond
         [check-binders? (or (equal? x y) (vu-helper x b check-binders?))]
         [else (if (equal? x y) false (vu-helper x b check-binders?))])]
    [(App f a) (var-used? x (list f a) check-binders?)]
    [(Ann e t) (var-used? x (list e t) check-binders?)]
    [(Type) false]
    [(Eq-refl a) (vu-helper x a check-binders?)] 
    [(Eq-elim e1 e2 e3 e4 e5)
      (var-used? x (list e1 e2 e3 e4 e5) check-binders?)]
    [(Teq a b) (var-used? x (list a b) check-binders?)]
    [(True) false]
    [(False) false]
    [(Bool-ind t1 t2 t3 t4)
       (var-used? x (list t1 t2 t3 t4) check-binders?)]
    [(Bool) false]
    [(Z) false]
    [(S k) (vu-helper x k check-binders?)]
    [(Nat-ind t1 t2 t3 t4)
       (var-used? x (list t1 t2 t3 t4) check-binders?)]
    [(Nat) false]
    [(Exists y tt tw)
       (cond
         [check-binders? (or (equal? x y) (var-used? x (list tt tw) check-binders?))]
         [else (if (equal? x y) false (var-used? x (list tt tw) check-binders?))])]
    [(Exists-intro e1 e2) (var-used? x (list e1 e2) check-binders?)]
    [(Exists-elim e1 e2) (var-used? x (list e1 e2) check-binders?)]
    ))

(define (dependency-conflict? ctx x)
  (or (assoc x deftypes) (ormap (λ (p) (var-used? x (rest p) false)) ctx)))

(define (refresh-with-env ctx x lst)
  (if (or (var-used? x lst true) (dependency-conflict? ctx x)) (refresh-with-env ctx (freshen x) lst) x))

(define (alpha-equiv? e1 e2) (ae-helper e1 e2 empty))

(define (ae-helper e1 e2 vmap)
  (match (list e1 e2)
    [(list (? symbol? x1) (? symbol? x2))
       (define xm1 (assoc x1 vmap))
       (equal? (if xm1 (second xm1) x1) x2)]
    [(list (Lam x1 b1) (Lam x2 b2)) (ae-helper b1 b2 (cons (list x1 x2) vmap))]
    [(list (App f1 a1) (App f2 a2)) (and (ae-helper f1 f2 vmap) (ae-helper a1 a2 vmap))]
    [(list (Ann e1 t1) (Ann e2 t2)) (and (ae-helper e1 e2 vmap) (ae-helper t1 t2 vmap))]
    [(list (Arrow x1 t1 w1) (Arrow x2 t2 w2))
       (and (ae-helper t1 t2 (cons (list x1 x2) vmap)) (ae-helper w1 w2 (cons (list x1 x2) vmap)))]
    [(list (Type) (Type)) true]
    [(list (Eq-refl x1) (Eq-refl x2)) (ae-helper x1 x2 vmap)]
    [(list (Eq-elim x1 P1 px1 y1 peq1) (Eq-elim x2 P2 px2 y2 peq2))
       (and (ae-helper x1 x2 vmap) (ae-helper P1 P2 vmap) (ae-helper px1 px2 vmap)
            (ae-helper y1 y2 vmap) (ae-helper peq1 peq2 vmap))]
    [(list (Teq a1 b1) (Teq a2 b2))
       (and (ae-helper a1 a2 vmap) (ae-helper b1 b2 vmap))]
    [(list (True) (True)) true]
    [(list (False) (False)) true]
    [(list (Bool-ind t11 t12 t13 t14) (Bool-ind t21 t22 t23 t24))
       (and (ae-helper t11 t21 vmap) (ae-helper t12 t22 vmap) (ae-helper t13 t23 vmap) (ae-helper t14 t24 vmap))]
    [(list (Bool) (Bool)) true]
    [(list (Z) (Z)) true]
    [(list (S a) (S b)) (ae-helper a b vmap)]
    [(list (Nat-ind t11 t12 t13 t14) (Nat-ind t21 t22 t23 t24))
       (and (ae-helper t11 t21 vmap) (ae-helper t12 t22 vmap) (ae-helper t13 t23 vmap) (ae-helper t14 t24 vmap))]
    [(list (Nat) (Nat)) true]
    [(list (Exists a1 b1 c1) (Exists a2 b2 c2)) (and (ae-helper b1 b2 (cons (list a1 a2) vmap)) (ae-helper c1 c2 (cons (list a1 a2) vmap)))]
    [(list (Exists-intro a1 b1) (Exists-intro a2 b2)) (and (ae-helper a1 a2 vmap) (ae-helper b1 b2 vmap))]
    [(list (Exists-elim a1 b1) (Exists-elim a2 b2)) (and (ae-helper a1 a2 vmap) (ae-helper b1 b2 vmap))]
    [else false]))

(define (weak-reduce ctx expr)
  (match expr
    [(? symbol? x)
       (cond
         [(assoc x ctx) x]
         [(assoc x defs) => (lambda (p) (weak-reduce ctx (second p)))]
         [else x])]
    [(App f a) 
       (define fr (weak-reduce ctx f))
       (match fr
         [(Lam '_ b) (weak-reduce ctx b)]
         [(Lam x b) (weak-reduce ctx (subst x a b))]
         [else (App fr a)])]
    [else expr]))

(define (strong-reduce ctx expr)
  (match expr
    [(? symbol? x)
        (cond
         [(assoc x ctx) x]
         [(assoc x defs) => (lambda (p) (strong-reduce ctx (second p)))]
         [else x])]
    [(Arrow '_ a b)
       (Arrow '_ (strong-reduce ctx a) (strong-reduce ctx b))]
    [(Arrow x a b)
       (define ra (strong-reduce ctx a))
       (define rb (strong-reduce (cons (list x ra) ctx) b))
       (Arrow x ra rb)]
    [(Lam '_ b) (Lam '_ (strong-reduce ctx b))]
    [(Lam x b) (Lam x (strong-reduce (cons (list x '()) ctx) b))]
    [(App f a)
       (define fr (strong-reduce ctx f))
       (define fa (strong-reduce ctx a))
       (match fr
         [(Lam x b) (strong-reduce ctx (subst x fa b))]
         [else (App fr fa)])]
    [(Ann e t) (strong-reduce ctx e)]
    [(Type) (Type)]
    [(Eq-refl x) (Eq-refl (strong-reduce ctx x))]
    [(Eq-elim x P px y peq)
       (define peqr (strong-reduce ctx peq))
       (match peqr
         [(Eq-refl _) (strong-reduce ctx px)]
         [else (Eq-elim (strong-reduce ctx x) (strong-reduce ctx P) (strong-reduce ctx px) (strong-reduce ctx y) peqr)])]
    [(Teq a b) (Teq (strong-reduce ctx a) (strong-reduce ctx b))]
    [(True) (True)]
    [(False) (False)]
    [(Bool-ind P tp fp b)
       (define br (strong-reduce ctx b))
       (match br
         [(True) (strong-reduce ctx tp)]
         [(False) (strong-reduce ctx fp)]
         [else (Bool-ind (strong-reduce ctx P) (strong-reduce ctx tp) (strong-reduce ctx fp) br)])]
    [(Bool) (Bool)]
    [(Z) (Z)]
    [(S k) (S (strong-reduce ctx k))]
    [(Nat-ind P zp sp n)
       (define nr (strong-reduce ctx n))
       (match nr
         [(Z) (strong-reduce ctx zp)]
         [(S k) (strong-reduce ctx (App (App (strong-reduce ctx sp) (strong-reduce ctx k))
                                        (Nat-ind (strong-reduce ctx P) (strong-reduce ctx zp) (strong-reduce ctx sp) (strong-reduce ctx k))))]
         [else (Nat-ind (strong-reduce ctx P) (strong-reduce ctx zp) (strong-reduce ctx sp) nr)])]
    [(Nat) (Nat)]
    [(Exists x e1 e2)
       (define re1 (strong-reduce ctx e1))
       (define re2 (strong-reduce (cons (list x re1) ctx) e2))
       (Exists x re1 re2)]
    [(Exists-intro e1 e2) (Exists-intro (strong-reduce ctx e1) (strong-reduce ctx e2))]
    [(Exists-elim e1 e2) (Exists-elim (strong-reduce ctx e1) (strong-reduce ctx e2))]))

(define (equiv? ctx e1 e2) (alpha-equiv? (strong-reduce ctx e1) (strong-reduce ctx e2)))

(define (type-check ctx expr type)
  (match expr
    [(Lam x b)
       (type-check ctx type (Type))
       (define tyr (weak-reduce ctx type))
       (match tyr
         [(Arrow x1 tt tw)
            (match (list x x1)
              [(list '_ '_) (type-check ctx b tw)]
              [(list '_ x1)
                 (cond
                   [(nor (var-used? x1 (list b) false) (dependency-conflict? ctx x1))
                      (type-check (cons (list x1 tt) ctx) b tw)]
                   [else
                      (define newx (refresh-with-env ctx x1 (list b tyr)))
                      (type-check (cons (list newx tt) ctx) b (subst x1 newx tw))])]
              [(list x '_)
                 (cond
                   [(nor (var-used? x (list tyr) false) (dependency-conflict? ctx x1))
                      (type-check (cons (list x tt) ctx) b tw)]
                   [else
                      (define newx (refresh-with-env ctx x (list b tyr)))
                      (type-check (cons (list newx tt) ctx) (subst x newx b) tw)])]
              [(list x x1)
                 (cond
                   [(and (equal? x x1) (not (dependency-conflict? ctx x1))) (type-check (cons (list x tt) ctx) b tw)]
                   [(nor (var-used? x (list tyr) true) (dependency-conflict? ctx x))
                      (type-check (cons (list x tt) ctx) b (subst x1 x tw))]
                   [else
                      (define newx (refresh-with-env ctx x (list expr tyr)))
                      (type-check (cons (list newx tt) ctx) (subst x newx b) (subst x1 newx tw))])])]
         [else (cannot-check ctx expr type)])]
    [(Exists-intro a p)
       (type-check ctx type (Type))
       (define tyr (weak-reduce ctx type))
       (match tyr
         [(Exists X T W)
          (type-check ctx a T)
          (type-check ctx p (subst X a W))]
         [else (cannot-check ctx expr type)])]
    [(Exists-elim f e)
       (define s (weak-reduce ctx (type-synth ctx e)))
       (match s
         [(Exists X T W)
          (type-check ctx f (Arrow X T (Arrow '_ W type)))]
         [else (cannot-check ctx expr type)])]
    [else (if (equiv? ctx (type-synth ctx expr) type) true (cannot-check ctx expr type))]))

(define (cannot-check ctx e t)
  (error 'type-check "cannot typecheck ~a as ~a in context:\n~a"
         (pretty-print-expr e) (pretty-print-expr t) (pretty-print-context ctx)))

(define (type-synth ctx expr)
  (match expr
    [(? symbol? x)
       (cond
         [(assoc x ctx) => second]
         [(assoc x deftypes) => second]
         [else (cannot-synth ctx expr)])]
    [(Lam x b) (cannot-synth ctx expr)]
    [(App f a) 
       (define t1 (weak-reduce ctx (type-synth ctx f)))
       (match t1
         [(Arrow '_ tt tw) #:when (type-check ctx a tt) tw]
         [(Arrow x tt tw) #:when (type-check ctx a tt) (subst x a tw)]
         [else (cannot-synth ctx expr)])]
    [(Ann e t) (type-check ctx t (Type)) (type-check ctx e t) t]
    [(Arrow '_ tt tw)
       (type-check ctx tt (Type))
       (type-check ctx tw (Type))
       (Type)]
    [(Arrow x tt tw)
       (type-check ctx tt (Type))
       (type-check (cons `(,x ,tt) ctx) tw (Type))
       (Type)]
    [(Type) (Type)]
    [(Teq e1 e2)
       (define t1 (type-synth ctx e1))
       (type-check ctx e2 t1)
       (Type)]
    [(Eq-refl x) (type-synth ctx x) (Teq x x)]
    [(Eq-elim x P px y peq) 
       (define A (type-synth ctx x))
       (type-check ctx P (Arrow '_ A (Type)))
       (define Pann (Ann P (Arrow '_ A (Type))))
       (type-check ctx px (App Pann x))
       (type-check ctx y A)
       (type-check ctx peq (Teq x y))
       (App Pann y)]
    [(True) (Bool)]
    [(False) (Bool)]
    [(Bool-ind P tp fp b)
       (type-check ctx P (Arrow '_ (Bool) (Type)))
       (define Pann (Ann P (Arrow '_ (Bool) (Type))))
       (type-check ctx tp (App Pann (True)))
       (type-check ctx fp (App Pann (False)))
       (type-check ctx b (Bool))
       (App Pann b)]
    [(Bool) (Type)]
    [(Z) (Nat)]
    [(S k) #:when (type-check ctx k (Nat)) (Nat)]
    [(Nat-ind P zp sp n)
       (type-check ctx P (Arrow '_ (Nat) (Type)))
       (define Pann (Ann P (Arrow '_ (Nat) (Type))))
       (type-check ctx zp (App Pann (Z)))
       (type-check ctx sp (Arrow 'k (Nat) (Arrow '_ (App Pann 'k) (App Pann (S 'k)))))
       (type-check ctx n (Nat))
       (App Pann n)]
    [(Nat) (Type)]
    [(Exists X T W)
       (type-check ctx T (Type))
       (type-check (cons (list X T) ctx) W (Type))
       (Type)]
    [else (cannot-synth ctx expr)]
    ))

(define (cannot-synth ctx expr)
  (error 'type-synth "cannot infer type of ~a in context:\n~a"
         (pretty-print-expr expr) (pretty-print-context ctx)))

(define defs empty)
(define deftypes empty)

(define (def name expr)
  (when (assoc name defs) (error 'def "~a already defined" name))
  (define e (parse-expr expr))
  (define et (type-synth empty e))
  (match e
    [(Ann ex tp) (set! defs (cons (list name ex) defs))
                 (set! deftypes (cons (list name tp) deftypes))]
    [else (set! defs (cons (list name e) defs))
          (set! deftypes (cons (list name et) deftypes))]))

(define (clear-defs) (set! defs empty) (set! deftypes empty))

(define (check-one expr)
  (printf "~a\n" (pretty-print-expr (type-synth empty (parse-expr expr)))))

(define (reduce-one expr)
   (printf "~a\n" (pretty-print-expr (strong-reduce empty (parse-expr expr)))))



(def 'eq-symm '((λ A => (λ x => (λ y => (λ z =>
                  (eq-elim x (λ a => (a = x)) (eq-refl x) y z)))))

                : (∀ (A : Type) (x : A) (y : A) -> ((x = y) -> (y = x)))))



(def 'eq-trans '((λ A => (λ x => (λ y => (λ z => (λ e1 => (λ e2 =>
                   (eq-elim y (λ a => (a = z)) e2 x (eq-symm A x y e1))))))))

                 : (∀ (A : Type) (x : A) (y : A) (z : A) -> ((x = y) -> (y = z) -> (x = z)))))



(def 'cong '((λ A => (λ B => (λ x => (λ y => (λ f => (λ e =>
               (eq-elim x (λ a => ((f x) = (f a))) (eq-refl (f x)) y e)))))))

             : (∀ (A : Type) (B : Type) (x : A) (y : A) (f : (A -> B)) -> ((x = y) -> ((f x) = (f y))))))



(def 'plus '((λ n => (λ m =>
               (nat-ind
                (λ x => Nat)
                n
                (λ k => (λ pk =>
                  (S pk)))
                m)))

             : (Nat -> Nat -> Nat)))



(def 'plus-zero-left '((λ n =>
                         (nat-ind
                          (λ x => ((plus Z x) = x))
                          (eq-refl Z)
                          (λ k => (λ pk =>
                            (cong Nat Nat (plus Z k) k (λ x => (S x)) pk)))
                          n))

                       : (∀ (n : Nat) -> ((plus Z n) = n))))



(def 'plus-lemma '((λ a => (λ b =>
                     (nat-ind
                      (λ x => ((plus (S a) x) = (S (plus a x))))
                      (eq-trans Nat (plus (S a) Z) (S a) (S (plus a Z))
                                (eq-refl (S a))
                                (cong Nat Nat a (plus a Z) (λ x => (S x)) (eq-refl a)))
                      (λ k => (λ pk =>
                        (eq-trans Nat (plus (S a) (S k)) (S (plus (S a) k)) (S (plus a (S k)))
                                  (eq-refl (S (plus (S a) k)))
                        (eq-trans Nat (S (plus (S a) k)) (S (S (plus a k))) (S (plus a (S k)))
                                  (cong Nat Nat (plus (S a) k) (S (plus a k)) (λ x => (S x)) pk)
                        (cong Nat Nat (S (plus a k)) (plus a (S k)) (λ x => (S x))
                                  (eq-symm Nat (plus a (S k)) (S (plus a k)) (eq-refl (S (plus a k)))))))))
                        b)))

              : (∀ (a : Nat) (b : Nat) -> ((plus (S a) b) = (S (plus a b))))))



(def 'plus-comm '((λ n => (λ m =>
                    (nat-ind
                     (λ x => ((plus n x) = (plus x n)))
                     (eq-trans Nat (plus n Z) n (plus Z n)
                               (eq-refl n)
                               (eq-symm Nat (plus Z n) n (plus-zero-left n)))
                     (λ k => (λ pk =>
                       (eq-trans Nat (plus n (S k)) (S (plus n k)) (plus (S k) n)
                                 (eq-refl (S (plus n k)))
                       (eq-trans Nat (S (plus n k)) (S (plus k n)) (plus (S k) n)
                                 (cong Nat Nat (plus n k) (plus k n) (λ x => (S x)) pk)
                       (eq-symm Nat (plus (S k) n) (S (plus k n)) (plus-lemma k n))))))
                     m)))

                  : (∀ (n : Nat) (m : Nat) -> ((plus n m) = (plus m n)))))



(def 'sub1 '((λ n =>
               (nat-ind
                (λ x => Nat)
                Z
                (λ k => (λ pk =>
                  k))
                n))

             : (Nat -> Nat)))



(def 'sub '((λ n => (λ m =>
              (nat-ind
               (λ x => Nat)
               n
               (λ k => (λ pk =>
                 (sub1 pk)))
               m)))

            : (Nat -> Nat -> Nat)))



(def 'leq '((λ n => (λ m =>
              ((sub n m) = Z)))

            : (Nat -> Nat -> Type)))



(def 'subS '((λ n => (λ m =>
               (nat-ind
                (λ x => ((sub (S n) (S x)) = (sub n x)))
                (eq-trans Nat (sub (S n) (S Z)) (sub1 (sub (S n) Z)) (sub n Z)
                          (eq-refl (sub1 (sub (S n) Z)))
                (eq-refl n))
                (λ k => (λ pk =>
                  (eq-trans Nat (sub (S n) (S (S k))) (sub1 (sub (S n) (S k))) (sub n (S k))
                            (eq-refl (sub1 (sub (S n) (S k))))
                  (eq-trans Nat (sub1 (sub (S n) (S k))) (sub1 (sub n k)) (sub n (S k))
                            (cong Nat Nat (sub (S n) (S k)) (sub n k) (λ x => (sub1 x)) pk)
                  (eq-refl (sub n (S k)))))))
                m)))

             : (∀ (n : Nat) (m : Nat) -> ((sub (S n) (S m)) = (sub n m)))))



(def 'leqZ '((λ n =>
               (nat-ind
                (λ x => (leq Z x))
                (eq-refl Z)
                (λ k => (λ pk =>
                  (eq-trans Nat (sub Z (S k)) (sub1 (sub Z k)) Z
                            (eq-refl (sub1 (sub Z k)))
                  (eq-trans Nat (sub1 (sub Z k)) (sub1 Z) Z
                            (cong Nat Nat (sub Z k) Z (λ x => (sub1 x)) pk)
                  (eq-refl Z)))))
                n))

             : (∀ (n : Nat) -> (leq Z n))))



(def 'leq-refl '((λ n =>
                   (nat-ind
                    (λ x => (leq x x))
                    (eq-refl Z)
                    (λ k => (λ pk =>
                      (eq-trans Nat (sub (S k) (S k)) (sub k k) Z
                                (subS k k)
                      pk)))
                    n))

                 : (∀ (n : Nat) -> (leq n n))))



(def 'nat-ind-strong '((λ P => (λ pz => (λ I => (λ n =>
                         (((nat-ind
                            (λ x => (∀ (m : Nat) -> ((leq m x) -> (P m))))
                            ((λ m =>
                               (nat-ind
                                (λ x => ((leq x Z) -> (P x)))
                                ((λ l => pz) : ((leq Z Z) -> (P Z)))
                                (λ k => (λ pk => ((λ lsz =>
                                  (eq-elim Z (λ x => (P x)) pz (S k)
                                           (eq-trans Nat Z (sub (S k) Z) (S k)
                                                     (eq-symm Nat (sub (S k) Z) Z lsz)
                                           (eq-refl (S k))))) : ((leq (S k) Z) -> (P (S k))))))
                                m)) : (∀ (m : Nat) -> ((leq m Z) -> (P m))))
                            (λ k => (λ pk => (I k pk)))
                            n) : (∀ (m : Nat) -> ((leq m n) -> (P m))))
                          n (leq-refl n))))))

                       : (∀ (P : (Nat -> Type)) ->
                            ((P Z) ->
                            (∀ (k : Nat) -> ((∀ (m : Nat) -> ((leq m k) -> (P m))) ->
                                             (∀ (m : Nat) -> ((leq m (S k)) -> (P m))))) ->
                            (∀ (n : Nat) -> (P n))))))



(def 'plus-assoc '((λ a => (λ b => (λ c =>
                     (nat-ind
                      (λ x => ((plus a (plus b x)) = (plus (plus a b) x)))
                      (eq-trans Nat (plus a (plus b Z)) (plus a b) (plus (plus a b) Z)
                                (cong Nat Nat (plus b Z) b (λ x => (plus a x)) (eq-refl b))
                      (eq-refl (plus a b)))
                      (λ k => (λ pk =>
                        (eq-trans Nat (plus a (plus b (S k))) (plus a (S (plus b k))) (plus (plus a b) (S k))
                                  (cong Nat Nat (plus b (S k)) (S (plus b k)) (λ x => (plus a x)) (eq-refl (S (plus b k))))
                        (eq-trans Nat (plus a (S (plus b k))) (S (plus a (plus b k))) (plus (plus a b) (S k))
                                  (eq-refl (S (plus a (plus b k))))
                        (eq-trans Nat (S (plus a (plus b k))) (S (plus (plus a b) k)) (plus (plus a b) (S k))
                                  (cong Nat Nat (plus a (plus b k)) (plus (plus a b) k) (λ x => (S x)) pk)
                        (eq-refl (S (plus (plus a b) k))))))))
                      c))))

                   : (∀ (a : Nat) (b : Nat) (c : Nat) -> ((plus a (plus b c)) = (plus (plus a b) c)))))



(def 'plus-exchange '((λ a => (λ b => (λ c => (λ d =>
                        (eq-trans Nat (plus (plus a b) (plus c d)) (plus a (plus b (plus c d))) (plus (plus a c) (plus b d))
                                  (eq-symm Nat (plus a (plus b (plus c d))) (plus (plus a b) (plus c d)) (plus-assoc a b (plus c d)))
                        (eq-trans Nat (plus a (plus b (plus c d))) (plus a (plus (plus b c) d)) (plus (plus a c) (plus b d))
                                  (cong Nat Nat (plus b (plus c d)) (plus (plus b c) d) (λ x => (plus a x)) (plus-assoc b c d))
                        (eq-trans Nat (plus a (plus (plus b c) d)) (plus a (plus (plus c b) d)) (plus (plus a c) (plus b d))
                                  (cong Nat Nat (plus b c) (plus c b) (λ x => (plus a (plus x d))) (plus-comm b c))
                        (eq-trans Nat (plus a (plus (plus c b) d)) (plus a (plus c (plus b d))) (plus (plus a c) (plus b d))
                                  (cong Nat Nat (plus (plus c b) d) (plus c (plus b d)) (λ x => (plus a x))
                                        (eq-symm Nat (plus c (plus b d)) (plus (plus c b) d) (plus-assoc c b d)))
                        (plus-assoc a c (plus b d))))))))))

                      : (∀ (a : Nat) (b : Nat) (c : Nat) (d : Nat) -> ((plus (plus a b) (plus c d)) = (plus (plus a c) (plus b d))))))



(def 'mult '((λ n => (λ m =>
               (nat-ind
                (λ x => Nat)
                Z
                (λ k => (λ pk =>
                  (plus n pk)))
                m)))

             : (Nat -> Nat -> Nat)))



(def 'mult-zero-left '((λ n =>
                         (nat-ind
                          (λ x => ((mult Z x) = Z))
                          (eq-refl Z)
                          (λ k => (λ pk =>
                            (eq-trans Nat (mult Z (S k)) (plus Z (mult Z k)) Z
                                      (eq-refl (plus Z (mult Z k)))
                            (eq-trans Nat (plus Z (mult Z k)) (plus Z Z) Z
                                      (cong Nat Nat (mult Z k) Z (λ x => (plus Z x)) pk)
                            (eq-refl Z)))))
                          n))

                       : (∀ (n : Nat) -> ((mult Z n) = Z))))



(def 'mult-lemma '((λ a => (λ b =>
                     (nat-ind
                      (λ x => ((mult (S a) x) = (plus x (mult a x))))
                      (eq-refl Z)
                      (λ k => (λ pk =>
                        (eq-trans Nat (mult (S a) (S k)) (plus (S a) (mult (S a) k)) (plus (S k) (mult a (S k)))
                                  (eq-refl (plus (S a) (mult (S a) k)))
                        (eq-trans Nat (plus (S a) (mult (S a) k)) (plus (S a) (plus k (mult a k))) (plus (S k) (mult a (S k)))
                                  (cong Nat Nat (mult (S a) k) (plus k (mult a k)) (λ x => (plus (S a) x)) pk)
                        (eq-trans Nat (plus (S a) (plus k (mult a k))) (plus (plus (S a) k) (mult a k)) (plus (S k) (mult a (S k)))
                                  (plus-assoc (S a) k (mult a k))
                        (eq-trans Nat (plus (plus (S a) k) (mult a k)) (plus (S (plus a k)) (mult a k)) (plus (S k) (mult a (S k)))
                                  (cong Nat Nat (plus (S a) k) (S (plus a k)) (λ x => (plus x (mult a k))) (plus-lemma a k))
                        (eq-trans Nat (plus (S (plus a k)) (mult a k)) (plus (plus a (S k)) (mult a k)) (plus (S k) (mult a (S k)))
                                  (cong Nat Nat (S (plus a k)) (plus a (S k)) (λ x => (plus x (mult a k))) (eq-refl (S (plus a k))))
                        (eq-trans Nat (plus (plus a (S k)) (mult a k)) (plus (plus (S k) a) (mult a k)) (plus (S k) (mult a (S k)))
                                  (cong Nat Nat (plus a (S k)) (plus (S k) a) (λ x => (plus x (mult a k))) (plus-comm a (S k)))
                        (eq-trans Nat (plus (plus (S k) a) (mult a k)) (plus (S k) (plus a (mult a k))) (plus (S k) (mult a (S k)))
                                  (eq-symm Nat (plus (S k) (plus a (mult a k))) (plus (plus (S k) a) (mult a k)) (plus-assoc (S k) a (mult a k)))
                        (cong Nat Nat (plus a (mult a k)) (mult a (S k)) (λ x => (plus (S k) x)) (eq-refl (plus a (mult a k)))))))))))))
                      b)))

                   : (∀ (a : Nat) (b : Nat) -> ((mult (S a) b) = (plus b (mult a b))))))



(def 'mult-comm '((λ n => (λ m =>
                    (nat-ind
                     (λ x => ((mult n x) = (mult x n)))
                     (eq-trans Nat (mult n Z) Z (mult Z n)
                               (eq-refl Z)
                     (eq-symm Nat (mult Z n) Z (mult-zero-left n)))
                     (λ k => (λ pk =>
                       (eq-trans Nat (mult n (S k)) (plus n (mult n k)) (mult (S k) n)
                                 (eq-refl (plus n (mult n k)))
                       (eq-trans Nat (plus n (mult n k)) (plus n (mult k n)) (mult (S k) n)
                                 (cong Nat Nat (mult n k) (mult k n) (λ x => (plus n x)) pk)
                       (eq-symm Nat (mult (S k) n) (plus n (mult k n))
                                (mult-lemma k n))))))
                     m)))

                  : (∀ (n : Nat) (m : Nat) -> ((mult n m) = (mult m n)))))



(def 'mult-left-dist '((λ a => (λ b => (λ c =>
                         (nat-ind
                          (λ x => ((mult a (plus b x)) = (plus (mult a b) (mult a x))))
                          (eq-trans Nat (mult a (plus b Z)) (mult a b) (plus (mult a b) (mult a Z))
                                    (cong Nat Nat (plus b Z) b (λ x => (mult a x)) (eq-refl b))
                          (eq-trans Nat (mult a b) (plus (mult a b) Z) (plus (mult a b) (mult a Z))
                                    (eq-refl (mult a b))
                          (cong Nat Nat Z (mult a Z) (λ x => (plus (mult a b) x)) (eq-refl Z))))
                          (λ k => (λ pk =>
                            (eq-trans Nat (mult a (plus b (S k))) (mult a (S (plus b k))) (plus (mult a b) (mult a (S k)))
                                      (cong Nat Nat (plus b (S k)) (S (plus b k)) (λ x => (mult a x)) (eq-refl (S (plus b k))))
                            (eq-trans Nat (mult a (S (plus b k))) (plus a (mult a (plus b k))) (plus (mult a b) (mult a (S k)))
                                      (eq-refl (plus a (mult a (plus b k))))
                            (eq-trans Nat (plus a (mult a (plus b k))) (plus a (plus (mult a b) (mult a k))) (plus (mult a b) (mult a (S k)))
                                      (cong Nat Nat (mult a (plus b k)) (plus (mult a b) (mult a k)) (λ x => (plus a x)) pk)
                            (eq-trans Nat (plus a (plus (mult a b) (mult a k))) (plus (plus a (mult a b)) (mult a k)) (plus (mult a b) (mult a (S k)))
                                      (plus-assoc a (mult a b) (mult a k))
                            (eq-trans Nat (plus (plus a (mult a b)) (mult a k)) (plus (plus (mult a b) a) (mult a k)) (plus (mult a b) (mult a (S k)))
                                      (cong Nat Nat (plus a (mult a b)) (plus (mult a b) a) (λ x => (plus x (mult a k))) (plus-comm a (mult a b)))
                            (eq-trans Nat (plus (plus (mult a b) a) (mult a k)) (plus (mult a b) (plus a (mult a k))) (plus (mult a b) (mult a (S k)))
                                      (eq-symm Nat (plus (mult a b) (plus a (mult a k))) (plus (plus (mult a b) a) (mult a k)) (plus-assoc (mult a b) a (mult a k)))
                            (cong Nat Nat (plus a (mult a k)) (mult a (S k)) (λ x => (plus (mult a b) x)) (eq-refl (plus a (mult a k))))))))))))
                          c))))

             : (∀ (a : Nat) (b : Nat) (c : Nat) -> ((mult a (plus b c)) = (plus (mult a b) (mult a c))))))



(def 'mult-assoc '((λ a => (λ b => (λ c =>
                     (nat-ind
                      (λ x => ((mult a (mult b x)) = (mult (mult a b) x)))
                      (eq-trans Nat (mult a (mult b Z)) (mult a Z) (mult (mult a b) Z)
                                (cong Nat Nat (mult b Z) Z (λ x => (mult a x)) (eq-refl Z))
                      (eq-trans Nat (mult a Z) Z (mult (mult a b) Z)
                                (eq-refl Z)
                      (eq-refl Z)))
                      (λ k => (λ pk =>
                        (eq-trans Nat (mult a (mult b (S k))) (mult a (plus b (mult b k))) (mult (mult a b) (S k))
                                  (cong Nat Nat (mult b (S k)) (plus b (mult b k)) (λ x => (mult a x)) (eq-refl (plus b (mult b k))))
                        (eq-trans Nat (mult a (plus b (mult b k))) (plus (mult a b) (mult a (mult b k))) (mult (mult a b) (S k))
                                  (mult-left-dist a b (mult b k))
                        (eq-trans Nat (plus (mult a b) (mult a (mult b k))) (plus (mult a b) (mult (mult a b) k)) (mult (mult a b) (S k))
                                  (cong Nat Nat (mult a (mult b k)) (mult (mult a b) k) (λ x => (plus (mult a b) x)) pk)
                        (eq-refl (plus (mult a b) (mult (mult a b) k))))))))
                      c))))

                   : (∀ (a : Nat) (b : Nat) (c : Nat) -> ((mult a (mult b c)) = (mult (mult a b) c)))))



(def 'mult-right-dist '((λ a => (λ b => (λ c =>
                          (eq-trans Nat (mult (plus a b) c) (mult c (plus a b)) (plus (mult a c) (mult b c))
                                    (mult-comm (plus a b) c)
                          (eq-trans Nat (mult c (plus a b)) (plus (mult c a) (mult c b)) (plus (mult a c) (mult b c))
                                    (mult-left-dist c a b)
                          (eq-trans Nat (plus (mult c a) (mult c b)) (plus (mult a c) (mult c b)) (plus (mult a c) (mult b c))
                                    (cong Nat Nat (mult c a) (mult a c) (λ x => (plus x (mult c b))) (mult-comm c a))
                          (cong Nat Nat (mult c b) (mult b c) (λ x => (plus (mult a c) x)) (mult-comm c b))))))))

                        : (∀ (a : Nat) (b : Nat) (c : Nat) -> ((mult (plus a b) c) = (plus (mult a c) (mult b c))))))



(def 'foil '((λ a => (λ b => (λ c => (λ d =>
               (eq-trans Nat (mult (plus a b) (plus c d)) (plus (mult a (plus c d)) (mult b (plus c d))) (plus (plus (plus (mult a c) (mult a d)) (mult b c)) (mult b d))
                         (mult-right-dist a b (plus c d))
               (eq-trans Nat (plus (mult a (plus c d)) (mult b (plus c d))) (plus (plus (mult a c) (mult a d)) (mult b (plus c d))) (plus (plus (plus (mult a c) (mult a d)) (mult b c)) (mult b d))
                         (cong Nat Nat (mult a (plus c d)) (plus (mult a c) (mult a d)) (λ x => (plus x (mult b (plus c d)))) (mult-left-dist a c d))
               (eq-trans Nat (plus (plus (mult a c) (mult a d)) (mult b (plus c d))) (plus (plus (mult a c) (mult a d)) (plus (mult b c) (mult b d))) (plus (plus (plus (mult a c) (mult a d)) (mult b c)) (mult b d))
                         (cong Nat Nat (mult b (plus c d)) (plus (mult b c) (mult b d)) (λ x => (plus (plus (mult a c) (mult a d)) x)) (mult-left-dist b c d))
               (plus-assoc (plus (mult a c) (mult a d)) (mult b c) (mult b d)))))))))

             : (∀ (a : Nat) (b : Nat) (c : Nat) (d : Nat) -> ((mult (plus a b) (plus c d)) = (plus (plus (plus (mult a c) (mult a d)) (mult b c)) (mult b d))))))



(def 'plus-one '((λ n =>
                   (eq-trans Nat (plus n (S Z)) (S (plus n Z)) (S n)
                             (eq-refl (S (plus n Z)))
                   (cong Nat Nat (plus n Z) n (λ x => (S x)) (eq-refl n))))

                : (∀ (n : Nat) -> ((plus n (S Z)) = (S n)))))



(def 'mult-one '((λ n =>
                   (eq-trans Nat (mult n (S Z)) (plus n (mult n Z)) n
                             (eq-refl (plus n (mult n Z)))
                   (eq-trans Nat (plus n (mult n Z)) (plus n Z) n
                             (cong Nat Nat (mult n Z) Z (λ x => (plus n x)) (eq-refl Z))
                   (eq-refl n))))

                : (∀ (n : Nat) -> ((mult n (S Z)) = n))))



(def 'exp '((λ n => (λ m =>
              (nat-ind
               (λ x => Nat)
               (S Z)
               (λ k => (λ pk => (mult n pk)))
               m)))

            : (Nat -> Nat -> Nat)))



(def 'exp-base-zero '((λ n =>
                        (eq-trans Nat (exp Z (S n)) (mult Z (exp Z n)) Z
                                  (eq-refl (mult Z (exp Z n)))
                        (mult-zero-left (exp Z n))))

                      : (∀ (n : Nat) -> ((exp Z (S n)) = Z))))



(def 'exp-power-one '((λ n =>
                        (eq-trans Nat (exp n (S Z)) (mult n (exp n Z)) n
                                  (eq-refl (mult n (exp n Z)))
                        (eq-trans Nat (mult n (exp n Z)) (mult n (S Z)) n
                                  (cong Nat Nat (exp n Z) (S Z) (λ x => (mult n x)) (eq-refl (S Z)))
                        (mult-one n))))

                      : (∀ (n : Nat) -> ((exp n (S Z)) = n))))



(def 'exp-base-one '((λ n =>
                       (nat-ind
                        (λ x => ((exp (S Z) x) = (S Z)))
                        (eq-refl (S Z))
                        (λ k => (λ pk =>
                          (eq-trans Nat (exp (S Z) (S k)) (mult (S Z) (exp (S Z) k)) (S Z)
                                    (eq-refl (mult (S Z) (exp (S Z) k)))
                          (eq-trans Nat (mult (S Z) (exp (S Z) k)) (mult (S Z) (S Z)) (S Z)
                                    (cong Nat Nat (exp (S Z) k) (S Z) (λ x => (mult (S Z) x)) pk)
                          (mult-one (S Z))))))
                        n))

                     : (∀ (n : Nat) -> ((exp (S Z) n) = (S Z)))))



(def 'exp-prod-same-base '((λ a => (λ b => (λ c =>
                             (nat-ind
                              (λ x => ((mult (exp a b) (exp a x)) = (exp a (plus b x))))
                              (eq-trans Nat (mult (exp a b) (exp a Z)) (mult (exp a b) (S Z)) (exp a (plus b Z))
                                        (cong Nat Nat (exp a Z) (S Z) (λ x => (mult (exp a b) x)) (eq-refl (S Z)))
                              (eq-trans Nat (mult (exp a b) (S Z)) (exp a b) (exp a (plus b Z))
                                        (mult-one (exp a b))
                              (cong Nat Nat b (plus b Z) (λ x => (exp a x)) (eq-refl b))))
                              (λ k => (λ pk =>
                                (eq-trans Nat (mult (exp a b) (exp a (S k))) (mult (exp a b) (mult a (exp a k))) (exp a (plus b (S k)))
                                          (cong Nat Nat (exp a (S k)) (mult a (exp a k)) (λ x => (mult (exp a b) x)) (eq-refl (mult a (exp a k))))
                                (eq-trans Nat (mult (exp a b) (mult a (exp a k))) (mult (mult (exp a b) a) (exp a k)) (exp a (plus b (S k)))
                                          (mult-assoc (exp a b) a (exp a k))
                                (eq-trans Nat (mult (mult (exp a b) a) (exp a k)) (mult (mult a (exp a b)) (exp a k)) (exp a (plus b (S k)))
                                          (cong Nat Nat (mult (exp a b) a) (mult a (exp a b)) (λ x => (mult x (exp a k))) (mult-comm (exp a b) a))
                                (eq-trans Nat (mult (mult a (exp a b)) (exp a k)) (mult a (mult (exp a b) (exp a k))) (exp a (plus b (S k)))
                                          (eq-symm Nat (mult a (mult (exp a b) (exp a k))) (mult (mult a (exp a b)) (exp a k)) (mult-assoc a (exp a b) (exp a k)))
                                (eq-trans Nat (mult a (mult (exp a b) (exp a k))) (mult a (exp a (plus b k))) (exp a (plus b (S k)))
                                          (cong Nat Nat (mult (exp a b) (exp a k)) (exp a (plus b k)) (λ x => (mult a x)) pk)
                                (eq-trans Nat (mult a (exp a (plus b k))) (exp a (S (plus b k))) (exp a (plus b (S k)))
                                          (eq-refl (mult a (exp a (plus b k))))
                                (cong Nat Nat (S (plus b k)) (plus b (S k)) (λ x => (exp a x)) (eq-refl (S (plus b k))))))))))))
                              c))))
                             
                           : (∀ (a : Nat) (b : Nat) (c : Nat) -> ((mult (exp a b) (exp a c)) = (exp a (plus b c))))))



(def 'exp-prod-same-power '((λ a => (λ b => (λ c =>
                              (nat-ind
                               (λ x => ((mult (exp a x) (exp b x)) = (exp (mult a b) x)))
                               (eq-trans Nat (mult (exp a Z) (exp b Z)) (mult (S Z) (exp b Z)) (exp (mult a b) Z)
                                         (cong Nat Nat (exp a Z) (S Z) (λ x => (mult x (exp b Z))) (eq-refl (S Z)))
                               (eq-trans Nat (mult (S Z) (exp b Z)) (mult (S Z) (S Z)) (exp (mult a b) Z)
                                         (cong Nat Nat (exp b Z) (S Z) (λ x => (mult (S Z) x)) (eq-refl (S Z)))
                               (eq-trans Nat (mult (S Z) (S Z)) (S Z) (exp (mult a b) Z)
                                         (mult-one (S Z))
                               (eq-refl (S Z)))))
                               (λ k => (λ pk =>
                                 (eq-trans Nat (mult (exp a (S k)) (exp b (S k))) (mult (mult a (exp a k)) (exp b (S k))) (exp (mult a b) (S k))
                                           (cong Nat Nat (exp a (S k)) (mult a (exp a k)) (λ x => (mult x (exp b (S k)))) (eq-refl (mult a (exp a k))))
                                 (eq-trans Nat (mult (mult a (exp a k)) (exp b (S k))) (mult (mult a (exp a k)) (mult b (exp b k))) (exp (mult a b) (S k))
                                           (cong Nat Nat (exp b (S k)) (mult b (exp b k)) (λ x => (mult (mult a (exp a k)) x)) (eq-refl (mult b (exp b k))))
                                 (eq-trans Nat (mult (mult a (exp a k)) (mult b (exp b k))) (mult a (mult (exp a k) (mult b (exp b k)))) (exp (mult a b) (S k))
                                           (eq-symm Nat (mult a (mult (exp a k) (mult b (exp b k)))) (mult (mult a (exp a k)) (mult b (exp b k))) (mult-assoc a (exp a k) (mult b (exp b k))))
                                 (eq-trans Nat (mult a (mult (exp a k) (mult b (exp b k)))) (mult a (mult (mult (exp a k) b) (exp b k))) (exp (mult a b) (S k))
                                           (cong Nat Nat (mult (exp a k) (mult b (exp b k))) (mult (mult (exp a k) b) (exp b k)) (λ x => (mult a x)) (mult-assoc (exp a k) b (exp b k)))
                                 (eq-trans Nat (mult a (mult (mult (exp a k) b) (exp b k))) (mult a (mult (mult b (exp a k)) (exp b k))) (exp (mult a b) (S k))
                                           (cong Nat Nat (mult (exp a k) b) (mult b (exp a k)) (λ x => (mult a (mult x (exp b k)))) (mult-comm (exp a k) b))
                                 (eq-trans Nat (mult a (mult (mult b (exp a k)) (exp b k))) (mult a (mult b (mult (exp a k) (exp b k)))) (exp (mult a b) (S k))
                                           (cong Nat Nat (mult (mult b (exp a k)) (exp b k)) (mult b (mult (exp a k) (exp b k))) (λ x => (mult a x))
                                                 (eq-symm Nat (mult b (mult (exp a k) (exp b k))) (mult (mult b (exp a k)) (exp b k)) (mult-assoc b (exp a k) (exp b k))))
                                 (eq-trans Nat (mult a (mult b (mult (exp a k) (exp b k)))) (mult (mult a b) (mult (exp a k) (exp b k))) (exp (mult a b) (S k))
                                           (mult-assoc a b (mult (exp a k) (exp b k)))
                                 (eq-trans Nat (mult (mult a b) (mult (exp a k) (exp b k))) (mult (mult a b) (exp (mult a b) k)) (exp (mult a b) (S k))
                                           (cong Nat Nat (mult (exp a k) (exp b k)) (exp (mult a b) k) (λ x => (mult (mult a b) x)) pk)
                                 (eq-refl (mult (mult a b) (exp (mult a b) k)))))))))))))
                               c))))

                            : (∀ (a : Nat) (b : Nat) (c : Nat) -> ((mult (exp a c) (exp b c)) = (exp (mult a b) c)))))



(def 'exp-power-prod '((λ a => (λ b => (λ c =>
                         (nat-ind
                          (λ x => ((exp a (mult b x)) = (exp (exp a b) x)))
                          (eq-trans Nat (exp a (mult b Z)) (exp a Z) (exp (exp a b) Z)
                                    (cong Nat Nat (mult b Z) Z (λ x => (exp a x)) (eq-refl Z))
                          (eq-trans Nat (exp a Z) (S Z) (exp (exp a b) Z)
                                    (eq-refl (S Z))
                          (eq-refl (S Z))))
                          (λ k => (λ pk =>
                            (eq-trans Nat (exp a (mult b (S k))) (exp a (plus b (mult b k))) (exp (exp a b) (S k))
                                      (cong Nat Nat (mult b (S k)) (plus b (mult b k)) (λ x => (exp a x)) (eq-refl (plus b (mult b k))))
                            (eq-trans Nat (exp a (plus b (mult b k))) (mult (exp a b) (exp a (mult b k))) (exp (exp a b) (S k))
                                      (eq-symm Nat (mult (exp a b) (exp a (mult b k))) (exp a (plus b (mult b k))) (exp-prod-same-base a b (mult b k)))
                            (eq-trans Nat (mult (exp a b) (exp a (mult b k))) (mult (exp a b) (exp (exp a b) k)) (exp (exp a b) (S k))
                                      (cong Nat Nat (exp a (mult b k)) (exp (exp a b) k) (λ x => (mult (exp a b) x)) pk)
                            (eq-refl (mult (exp a b) (exp (exp a b) k))))))))
                          c))))

                       : (∀ (a : Nat) (b : Nat) (c : Nat) -> ((exp a (mult b c)) = (exp (exp a b) c)))))



(def 'exp-pseudo-comm '((λ a => (λ b => (λ c =>
                          (eq-trans Nat (exp (exp a b) c) (exp a (mult b c)) (exp (exp a c) b)
                                    (eq-symm Nat (exp a (mult b c)) (exp (exp a b) c) (exp-power-prod a b c))
                          (eq-trans Nat (exp a (mult b c)) (exp a (mult c b)) (exp (exp a c) b)
                                    (cong Nat Nat (mult b c) (mult c b) (λ x => (exp a x)) (mult-comm b c))
                          (exp-power-prod a c b))))))

                        : (∀ (a : Nat) (b : Nat) (c : Nat) -> ((exp (exp a b) c) = (exp (exp a c) b)))))



(def 'fact '((λ n =>
               (nat-ind
                (λ x => Nat)
                (S Z)
                (λ k => (λ pk => (mult (S k) pk)))
                n))

             : (Nat -> Nat)))



(def 'sub1-lemma '((λ n => (λ e =>
                     (eq-elim Z (λ x => ((sub1 x) = Z)) (eq-refl Z) n (eq-symm Nat n Z e))))

                   : (∀ (n : Nat) -> ((n = Z) -> ((sub1 n) = Z)))))



(def 'sub1-inverse-basic '((λ n =>
                             (nat-ind
                              (λ x => ((leq (S Z) x) -> ((S (sub1 x)) = x)))
                              ((λ l =>
                                 (eq-trans Nat (S (sub1 Z)) (S Z) Z
                                           (eq-refl (S Z))
                                 (eq-trans Nat (S Z) (sub (S Z) Z) Z
                                           (eq-refl (S Z))
                                 l))) : ((leq (S Z) Z) -> ((S (sub1 Z)) = Z)))
                              (λ k => (λ pk => ((λ l =>
                                (eq-refl (S k))) : ((leq (S Z) (S k)) -> ((S (sub1 (S k))) = (S k))))))
                              n))

                           : (∀ (n : Nat) -> ((leq (S Z) n) -> ((S (sub1 n)) = n)))))



(def 'leq-lemma-left '((λ a => (λ b =>
                    (nat-ind
                     (λ x => ((leq (S a) x) -> (leq a x)))
                     ((λ l => (eq-elim Z (λ x => ((sub x Z) = Z)) (eq-refl Z) a
                                       (eq-symm Nat a Z
                                                (cong Nat Nat (S a) Z (λ x => (sub1 x))
                                                      (eq-elim (sub (S a) Z) (λ x => (x = Z)) l (S a) (eq-refl (S a))))))) : ((leq (S a) Z) -> (leq a Z)))
                     (λ k => (λ pk => ((λ l =>
                       (eq-elim (sub1 (sub a k)) (λ x => ((sub a (S k)) = x)) (eq-refl (sub1 (sub a k))) Z
                                (sub1-lemma (sub a k) (eq-elim (sub (S a) (S k)) (λ x => ((sub a k) = x)) (eq-symm Nat (sub (S a) (S k)) (sub a k) (subS a k)) Z l)))) : ((leq (S a) (S k)) -> (leq a (S k))))))
                     b)))

                  : (∀ (a : Nat) (b : Nat) -> ((leq (S a) b) -> (leq a b)))))



(def 'leq-lemma-right '((λ a => (λ b => (λ l =>
                          (eq-trans Nat (sub a (S b)) (sub1 (sub a b)) Z
                                    (eq-refl (sub1 (sub a b)))
                          (eq-trans Nat (sub1 (sub a b)) (sub1 Z) Z
                                    (cong Nat Nat (sub a b) Z (λ x => (sub1 x)) l)
                          (eq-refl Z))))))

                        : (∀ (a : Nat) (b : Nat) -> ((leq a b) -> (leq a (S b))))))



(def 'nat-ind-two '((λ P => (λ pzz => (λ paz => (λ pzb => (λ I => (λ n => (λ m =>
                      (((nat-ind
                       (λ x => (∀ (t : Nat) -> (P t x)))
                       ((λ t =>
                          (nat-ind 
                           (λ x => (P x Z))
                           pzz
                           (λ k => (λ pk => (paz k)))
                           t)) : (∀ (t : Nat) -> (P t Z)))
                       (λ i => (λ pi => ; substitution error! cannot use k here, otherwise it gets subbed with l, because in typesynth, we force a k into it
                         ((λ t => ; to reproduce the problem: make a nat ind, name your arbitary nat k, and then do another nat ind within the inductive part
                            (nat-ind
                             (λ x => (P x (S i)))
                             (pzb i)
                             (λ k => (λ pk => (((((I k) i) ((pi : (∀ (t : Nat) -> ((P t) i))) k)) ((pi : (∀ (t : Nat) -> ((P t) i))) (S k))) pk)))
                             t)) : (∀ (t : Nat) -> (P t (S i))))))
                       m) : (∀ (t : Nat) -> (P t m))) n))))))))

                    : (∀ (P : (Nat -> Nat -> Type)) ->
                         ((P Z Z)
                          -> (∀ (a : Nat) -> (P (S a) Z))
                          -> (∀ (b : Nat) -> (P Z (S b)))
                          -> (∀ (a : Nat) (b : Nat) ->
                                ((P a b)
                                 -> (P (S a) b)
                                 -> (P a (S b))
                                 -> (P (S a) (S b))))
                          -> (∀ (n : Nat) (m : Nat) -> (P n m))))))



(def 'choose '((λ n => (λ r =>
                 ((nat-ind-two ((λ x => (λ y => Nat)) : (Nat -> Nat -> Type))
                               (S Z)
                               (λ a => (S Z))
                               (λ b => Z)
                               (λ a => (λ b => (λ pab => (λ psab => (λ pasb =>
                                 (plus pab pasb))))))) n r))) ; pascal identity

               : (Nat -> Nat -> Nat)))

; sum from a to (plus a b) of (f x)

(def 'sum '((λ a => (λ b => (λ f =>
                  (nat-ind
                   (λ x => Nat)
                   (f a)
                   (λ k => (λ pk => (plus pk (f (plus a (S k))))))
                   b))))

                : (Nat -> Nat -> (Nat -> Nat) -> Nat)))



(def 'leq-plus '((λ a => (λ b => (λ c =>
                   (nat-ind
                    (λ x => ((leq a b) -> (leq a (plus b x))))
                    ((λ l =>
                       (eq-trans Nat (sub a (plus b Z)) (sub a b) Z
                                 (eq-refl (sub a b))
                       l)) : ((leq a b) -> (leq a (plus b Z))))
                    (λ k => (λ pk => ((λ l =>
                       (eq-trans Nat (sub a (plus b (S k))) (sub a (S (plus b k))) Z
                                 (eq-refl (sub a (S (plus b k))))
                       (leq-lemma-right a (plus b k) ((pk : ((leq a b) -> (leq a (plus b k)))) l)))) : ((leq a b) -> (leq a (plus b (S k)))))))
                    c))))

                 : (∀ (a : Nat) (b : Nat) (c : Nat) -> ((leq a b) -> (leq a (plus b c))))))



;(def 'leq-sum-basic '((λ n => (λ f =>
;                        (nat-ind
;                         (λ x => (leq (f Z) (sum-basic x f)))
;                         (leq-refl (f Z))
;                         (λ k => (λ pk =>
;                           (eq-elim (sub (f Z) (plus (sum-basic k f) (f (S k)))) (λ x => (x = Z)) (leq-plus (f Z) (sum-basic k f) (f (S k)) pk) (sub (f Z) (sum-basic (S k) f))
;                                    (eq-refl (sub (f Z) (plus (sum-basic k f) (f (S k))))))))
;                         n)))

;                      : (∀ (n : Nat) (f : (Nat -> Nat)) -> (leq (f Z) (sum-basic n f)))))



(def 'plus-sub-cancel '((λ a => (λ b =>
                          (nat-ind-two
                           ((λ x => (λ y => ((leq y x) -> ((plus (sub x y) y) = x)))) : (Nat -> Nat -> Type))
                           ((λ l => (eq-refl Z)) : ((leq Z Z) -> ((plus (sub Z Z) Z) = Z)))
                           (λ left => ((λ l => (eq-refl (S left))) : ((leq Z (S left)) -> ((plus (sub (S left) Z) Z) = (S left)))));  : ((leq (S left) Z) -> ((plus (sub (S left) Z) Z) = (S left)))))
                           (λ right => ((λ l =>
                             (eq-trans Nat (plus (sub Z (S right)) (S right)) (plus (sub Z Z) Z) Z
                                       (cong Nat Nat (S right) Z (λ x => (plus (sub Z x) x))
                                             (eq-trans Nat (S right) (sub (S right) Z) Z
                                                       (eq-refl (S right))
                                             l))
                             (eq-refl Z))) : ((leq (S right) Z) -> ((plus (sub Z (S right)) (S right)) = Z))))
                           (λ a => (λ b => (λ pab => (λ psab => (λ pasb => ((λ l =>
                             (eq-trans Nat (plus (sub (S a) (S b)) (S b)) (S (plus (sub (S a) (S b)) b)) (S a)
                                       (eq-refl (S (plus (sub (S a) (S b)) b)))
                             (eq-trans Nat (S (plus (sub (S a) (S b)) b)) (S (plus (sub a b) b)) (S a)
                                       (cong Nat Nat (sub (S a) (S b)) (sub a b) (λ x => (S (plus x b))) (subS a b))
                             (cong Nat Nat (plus (sub a b) b) a (λ x => (S x)) ((pab : ((leq b a) -> ((plus (sub a b) b) = a)))
                                   (eq-trans Nat (sub b a) (sub (S b) (S a)) Z
                                             (eq-symm Nat (sub (S b) (S a)) (sub b a) (subS b a))
                                             l)))))) : ((leq (S b) (S a)) -> ((plus (sub (S a) (S b)) (S b)) = (S a)))))))))
                           a
                           b)))

                        : (∀ (a : Nat) (b : Nat) -> ((leq b a) -> ((plus (sub a b) b) = a)))))



(def 'sub-plus-cancel '((λ a => (λ b =>
                          (nat-ind
                              (λ x => ((sub (plus x b) x) = b))
                              (eq-trans Nat (sub (plus Z b) Z) (sub b Z) b
                                        (cong Nat Nat (plus Z b) b (λ x => (sub x Z)) (plus-zero-left b))
                              (eq-refl b))
                              (λ k => (λ pk =>
                                (eq-trans Nat (sub (plus (S k) b) (S k)) (sub (S (plus k b)) (S k)) b
                                          (cong Nat Nat (plus (S k) b) (S (plus k b)) (λ x => (sub x (S k))) (plus-lemma k b))
                                (eq-trans Nat (sub (S (plus k b)) (S k)) (sub (plus k b) k) b
                                          (subS (plus k b) k)
                                pk))))
                              a)))

                        : (∀ (a : Nat) (b : Nat) -> ((sub (plus a b) a) = b))))



(def 'sum-add-term-last '((λ a => (λ b => (λ f =>
                            (eq-trans Nat (plus (f (plus a (S b))) (sum a b f)) (plus (sum a b f) (f (plus a (S b)))) (sum a (S b) f)
                                      (plus-comm (f (plus a (S b))) (sum a b f))
                            (eq-refl (plus (sum a b f) (f (plus a (S b)))))))))

                     : (∀ (a : Nat) (b : Nat) (f : (Nat -> Nat)) -> ((plus (f (plus a (S b))) (sum a b f)) = (sum a (S b) f)))))



(def 'sum-add-term-first '((λ a => (λ b => (λ f =>
                             (nat-ind
                              (λ x => ((plus (f a) (sum (S a) x f)) = (sum a (S x) f)))
                              (eq-trans Nat (plus (f a) (sum (S a) Z f)) (plus (f a) (f (S a))) (sum a (S Z) f)
                                        (eq-refl (plus (f a) (f (S a))))
                              (eq-refl (plus (f a) (f (S a)))))
                              (λ k => (λ pk =>
                                (eq-trans Nat (plus (f a) (sum (S a) (S k) f)) (plus (f a) (plus (sum (S a) k f) (f (plus (S a) (S k))))) (sum a (S (S k)) f)
                                          (eq-refl (plus (f a) (plus (sum (S a) k f) (f (plus (S a) (S k))))))
                                (eq-trans Nat (plus (f a) (plus (sum (S a) k f) (f (plus (S a) (S k))))) (plus (plus (f a) (sum (S a) k f)) (f (plus (S a) (S k)))) (sum a (S (S k)) f)
                                          (plus-assoc (f a) (sum (S a) k f) (f (plus (S a) (S k))))
                                (eq-trans Nat (plus (plus (f a) (sum (S a) k f)) (f (plus (S a) (S k)))) (plus (sum a (S k) f) (f (plus (S a) (S k)))) (sum a (S (S k)) f)
                                          (cong Nat Nat (plus (f a) (sum (S a) k f)) (sum a (S k) f) (λ x => (plus x (f (plus (S a) (S k))))) pk)
                                (eq-trans Nat (plus (sum a (S k) f) (f (plus (S a) (S k)))) (plus (sum a (S k) f) (f (S (plus a (S k))))) (sum a (S (S k)) f)
                                          (cong Nat Nat (plus (S a) (S k)) (S (plus a (S k))) (λ x => (plus (sum a (S k) f) (f x))) (plus-lemma a (S k)))
                                (eq-trans Nat (plus (sum a (S k) f) (f (S (plus a (S k))))) (plus (sum a (S k) f) (f (plus a (S (S k))))) (sum a (S (S k)) f)
                                          (cong Nat Nat (S (plus a (S k))) (plus a (S (S k))) (λ x => (plus (sum a (S k) f) (f x))) (eq-refl (S (plus a (S k)))))
                                (eq-refl (plus (sum a (S k) f) (f (plus a (S (S k)))))))))))))
                              b))))

                           : (∀ (a : Nat) (b : Nat) (f : (Nat -> Nat)) -> ((plus (f a) (sum (S a) b f)) = (sum a (S b) f)))))



(def 'sum-factor '((λ a => (λ b => (λ c => (λ f => (λ g => (λ rel =>
                     (nat-ind
                      (λ x => ((sum a x g) = (mult c (sum a x f))))
                      (eq-trans Nat (sum a Z g) (g a) (mult c (sum a Z f))
                                (eq-refl (g a))
                      (eq-trans Nat (g a) (mult c (f a)) (mult c (sum a Z f))
                                (rel a)
                      (eq-refl (mult c (f a)))))
                      (λ k => (λ pk =>
                        (eq-trans Nat (sum a (S k) g) (plus (sum a k g) (g (plus a (S k)))) (mult c (sum a (S k) f))
                                  (eq-refl (plus (sum a k g) (g (plus a (S k)))))
                        (eq-trans Nat (plus (sum a k g) (g (plus a (S k)))) (plus (mult c (sum a k f)) (g (plus a (S k)))) (mult c (sum a (S k) f))
                                  (cong Nat Nat (sum a k g) (mult c (sum a k f)) (λ x => (plus x (g (plus a (S k))))) pk)
                        (eq-trans Nat (plus (mult c (sum a k f)) (g (plus a (S k)))) (plus (mult c (sum a k f)) (mult c (f (plus a (S k))))) (mult c (sum a (S k) f))
                                  (cong Nat Nat (g (plus a (S k))) (mult c (f (plus a (S k)))) (λ x => (plus (mult c (sum a k f)) x)) (rel (plus a (S k))))
                        (eq-trans Nat (plus (mult c (sum a k f)) (mult c (f (plus a (S k))))) (mult c (plus (sum a k f) (f (plus a (S k))))) (mult c (sum a (S k) f))
                                  (eq-symm Nat (mult c (plus (sum a k f) (f (plus a (S k))))) (plus (mult c (sum a k f)) (mult c (f (plus a (S k))))) (mult-left-dist c (sum a k f) (f (plus a (S k)))))
                        (eq-refl (mult c (plus (sum a k f) (f (plus a (S k))))))))))))
                      b)))))))

                   : (∀ (a : Nat) (b : Nat) (c : Nat) (f : (Nat -> Nat)) (g : (Nat -> Nat)) -> ((∀ (x : Nat) -> ((g x) = (mult c (f x)))) -> ((sum a b g) = (mult c (sum a b f)))))))



(def 'leq-one-sub '((λ a => (λ b =>
                      (nat-ind-two
                       ((λ x => (λ y => ((leq (S y) x) -> (leq (S Z) (sub x y))))) : (Nat -> Nat -> Type))
                       ((λ l =>
                          (eq-trans Nat (sub (S Z) (sub Z Z)) (S Z) Z
                                    (eq-refl (S Z))
                          (eq-trans Nat (S Z) (sub (S Z) Z) Z
                                    (eq-refl (S Z))
                          l))) : ((leq (S Z) Z) -> (leq (S Z) (sub Z Z))))
                       (λ left => ((λ l =>
                         (eq-trans Nat (sub (S Z) (sub (S left) Z)) (sub (S Z) (S left)) Z
                                   (eq-refl (sub (S Z) (S left)))
                         l)) : ((leq (S Z) (S left)) -> (leq (S Z) (sub (S left) Z)))))
                       (λ right => ((λ l =>
                         (eq-trans Nat (sub (S Z) (sub Z (S right))) (sub (S Z) Z) Z
                                   (cong Nat Nat (sub Z (S right)) Z (λ x => (sub (S Z) x)) (leqZ (S right)))
                         (eq-trans Nat (sub (S Z) Z) (S Z) Z
                                   (eq-refl (S Z))
                         (eq-trans Nat (S Z) (S right) Z
                                   (cong Nat Nat Z right (λ x => (S x))
                                         (eq-trans Nat Z (sub right Z) right
                                                   (eq-symm Nat (sub right Z) Z (leq-lemma-left right Z (leq-lemma-left (S right) Z l)))
                                         (eq-refl right)))
                         (eq-trans Nat (S right) (sub (S right) Z) Z
                                   (eq-refl (S right))
                         (leq-lemma-left (S right) Z l)))))) : ((leq (S (S right)) Z) -> (leq (S Z) (sub Z (S right))))))
                       (λ a => (λ b => (λ pab => (λ psab => (λ pasb => ((λ l =>
                         (eq-trans Nat (sub (S Z) (sub (S a) (S b))) (sub (S Z) (sub a b)) Z
                                   (cong Nat Nat (sub (S a) (S b)) (sub a b) (λ x => (sub (S Z) x)) (subS a b))
                         ((pab : ((leq (S b) a) -> (leq (S Z) (sub a b))))
                          (eq-trans Nat (sub (S b) a) (sub (S (S b)) (S a)) Z
                                    (eq-symm Nat (sub (S (S b)) (S a)) (sub (S b) a) (subS (S b) a))
                          l)))) : ((leq (S (S b)) (S a)) -> (leq (S Z) (sub (S a) (S b))))))))))
                       a b)))

                    : (∀ (a : Nat) (b : Nat) -> ((leq (S b) a) -> (leq (S Z) (sub a b))))))



(def 'sub-lemma '((λ a => (λ b =>
                    (nat-ind
                     (λ x => ((leq x a) -> ((sub (S a) x) = (S (sub a x)))))
                     ((λ l => (eq-refl (S a))) : ((leq Z a) -> ((sub (S a) Z) = (S (sub a Z)))))
                     (λ k => (λ pk => ((λ l =>
                       (eq-trans Nat (sub (S a) (S k)) (sub a k) (S (sub a (S k)))
                                 (subS a k)
                       (eq-trans Nat (sub a k) (S (sub1 (sub a k))) (S (sub a (S k)))
                                 (eq-symm Nat (S (sub1 (sub a k))) (sub a k) (sub1-inverse-basic (sub a k) (leq-one-sub a k l)))
                       (eq-refl (S (sub1 (sub a k))))))) : ((leq (S k) a) -> ((sub (S a) (S k)) = (S (sub a (S k))))))))
                     b)))

                  : (∀ (a : Nat) (b : Nat) -> ((leq b a) -> ((sub (S a) b) = (S (sub a b)))))))



(def 'plus-sub-left '((λ a => (λ b => (λ c =>
                        (nat-ind
                         (λ x => ((leq b a) -> ((plus (sub a b) x) = (sub (plus a x) b))))
                         ((λ l =>
                            (eq-refl (sub a b))) : ((leq b a) -> ((plus (sub a b) Z) = (sub (plus a Z) b))))
                         (λ k => (λ pk => ((λ l =>
                           (eq-trans Nat (plus (sub a b) (S k)) (S (plus (sub a b) k)) (sub (plus a (S k)) b)
                                     (eq-refl (S (plus (sub a b) k)))
                           (eq-trans Nat (S (plus (sub a b) k)) (S (sub (plus a k) b)) (sub (plus a (S k)) b)
                                     (cong Nat Nat (plus (sub a b) k) (sub (plus a k) b) (λ x => (S x)) ((pk : ((leq b a) -> ((plus (sub a b) k) = (sub (plus a k) b)))) l))
                           (eq-trans Nat (S (sub (plus a k) b)) (sub (S (plus a k)) b) (sub (plus a (S k)) b)
                                     (eq-symm Nat (sub (S (plus a k)) b) (S (sub (plus a k) b)) (sub-lemma (plus a k) b (leq-plus b a k l))) 
                           (eq-refl (sub (S (plus a k)) b)))))) : ((leq b a) -> ((plus (sub a b) (S k)) = (sub (plus a (S k)) b))))))
                         c))))

                      : (∀ (a : Nat) (b : Nat) (c : Nat) -> ((leq b a) -> ((plus (sub a b) c) = (sub (plus a c) b))))))



(def 'plus-subs '((λ a => (λ b => (λ c => (λ d =>
                    (nat-ind-two
                     ((λ x => (λ y => ((leq b a) -> (leq y x) -> ((plus (sub a b) (sub x y)) = (sub (plus a x) (plus b y)))))) : (Nat -> Nat -> Type))
                     ((λ l1 => (λ l2 => (eq-refl (sub a b)))) : ((leq b a) -> (leq Z Z) -> ((plus (sub a b) (sub Z Z)) = (sub (plus a Z) (plus b Z)))))
                     (λ left => ((λ l1 => (λ l2 =>
                       (eq-trans Nat (plus (sub a b) (sub (S left) Z)) (plus (sub a b) (S left)) (sub (plus a (S left)) (plus b Z))
                                 (eq-refl (plus (sub a b) (S left)))
                       (eq-trans Nat (plus (sub a b) (S left)) (sub (plus a (S left)) b) (sub (plus a (S left)) (plus b Z))
                                 (plus-sub-left a b (S left) l1)
                       (eq-refl (sub (plus a (S left)) b)))))) : ((leq b a) -> (leq Z (S left)) -> ((plus (sub a b) (sub (S left) Z)) = (sub (plus a (S left)) (plus b Z))))))
                     (λ right => ((λ l1 => (λ l2 =>
                       (eq-trans Nat (plus (sub a b) (sub Z (S right))) (plus (sub a b) Z) (sub (plus a Z) (plus b (S right)))
                                 (cong Nat Nat (sub Z (S right)) Z (λ x => (plus (sub a b) x)) (leqZ (S right)))
                       (eq-trans Nat (plus (sub a b) Z) (sub (plus a Z) b) (sub (plus a Z) (plus b (S right)))
                                 (plus-sub-left a b Z l1)
                       (eq-trans Nat (sub (plus a Z) b) (sub (plus a Z) (plus b Z)) (sub (plus a Z) (plus b (S right)))
                                 (eq-refl (sub (plus a Z) b))
                       (cong Nat Nat Z (S right) (λ x => (sub (plus a Z) (plus b x)))
                             (eq-symm Nat (S right) Z
                                      (eq-trans Nat (S right) (sub (S right) Z) Z
                                                (eq-refl (S right))
                                      l2)))
                       ))))) : ((leq b a) -> (leq (S right) Z) -> ((plus (sub a b) (sub Z (S right))) = (sub (plus a Z) (plus b (S right)))))))
                     (λ first => (λ second => (λ pab => (λ psab => (λ pasb => ((λ l1 => (λ l2 =>
                       (eq-trans Nat (plus (sub a b) (sub (S first) (S second))) (plus (sub a b) (sub first second)) (sub (plus a (S first)) (plus b (S second)))
                                 (cong Nat Nat (sub (S first) (S second)) (sub first second) (λ x => (plus (sub a b) x)) (subS first second))
                       (eq-trans Nat (plus (sub a b) (sub first second)) (sub (plus a first) (plus b second)) (sub (plus a (S first)) (plus b (S second)))
                                 (((pab : ((leq b a) -> ((leq second first) -> ((plus (sub a b) (sub first second)) = (sub (plus a first) (plus b second)))))) l1)
                                  ((eq-trans Nat (sub second first) (sub (S second) (S first)) Z
                                                (eq-symm Nat (sub (S second) (S first)) (sub second first) (subS second first))
                                                l2) : (leq second first)))
                       (eq-trans Nat (sub (plus a first) (plus b second)) (sub (S (plus a first)) (S (plus b second))) (sub (plus a (S first)) (plus b (S second)))
                                 (eq-symm Nat (sub (S (plus a first)) (S (plus b second))) (sub (plus a first) (plus b second)) (subS (plus a first) (plus b second)))
                       (eq-refl (sub (S (plus a first)) (S (plus b second)))))))))                                        
                     : ((leq b a) -> (leq (S second) (S first)) -> ((plus (sub a b) (sub (S first) (S second))) = (sub (plus a (S first)) (plus b (S second)))))))))))
                     c d)))))

                  : (∀ (a : Nat) (b : Nat) (c : Nat) (d : Nat) -> ((leq b a) -> (leq d c) -> ((plus (sub a b) (sub c d)) = (sub (plus a c) (plus b d)))))))



(def 'split-sum '((λ a => (λ b => (λ f => (λ g => (λ h => (λ rel =>
                    (nat-ind
                     (λ x => ((plus (sum a x f) (sum a x g)) = (sum a x h)))
                     (eq-trans Nat (plus (sum a Z f) (sum a Z g)) (plus (f a) (g a)) (sum a Z h)
                               (eq-refl (plus (f a) (g a)))
                     (eq-trans Nat (plus (f a) (g a)) (h a) (sum a Z h)
                               (eq-symm Nat (h a) (plus (f a) (g a)) (rel a))
                     (eq-refl (h a))))
                     (λ k => (λ pk =>
                       (eq-trans Nat
                                 (plus (sum a (S k) f) (sum a (S k) g))
                                 (plus (plus (sum a k f) (f (plus a (S k)))) (plus (sum a k g) (g (plus a (S k)))))
                                 (sum a (S k) h)
                                 (eq-refl (plus (plus (sum a k f) (f (plus a (S k)))) (plus (sum a k g) (g (plus a (S k))))))
                       (eq-trans Nat
                                 (plus (plus (sum a k f) (f (plus a (S k)))) (plus (sum a k g) (g (plus a (S k)))))
                                 (plus (plus (sum a k f) (sum a k g)) (plus (f (plus a (S k))) (g (plus a (S k)))))
                                 (sum a (S k) h)
                                 (plus-exchange (sum a k f) (f (plus a (S k))) (sum a k g) (g (plus a (S k))))
                       (eq-trans Nat
                                 (plus (plus (sum a k f) (sum a k g)) (plus (f (plus a (S k))) (g (plus a (S k)))))
                                 (plus (sum a k h) (plus (f (plus a (S k))) (g (plus a (S k)))))
                                 (sum a (S k) h)
                                 (cong Nat Nat (plus (sum a k f) (sum a k g)) (sum a k h) (λ x => (plus x (plus (f (plus a (S k))) (g (plus a (S k)))))) pk)
                       (eq-trans Nat
                                 (plus (sum a k h) (plus (f (plus a (S k))) (g (plus a (S k)))))
                                 (plus (sum a k h) (h (plus a (S k))))
                                 (sum a (S k) h)
                                 (cong Nat Nat (plus (f (plus a (S k))) (g (plus a (S k)))) (h (plus a (S k))) (λ x => (plus (sum a k h) x))
                                       (eq-symm Nat (h (plus a (S k))) (plus (f (plus a (S k))) (g (plus a (S k)))) (rel (plus a (S k)))))
                       (eq-refl (plus (sum a k h) (h (plus a (S k)))))))))))
                     b)))))))

                  : (∀ (a : Nat) (b : Nat) (f : (Nat -> Nat)) (g : (Nat -> Nat)) (h : (Nat -> Nat))
                       -> ((∀ (x : Nat) -> ((h x) = (plus (f x) (g x)))) -> ((plus (sum a b f) (sum a b g)) = (sum a b h))))))



(def 'shift-bounds '((λ a => (λ b => (λ f => (λ g => (λ rel =>
                       (nat-ind
                        (λ x => ((sum a x f) = (sum (S a) x g)))
                        (eq-trans Nat (sum a Z f) (f (sub1 (S a))) (sum (S a) Z g)
                                  (eq-refl (f a))
                        (eq-trans Nat (f (sub1 (S a))) (g (S a)) (sum (S a) Z g)
                                  (eq-symm Nat (g (S a)) (f (sub1 (S a))) (rel (S a)))
                        (eq-refl (g (S a)))))
                        (λ k => (λ pk =>
                          (eq-trans Nat (sum a (S k) f) (plus (sum a k f) (f (plus a (S k)))) (sum (S a) (S k) g)
                                    (eq-refl (plus (sum a k f) (f (plus a (S k)))))
                          (eq-trans Nat (plus (sum a k f) (f (plus a (S k)))) (plus (sum (S a) k g) (f (plus a (S k)))) (sum (S a) (S k) g)
                                    (cong Nat Nat (sum a k f) (sum (S a) k g) (λ x => (plus x (f (plus a (S k))))) pk)
                          (eq-trans Nat (plus (sum (S a) k g) (f (plus a (S k)))) (plus (sum (S a) k g) (f (sub1 (S (plus a (S k)))))) (sum (S a) (S k) g)
                                    (eq-refl (plus (sum (S a) k g) (f (plus a (S k)))))
                          (eq-trans Nat (plus (sum (S a) k g) (f (sub1 (S (plus a (S k)))))) (plus (sum (S a) k g) (g (S (plus a (S k))))) (sum (S a) (S k) g)
                                    (cong Nat Nat (f (sub1 (S (plus a (S k))))) (g (S (plus a (S k)))) (λ x => (plus (sum (S a) k g) x))
                                          (eq-symm Nat (g (S (plus a (S k)))) (f (sub1 (S (plus a (S k))))) (rel (S (plus a (S k))))))
                          (eq-trans Nat (plus (sum (S a) k g) (g (S (plus a (S k))))) (plus (sum (S a) k g) (g (plus (S a) (S k)))) (sum (S a) (S k) g)
                                    (cong Nat Nat (S (plus a (S k))) (plus (S a) (S k)) (λ x => (plus (sum (S a) k g) (g x)))
                                          (eq-symm Nat (plus (S a) (S k)) (S (plus a (S k))) (plus-lemma a (S k))))
                          (eq-refl (plus (sum (S a) k g) (g (plus (S a) (S k))))))))))))
                        b))))))

                     : (∀ (a : Nat) (b : Nat) (f : (Nat -> Nat)) (g : (Nat -> Nat)) -> ((∀ (x : Nat) -> ((g x) = (f (sub1 x)))) -> ((sum a b f) = (sum (S a) b g))))))



(def 'plus-equals-zero '((λ a => (λ b =>
                           (nat-ind
                            (λ x => (((plus a x) = Z) -> (x = Z)))
                            ((λ e =>
                              (eq-refl Z)) : (((plus a Z) = Z) -> (Z = Z)))
                            (λ k => (λ pk => ((λ e =>
                              (eq-trans Nat (S k) (S Z) Z
                                        (cong Nat Nat k Z (λ x => (S x))
                                              ((pk : (((plus a k) = Z) -> (k = Z)))
                                                (eq-trans Nat (plus a k) (sub1 (S (plus a k))) Z
                                                          (eq-refl (plus a k))
                                                (eq-trans Nat (sub1 (S (plus a k))) (sub1 Z) Z
                                                          (cong Nat Nat (S (plus a k)) Z (λ x => (sub1 x))
                                                                (eq-trans Nat (S (plus a k)) (plus a (S k)) Z
                                                                          (eq-refl (S (plus a k)))
                                                                e))
                                                (eq-refl Z)))))
                               (eq-trans Nat (S Z) (S (plus a k)) Z
                                         (cong Nat Nat Z (plus a k) (λ x => (S x))
                                               (eq-symm Nat (plus a k) Z
                                                        (eq-trans Nat (plus a k) (sub1 (S (plus a k))) Z
                                                                  (eq-refl (plus a k))
                                                        (eq-trans Nat (sub1 (S (plus a k))) (sub1 Z) Z
                                                                  (cong Nat Nat (S (plus a k)) Z (λ x => (sub1 x))
                                                                        (eq-trans Nat (S (plus a k)) (plus a (S k)) Z
                                                                                  (eq-refl (S (plus a k))) e))
                                                        (eq-refl Z)))))
                                (eq-trans Nat (S (plus a k)) (plus a (S k)) Z
                                          (eq-refl (S (plus a k)))
                                e)))) : (((plus a (S k)) = Z) -> ((S k) = Z)))))
                            b)))

                         : (∀ (a : Nat) (b : Nat) -> (((plus a b) = Z) -> (b = Z)))))



(def 'choose-zero '((λ n =>
                      (nat-ind
                       (λ x => ((choose x Z) = (S Z)))
                       (eq-refl (S Z))
                       (λ k => (λ pk => (eq-refl (S Z))))
                       n))

                    : (∀ (n : Nat) -> ((choose n Z) = (S Z)))))



(def 'choose-equals-zero '((λ a => (λ b =>
                             (nat-ind-two
                              ((λ x => (λ y => (((choose x y) = Z) -> ((choose x (S y)) = Z)))) : (Nat -> Nat -> Type))
                              ((λ e =>
                                 (eq-refl Z)) : (((choose Z Z) = Z) -> ((choose Z (S Z)) = Z)))
                              (λ a => ((λ e =>
                                (eq-trans Nat (choose (S a) (S Z)) (choose (S a) (choose (S a) Z)) Z
                                          (eq-refl (choose (S a) (S Z)))
                                (eq-trans Nat (choose (S a) (choose (S a) Z)) (choose (S a) Z) Z
                                          (cong Nat Nat (choose (S a) Z) Z (λ x => (choose (S a) x)) e)
                                e))) : (((choose (S a) Z) = Z) -> ((choose (S a) (S Z)) = Z))))
                              (λ b => ((λ e =>
                                (eq-refl Z)) : (((choose Z (S b)) = Z) -> ((choose Z (S (S b))) = Z))))
                              (λ a => (λ b => (λ pab => (λ psab => (λ pasb => ((λ e =>
                                (eq-trans Nat (choose (S a) (S (S b))) (plus (choose a (S b)) (choose a (S (S b)))) Z
                                          (eq-refl (plus (choose a (S b)) (choose a (S (S b)))))
                                (eq-trans Nat (plus (choose a (S b)) (choose a (S (S b)))) (plus Z (choose a (S (S b)))) Z
                                          (cong Nat Nat (choose a (S b)) Z (λ x => (plus x (choose a (S (S b)))))
                                                (plus-equals-zero (choose a b) (choose a (S b))
                                                                  (eq-trans Nat (plus (choose a b) (choose a (S b))) (choose (S a) (S b)) Z
                                                                            (eq-refl (plus (choose a b) (choose a (S b))))
                                                                  e)))
                                (eq-trans Nat (plus Z (choose a (S (S b)))) (plus Z Z) Z
                                          (cong Nat Nat (choose a (S (S b))) Z (λ x => (plus Z x))
                                                ((pasb : (((choose a (S b)) = Z) -> ((choose a (S (S b))) = Z)))
                                                 (plus-equals-zero (choose a b) (choose a (S b))
                                                                   (eq-trans Nat (plus (choose a b) (choose a (S b))) (choose (S a) (S b)) Z
                                                                             (eq-refl (plus (choose a b) (choose a (S b))))
                                                                   e))))
                                (eq-refl Z))))) : (((choose (S a) (S b)) = Z) -> ((choose (S a) (S (S b))) = Z))))))))
                              a b)))

                           : (∀ (a : Nat) (b : Nat) -> (((choose a b) = Z) -> ((choose a (S b)) = Z)))))



(def 'choose-lemma '((λ n =>
                       (nat-ind
                        (λ x => ((choose x (S x)) = Z))
                        (eq-refl Z)
                        (λ k => (λ pk =>
                          (eq-trans Nat (choose (S k) (S (S k))) (plus (choose k (S k)) (choose k (S (S k)))) Z
                                    (eq-refl (plus (choose k (S k)) (choose k (S (S k)))))
                          (eq-trans Nat (plus (choose k (S k)) (choose k (S (S k)))) (plus Z (choose k (S (S k)))) Z
                                    (cong Nat Nat (choose k (S k)) Z (λ x => (plus x (choose k (S (S k))))) pk)
                          (eq-trans Nat (plus Z (choose k (S (S k)))) (plus Z Z) Z
                                    (cong Nat Nat (choose k (S (S k))) Z (λ x => (plus Z x)) (choose-equals-zero k (S k) pk ))
                          (eq-refl Z))))))
                        n))

                     : (∀ (n : Nat) -> ((choose n (S n)) = Z))))



(def 'sum-function-lemma '((λ a => (λ b => (λ f => (λ g => (λ rel =>
                             (nat-ind
                              (λ x => ((sum (S a) x f) = (sum (S a) x g)))
                              (eq-trans Nat (sum (S a) Z f) (f (S a)) (sum (S a) Z g)
                                        (eq-refl (f (S a)))
                              (eq-trans Nat (f (S a)) (f (S (sub1 (S a)))) (sum (S a) Z g)
                                        (eq-refl (f (S a)))
                              (eq-trans Nat (f (S (sub1 (S a)))) (g (S a)) (sum (S a) Z g)
                                        (rel (S a))
                              (eq-refl (g (S a))))))
                              (λ k => (λ pk =>
                                (eq-trans Nat (sum (S a) (S k) f) (plus (sum (S a) k f) (f (S (sub1 (plus (S a) (S k)))))) (sum (S a) (S k) g)
                                          (eq-refl (plus (sum (S a) k f) (f (plus (S a) (S k)))))
                                (eq-trans Nat (plus (sum (S a) k f) (f (S (sub1 (plus (S a) (S k)))))) (plus (sum (S a) k g) (f (S (sub1 (plus (S a) (S k)))))) (sum (S a) (S k) g)
                                          (cong Nat Nat (sum (S a) k f) (sum (S a) k g) (λ x => (plus x (f (S (sub1 (plus (S a) (S k))))))) pk)
                                (eq-trans Nat (plus (sum (S a) k g) (f (S (sub1 (plus (S a) (S k)))))) (plus (sum (S a) k g) (g (plus (S a) (S k)))) (sum (S a) (S k) g)
                                          (cong Nat Nat (f (S (sub1 (plus (S a) (S k))))) (g (plus (S a) (S k))) (λ x => (plus (sum (S a) k g) x)) (rel (plus (S a) (S k))))
                                (eq-refl (plus (sum (S a) k g) (g (plus (S a) (S k))))))))))
                              b))))))

                           : (∀ (a : Nat) (b : Nat) (f : (Nat -> Nat)) (g : (Nat -> Nat)) -> ((∀ (x : Nat) -> ((f (S (sub1 x))) = (g x))) -> ((sum (S a) b f) = (sum (S a) b g))))))



(def 'sum-function-lemma-general '((λ a => (λ b => (λ f =>
                                     (nat-ind
                                      (λ x => ((sum (S a) x (λ i => (f i i (S (sub1 i))))) = (sum (S a) x (λ i => (f i (S (sub1 i)) i)))))
                                      (eq-refl (f (S a) (S a) (S a)))
                                      (λ k => (λ pk =>
                                        (eq-trans Nat
                                                  (sum (S a) (S k) (λ i => (f i i (S (sub1 i)))))
                                                  (plus (sum (S a) k (λ i => (f i i (S (sub1 i))))) (f (plus (S a) (S k)) (plus (S a) (S k)) (S (sub1 (plus (S a) (S k))))))
                                                  (sum (S a) (S k) (λ i => (f i (S (sub1 i)) i)))
                                                  (eq-refl (plus (sum (S a) k (λ i => (f i i (S (sub1 i))))) (f (plus (S a) (S k)) (plus (S a) (S k)) (S (sub1 (plus (S a) (S k)))))))
                                        (eq-trans Nat
                                                  (plus (sum (S a) k (λ i => (f i i (S (sub1 i))))) (f (plus (S a) (S k)) (plus (S a) (S k)) (S (sub1 (plus (S a) (S k))))))
                                                  (plus (sum (S a) k (λ i => (f i (S (sub1 i)) i))) (f (plus (S a) (S k)) (plus (S a) (S k)) (S (sub1 (plus (S a) (S k))))))
                                                  (sum (S a) (S k) (λ i => (f i (S (sub1 i)) i)))
                                                  (cong Nat Nat
                                                        (sum (S a) k (λ i => (f i i (S (sub1 i)))))
                                                        (sum (S a) k (λ i => (f i (S (sub1 i)) i)))
                                                        (λ x => (plus x (f (plus (S a) (S k)) (plus (S a) (S k)) (S (sub1 (plus (S a) (S k)))))))
                                                        pk)
                                        (eq-trans Nat
                                                  (plus (sum (S a) k (λ i => (f i (S (sub1 i)) i))) (f (plus (S a) (S k)) (plus (S a) (S k)) (S (sub1 (plus (S a) (S k))))))
                                                  (plus (sum (S a) k (λ i => (f i (S (sub1 i)) i))) (f (plus (S a) (S k)) (S (sub1 (plus (S a) (S k)))) (plus (S a) (S k))))
                                                  (sum (S a) (S k) (λ i => (f i (S (sub1 i)) i)))
                                                  (eq-refl (plus (sum (S a) k (λ i => (f i (S (sub1 i)) i))) (f (plus (S a) (S k)) (S (plus (S a) k)) (S (plus (S a) k)))))
                                        (eq-refl (plus (sum (S a) k (λ i => (f i (S (sub1 i)) i))) (f (plus (S a) (S k)) (S (sub1 (plus (S a) (S k)))) (plus (S a) (S k))))))))))
                                      b))))

                                   : (∀ (a : Nat) (b : Nat) (f : (Nat -> Nat -> Nat -> Nat)) -> ((sum (S a) b (λ i => (f i i (S (sub1 i))))) = (sum (S a) b (λ i => (f i (S (sub1 i)) i)))))))



(def 'sum-equal-functions '((λ a => (λ b => (λ f => (λ g => (λ rel =>
                              (nat-ind
                               (λ x => ((sum a x f) = (sum a x g)))
                               (eq-trans Nat (sum a Z f) (f a) (sum a Z g)
                                         (eq-refl (f a))
                               (eq-trans Nat (f a) (g a) (sum a Z g)
                                         (rel a)
                               (eq-refl (g a))))
                               (λ k => (λ pk =>
                                 (eq-trans Nat (sum a (S k) f) (plus (sum a k f) (f (plus a (S k)))) (sum a (S k) g)
                                           (eq-refl (plus (sum a k f) (f (plus a (S k)))))
                                 (eq-trans Nat (plus (sum a k f) (f (plus a (S k)))) (plus (sum a k g) (f (plus a (S k)))) (sum a (S k) g)
                                           (cong Nat Nat (sum a k f) (sum a k g) (λ x => (plus x (f (plus a (S k))))) pk)
                                 (eq-trans Nat (plus (sum a k g) (f (plus a (S k)))) (plus (sum a k g) (g (plus a (S k)))) (sum a (S k) g)
                                           (cong Nat Nat (f (plus a (S k))) (g (plus a (S k))) (λ x => (plus (sum a k g) x)) (rel (plus a (S k))))
                                 (eq-refl (plus (sum a k g) (g (plus a (S k))))))))))
                               b))))))

                            : (∀ (a : Nat) (b : Nat) (f : (Nat -> Nat)) (g : (Nat -> Nat)) -> ((∀ (x : Nat) -> ((f x) = (g x))) -> ((sum a b f) = (sum a b g))))))



(def 'pascal-row '((λ n =>
                     (nat-ind
                      (λ x => ((exp (S (S Z)) x) = (sum Z x (λ i => (choose x i)))))
                      (eq-refl (S Z))
                      (λ k => (λ pk =>
                        (eq-trans Nat
                                  (exp (S (S Z)) (S k))
                                  (mult (S (S Z)) (exp (S (S Z)) k))
                                  (sum Z (S k) (λ i => (choose (S k) i)))
                                  (eq-refl (mult (S (S Z)) (exp (S (S Z)) k)))
                        (eq-trans Nat
                                  (mult (S (S Z)) (exp (S (S Z)) k))
                                  (mult (S (S Z)) (sum Z k (λ i => (choose k i))))
                                  (sum Z (S k) (λ i => (choose (S k) i)))
                                  (cong Nat Nat (exp (S (S Z)) k) (sum Z k (λ i => (choose k i))) (λ x => (mult (S (S Z)) x)) pk)
                        (eq-trans Nat
                                  (mult (S (S Z)) (sum Z k (λ i => (choose k i))))
                                  (sum Z k (λ i => (mult (S (S Z)) (choose k i))))
                                  (sum Z (S k) (λ i => (choose (S k) i)))
                                  (eq-symm Nat (sum Z k (λ i => (mult (S (S Z)) (choose k i)))) (mult (S (S Z)) (sum Z k (λ i => (choose k i))))
                                           (sum-factor Z k (S (S Z)) ((λ i => (choose k i)) : (Nat -> Nat)) ((λ i => (mult (S (S Z)) (choose k i))) : (Nat -> Nat))
                                                       (λ x => (eq-refl (mult (S (S Z)) (choose k x))))))
                        (eq-trans Nat
                                  (sum Z k (λ i => (mult (S (S Z)) (choose k i))))
                                  (sum Z k (λ i => (mult (choose k i) (S (S Z)))))
                                  (sum Z (S k) (λ i => (choose (S k) i)))
                                  (sum-equal-functions Z k ((λ i => (mult (S (S Z)) (choose k i))) : (Nat -> Nat)) ((λ i => (mult (choose k i) (S (S Z)))) : (Nat -> Nat))
                                                       (λ x => (mult-comm (S (S Z)) (choose k x))))
                        (eq-trans Nat
                                  (sum Z k (λ i => (mult (choose k i) (S (S Z)))))
                                  (sum Z k (λ i => (plus (choose k i) (choose k i))))
                                  (sum Z (S k) (λ i => (choose (S k) i)))
                                  (sum-equal-functions Z k ((λ i => (mult (choose k i) (S (S Z)))) : (Nat -> Nat)) ((λ i => (plus (choose k i) (choose k i))) : (Nat -> Nat))
                                                       (λ x => (eq-refl (plus (choose k x) (choose k x)))))
                        (eq-trans Nat
                                  (sum Z k (λ i => (plus (choose k i) (choose k i))))
                                  (plus (sum Z k (λ i => (choose k i))) (sum Z k (λ i => (choose k i))))
                                  (sum Z (S k) (λ i => (choose (S k) i)))
                                  (eq-symm Nat (plus (sum Z k (λ i => (choose k i))) (sum Z k (λ i => (choose k i)))) (sum Z k (λ i => (plus (choose k i) (choose k i))))
                                           (split-sum Z k
                                                      ((λ i => (choose k i)) : (Nat -> Nat))
                                                      ((λ i => (choose k i)) : (Nat -> Nat)) ((λ i => (plus (choose k i) (choose k i))) : (Nat -> Nat))
                                                      (λ x => (eq-refl (plus (choose k x) (choose k x))))))
                        (eq-trans Nat
                                  (plus (sum Z k (λ i => (choose k i))) (sum Z k (λ i => (choose k i))))
                                  (plus (plus (choose k (S k)) (sum Z k (λ i => (choose k i)))) (sum Z k (λ i => (choose k i))))
                                  (sum Z (S k) (λ i => (choose (S k) i)))
                                  (cong Nat Nat (sum Z k (λ i => (choose k i))) (plus (choose k (S k)) (sum Z k (λ i => (choose k i)))) (λ x => (plus x (sum Z k (λ i => (choose k i)))))
                                        (eq-trans Nat (sum Z k (λ i => (choose k i))) (plus Z (sum Z k (λ i => (choose k i)))) (plus (choose k (S k)) (sum Z k (λ i => (choose k i))))
                                                  (eq-symm Nat (plus Z (sum Z k (λ i => (choose k i)))) (sum Z k (λ i => (choose k i))) (plus-zero-left (sum Z k (λ i => (choose k i)))))
                                        (cong Nat Nat Z (choose k (S k)) (λ x => (plus x (sum Z k (λ i => (choose k i)))))
                                              (eq-symm Nat (choose k (S k)) Z (choose-lemma k)))))
                        (eq-trans Nat
                                  (plus (plus (choose k (S k)) (sum Z k (λ i => (choose k i)))) (sum Z k (λ i => (choose k i))))
                                  (plus (sum Z (S k) (λ i => (choose k i))) (sum Z k (λ i => (choose k i))))
                                  (sum Z (S k) (λ i => (choose (S k) i)))
                                  (cong Nat Nat (plus (choose k (S k)) (sum Z k (λ i => (choose k i)))) (sum Z (S k) (λ i => (choose k i))) (λ x => (plus x (sum Z k (λ i => (choose k i)))))
                                        (eq-trans Nat
                                                  (plus (choose k (S k)) (sum Z k (λ i => (choose k i))))
                                                  (plus (choose k (plus Z (S k))) (sum Z k (λ i => (choose k i)))) (sum Z (S k) (λ i => (choose k i)))
                                                  (cong Nat Nat (S k) (plus Z (S k)) (λ x => (plus (choose k x) (sum Z k (λ i => (choose k i)))))
                                                        (eq-symm Nat (plus Z (S k)) (S k) (plus-zero-left (S k))))
                                        (sum-add-term-last Z k (λ i => (choose k i)))))
                        (eq-trans Nat
                                  (plus (sum Z (S k) (λ i => (choose k i))) (sum Z k (λ i => (choose k i))))
                                  (plus (sum Z (S k) (λ i => (choose k i))) (sum (S Z) k (λ i => (choose k (sub1 i)))))
                                  (sum Z (S k) (λ i => (choose (S k) i)))
                                  (cong Nat Nat (sum Z k (λ i => (choose k i))) (sum (S Z) k (λ i => (choose k (sub1 i)))) (λ x => (plus (sum Z (S k) (λ i => (choose k i))) x))
                                        (shift-bounds Z k ((λ i => (choose k i)) : (Nat -> Nat)) ((λ i => (choose k (sub1 i))) : (Nat -> Nat))
                                                      (λ x => (eq-refl (choose k (sub1 x))))))
                        (eq-trans Nat
                                  (plus (sum Z (S k) (λ i => (choose k i))) (sum (S Z) k (λ i => (choose k (sub1 i)))))
                                  (plus (plus (choose k Z) (sum (S Z) k (λ i => (choose k i)))) (sum (S Z) k (λ i => (choose k (sub1 i)))))
                                  (sum Z (S k) (λ i => (choose (S k) i)))
                                  (cong Nat Nat
                                        (sum Z (S k) (λ i => (choose k i)))
                                        (plus (choose k Z) (sum (S Z) k (λ i => (choose k i)))) (λ x => (plus x (sum (S Z) k (λ i => (choose k (sub1 i))))))
                                        (eq-symm Nat (plus (choose k Z) (sum (S Z) k (λ i => (choose k i)))) (sum Z (S k) (λ i => (choose k i)))
                                                 (sum-add-term-first Z k (λ i => (choose k i)))))
                        (eq-trans Nat
                                  (plus (plus (choose k Z) (sum (S Z) k (λ i => (choose k i)))) (sum (S Z) k (λ i => (choose k (sub1 i)))))
                                  (plus (choose k Z) (plus (sum (S Z) k (λ i => (choose k i))) (sum (S Z) k (λ i => (choose k (sub1 i))))))
                                  (sum Z (S k) (λ i => (choose (S k) i)))
                                  (eq-symm Nat
                                           (plus (choose k Z) (plus (sum (S Z) k (λ i => (choose k i))) (sum (S Z) k (λ i => (choose k (sub1 i))))))
                                           (plus (plus (choose k Z) (sum (S Z) k (λ i => (choose k i)))) (sum (S Z) k (λ i => (choose k (sub1 i)))))
                                           (plus-assoc (choose k Z) (sum (S Z) k (λ i => (choose k i))) (sum (S Z) k (λ i => (choose k (sub1 i))))))
                        (eq-trans Nat
                                  (plus (choose k Z) (plus (sum (S Z) k (λ i => (choose k i))) (sum (S Z) k (λ i => (choose k (sub1 i))))))
                                  (plus (choose k Z) (sum (S Z) k (λ i => (plus (choose k i) (choose k (sub1 i))))))
                                  (sum Z (S k) (λ i => (choose (S k) i)))
                                  (cong Nat Nat
                                        (plus (sum (S Z) k (λ i => (choose k i))) (sum (S Z) k (λ i => (choose k (sub1 i)))))
                                        (sum (S Z) k (λ i => (plus (choose k i) (choose k (sub1 i))))) (λ x => (plus (choose k Z) x))
                                        (split-sum (S Z) k
                                                   ((λ i => (choose k i)) : (Nat -> Nat))
                                                   ((λ i => (choose k (sub1 i))) : (Nat -> Nat)) ((λ i => (plus (choose k i) (choose k (sub1 i)))) : (Nat -> Nat))
                                                   (λ x => (eq-refl (plus (choose k x) (choose k (sub1 x)))))))
                        (eq-trans Nat
                                  (plus (choose k Z) (sum (S Z) k (λ i => (plus (choose k i) (choose k (sub1 i))))))
                                  (plus (choose k Z) (sum (S Z) k (λ i => (plus (choose k (S (sub1 i))) (choose k (sub1 (S (sub1 i))))))))
                                  (sum Z (S k) (λ i => (choose (S k) i)))
                                  (cong Nat Nat
                                        (sum (S Z) k (λ i => (plus (choose k i) (choose k (sub1 i)))))
                                        (sum (S Z) k (λ i => (plus (choose k (S (sub1 i))) (choose k (sub1 (S (sub1 i))))))) (λ x => (plus (choose k Z) x))
                                        (sum-function-lemma Z k ((λ i => (plus (choose k i) (choose k (sub1 i)))) : (Nat -> Nat)) ((λ i => (plus (choose k (S (sub1 i))) (choose k (sub1 (S (sub1 i)))))) : (Nat -> Nat))
                                                            (λ x => (eq-refl (plus (choose k (S (sub1 x))) (choose k (sub1 (S (sub1 x)))))))))
                        (eq-trans Nat
                                  (plus (choose k Z) (sum (S Z) k (λ i => (plus (choose k (S (sub1 i))) (choose k (sub1 (S (sub1 i))))))))
                                  (plus (choose k Z) (sum (S Z) k (λ i => (plus (choose k (sub1 (S (sub1 i)))) (choose k (S (sub1 i)))))))
                                  (sum Z (S k) (λ i => (choose (S k) i)))
                                  (cong Nat Nat
                                        (sum (S Z) k (λ i => (plus (choose k (S (sub1 i))) (choose k (sub1 (S (sub1 i)))))))
                                        (sum (S Z) k (λ i => (plus (choose k (sub1 (S (sub1 i)))) (choose k (S (sub1 i)))))) (λ x => (plus (choose k Z) x))
                                        (sum-equal-functions (S Z) k
                                                             ((λ i => (plus (choose k (S (sub1 i))) (choose k (sub1 (S (sub1 i)))))) : (Nat -> Nat))
                                                             ((λ i => (plus (choose k (sub1 (S (sub1 i)))) (choose k (S (sub1 i))))) : (Nat -> Nat))
                                                             (λ x => (plus-comm (choose k (S (sub1 x))) (choose k (sub1 (S (sub1 x))))))))
                        (eq-trans Nat
                                  (plus (choose k Z) (sum (S Z) k (λ i => (plus (choose k (sub1 (S (sub1 i)))) (choose k (S (sub1 i)))))))
                                  (plus (choose k Z) (sum (S Z) k (λ i => (choose (S k) (S (sub1 i))))))
                                  (sum Z (S k) (λ i => (choose (S k) i)))
                                  (cong Nat Nat
                                        (sum (S Z) k (λ i => (plus (choose k (sub1 (S (sub1 i)))) (choose k (S (sub1 i))))))
                                        (sum (S Z) k (λ i => (choose (S k) (S (sub1 i)))))
                                        (λ x => (plus (choose k Z) x))
                                        (sum-equal-functions (S Z) k
                                                             ((λ i => (plus (choose k (sub1 (S (sub1 i)))) (choose k (S (sub1 i))))) : (Nat -> Nat))
                                                             ((λ i => (choose (S k) (S (sub1 i)))) : (Nat -> Nat))
                                                             (λ x => (eq-refl (plus (choose k (sub1 x)) (choose k (S (sub1 x))))))))
                        (eq-trans Nat
                                  (plus (choose k Z) (sum (S Z) k (λ i => (choose (S k) (S (sub1 i))))))
                                  (plus (choose k Z) (sum (S Z) k (λ i => (choose (S k) i))))
                                  (sum Z (S k) (λ i => (choose (S k) i)))
                                  (cong Nat Nat (sum (S Z) k (λ i => (choose (S k) (S (sub1 i))))) (sum (S Z) k (λ i => (choose (S k) i))) (λ x => (plus (choose k Z) x))
                                        (eq-symm Nat (sum (S Z) k (λ i => (choose (S k) i))) (sum (S Z) k (λ i => (choose (S k) (S (sub1 i)))))
                                                 (sum-function-lemma Z k ((λ i => (choose (S k) i)) : (Nat -> Nat)) ((λ i => (choose (S k) (S (sub1 i)))) : (Nat -> Nat))
                                                                     (λ x => (eq-refl (choose (S k) (S (sub1 x))))))))
                        (eq-trans Nat
                                  (plus (choose k Z) (sum (S Z) k (λ i => (choose (S k) i))))
                                  (plus (choose (S k) Z) (sum (S Z) k (λ i => (choose (S k) i))))
                                  (sum Z (S k) (λ i => (choose (S k) i)))
                                  (cong Nat Nat (choose k Z) (choose (S k) Z) (λ x => (plus x (sum (S Z) k (λ i => (choose (S k) i)))))
                                        (eq-trans Nat (choose k Z) (S Z) (choose (S k) Z)
                                                  (choose-zero k)
                                        (eq-refl (S Z))))
                        (sum-add-term-first Z k (λ i => (choose (S k) i))))))))))))))))))))))
                      n))

                   : (∀ (n : Nat) -> ((exp (S (S Z)) n) = (sum Z n (λ i => (choose n i)))))))



(def 'mult-insert '((λ a => (λ b => (λ c => (λ d =>
                      (eq-trans Nat
                                (mult a (mult b (mult c d)))
                                (mult (mult a b) (mult c d))
                                (mult b (mult (mult a c) d))
                                (mult-assoc a b (mult c d))
                      (eq-trans Nat
                                (mult (mult a b) (mult c d))
                                (mult (mult b a) (mult c d))
                                (mult b (mult (mult a c) d))
                                (cong Nat Nat (mult a b) (mult b a) (λ x => (mult x (mult c d))) (mult-comm a b))
                      (eq-trans Nat
                                (mult (mult b a) (mult c d))
                                (mult b (mult a (mult c d)))
                                (mult b (mult (mult a c) d))
                                (eq-symm Nat (mult b (mult a (mult c d))) (mult (mult b a) (mult c d)) (mult-assoc b a (mult c d)))
                      (cong Nat Nat
                            (mult a (mult c d))
                            (mult (mult a c) d)
                            (λ x => (mult b x))
                            (mult-assoc a c d)))))))))

                    : (∀ (a : Nat) (b : Nat) (c : Nat) (d : Nat) -> ((mult a (mult b (mult c d))) = (mult b (mult (mult a c) d))))))



(def 'mult-insert-right '((λ a => (λ b => (λ c => (λ d =>
                            (eq-trans Nat
                                      (mult a (mult b (mult c d)))
                                      (mult b (mult (mult a c) d))
                                      (mult b (mult c (mult a d)))
                                      (mult-insert a b c d)
                            (eq-trans Nat
                                      (mult b (mult (mult a c) d))
                                      (mult b (mult (mult c a) d))
                                      (mult b (mult c (mult a d)))
                                      (cong Nat Nat (mult a c) (mult c a) (λ x => (mult b (mult x d))) (mult-comm a c))
                            (eq-symm Nat
                                     (mult b (mult c (mult a d)))
                                     (mult b (mult (mult c a) d))
                                     (cong Nat Nat (mult c (mult a d)) (mult (mult c a) d) (λ x => (mult b x)) (mult-assoc c a d)))))))))

                    : (∀ (a : Nat) (b : Nat) (c : Nat) (d : Nat) -> ((mult a (mult b (mult c d))) = (mult b (mult c (mult a d)))))))



(def 'sub-plusses '((λ a => (λ b => (λ c =>
                      (nat-ind
                       (λ x => ((sub a b) = (sub (plus x a) (plus x b))))
                       (eq-trans Nat (sub a b) (sub (plus Z a) b) (sub (plus Z a) (plus Z b))
                                 (cong Nat Nat a (plus Z a) (λ x => (sub x b))
                                       (eq-symm Nat (plus Z a) a (plus-zero-left a)))
                       (cong Nat Nat b (plus Z b) (λ x => (sub (plus Z a) x))
                             (eq-symm Nat (plus Z b) b (plus-zero-left b))))
                       (λ k => (λ pk =>
                         (eq-trans Nat (sub a b) (sub (plus k a) (plus k b)) (sub (plus (S k) a) (plus (S k) b))
                                   pk
                         (eq-trans Nat (sub (plus k a) (plus k b)) (sub (S (plus k a)) (S (plus k b))) (sub (plus (S k) a) (plus (S k) b))
                                   (eq-symm Nat (sub (S (plus k a)) (S (plus k b))) (sub (plus k a) (plus k b))
                                            (subS (plus k a) (plus k b)))
                         (eq-trans Nat (sub (S (plus k a)) (S (plus k b))) (sub (plus (S k) a) (S (plus k b))) (sub (plus (S k) a) (plus (S k) b))
                                   (cong Nat Nat (S (plus k a)) (plus (S k) a) (λ x => (sub x (S (plus k b))))
                                         (eq-symm Nat (plus (S k) a) (S (plus k a)) (plus-lemma k a)))
                         (cong Nat Nat (S (plus k b)) (plus (S k) b) (λ x => (sub (plus (S k) a) x))
                               (eq-symm Nat (plus (S k) b) (S (plus k b)) (plus-lemma k b))))))))
                       c))))

                    : (∀ (a : Nat) (b : Nat) (c : Nat) -> ((sub a b) = (sub (plus c a) (plus c b))))))



(def 'sum-sub-S '((λ a => (λ b => (λ c => (λ f =>
                    (nat-ind
                     (λ x => ((leq x c) -> ((sum a x (λ i => (f i (S (sub (plus a c) i))))) = (sum a x (λ i => (f i (sub (S (plus a c)) i)))))))
                     ((λ l =>
                        (eq-trans Nat
                                  (sum a Z (λ i => (f i (S (sub (plus a c) i)))))
                                  (f a (S (sub (plus a c) a)))
                                  (sum a Z (λ i => (f i (sub (S (plus a c)) i))))
                                  (eq-refl (f a (S (sub (plus a c) a))))
                        (eq-trans Nat
                                  (f a (S (sub (plus a c) a)))
                                  (f a (S c))
                                  (sum a Z (λ i => (f i (sub (S (plus a c)) i))))
                                  (cong Nat Nat
                                        (sub (plus a c) a)
                                        c
                                        (λ x => (f a (S x)))
                                        (sub-plus-cancel a c))
                        (eq-trans Nat
                                  (f a (S c))
                                  (f a (sub (S c) Z))
                                  (sum a Z (λ i => (f i (sub (S (plus a c)) i))))
                                  (eq-refl (f a (S c)))
                        (eq-trans Nat
                                  (f a (sub (S c) Z))
                                  (f a (sub (plus a (S c)) (plus a Z)))
                                  (sum a Z (λ i => (f i (sub (S (plus a c)) i))))
                                  (cong Nat Nat
                                        (sub (S c) Z)
                                        (sub (plus a (S c)) (plus a Z))
                                        (λ x => (f a x))
                                        (sub-plusses (S c) Z a))
                        (eq-refl (f a (sub (S (plus a c)) a))))))))
                      : ((leq Z c) -> ((sum a Z (λ i => (f i (S (sub (plus a c) i))))) = (sum a Z (λ i => (f i (sub (S (plus a c)) i)))))))
                     (λ k => (λ pk => ((λ l =>
                       (eq-trans Nat
                                 (sum a (S k) (λ i => (f i (S (sub (plus a c) i)))))
                                 (plus (sum a k (λ i => (f i (S (sub (plus a c) i))))) (f (plus a (S k)) (S (sub (plus a c) (plus a (S k))))))
                                 (sum a (S k) (λ i => (f i (sub (S (plus a c)) i))))
                                 (eq-refl (plus (sum a k (λ i => (f i (S (sub (plus a c) i))))) (f (plus a (S k)) (S (sub (plus a c) (plus a (S k)))))))
                       (eq-trans Nat
                                 (plus (sum a k (λ i => (f i (S (sub (plus a c) i))))) (f (plus a (S k)) (S (sub (plus a c) (plus a (S k))))))
                                 (plus (sum a k (λ i => (f i (sub (S (plus a c)) i)))) (f (plus a (S k)) (S (sub (plus a c) (plus a (S k))))))
                                 (sum a (S k) (λ i => (f i (sub (S (plus a c)) i))))
                                 (cong Nat Nat
                                       (sum a k (λ i => (f i (S (sub (plus a c) i)))))
                                       (sum a k (λ i => (f i (sub (S (plus a c)) i))))
                                       (λ x => (plus x (f (plus a (S k)) (S (sub (plus a c) (plus a (S k)))))))
                                       ((pk : ((leq k c) -> ((sum a k (λ i => (f i (S (sub (plus a c) i))))) = (sum a k (λ i => (f i (sub (S (plus a c)) i)))))))
                                        (leq-lemma-left k c l)))
                       (eq-trans Nat
                                 (plus (sum a k (λ i => (f i (sub (S (plus a c)) i)))) (f (plus a (S k)) (S (sub (plus a c) (plus a (S k))))))
                                 (plus (sum a k (λ i => (f i (sub (S (plus a c)) i)))) (f (plus a (S k)) (S (sub c (S k)))))
                                 (sum a (S k) (λ i => (f i (sub (S (plus a c)) i))))
                                 (cong Nat Nat
                                       (sub (plus a c) (plus a (S k)))
                                       (sub c (S k))
                                       (λ x => (plus (sum a k (λ i => (f i (sub (S (plus a c)) i)))) (f (plus a (S k)) (S x))))
                                       (eq-symm Nat
                                                (sub c (S k))
                                                (sub (plus a c) (plus a (S k)))
                                                (sub-plusses c (S k) a)))
                       (eq-trans Nat
                                 (plus (sum a k (λ i => (f i (sub (S (plus a c)) i)))) (f (plus a (S k)) (S (sub c (S k)))))
                                 (plus (sum a k (λ i => (f i (sub (S (plus a c)) i)))) (f (plus a (S k)) (sub (S c) (S k))))
                                 (sum a (S k) (λ i => (f i (sub (S (plus a c)) i))))
                                 (cong Nat Nat
                                       (S (sub c (S k)))
                                       (sub (S c) (S k))
                                       (λ x => (plus (sum a k (λ i => (f i (sub (S (plus a c)) i)))) (f (plus a (S k)) x)))
                                       (eq-symm Nat
                                                (sub (S c) (S k))
                                                (S (sub c (S k)))
                                                (sub-lemma c (S k) l)))
                       (eq-trans Nat
                                 (plus (sum a k (λ i => (f i (sub (S (plus a c)) i)))) (f (plus a (S k)) (sub (S c) (S k))))
                                 (plus (sum a k (λ i => (f i (sub (S (plus a c)) i)))) (f (plus a (S k)) (sub (plus a (S c)) (plus a (S k)))))
                                 (sum a (S k) (λ i => (f i (sub (S (plus a c)) i))))
                                 (cong Nat Nat
                                       (sub (S c) (S k))
                                       (sub (plus a (S c)) (plus a (S k)))
                                       (λ x => (plus (sum a k (λ i => (f i (sub (S (plus a c)) i)))) (f (plus a (S k)) x)))
                                       (sub-plusses (S c) (S k) a))
                       (eq-refl (plus (sum a k (λ i => (f i (sub (S (plus a c)) i)))) (f (plus a (S k)) (sub (S (plus a c)) (plus a (S k)))))))))))) : ((leq (S k) c) -> ((sum a (S k) (λ i => (f i (S (sub (plus a c) i))))) = (sum a (S k) (λ i => (f i (sub (S (plus a c)) i)))))))))
                     b))))) 

                  : (∀ (a : Nat) (b : Nat) (c : Nat) (f : (Nat -> Nat -> Nat)) -> ((leq b c) -> ((sum a b (λ i => (f i (S (sub (plus a c) i))))) = (sum a b (λ i => (f i (sub (S (plus a c)) i)))))))))



(def 'sum-from-zero-sub-S '((λ n => (λ c => (λ f => (λ l =>
                              (eq-trans Nat
                                        (sum Z n (λ i => (f i (S (sub c i)))))
                                        (sum Z n (λ i => (f i (S (sub (plus Z c) i)))))
                                        (sum Z n (λ i => (f i (sub (S c) i))))
                                        (cong Nat Nat
                                              c
                                              (plus Z c)
                                              (λ x => (sum Z n (λ i => (f i (S (sub x i))))))
                                              (eq-symm Nat
                                                       (plus Z c)
                                                       c
                                                       (plus-zero-left c)))
                              (eq-trans Nat
                                        (sum Z n (λ i => (f i (S (sub (plus Z c) i)))))
                                        (sum Z n (λ i => (f i (sub (S (plus Z c)) i))))
                                        (sum Z n (λ i => (f i (sub (S c) i))))
                                        (sum-sub-S Z n c (λ x => (λ y => (f x y))) l)
                              (cong Nat Nat
                                    (plus Z c)
                                    c
                                    (λ x => (sum Z n (λ i => (f i (sub (S x) i)))))
                                    (plus-zero-left c))))))))

                            : (∀ (n : Nat) (c : Nat) (f : (Nat -> Nat -> Nat)) -> ((leq n c) -> ((sum Z n (λ i => (f i (S (sub c i))))) = (sum Z n (λ i => (f i (sub (S c) i)))))))))



(def 'binomial-theorem '((λ a => (λ b => (λ n =>
                           (nat-ind
                            (λ x => ((exp (plus a b) x) = (sum Z x (λ i => (mult (choose x i) (mult (exp a (sub x i)) (exp b i)))))))
                            (eq-refl (S Z))
                            (λ k => (λ pk =>
                              (eq-trans Nat
                                        (exp (plus a b) (S k))
                                        (mult (plus a b) (exp (plus a b) k))
                                        (sum Z (S k) (λ i => (mult (choose (S k) i) (mult (exp a (sub (S k) i)) (exp b i)))))
                                        (eq-refl (mult (plus a b) (exp (plus a b) k)))
                              (eq-trans Nat
                                        (mult (plus a b) (exp (plus a b) k))
                                        (mult (plus a b) (sum Z k (λ i => (mult (choose k i) (mult (exp a (sub k i)) (exp b i))))))
                                        (sum Z (S k) (λ i => (mult (choose (S k) i) (mult (exp a (sub (S k) i)) (exp b i)))))
                                        (cong Nat Nat
                                              (exp (plus a b) k)
                                              (sum Z k (λ i => (mult (choose k i) (mult (exp a (sub k i)) (exp b i)))))
                                              (λ x => (mult (plus a b) x))
                                              pk)
                              (eq-trans Nat
                                        (mult (plus a b) (sum Z k (λ i => (mult (choose k i) (mult (exp a (sub k i)) (exp b i))))))
                                        (sum Z k (λ i => (mult (plus a b) (mult (choose k i) (mult (exp a (sub k i)) (exp b i))))))
                                        (sum Z (S k) (λ i => (mult (choose (S k) i) (mult (exp a (sub (S k) i)) (exp b i)))))
                                        (eq-symm Nat
                                                 (sum Z k (λ i => (mult (plus a b) (mult (choose k i) (mult (exp a (sub k i)) (exp b i))))))
                                                 (mult (plus a b) (sum Z k (λ i => (mult (choose k i) (mult (exp a (sub k i)) (exp b i))))))
                                                 (sum-factor Z k (plus a b)
                                                             ((λ i => (mult (choose k i) (mult (exp a (sub k i)) (exp b i)))) : (Nat -> Nat))
                                                             ((λ i => (mult (plus a b) (mult (choose k i) (mult (exp a (sub k i)) (exp b i))))) : (Nat -> Nat))
                                                             (λ x => (eq-refl (mult (plus a b) (mult (choose k x) (mult (exp a (sub k x)) (exp b x))))))))
                              (eq-trans Nat
                                        (sum Z k (λ i => (mult (plus a b) (mult (choose k i) (mult (exp a (sub k i)) (exp b i))))))
                                        (sum Z k (λ i => (plus (mult a (mult (choose k i) (mult (exp a (sub k i)) (exp b i)))) (mult b (mult (choose k i) (mult (exp a (sub k i)) (exp b i)))))))
                                        (sum Z (S k) (λ i => (mult (choose (S k) i) (mult (exp a (sub (S k) i)) (exp b i)))))
                                        (sum-equal-functions Z k
                                                             ((λ i => (mult (plus a b) (mult (choose k i) (mult (exp a (sub k i)) (exp b i))))) : (Nat -> Nat))
                                                             ((λ i => (plus (mult a (mult (choose k i) (mult (exp a (sub k i)) (exp b i)))) (mult b (mult (choose k i) (mult (exp a (sub k i)) (exp b i)))))) : (Nat -> Nat))
                                                             (λ x => (mult-right-dist a b (mult (choose k x) (mult (exp a (sub k x)) (exp b x))))))
                              (eq-trans Nat
                                        (sum Z k (λ i => (plus (mult a (mult (choose k i) (mult (exp a (sub k i)) (exp b i)))) (mult b (mult (choose k i) (mult (exp a (sub k i)) (exp b i)))))))
                                        (sum Z k (λ i => (plus (mult (choose k i) (mult (mult a (exp a (sub k i))) (exp b i))) (mult b (mult (choose k i) (mult (exp a (sub k i)) (exp b i)))))))
                                        (sum Z (S k) (λ i => (mult (choose (S k) i) (mult (exp a (sub (S k) i)) (exp b i)))))
                                        (sum-equal-functions Z k
                                                             ((λ i => (plus (mult a (mult (choose k i) (mult (exp a (sub k i)) (exp b i)))) (mult b (mult (choose k i) (mult (exp a (sub k i)) (exp b i)))))) : (Nat -> Nat))
                                                             ((λ i => (plus (mult (choose k i) (mult (mult a (exp a (sub k i))) (exp b i))) (mult b (mult (choose k i) (mult (exp a (sub k i)) (exp b i)))))) : (Nat -> Nat))
                                                             (λ x => (cong Nat Nat
                                                                           (mult a (mult (choose k x) (mult (exp a (sub k x)) (exp b x))))
                                                                           (mult (choose k x) (mult (mult a (exp a (sub k x))) (exp b x)))
                                                                           (λ y => (plus y (mult b (mult (choose k x) (mult (exp a (sub k x)) (exp b x))))))
                                                                           (mult-insert a (choose k x) (exp a (sub k x)) (exp b x)))))
                              (eq-trans Nat
                                        (sum Z k (λ i => (plus (mult (choose k i) (mult (mult a (exp a (sub k i))) (exp b i))) (mult b (mult (choose k i) (mult (exp a (sub k i)) (exp b i)))))))
                                        (sum Z k (λ i => (plus (mult (choose k i) (mult (mult a (exp a (sub k i))) (exp b i))) (mult (choose k i) (mult (exp a (sub k i)) (mult b (exp b i)))))))
                                        (sum Z (S k) (λ i => (mult (choose (S k) i) (mult (exp a (sub (S k) i)) (exp b i)))))
                                        (sum-equal-functions Z k
                                                             ((λ i => (plus (mult (choose k i) (mult (mult a (exp a (sub k i))) (exp b i))) (mult b (mult (choose k i) (mult (exp a (sub k i)) (exp b i)))))) : (Nat -> Nat))
                                                             ((λ i => (plus (mult (choose k i) (mult (mult a (exp a (sub k i))) (exp b i))) (mult (choose k i) (mult (exp a (sub k i)) (mult b (exp b i)))))) : (Nat -> Nat))
                                                             (λ x => (cong Nat Nat
                                                                           (mult b (mult (choose k x) (mult (exp a (sub k x)) (exp b x))))
                                                                           (mult (choose k x) (mult (exp a (sub k x)) (mult b (exp b x))))
                                                                           (λ y => (plus (mult (choose k x) (mult (mult a (exp a (sub k x))) (exp b x))) y))
                                                                           (mult-insert-right b (choose k x) (exp a (sub k x)) (exp b x)))))
                              (eq-trans Nat
                                        (sum Z k (λ i => (plus (mult (choose k i) (mult (mult a (exp a (sub k i))) (exp b i))) (mult (choose k i) (mult (exp a (sub k i)) (mult b (exp b i)))))))
                                        (sum Z k (λ i => (plus (mult (choose k i) (mult (exp a (S (sub k i))) (exp b i))) (mult (choose k i) (mult (exp a (sub k i)) (exp b (S i)))))))
                                        (sum Z (S k) (λ i => (mult (choose (S k) i) (mult (exp a (sub (S k) i)) (exp b i)))))
                                        (sum-equal-functions Z k
                                                             ((λ i => (plus (mult (choose k i) (mult (mult a (exp a (sub k i))) (exp b i))) (mult (choose k i) (mult (exp a (sub k i)) (mult b (exp b i)))))) : (Nat -> Nat))
                                                             ((λ i => (plus (mult (choose k i) (mult (exp a (S (sub k i))) (exp b i))) (mult (choose k i) (mult (exp a (sub k i)) (exp b (S i)))))) : (Nat -> Nat))
                                                             (λ x => (eq-refl (plus (mult (choose k x) (mult (mult a (exp a (sub k x))) (exp b x))) (mult (choose k x) (mult (exp a (sub k x)) (mult b (exp b x))))))))
                              (eq-trans Nat
                                        (sum Z k (λ i => (plus (mult (choose k i) (mult (exp a (S (sub k i))) (exp b i))) (mult (choose k i) (mult (exp a (sub k i)) (exp b (S i)))))))
                                        (sum Z k (λ i => (plus (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i))) (mult (choose k i) (mult (exp a (sub k i)) (exp b (S i)))))))
                                        (sum Z (S k) (λ i => (mult (choose (S k) i) (mult (exp a (sub (S k) i)) (exp b i)))))
                                        (sum-from-zero-sub-S k k
                                                             (λ x => (λ y => (plus (mult (choose k x) (mult (exp a y) (exp b x))) (mult (choose k x) (mult (exp a (sub k x)) (exp b (S x))))))) (leq-refl k))
                              (eq-trans Nat
                                        (sum Z k (λ i => (plus (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i))) (mult (choose k i) (mult (exp a (sub k i)) (exp b (S i)))))))
                                        (plus (sum Z k (λ i => (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i))))) (sum Z k (λ i => (mult (choose k i) (mult (exp a (sub k i)) (exp b (S i)))))))
                                        (sum Z (S k) (λ i => (mult (choose (S k) i) (mult (exp a (sub (S k) i)) (exp b i)))))
                                        (eq-symm Nat
                                                 (plus (sum Z k (λ i => (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i))))) (sum Z k (λ i => (mult (choose k i) (mult (exp a (sub k i)) (exp b (S i)))))))
                                                 (sum Z k (λ i => (plus (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i))) (mult (choose k i) (mult (exp a (sub k i)) (exp b (S i)))))))
                                                 (split-sum Z k
                                                            ((λ i => (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i)))) : (Nat -> Nat))
                                                            ((λ i => (mult (choose k i) (mult (exp a (sub k i)) (exp b (S i))))) : (Nat -> Nat))
                                                            ((λ i => (plus (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i))) (mult (choose k i) (mult (exp a (sub k i)) (exp b (S i)))))) : (Nat -> Nat))
                                                            (λ x => (eq-refl (plus (mult (choose k x) (mult (exp a (sub (S k) x)) (exp b x))) (mult (choose k x) (mult (exp a (sub k x)) (exp b (S x)))))))))
                              (eq-trans Nat
                                        (plus (sum Z k (λ i => (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i))))) (sum Z k (λ i => (mult (choose k i) (mult (exp a (sub k i)) (exp b (S i)))))))
                                        (plus (plus (mult (choose k (S k)) (mult (exp a (sub (S k) (S k))) (exp b (S k)))) (sum Z k (λ i => (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i)))))) (sum Z k (λ i => (mult (choose k i) (mult (exp a (sub k i)) (exp b (S i)))))))
                                        (sum Z (S k) (λ i => (mult (choose (S k) i) (mult (exp a (sub (S k) i)) (exp b i)))))
                                        (cong Nat Nat
                                              (sum Z k (λ i => (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i))))) ;jan 13 16 17 2020 mid island allergy (S (sub k i))
                                              (plus (mult (choose k (S k)) (mult (exp a (sub (S k) (S k))) (exp b (S k)))) (sum Z k (λ i => (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i))))))
                                              (λ x => (plus x (sum Z k (λ i => (mult (choose k i) (mult (exp a (sub k i)) (exp b (S i))))))))
                                              (eq-trans Nat
                                                        (sum Z k (λ i => (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i)))))
                                                        (plus Z (sum Z k (λ i => (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i))))))
                                                        (plus (mult (choose k (S k)) (mult (exp a (sub (S k) (S k))) (exp b (S k)))) (sum Z k (λ i => (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i))))))
                                                        (eq-symm Nat
                                                                 (plus Z (sum Z k (λ i => (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i))))))
                                                                 (sum Z k (λ i => (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i)))))
                                                                 (plus-zero-left (sum Z k (λ i => (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i)))))))
                                              (eq-trans Nat
                                                        (plus Z (sum Z k (λ i => (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i))))))
                                                        (plus (mult Z (mult (exp a (sub (S k) (S k))) (exp b (S k)))) (sum Z k (λ i => (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i))))))
                                                        (plus (mult (choose k (S k)) (mult (exp a (sub (S k) (S k))) (exp b (S k)))) (sum Z k (λ i => (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i))))))
                                                        (cong Nat Nat
                                                              Z
                                                              (mult Z (mult (exp a (sub (S k) (S k))) (exp b (S k))))
                                                              (λ x => (plus x (sum Z k (λ i => (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i)))))))
                                                              (eq-symm Nat
                                                                       (mult Z (mult (exp a (sub (S k) (S k))) (exp b (S k))))
                                                                       Z
                                                                       (mult-zero-left (mult (exp a (sub (S k) (S k))) (exp b (S k))))))
                                              (cong Nat Nat
                                                    Z
                                                    (choose k (S k))
                                                    (λ x => (plus (mult x (mult (exp a (sub (S k) (S k))) (exp b (S k)))) (sum Z k (λ i => (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i)))))))
                                                    (eq-symm Nat
                                                             (choose k (S k))
                                                             Z
                                                             (choose-lemma k))))))
                              (eq-trans Nat
                                        (plus (plus (mult (choose k (S k)) (mult (exp a (sub (S k) (S k))) (exp b (S k)))) (sum Z k (λ i => (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i)))))) (sum Z k (λ i => (mult (choose k i) (mult (exp a (sub k i)) (exp b (S i)))))))
                                        (plus (sum Z (S k) (λ i => (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i))))) (sum Z k (λ i => (mult (choose k i) (mult (exp a (sub k i)) (exp b (S i)))))))
                                        (sum Z (S k) (λ i => (mult (choose (S k) i) (mult (exp a (sub (S k) i)) (exp b i)))))
                                        (cong Nat Nat
                                              (plus (mult (choose k (S k)) (mult (exp a (sub (S k) (S k))) (exp b (S k)))) (sum Z k (λ i => (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i))))))
                                              (sum Z (S k) (λ i => (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i)))))
                                              (λ x => (plus x (sum Z k (λ i => (mult (choose k i) (mult (exp a (sub k i)) (exp b (S i))))))))
                                              (eq-trans Nat
                                                        (plus (mult (choose k (S k)) (mult (exp a (sub (S k) (S k))) (exp b (S k)))) (sum Z k (λ i => (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i))))))
                                                        (plus (mult (choose k (plus Z (S k))) (mult (exp a (sub (S k) (plus Z (S k)))) (exp b (plus Z (S k))))) (sum Z k (λ i => (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i))))))
                                                        (sum Z (S k) (λ i => (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i)))))
                                                        (cong Nat Nat
                                                              (S k)
                                                              (plus Z (S k))
                                                              (λ x => (plus (mult (choose k x) (mult (exp a (sub (S k) x)) (exp b x))) (sum Z k (λ i => (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i)))))))
                                                              (eq-symm Nat
                                                                       (plus Z (S k))
                                                                       (S k)
                                                                       (plus-zero-left (S k))))
                                               (sum-add-term-last Z k (λ i => (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i)))))))
                              (eq-trans Nat
                                        (plus (sum Z (S k) (λ i => (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i))))) (sum Z k (λ i => (mult (choose k i) (mult (exp a (sub k i)) (exp b (S i)))))))
                                        (plus (sum Z (S k) (λ i => (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i))))) (sum (S Z) k (λ i => (mult (choose k (sub1 i)) (mult (exp a (sub k (sub1 i))) (exp b (S (sub1 i))))))))
                                        (sum Z (S k) (λ i => (mult (choose (S k) i) (mult (exp a (sub (S k) i)) (exp b i)))))
                                        (cong Nat Nat
                                              (sum Z k (λ i => (mult (choose k i) (mult (exp a (sub k i)) (exp b (S i))))))
                                              (sum (S Z) k (λ i => (mult (choose k (sub1 i)) (mult (exp a (sub k (sub1 i))) (exp b (S (sub1 i)))))))
                                              (λ x => (plus (sum Z (S k) (λ i => (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i))))) x))
                                              (shift-bounds Z k
                                                            ((λ i => (mult (choose k i) (mult (exp a (sub k i)) (exp b (S i))))) : (Nat -> Nat))
                                                            ((λ i => (mult (choose k (sub1 i)) (mult (exp a (sub k (sub1 i))) (exp b (S (sub1 i)))))) : (Nat -> Nat))
                                                            (λ x => (eq-refl (mult (choose k (sub1 x)) (mult (exp a (sub k (sub1 x))) (exp b (S (sub1 x)))))))))
                              (eq-trans Nat
                                        (plus (sum Z (S k) (λ i => (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i))))) (sum (S Z) k (λ i => (mult (choose k (sub1 i)) (mult (exp a (sub k (sub1 i))) (exp b (S (sub1 i))))))))
                                        (plus (plus (mult (choose k Z) (mult (exp a (sub (S k) Z)) (exp b Z))) (sum (S Z) k (λ i => (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i)))))) (sum (S Z) k (λ i => (mult (choose k (sub1 i)) (mult (exp a (sub k (sub1 i))) (exp b (S (sub1 i))))))))
                                        (sum Z (S k) (λ i => (mult (choose (S k) i) (mult (exp a (sub (S k) i)) (exp b i)))))
                                        (cong Nat Nat
                                              (sum Z (S k) (λ i => (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i)))))
                                              (plus (mult (choose k Z) (mult (exp a (sub (S k) Z)) (exp b Z))) (sum (S Z) k (λ i => (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i))))))
                                              (λ x => (plus x (sum (S Z) k (λ i => (mult (choose k (sub1 i)) (mult (exp a (sub k (sub1 i))) (exp b (S (sub1 i)))))))))
                                              (eq-symm Nat
                                                       (plus (mult (choose k Z) (mult (exp a (sub (S k) Z)) (exp b Z))) (sum (S Z) k (λ i => (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i))))))
                                                       (sum Z (S k) (λ i => (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i)))))
                                                       (sum-add-term-first Z k (λ i => (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i)))))))
                              (eq-trans Nat
                                        (plus (plus (mult (choose k Z) (mult (exp a (sub (S k) Z)) (exp b Z))) (sum (S Z) k (λ i => (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i)))))) (sum (S Z) k (λ i => (mult (choose k (sub1 i)) (mult (exp a (sub k (sub1 i))) (exp b (S (sub1 i))))))))
                                        (plus (mult (choose k Z) (mult (exp a (sub (S k) Z)) (exp b Z))) (plus (sum (S Z) k (λ i => (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i))))) (sum (S Z) k (λ i => (mult (choose k (sub1 i)) (mult (exp a (sub k (sub1 i))) (exp b (S (sub1 i)))))))))
                                        (sum Z (S k) (λ i => (mult (choose (S k) i) (mult (exp a (sub (S k) i)) (exp b i)))))
                                        (eq-symm Nat
                                                 (plus (mult (choose k Z) (mult (exp a (sub (S k) Z)) (exp b Z))) (plus (sum (S Z) k (λ i => (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i))))) (sum (S Z) k (λ i => (mult (choose k (sub1 i)) (mult (exp a (sub k (sub1 i))) (exp b (S (sub1 i)))))))))
                                                 (plus (plus (mult (choose k Z) (mult (exp a (sub (S k) Z)) (exp b Z))) (sum (S Z) k (λ i => (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i)))))) (sum (S Z) k (λ i => (mult (choose k (sub1 i)) (mult (exp a (sub k (sub1 i))) (exp b (S (sub1 i))))))))
                                                 (plus-assoc (mult (choose k Z) (mult (exp a (sub (S k) Z)) (exp b Z)))
                                                             (sum (S Z) k (λ i => (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i)))))
                                                             (sum (S Z) k (λ i => (mult (choose k (sub1 i)) (mult (exp a (sub k (sub1 i))) (exp b (S (sub1 i)))))))))
                              (eq-trans Nat
                                        (plus (mult (choose k Z) (mult (exp a (sub (S k) Z)) (exp b Z))) (plus (sum (S Z) k (λ i => (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i))))) (sum (S Z) k (λ i => (mult (choose k (sub1 i)) (mult (exp a (sub k (sub1 i))) (exp b (S (sub1 i)))))))))
                                        (plus (mult (choose k Z) (mult (exp a (sub (S k) Z)) (exp b Z))) (sum (S Z) k (λ i => (plus (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i))) (mult (choose k (sub1 i)) (mult (exp a (sub k (sub1 i))) (exp b (S (sub1 i)))))))))
                                        (sum Z (S k) (λ i => (mult (choose (S k) i) (mult (exp a (sub (S k) i)) (exp b i)))))
                                        (cong Nat Nat
                                              (plus (sum (S Z) k (λ i => (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i))))) (sum (S Z) k (λ i => (mult (choose k (sub1 i)) (mult (exp a (sub k (sub1 i))) (exp b (S (sub1 i))))))))
                                              (sum (S Z) k (λ i => (plus (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i))) (mult (choose k (sub1 i)) (mult (exp a (sub k (sub1 i))) (exp b (S (sub1 i))))))))
                                              (λ x => (plus (mult (choose k Z) (mult (exp a (sub (S k) Z)) (exp b Z))) x))
                                              (split-sum (S Z) k
                                                         ((λ i => (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i)))) : (Nat -> Nat))
                                                         ((λ i => (mult (choose k (sub1 i)) (mult (exp a (sub k (sub1 i))) (exp b (S (sub1 i)))))) : (Nat -> Nat))
                                                         ((λ i => (plus (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i))) (mult (choose k (sub1 i)) (mult (exp a (sub k (sub1 i))) (exp b (S (sub1 i))))))) : (Nat -> Nat))
                                                         (λ x => (eq-refl (plus (mult (choose k x) (mult (exp a (sub (S k) x)) (exp b x))) (mult (choose k (sub1 x)) (mult (exp a (sub k (sub1 x))) (exp b (S (sub1 x))))))))))
                              (eq-trans Nat
                                        (plus (mult (choose k Z) (mult (exp a (sub (S k) Z)) (exp b Z))) (sum (S Z) k (λ i => (plus (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i))) (mult (choose k (sub1 i)) (mult (exp a (sub k (sub1 i))) (exp b (S (sub1 i)))))))))
                                        (plus (mult (choose k Z) (mult (exp a (sub (S k) Z)) (exp b Z))) (sum (S Z) k (λ i => (plus (mult (choose k (S (sub1 i))) (mult (exp a (sub (S k) i)) (exp b i))) (mult (choose k (sub1 i)) (mult (exp a (sub (S k) i)) (exp b i)))))))
                                        (sum Z (S k) (λ i => (mult (choose (S k) i) (mult (exp a (sub (S k) i)) (exp b i)))))
                                        (cong Nat Nat
                                              (sum (S Z) k (λ i => (plus (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i))) (mult (choose k (sub1 i)) (mult (exp a (sub k (sub1 i))) (exp b (S (sub1 i))))))))
                                              (sum (S Z) k (λ i => (plus (mult (choose k (S (sub1 i))) (mult (exp a (sub (S k) i)) (exp b i))) (mult (choose k (sub1 i)) (mult (exp a (sub (S k) i)) (exp b i))))))
                                              (λ x => (plus (mult (choose k Z) (mult (exp a (sub (S k) Z)) (exp b Z))) x))
                                              (eq-trans Nat
                                                        (sum (S Z) k (λ i => (plus (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i))) (mult (choose k (sub1 i)) (mult (exp a (sub k (sub1 i))) (exp b (S (sub1 i))))))))
                                                        (sum (S Z) k (λ i => (plus (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i))) (mult (choose k (sub1 i)) (mult (exp a (sub (S k) (S (sub1 i)))) (exp b (S (sub1 i))))))))
                                                        (sum (S Z) k (λ i => (plus (mult (choose k (S (sub1 i))) (mult (exp a (sub (S k) i)) (exp b i))) (mult (choose k (sub1 i)) (mult (exp a (sub (S k) i)) (exp b i))))))
                                                        (sum-equal-functions (S Z) k
                                                                             ((λ i => (plus (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i))) (mult (choose k (sub1 i)) (mult (exp a (sub k (sub1 i))) (exp b (S (sub1 i))))))) : (Nat -> Nat))
                                                                             ((λ i => (plus (mult (choose k i) (mult (exp a (sub (S k) i)) (exp b i))) (mult (choose k (sub1 i)) (mult (exp a (sub (S k) (S (sub1 i)))) (exp b (S (sub1 i))))))) : (Nat -> Nat))
                                                                             (λ x => (cong Nat Nat
                                                                                           (sub k (sub1 x))
                                                                                           (sub (S k) (S (sub1 x)))
                                                                                           (λ y => (plus (mult (choose k x) (mult (exp a (sub (S k) x)) (exp b x))) (mult (choose k (sub1 x)) (mult (exp a y) (exp b (S (sub1 x)))))))
                                                                                           (eq-symm Nat
                                                                                                    (sub (S k) (S (sub1 x)))
                                                                                                    (sub k (sub1 x))
                                                                                                    (subS k (sub1 x))))))
                                              (sum-function-lemma-general Z k (λ x => (λ y => (λ z => (plus (mult (choose k y) (mult (exp a (sub (S k) x)) (exp b x))) (mult (choose k (sub1 x)) (mult (exp a (sub (S k) z)) (exp b z))))))))))
                              (eq-trans Nat
                                        (plus (mult (choose k Z) (mult (exp a (sub (S k) Z)) (exp b Z))) (sum (S Z) k (λ i => (plus (mult (choose k (S (sub1 i))) (mult (exp a (sub (S k) i)) (exp b i))) (mult (choose k (sub1 i)) (mult (exp a (sub (S k) i)) (exp b i)))))))
                                        (plus (mult (choose k Z) (mult (exp a (sub (S k) Z)) (exp b Z))) (sum (S Z) k (λ i => (mult (plus (choose k (S (sub1 i))) (choose k (sub1 i))) (mult (exp a (sub (S k) i)) (exp b i))))))
                                        (sum Z (S k) (λ i => (mult (choose (S k) i) (mult (exp a (sub (S k) i)) (exp b i)))))
                                        (cong Nat Nat
                                              (sum (S Z) k (λ i => (plus (mult (choose k (S (sub1 i))) (mult (exp a (sub (S k) i)) (exp b i))) (mult (choose k (sub1 i)) (mult (exp a (sub (S k) i)) (exp b i))))))
                                              (sum (S Z) k (λ i => (mult (plus (choose k (S (sub1 i))) (choose k (sub1 i))) (mult (exp a (sub (S k) i)) (exp b i)))))
                                              (λ x => (plus (mult (choose k Z) (mult (exp a (sub (S k) Z)) (exp b Z))) x))
                                              (sum-equal-functions (S Z) k
                                                                   ((λ i => (plus (mult (choose k (S (sub1 i))) (mult (exp a (sub (S k) i)) (exp b i))) (mult (choose k (sub1 i)) (mult (exp a (sub (S k) i)) (exp b i))))) : (Nat -> Nat))
                                                                   ((λ i => (mult (plus (choose k (S (sub1 i))) (choose k (sub1 i))) (mult (exp a (sub (S k) i)) (exp b i)))) : (Nat -> Nat))
                                                                   (λ x => (eq-symm Nat
                                                                                    (mult (plus (choose k (S (sub1 x))) (choose k (sub1 x))) (mult (exp a (sub (S k) x)) (exp b x)))
                                                                                    (plus (mult (choose k (S (sub1 x))) (mult (exp a (sub (S k) x)) (exp b x))) (mult (choose k (sub1 x)) (mult (exp a (sub (S k) x)) (exp b x))))
                                                                                    (mult-right-dist (choose k (S (sub1 x)))
                                                                                                     (choose k (sub1 x))
                                                                                                     (mult (exp a (sub (S k) x)) (exp b x)))))))
                              (eq-trans Nat
                                        (plus (mult (choose k Z) (mult (exp a (sub (S k) Z)) (exp b Z))) (sum (S Z) k (λ i => (mult (plus (choose k (S (sub1 i))) (choose k (sub1 i))) (mult (exp a (sub (S k) i)) (exp b i))))))
                                        (plus (mult (choose k Z) (mult (exp a (sub (S k) Z)) (exp b Z))) (sum (S Z) k (λ i => (mult (choose (S k) i) (mult (exp a (sub (S k) i)) (exp b i))))))
                                        (sum Z (S k) (λ i => (mult (choose (S k) i) (mult (exp a (sub (S k) i)) (exp b i)))))
                                        (cong Nat Nat
                                              (sum (S Z) k (λ i => (mult (plus (choose k (S (sub1 i))) (choose k (sub1 i))) (mult (exp a (sub (S k) i)) (exp b i)))))
                                              (sum (S Z) k (λ i => (mult (choose (S k) i) (mult (exp a (sub (S k) i)) (exp b i)))))
                                              (λ x => (plus (mult (choose k Z) (mult (exp a (sub (S k) Z)) (exp b Z))) x))
                                              (eq-trans Nat
                                                        (sum (S Z) k (λ i => (mult (plus (choose k (S (sub1 i))) (choose k (sub1 i))) (mult (exp a (sub (S k) i)) (exp b i)))))
                                                        (sum (S Z) k (λ i => (mult (choose (S k) (S (sub1 i))) (mult (exp a (sub (S k) i)) (exp b i)))))
                                                        (sum (S Z) k (λ i => (mult (choose (S k) i) (mult (exp a (sub (S k) i)) (exp b i)))))
                                                        (sum-equal-functions (S Z) k
                                                                             ((λ i => (mult (plus (choose k (S (sub1 i))) (choose k (sub1 i))) (mult (exp a (sub (S k) i)) (exp b i)))) : (Nat -> Nat))
                                                                             ((λ i => (mult (choose (S k) (S (sub1 i))) (mult (exp a (sub (S k) i)) (exp b i)))) : (Nat -> Nat))
                                                                             (λ x => (cong Nat Nat
                                                                                           (plus (choose k (S (sub1 x))) (choose k (sub1 x)))
                                                                                           (choose (S k) (S (sub1 x)))
                                                                                           (λ y => (mult y (mult (exp a (sub (S k) x)) (exp b x))))
                                                                                           (eq-trans Nat
                                                                                                     (plus (choose k (S (sub1 x))) (choose k (sub1 x)))
                                                                                                     (plus (choose k (sub1 x)) (choose k (S (sub1 x))))
                                                                                                     (choose (S k) (S (sub1 x)))
                                                                                                     (plus-comm (choose k (S (sub1 x))) (choose k (sub1 x)))
                                                                                           (eq-refl (plus (choose k (sub1 x)) (choose k (S (sub1 x)))))))))
                                              (sum-function-lemma-general Z k (λ x => (λ y => (λ z => (mult (choose (S k) z) (mult (exp a (sub (S k) x)) (exp b x)))))))))
                              (eq-trans Nat
                                        (plus (mult (choose k Z) (mult (exp a (sub (S k) Z)) (exp b Z))) (sum (S Z) k (λ i => (mult (choose (S k) i) (mult (exp a (sub (S k) i)) (exp b i))))))
                                        (plus (mult (choose (S k) Z) (mult (exp a (sub (S k) Z)) (exp b Z))) (sum (S Z) k (λ i => (mult (choose (S k) i) (mult (exp a (sub (S k) i)) (exp b i))))))
                                        (sum Z (S k) (λ i => (mult (choose (S k) i) (mult (exp a (sub (S k) i)) (exp b i)))))
                                        (cong Nat Nat
                                              (choose k Z)
                                              (choose (S k) Z)
                                              (λ x => (plus (mult x (mult (exp a (sub (S k) Z)) (exp b Z))) (sum (S Z) k (λ i => (mult (choose (S k) i) (mult (exp a (sub (S k) i)) (exp b i)))))))
                                              (eq-trans Nat
                                                        (choose k Z)
                                                        (S Z)
                                                        (choose (S k) Z)
                                                        (choose-zero k)
                                              (eq-symm Nat
                                                       (choose (S k) Z)
                                                       (S Z)
                                                       (choose-zero (S k)))))
                              (sum-add-term-first Z k (λ i => (mult (choose (S k) i) (mult (exp a (sub (S k) i)) (exp b i))))))))))))))))))))))))))
                            n))))

                         : (∀ (a : Nat) (b : Nat) (n : Nat) ->
                              ((exp (plus a b) n) = (sum Z n (λ i => (mult (choose n i) (mult (exp a (sub n i)) (exp b i)))))))))