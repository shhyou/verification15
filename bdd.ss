(use util.match)

(define example-bdd
  (let* ([v4 `(3 . (#t . #f))]
         [v3 `(2 . (#t . ,v4))]
         [v2 `(1 . (,v4 . ,v3))]
         [v1 `(1 . (#t . ,v3))]
         [v0 `(0 . (,v1 . ,v2))])
    v0))

(define bdd-var car)
(define bdd-true cadr)
(define bdd-false cddr)

(define (bdd->expr bdd)
  (define cache (make-hash-table 'eq?))
  (define (build-aux bdd)
    (cond [(hash-table-exists? cache bdd) (hash-table-get cache bdd)]
          [(boolean? bdd) bdd]
          [else (let [(fn `(or (and ,(bdd-var bdd) ,(bdd->expr (bdd-true bdd)))
                               (and (not ,(bdd-var bdd)) ,(bdd->expr (bdd-false bdd)))))]
                  (hash-table-put! cache bdd fn)
                  fn)]))
  (expr-simplify (build-aux bdd)))

(define (expr-fold const op)
  (define rec
    (lambda (expr)
      (if (pair? expr)
          (op `(,(car expr) . ,(map rec (cdr expr))))
          (const expr))))
  rec)

; the rewriting step must be confluent
(define expr-simplify
  (expr-fold
    (lambda (expr) expr)
    (lambda (expr)
      (match expr
        [('not (? boolean? b)) (not b)]
        [(or ('or #t _) ('or _ #t)) #t]
        [(or ('and #f _) ('and _ #f)) #f]
        [(or ('or #f e) ('or e #f) ('and #t e) ('and e #t)) e]
        [e e]))))

; expr[v/x]
(define (expr-subst x v expr)
  ((expr-fold
     (lambda (expr) (if (eq? x expr) v expr))
     (lambda (expr) expr))
    expr))

; vars is the order to build variables
(define (expr->bdd expr vars)
  (define cache (make-hash-table 'equal?))
  (define (build-aux expr vars)
    (if (hash-table-exists? cache expr)
        (hash-table-get cache expr)
        (let* ([v (car vars)]
               [vs (cdr vars)]
               [bdd-t (build-aux (expr-simplify (expr-subst v #t expr)) vs)]
               [bdd-f (build-aux (expr-simplify (expr-subst v #f expr)) vs)]
               [bdd (if (eq? bdd-t bdd-f) bdd-t
                        `(,v . (,bdd-t . ,bdd-f)))])
          (hash-table-put! cache expr bdd)
          bdd)))
  (hash-table-put! cache #t #t)
  (hash-table-put! cache #f #f)
  (build-aux (expr-simplify expr) vars))

; if the sharing invariant is maintained, bdd-equal? should take O(1) time
(define (bdd-equal? bdd1 bdd2)
  (cond [(or (boolean? bdd1) (boolean? bdd2)) (eq? bdd1 bdd2)]
        [(eq? bdd1 bdd2) #t]
        [(not (eq? (bdd-var bdd1) (bdd-var bdd2))) #f]
        [else (and (bdd-equal? (bdd-true bdd1)  (bdd-true bdd2))
                   (bdd-equal? (bdd-false bdd1) (bdd-false bdd2)))]))

(define (bdd-not bdd)
  (if (boolean? bdd) (not bdd)
      `(,(bdd-var bdd) . (,(bdd-not (bdd-true bdd)) . ,(bdd-not (bdd-false bdd))))))

; op is assumed to be commutative
(define (bdd-op op bdd1 bdd2)
  (define (bdd-mkstep var)
    (lambda (bdd-select bdd)
      (if (and (pair? bdd) (= (bdd-var bdd) var))
          (bdd-select bdd)
          bdd)))
  (cond [(and (boolean? bdd1) (boolean? bdd2))
         (op bdd1 bdd2)]
        [else (let* ([var (bdd-var (if (boolean? bdd2) bdd1 bdd2))]
                     [step (bdd-mkstep var)]
                     [bdd-t (bdd-op op (step bdd-true bdd1)  (step bdd-true bdd2))]
                     [bdd-f (bdd-op op (step bdd-false bdd1) (step bdd-false bdd2))])
                (if (bdd-equal? bdd-t bdd-f) bdd-t
                    `(,var . (,bdd-t . ,bdd-f))))]))
