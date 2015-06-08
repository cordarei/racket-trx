;; ===================================================================================================
;; Implements a matcher for regular tree expressions
;;   based on Ilya Bagrak and Olin Shivers (2004) 'trx: Regular-tree expressions, now in Scheme'.

#lang racket

(require racket/control)
(require racket/generator)

(require (for-syntax syntax/parse))

(module+ test
  (require rackunit))

(provide trx trx-match ast->fta build-ast)

;; ---------------------------------------------------------------------------------------------------
;; automata

;; the record type that holds a compiled tree automaton
(struct fta
  (states
   alphabet
   labeled-rules
   empty-rules
   final-states
   special-states
   submatch-states)
  #:transparent)

;; a non-empty rule: f(q_in)q_out -> q
(struct labeled-rule
  (sym-name
  in-state
  out-state
  final-state)
  #:transparent)

;; an empty rule: () -> q
(struct empty-rule
  (final-state)
  #:transparent)

;; symbol for epsilon rules
(define epsilon (string->uninterned-symbol "ε"))
;; special symbol for matching unlabeled trees
(define unlabeled-tree (string->uninterned-symbol "^"))

(module+ test
  ;; example fta that matches (a b c d) and no other tree
  (define ex-fta
    (fta '(q0 q1 q2 q3 q4 q6)
         '(a b c d)
         (list (labeled-rule 'a 'q1 'q2 'q0)
               (labeled-rule 'b 'q2 'q4 'q1)
               (labeled-rule 'c 'q2 'q6 'q4)
               (labeled-rule 'd 'q2 'q2 'q6))
         (list (empty-rule 'q2))
         '(q0)
         '()
         '())))

;; does the given rule match the given node in the given state
(define (rule-match? fta rule node state)
  (let* ([q (labeled-rule-final-state rule)]
         [f (labeled-rule-sym-name rule)]
         [special (assoc q (fta-special-states fta))]
         [n.label (cond
                    [(eq? f unlabeled-tree) f]
                    [(eq? f epsilon) f]
                    [(list? node) (car node)]
                    [else node])])
    (and (eq? q state)
         (if special
             (apply (cdr special) (list n.label))
             (equal? f n.label)))))

(module+ test
  (check-true (rule-match? ex-fta (list-ref (fta-labeled-rules ex-fta) 0) '(a b c d) 'q0))
  (check-false (rule-match? ex-fta (list-ref (fta-labeled-rules ex-fta) 1) '(a b c d) 'q0))
  (check-false (rule-match? ex-fta (list-ref (fta-labeled-rules ex-fta) 1) '(a b c d) 'q1))
  (check-false (rule-match? ex-fta (list-ref (fta-labeled-rules ex-fta) 0) '(b c d) 'q0))
  (check-true (rule-match? ex-fta (list-ref (fta-labeled-rules ex-fta) 1) 'b 'q1))
  (check-true (rule-match? ex-fta (list-ref (fta-labeled-rules ex-fta) 1) '(b c d) 'q1))
  (check-true (rule-match? ex-fta (list-ref (fta-labeled-rules ex-fta) 3) 'd 'q6))

  (define special-fta (fta '() '() (list (labeled-rule null 'qe 'qe 'qf)) (list (empty-rule 'qe)) '(qf) (list (cons 'qf number?)) '()))
  (check-true (rule-match? special-fta (list-ref (fta-labeled-rules special-fta) 0) 42 'qf)))


(define (leaf? node) (or (not (list? node)) (empty? (cdr node))))
(define (children node (labeled #t))
  (cond
    [(not (list? node)) '()]
    [(not labeled) node]
    [else (cdr node)]))
(define (leftchild node) (cadr node))
(define (child-siblings node) (cddr node))

(define (error) (shift k #f))
(define-syntax (or/err stx)
  (syntax-case stx ()
    [(_ bodies ...) #'(or bodies ... (error))]))

(define (epsilon-closure fta state)
  (let loop ([estates (list state)])
    (define estates*
      (set-union estates
                 (map (λ (r) (labeled-rule-out-state r))
                      (filter (λ (r) (and (eq? epsilon (labeled-rule-sym-name r))
                                          (eq? state (labeled-rule-final-state r))))
                              (fta-labeled-rules fta)))))
    (if (set=? estates estates*)
        estates
        (loop estates*))))

(define (match-empty fta state)
  (or/err
   (not (empty? (set-intersect (epsilon-closure fta state)
                               (map empty-rule-final-state (fta-empty-rules fta)))))))

(define-syntax-rule (combine-result child-result sibling-result) (begin child-result sibling-result))

(define (match-with-rule fta rule node siblings state)
  (match rule
    [(labeled-rule f qin qout _)
     (define cs (children node (not (eq? unlabeled-tree f))))
     (combine-result
      (if (or (null? cs) (assoc state (fta-special-states fta)))
          (match-empty fta qin)
          (match-node fta (car cs) (cdr cs) qin))
      (if (empty? siblings)
         (match-empty fta qout)
         (match-node fta (car siblings) (cdr siblings) qout)))]))

(define (match-node fta node siblings state)
  ;; predicates for partitioning rules
  (define matches? (λ (r) (rule-match? fta r node state)))
  (define repeats? (λ (r) (eq? (labeled-rule-out-state r) (labeled-rule-final-state r))))
  (define eps? (λ (r) (eq? epsilon (labeled-rule-sym-name r))))
  (define neither? (λ (r) (not (or (repeats? r) (eps? r)))))

  (define matching-rules (filter matches? (fta-labeled-rules fta)))
  (define-values (epsilon-rules non-epsilon-rules) (partition eps? matching-rules))
  (define reordered-rules (let-values ([(a b) (partition repeats? non-epsilon-rules)]) (append a b)))
  (or/err
   (for/or ([r reordered-rules])
     (reset (match-with-rule fta r node siblings state)))
   (for/or ([r epsilon-rules])
     (reset (match-node fta node siblings (labeled-rule-out-state r))))))

(module+ test
  (check-not-false (match-node ex-fta '(a b c d) '() 'q0))
  (check-not-false (match-node ex-fta 'b '(c d) 'q1))
  (check-not-false (match-node ex-fta 'd '() 'q6))
  (check-false (match-node ex-fta '(a b) '() 'q0))
  (check-false (match-node ex-fta '(a c) '() 'q0)))

;; run automaton fta against tree
(define (fta-match fta tree)
  (for/or ([q (fta-final-states fta)])
    (reset (match-node fta tree '() q))))

(module+ test
  (check-not-false (fta-match ex-fta '(a b c d)))
  (check-false (fta-match ex-fta '(b d)))
  (check-false (fta-match ex-fta 'b))
  (check-false (fta-match ex-fta '(a b c)))
  (check-false (fta-match ex-fta '(a c b d)))

  ;; =/= (rec q (| 1 (@ + (+ q))))
  (define complex-fta
    (fta null
         null
         (list (labeled-rule epsilon 'qe 'q1 'q0)
               (labeled-rule 1 'qe 'q2 'q1)
               (labeled-rule epsilon 'qe 'qe 'q2)
               (labeled-rule epsilon 'qe 'q4 'q0)
               (labeled-rule '+ 'q6 'q5 'q4)
               (labeled-rule epsilon 'qe 'qe 'q5)
               (labeled-rule epsilon 'qe 'q7 'q6)
               (labeled-rule epsilon 'qe 'q8 'q7)
               (labeled-rule 1 'qe 'q9 'q8)
               (labeled-rule epsilon 'qe 'q10' q9)
               (labeled-rule epsilon 'qe 'q7 'q10)
               (labeled-rule epsilon 'qe 'q11 'q7)
               (labeled-rule '+ 'q6 'q12 'q11)
               (labeled-rule epsilon 'qe 'q10 'q12))
         (list (empty-rule 'qe) (empty-rule 'q10))
         '(q0)
         null
         null))

  (check-not-false (fta-match complex-fta 1))
  (check-not-false (fta-match complex-fta '(+ 1 1 1)))
  (check-not-false (fta-match complex-fta '(+ 1 1 (+ 1))))
  )

;; ---------------------------------------------------------------------------------------------------
;; abstract syntax

;; literal atom or 'symbol
(struct ast-lit-node
  (literal
  [private #:mutable])
  #:transparent)

;; (@ symbol rte ...) or (symbol rte ...)
(struct ast-sym-node
  (symbol
  children
  [private #:mutable])
  #:transparent)

;; (^ rte ...)
(struct ast-unlabeled-node
  (children
   [private #:mutable])
  #:transparent)

;; (* rte ...) or (+ rte ...) or (? rte ...)
(struct ast-seq-node
  (quantifier
  child
  [private #:mutable])
  #:transparent)

;; (| rte ...)
(struct ast-choice-node
  (children
   [private #:mutable])
  #:transparent)

;; ,number? ,(λ (x) scheme code)
(struct ast-special-node
  (proc
   [private #:mutable])
  #:transparent)

;; recursive rte (rec id rte)
(struct ast-rec-node
  (id
   child
   [private #:mutable])
  #:transparent)

(struct ast-ref-node
  (id
   [private #:mutable])
  #:transparent)

(define (set-private! ast priv)
  (cond
    [(ast-lit-node? ast) (set-ast-lit-node-private! ast priv)]
    [(ast-sym-node? ast) (set-ast-sym-node-private! ast priv)]
    [(ast-unlabeled-node? ast) (set-ast-unlabeled-node-private! ast priv)]
    [(ast-seq-node? ast) (set-ast-seq-node-private! ast priv)]
    [(ast-choice-node? ast) (set-ast-choice-node-private! ast priv)]
    [(ast-special-node? ast) (set-ast-special-node-private! ast priv)]
    [(ast-rec-node? ast) (set-ast-rec-node-private! ast priv)]
    [(ast-ref-node? ast) (set-ast-ref-node-private! ast priv)]
    [else (raise-argument-error 'ast "ast must be an ast struct" ast)]
    ))

;;; compile

(define (ast->fta ast)
  ;(define (new-state) (gensym 'q))
  (define new-state (generator () (let loop ([i 0]) (begin (yield i) (loop (+ i 1)))) ))

  (define empty-state (new-state))

  (define (compile-children-with-symbol ast priv state out-state symbol children id-ast-map)
    (cond
      [(priv ast)
       (values state (list (labeled-rule symbol (priv ast) out-state state)) null null)]
      [else
       (set-private! ast (box #f))
       (define child-end-state (new-state))
       (define-values (child-state child-rules child-empty-symbols child-special-states)
         (compile-nodes-in-sequence children child-end-state id-ast-map))
       (set-box! (priv ast) child-state)
       (values state
               (cons (labeled-rule symbol child-state out-state state)
                     child-rules)
               (cons child-end-state child-empty-symbols)
               child-special-states)]))

  (define (compile-nodes-in-sequence nodes out-state id-ast-map)
    (for/fold ([out-state out-state]
               [lrules '()]
               [empty-symbols '()]
               [special-states '()])
        ([node (reverse nodes)])
      (define-values (s r e p)
        (compile-node node out-state id-ast-map))
      (values s
              (append r lrules)
              (append e empty-symbols)
              (append p special-states))))

  (define (compile-node ast out-state id-ast-map)
    (define state (new-state))
    (match ast

      [(ast-lit-node literal priv)
       (values state
               (list (labeled-rule literal empty-state out-state state))
               '()
               '())]

      [(ast-sym-node symbol children priv)
       (compile-children-with-symbol ast ast-sym-node-private state out-state symbol children id-ast-map)]

      [(ast-unlabeled-node children priv)
       (compile-children-with-symbol ast ast-unlabeled-node-private state out-state unlabeled-tree children id-ast-map)]

      [(ast-seq-node quantifier child priv)
       (define child-out-state (if (eq? quantifier '+) out-state (new-state)))
       (define-values (child-state child-rules child-empty-symbols child-special-states)
         (compile-node child child-out-state id-ast-map))
       (define maybe-skip-rules
         (if (eq? quantifier '+)
             child-rules
             (cons (labeled-rule epsilon null out-state state)
                   (cons (labeled-rule epsilon null out-state child-out-state)
                         child-rules))))
       (define maybe-repeat-rules
         (if (eq? quantifier '?)
             maybe-skip-rules
             (cons (labeled-rule epsilon null child-state child-out-state)
                   maybe-skip-rules)))
       (define rules (cons (labeled-rule epsilon null child-state state) maybe-repeat-rules))
       (values state
               rules
               child-empty-symbols
               child-special-states)]

      [(ast-choice-node children priv)
       (define-values (rules empty-symbols special-states)
         (for/fold ([rules '()]
                    [empty-symbols '()]
                    [special-states '()])
             ([child children])
           (define child-out-state (new-state))
           (define-values (child-state child-rules child-empty-symbols child-special-states)
             (compile-node child child-out-state id-ast-map))
           (values (cons (labeled-rule epsilon null child-state state)
                         (cons (labeled-rule epsilon null out-state child-out-state)
                               (append child-rules rules)))
                   (append child-empty-symbols empty-symbols)
                   (append child-special-states special-states))))
       (values state rules empty-symbols special-states)]

      [(ast-special-node proc priv)
       (values state
               (list (labeled-rule null empty-state out-state state))
               '()
               (list (cons state proc))
               )]

      [(ast-rec-node id child priv)
       (compile-node child out-state (cons (cons id child) id-ast-map))
       ;; (define-values (child-state child-rules child-empty-symbols child-special-states)
       ;;   (compile-node child #f (cons (cons id child) id-ast-map)))
       ;; (values null null null null)
       ]

      [(ast-ref-node id priv)
       (cond
         [priv
          (values priv null null null)]
         [else
          (define ref-ast (assoc id id-ast-map))
          (unless ref-ast (raise-arguments-error 'id-ast-map "no entry for reference node" "node" id "map" id-ast-map))
          (set-private! ast (box #f))
          (define-values (ref-state ref-rules ref-empty-symbols ref-special-states)
            (compile-node (cdr ref-ast) out-state id-ast-map))
          (set-box! (ast-ref-node-private ast) ref-state)
          (values ref-state ref-rules ref-empty-symbols ref-special-states)
          ])
       ]

      ))

  (define-values (state rules empty-symbols special-states)
    (compile-node ast empty-state null))

  (define (unbox-assert b)
    (or (unbox b)
        (error "boxed state value was null")))
  (define (maybe-unbox b)
    (if (box? b)
        (unbox-assert b)
        b))
  (define (fixup-rule r)
    (match r
      [(labeled-rule f in out q)
       (labeled-rule f (maybe-unbox in) (maybe-unbox out) (maybe-unbox q))]))

  (fta null
       null
       (map fixup-rule rules)
       (map empty-rule (cons empty-state empty-symbols))
       (list state)
       special-states
       null)
  )

(module+ test

  (let ([ast (ast->fta (ast-sym-node 'a (list (ast-seq-node '+ (ast-lit-node 42 #f) #f)) #f))])
    (check-not-false (fta-match ast '(a 42)))
    (check-not-false (fta-match ast '(a 42 42)))
    (check-not-false (fta-match ast '(a 42 42 42)))
    (check-false (fta-match ast '(a)))
    (check-false (fta-match ast '(a 42 1 42)))
    (check-false (fta-match ast '(a 42 42 42 'x))))

  (let ([ast (ast->fta (ast-sym-node 'a (list (ast-seq-node '+ (ast-lit-node 42 #f) #f)
                                              (ast-lit-node 1 #f)) #f))])
    (check-not-false (fta-match ast '(a 42 1)))
    (check-not-false (fta-match ast '(a 42 42 1)))
    (check-false (fta-match ast '(a 1)))
    (check-false (fta-match ast '(a 42 42))))

  (let ([ast (ast->fta (ast-sym-node 'a (list (ast-seq-node '? (ast-lit-node 42 #f) #f)
                                              (ast-lit-node 1 #f)) #f))])
    (check-not-false (fta-match ast '(a 1)))
    (check-not-false (fta-match ast '(a 42 1)))
    (check-false (fta-match ast '(a 42 42 1))))

  (let ([ast (ast-sym-node '+ (list (ast-seq-node '+ (ast-special-node number? #f) #f)) #f)])
    (check-not-false (fta-match (ast->fta ast) '(+ 1 2 42)))
    (check-false (fta-match (ast->fta ast) '(+ 1 a 42))))

  (let ([fta (ast->fta (ast-sym-node '+ (list (ast-seq-node '+ (ast-special-node (λ (x) (or (number? x) (string? x))) #f) #f)) #f))])
    (check-not-false (fta-match fta '(+ 1 2 42)))
    (check-not-false (fta-match fta '(+ 1 "a" 42)))
    (check-false (fta-match fta '(+ 1 a 42))))

  (let ([fta (ast->fta (ast-rec-node 'q
                                     (ast-choice-node
                                      (list
                                       (ast-lit-node 'null #f)
                                       (ast-sym-node 'cons
                                                     (list (ast-ref-node 'q #f)
                                                           (ast-ref-node 'q #f))
                                                     #f)
                                       (ast-sym-node 'cons
                                                     (list (ast-lit-node 1 #f)
                                                           (ast-ref-node 'q #f))
                                                     #f))
                                      #f)
                                     #f))])
    (check-not-false (fta-match fta '(cons 1 null)))
    (check-not-false (fta-match fta '(cons null null)))
    (check-not-false (fta-match fta '(cons (cons 1 null) null)))
    (check-false (fta-match fta '(cons null 1)))
    (check-false (fta-match fta '(cons (cons a null) (cons 1 null))))
    )
  )

;; ---------------------------------------------------------------------------------------------------
;; interface

(define-syntax (build-ast stx)
  (syntax-parse stx
    #:datum-literals (@ ^ any or * + ? quote unquote rec let let* letrec)
    [(_ (rec ident:id rte))
     #'(ast-rec-node (quote ident) (build-ast rte) #f)]
    [(_ (unquote ex))
     #'(ast-special-node ex #f)]
    [(_ lit:str)
     #'(ast-lit-node lit #f)]
    [(_ lit:number)
     #'(ast-lit-node lit #f)]
    [(_ lit:boolean)
     #'(ast-lit-node lit #f)]
    [(_ lit:char)
     #'(ast-lit-node lit #f)]
    [(_ (quote symbol:id))
     #'(ast-lit-node (quote symbol) #f)]
    [(_ (^ rte ...))
     #'(ast-unlabeled-node (list (build-ast rte) ...) #f)]
    [(_ (any))
     #'(ast-special-node (const #t) #f)]
    [(_ (or rte ...))
     #'(ast-choice-node (list (build-ast rte) ...) #f)]
    [(_ (* rte))
     #'(ast-seq-node '* (build-ast rte) #f)]
    [(_ (+ rte))
     #'(ast-seq-node '+ (build-ast rte) #f)]
    [(_ (? rte))
     #'(ast-seq-node '? (build-ast rte) #f)]
    [(_ (@ symbol:id rte ...))
     #'(ast-sym-node (quote symbol) (list (build-ast rte) ...) #f)]
    [(_ (symbol:id rte ...))
     #'(ast-sym-node (quote symbol) (list (build-ast rte) ...) #f)]
    [(_ ident:id)
     #'(ast-ref-node (quote ident) #f)]
    ))

(define-syntax (trx stx)
  (syntax-case stx ()
    [(_ rte) #'(ast->fta (build-ast rte))]))

(define (trx-match fta tree) (fta-match fta tree))


(module+ test
  (check-not-false (trx-match (trx 'a) 'a))
  (check-not-false (trx-match (trx (rec q (or (cons 1 q) (cons q q) 'null))) '(cons 1 null)))
  (check-not-false (trx-match (trx (any)) 42))
  (check-not-false (trx-match (trx (any)) '(+ 1 2 3))))
