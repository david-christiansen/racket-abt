#lang racket

(require (for-syntax racket/list syntax/parse racket/syntax (for-syntax racket/base))
         racket/fixnum racket/provide-syntax
         zippers)

(module+ test (require rackunit))

;; TODO:
;;  1. Add needed dynamic well-sortedness checks
;;  2. Add match expanders for constructing terms as well
;;  3. Second-order variables
;;  4. Symbols and symbol binders (to support e.g. (ν (x) body))
;;  5. Provide form for a sort (provide (sort-out Expr))
;;  6. Annotations on objects (for storing source locations etc)
;;  7. Parameters on objects à la Nuprl
;;  8. Explicit substitutions, applied lazily

(struct sort (name predicate)
  #:methods gen:custom-write
  [(define (write-proc s port mode)
     (fprintf (or port (current-output-port)) "#<sort:~a>" (sort-name s)))])

(define/contract (has-sort? s v)
  (-> sort? any/c boolean?)
  (if (free-name? v)
      (equal? s (free-name-sort v))
      ((sort-predicate s) v)))

(struct binder (abs inst) #:transparent)

(define-values (prop:bindings has-prop:bindings? real-bindings-accessor)
  (make-struct-type-property 'bindings
                             (lambda (v _)
                               (and (binder? v) v))))

;; For now, there's a hard-coded collection of primitive sorts. This needs fixing.
(define String (sort 'String string?))
(define Natural (sort 'Natural exact-nonnegative-integer?))
(define Integer (sort 'Integer exact-integer?))
(define the-primitive-sorts (list String Natural Integer))
(define (primitive-sort? s)
  (-> sort? boolean?)
  (not (not (member s the-primitive-sorts))))
(define (has-primitive-sort? v)
  (for/or ([prim the-primitive-sorts])
    (has-sort? prim v)))

(define (bindings? v)
  (or (has-primitive-sort? v) (has-prop:bindings? v)))

(define primitive-bindings
  (binder (lambda (v frees i) v) (lambda (v i new) v)))

(define (bindings-accessor v)
  (if (has-primitive-sort? v)
      primitive-bindings
      (real-bindings-accessor v)))

;; Used only for debug output
(define used-names (make-parameter '()))
(define/contract (string-incr hint)
  (-> string? string?)
  (define last-char (string-ref hint (sub1 (string-length hint))))
  (if (char=? last-char #\z)
      (string-append hint "a")
      (string-append (substring hint 0 (sub1 (string-length hint)))
                     (string (integer->char (add1 (char->integer last-char)))))))
(define/contract (next-name hint used)
  (-> string? (listof string?) string?)
  (if (member hint used)
      (next-name (string-incr hint) used)
      hint))

(define/contract (fresh-print-names n)
  (->i ((n exact-nonnegative-integer?))
       (result (n) (and/c (listof string?)
                          (lambda (r) (= (length r) n)))))
  (if (zero? n)
      '()
      (let ((x (next-name "a" (used-names))))
        (parameterize ([used-names (cons x (used-names))])
          (cons x (fresh-print-names (sub1 n)))))))

;; valence is a list of the sorts of the variables bound by the scope, and body is a member of some
;; sort
(struct scope (valence body)
  #:methods gen:custom-write
  [(define (write-proc sc port mode)
     (define temps (fresh-print-names (length (scope-valence sc))))
     (define binder (string-append "⟨"
                                   (string-join
                                    (for/list ([x temps]
                                               [srt (scope-valence sc)])
                                      (format "~a:~a" x (sort-name srt)))
                                    ", ")
                                   "⟩"))
     (parameterize ([used-names (append temps (used-names))])
       (fprintf (or port (current-output-port)) "#<sc ~a.~a>" binder (scope-body sc))))]
  #:property prop:bindings
  (binder
   ;; abs
   (lambda (sc frees i)
     (define valence (scope-valence sc))
     (define body (scope-body sc))
     (match-define (binder abs _) (bindings-accessor body))
     (scope valence
            (abs body frees (+ i (length valence)))))
   ;; inst
   (lambda (sc i new-exprs)
     (define valence (scope-valence sc))
     (define body (scope-body sc))
     (match-define (binder _ inst) (bindings-accessor body))
     (scope valence (inst body (+ i (length valence)) new-exprs))))
  #:methods gen:equal+hash
  ((define (equal-proc sc1 sc2 rec-equal?)
     (and (rec-equal? (scope-valence sc1) (scope-valence sc2))
          (rec-equal? (scope-body sc1) (scope-body sc2))))
   (define (hash-proc sc rec-hash)
     (fxxor (rec-hash (scope-valence sc))
            (rec-hash (scope-body sc))))
   (define (hash2-proc sc rec-hash2)
     (fxxor (rec-hash2 (scope-valence sc))
            (rec-hash2 (scope-body sc))))))

(struct scope-body-frame (free-vars)
  #:transparent
  #:property prop:zipper-frame
  (lambda (frame focus)
    (abs (scope-body-frame-free-vars frame) focus)))
(define down/scope
  (zipper-movement
   (lambda (z)
     (define sc (zipper-focus z))
     (match-define (scope valence body) sc)
     (define free-vars (for/list ([srt valence])
                         (fresh srt)))
     (zipper (inst sc free-vars)
             (cons (scope-body-frame free-vars)
                   (zipper-context z))))
   (lambda (z)
     (scope? (zipper-focus z)))))

(define (auto-inst sc)
  (define frees (for/list ([srt (scope-valence sc)])
                  (fresh srt)))
  (cons frees (inst sc frees)))

(define-match-expander in-scope
  (lambda (stx)
    (syntax-parse stx
      [(_ (x:id ...) body:expr)
       (with-syntax ([var-count (length (syntax->list #'(x ...)))])
         #'(? (lambda (sc)
                (and (scope? sc)
                     (= (length (scope-valence sc)) var-count)))
              (app auto-inst
                   (cons (list x ...) body))))]
      [(_ ((x:id sort:expr) ...) body:expr)
       (with-syntax ([var-count (length (syntax->list #'(x ...)))])
         #'(? (lambda (sc)
                (and (scope? sc)
                     (= (length (scope-valence sc)) var-count)
                     (equal? (list sort ...) (scope-valence sc))))
              (app auto-inst
                   (cons (list x ...) body))))]))
  (lambda (stx)
    (syntax-parse stx
      [(_ ((x:id sort:expr) ...)
          body:expr)
       (with-syntax ([(x-str ...) (map symbol->string (syntax->datum #'(x ...)))])
         (syntax/loc stx
           (let ([x (fresh sort x-str)] ...)
             (abs (list x ...) body))))])))

(struct free-name (sort sym hint)
  #:property prop:bindings
  (binder
   ;; abs
   (lambda (expr frees i)
     (let ((j (index-of frees expr
                        (lambda (x y)
                          (eqv? (free-name-sym x)
                                (free-name-sym y))))))
       (if j
           (bound-name (+ i j))
           expr)))
   ;; inst
   (lambda (expr i new-exprs)
     expr))
  #:methods gen:custom-write
  ((define (write-proc x port mode)
     (fprintf port "#<free:~a>" (free-name-sym x))))
  #:methods gen:equal+hash
  ((define (equal-proc fn1 fn2 rec-equal?)
     (eqv? (free-name-sym fn1) (free-name-sym fn2)))
   (define (hash-proc fn rec-hash)
     (rec-hash (free-name-sym fn)))
   (define (hash2-proc fn rec-hash2)
     (rec-hash2 (free-name-sym fn)))))

(define (fresh sort (str "x"))
  (free-name sort (gensym str) str))

(struct bound-name (index)
  #:transparent
  #:property prop:bindings
  (binder (lambda (expr frees i)
            expr)
          (lambda (expr i new-exprs)
            (define j (- (bound-name-index expr) i))
            (if (<= 0 j (add1 (length new-exprs)))
                (list-ref new-exprs j)
                expr)))
  #:methods gen:custom-write
  ((define (write-proc x port mode)
     (define print-x
       (let loop ((i (bound-name-index x))
                  (used (used-names)))
         (if (zero? i)
             (if (pair? used)
                 (car used)
                 (format "#<~a>" (bound-name-index x)))
             (if (pair? used)
                 (loop (sub1 i) (cdr used))
                 (format "#<~a>" (bound-name-index x))))))
     (write-string print-x port))))

(define/contract (sorts-match? sorts vals)
  (-> (listof sort?) (listof any/c) boolean?)
  (match* (sorts vals)
    [((cons s ss) (cons v vs))
     (and (has-sort? s v)
          (sorts-match? ss vs))]
    [('() '()) #t]
    [(_ _) #f]))

;; Instantiate the variables bound by this scope with well-sorted values
(define/contract (inst sc vals)
  (->i ((sc scope?)
        (vals list?))
       #:pre (sc vals) (sorts-match? (scope-valence sc) vals)
       (result any/c))
  (define open-expr (scope-body sc))
  (match-let ([(binder _ inst) (bindings-accessor open-expr)])
    (inst open-expr 0 vals)))

(define/contract (distinct? frees)
  (-> (listof free-name?) boolean?)
  (define seen (mutable-set))
  (for/and ([var frees])
    (begin0 (not (set-member? seen var))
            (set-add! seen var))))

;; Abstract over distinct free names in a term, returning the appropriate scope
(define/contract (abs frees closed-expr)
  (->i ((frees (and/c (listof free-name?)
                      distinct?))
        (closed-expr bindings?))
       (result (frees)
               (and/c scope?
                      ;; todo: insert check that abstraction is sort-preserving, we need a runtime
                      ;; sort recognition operator for this.
                      (lambda (r)
                        (equal? (scope-valence r)
                                (map free-name-sort frees))))))
  (define open-expr
    (match-let ([(binder abs _) (bindings-accessor closed-expr)])
      (abs closed-expr frees 0)))
  (scope (map free-name-sort frees) open-expr))


(define-syntax (define-op-zipper stx)
  (syntax-parse stx
    [(_ op:id make-op:id op?:id op-acc:id field-name:id ...)
     (define fields (syntax->list #'(field-name ...)))
     (with-syntax ([((this other ...) ...)
                    (for/list ([i (in-range 0 (length fields))])
                      (define-values (pre post) (split-at fields i))
                      (cons (format-id #'op "~a-~a-frame" #'op (car post)) (append pre (cdr post))))]
                   [(down/op-field ...)
                    (for/list ([f fields])
                      (format-id #'op "down/~a-~a" #'op f))]
                   [(field-ix ...) (range 0 (length fields))]
                   [(((before-temp ...) (after-temp ...)) ...)
                    (for/list ([i (in-range 0 (length fields))])
                      (define-values (before after) (split-at fields i))
                      (list (generate-temporaries before) (generate-temporaries (cdr after))))]
                   [((before-field-ix ...) ...)
                    (for/list ([x (in-range 0 (length fields))])
                      (for/list ([f (in-range 0 x)])
                        f))]
                   [((after-field-ix ...) ...)
                    (begin (for/list ([x (range 0 (length fields))])
                             (for/list ([f (range (add1 x) (length fields))])
                               f)))])
       (syntax/loc stx
         (begin
           (define acc op-acc) ;; work around ellipsis mismatch
           (struct this (other ...)
             #:transparent
             #:property prop:zipper-frame
             (lambda (fr old-focus)
               (match-define (this before-temp ... after-temp ...) fr)
               (make-op before-temp ... old-focus after-temp ...)))
           ...
           (define down/op-field
             (zipper-movement
              (lambda (z)
                (match-define (zipper focus ctxt) z)
                (define new-focus (acc focus field-ix))
                (define new-frame
                  (this (acc focus before-field-ix) ...
                        (acc focus after-field-ix) ...))
                (zipper new-focus (cons new-frame ctxt)))
              (lambda (z)
                (op? (zipper-focus z)))))
           ...
           (void))))]))

(define-syntax (define-sort stx)
  (syntax-parse stx
    [(_ sort-name
        (op:id
         (field-name:id (bound-sort ...) field-sort)
         ...)
        ...)
     (define ops (syntax->list #'(op ...)))
     (define (formatted str)
       (for/list ([op-name (in-list ops)])
         (format-id op-name str op-name)))
     (with-syntax ([(op-ty ...) (formatted "~a-type")]
                   [(make-op ...) (formatted "make-~a")]
                   [(op? ...) (formatted "~a?")]
                   [(op-acc ...) (formatted "~a-acc")]
                   [(op-mut ...) (formatted "~a-mut")]
                   [((op-field-frame ...) ...)
                    (for*/list ([op (in-list ops)]
                                [fs (in-list (syntax->list #'((field-name ...) ...)))])
                      (for/list ([f (in-list (syntax->list fs))])
                        (format-id op "~a-~a-frame" op f)))]
                   [((field-temp ...) ...)
                    (map generate-temporaries (syntax->list #'((field-name ...) ...)))]
                   [(field-count ...)
                    (for*/list ([fs (syntax->list #'((field-name ...) ...))])
                      (length (syntax->list fs)))]
                   [((field-index ...) ...)
                    (for*/list ([fs (syntax->list #'((field-name ...) ...))])
                      (range 0 (length (syntax->list fs))))]
                   [sort-name? (format-id #'sort-name "~a?" #'sort-name)])
       (syntax/loc stx
         (begin
           (define-values (op-ty make-op op? op-acc op-mut)
             (make-struct-type 'op #f field-count 0 #f
                               (list
                                (cons prop:bindings
                                      (binder
                                       ;; abs
                                       (lambda (expr frees i)
                                         (define acc op-acc) ;; ellipsis count hack
                                         (define field-temp
                                            (let ([field-val (acc expr field-index)])
                                              (match-let ([(binder abs _) (bindings-accessor field-val)])
                                               (abs field-val frees i))))
                                         ...
                                         (make-op field-temp ...))
                                       ;; inst
                                       (lambda (old-expr i new-exprs)
                                         (define acc op-acc) ;; ellipsis count hack
                                         (define field-temp
                                           (let ([field-val (acc old-expr field-index)])
                                             (match-let ([(binder _ inst) (bindings-accessor field-val)])
                                               (inst field-val i new-exprs))))
                                         ...
                                         (make-op field-temp ...))))
                                (cons prop:custom-write ;; TODO figure out how to port to gen:custom-write
                                      (lambda (me port mode)
                                        (define acc op-acc)
                                        (define count (sub1 field-count))
                                        (fprintf port "#<~a " 'op)
                                        (begin (fprintf port "~a" (acc me field-index))
                                               (when (< field-index count)
                                                 (fprintf port " ")))
                                        ...
                                        (fprintf port ">")))
                                (list prop:equal+hash;; TODO figure out how to port to gen:equal+hash
                                      (lambda (a b rec-equal?)
                                        (define acc op-acc)
                                        (and (rec-equal? (acc a field-index)
                                                         (acc b field-index))
                                             ...))
                                      (lambda (x rec-hash)
                                        (define acc op-acc)
                                        (bitwise-xor (rec-hash (acc x field-index)) ...))
                                      (lambda (x rec-hash)
                                        (define acc op-acc)
                                        (bitwise-xor (rec-hash (acc x field-index)) ...))))))
           ...
           (define-match-expander op
             (lambda (stx)
               (syntax-parse stx
                 [(_ field-temp ...)
                  (with-syntax ([acc #'op-acc])
                    (syntax/loc stx
                      (? op?
                         (and (app (lambda (x)
                                     (acc x field-index))
                                   field-temp) ...))))]))) ...
           (define-op-zipper op make-op op? op-acc field-name ...)
           ...
           (define (sort-name? x)
             (or (op? x) ...))
           (define sort-name (sort 'sort-name sort-name?)))))]))

;; TODO: define provide form for a sort that exports:
;;  1. Constructors
;;  2. Safe projections
;;  3. Zipper movements
;;  4. The run-time witness of the sort

(define-sort Type
  (Nat)
  (→ (dom () Type) (cod () Type)))

(define-sort Op
  (:+:)
  (:*:))

(define-sort Expr
  (nat (num () Natural))
  (bin (op () Op)
       (left () Expr)
       (right () Expr))
  (ap (rator () Expr)
      (rand () Expr))
  (lam (body (Expr) Expr)))

(define always-42
  (make-lam (abs (list (fresh Expr "n")) 42)))

(define id-fun
  (let ([x (fresh Expr "x")])
    (make-lam (abs (list x) x))))

(define add
  (let ([x (fresh Expr "x")]
        [y (fresh Expr "y")])
    (make-lam (in-scope ((x Expr))
                (make-lam
                 (in-scope ((y Expr))
                  (make-bin (make-:+:) x y)))))))



(module+ test
  (check-true (has-sort? Natural 42))
  (check-true (has-sort? Expr (make-nat 42)))
  (check-true (has-sort? Expr (make-ap (make-nat 30) (make-nat 44))))

  ;; Zipper testing
  (define id-fun-zipper-1 (zip id-fun))
  (define id-fun-zipper-2 (down/lam-body id-fun-zipper-1))
  (define id-fun-zipper-3 (down/scope id-fun-zipper-2))
  (define id-fun-zipper-4 (up id-fun-zipper-3))
  (define id-fun-zipper-5 (up id-fun-zipper-4))
  (check-equal?
   (zipper-focus id-fun-zipper-1)
   (zipper-focus id-fun-zipper-5))
  (check-equal?
   (zipper-focus id-fun-zipper-2)
   (zipper-focus id-fun-zipper-4))
  (check-not-equal?
   always-42
   id-fun)

  ;; Match testing
  (check-equal?
   (match always-42 ((lam (in-scope (x) body)) body))
   42)
  (check-true
   (match add
     [(lam (in-scope (x) (lam (in-scope (y) (bin (:+:) w z)))))
      (and (equal? x w)
           (equal? y z)
           (not (equal? x z))
           (not (equal? y w)))]))
  )
