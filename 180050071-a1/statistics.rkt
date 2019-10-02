#lang racket/base

;; You can require more modules of your choice.
(require racket/list
         racket/match
         racket/string
         (prefix-in utils: "utils.rkt")
         )

(define lst utils:cipher-word-list)
(define txt utils:ciphertext)
(provide (all-defined-out))
(struct node(t1 t2) #:transparent)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define-syntax lc
  (syntax-rules (: <- @)
    [(lc expr : var <- drawn-from) (map (lambda (var) expr) drawn-from)]
    [(lc expr : @ guard) (if guard (list expr) `())]
    [(lc expr : @ guard  qualifier ...) 
     (append* (lc (lc expr : qualifier ...) : @ guard))]
    [(lc expr : var <- drawn-from  qualifier ...) 
     (append* (lc (lc expr :  qualifier ... ) : var <- drawn-from))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                                                                 ;;
;; Ciphertext Statistics                                                           ;;
;; =====================                                                           ;;
;;                                                                                 ;;
;; The module should provide a bunch of functions that do statistical analysis of  ;;
;; ciphertext. The output is almost always just an ordered list (counts are        ;;
;; omitted).                                                                       ;;
;;                                                                                 ;;
;; Fill in the body for the skeletons and do not change the arguments. You can     ;;
;; define as many functions as you require, there's no special credit for          ;;
;; implementing/using all of them.                                                 ;;
;;                                                                                 ;;
;; CAUTION:                                                                        ;;
;; 1. Be mindful that bi, tri and quadgrams do not cross word boundaries. Hence,   ;;
;; you must process each word separately.                                          ;;
;;                                                                                 ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Analyses
(provide cipher-monograms
         cipher-bigrams
         cipher-unique-neighbourhood
         cipher-neighbourhood
         cipher-trigrams
         cipher-quadgrams
         cipher-common-words-single
         cipher-common-words-double
         cipher-common-words-triple
         cipher-common-words-quadruple
         cipher-common-initial-letters
         cipher-common-final-letters
         cipher-common-double-letters
         ;; any other functions of your design come below:

         ;; my-fundoo-analysis
         )
;; Takes ciphertext and produces a list of cipher chars sorted in decreasing
;; order of frequency.
(define (freq p l)
  (define (freq-h p l cnt)
    (cond [(null? l) cnt]
          [(char=? p (car l)) (freq-h p (cdr l) (+ cnt 1))]
          [else (freq-h p (cdr l) cnt)]))
  (freq-h p l 0))

(define (cipher-monograms txt)
  (let* ([cipherlist (string->list txt)]
         [l (map (lambda (z) (cons z (freq z cipherlist))) (build-list 26 (lambda (x) (integer->char (+ (remainder x 26) 97)))))]
         [p1 (sort l (lambda (x y) (>= (cdr x) (cdr y))))])
       (lc (car x) : x <- p1 @(not (= 0 (cdr x))))))

;; Takes the cipher-word-list and produces a list of 2-letter bigram (strings)
;; sorted in decreasing order of frequency. Each element must be a string!
(define (freq1 a l)
  (freq1-h a l (car l) 0))
  (define (freq1-h a l m cnt)
    (cond [(null? l) cnt]
          [(= 1 (length l))(define (freq1-h2 a b)
                                     (define (freq1-h3 a q cnt1)
                                     (cond [(> 2 (string-length q)) cnt1]
                                       [(= 2 (string-length q)) (if (equal? a q) (+ cnt1 1) cnt1)]
                                     [(equal? a (substring q 0 2)) (freq1-h3 a (substring q 1 (string-length q)) (+ cnt1 1))]
                                     [else (freq1-h3 a (substring q 1 (string-length q)) cnt1)]))
                                     (freq1-h3 a b cnt))
           (freq1-h2 a (car l))]
          [(> 2 (string-length m)) (freq1-h a (cdr l) (cadr l) cnt)]
          [(= 2 (string-length m)) (if (equal? a m) (freq1-h a (cdr l) (cadr l) (+ cnt 1)) (freq1-h a (cdr l) (cadr l) cnt))]
          [(equal? a (substring m 0 2)) (freq1-h a l (substring m 1 (string-length m)) (+ cnt 1))]
          [else (freq1-h a l (substring m 1 (string-length m)) cnt)]))
  

(define (cipher-bigrams lst)
   (let* ([p (lc (list->string (list x y)) : x <- (build-list 26 (lambda (x) (integer->char (+ (remainder x 26) 97)))) y <- (build-list 26 (lambda (x) (integer->char (+ (remainder x 26) 97)))))]
          [l (lc (cons x (freq1 x lst)) : x <- p)])
        (lc (car m) : m <- (sort l (lambda (x y) (>= (cdr x) (cdr y)))) @( not (= (cdr m) 0)))))

;; Takes the bigram frequency order (output of `cipher-bigrams`) and computes
;; the neighbourhood of each letter with every other letter. Only unique
;; neighbours are to be counted.
;; Consider the character #\o.
;;
;; Takes an argument `mode`:
;; 1. (cipher-unique-neighbourhood cipher-bigrams 'predecessor)
;;    - Count only those unique occurrences where the (given) char preceeds
;;      other char.
;;    - Patterns of the form: "o?"
;; 2. (cipher-unique-neighbourhood cipher-bigrams 'successor)
;;    - Count only those unique occurrences where the (given) char succeeds
;;      other char.
;;    - Patterns of the form: "?o"
;; 3. (cipher-unique-neighbourhood cipher-bigrams 'both)
;;    - Count all unique occurrences where the (given) char neighbours the other
;;      char.
;;    - Patterns of the form "?o" and "o?". Note that this is not sum of (1) and
;;    (2) always.
;;
;; The output is a list of pairs of cipher char and the count of it's
;; neighbours. The list must be in decreasing order of the neighbourhood count.
(define (sum-unique-p a l)
  (sumu-h1 a l 0))
(define (sumu-h1 a l cnt)
  (cond [(null? l) cnt]
        [(equal? a (string-ref (car l) 0)) (sumu-h1 a (cdr l) (+ cnt 1))]
        [else (sumu-h1 a (cdr l) cnt)]))

(define (sum-unique-s a l)
  (sumu-h2 a l 0))
(define (sumu-h2 a l cnt)
  (cond [(null? l) cnt]
        [(equal? a (string-ref (car l) 1)) (sumu-h2 a (cdr l) (+ cnt 1))]
        [else (sumu-h2 a (cdr l) cnt)]))

(define (sum-unique-b a l)
  (sumu-h3 a l 0))
(define (sumu-h3 a l cnt)
  (cond [(null? l) cnt]
        [(and (equal? a (string-ref (car l) 0)) (equal? a (string-ref (car l) 1))) (sumu-h3 a (cdr l) (+ cnt 1))]
        [else (sumu-h3 a (cdr l) cnt)]))

(define (total-neighbours-unique a)
  (let ([la (cipher-bigrams lst)])
  (- (+ (sum-unique-p a la) (sum-unique-s a la)) (sum-unique-b a la))))

(define (cipher-unique-neighbourhood cipher-bigrams-list mode)
  (match mode
    ['predecessor
     (let ([l (lc (cons x (sum-unique-p x cipher-bigrams-list)) : x <- (build-list 26 (lambda (x) (integer->char (+ (remainder x 26) 97)))))])
          (sort l (lambda (x y) (>= (cdr x) (cdr y)))))]
    ['successor
     (let ([l (lc (cons x (sum-unique-s x cipher-bigrams-list)) : x <- (build-list 26 (lambda (x) (integer->char (+ (remainder x 26) 97)))))])
       (sort l (lambda (x y) (>= (cdr x) (cdr y)))))]
    ['both
      (let ([l (lc (cons x (total-neighbours-unique x)) : x <- (build-list 26 (lambda (x) (integer->char (+ (remainder x 26) 97)))))])
       (sort l (lambda (x y) (>= (cdr x) (cdr y)))))]))
  
 ;; You must match against or test (using cond) for the `mode` argument. Possibilities are:
  ;; 'predecessor, 'successor, 'both
  ;; Figure out experimentally which of these is a good indicator for E vs T.

;; Takes the bigram frequency order (output of `cipher-bigrams`) and computes
;; the neighbourhood of each letter with every other letter, but counts each
;; occurrence distinctly. This comment contains 6 bigrams with "w", all with "i" or "h".
;; So "w" has:
;; when mode is 'both,        6 neighbours
;; when mode is 'predecessor, 6 neighbours
;; when mode is 'successor,   0 neighbours

(define (sum-p a p)
  (sum-h1 a p 0))
(define (sum-h1 a p cnt)
 (cond [(null? p) cnt]
   [(equal? a (string-ref (car p) 0)) (sum-h1 a (cdr p) (+ cnt (freq1 (car p) lst)))]
   [else (sum-h1 a (cdr p) cnt)]))

(define (sum-s a p)
  (sum-h2 a p 0))
(define (sum-h2 a p cnt)
 (cond [(null? p) cnt]
   [(equal? a (string-ref (car p) 1)) (sum-h2 a (cdr p) (+ cnt (freq1 (car p) lst)))]
   [else (sum-h2 a (cdr p) cnt)]))

(define (sum-b a p)
  (sum-h3 a p 0))
(define (sum-h3 a p cnt)
 (cond [(null? p) cnt]
   [(and (equal? a (string-ref (car p) 0)) (equal? a (string-ref (car p) 1))) (sum-h3 a (cdr p) (+ cnt (freq1 (car p) lst)))]
   [else (sum-h3 a (cdr p) cnt)]))

(define (total-neighbours a)
  (- (+ (sum-p a (cipher-bigrams lst)) (sum-s a (cipher-bigrams lst))) (sum-b a (cipher-bigrams lst))))

(define (cipher-neighbourhood lst mode)
  (cph1 (cipher-bigrams lst) mode))
(define (cph1 g h)
  (match h
    ['predecessor
     (let ([l (lc (cons x (sum-p x g)) : x <- (build-list 26 (lambda (x) (integer->char (+ (remainder x 26) 97)))))])
       (sort l (lambda (x y) (>= (cdr x) (cdr y)))))]
    ['successor
     (let ([l (lc (cons x (sum-s x g)) : x <- (build-list 26 (lambda (x) (integer->char (+ (remainder x 26) 97)))))])
       (sort l (lambda (x y) (>= (cdr x) (cdr y)))))]
    ['both
      (let ([l (lc (cons x (total-neighbours x)) : x <- (build-list 26 (lambda (x) (integer->char (+ (remainder x 26) 97)))))])
       (sort l (lambda (x y) (>= (cdr x) (cdr y)))))]))
      


  ;; You must match against or test (using cond) for the `mode` argument. Possibilities are:
  ;; 'predecessor, 'successor, 'both
  ;; Figure out experimentally which of these is a good indicator for E vs T.
  

;; Takes the cipher-word-list and produces a list of 3-letter bigram (strings)
;; sorted in decreasing order of frequency. Each element must be a string!
(define (cipher-trigrams cipher-word-list)
  '())

;; Takes the cipher-word-list and produces a list of 4-letter bigram (strings)
;; sorted in decreasing order of frequency. Each element must be a string!
(define (cipher-quadgrams cipher-word-list)
  '())

;; Takes the cipher word list and produces a list of single letter words, sorted
;; in decreasing order of frequency. Each element must be a string!
(define (fltr l)
  (define (fltr-h l m)
 (cond [(null? l) m]
 [(= 1 (length (string->list (car l)))) (fltr-h (cdr l) (append m (string->list (car l))))]
 [else (fltr-h (cdr l) m)]))
  (fltr-h l '()))
  
(define (cipher-common-words-single lst)
  (let* ([a (fltr lst)]
        [b (map (lambda (z) (cons z (freq z a))) (remove-duplicates a))]
  [p (sort b (lambda (x y) (>= (cdr x) (cdr y))))])
  (map (lambda (z) (list->string (list (car z)))) p)))


;; Takes the cipher word list and produces a list of double letter words, sorted
;; in decreasing order of frequency.
(define (cipher-common-words-double cipher-word-list)
  '())

;; Takes the cipher word list and produces a list of triple letter words, sorted
;; in decreasing order of frequency.
(define (cipher-common-words-triple cipher-word-list)
  '())

;; Takes the cipher word list and produces a list of four letter words, sorted
;; in decreasing order of frequency.
(define (cipher-common-words-quadruple cipher-word-list)
  '())

;; Takes the cipher word list and produces a list of chars that appear at the
;; start of words, sorted in decreasing order of frequency. Each element must be
;; a char!
(define (cipher-common-initial-letters cipher-word-list)
  '())

;; Takes the cipher word list and produces a list of chars that appear at the
;; end of words, sorted in decreasing order of frequency. Each element must be
;; a char!
(define (cipher-common-final-letters cipher-word-list)
  '())

;; Takes the cipher word list and produces a list of chars that appear as
;; consecutive double letters in some word, sorted in decreasing order of
;; frequency. Each element must thus be a char!
(define (cipher-common-double-letters cipher-word-list)
  '())
