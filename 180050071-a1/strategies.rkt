#lang racket

;; You can require more modules of your choice.
(require racket/list
         (prefix-in utils: "utils.rkt")
         (prefix-in stats: "statistics.rkt"))
(define alpha stats:total-neighbours-unique)
(define gamma utils:is-monoalphabetic?)
(define eps stats:freq)
(define m (stats:cipher-common-words-single utils:cipher-word-list))
(define n (stats:cipher-monograms utils:ciphertext))
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
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                                                                     ;;
;; Strategies                                                                          ;;
;; ==========                                                                          ;;
;; For the purpose of this assignment, just the `etai` strategy is expected, since     ;;
;; we have dictionary-closure and secret-word-enumeration to leap-frog to the right    ;;
;; key. This technique would fail for harder keys which are arbitrary permutations of  ;;
;; the alphabet. We will be forced to explore many more strategies (along with         ;;
;; dictionary-closure of course).                                                      ;;
;;                                                                                     ;;
;; Strategies to guess substitutions for the key using statistical information about   ;;
;; - the English language from utils.rkt                                               ;;
;; - the cipher text      from statistics.rkt                                          ;;
;;                                                                                     ;;
;; Follow the function signature as indicated below. Deviations will make it           ;;
;; impossible for automatic grading of your submission.                                ;;
;; Moreover, we do not expect your strategies to require any more/different            ;;
;; arguments. Note that you recieve the key as argument, so you can at the very        ;;
;; least ensure that all the substitutions are monoalphabetic wrt this key.            ;;
;;                                                                                     ;;
;; Signature:                                                                          ;;
;; ```                                                                                 ;;
;; (define (my-fundoo-strategy key)                                                    ;;
;;   ;; Make use of `utils:ciphertext`, `utils:cipher-word-list`                       ;;
;;   ...)                                                                              ;;
;; ```                                                                                 ;;
;;                                                                                     ;;
;; Substitutions                                                                       ;;
;; -------------                                                                       ;;
;; In order to extend the key incrementally, we use `utils:add-substitution` to        ;;
;; extend a given key with a substitution.                                             ;;
;;                                                                                     ;;
;; A substitution is a list of pairs, each pair mapping a plaintext char to a          ;;
;; ciphertext char. For example, to extend the key with T -> a and O -> r              ;;
;; (simultaneously), we use the substitution:                                          ;;
;; ```                                                                                 ;;
;; (list (cons #\T #\a) (cons #\O #\r))                                                ;;
;; ```                                                                                 ;;
;; For a single substitution use a singleton list (containing just one pair).          ;;
;;                                                                                     ;;
;; **CAUTION**                                                                         ;;
;; -----------                                                                         ;;
;; 1. Note that add-substitution does not do sanity checks on the substitution and use ;;
;;    of `utils:is-monoalphabetic` is recommended to ensure that you don't             ;;
;;    inadvertently create invalid keys.                                               ;;
;; 2. You must provide a list called `compositions` in this module.                    ;;
;;                                                                                     ;;
;; See docs in "utils.rkt" for more information.                                       ;;
;;                                                                                     ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; You must add "public" functions of this module to this list.
(provide etai
         ;; Some more suggested strategies:
         
         ;; common-words-double
         ;; bigrams
         ;; common-initial-letters
         ;; common-final-letters
         ;; common-words-triple
         ;; trigrams
  
         ;; common-double-letters
         ;; common-words-quadruple
         ;; quadgrams
         
         ;; lists of strategies
         composition)

;; A strategy that uses some statistical information to generate potential
;; substitutions for E, T, A and I.
;; Refer the assignment manual for tips on developing this strategy. You can
;; interact with our etai with the executable we provide.
(define (slice l a b)
  (slc l a b 1))
(define (slc l a b cnt)
  (cond [(null? l) l]
        [(< cnt a) (slc (cdr l) a b (+ cnt 1))]
        [(> cnt b) '()]
        [else (cons (car l) (slc (cdr l) a b (+ cnt 1)))]))

(define (leastfriendly l)
  (let ([f (lc (cons x (alpha x)) : x <- l)])
    (sort f (lambda (x y) (<= (cdr x) (cdr y))))))

(define (etai key)
  (define l1 (lc x : x <- (slice n 1 5)))
 (cond [(>= (length m) 2)
  (let* ([x1 (string->list (car m))]
        [x2 (string->list (cadr m))]
        [p (remove* x1 (remove* x2 l1))]
        [x3 (car (car (leastfriendly p)))]
        [x3a (car (cadr (leastfriendly p)))]
        [x4 (car (remove* (list x3) p))]
        [x4a (cadr (remove* (list x3) p))])
    
      (lc (list (cons #\E a) (cons #\T b) (cons #\A c) (cons #\I d)) :
          a  <- (append (list x4) (list x4a) (remove* (list x4 x4a) p)) b <- (append (list x3) (list x3a) (remove* (list x3 x3a) p)) c <- (append x1 x2) d <- (append x2 x1)
          @(and (gamma (list (cons #\E a) (cons #\T b) (cons #\A c) (cons #\I d)) key) )))]

       [(= (length m) 1)
        (let* ([x1 (string->list (car m))]
        [p (remove* x1 l1)]
        [x3 (car (car (leastfriendly p)))]
        [x3a (car (cadr (leastfriendly p)))]
        [x4 (car (remove* (list x3) p))]
        [x4a (cadr (remove* (list x3) p))])
      (lc (list (cons #\E a) (cons #\T b) (cons #\A c) (cons #\I d)) :
          a  <- (append (list x4) (list x4a) (remove* (list x4 x4a) p)) b <- (append (list x3) (list x3a) (remove* (list x3 x3a) p)) c <- (append x1 p) d <- (append x1 p)
          @(and (gamma (list (cons #\E a) (cons #\T b) (cons #\A c) (cons #\I d)) key))))]

        [else
          (let* ([p l1]
                 [x3 (car (car (leastfriendly p)))]
                 [x3a (car (cadr (leastfriendly p)))]
                 [x4 (car (remove* (list x3) p) )]
                  [x4a (cadr (remove* (list x3) p))])
      (lc (list (cons #\E a) (cons #\T b) (cons #\A c) (cons #\I d)) :
          a  <- (append (list x4) (list x4a) (remove* (list x4 x4a) p)) b <- (append (list x3) (list x3a) (remove* (list x3 x3a) p)) c <- p d <- p
          @(and (gamma (list (cons #\E a) (cons #\T b) (cons #\A c) (cons #\I d)) key) )))]))
        

;; A suggested composition of strategies that might work well. Has not been
;; exhaustively tested by us. Be original ;)
(define composition (list (etai (build-list 26 (lambda (_) #\_)))))
                  ;; common-words-double
                  ;; bigrams
                  ;; common-initial-letters
                  ;; common-final-letters
                  ;; common-words-triple
                  ;; trigrams
                  ;; common-double-letters))
                  ;; common-words-quadruple
                  ;; quadgrams))

