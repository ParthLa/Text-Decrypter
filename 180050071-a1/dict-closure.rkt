#lang racket

;; You can require more modules of your choice.
(require racket/list
         racket/string
        (prefix-in utils: "utils.rkt"))

(provide dictionary-closure)


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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                                                                  ;;
;; Dictionary Closure                                                               ;;
;; ==================                                                               ;;
;;                                                                                  ;;
;; A choice of substitution can really trigger more substitutions by looking at the ;;
;; partially decrypted text - surely there will be some words which can be uniquely ;;
;; determined using the dictionary. It is prudent to concretize this "choice" as    ;;
;; this purely deterministic (involving absolutely no guess-work). In more          ;;
;; technical terms, this is called "maintaining arc-consistency" (look it up on     ;;
;; Wikipedia).                                                                      ;;
;;                                                                                  ;;
;; This function must utilise the dictionary and the cipher-word-list. Decrypt each ;;
;; word (`utils:decrypt`) and check if the dictionary has:                          ;;
;;                                                                                  ;;
;; 1. a unique completetion!                                                        ;;
;;    - Extend your key using the information with this match. Continue exploring   ;;
;;      the words under the extended key.                                           ;;
;; 2. many completions.                                                             ;;
;;    - Do nothing, just continue exploring the words under the same key. If none   ;;
;;      of the words fall into (1), return with the key that you have built so far. ;;
;; 3. no completions!                                                               ;;
;;    - Return `#f` (false), indicating that this partial key is wrong, and we must ;;
;;      revert to the original key.                                                 ;;
;;                                                                                  ;;
;; Returns either of:                                                               ;;
;; a. a (possibly) extended-key.                                                    ;;
;; b. `#f` if this key led to case (3) for some word.                               ;;
;;                                                                                  ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define lst utils:cipher-word-list)
(define x32 utils:dictionary)
(define x33 utils:decrypt)
(define beta utils:add-substitution)


(define (equal-small? p)
  (> (char->integer p) 96))

(define (equal-capital? p)
 (and (> (char->integer p) 64) (< (char->integer p) 91)))

(define (full-capital? a)
  (full-cap? (string->list a)))
(define (full-cap? l)
  (cond [(null? l) #t]
        [(equal-capital? (car l)) (full-cap? (cdr l))]
        [else #f]))

(define (zip l1 l2)
  (match (cons l1 l2)
    [(cons '() _) '()]
    [(cons _ '()) '()]
    [(cons (cons a b) (cons c d)) (cons (cons a c) (zip b d))]))

(define (check-match a b k)
  (cond [(= (length a) (length b)) (check-match1 (zip b a) '() k)]
        [else #f]))
(define (check-match1 l l3 k)
  (cond [(null? l) (utils:is-monoalphabetic? (remove-duplicates l3) k)]
        [(equal-capital? (cdar l)) (if (equal? (cdar l) (caar l)) (check-match1 (cdr l) l3 k) #f)]
        [else (check-match1 (cdr l) (cons (car l) l3) k)]))
     
(define (work-on p l l-key)
  (generate-list p l '() l-key))
(define (generate-list l1 l2 l3 l4)
  (cond [(= 2 (length l3)) l3]
        [(null? l2) l3]
        [(check-match (string->list l1) (string->list (car l2)) l4) (generate-list l1 (cdr l2) (append l3 (list (car l2))) l4)]
        [else (generate-list l1 (cdr l2) l3 l4)]))

(define (purify x)
  (filter (lambda (z) (char-lower-case? (cdr z))) x))

(define (substitutes la lb)
  (remove-duplicates (purify (zip (string->list (car la)) (string->list lb)))))
  
(define (dictionary-closure key)
  (displayln "Starting at the beginning of the word list")
  (define (dict-close k l)
  (cond [(null? l) k]
        [else (define decrypted-word (x33 k (car l)))
               (cond [(full-capital? decrypted-word) (begin ;(display decrypted-word)
                                                     ;(displayln " --> Skipping this one")
                                                      (dict-close k (cdr l)))]
                              
                     [else (let ([matching-list (work-on decrypted-word x32 k)])
                      (cond [(= 0 (length matching-list)) (begin (display decrypted-word)
                                                                        (displayln " --> no match found")
                             #f)]
                            [(< 1 (length matching-list)) (begin ;(display decrypted-word)
                                                                  ;       (display " --> multiple matches (")
                                                                   ;      (display (car matching-list))
                                                                    ;     (display " ")
                                                                     ;    (display (cadr matching-list))
                                                                      ;   (display " . . .")
                                                                       ;  (displayln ")")
                                                                         (dict-close k (cdr l)))]
                            [else (begin (display "@@@+");(display decrypted-word)
                                  ;(display " --> unique match ")
                                  ;(displayln matching-list)
                                  (displayln "dc*: (A B C D E F G H I J K L M N O P Q R S T U V W X Y Z)")
                                  (displayln (beta (substitutes matching-list decrypted-word) k))
                                  (displayln "@@@-")
                                  (dictionary-closure (beta (substitutes matching-list decrypted-word) k)))]))])]))

  (dict-close key lst))


