#lang racket

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; You can require more modules of your choice.
(require racket/string
         racket/list
         (prefix-in utils: "utils.rkt")
         (prefix-in strat: "strategies.rkt")
         (prefix-in dict: "dict-closure.rkt"))
(define-syntax lc
  (syntax-rules (: <- @)
    [(lc expr : var <- drawn-from) (map (lambda (var) expr) drawn-from)]
    [(lc expr : @ guard) (if guard (list expr) `())]
    [(lc expr : @ guard  qualifier ...) 
     (append* (lc (lc expr : qualifier ...) : @ guard))]
    [(lc expr : var <- drawn-from  qualifier ...) 
     (append* (lc (lc expr :  qualifier ... ) : var <- drawn-from))]))

(define x32 utils:dictionary)
(define use-slice strat:slice)

(define filtered-dictionary (lc (string-downcase x) : x <- x32 @(= (string-length x) 6)))
(define enc utils:encryption-key)

(provide secret-word-enumeration)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                                                                           ;;
;; Secret Word Enumeration                                                                   ;;
;; =======================                                                                   ;;
;;                                                                                           ;;
;; This step exploits the fact that all keys begin with a secret word that is a              ;;
;; proper SIX-LETTER word from the English dictionary.                                       ;;
;;                                                                                           ;;
;; Given a partial key, we can query the dictionary for a list of 6 letter words             ;;
;; that can potentially begin the key.                                                       ;;
;; We can then filter out potential candidates whose keys do not agree with our partial key. ;;
;;                                                                                           ;;
;; It is possible that given a (wrong) partial key, we discover that none of these           ;;
;; potential candidates can agree with our partial key. This really implies a                ;;
;; mistake in the choice of substitution, since dictionary-closure is completely             ;;
;; deterministic (modulo any bugs in your implementation :)                                  ;;
;;                                                                                           ;;
;; Hence, this function must return either of:                                               ;;
;; a. `#f` if there are no consistent candidates for this key.                               ;;
;; b. the original key if there are multiple consistent candidates.                          ;;
;; c. the complete key if there's only one consistent candidate!                             ;;
;;                                                                                           ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define (matching l1 l2)
  (cond [(null? l1) #t]
        [(equal? (car l1) #\_) (matching (cdr l1) (cdr l2))]
        [(equal? (car l1) (car l2)) (matching (cdr l1) (cdr l2))]
        [else #f]))

(define (finding r s)
  (finding-h r s '()))
(define (finding-h a b c)
  (cond [(null? b) c]
        [(matching a (car b)) (finding-h a (cdr b) (append c (list (car b))))]
        [else (finding-h a (cdr b) c)]))

(define l (lc (enc (string-upcase x)) : x <- filtered-dictionary))
(define (secret-word-enumeration key-after-dictionary-closure);; Returns a key or false (#f)
  (define find-proc (finding key-after-dictionary-closure l))
       (cond [(= 1 (length find-proc)) (begin 
                                              (display "swe: potential consistent candidates:")
                                              (displayln (list->string (use-slice (car find-proc) 1 6)))
                                              (displayln "swe: completed key found!")
                                              (display "swe: secret-word is " )
                                              (displayln (list->string (use-slice (car find-proc) 1 6)))
                                              (car find-proc))]                                                                                                                                   
                                                                      
             [(< 1 (length find-proc)) (begin (displayln "swe: potential consistent candidates:")
                                                                      (displayln (lc (list->string (use-slice x 1 6)) : x <- find-proc))
                                                                       key-after-dictionary-closure)]
             [else (displayln "no consistent candidates found!") #f]))
