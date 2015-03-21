#lang racket
(struct addr ip mask)
(define-syntax ip 
  (syntax-rules (. /) 
    [(ip a.b.c.d/m) (addr (list a b c d) m)]))